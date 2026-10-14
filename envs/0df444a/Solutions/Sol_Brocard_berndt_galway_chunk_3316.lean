-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3316
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:18:27.436166+00:00
-- url     : https://prove2.me/submissions/91a197d5-d534-42ab-874c-0ecae9835535

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 596223021 ≤ n < 596402877 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 596224271 1250 596223021 596223029
    0xb0f071e06180b011412011e0b09150f18041b08010e03120a2a0e150a08090712110909060c071401060504050f0609011502120702030a0519030909060f05090a15 70
    0x700d1349235201e00002c4804e0260200210086610522b40d00e011440003044041d020404d603c40c2c9943d1960040c0d40d1200c20708903400fa80c60100f100018a494203060341070814503885180812003101002030948011321400070048082d0f030103145001c0032000180c03607161000e41b2080c090703551030340c40d500c0c443c200da510410280e07640c01155101d10700c1110090600c86640075000d0140c80007000c80038840d04004210f641128040c20420250f484080390903140120540200e40d407605e1040006050010b003000340d140d031010880b01c0c1c030340640c0c40b00d8007151104015541603803000c03414003000c00041d04507035046018441d0f910000900d030f69500c0000301035983c11b423240ca100e030980006204880c00c00c807c406025154100f0b05d03524400404e04000e680341c811210310095003c020400b10115a802d000d0385a010b6040401c49a00351200c07400081050442c0f601280450b10b056800124900e0b68041e010446140e8104401420700c2c0c5014000c203404000c000ca0036041d42e505003080100002a5114060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 596225521 1250 596224271 596224301
    0x1b0506070308100b18190503030c03090411070c030f06090b0c091201110306040e0f0d0e1f08070c03020c030a061a030c0603010b0f071e06180b01141201 67
    0x341060500c41900050395046000b12007000c000f00d04041c925825049035880095801c02004170102106c90340c55070440c2c0103190305000c0015000c0b2071690010140c005280101d41c100191366407403082d002d0502c2150740051500386d04610420116030700501c08554240500c0c0d001c6817a501ca40e031461104002140c0210741032a010400c0b020500f8400894000845100001c21145150160200c200d01000704980e10498640c0c40803207000c102401400492240340d401c980e1410981c41018184804030350150380110000500400d0441602e101300700b0842d42c0c3d4a80c51020f46800c1c104440c0d84440d224140d0961161410486a0340c41c1040b00500072802050001481e4140d0348940300311155503464248290302240041c905030340ca80c4103da0441e45185003195682e413040184094a000d00303a005402500441740500f445540c52048900061003030004102183c14603170f92240d8001f141802900d8480518014002042c2111000e0080a002041ca15144048418003420344840507544044 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 596226771 1250 596225521 596225537
    0x40e0a080c0d12051e0601050c0f0706080f160e0a030209090717070b0f0915030f040c15020a232406030d0c0813090e010e0601051009031b05060703 65
    0x2450358800750f1003010310780c801010b00090130120110b0010054060360910003000040101d03030315a01500032910340b404443d054440715a01e002c2081d440c0c0781c25101f4840401c0480002a01c80b10810035082d20a21180d100c0702d0001c09143d00469001e100b00301c0143d005029404080056500d40141900c5102c445009202090805460300c0c400080034083c255035900411040c809034a120007510b90182c44e00c0c642c584c85034400c0380050549240050200399414000040c0719452907201c103107502c20b42c010380d0031090303103507644030403001480710a01c90400581111309120001021808981520305ca1082912101c68243c035180382000324107445000a41c80c8103a04401c0410b517064525032040c1d044010f400c40207a541400343c83d4081181700180141c50000b03100502da40e01c1340108000d805040001c0103100c00a4040720b0092042009400070b40c4980700001800d032805800381101d1500750341d40e100351075181d03a550314851402a6a42481500740c2c04010070700b522a01d000e030054034001c0e07988401c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 596228021 1250 596226771 596226793
    0x120112060c0534140706030e0307080d0207050a140a0303060e070f30091e150209040603020d0c03031d062b060305030d2306040e0a080c 60
    0x31600320300542402d00c00180310404240740c200340030703100005003400e03a101842d090595004440302c0c40c810003822400800d200080c542c0c0c00080e100107483c51910101316440c140d01003241d890007806001068518108120418964141c0107014030740e104d00300b03e4100342441d54400b9030a04250317002c0c548503403042d1500030902d540b41c024800284501151031002c0d080c00b5000600616074031803600b00340044141103281c00d250020040711280940303445081136410700d00035000a0209980f0a603400b13510500d0424bc2068441c0300d00300c40c07540c017840620500c001c41403010040d42251507482d0f4041d54401000015840726880c20340c4003807081c203c10315028103600e400362100400b6456004030200e0701d81030f0391050321001c0440b9080c59018915a6260300c0000302d080d88808c0e040034003a50981810703400020008004043c141c0400c4150080c08640011030b030304541c890811414200c64140107011903c3d0342456809600381c44000c20035036141400c103403200046030303221841000007580704100c0300b0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 596229271 1250 596228021 596228033
    0xe010e0405071809090503070f0c030b01030b2509301109070c0f0b13150507030b030102090112091109011d0609091c210f0c0e1c0305120112 62
    0x20f0250001180030454000a501c8903984e07801035500041c584128010024280003011944d100110780c00b007841400c0d5070312480c024072200e0703040e114203400c58005414503200481c3d403c0c8008481403d40da03680081450000d03804d0070895802c0001c031001d030000d4604034254450080b90b923102400391645c08000d81003242404203086005018004000040c3d201a00150090400c00d880d150003101c14145915a48460400c011080790028a140c90382213403818542120303009a4404c40310740d03c040100b0300452040c035080c1c0c0f00f00c541803400100600c1e41d00344c07200c28690080302041c1c01040c46028841c01403020501c968020317000703484c00c0100207000d98401e0b10304005003544420305940f004942c0c104001c01c640d443c8102e40d5551501140000721241c05440360b4402e82066a401c501ca661901c11010458001c0a504001c051000c0c24904040c041601450000c480700780d018100c415420281441c01fa2140c070384280c00c6080100c00c0202150541d000c01c0c506001e4080b21124031621081443c0c00 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 596230521 1250 596229271 596229317
    0x261c060f050307050d06020304060b10020606040b0907051b01060503031b0f010204030c0e090a0203100c030506090702070e090109060c0305010602160302030c150c01020a02010c02101505010e010e040507 89
    0x1c0c5200360300000c4280030b261144000001c9007948100e01580360380b03c503d8550041d1401201e0160413905843c03418000660000c1e10718002d1710b06a60030007544966400b80041c0d0f65044807a040462400c2151000850030b4000e0314451a00c40000003c0141d221400241107610907480500d42002240c44108055424000c00398a81080340003146454919604d00b05d1078400e52150b4003002d1700520009a100d901800441601d07540242950a0340b0f8120802c03000820303440e90940300017807901c00010a14181407498038090010364004204141c6494000603840390000c010524035500c1e84149000140c050052556824250320701280030f40c141031009292801801d0000c5240401020420160302c011840b10940b24040da8070b00d07580c09030050910082d21038801410120341c400100c2c680010350643c0b140404081580c00d440d041e0542096110980d481c560820030388101c0890100041e41c000c040c01c01d0100700604000b600c1c2e6070400005421501c0c12516000030511101d04d00650309600303480 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 596231771 1250 596230521 596230529
    0x5070f060921020102101e1a0d060c11030d061d040f02091b03010b0d1103090303070c020d050604051005070f0e0409061b11010b010804261c060f 64
    0x200030403191070410160720a08941c0500540c003000450100b055910a00c074501030490609400d0165612085048145039030601200d994946011504100141e15062003140000010540003240d40d03a03443d498028080c030301001c010b020300000c032000402803d001500030701c2a1b900c000541c0e145841300b42071082d4a11084445484c4504040200041c00381407081d060a405861480a0303568200d0a0282c00f0704403481004504000f000014035240e2440c020225500e91100030300c031030810805051201c1c0070941c1c420303000ba0014000075005030310503400741040c0c0d4001040e01103030345120b8440f00c0c186402034809503441e4018904074464a141c5004d0316821465500c0c2071003240a180400030207408209008511482d110300a5600340460740e0810501090b140b02e8506401d958500c000d40311100d0035138885141d500b00412040b0765806070b020a880340d9003001640d001c003c4400c5501709501e00900340d41400c0c81d001d01c00c2d00b001030f11043d800c0d801941c00300c600003221400d100034144001c680390701c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 596233021 1250 596231771 596231777
    0xb090d030605092707170709140c0a02120307180e01061d030708070e0702100603170a030e0f1e030a0f200307080d0509070b03060f060c070305070f06 66
    0x300030029611545442e550100603080018601040c0602501d000304c40852000910300c01e8100101c0c01848000300803d4804503c8115289645e8900054080d0380c851607034004038205400c0000d80200c6c0050080c45031500c103205554480840c240020402e410039a09080000d030103402da07040052015840d100603060f250300c8100c3c107624040d401029006040382c10a8500b0000b403030b02081c2e480402420300a48031003800d40300a071b030b1612880e9030b4821007200d40c42e00520895032085d101c5040b61041b0029282c20100122541907060300a286aa01440017041096542d040004075840c040c00040b021250690240602c26404ec400c800c41c1c03690b07441207801c1c41e0020041d0780340a035004052505090154100511000000d0302e01942101d1005100b03041400001040020880b480000380b214110b00d400c104400d403141262aa5600f245003c0d1210450040012407024508000540d00744500140194a800010010581040415401103905c0d5005580900401603003000754405446946 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 596234271 1250 596233021 596233031
    0x180a030f02130e0c010c030311030f04200a0e090a02120c010e06030f0708070908030c010203010609150e0f06160804300308060a0e070908010b040c0e06030a180b090d03 74
    0x145868250584c107190510050b0080a8201030180e00140d5002030080081c40d10b0b071501207100c00b81c800003250111041c001d0b09000c49503081c08500020751211001d05001c10031400c103000041c1c40040a4006a00340c82060070342001aa5481c407080c1c0084113900c09403440c04113000001d800c0410070322000d0300c18075091003000060b080062840d0761100203071401c100740341c07a1101c0a44901105401038040d60100188481c4941c20540046040303400a958010b055a0355099403000b0311007005165001400c81c00c122062454110803400700403900030402071400c41f0080d43c10314041a03007c0121030030075001c81c003001140e0000d1800e040c041c1a40d64004280c0b4103454a0510f540d41c0c480009040c0030005000c19840d4842ca03081c030000e003040710311024041c02c00003000f40c0801c0c1d09200e02c000660070800f03015440c0c1090301940400e40c14548848a80102a004001035034000901102c0c0d002c0d078543c01c2c2c40015200705007aa40d554060b403400003a40c00c0c60220389050000800c00c11082c14105 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 596235521 1250 596234271 596234291
    0x4240f0e0d021309050a060515100c0615080d1706190306180f06051611030f0313050d0c0b0108010612030e01022d0615030c06180a030f0213 62
    0x105010080c0c60b0360484100b03076460900c8128500a1400940240c024440c9100c1c210410030b0980c084d0f4040d800011014004601d001d04000b40d0b602d003031002100040703a04c142c682c009103c45c0c10003400324080c040b61008660721406e0542c500b039114066000003500700e0096801e1800d80881103038020006465010780c07090441c203a143c0d28607140c4401002c0958610328815000c41a41103030030410340c0b05803640b101d041c2c5402c24102400d8103503107841e0450a04105912050700455487c00340701c1244000d142011010342400e02e558000804803940650544c1602c00002d40134050f031703001c42c10705448912071034209092124080340141c03c1040350b41c3c900b0301c00b0300410798039036040d00c3c0d00c55051030031051000500e00102d08084614000c1c1042a525410070a00340820000809000243c081250324540d1480c4603403042a512104079505a00807004000c05400c0c030b4001401001481801d140e107070540c01020460910341644140e40110044080030118602000c600c6040c00d00f455061081d0903030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 596236771 1250 596235521 596235529
    0x702130923010f0f0b0a0614121302211e030702030f0102121602060604020a030f09150e030702180714190f03020901270306020301030605090f120a0c060204240f0e 72
    0x498004c100074400d5914848c070078100074404a4440700300142d40b000381da0401003d18180021125401c91050301c01054450b4003c0b040702100000c400c24030002d04d65526504001c070ba490050000748c030050b010411034100582c804101080d0102c40c020001680d54864554008080c3c030043e00c4441c0c544003003456110945c2e40040c642d03800c15001c42d001691808182800e80040c4468049511203501300801a02840b0380c0c0c03c003903801c04d080d524080c0401440290100e4a170711071140e00943c4002030800c0c4001d0300041c25440d9500c400c450074255001c6800268010300fa8010b54101c2c00c10400c10442d11031603a42c4030503861070450150500358201088140081c04030300b030360500b031002c0d01840350769020140301c02402c0030011a04802d0840da80d507120304040000d0541214006030a20914140340c5a0b00d2000a0300d100502401c44c407103003018504682180c620302c1540080e00ea5607000e0202280712950400c030324090780340040001c1e40c0501340e0080034003054902050803062021104034080c240d15 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 596238021 1250 596236771 596236789
    0xf06050f0f030606160c0303080a02160f0501111b0c100e220c050702040e03030106080c090f18041b140103090206130315050a020702130923010f0f0b 66
    0x1100c614094480d0f07078110201d40d0fa40203000079602c209509602000521034a81840e00079240207a468440b20b80d201a0740000368131a2012100001014030f21850201f02c3c60800c0302507a921603400172030201c80e805c400084c50f8104240e0b058042030201c20b184032507101000340e1040c1d05004c0e69110180310070b40038064459041c18445600880e0041c10409600e00c4000503201700c010b014400300903441140034000c015410007803080740035a03d00031100740c0c904800810b8038101e40c40b503520b00720305950348100508180c000054803900714a5180c010011943c0c1c55516825040350352604a204e854103003000c1c000703038507185142c070000000e8250501c080f11107110030054001080c00c012841c043d051000c100c441c4500b41400c0740c0c2c550120004410072040c87c0d00407255504e922001c1c0000c0d00c91601d01401c910031458020f612244144d1180b02c01c51650300048507084c0075103003040741c0d0070341111940c00b0a410b107940544d55966880314400300c46600e11620b1030403602c046040184040520100707403010 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 596239271 1250 596238021 596238037
    0x210140a1e0606090e09070302030c011209020301020f0d0b0f010e120703140715030501080615030309040c08071205160804050709020c0d030f050f16050405030312010f06050f 77
    0x562520301d401c00344114424100c001031441c200c100704455440300010203040a90007490411028280480d9240500256000550b60028090201d020b0707540d0054500040c003107107401c3c0e050f4440a0400c056942031002c1c0030050500440259150b08141c0004111002166003520070002456030325901e0340d002c074070900c0c150070680364603090603640030340d05140480310b610091a043c208010320b00c091401181d03900441d80800b041d103017144203200b016030558000740a450041d0b8041000600d03444142d003600038074004040d05803890070449070041001d8415403407001c00070401b03807003e00020aa00c1007001c81c008504030f604102c0c42c14840e820060581c0000c22050801c078590001c582800030a01140c80100f8040e203003103541e52b01101015480e22412040800402d1038620340d103081110a0086c3e602c10364140581000300d644092000d4607234143c184102c07007000002d02011400fa2001c0004252400000c4028000e42d8903080f1800c0d06902903402c00f0f03040182c14081c0e82c4045c107241041d94910 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 596240521 1250 596239271 596239291
    0x4120329030c12072108030c090105120f191802090c190801091401060503071107080a06060f090902060f0904090c030321020a1418090405030a021014 66
    0x40440030006440e09042c418440e6000002010111503c40001200c0d000c43d1041c081444c0745480d000342c4c0303004440d94000003402d150f008100203109950300500034454080141081170829280700e401135046c100465a960b2801101401d2013088028482100c0401615a000303015500741d80705019015180700e00c00038060558540469540c00540701070342c0309084d4039002080300a10035240104400380a1144c40b20355032170400480e0705114100000342c141c80490700e400f07156440e110422940e0000c110f48110841c05115004121110103101c00e00b4040e0098002003203143c24050143c0c50b01c41d00c0d5101e07258445c41c241070200181c5554050704c900880f0101e140c0c2d1a1000030000c10301500745207100418204074414080100f5030010740303520140310243e14201080075043c2c8011304a101d0f4040e6100462074011944141c54207260080c030000c1000c141c0e0802d402100000306203100e0080d44e003281e05400119008200c81da04000c800d4108444080900102584056001a18401174842144 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 596241771 1250 596240521 596240591
    0x11071508040804050d050601140d0f03110a2f0a05010f120612030302030405240a0207030215010f05150301140402090120030a0e01090806011e0f0e041203 68
    0x2d20110105880042c00080e084251031007807440c0c8262075010900481d8000d02a01000d510300d03082402e81d241c4070b0703580031650010711412520203503035002810b00e89109520600c0c0340c3c0d500203581d004001c00311013a81a40501d07290051082100150b000e60240d60140c25400030401c6180e90021040c0c2c81130700030f030404046240311180148060300c03442e0001140f0216007042c5104140d4103500852040d805041a01c505020088900e8401941c040030064003050001c042611840d4582c001c0c00847e200740102c503440300b5401c1d80d48005003000d0380f10500c050341c0044100007a0400d8640305800301292800680765604180070341d00d61604411541d070150f54007042e03c0180743d011f090002c0090302c005450200301d01842c81500d80d21785c403040d81000000e44120400c00c181d40121000b8068941e4940034006a070f003011001d129681030b404018038000761502c4c0002c2c1080710100c512014101034101003480d03142500346000e000e603815802004042c989428800c404a101c9408103040e09241c4c0d11842d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 596243021 1250 596241771 596241773
    0x3010504050712110a03060b070b0c0a0302091807200a241a19030b130203011d1c0804030512040c1707140d021f180311011107150804 59
    0x303040c500441031243c0952414112481c00001d05010307104540ca140da007481a03d072600104400b900510800800301324642020580086210024000400c420300d0b0060800b601d51002600d200110700d06554070031405401c2c040b2050384160b08541903c5c54400c070780d003c110100d218a584001001c03001c0c0c10100720142070310416040303541c1d100e86440c0d42482404143d00c0c140380080341e051402c0711148035114913042082d00480040c069822207410a60246140c1d82d0000d010384c4030400110120307419580c4004840d012511103034080342c2844040018400e04140c010642140801c54800d803041c070110808102c0044d50007003c441c840c800c0c5801c80c10080d01c4e145407400540d25503400c502d41c010020001080c0300f20340041c0030b600301c80e10186040e6541000300c0501220486c5024065005071811900c945480e0320403540711003001403441e2050300e4002c0790385a910140701c640c000b00c03550081600d07404415a8040710400750450000080e18a051500035943c50300401c5020380d034244150600010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 596244271 1250 596243021 596243027
    0x5090f061f0e01090e01140702070302040504020d08070f12020703080405061c061508011e330e040b1f031107120503011509150e04091202011d0f03030105040507 71
    0x803000341a40300071405a561180404005800051717136440d41986010f02518100e01c1040480307001c0c148980181103c00d045400340005010004d10503030308960000300b043c0c0022501e5005040320b90103107403009940f407440c0c030b420000b10200d141c20604641c0000300900c013042000c4c044404564085500070f0b03076410f070055440940442c0c0721112049070b03c0e01303034005103101900050090b145800c0e1340c0c040640c2e80f078032005055030b4089401c010701e42004200c240034041c84048e40c000032100581044a101c2003a19030b0480c2c1c4015620820002600301801c2000c5062502500340140011100b6130f8242d601424400c40060340340d8102410141c07200c1e42c200b00d155001f000c44034803603085003a10b1861400c080c40a04143c0c1b00703204180300805105603416009103e54540340950f86600c50340d0074900140c03482241c001000c080c11603803140c2d80d400350100089205c1c0d8200a6990140c00100d060030718010349400c1c50440d481205040e40000041d0703041008040205ca0554408580c00115607c07450310403 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 596245521 1250 596244271 596244331
    0x20306030f060c0a030f0e07032316030b06060c0a0803100e010b0a02060903030106050f030a020f0705010509010506060c070e0705120406021e040302011b02060d06090605030105090f06 81
    0x40e0682c05a007050010080300c001c01402ea40d0b1060314280804804c8204c0842120302c0c4403030800326074001600c2400020312403e42803080c40c014110b44410382239041080c6081138030407040540045062a410801c100c0751140e481d900c01012940c10341000082245641c842c81400c400420603440000001c40c110700c8030419070f0282102c400070004940c1c445001e10f0155000c900420017610804001503013800d0004112030590744195241070404441d41c4401c1c09a40014081e1681c01d90280f006a00c0e100840c000740c00c4060180c030001c962030030420011400c4440207020107010b04020018401008000200c85049442c000b03003c1003259074a01c01181c4038068005080401c41600c420300c01400600d4018214250500d01103101c586524807141555200f9880003d0100e0070131502481e0703203400c00310701c0360000d40081e100b00d00e0401d804030048110f40941d0000041c031603440c28180090b0409100710340d0310840c08402040080c20713403081c80b44d5840000340124071100c0104e002d5050304441b03a40e1 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 596246771 1250 596245521 596245543
    0xa030c05071d06030f0601030c09050705040905071214071b050c060c03030117070e180115081005060609061c0b031617010c08150607020d050a03111c0302030603 71
    0x25181201072480c40300010000340c45144c400c0c03050652144010801040f818100c9034007840000b000d51a200e251400f41030f0040c0320b14107001e420b0100251034031403402581c2c414407140d40c1e0121503900032180d081c110b0780014905d2110300c4900b03007004070039078000c60124411071481c403034041c2580191030301d1440c1800300d00007d5048000840c80600420000010b10306850001e00720400014009240998a0b40144640c01081b42e00c40046103503058010300030313011041c0760300c004958403011320420b40352503406521004a9038410710000e442840d8603c589600140102c800b0ba24001c036140c00500c0030700902c8051386480049000c0b6212a403100d92104500c0c24014080e245200194000d030326070751a4900c555032041c4a000010340e404c240610510046860689815545880740c40786282004d1149003450b82203e41003000a0160b503c0c254141c0340c1e00d1181d40103020250492800402003d40045942c1a036888901d041e8000300400440901003000c1d4030300161a6511b0b0340c0000d20340f440d4002 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 596248021 1250 596246771 596246789
    0xe19030305150108070509040618050405070e091216052e0b0a060810030c0b1e1201210b040507081908040603020306150703031a0d0201200a050f01050601090e090a030c0507 76
    0x24046c4ad4009180c0100b8031440c050300c2529102c0380c1e215060205c648085940752041e4200b11110b651104401b4007410301084425940d02e10031a00d80e8800c0c0c5003c4803003034124400d50028071500c41e0810340200301784130b00c41d84600500011040c0300114416660a000b08402e000e02400043d44880307644141c0002150802007441d9840e58444160b0240e0313015004920455a280c0501d040101c03c00c1d0407500c0d41002440440c5160307180420582408002018202286844800b0640810984820a40181d0140015007400344c60070410a00d42206200c1d628480d010501c41c3d58042203030384c0700765000c07104541030141e9265038a400007044201d00041e00915a6000b0510f101410350690284038140030026408150f4220071042120302c2c1ca09420083c00501e000c5051080240c00c01110340300a0420411032700b611340c440c2d58a0781030040d081c80401c2e20341c0d135800400c080307580c4c001c0020004020a214141c1142000c4010507140e0701c081da406002e106080c4581c000b00282009004002c103c0d02d4 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 596249271 1250 596248021 596248049
    0xc08191103010909320c0406121401020c0a0c050906010809070e0a02070f12090b16170c010501032001050a05040e070e0603130c0e070f120e190303051501080705090406 74
    0x940100781144a42c5d003150480c46024042c078902d00b4a84240819035840800b115a082c0c0c5540d20341c2e558000c201aa400c0c3c03035400788014852004100000d1100034443c500040206050005000c003440d80248854104240c10081c4507034500c0200744241580d20580d46940b050381da00c0041c070b01034443c1d00f070300801980c040c8060704180a001c15a0f48807020081c0ea8000c1d4681d41c40e000c60000f401404004098070964540080004910071101007501e504800c6883c1400480420542116404d80c426034034100c14071020807124070601656410540e007400d00d03074148032071804024a540120b00980444484c100e000c120710754080c030707010340a501c0010440c41d9070b4540240e803062081e40d1207c080340c002061600104522004802444c441c1009544400015480a9044902450103241c0d03d81882e40d4810040c9401c1050040500000740319443d07044a00c00c91400604075240103208081c0d004901102102907030b48602c00d190007120624040d5103858800b40060010041580541c0b80740c6209 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 596250521 1250 596249271 596249333
    0x503030a02030f07030c0e062a03212a090d0302011505150a08180d09150509031209030f011401091104060e060706020c010c08191103010909 62
    0x960002c51040040c16005030090322a150700f41c080c4c2d401040b1010200b40c011082200703600700403010308000241c0c8650400e1415016010814401c046010340c0215000055021200b0010003442c603603003c1c1480c40c1e032500b45424100d60700c0501c812011501000031881c5442509011102640c0e030591005100d8001c140040ca8003900030498241048003400d0510b20000c0c5c14548102028100c490742d8018510309241c9450860b07044000604544881c803141520035400c40341000180d890110584484444070f040a00d540e8010041c141d442c010448100544095038070082074204070901c500c5245600d8510740c10000e400c0034103444000e5410341c0f0303058500d040440b104054604075140303120104450a80413201c00403500c9180154000310340c1d045200b0344c1500b8260300409000f40205001410700030310500b80c9007900c4880d07030040c00291080e400c2c02216110360b42d6010011280e090100810100e04c81d020100c0d00051003090500760740e9003005401d12140c40a8803d0041c504c2c000343d1050110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 596251771 1250 596250521 596250541
    0x20903061003034d0d020a02010905041b0309050c0414011401050703051b0102040905010b0a121a0906060712090f09051003150b1c02091311130603050303 68
    0x141d1200341e0006013004410800070300605203820700c80d031005603004140d1000200030040b40c810f250740015000d0302c02240340d07145042803080844456666003e840b8021082c00010003044003a0003192040f454094035407502a041614004008054140841c442446003845400d0603201c0b0f28442e0011700303025120307408469050085041e01c81c0c2405500010b010840112031038010001c00034040b0b50f04010352445c1c4124462500c941d80080000581340c26101c2d10394405441080e400081c4800300411515106904100100c1d00550031030360130000d0f4800d51030011174a00355a1201c50240604501040450301c070320702141d0303500380c000c15155201844614002d040c20228411007800b445a042c02213220741b83c40c0220ba004101160880000c01c2c110b46500c10200132591503000e8459640f0071004040c2c403114074100c0c00b01000f000c0000110300034010b100c2c2a0303000038800944003454145480000303e00c6411a0031004055880311010283d940007031009020a400c054001e1001208100384a00 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 596253021 1250 596251771 596251801
    0x61e051003030206160504030209040503090301140114041e020a051201120209100f03030e030a051006180e06010b1c0f020a09080a03090501120f020c01020403050601060804030c020607030302090306 87
    0x4800d50864803103640d00f09002c02c0d04405141c40301d00044c810401040545841450ac60304035000d101501e103402480400a400c5948000d010300c1c1660960004000394460121094580301007503805002c542e9000103907415581120441074611b83d0302042c42a601c5214400fa60544074900c1c250203034950f1540003c2440c0c00702440c04a104026170400601d081042e10032200803158400541e110644c259a410341d54a000f02c000300d50548542825074000c03400401901c0e05032070b080e840004890341400321440d0800c0c4034404448900741002c0010307400800010342d082c1141d41140070b0545602412440003441500c800d01c06c00d82608100c440b80112040e58000c0104441a07214940348581c0c8407291070321585081400b40c08132350b40d49820000c1c4d5016081c14000a0b003040c50000b160304210034002d041380c00007181001c59a50209041c01000010440180549040d003004400b0b49460703900100081004503000740581c41c0802d0010405009405840c0d00b440c00900360341807440e1030700350140560 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 596254271 1250 596253021 596253023
    0x604030507090b1206040209070309080a03150605070819020a0b01230f0d0210030209040e0303090708120f0f0405061c1104060203121e040b07030f0b0d061e051003 72
    0x14a070007140c56080c1350804500e05103401e00c1024224a03961a020054161001040141071507140d5604100082e040c40c000d21a4203140c4d00c00041d058a940b403041882c902d0780c0c00000500404000a0011071420003d80c0e40314060030200b104107018108040707092052007400100200d103040c0011402e603180b121008100000108049000620360080003150b80580340b0060b0441c502d2450304003d400c01c07030f110303d8402e1030364103016141000104c041402c507001004091070b65000401403007202d14081c80508010302e006d000900c010070045085031100c1c407590701803416101000500009081040b401d540042a00921880d255200d1901e980e084c986030b84a1094020324001d1181e8080303d800d01542c007581d40960045040039140c00850301400c8010f4030122562403206d0740c2410302c2210030301d1244100e115400714500c80c00c020300301806948003914140310882c2800d00d0a10f05441d9002510311b40c9030883c001240d81c00d9613940e8000c65801c60b0407502c00c9030f07040508020315a954040650122 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 596255521 1250 596254271 596254289
    0x91d0105060f1305070e060f04060210020307090b0c01090606151803031d0d0b040317090105060114030406021303050f0c040b0904080901020304090c031b0e0114030c090604030507 79
    0x1a56403001008507070701c03104054503400300d290102903410b28504e601c9640e2181044c10303d49581c89019000401c140c02480c00d42c0c11100d0000b07400d00c60983c0c140014000501160000e6095007001100504003072040c0c000c010200e50b002c036a00301c130b9500941010828a800210800c041e5868480d000e52042e4040c407d00b01089540302004010483c1c094910100d98160f6211003200c0034038080880b903060044200c030b9000030512128004201101d400c0c901503071003a01e503c0b0320030406108a80a140000b4005042031340741c0760401c07001c0c1c0d81040d801c2c4507509201080740c1c7d8a030b59600d440710090080c0406c7c01d0180a1003500407040010009060341400c107018102c0b2485070b21a000c100589450010342c6d500460910302240002d68010050034906105006490034280c07544c44810841c2d401c000b05034002a150340d20540003c16921603007200321011325150051028603000600960f04a8141c010700e810f0000000f0300d84441c24040d03810190000f0100750345c541e900c0c2007440d91001140508151 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 596256771 1250 596255521 596255531
    0x30f191a0109150801090e070f0b030f0f071e050c060718140f040c030209060a09050a060f1d01030b060a0816050304021f0306050604030f232104091d01 67
    0xd006100c103007511a0b0350f49648001d800d038203249410010b0107103005912030074415000003098840700d12078420301400141810320f440386400d1807440240070021303000350032404200080c0002d00d540003441c0451008640500e10003a02850340c202c820b407240c4181c0c2c04031781c018071042c03101c5194046101c520303699101902c04c1110761142c42c8440c2e1500c08a08141c0c1c40988210441d900703040c540c00c00d0400403180d05005090681c1c54000c2581d6a00000700c40d000502c141a0921607483c011002074044e0020b440c14a070025000200940019042d085070891003a0002c0480c242d42e10030342100300c40c850050035603900c41c4502c070b00140c640c100680b08084440100301041c001c40d48940d058a1150b80c00038643d404000c0d00c0da001c1c894041450207040d08140d00d40324007140c50389400b0001d00046115242c010544801390608115000200307040d1802c0b04e00006c12010120000282614101e140c8030b4540310312107485811488901c5907500c1200c0c41800d0004443c42017981303202c5211102091402886 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 596258021 1250 596256771 596256779
    0x71704110306090129040f0612120306050a0506031305010617011d031b070503060106050a0e0136180e16050310021633060506030f191a0109 62
    0x826a42c17401c40303c19000e03908400c0b8150071540c0384200104000060400100c0581c00006003056030691b8000034041c42400800004009071b00c2c000c3e600d20300461804100d06828000014008902c0d40710f050700c00d08003c0041045681c03410700c0e0340c0e41035501c94002c01420b40e807559207041d81d600682da820055440c0c103184034005040d500d51603c5800d160b60240d4903240e21803e0a24040400c07440846252003049004a81900c003040300c1070103805a611495200d0300406d9006100f802040403503810460806404038451038000e904400d02c0c503100c6059054058000d00500e10303946217a0190a43c0b03c100704604e040700109500071b2035000017507401c0d518100e103400f0742d01c1802c417024882c868042e8416002010b030003655030301030312180204465600543c0242d4a5400100b000c0c90424034a1306c2c0c0061142e042040e00000f00c100c0042001c90a02c421460240051603038040184140d009001840000701400040905801a036003130308010003480741c0c1780400c00c4d403220b0b1818040e4003080303070040041 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 596259271 1250 596258021 596258023
    0xf090503010207020310021b0a030909050115120b04020f0409060e060a0b0d020d06050d030801060e0d080909040507050a0806060108070c02031911130e0d17070807170411030609 78
    0x3d880b680c0140042c0425034152115200035884215175a00407001c1065003118840f0500c40b0501c003a0080e543c0208280c10308502108580060744181c201440340e02102c581581c11090030040704181d07100000e5105080c00208000e4800c580c038851600e200040e0104030344074513900c58010360303488171030030000c0750350302802d20140805c0b80c0a440002881407040400501042c0c0003010191100540859800e59800c04212280d0461340c041b4003203240d000050111950100c7c00c0301c801d090403210368509514503115207405200d902c001901078250540000c0070700a041011030000c002c0940202c00482e5104c1500782c80311800e903010383c00100d6803000b01c0d400c81e00c901d0320303090729075001806031603044070300e030389100074500024022181e00d00c000032841050340d070306002c001940d48800f03002303e280d42c22180040e007884040e000c40c5080c40b03036407a1416000c2814000c81030341300c02a0704200145445583d000d0b0351000310700c9521414002c0d40c03400c200070005060722403000a0821b504803843d81c0c032601e0402d = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 596260521 1250 596259271 596259277
    0xd060e01030f1103030912010f0b03010b242a01060603020708041203110613020301050f0f070f2c0f04110a032712080106020a0b060d1a070f0905030102 67
    0x181c03036140300c10944400700c1c00030f4002c20f0b000d8100504072440c0800c24004170702d040c80d07103030f480e081d85075910309280341045c625009010078202d0440c02080004131540001d5845010300300c04170b0410000400c43c14820038500c0c1111a8a0b05408541c10070f081800c0c4402c5042c288840700284d15402d09100103007070ba02900035035030100c0c2d005043c0341c2072038244005131780303e481071020503010032201d488075100010041c01514012407000c40841456003040c0181429103602501c1e5150b519a1402088400c01a11107441d401000e1450b241c0020041c180741107503180c40003ca0701440010b0030348044004050003118020720398050b51040b400d074a00703134100011940c1100c0c40503c465420040c6006080c40780d401745480c01d0f40c280c1040d42914003013454188d41c07400e82c6012101b490492240c0903401ea000f0040320700400c0c0c02c0c401018003a00e642d50790b828000010381582c0c01031583d5480c5204001248220b40300710950740f6100e568604d010390000302031610f5180da500108015001c04a42410f0600032 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 596261771 1250 596260521 596260523
    0x1519300507080d020f07152106170703020d020409020102150a061401050a1205070c06050c03010503120a02030901080601120207050d091208031f0f0803040815040210140c0d050d060e0103 82
    0x15005003484d081c4480d905c022042c110a04014410091012305803840c2c4400e0209001882e001a02c1401e00d50143c00428070700024800c1c03640b0840c000c000513629000345c150202d0b4180e40c041241c1c0c1c000d200603468800784074500141b2607100801c004a10001d680180225550054507a0004102a0041d100c0c0d200c0e85203050300103030000d8405104c2c604c1581105802090070726183c0810300f0551205001c40b0740696924a04410000c010232440c541000f04a070780b51841c2c09030074a08501c0c060041d590748142c0c4507072818060720000040c0982e00403c00c171644041d41c000295500c082500d413550b04c0d80c0c0000040c0d40821000d1401080a001e240206880f15a01451540c91500c941c070f17258601028003183c548a101d0b00c0d174400700701ca104481c20b001c001e01c0301c41e0003035407550309280e41c082c1841d03070741103045010071082810400542c0d94900860149441801c19025a1640941320b42142c801c40200040714883c00c2c000d45001a445401880801071703480c010400c1580360103486040300307002c1c44 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 596263021 1250 596261771 596261773
    0x30d030e0d0c02210319200d1707300c090f091d1510140609010302030901150f0807050d050601170708151519300507080d020f 56
    0x1109404e494242002c0c2c0481c0b14042c01c4a00303203000082c2d525140452900700340c3c00210300e1800014056951240707401280d5030b81019204030484414001c3c400060881da0111640c1340304003040c6024000c4a055a40c42c0884940c1100348034109002442c0340d1014640b004410316012201c010b041c0f182262200756007115041c10741c4940341c41003c40180c109840303c80c0c1540700120b00480c0d85241048404034211114521001130f103041d090740c40c105a42c42d8400c2e8030341c10380c1d20702d241d92071782e1180201d424100003420b0068503512040c0b9003600426090080c070941b4400b44d1800f2591100ea2180740c000c44441400b1103000e140c580c4148114a0120f0500426076400b074801804004000384145404403643c40407a040309540f04246c924061030190328207400702207802030011240b03203010900c1c4040d40036030b0101150f2804000310702d500c101522541d50b40001c1c1c000e04075030340101504c00308101011a81c2e03401800000d81012901c2d88410b11450340b06109846003144c0e1b047c00400e40c6104104000 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 596264271 1250 596263021 596263039
    0x30203011e24020c090907032d06091e0602190507150b270a050606070203070603151206021b1501030201120603050d02160602120304060f0b030d030e0d0c02 69
    0x581280c1107881c0e442d40710055010f40c0c0021501501c83c50f12662007400000024024107142d41400452501707440c0304490104c24040410300b20f00d91429445c46407070750041c400208405a41000c83e001c0d404040310b030210006200010b42400714940192072a03152220f8504e12141c1000400d584612510341e0052542010084280e005895035020741d040c070303030091700c3d030b01c0f08501c2d880031140d80201d103610112540030180f0601404407510b100300c0364448000c0e5103180c9020650b0700000d50760a0103100b04410503840706c84c4014200140c500c1e4000502c070305501c10400c08410314102c1c019401080c0818502aaa0a0440500f440000e01540c01401140410740917900310340044691284000d003618106441d80c00000025804004218484046902070316451407016606401e56007150f00801c2194007031014403410140420072a60001e6110a0014800c1d4254000501424080e0f010607814000c805007140c029805402c00d50700756900100340e4190f8000090259a01450040040d401151030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 596265521 1250 596264271 596264309
    0x90901090207081c0905071508162307020306061804030c020d0b091c03020408071e24110d09030807020406080d0f0915050723010507030203011e 64
    0x39500904900707000d183c502d890701003410200b40d80480728031061400c40b80e442c1104820b000083c090ba5020b0140007011500d0484a408010038403040035000418a0030410200c800c03141c0580c9510040c50307020703505c2051003004991000b0325904017203401d90290040c0000100380349003810380040c0e640c1101086540b1078035162030031140d4034610707001280c2100e0041401030100d850001c202c3d01c1601402c006082d50b212800c1d00c0920124081031660600d80180014801c040c0c000c1800400d9a1829121859114014080083c02121640240701c0c88030301c0c001c0d84101000300920ba20200c80d0588941010300480090035650340344a49000000421040050000521580050004a00041002c1407141d00c031000c10b410f00500b5148800805c400141b442696034100d03061000070f0580702054080204076042c0901030b481046401083c551149141100070903d070b560700341110000000030002d5151005c0003800941c400e000700c0b4420b00106000048074020741225605880040511410380511 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 596266771 1250 596265521 596265539
    0x509010b101202042301030f0504020303090d08120a0b03061b0f1c060b0c0c01230304050a05030f03180c0a210503070f030e011e050a12091203050c090901 68
    0x202e4610030704107540030000001c82d89402202c800c035100102003202040904036001504860306182c6048500781024100300240e500071080d58050103055810f940d208010780382c6281c4504c5400350b80300020052070148585070010b540b2085c41368030164200c40c40c6440f00c1c80c1c2d0070000326102640354171041c4100700c166140400c1d40080e04030210007002e12501025442050802d50709542c01103d80a0700109400700859010001450070b40020b0801851a40c051611550b440311130310580c0d05034000c000701280030030030200070103510705402c1002d0700d844042440c00c501060b4800e88a0480c50f00b803001d02c084040300702080360320345007100a002c611042e14050008640c20500e600b40d0541c2c03094401e6034408150140020b00c8614030035407103a40035007214039010f407280707101112040c100071024607a00d102c05003001c5048048101801c0c000d85488005104850480511010b009030b5401d01400f4410003405403a210120a015242403010b80e0703030202844c189000b80c0b07020f039070300c054100c0040000d0702d6 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 596268021 1250 596266771 596266787
    0x30307230f0f04030f050c0a120b0121021e09070f02100c120f0f060b040302010f0e030a0c12030207060206090705040908190c141507030f091407090509010b10 70
    0x30140d00b2a60074a03640f0b850b03c940c07030202c5403800d40b91904400c3d4681d0b41352070074004000c054202c0d5030b0b0004131b24004d5210400c203c58140151140008420405402903010300100070220740c5c020092080448805400c40382015003144250090565101051a060080f0f103040b410291640c020121200e200703031040090011282e200741488584142c0e801090100d004103161800e82403400f042c5400304d09414030449109500c200710081d018803085c0010307070b840a18180d81010b18075119860f8200b9000007420100b81543c000c0480c010303e64000349051040c1c00c0c150b0268025000d40c0c805a07560b9906a81300c900c216000318079a040184180304e14034050b0300c00590306000362101400c00ba500c9182102a00d44c41c092800440e0546040004128503210340081c4012020003500c40c0d01c0006211076440709e40038160809264680310200010343c1c2c0c59218170b4009422400580c600380c544810251501d1240c05440000750504000680481050081d000c0e500b4000e4120303140340c0103074241151102 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 596269271 1250 596268021 596268037
    0xa1a190b0f13020406180e040209100f03031e0309020f131e06050a08010608100e0309041d011503021503100803040810050a0903090b0c0c040905030307230f 69
    0xe881ea5a0140180c546864030b82d00d000e1034540c016035590601d41d0140200c8000c802003c00301c0100d110600c01d91404103401e0342c106606031000030464540808441d000c001e0b83c0c100111401180c4400024103901c1070001003225404850202c9a892a00040f82030745c1d40600040d4000c0c41d0783e04210321a050a2448a840f000c40c9000040c8401c20207454a10101000300703407a0100e03480f410140b0852522600707150041551600801c4498030b06202e80380c58a944103603d802044c0d40d203c2880c8280350034002c07204800b0000300304000c0010b401280c1814900319180026556103041c0a4200010801c01d40382c051704e0b001050b9000b04140c0071042081a4401030101542011103180010400302c1000600060a2000c01504069030b00c603440340e003291320050501d18805d0070b0022010209401c510000d00381c44500d00c80c40e0b611108504803500e0140703200c0c001d540080c80d16038000107000b0080301650003080346641e60301c011030702004890384600555400d01c1c1c010008102128601c41c40c1c00c010032240e = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 596270521 1250 596269271 596269279
    0x45040207060f060e0610080c130b07050706030b0301020f0306190806040803040203010c03062403060f1202030d080f0f07200307111c06020315120a1a190b 68
    0x440c0d81a0307a1041650b00400c00240c1e1140c55070802e21503588221a120762000090310040418000c51900070402d10001d40000d0052340000b41c00c1001d03000013840c1c8006442111840340d510009482c08a40d00d62440c0702d1000080d1602c0d040040740e2a048c02103a219042700300e82c041c2152500e00402c0001011102d05020514060b040003a030302c142444450702c03031030081c0a116107d10782401458203459008011f101090b1415105021010716140040c0d10b90a5409055602501c034050075070061400d030700100c41d6100c101c03000041c0015581c0054903140d100b80c0a0740c001040c54541540c45100a071811944006028002001200c2210400741c0c044020301d00b6081c0d070046616048400c00b100e0b0506055504001004401d00228240c1003040d444240c45608908592848090b02c1c200844001850b054001001c2140b04407544400c91181c0700080c96524820440e030703803460380c1d68a8070710219011100002007a455102015580b82b00c1c400030465100340c10003030981e8a00600c1c01260581d40 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 596271771 1250 596270521 596270527
    0x80106060e130b0a2303160b09121b030111030708060d0f0b0c090306150603060409050f010608011d070b1614060906010f0e0103050d08090712030203450402 69
    0x5542c4c0e460003190003c1c4045443c8405d00c4d060b21202c1103201e42e061402c5400307607214644201c01d4005400e00281105e00c0020103e4850700501c000505644010107000d4003445002d070422402802024002c06145080780208206041c0720b582e0207075400100c550700b001c0f60075800024410b0400309a18400544240b0060100c0840d580c0c9a8a0404064a80c0030310310300040383c949880d0804024060b005418550803014040c2007100084582c80018071890080d5120a0110b082200c1040800d104894900c02800300e10780b1440081d009001d14906070001080300b40381c40c1e9803e0000301d0041c0560307810300041803820100e070b82210b512071415102150200b060650030340c01c010040c041940a03102101c054200365240c05c0c140c0d0001401904410444090b91004100007000022600030207880383c10041d4466807811402c9090100940c0300d02c450101341d03041c02d4100340d03010004100d03110351440c05c084882c400c000000012449000d8182091580401e02407074a88001c0780021010401000545 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 596273021 1250 596271771 596271791
    0x206040801020406231e090a081507031401140103020f0d050403030501080f24090a0c06020619110a11010f1409070e070206010e06150708090307080106060e13 70
    0x100b240d00a9028200141c0000c440d03507a84070160740805080e10541ca052401c110174425001d405a01d245010f01c0500400603c091081e26590840c1700148141425100c52902010840d4403103041140c143c40024035040a98007001d65a8440f6170507600040b901c49074204102006400a42c404020030605003c00e1141d0749800c1540d000e4207214034800d03900441c00e0b5141030442740c9800f500c2e01441800350013141242e441c011003c41030030803000c001d4070307140182e0315000007003400c02600600103000201c99400c0402d2072500051072030f0007035511441c00300c8050369030101503044491007c10700d000f00c8010003040b803d0a1151703030545640b4540b20000135514038465051403c81c1c41032036440104c0200c1d0310400516090502c54030b00100034422550410b07140c8141700a480b40414003c25240082040110707415031114000074800441c80d803501a5a0106410b2010300d5410154002c2d200740b080c0500412000f4060150b60200c0b82c0d83d0300c032807134039402400420404a04969605c603041380e407084640 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 596274271 1250 596273021 596273023
    0x806012109030212040b090108100807060507110108010609090c140d090b090105100b0a0507020306070309110d0804150201180f030906090e0606030a090209070206370902060408 78
    0xc961020000001080c84052801900341642019000c04948050104020840c00041164071b000d6003440d01c3d070200e5450148503065011681c000f2103162080603008110039400400804040e07008000c94440400740f100111102d160074006d07030001580042d010054400036400c042944483c3d4100071542500c54080c1a1440d008800c50b80145900c0d07294030b030b09004102202c1500a4039643c02804241350544030880c0090081c460083d10700d1000501214440c400d4040d116a258000c01f42c800034104100b00402910882c202907403c00b62000c0d0122240c9041c034031110181e980700702d5150802d4604644c0c0805980040401c8003503548903a00b10404d03e0584450702c1c5a5407140440c032002c1c604a0400a040341c00c00e40000e02130041a0303405000300d1044840d960350000381101e0503035a84c3c1c0c440041c06d01038201050001e42100780d090503c88266004606607105040c0c40f003200300c1e0042070b0075611105e200750001000404804140201d40e03120035801508615001034407441c6010341c0c50740d440e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 596275521 1250 596274271 596274317
    0x60301090b070f1d0f01110f03030f0402090702010902031f110c1c09140904110603151f0509040905070b0310050a090e030a0c140304080106090b100807080601 70
    0x14001080900c0180409130041081c00040f01c1030000341004c001c080d800304100d032825044960612001c202003040d2098204519480e500c1e604003500d4807400c25004600388540156000c9120749614030015051500c14801c001c10346030010001c2218400742e00304160041e40445240c9041034a0300140610f502109c001404461804401000d080c400c1c0c901d80d503501c0301001d82d444100252000f0420211910303801902214100300c490038482e8442d4503141840c001c4140c4501c0d00840084100074110004000d69071a018080c2c604140071042e036405140103a007122121004504140801c3e40c060503d640038032a000d1080088070181c549903141d030107940d0400c07915500d00f01c00d8808140a070741440c080080051040712828001040070134041d548a0103205e607042c1c104078000c1c0ca09800d001d0703605041c10100030000156603450f52a080020f0207005180180f8010070f04255100c0c00d20700300000902048444c0d941d440c1402e031102c1d20115206140034100c01d040041d00c150003080030381c40c1c00708 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 596276771 1250 596275521 596275531
    0xb0f060c03091906090314071206140106081e1905130302010b06092d040e03070b0606070c0315091226010305070b090109030f08120c090102030f03060301090b 70
    0x1103407504007038030410114601c10000340c001091504000c0062981000c484c5081c0c3e98001032105181d1f03204400303549411456031102032608080a251410701807190f103d5410700d000c4100564650307803203100a8490401c20b4440601c5015401e206d10132954160a01c15000008146824905984a01d42405544090b20391081c100c6100ea0360208158091151021444050721500c1c1440001030004c1d03060704865a01c0c7c00030318044076020106604c000203080c2c054000602c10006001000d4901d690f85d0044070701120002e40346400700e00d4a01d031080c00e44040c540c2c461204900300b07043da6540d41d10420a82152403072640c80d0810040054500b4a040d4201951552084402d20003102030780d501c5140c9030351444643c508800140007065000c0340d80d2003035400c25103c055441e840d1200407103048070b0701c0d84040c0c030324444908480200400d000003000840709030104000980c44110b80d071401846042070540c0564010088100c02078042c0c3d010750b500a800034000140307080702d0388514165100c1221 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 596278021 1250 596276771 596276773
    0xa020d06030b0f0a1b05130810140a0603020d03031d100e0c040605030a082209090b06270907120c060f1103030f040c030b0a050a0510031a06030124051c050a060b0f060c 74
    0x4284030070071070614403603000d4140f000030300904dc559004524442002c2002408041e160700d1007500da82804801842050070150494a06081c034422030070090907410041d141a028000740910941341a0051809803003000b0301411010550b0ba54558036039100880c0c2c168030074000c6000b01c00d2000c0343e110b40e0001303121965020401d1042403801c102c10042c01032049100300c041d402144800c0082981281803081000340000050700c0b01c2070f8041c46d29030329502100b000b505542c4010b0412085200c1c0208884140d143c80052454401040c0d429441d03a044d100d01e80e0f8002d01c0041c0003500300c0440d25400c01d00459210700400e44a0325110413800086410010305516442445140c0d41540300360f951049c25280f1420010f4255a9000c0c100049408481c282030040401329000d65801c1d802002c8400064044200b0040c101e210760030304545611800c0e00c900103503141600b0540ca90080b44c0559030b8450003502d0750030b00968904004100c0d944a45400c000700315021006030301c401004212408441f0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 596279271 1250 596278021 596278031
    0x1c020a08160c0b07061a060f0706090c0b070606150e010203070308130f0302010b0112060503030702041a03070608150405160804060b28140906090a020d06030b0f0a1b05130810 77
    0x40e81c50140c82d000b1b0b0484902442080041948500110040c3c8120303e500c04404265060313a418500301c00600c0c2e4202403c20107000803524104a01076001c04121080c0381c00203960b41c106c4c02c2080d5000c4000301801409600100709203400240b0540c28141c1c0071070035071070340c404c0807004c0d841c0c00f843c8075002441100540c5d9a4002d0349400c0d1b030489103c00c0740b07010054003480200d007880003180c0c80380180007009004540300e180c02c14000750200301d1741804481c041d044500c681d6940400400d80e038010340380c0f010b088074003161000450604d07018041c891546114581107420420200700d400e154001d0080e110f440e50380f0313920000b81d510000419508008682c100c218684520848100b8041c5607015442482440807000620f0300c40c10040c0f80e001508071800c11a0755a8101000064401d90030340c203014510f0f1010210401030081690760080300781407400d010315034401c54400115002c600380090f2070000702107000507861150006241c912070b00004280d49566420301d0038075000c1c042840080250b114 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 596280521 1250 596279271 596279291
    0x80312010905181009030e0409060903080c0f0301030f150609060512160608040c0305010c08010614070b0f06150f070203160e0c090607050f1c020a08160c0b0706 71
    0x502925030041d44001c182d00c03c030041a01e056640351680e04103200c02984540d00300c8141801008202241a0050000d00002d4220300d4410001c00705140e045010901c0000412942c0c05100190350b418103042000c2031035a425501e03051b4200c12007800407940084140950101e4100e6070041c3e000500c400705001c00c6003400d01c03040101c514120006d400155114a244044010100a0500c00c41b0380e141000d5005844504060390402c4664001900a41c01c2002c4a10a90707801040e25040310b4450303aa00c0d030540b10165554440303202d4a00c0141109555802007040d941b001c900d6a500400020201c0e5100071182e181c14110350400d01c200f0758030003800305e480e1040d030400b405a80d181034840203401e500c2c00c1c2884100e14000030050b084820f010004035411965440c0e413805c850303003540c12504841d21007200c4140c44e6950303200a0800311202c41c1500c2c1c803080340c9000162074100e8030352148e0100c0c20710a048610190501d8102d10503181c46c0003604c00020107800c440000e02080303000700400b2940f00c3ca0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 596281771 1250 596280521 596280539
    0x15021605060a1d0a080d020c0706080f0f160807111b100801080303130303090b04260405060a081e0f07030608030315040e120a030204050f0a050d0f030908031201 71
    0x403260284aa00c0300b4101465010100c1c4d00c006a641c04906240c0310481c109148000f030040704000b0510b440752800125060380c00490003440381c084102481410360b0703958546c40306c480d01030f141599a1480443c400440320300505009501048501d054040d030001d0024861500300b040c818200c0e102e143e03011012603403d0080f448001c1503110b0030094820352501a150360b40344001000c2d41c415075000482d1204140c0301e0340024400540003580d00c151828036040000c02812003d03a4030210040d10302c4403d10442c1001d094030119400280000c2c02d200140500b9250082c00501241c1ea41289002c2542050301060700240141c3d184000e030156494540c1000d421503900307402021540c1c1c03051082081817840b0031b021644548041d00c01003910900c0c010b0b070902c2c2031540c41c4100e50050001c2a03520300c43d5403580c00f030b100301c80003111148680300c54041032088030346413802041c1e04116424901170200c0c11001c07020118134403d240145519035940525130070764001c00d040141228600c4010409000 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 596283021 1250 596281771 596281781
    0x20c07080c01020303130305090618090604092a0807030303050601080c04030512160b0106050d18111c0b0f330915040e0c090c041215021605060a 64
    0x1000300050424000450010350759000c01041080240d111026020405100720295a4429400780c0303066100c210f0f580380d41042c1729074030007524000c110140009440d4a01400707444640f9030004e02c05030103c4040c81400520080c2120b0062041044a10006542408005d540000c4d03020390350000d02c90821100041032000082c0a007110a40c0a01090001ca54086414580c0d0a01d00e1404c40e6610303540c526000f940400e0b000040c010001550001810700d8100c0014450241d0402041100144450306601081c0b01000d014080045401641095040029a4561050a8044000c900c0c45156607006100034100c41801c0d2106ea0f00c0280b00840828080241558100100401d44d044c54043c0c046a000d07004d50324180304001a50114001200e00026943d0890300904280a0f98082030005513075107110005e4180140320090028450072105001e940943c0c00b0b4040030559018691640000180710b00d0f00110615420000c4643e240b10754880823030001d2107100a00303d140b034407880c0076048503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 596284271 1250 596283021 596283029
    0x160302010315080d2109030e09091605040914160e0a020f0a08060111190b01060201200c10052404110f130b04030803040b070201060b12190f020c07 65
    0x10003054403e101c20a00411a16655225460401d0341d02070107690015503030344001c4440d00c0e12480c1410701d0b803d05500000440005030140d500f60704c603031035140c451a540e907940e1401020355141920180194905504a880303403501528081c80c40c100002401ca0803c2c4201c21042d044c0303010000c040003240120713811694000302001c0300b1800e04a2040d440340240c8140d10351003040220405c00200907a000b07095a03140316241c2070484035000b004098111501078142d000f61002d610020000801c01c3c414020100070880f84c1c607165203030803003a59140c030041c0c00c880e40c0d540700c1d40503101e4200c600c262076100b410f20414400b6038041c640c1c01d03601d000380c0d1003000400704180a142480342c000d41c0f20380c10303004442940320407040561741c0e4000c00d01c0d4003809080e10740141e441c501d0000b80000174001d811014501960141e100e43d60075443d5141d050f4200c03241481015190117050000030b0842ca900300090b0b90042d05034450300d03684070380b0f0b07501d031011500d543e0382c0707034030f109602180c001459101003241e030020b0 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 596285521 1250 596284271 596284301
    0x801080d05030604020702120601260d0f0f020f060709090f0506010522030803090d170f06060325030c0f0503060a032904030f0f0509130e07081603020103 68
    0x1085a203400500307a100061285020f29000140c0e1011500c0b08090380340511544400d80c0c0351035840310161810820840350101411f42099030700315154801242401851103917840b5030780c000c045c00f8400d96088550400040c154000d1b0074081150150a0000911841499990f210074504212400007100d420161088185d440d05040166590704801151840700e02c001d80000200300101040445008a8200410407c000b10502510a10000c0d0071220010715482c3c0b14084400400801c1c4c00d0031044a1421001100102182883c00e12800450300083d00f00c00b4042c0680c0b1041000c5880c024100c0044e00280c0d9610009180c0c540c4081203c40c80001d600d44a442e6041c0340340010030809150001401c0d03203407150381c0d03044001c01c0d40b4001ba04220000134105000c1c40e05040c0504401112b06000300810b81c500640612184540b04803a0b0b10368000b8143c561151040003141c0080c02c0070107103142c1620a00e01c001c548040100500c04503043c10144119640742184001030545040c4290a1f0716 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 596286771 1250 596285521 596285533
    0x10806040b01081f02030a1e050601080622050a060302120c03071505070204020d020405270a060e07080603010b12030c010c0302030103170a200c0f03062a040e010e07080108 76
    0xc0540300c0180c4040c803000150015031261103018100c0c00914908c00280541164440c88403814052500120f10580091304c03030040950781c54040c055008450840c00c2e407090b4100c0064800c02449902040d0455200040000c1454480c0d01049040e1051460284558041d8900c0c890503d42041010017070120750405101c80200321902034114014903100a108a40204461030100c900d0780c150b40c0141030051084000e4082c131080700407540040c0d1901003100c075078500000c0410b015405548115051000d4980040d5545541120b130b110000e000c0079815520f4000240e1980d40f00c1041d00d484030a044060756070b0b6041002001d08540d1029031120505d80140010400f10382d20a07812200d41100900d22503407031f540c882c0c085511500e5404440c180d0040015640c800c0c1030300003a902c0080c0700513503140c0321110322003040503503c1101b169440b001070306034442c440c10074007070113505603a03030607410603490138a6114101508040026008480c004074100108560280c0c019007003030050544101901c6 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 596288021 1250 596286771 596286793
    0x3020c03120c0c0d0807050d18060c030923060301080c0f0d020916030b03060106200601031112070b0d0207021c0807081b10061a040b030112020315010806040b0108 72
    0x240342c044058203c0e01c100703000c1082d2014025140d044036a241d40c4070080c0c8805501d00c0d84043c00e41da40700030300060305a000010118a00d4040d4008007003094040c1c42e07901d8540e1030a10404c02c16038451000043c5030501400d200302031b40310300c0d010314040c01181020f40724070141c0741e0a1142070040c880301184a9801d901c107010158940765200d58000178008914031a80c0c0344100f060700034040c1c007545c43d07801d4400d40c0000507505500910030310324004509401d000c9508500c846568524084c003024004c0707202800407100502c1c0010351503900f81d100c50281c03446550760f8400d44600307030049840e01d40301d503400141080443c5040c4ac6000354520100717000d604490b2203601c854000340544140181030020011f21035a42c4014a880d05a041d4035620445140310f44540f03078240034000a101d80342481500e9000302581d81e40d50001e07542510f40b2a103250741980c0c46d0403c002c0305d001098030180c0c5c05000310003901d0840d80e00e1445481c060312241000301501e00b4a45000036403001c05a00c250700380c0c3c1065030302c21 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 596289271 1250 596288021 596288023
    0x50103290c090409141204030b0106231e030c0304211d12100c0306090905250b12070801050402070206191b050f060a02090307120804050d03020c03120c 67
    0x2142c2000507107001540e9007561814180281c042005a002486030001c6040381c0602080100103980c07050b0b1501c03c1c0303a66200001c0d44c40203102c3c000c504502700104e0680030b108c134101703010b0600c3c68404000050041e06040086035a23520584e41c000e28000000100400c0c801420058840031040ca40d810000b0700d04054002c003d5420038890120011010788600320b1a1746030003103014544150819035552112403c4403600420b030700d0b0b407180d000c20700301040081e1616040c480d501c2c03015000000b9210f100d04a81c0b856102a4141c1315009100718200302c00305076829100017034200350504030281d410301e04080c030380501601c0e8140e01440c0305500401003840140c40307401c11385682c0320180c0040080301d54500c50a640a034030003003500d40d01c82c10640c003900900200050fa503404c0750300c40041e034050340c8403181e05809034840e030001240c00d0340c402d040400070911300701200e40500d801803903100d08180d10f8800040c880000d006003600141d0000401c2c3d5814901030003400c40c0d0500401c0c00c01d180c4400b0100d07603 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 596290521 1250 596289271 596289277
    0x41109010b0703120605090906060406150509060d02040b1626090609030a060c0201060f050d020a0b0c0a060c030606081008300c011401080d0e04050406090501050103290c 75
    0x50130000d03c14200ea12201076170304010301520004128105519208003020ba44020481d00c0c544960f05001001903100c0384101c4450300742a00303a90b07083c9010302031400d010042e881558018134a0b42e08000c0091615001006002952044035070b40b40d42c586a03052003072005000c02148140b40070040c8032040c1c4070300c0040440d2010302c070648015480e01c96440002c9d00301401000050005820007a580d0540c6d42d040d840101a51034603151030080a89403828491160144003009402001c00c07c81070240c07a5509024200d00310003070048454408413a500d880030741d0075400800300482e484100600c051a084000e6039440380d40501901c1242e85800c0b2519921507014415840c9409510b46030044090694001012030280405071550759440381115402850a00e81c000621409003001143c45080410107421f06007099580802846041c000c2100500d400b078000c94015942d01450400a44280a5180203500481c0760700380140d1004c51071010075400b11442480004843d041200303801c519002c1e = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 596291771 1250 596290521 596290523
    0x12050f0118030309110307030c0f0614090402220605210601120b0604090e030306010906020313090b13051503070b0a092312060403030b1e10180e041109010b07 70
    0x3003082210b90905040e081110756a1745d40500402c9408414017416105c40400c4801401d460020a0f42e661001c540014001d812115059030800c241c04c014601500a048070b200c00c0e0601408407801d902303d1455101e05584021302041d00031503100040080c00c0424180c030604041000514508400001c1c42c5103140744008242c1950750920001c3c6032900000e41e070107428461000c001d8542d0f1948401d0340c4e0340084a03c1c5000605000e40481c8451010059584500086158a040a04000007440501008000c41b5040400303c0f17031050800140d4020742d07002d07076641c020354404550800c0c107041c141445038003d20094181081590390a030760ac1000300c0c08585581c20001418002c0c540700310110071424400980c0a0a10002c1a4402c2000f2800c2c6014900c01d403000c0082140311018400304194260900850803407066018807241450040c040c035a4809280200c0ec0244440340d00121120541112803d051280e040004000b41c5d4602e4540300c040071035809400d5031501901c542a1b01c134400c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 596293021 1250 596291771 596291777
    0x10503031903061502030c070812030109020c0307061a0f09060d030e04150b04090b0d0804150c05010e0f070b0f091002120a050315040e21090a12050f011803 69
    0x4000c039501c1e8401c0e40034002500410407a032a4212450b80002e54030782050090303403034901411400003a81d5400051888607410042402401d42e880e190101c1c009400c840d42424040c0000c11114000a4081c407514219000401180000840b000181310140b600b58040728081c451141c2800714650f5880b1140c1151585882d03ca1008808803001c50082c000e0480c000c0307099821a840465241000c201800030f0700c1d10b00c841080088420300070821030130080030004c0d000e035004102c00d0040441d02d60346201c56240300d0810950740000c2c0c0d921142102c441e080f0344400750300035032040107541d001845403d00401207a8107503424840d0b004100703070700c078442c03242101c5c4200c050b400981c11207802840800c00303504004000c2c948a51141c1c00140c1254000c40f4451200c102c110b000c1106841c1a2054900402d030b144020030b9071080804541204100400110009143c1404901246d40c2e0b4401c81034040c001850341c9403443c51a5180041c034000803c143d02c0d04036410232030741da4a035080d960940c2001d150586 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 596294271 1250 596293021 596293057
    0x207081903020a0209101a042108070b0901060f050d0c06080702101a010806030109030f03020306010318050f010506060403120804150e0706090605090d0b06041107060b0a0e01050303 80
    0x11600383c0c80d041c443c0100940002c0312108000500300000400c0003151000c0505900f0480d10000111241c1b01d14065003601c00188078440001ca003606044056891040ca4140e10340700071915520b08002d0100c07117002e41d5a46a07901030180b00101c14502000341002c1c1c0e4019485521903882241c5080180500420803011000154649208216543d000303102480100b0100d204405500783c10810045001d0208654501040c810300f01486070002c0f041e05580d9500601c09514030883c0658005040c540c1015203a0f09010b0380c102034a84038070b5050744a88020130207811560141829100010b2a06104080600040000c074000d0040150700803410b2a110009a0b01e91410612300c01c0e280d10003040b641c2c03500e1001c41c0d21030400503001d01600d203151a0204102d9403500d040342c0f01c1c80f610b802c550b048039580c41800e001a280a0819402c904018000300388038040d03031a6041c1364ac104100680f1281d03102c1705044400c0c2000010b8034041d249c01c83c1e400e50b080d811300b00400d42d20300c1600818400341c0d03040c0e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 596295521 1250 596294271 596294273
    0xa0606090f1d090a0f0f110a05220b210d0c0b01030f0813030609021201021c05090c1207030b06030604030e210708030714011802010c030311040603050a0c02070819 72
    0xd04c045042d0300d5000041c21810501030802d580c103038894030012036035031b0480c0c1208003840c50708200c000c08603100184a0034224101d0003003041c1011600c0c0f40c074020903450340034510203a80c0c0e00140c50f2411914002c80c01c00b081280c000745152800028100091101100d50345000c01c804103c6a41903d030024075941811800b8a085480d51244040b1090542c420303020200c1004074503085051100e0085514004d0200c0d0401c40d41c0c00c038424070400510b0230340710050401850b0640d0b08280d074840303030203020b035800324600b9800b02c2d1140301d8178501441540c102440900070010040c4029400443c00d0703000f000c045c13034166009484071000181403841400700e80000c14448252141d0401100c0c00c00c420346692982c0c82080664981020740129016030381d4801c29042c0c14070505c19981008404001039000410030380054400c25a5018140d04040c0c0f07540301c7d4005201100001c200800342943d0000340c5107840a0007404851038440d6040440d008001e040200c480001180030f4220728004203951003242d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 596296771 1250 596295521 596295523
    0x1517161a0a0c02040f0c0305070e03060a0c090519050a0602030906040603090807120e03010e010209030c21010501140a050d2f04060b0705011503150906140a0606090f1d09 75
    0x1d42c1c4025800340c20b0410f8a100f4001c2900841c103800500e40701404103885004003542c00242070840680c2560240c000290881d02d580c2020701001d183d81440c150654903403000c50fa21030081782e102d00c0c2140d40790130100071074180b101d026001032420f40b02460411407504000b9505102d80d108050400d40c47e0440d00d4203100e031050860700d00b50b07401281c02040e41081d0401916084984c52818425403030b116a2440064041c004c032400441c1c01005842140e08036010417240d000e008104110503041d820003410700400910401e40601988040070300d64814041c01c00c8884200c60300664083c00036501b1100019254101c01e08103044036400f0301050040001015140d5240026404c0d88182003101c0041c0d02c4800d50003c2c41c6550103040203002100c004c0761240f54807041c61000900700c07404034208200e6034a49a00811440c1e110342404a060000d00d0080700c008407095590141352951039000f00700e9aa003200c2e80c1c0006082e00259840610315262103041402c194020380c03911026064009a18440 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 596298021 1250 596296771 596296787
    0x70f050f0c030706060302041107080409020c1c020105060916020c010c2105130f05030307120c0b0903131406041403070b03190605041a01050702041517161a0a 70
    0x16200c400c5a881d14a030741413080291040c3d100a0b40a0303803420004107212540e040840f508250042016407606c2d207401603400007036020440b0300710300340108004140c0d80c170070102032140301078500c0c3e00100d45801c1c50020001a0344010f898a90321410420f003150f8401e0f00070800070801e0200342080d034440086810544250002c100610120007440700c54003420680040c003a0500071034150141c1c10b03d1340c5540c00b00700040224010503505038414044400012030301000351100300540e143c420701018050386d90b00c00c022001c1d180210181c0020892030510001d40300003000034100359410089200000c03020503030500c505d003d916100d004104880480351401c02c0b0640040100e0075006a1301d1902400c04541c0038030b04503c520043c2d080c802c00150500c2d0034040c1c0640e2001d00c529031104042d000b03005480c0340c2c4c89880101c1c1c00c143c413021b4100490380ca881c00d2000800503110300b403107030030805210f003401e0188404010b4000c0005110900c0104c4000c0c0102e80d001c1d10041407260f40341401e032015240e04ca = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 596299271 1250 596298021 596298037
    0x9050c03061e0c092d0604170d0305060a12030201020f040e04021002010b01090e130b19060503070b0703140c0105150a051014030a0902090903030609060306070f050f 73
    0x2219203000d1150102c0040e2112402c8002c80c0e803802c4081e12898101a0030b4414501c1d542d03400b400780b0316403880700119000025000701d1501c1e45012044e0801001c40d00c5c60f0021b0703002d44840442c05c011200312a1b000e00114800f4070b01d41c6810459854640700140c0080716a005036001d40103044120002c15000b581101c064100010426440300d80d500081d00d44407100715001c9002d81c0907502c4030803d940c0140148403030000c0584400c2c036010b040c0b815000c1d94140081c040100940d10084142c04145034580d4103000380c3c981c1d41c00e00000c1e14178144103030654906030f000a010341c6c0045010050030f20074800392915558980b81c071021364144160b49850600542403c96400d529160500501840044034a0b40740d100c01e6405640d1281c6c0d4004105000724000350200200381d4a0803181e0803521b05000543d0311000681c80018060420b0300400c0c42e159080351840003540c000010f0003010b02e00f8100c20b0380e1111044000344406d21341840d0040c520150b50000700c040c41000315048001c02d001d1826180d401c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 596300521 1250 596299271 596299273
    0x2304150b0402090910061701081207110909100b0a03030903110f1216060807050913020d02040b0318060603100e0c0904150e030f04050d020307030b0f090c04091509050c03 75
    0x10f42481702d03500501c095144100004a041c0c21341d51484100c005010604841c0c90001610046440c030b01c45411640c0b00040c01c4030748020344a482001940c4d041c030315a003c1c1e4560001450003e00d010000c1080310340c421a80c504c1580612410030001e40d200301c6910a50ba0300241002e030700c4003a0808502440841c11070a0752104072012140d149100c00078041c00702404154400000d6642e030b01066481d00b20035600803001a4040040d41206c0c141405c012303541e541c0340c40006181000510b2004101d1704590089200c0c100004180314003000941c01c0034600b000d0650241141e420711030300181d0758074021101c0c0280c154880690407031008007031118800140f009071030068203203001e1030024800003840035960480751421142c450031a400200b50317150b003140c2802d2240784c64100010080c1408203800c04030703410b124120000c0000380049004600841080317040700c2d00c50800000072400c001a0f0656140034904d0181300c0340100c1c0680e0701c81d0541c808403c80020b4004420309209060a9690000030b0301 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 596301771 1250 596300521 596300539
    0x1805060c0a110418030804051216110a03080a0201060614161707050109140f06010612020d061e1505070b060f03240702070602071d070203070c03062304150b040209 72
    0x174180c2000754240b1640c4a1002d44426070320303030b501d0a0041d0150207442e500c06445280c0240c0010824840125800320040c804003c0c46c0d5603070b03560701d442d40c414000c01006035100c0d0020402260130012410407000a540c1444c10090380b10a0703016099142d4402409151201d803c1200404410007200c22481d00a002032005188c5800c0c07a0612030743c5214101c425200e8400c2c0d0000b016400301701541602e000c0e640f043c1141510341200c0c8042c1d00184a070158403a039400300018070340100140400c5c100844441208070b00d02d4000346098410070300c90044140300c820004180014100d03106550300c810201c5141c01d1080381480442d1078030042a0340b804044540030b0b0649038003007040c020188100b2403a8200c8100c00e4135400300f02e89400441c400c04081d43c2601480782e01d414502d8800c42ea0089583c81101c2c00e10b261798460100b4030280ba44203490b0540e83d18144070780e1910180e44034010041e002c0350900603080c07641d100707402c9601501d140350f0070355900c0003000110b903200d404481c454034000f45020b00c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 596303021 1250 596301771 596301773
    0x3090c09020a021b06090d03081e19150e0a0c030212070306050f220b120712060b0409032120040905011703040608060112020a1805060c0a110418 64
    0x241e074081d91050b900d0400d4400380ba50380c041c03405d03030203c0d800c418001d0000700e03000e00c3c5075400b41e0700d20b107014000b0f070f6401c28090b000e4002241076844180c400c400c6118810142d08414072100c00b218060030b0b0011a03880e0926003440b1030b000c180040c0c0e8000710202c17800036035042c100c07808070000d00451100b400286c14001c280401994035401040980391308841c0c001521810800b01700300ca00800320700d40c16019a6101a0720b00003900c0d4004080d440700a4040390041c0025405c213400c00c042038000103c28001040044103115080c4100d03030805605075020081d00080f9100604005412000f001d00170050559010f004d100e02d070425460090016801004018000c0d4003280541050007500d001034a0701000080582c5101080760303400111300051403a29040800448186000030003560500c030310040c008000401e80c0c030082c0408940c075580c0342e15011044044021000080e030181d4403a8500303000104a40402041c0b8100b15a8416403090711400c41c80049800b500e0f030400820745d8190a90607002c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 596304271 1250 596303021 596303023
    0x190f0305073f0f03020702120a1406011d13030306091b080f0c0702150f070807031107062f0703050606030d1b110f03011505010e031c03090c09020a02 66
    0x186003a0403803008402d240b02481100d0710b001c41c840d039000001a00c81e42d0510846402070780180300c00c50001d84203035442d0090000451a0805640c0201c540b08514481e066480000b07012140c0501200751802014080381150540c5e546400381c001d02071f1020700901d0b48205400b13a400f403001444100d80c10301034083d28030070200004944600d0200401c07520390001d60264440c0d42c060744220303440b01034107040a440d5000d0203008140441150744400003003141c0f02c1080d1140d800303410072500c9510301c50303500e004501c0d000b058480462175040540d400311005014141d0004042c820301940302200104d1012000a61044105640e48110481c001c00901009004000c41e1182c42003005030216010f070030312032800301e4a09401c04107079100d00410b018110006807030b070003100b0064200248079806814004c00001d00f11590082d0700b0780303046082002088296000b0000101c2d5840c00c40280c03190214043c4014905d240d015001020980e8600c00381c420005101740f00e5028100c034440854603040007440103 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 596305521 1250 596304271 596304323
    0x15060801150503060d0602090303163e01030c090b1308011401080c0d03122c0102160f020d081801020106050a1d06121203011403190f030507 62
    0x40c0d1034481008541c00900c50060003281c1c01044050a5140d8000c02602e41c03400940150189580c140010800381d51070740c3e218400c1900882c002c2045144484d02581024200030b540c10105100221a4691280c1c0040e400c00804d5080c1017070901190141806d84201c0790340155400c450804940805c0c0e10440000003551081980ca9a04c000c1107241403d010134808500309118840d0194083e0500702c4282c20003d0001d0802c2d8800d043c0780c28486189401d1101303803070f00c0706640c0440c200c41030300c1c0d80284c0e55907032010030010204c20001c6150038841c80303002c078500000c1d020103041d101c0550450011501c1e00700001d40090b40100318281c0f1100615540410101e030162400d0041d801c00758040307010302e4448200300c101d50026283c0702154001c0c0012880d00c49006060507448405421070300d005032001d21580302042a412800c554030360414020b02246000751400034001d6100480f141074920801c0c685203034140c0c104082c000882c48a00d41103455100300e0000404a00f10710036003903d145503405c40 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 596306771 1250 596305521 596305529
    0x4060902130801090807060f110c01150f140d0c09020a090e0618040b1003060615140c030f0f0c240a0c050d0e07210219030c03060f15060801 62
    0x16862a595202072241c20707030713048960140040504001100000790258005c003082140c05001003034031346a161940391140c004d84440b40740d81c1d458200d4030340038450701c1740c12802408000d21240d421a0401c151184d01d142142191402401003111540500242d14103020080402c0c003000e540c0c0d41e00348080100b06108900c034018507000e0402c0465410b250a0040031004080303090520340c1c82d5600d407210030580e0340c060542195514804800f00c080f610a014000182001001500c000307680f1403c01003000c5811141e04000600c10300c244c40c0d60700804000c40c0c02080d025990329031900520301d42010184221205501e41c1c0c80780503148080058000400750032010b0807041041f6a5441c5906c08090ba0083c109010004800300010f582c00301859222003c1842447d04a80c1e0b9203403107050391320b0000314909a6600691a4480000440c41c2c44e000505040e40c1030000c922401c2c4c550340e01c807818210607000040c03999880300110026801c0e1743c1e00c242528441c4064032469907564050181c240e907400e000d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 596308021 1250 596306771 596306797
    0x4030309021212120402011b0303150b0301140d020a180b09090c030c2209060203060a0503120301150e09042109061b050a0507060203180108070f0c080904060902 71
    0x10b00c990303201d401103851441c0c00542040140f8100c00c58104000445008004070b0501004144038280d400075841c02841503486610001103801a560003c0240c102c3da600c0f0f0700c0e80010410060142c0c0c0e944203810350001d038084d18400c0811300315100180703103103401d504401003942481c016005001100c0d000140500f0080d42d0590b1175481e041c000359202d50201007181c3e050b034030031620302909050a505082079240610462005401c036459040c00b40c50405030103860564010080c40520f1070000400700c02014100c005000f0032040468006140c001441a2440801d0500306070012901075805e44054101c0204a040c15261501c0d10040c1821001c2c507500703208030301041c103180ca140507008141c203a60680e2a00e03030407a550421141244020031000312800d016030f046800016808000c1740340a4402500a1911034039000a40c2150400748883d00341084030314828030140603000b0242c0800c2e0020b5142000269400b824480715030f119454120350802c0c5001800a0b56040c1a4050701003121030391 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 596309271 1250 596308021 596308039
    0x3812070c061a0f13060b0d0b19030b0114060708041d0f1302041e02210703022502030a0210200706020601170c090103081209070b09060a050408060403030902 69
    0x41c0001018011500301c06400240f4590007290740d14000703070300c8086040b00b20000b00b00103883c0da4044025402076421943c030152548111042e62429015009401c00d4100e08100f0540c03450f12507501c1240184140704a40c81c1e0400da51104e6194401211012900306104569488d0b880700d4148001021071010b5a05070340c0000414685000c0300c0c01540900c050f84d060003c00344180e0200401803c03444000303010034450014174510740702540040c0403622201c213143c40c000c0b2660103480700c41c560020029010075104200060f2900b80c01c04022a1460740841c00160b21901807001c40e2400264242c040e501041d20b010a51813582c1c08403401440144198042848140203040140c0e5240035000d4540036812180c01400701111091035100e0b03000740c0c80c04844880f49120041281250f0a0700142d685100000709044882c1c07103055425001a01e031002800c0e02882d20b6503d90721400b501702c001d80b01e4180040c0d0b031700e501889641514050910601903a2050805240141c01171400344030480c0600780724 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 596310521 1250 596309271 596309291
    0xa0611100e030d020903070e09010501060f0e0108070c022e0f03090c1a070b04030509040533010c140d020c100210090c0803030a0c02073812070c06 65
    0x40e001d0356030000c60480c0214104100c4850200c042d40200307110790f400d4440e10703000203110400711071024045d81c698000020594145200140302c4042e46401a003441142e002009250340d100c065298854028503000c0395060f8070b840090000603946924080d0240340028282c100482d500c41c12400d1083c545171000b00603a00b4000390103030f4032180c03005031144141c0d04003080000e4071704810750a6244150025454251580e40e0449441e8065070103400045002c5824081c0b4200341c07107041e4124010b942c4103860a0800c1c0b821003101c81c4108140502000c4000d030b868010307405920b029083d5648402417207852401044800c3d13075104010b040c64014411a101600503040190080385110141e60107408103038191181e00001e4945a14210345106168900140d0610140040e6001d484070800120b144900d13045c000f442c0c0080ca400883c1e2605480240803400112940114000d44902d103c0c0c04208541034280d4803a0700840d21088400d100da001000381140e4801044064684131b600c00700302611038 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 596311771 1250 596310521 596310553
    0x70f09380402070609110901140d140307140106082b030b0f0a031b0605041802030606090607060510090203010b07020d020a090603030c0b0f3310090311060a02060708090703020a0611 80
    0x68948201c1cac0106001460101062600300c0000031501c1e8074048914040d1180d91b0007850901d000d40e8400941d40d030396020701c404441480003c543e8650512250390320040c04140f6030110200c18444002d240d95132041201d1510b84080343c00d036003075000300050342c4207580c3c0c1040c448202d07100d0180c0b00a10501d000124545004000b5541602e142d10900384a1204185241009503c09000254010030620000086a80f040d0013040d030144a4200030600e818043c0d01d00603d41003641000d08003074010310050040c100340d07505031220f507501110740c1c003c00c91b400d0010941300c88050f0400f42c489420401d0103c18140c03c03228540300c43d40300f1035004800c0d544803606428442401d0310714046185a8140c20352500d03800d01c81c8028050b104c1c50081c1700b0300111200148400a0140110003c039210b0700d000c20078040c050301c402405030425102146400b02c0350000a407641c0d40285010103000e04000070030807401003084039001565000d0104038049489407000740c20250840c07000905449892114440311107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 596313021 1250 596311771 596311799
    0xc05130e2b08090a061b030e0a051c0909020a0503010614071e02060d051008011a060a32030f0604090f061d070f09380402070609110901 60
    0x1003034950070004040c000310212810003000e4241c46482c442e807455071010070135500c190f001840b0000002440d000d003981c0701a040c0d5034440008029134000c4105440850b4004c42d001124004000201802d454110340030b5070b00290710341000c4031307451000c00c103500c50b41c1d0007074000d50603504140c6510741c070450041c5400c0c2a5104462008000111020046010341401d4810016082c4002e012600b0540c0e11540c14049400840c2e2002d03c0c2890f00c48100700d110800c3c440c003c0c8030704d001294490049143e8011481612a14084ca0200402401c8079402c07030380650721091520070000d0b9400d01d003052140400015400656864181c00780410200d019440c2600c12100c8007039104580044a00702d607100e610080c60403008001c8002200210900014000c1c02100e02a086540883d00038a080003245c500f261101581203903202c0c030f072070154844550804070809010f41c040c0b030101b0004c0f02d00004038000e400380e00d20051445050445039020031002c40211048005c040e181003500d40c1c0d845900343c42d003207 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 596314271 1250 596313021 596313073
    0x80601050a1a190509101e090b0f030403030204030b01030834031808010e1f0509070312210e16150c0609052a0102070f120c05130e 58
    0x80c800c2103c0d6448400001c500032154080781003860405503214045a0b5604030305524800040744d03c181c0b42ca10703150f1865009040211445c00810351800d100b402042842030401019071000040300180405100350101c40203564480031010582d696450441c0340e49d08061021050030356410140391034203040c01040441350100681c0300070040307010f4509a4000b9101c0c4030103107503540640301c085852102400742802d1011100010419180d402c01001c0c1680540ba0500003c103081405110a0314000500b60058035000305040e00049001c09041d107215044615400000c11492003c4084642c0c6a0115000e9500c003019100343c000c03800305442e24080140920f060700c1201c640311540042c07050540b6201907200f0a0000b449106a403290781c40e001002d11222401c0205241068084812030f070420000f03031f8280014048070303080c480e5a0750040400d004507150400844107400501203040042c5000740806422403015600030340360a0041c00682c04005c90b14841d00350103a40d21003105080c1503182c = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 596315521 1250 596314271 596314319
    0x430050f010c020307020a09021804050c0c16030317070210050f1504090201020d0c0f0f050a0507090501030c030b1e0c09011b0c12030c0803070201020a09120b0a0506040e0106080601050a 82
    0x190424208d04025000140d002400c954103100b60907040e10340b4803c090042c140765424540320301400710003620b01120020b480d25540b5032040108000f0b504500100c481d00c1482801e040e0340e54034480200d25046132410b450307441900740b8042c802c141183c02c20541c040c00707900c0041a201b148200c140001d4075039100e4001c0c0164090146403120360b12036401c8146042c41803456002906064480c1c05030245141003d5035103400141540d0304001341080480001c01510030240803640c03640c0c4821840418921000e450094500c2c002038110405010b02d010440c2a110307444264204041c4002d403a03040320f48003c0c04544a000008075044445556180b41e40d44101c0781881c0c24100407081034000e1020000b01e01b0f100040c0f00010003d84a1800b842c070480481d4001a152240b00ca001016180302e40d12000030740b13a45081440204852007040e95000d8a4100d0126881c3c440d50081030040001d00d0a5130401d502e0703d10041082c02d800b1800c01e0481d40200c84008202e5142c074411404407a0940d04500c0e2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 596316771 1250 596315521 596315539
    0xb12010903350a1d032106090411010302090604090c0909050c0903070311030c0d060212100501080402100e13091505070c0b1504020705010203040c1a0430050f010c02030702 76
    0x10610943e08a260292001d0f100c00c1c08134503605542d18595040800c00d204605800c0c001e011500420424031a409401103403c101e0368181a250a02e81d09100c0c1c99103410540c00180700c00a54072090100c4008118100d403c00101c41c0176040188002a80d0050b000f100c3d0070540414007800d04401136903030740480140501031a528560312149540030b42c0341255010700501300259440d507035030f090640056000700409a074900e41629030b0f0842540c014035050582658100601031a6030200c100d55100e5030586510000e00c40d80202a0742c1c2580c113407103455101041d40c0e64141d0768840c1da001070603510f1085400a008440c4108488142e503402c403040b0300064041c0c502030022840e00b8020b680c10040a50400e143c400310b032001718060340d00c00348044c0c480f60340000034001085801c0006500400c0b01c542c20004100391030400a109100380d1107000e0043e401d440c080500f8800c0100400b1a0b07034811500d015000b115458100d4907986243d60680c0c00c0d511344605a858203001000701d9104a9004003540f00c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 596318021 1250 596316771 596316781
    0x601290a18030f06050f07030507020c06070c0b03010b040314071419080304060c050c030712030804030905130617060c03060d150509061f0b0a1d10022505030c040b1201090335 77
    0x103801c1032403f0b40304110040c5001039203044400003103000c0d1021051103561107066047c8225a20803a4122104a60088804100b551107454420f800408200c520402150800c0e45000001450b0f4110036a80d0000040002e40c280d00b0140b0002038905c0341081c0d950002034034040546410307070741c8210a0040c00c45200c0100007485a40d24640c000c0c802d0401d400100c0e104c10105040c2d542100044010340c1d6241400c0c440b03142404241c0f02d0484030a001842c1600d88508403640328040a03203100c5c0604800c40c12541008401c103100c40305410850703400c2150740f0b080c0c00e4580ea6a501070703c0f2492800725800da50200116214002402d84614584140c944001028104c84500c4405010005c2d006104007519040e80c0b80d140c3c8280d940c07075581c000c181960350658126080310640d02c4800000030b007508100080d40700421072255159040305e00140d031b00c3c180e8000c1840d1142140300e1000c194a009824810950131000103102141e5841d418200d89800c01421003980094800e0f0b100e0449103440018 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 596319271 1250 596318021 596318029
    0x510090203040b060d080c1501031416050613120f120f020303070f03140a050403081006020709020a0e060412050c330f0a020601290a18030f06050f07030507020c 71
    0x1c07140c400c1300814a030485c01d121f06414602407440c0d06085030340d02001081444405026142d00d081c498002e4010501e61403035400c2404c846106041c06440d001c11034180b41014000740c1070062010700000c00d4641524a0901180b2500c0042222803403020b2030007107045482480c042082111580065186454407403040d214600142106000c02d51194100c0300d8081480003600d000355000c078404505402d042c6170292801c40010130721070756507003010310420030345034001010012220f0990005a403821048812200c00c4141a52150480000140000e40401141d940e0410502600640316840c07028400c011078000b0500040c420300d030b5440c84032a003404a002c801d416029441d041603240102c070b141004459042010b44501680045d40100000c0c08508091040c1d180c15140011a1401b41d404280c840d0140c2400c9804022118480b8041c400d0760240e8400510741140304812800740516010340903000813140e01001d143d0100105032103038040e01900e4090b144580240c030300c206078070f400c0c4 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 596320521 1250 596319271 596319289
    0x6101704031101020d1d0d030e1203090304051f0201060806060904152414060a0c2013020301080d09080705040209010c060204080a2109050616150510090203040b06 72
    0x4030310b09560801500380044c015200301d91480c1d00f441c0d240002d542c1d0032000d035824038003c4214030381818140441c0450b4800007203010011a0074a0b54050703200c2c0c5643c100c641c90350083da0091034020b00040c0480500102e44040b850f10304a0543c001c1c06600e071118025a164001a50140d800000a03008200019071007040a031034620454070004031080300e070709150401d04042c41201c12100014000b40103000f41e403842c0d10207a840c182c0d080c61078541104401028503000034400b801e2103000480240d69584200c10015001340c00400091803a142122003600a50080c441d0003040c2c03207080180707054107020b20b88000071502c5400242455626060a00c0040c1d482007820f581004046415080007441d2480504050247d0b0401455080950318002d0340c0031082740f411481c60011103180c00c40280d80640c502003500e2040d00c2060301c0c4c030709011203c011403e40080041c1071011014605a25000300c2d440240b01da80e64501d00c0344240d9aa40521040340b0064130040c18407940800000c5c141d040940030 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 596321771 1250 596320521 596320547
    0xb2701080712150b090f09120702031506011407060f060602060402010906030e010b040914071d04120903150c0e0604051311040f0611010507090608040209040302030d0f02030610170403 81
    0x204aa03131140d0b0025141075000c171341c0480717400555428002c3c207807010490240c0c0c0e8803d2400e811301c0c0040c503400003136a0302c050440b24011301d0070010000320903902c154a0001c60036920107901d83c03503020601e0a1f1020700681740500365201e1524a00285461000a105004640603169030041c103040c0081100a4000800d07414619134840d40c404050b62105c1c4a20403d56000d00c0300c11011f6003568050310b003040c03260307442090f14901c42510080b10040001c1410b801030342c071904108190031281e00a951a01840d8809880304031842e8007a1120740c0b950300070202c06022603032190241108402004064000c50140c10340010b00251200c481c1142940300c0c007028040c50070b1050606c1c0d0b4649a10000c0e640580024000902407500501c640c1c009020ba550040041e0800d855002c3c104a002481c6081c0288080d21440c2108049001c5c1802841181c1156408060600c042000c1c42c000602a50080c0c506a0042c808100710700c100c40c2c815081c006c0d04001905444d00302c6e8440d5281201c401c9088a2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 596323021 1250 596321771 596321813
    0x311070803040803040806060a1d0402011e0815030610030803090c0619031a0f060a0c05071d010806090607050c070f0e0a0f05010609180b2701080712 66
    0x2001242152040000d400102810001165a682085921400c00c000509100d0082080c29010300080860300300c2c0940c0e10280600030369003540da60004aa243d00c10080101800c003001d503200c50a00c0c0d020b11135500c501c50520040c07181d2802c0d60b0515560743c1b8100c0d0381d02200302250342c003400001c50603002960401f40c500203d8801c0a291800941140d00540e41d54070f4264241c01120b45550300b500502c13220b02000c0f91000c44c054400380100d03501c89680140c00b880342c5c6e00044c00d894194022404045030f5504401215440d036102d400c0096402d20031513010708880395240000171042d0000524a02c101c0da40400341c80240c031242c0c004c1d12950800c20300700320240203407800401c9000300213500390003c000300d000e03004c05824282c00446c1100d101c136005a81e01e604200051190b90b80065850045034485213801c1e0b06200407486120090640d440c519a111840c030f010085440a1419400c00c07910028540c3c41803a6620303410141c3d00c0d0194401c1e42100c881c01f866034004a021071900001400600e0 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 596324271 1250 596323021 596323033
    0x3020607180803030703051014060f09031f06080c03010524010c1506051003020918100e0c0301060201290f01050c011407030c020703020d06020c010b030d0804031205040b040311 78
    0x1c0b10140c210340080301e0307100020785d90740b04100444024500c1ca4008024100075000d01489003008038095119103c8112070340030b80000c060081d91810044900400d0100500c0c140b03814080900b407010340ba440c4111001c070f11802805400b140340c1842003500403d00c251450000014120b1241c080c500000c420070f0511281003074100c0032850040700c130b080e081075107680028941e04040400c0341d040341100801c0101441030101d217085440f0800007a602040c0140001050703555540b0201c000280b64200d21107a03030116052098481003000914141c500d1034000b408200365214601d14071039a041c0000030074840b600c0200061741005035800d07580140624105140030400322100e070944820400d441100c1c90323981c0070001556807500c10310b41c809000740b000c1e00707401c3d141d600004d4000010b0781020b8856030b80020720b407203411002d41c0000340020000c3c050b500410b0700e142026010040480341a000300b0b10800880310380108030300c9483c3c80741d5880105600180c40301c0c0c6040310251289001002c01d03114034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 596325521 1250 596324271 596324279
    0x1080f0c0903060403032007050604030e03010b06040602010e0c040203061e15030f04170307021e03130e19201815130e07080403231b0115030302060718 67
    0x50040e91311aa00944021907603803040e600c0b072515404d07040c0800320061003c2c42000000f41011650b1600140c00d858140380e0038000200090040642d28503050b41315000080004105030190001c0ca00c03070036160107070342001d1102002c7c07209911085884a500184030b4102c140c1070360341c40e210b80007490005000c2c411202074161a440c81d07075109030340e01c0500c5a0fa0504100401c424841003482a6070391001c114110b0a0000010307580750324051460480300c183d41c1410140c05030400070340b615500c0303401d28104066a61101d03621039100a44891a8072110140341c49119401c81c00f8a41d03010550781300031070f1045c80d41c4e4100302c007980004070352807443c02100194070807a540320a84d06c0035583c07401071100e076903207036024a00036124a2a40b2079440f8402c01420854450703001220079a00541508040200391450100004003d280e1030311040c401d88041003202042c101c5540170b09000002e40000c0014131001c5401c1e4184400c43c5c4402001680301c8000503841c01e21a000c201d61741a44d00810711195512 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 596326771 1250 596325521 596325523
    0x2031504060230091f0c0509030d0e01080702150a05060f040507050421020315130b01090606030b01031a01140d09050102031501080903040510050904090f0203010c090501080f0c0903 80
    0x41811401d00d0784100f65402800508140c00080040c0103294001e50103001c01015617100448801280d9a84c002c1e4817864018812640b0050b002401c3d2030000703600314001303000072503026506030000310030300d0010b09014000259050102c5c0f040c1c5500903242e03900000c80c005020700908840d040442c8643e803d29503216401064080d4a4075290340f6221824030a0340d070360605d0044003d65500d040b6030a442c0243c1c40110317550f40240545c81d070b20116555003c1003d250b018020f08010a100d050744000102080594082415a8a142d9003400040e03485001101556510384040cbc1e07100440308408042580100000000b83d071180020500341002e00c248201152031198090328565000810404620303201d481c0756002841c2424124005d080c0b00114907034030f01550107801c0c00341c07420041d514111401801a9121403c0c01001840010418030b40043c1040340410304a00039030800014084c414003410382d90064030410b81d00c03600c250b960300b0240c40391204054814241da80c001c000c041c0007a14 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 596328021 1250 596326771 596326807
    0x30d021b19060b040b060421050d090e010e040803060d0213020d0f0f1b0c0507051210050109180807021302040609080613020d02040203180303010f06020606060403020315040602 78
    0x81164089007008125042c494140c0d9401c030b58040c8264070b8211854185c1e41c500f0240e070192481085500c01c51205403520141100f0704490151a03407042c550346028095015642d103017521211002d038a070b41e907641d00b02000e40c090196002810700300f0078000902c95003081400c0004036800180b480c1d11420201483e0805c0b80e005c04d4042c1211074a40780c0f508081c010300e018140c00303021810340400044c00340c4168480b40d04041000301d010031400440f10400d10400b0050030001d44401014000f00302d8445007a0b80e0340f01c11071440c1d0500a400c2c0380000410a06611032101068842c0d10114089a42540c031000c0941c03242504a031b100d2607260011400c0c1c441ca02c054009801d1544421034a41c2c10412480e1406200400c800300070040c000c0b0752801a114480590303da00e82c140d40140c1c480c0c690b440325940241e01c07180c20105c0307844084000038481d0105003002c2c08403807050b000c0d41c041d5100c440502a0b64416800701a4242c0c0c02141ca000b10b40e29410f031456402801010014200103107004a09047c10b = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 596329271 1250 596328021 596328043
    0x4120804031d0f041d1608030703051e0f091e03060114031e061f080705060d1d1b040509060622020301060e01030b0d03080a0506010203040306050c0a080105060c030d021b 75
    0xc181710802c080510010018001e400702244512031480d454100b95030303900d01c11824010100310021134a80d01e81410280410111850b0071000ca803140604010458290841003000e846600541e50b10401d0075034a0074030100b403200207806800c0c160300f4480003808000580340040d4162054121a01542c448200001c11000c640301c080d200d5400c000448280b000e050703952000c002881040200041640021507808440f01603480360b4440d440ba1441c2c0b8014011949100c0c4544400c84000c01070142c04204101c102181280702c0d181140d20a003070000312070088880215540c40000441c145240010240284441e42401c411603910106881010b030380003a032064010480e465024030f21907800d030103110900ba07400d603095207162090740c5008058007400750000803c00e60703d4001c910503074401d05c200e902540d04010144104d04003803402800d40c2d07101d1820700f40010200070000c00c541c90702070100c0d445081b6010056050400d000d910b400250720107941981d11804108000c060740805016a4620b5 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 596330521 1250 596329271 596329301
    0x70501081f08071d100527090a020a09060302060708030603160b120c12040f052d0c01050405060a121401120b180a0305090402040e0108030304120804031d0f04 70
    0x41c0e8504009415a40004003003900050b001c0c0c0700b0402c004c010066100c049486c103c8269000c013045658204550205650864074200e5040c2000901c0400180702c4c465144280d4812084581d40d80c8920106d4840f408000d602c1502001008081100c02001e182c2104c4010706661460b0361030107146800714a81d034003140541030046141c5006040b0000910b500c80c1d00a111249400400e994100b03140c800108000c4c00320000b412030005004003002000c05032900b9070000000c00f042c0b00c4903a54014081d251000e000d00c181c803203051555200f401950210f070809020107003444013100301600c010500c600555252a51100d100301c403000da40810034001c204401ca110310100c120308020308005402820388401403e284201500f0200024100c40e4007901450501e03110a00e40c40040c001e03205e1980801c40105c0301ca0700210b040d84c1c0100085000e1886240b4085140320188029a000c800458000e80030620b500240450302102241d04041c07031100030300c048440d00100e4009003c139000342e190380e519 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 596331771 1250 596330521 596330533
    0x5040618150e01050105010903120311040807090e0102071a0405030903060705031501020601030c050613050402190801080c060d0906020c0f1b010c0b04110105190816050c070501081f08 81
    0x10701d070a03445050a2885500700034000e642c10a400601941d0480c44018201800503c0c42e51807103200754001c900c0d42c80441c441303541d20780d51003805590b101140c0c002c0c00d03140b5150211480c444601403007102c1546505c0f440140c542003040c0341c07813481c2403001402501c036800304004041e0750b0340d0140441e0b4812500c0d07486041d1070b41007c200b0310115000c00c021403410740d80841c0040c07001c036030411200c40482e141160001d035100d940d180b1000c02034507a540314a410500101c1d85010b51620a1001700d0740560f02d603901c0c801c6a0345c0300046566101001d1685800c44400c000c0c0b203801d18100c0d040388400d60b016040151418484403041840c04030848040d0b103d54200140704900080310191010a48100346000e610742d640316111075029400180004044410700000b130b810341e90180e016034103036480c0d40300780c1a2500c2d80071001600c685821141e00c0d6140c0109031030810054018002d96451801702001001414148801518419801350400c0402c0d0980581c422803040543c00c00c03800380c101d02020b081 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 596333021 1250 596331771 596331803
    0x70f020a050a030807090509060a09020901110111220b1806190e040e0106030b0f04050703050706030c0212041d07052704060509092a09010314120906090405040618 72
    0x2031b40e059004288140030100034010709507901c2c1141004d842c600440141d84145a02c0184d803130a040300c007509900c3d4241500f5503006c2181c407005d010030892500d54022501d004c0860840c444d0303070314091403038008428803100f44020480b00c44910200c81c00740c85c3ca0f1071301c1d400c01c0911140c0c02501080e80300103020510310f07040c5420f06024210b881210780c4024800d090555507104582200240b401da410340300b010014080c04401c124143c0119042010f44072001d845040003405000d0381c41c80b400261281c1002a441e0454500c116000c85010303d407a02079880300c140e80700f102890090407010400806004045c0c0005d6584079034000402402c00305900100c1440910086d501c8680c400d610642e203c504220611002003585840c08880d44002d154000030780041320456a04112203a8100d01000c00100070407a02c1c2c8170f03904c1010605821900007441511048200f48038003402581c100f1800c0c00620003600b02a001a5000b910ac6da00200386515240008a000c0d100c060702a1043d82d40040c03416 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 596334271 1250 596333021 596333027
    0x504050706020606010c1502040902040315050f071b0302010b0909070f05090103080702100306120b041407060519051606061a030402090708091504110a080114070f020a050a030807 79
    0x300500c1039002411803803030600000b0b0615800072101410109804592070b100a003550b0440700a0104e4a8003192526142d0428040f10083d410810207054070300008280403552190686208604036a00c0786807114540010074541c908151003102559221002c440c055545c0c1c4142901c940ca28100421f181440c1130103403030b92060f1950026018040c84001400440c0c203180459520f00e406907105443d10059010450040c982c5512100c540c203e001d4400040041c2c01ca04980140e01500c1712111540fa1000096103910444c840d45001c1a0204021613101440c082020441009401c5c0350341011208051707003070a041d4099003120820340c0d4810900c00c41032a4400105808040d520050840c902907022035800700000d0700290a21641500041e034047d810012046801c4180030b0724003141c281454a05a101c1410207103e02c01c0141c0e81000c6600141441401c3c0c04800010503d2455200c0c680c082c1c0320303e0f141e40300c40d02c2113000d03441d40d01d000700b4001c0000710942072096840d40ca46d460100001 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 596335521 1250 596334271 596334283
    0x20d0518010c140306120304080a0807060f050f06011206030c09060e07020609030909060d0f050a0605070c0c050405070e030f1c1b0b0c1b01060801050f24060d0f050405 74
    0xa1014009411550400d4a2103001130301d51046040e00c0169016035900c0010b07180d401140c2c008059482b42d81d10060411048a000c1c0c10054403850050003102c44401c138490075500216644081e400a90001a8066200d01d081226241d80100002038640d140c0d16141040310450700515070f100e860341d0041111508298416500c20003e10203030409081140b030650316882074040382403250b150b07540850705540d60030400d01100c80d480083c00030340070b410340762540c4c403a08042e0007640c0c010b1410000403103440c002c042c1c1001c3c640c1d101c10310400803401d0104100081c10701800c91420855195060019510100101c03484005203500400309040070829107094501c51504001c20000d045504510441c40b51a171801490780c006c0c00540113a0790100900c009020708459007400600ca004244452007065000a0644100000a101503a50480501030f00d100560f1a8100704480c0c0e454140d0b01546152280c07c64040200300b280307400d0b000b803c0030098411f1744400c0d046c4c580e911418801004010040 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 596336771 1250 596335521 596335541
    0x609080d09030c050c0f18091002040303210b21010b040c050705061006140c120d200f0403020126010e0937080403020406080102071401140105010c030201020d051801 73
    0x4c4d010340b114898020170b41806d21f540d05040d2490380b40010030401141440103901e51064442d04544680c0c0d20300340201642c12010100805540000030629801b0240c050b2000b4a00c000d00044080c03c15440d01420340a44140407003030039561901d0002d61583c0d6802a854a000d05a03509901c40c4e8042c20309504240005e4804080c50155140800c4000d4018181181d061891307021141c803450747d0040c05d410a00c000003080b140a00004420380220010b82c0800c860f500880c4144005440741e85070150310b0300c180310032f0004100082c001000190311030505c0c4040031b840c0d200006c030482206125880f01c0002a0005200000c4000811084c00401c00101d901c0c1d07020b503a0700c0005511005e09440134000722516248103400307101442c20038804074000300c800655000d4000c00200340d850402078001d400c002000c80e03917051240004c03a02d08c4d405004410310352000d0a0200317081e929100040d6110300302c0780c0c1c0880565409124206c211402d501c6203d01c105402c218000d100c0e2860003105007100d00c00c0314 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 596338021 1250 596336771 596336779
    0x5060307260a140a02210403020109051f0b01090506040b030705040b03090c1e0901261c022e02030a0b1207030311150619030b15150909040609080d09030c050c 70
    0x1e0030440d11000c0341c1031216103e40c020034030b06c98556040403400b42c0781405000d40680700b4100d0312200740c18507a6403801c2080b220001040849400d00c01100e11a00b02d00c141540090144003d008803901c0700000d40d040320780c42c00d06e81d01d850b07a40c1d604849e064000f00c07460082038100643c1042942010011020b100300d00a1303648000c1d451280010b6005841802000c41c2c0036552021384020704000143d51942428000407100c101c400c60010208900170480c151006010304201c0c080011403d01d101100480c0001c004549285c07040c144200135000100481c0165844040e81d00450b100c80010422040c02c160141084074190309000e8011807040c0d002050507401070a01c000b816085981c802c0d00103208481110311220310300f4911203401c0c2281c01c0a40088003c80900c2401810a890303108a81c006031100e0000310391000241c0018064120400d4201c803032400040c000450b160300107030b011841074842605113003407503002030300b19542564200d0124200c060130b5000d0020411001c200480112 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 596339271 1250 596338021 596338027
    0x11010e06120403030204210507050609010210020d1d011b09140f060d060e0403081b0909090703050d030b12030c03040e0c0c12070b07020705060307260a140a02 70
    0x20010403600d110303a0071011200214000420101031080d0119030041030590340300a84e00480d07071441c0071126102101219140320700100010581400000c0e81c00091050300a0640031b6074144160b4007940c8003511942040da9120728040b03480e003202d005181141c0300140001103482800141c07244c8411500030303a1b018040e044604022140d00700c1024000c084041d982c1d02d501c201d054001c54800d00580041c0d680f41400c160011814601075511544100d01070b42da82c0a913504d40c2900034480d044003042003c8103240401c494041c60500102841d040b1302030208940c2959500c0d1282410f0a1451600000282c0c40f560b06000d9490141080400442c4c4600550710744080000e4582d600d00c1f4074810b02140d24021000625a01607141c1951640e030214803e0300c0c2200320010341c02060b54040d400849100e0f8043d8007081d000c40c4005510803d40d64017801e0f0600e0340e15481015188101e480340005040400706440c1038403070300aa01c085018080c40f02c4082040c2040402c040f81e410f0f030043c40050020b01c14 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 596340521 1250 596339271 596339297
    0xb040e07030501031214120103110102061e0412210203190608030a030902060f031005040c08070c1502070818012a02060d09050a050604020910080616090e01060c1101 73
    0x40317008a0031015150514129142c4115110306103805041d481c0c00d180c00054000106000d0342c0982681f07115000d03825940340e6507036100c0605900d0701185810b040d600c0044005000510440382181d01010241032003510000c0581442e9030042000c19007850443d004424005001d80c000c0b030001b80001d0500301405468101001e181c0c2e41d0054503802010141c07034100300400d5446000442c1e00020790403462603a01d10f04920380122400380352103924000c3e841c3c204184c0c0624801d12440380220450303920618026060340302d90240d040c0d006504030f015a0308000030000684640018141c2c901d04440f08801c099450001510500d40e0280c13007100023005034038154502098101c21005c50b0350454480b0340b01c2d45000554002032207214401081c902c01c085144080c814000750151042d4421641490b01e83d4507103d0781036403000c052003100c04a070f101d40007080040a03040ca11b60f40055041ca02003440c5070342c0320300401c2115000c0c2d21000100d52100200001d00403c180704400d500d0081c00c203000000f06c4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 596341771 1250 596340521 596340533
    0xf06043c06151502030d2d0b130b030c040917070b010e07050a02032b09110a05030f0d03020d1b170c0a0e010f020a0c0b040905010e01061707180b040e0703050103 71
    0x184400c1409026030780c40a46480c80844a1400c1c2c10000c0840e07c00e0402d00442020790045c101071007010300c2028458200212400d05010b641c841031400b030064444e84440409010150840010445078420b0100c14403036880c20b03000203041218001c24040003554503244502c2058000070384401c080010401c001e0082a8000081324082e130744c220075001250f0b42d000c5945000042211100552904000340300c002e006280101f4407000c6011550001700c00c0c0c0d03910800d07640300c101a0407402140c101250049459001c0d41c0a0200d0f90318070b40c80804d05104814a0310105c1a04082000109814490340c4010888030f081d10b0b54050020b9184078513060141d200505200d0513215500e04000c4003643c1080000e2080c800d1010b113a81c00030211002e0750310341e0f403404e82640260180040d42c510340000064030030169000e203412103103142c41e250300d911a8894900c0b440385008022406210340300361020006007400620724010070b5922010341d1150b041030200800020058800b4042506040050002c0340c5 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 596343021 1250 596341771 596341777
    0x8060603090705210d050d0c030b0a060c031e020d08070305090c062101080105150618060c03040b04090218180610030b09090705030f06043c0615150203 67
    0x41114100702031803507015a1407000c544006020130b1402222503d40202e03420134080c260710b807a014014040020380020842c1103038482154107900c01849681000100c1c010340d402604035002c1c5c54401c00c40c4108010405080e9581002f8400590040c80d501903129030141da41900700c89240360902c0a42000c0707004e00d40c2d41000040051285000107440c4124141c09014858020301da180210300ea1740e0745460490080104480d0000340c1100c19118a40d03d2404404031003943d25143d401c501d04509031414094030343c000480303041c040e1100300804140c02d0b501c0d0700a0030007000c2400000d680c40c9801c200703070603085040c100b00034013408100314a4032001404000d03582c1e202c9010f1780c1101c0705c2c03800030404401812041e203005401032881400d1045608010400380281c85042e011100c448100d00c0078203581e0041200d01405118505908a69500d030b0060809a00300d910006920184444108c0480d5243c9144044500b242e0380c000d1104140c5201c4510340003080040e04034a4956410503020307440384 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 596344271 1250 596343021 596343029
    0x11a0d02030c070506090601060e0d23030f0d0603020a050f090a050c191707300603081b06280b030a0f12091a0711010917030901080606030907 63
    0x303030048002240d104180d0143c96545802c48100c5031207080070b01e500f41c1c441c20280242d00018101003010455814800e868030314055009008074418030348807102c05000301c5441c10040d000e0000700515804c44c0e154202400c003160205000040c25451441002405c030001d504c600d01900003540c4000c1c040c1e9801183d0340d48407030408400310706030f50307a00005038081c842d150031211205800d0b80c4001c600d60b03011500303080201100307030a82103680f100e030000c0d1358140d40304500070358001d11008441c0b6119520042c000d881e04440c00b0200b0403a4480d543c1c4859604481034442c001414028140f240f10420450150850600448802c0401d40d101c400282d07480805000e144858031980102d0103500c0401c1095400780d000700481030300d50f40c289410304205003000c095100080780c0107008075421900000095448402c0c80000e0700d07140c5940c3c0da84410128265030b0705c1c103001c400b160010b01c05500e8002a13101c64a203501a6a4a081010001d001d000d00600317103d0240605004100303500d04d000903140e091f1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 596345521 1250 596344271 596344297
    0x702070b03011203030f02041217120112031103180315060f0415050d0803040209010f051003051f080d020115050f0603040206071a0a110a1202131a030f011a 69
    0x243e080c505040e006061641144900180f00080014500ca03400980004d00f40c401d030b0f40f403c60700d0300998004284d406603524041d0742240c21001080745201c040c00c1d00311581d12030304108400b42580c00420b41507800603445008020142c2c441c401e40c514060080982601c07141160380c1070f50030700e000465490900030310564021903440d10300e103140d042064031501c020003009203035042800917490035040581051750b04a01891019001003001c003042440740003511400b400c0b06040d2200001c0441c0a03100c0903003025280744442d1811103101001d85099000780001e8002004c1082d5148c00c02801c40700110141d21040c0400d010901c2030f655502c60000d114801243c07419201c0c1c845000281140c0706020004211003020b11000b001d95000c01581403207584208000c20482541c0ea6410100d481882901c10010b514841c5501502c02107a028281006038034442400780c50b11480840d05c5504007032180e209600c404410450000c1c0300588140c090440c01d2000c20564900782e03004c0101e401000342882d00 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 596346771 1250 596345521 596345549
    0x310050907030e0a12030e0336030d1107140a0902130b1309060905010806070c1e0501050a0b1c0f15050c0304210903020108060d020402070c0e0702070b0301 69
    0x20451081d00301d0700f011440034044e00e00d000d940389441c00d40e542c190046203000c00c3c1000300141a500020043d2a815222a841c40c008507886204c2840c002c4050b040c0d1420190902c0300e034007159241080034152407107154a90020480040003030070715066007035002206e6039414551886482e101d101d800740c01c4480d40c020150700c0d44107620010130491295000b030450b06401148841d42094100000d0048a03000b4008000d01030720303511000242c54090041000c0d590100c00403506080c8903040b49949280103250040340071071405c3d024002c10b078039242c080d40c1c969100c3c0c05001600600d4030407100700010403600003082c1a503c42e50111001003880740500b00c1019850080107104006070180003150180000308050b01d855404030845800c240c90a807034504002d01844c110440d55583c060100050340c80d0684860320f564011959050300a003088d801901d1072440200580341c0340040c1c4540e074803529200045070301f0305400030141d0798010203040c00c5500143c0104204014042101e0540f8010303410005 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 596348021 1250 596346771 596346781
    0xc031501211b1101090c1e051e03011b0e06030901150312020c0f01080c1b060405011b0c0c03080307022103060a06080c0a051b0105100f080303100509 66
    0x481038904040390441c0d142806110345604508848000628145407a0501da101440d01000c0c00c07a0504d003c01090020352890034002155240303480780d007450b000144004402c0e1030701d001c07134543c41001820741d46120b00481e15031701da8a070a00071a074100b1910f2001e0542c04008402c01003008845550b914020000000801c0110703800303410254402580344007600c1007564134030f0000040110180072100502480301700c24001e180c00d101d21751102038141e558040c00e48441d040140700358084c580d1440104468500c445010906200203480f8500074400002c0e10100d007081c0c00ca0224100842408011b40d1918040004007580e20b40c0c2e055030380205000340c4035610048181c0c600a80e00464003882d8540001e440a1110100019407141c0c03403d40350780c011642e03581e5003592094014eda58100c007910621180105a11400141905101103103074594000e00240042c1c1c2140c809440d100e001c8000d4039000c1c002e000450014000903e4a0802035265107400592115039051a0140910546a000100b0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 596349271 1250 596348021 596348057
    0x30f0601030b061603360b2508130f08060c13080f06040c0909020102030906090114070c05040b011d040902010e1008180304050307030f1506060c0b0c031501 69
    0x2131074012840d0000316218600d400c010340300d100d81448586002d44030541a004050342505000c60520000040d40c008508261241c1c0044d04800780402000ba031080000d44007461440040c0103e60007004000c0c0d80300320000500c8400c40751a0012240004651010003001500144141e401f09440f00010f032110000b85d00d0301c002c0d00141c1c2c03200002d841000e2100c661058080b0b4480c0c001c512a09203881e8980ea200050001c1d50000d140290260704140080081030403d080140140207052511480d019a21903900585e500b01d2002914050401a024400e505081c41442d504e2003003400c080c480704503048003950381c000d60b410001d4051038940c040d2104590107004500040301d8020040c90340d021100d140104001402c950752110320340b220005000c0500040111800c0e43c00c05405407105a0454445508070b20040170200c2c2c030b09035007500002d0080100d101f150003504455541140c40304060800201403030f4040e001310b400a0007041404050120201540d80708182820f04980811120a400c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 596350521 1250 596349271 596349277
    0x5071707180b0a06030e030a050304110301020f0a02060a061202040b0a23030118051c022a212a030708010c1205040503030106050f0705150a060803030f0601030b06 72
    0xc41801c1180d550803804a40c89800c2402c41400a50f81c042c8440e07580c1d01c0403400d030740d0030380700d1b50f04140c004101411145102c0d03002160312a00410224942c0395002c00400d003245d101d041641d204040116088000c4ca5060180c190407101ca224180200b07410728441d104104040240203203d01d9a981c0d07109025280c00031081c6c01480d14503006000d1441c40c2c4102c141947d1140d200900c41d518005407101b8090805501d00c01d8281c0000c020080400003017602400d60b05402c1920066101c4c4411128550000b080c40a074540d0201101d000c040800d0000d00c5141003400001215010f41044254070704c000010741210000d08900b4601c084100900700358100c02e08002050341c05008111002c1082801504620040c1c1816510150581e0040300c804003240c0d029240205950020401040b03114030480c09800c0c680480140d49240443d16a60186840d0038001c00940c5242641c0070800c2c2154180b2075000140300c4140903514514104020289810340140b0803070505a603005400b819484420503 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 596351771 1250 596350521 596350529
    0xd030c18141c120c020a270f0e0c090c070209090a03020c0603040b280c0809070909050601030611040e1302031c1e050c010609050a0b040905071707 65
    0x8a580c586032140200c441c6100448907076401090380c80c541e0320a0480d4005412034050b003142e510034054022007411200b00060b1441603034803696602020030541c0e154900300003500c50072074400703100c0301052410f0026648080c100c890034914120706104100e1000c0b64070300402c0f00c12260048560341d12203003c00513005640d000ba41120030101080b02441c400035000502e40d0107902152410740c1c20400300492071008450081c01e100e105030105049a08816102c40002c070b020b0740e045c03900c4500190400840b54003402c0100010768120600040001c244181d90140180c40c005200c41d00040d102e40381c1d03840c810f02c80241026030f1055441c1b0320301e03011400d80d0054061014012024149040c0120080c0358442c001d86c0f090003456221509202a140b2900c40c064a07a1a04048640040250714407070202c52089014081c0403c40140c10300e9003031246501500c01100c000507182441c010300c07402c0302d8040700d4080c0101c1c40d120325a00451000508102201e5030368004000c030140b89140e0604111103540 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 596353021 1250 596351771 596351807
    0x150c0507021909150e010b070f0b0a11030c0910020309060414060405120d08010b030f0c030a090b07212003100f03060614090106050a050901020c100513080c030d030c 73
    0x35054110b60002600030440d401001d003c0c0315030341c90741f4148880b03104038a801407100c0418801d803400070302c003500310a5018042840008529940c01703800d40d410f86c401c40c1e07003458402c00091018102d14041d0f26084400d16a8402142041d0800001c5995445940030310342d0b100c0050320207a4540d544000031940600750140c415001491028003407035448200e0032004010400c02400840c00e41602000d8a2003291010700c420599200d10480801d281d0016080000e002d854904001c00714400707038800d600035800755407401440e0551408003450030070341c3c03200e400d041d608003d101381000c1121043d19044409001c5c520ba925201d11f20318045903061540140d00310342615100000b800305544c00b00d4111004241c40d482121019010403091441c24041e55010a2040c400040d0081c800c001520304500306004942455581000141c0c0740020411181c0000b1400a4000960340c000d8403504000d19a04008150340346038400000c0c1c56440a4a545080554501d00d501d0482c3c4122064030021420b10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 596354271 1250 596353021 596353031
    0x19020a0f06030608070608070f0302090607021806040f02070b0103110310060b030a0c0201230a090f050601030201031104060927020a08090d090e04150603050f0a150c0507021909 78
    0x7220203000750a1600c203941040c003443d400010300d98014840c41d4071616183e90344641403c01c22500b0ba0007504155460343c0c00550502130303d001030b154000c0440f0a800f4182d049041407400c9800c00003502c4514001c3d0308020300500c07007800000d00300500c07641541e0344a51440810320104011a2420703140c0c3c628264454142003000545072801c0e40190b0288425040601880c0c1c845030007a4280c9a845941c518002031104640c000c0c072500004460f00903c1e0000080b44180e050345400790f01403450181501e05070060001041150303050f10034001c6004014a103d414507241c580098040e05180c4500b041542e007491031030101c0e10905402c00021502c9200c1192201d40d071080c02402c4035000c54108041d8410300e01c8801311580102000011201d0035500804565200e644400007590380280d5010807036160394010000074000e22216003640c0842c4011b060b07a00090600032581011a0302141c6000d05d07000300c0c0003004c1c0e0f1020440700c82c6074040d81c0280c01c0f8558606020104100d80d0b000325189440e00d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 596355521 1250 596354271 596354279
    0x403080f21040606410120060a0b0f1005030406020d0c02160b0c0c01110309040501081b0603010e070e130c090314010b011e03060305030310210519020a0f 68
    0x591040c41950307240000c0070aa030840f00081c5510b0007220b00e03004110444881141034050417019440300000061416040c6c40c0882001d807a280c803030003412460550402c074100605000d207440f6552003034204481c140c1810924002048101c0041e4222034100140003000030140121501210b0300f01c0003400042001910224009440d07a10407905401d01603621080055184c2401d01550310b000b0307126005c0d118040301c941c015251505410842e4205000610401900c0da440d4800c250092411102500103000104084845095880c2034144030700c1c020300060002900700841594082c4550a03c60f030303108000c0b000907550781ca800041035280380c01c04100000d0b165001240200312407180075219600b080c000d101600741e44003135460f180081c0303607400c48000c0c5150b040d40e030301c0709141e03903043c0000c40d1511b945a460441d44200c0e13100034120303013144081140824444120420701d01c8080d032582142090b59480c0e44414080250751b00401c0c0380030b4520295660043c480e0010b0030035a80c40c00c1c2599403 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 596356771 1250 596355521 596355533
    0x1903050a0f2703020112050c162301151509060c02010e092e120807021908010c0905040e120d061205011b020d0e0103020d060503250b0403080f2104 65
    0x10b0342c00124002000d1800503d41480b050080b03d01410380780c0c1000d803d140b010840d121940ca03c04405440f0a1500402c1580d104070805400003103104a5002142480c0103440300303034062200390b120802c003a1031401c40c16400b80d0722002c20001e40d00316190400000c4110700040b126200400c8489034011600014030203669041030140a1841481d0b13040e841741c804450040009000b075120769451040440100c07000241e0150050603000c0c07004152061015440d10b6503184400c564000e014541c1d91400b4900d059a00210104000d00007114144007000213a80328580720315401d20890b210400104049007059540d0b040f00000d0507442c881a86041d50a05001d0b000e0070b92119000554007009241091641c804551101c0c801d10b540c4544800c1c03059080110001d511030720901249940c0c2e8440070505940a00480c1c45200121801480381310201200c04064000c582c000301d0448400c0000300000b810703603000c1d02c15911011582c40d849000140020b089070400100c1c0b184c03403801c02c200700810881 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 596358021 1250 596356771 596356847
    0x130091a010f050109080a02093d09020703050a0e03100c02060a0f05040b01060c0507090e060906090304060e0d020d050d110c011d06030907150906021903050a0f 71
    0x41086000c1240303d503508015107103080c00d800349075000d801ca5040c0034050304100307100c180c000b1400000c0058841c1040e504404010035040c0c130707070780b01401e4066034201c1c4001000e060002d024400000c40c6400b0103603078040d100d44102141e04040c491018426071a0743c2d0248070407602c00d04020300070701c401510b03a07000a4403100e04031400b004003482c0c08006030900b0342620410784165813100300c1070196402c018054527104042c540441d094441d4400100c1c14546a024922220502c400241054240b0179030590800c04014a9600c00c1d034028081000060303400782c480700d914501034039658078002075030010407080e4100620261851141c0b145041201d0390043ca100a42d02150781a03070f4040146100445000300380d1b125030f2551101c140149243c5150150081d60040e01480498805d5580c643d10001c8044203503c49402082c84c0b03810812205070140210000985070241038044901c260340c000d03104e405140542c0c030030004801c40c1040c580b402517500001c03140c4981c9030344071400303081091020000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 596359271 1250 596358021 596358029
    0xf0909050c0c0f031603050d1b030218011806050903100c020304061209020f0f031606020309010f08040510021b070807060e09040215030604110d020301090b0130091a01 74
    0x803003106558210f80b4004003e90300d928000c40310711048261142c4080382c1c2508030120302110300d0342e40c2c1072a20420f07a080070f04841c00e403440e85016071106008c842c4000d03030640058019040c00151390714140d21104c48054030041d50300608007540c8680c40318001c0f0f0f25003002200080d60309450700c4044510b00e500007000d0003c9400a6403003008880e4a41000400c4c2c0b001032000035084240d620140b0060300d48207058280e101005011218032528581c05030110a00e1940301401503040002d40310400c0d644002403070b100040030f0030100d80c207043c950b8444d6a2030344203202c4101810707030104004000c414250f5521043c00b80040403103c815450309521619141103100b540f0101d124803000280034102060b04900c2980c00070000c0c4030a1410321001d807040c0d800107041552080d80c038405108610501340180c6642c0c800f1001c01a181c1d0f0400340300000725580110000d0511070742100c40800305484480d2180c01c412002d8028000d07aa968148001819811200500c5100415070750a0350260b4808018125 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 596360521 1250 596359271 596359273
    0x4090515090c040213170319030c1b060506130c08043203031f0501020a02040c050c01090303050105030c0103020c1209040605210d0306120f1a09061006050f04060f0909050c0c 77
    0x500b01c004881b0390b03a07118403281540305000e0070001c0c50960313010303602045c8034024605002c20700c2411070341998202e46501900700c500a640f01c0500410303080102c000444c0650300304080140000400b000b801081004000403ca03494040c5403030041d440c0c0e80024074903211403599450303564440c024119102c1d00101c8d40c080300d84d07007011502038144040c400c6c0700d0304541060300a810006e0054080c400a05000d0250005004003000b001d070660a003481101a01402033b600000d465040004040c14012402503150401d8011711000c0605d4401203142c0900503001054159104940c00200e000741469030b0005070312000c0e8a000c90056141c891002008240e12000d403104250000b405070700710748443c01068442d100655014000030b5540c08410042c030300448408280c4420100d00081a02040b140048240c0064040c0300c0c0d000858170031079010f802c040c10102c0c02c06100340c907200c1c02402140b007904100700d900003540c10424000c0380400c01a0421500500c51460440c1c048040c45d40040c0c160912 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 596361771 1250 596360521 596360549
    0x3270a030c090c020c15090a0308040833280603030c060b0d0c06110f01020301140a0e13151b0203031b090d060c090b1801030b04090515090c040213 65
    0x803e510224003450011390003070020b2104088102c88004c0c1d41c204a00d4660490501c00740403001c00c8000c009000240590401001c003440c0030380040c034000203400c07880d151010a030607582921400c3d4850542c1d014041e0103600703010b0f10500041d0f0030340448070030100e00028642038000c4203140d0301c080c2a9000c0c60003604180041043c1006000f1103032819a03001c0d000752030444d0705203c640d2080c100c010410010340d080324150505031a05508a901c281e00c10000d250400031100aa82410b4060304024881c40107180b11510786000d11062085280340002c25820b41d02c3d41b917098a0480d98001e5103141d441410110745002c00080281d40c0354801d03510350046100301080407600790511400c4410216000e005650030305a1a03648101402e8400858020702c9802a0046201811032024000d40d140a1b460b508041411900140c121114582414001c40c10200108089840020343c501d8803020300c000d0744459918240c140f41802a10500d03a54803600008061404600950445069450b4070410280c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 596363021 1250 596361771 596361791
    0x308070b0609010b0a020709020f12180f031602042a03050402091501020c040e0a021921110906040204090204090603050712120e190902030a0b100203270a030c09 71
    0x200b6019a00c000745c011b0740000c200b0b000e242042d80140100444021984d401d001c04941e00e904136107001c540d1600c02e101580c42406981d64200451350355400f244d005180741c5031a00070540b2607003400c136102900031034030340e00b51262001d2858032882102c90001c0c541400b81107080401005444191000c2c0d2094501e50045201029000754807480060160020312141c007a000911000d401e071102c92003503500604440d00c01507160000e1200b843e101c4c1402d005243c508000e214083d000c0c240d00c0c3c0710014510066800006001c100550328481012120004e095884c440001d000c1d101c2c5402ca6096075002003000102080e054100c2c0060301e1040058070080750710740300300d00c8910700c003504040e024071000241c000d01c6a0080324244440280605000f541ea802c10380003000b90f002e6036200c1d9a1a035400000c00c15008041c0c410481c0c0000704030b602c11550307111070000030358074040c0342c0ca04110380541c06426222800f01610942c40301c100a07200300421076580c02c0441d8141081d10034040c2050400c0c003022 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 596364271 1250 596363021 596363039
    0x12050f090f03090a0608090a0501020c1e120304150e010609090c080d05162612070e09070f03020d11091903080a050306010516060b1302190e06040308070b060901 71
    0x2054000f02501e0400c0944c54180b0032100010050318804650003402c0b0f501c804a0401e00040513158945402030000300d03c0c80104200781d5510004076100b40d046182d9110400203203e080703a410030b03001158548940e2440390001c00a00c20415841501d41c078001c0300041c0d038401604a031041c140100842c40700340303580d203880399154003850000030001803041028405600b04038000d54251805142d56050011182201c00e880b1419a51079515035040804d40c101c085081180c400d074040d009203400c3c01c1a000480c0454403411014080005101d04242d5a00d25144a541a52100c01c41c050051084c1ca81c00554400141d0003c801c0754000e2440003a080820b8101001182c212035100c2009440d0083c182c2003100d6507000130700310390304022040110304900005240001130f902d020754000105841c50ba0f040200180001c0d190240343d9005202d040c040d9030b1920940b00c0c1c90300541c1030406581000b100051914400e981008107071040114002c824421148140d91042138152040c10650340c170f8100503 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 596365521 1250 596364271 596364277
    0x9060212030906040212070308070f06110c0604030809012a0e030616030f0b310b0f0906031c050301050307060903020d02100905030a0602270108010e0712050f090f03 73
    0x501c410b5030200f004500141029003501d50844003000035200103130348136640c0c41200d5001010030340e0000c05c609082c20611030903109181c24044d13240052440e0640700d000031074581c600103001500340502c8000140d800c84080d00001c0655642e900709610b0315040c0303942011101c0c02c2444000c0000c540c94110180e03820001801801030380050451031174907010f0741d4100c3c0a403015840f090401d075211011031405494030700c1d40e100c100c0d42c0040da00c40a0112010542d5100c01c85243c217038940f908200c042aa5030320359100710364681005403403000c81591100301085c0391102e1030403030104145c4200d034024030056210b0040c5068641c21404c0c1ca00469a814084460391000d00001c2d40c00900300d110f120051400b040850344098a6091101005583d0800641040d0070130303070300307441240d00007071091034000e503070b80755420002d03039071802c518208490000003824020140120700c01105168042a070350f6000d01940700084040c2c00e400e00c054a803101a03803051510640f50b6520f80e1069540780b514801021042d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 596366771 1250 596365521 596365531
    0x5010f0503100903050f031e0a0b060702090a061d090705030a12080603120c0a031b0506070807030f1508100c05030601050703030e0a05030403020a0b0f120916060906021203 76
    0x42c480118110225001403000030012014400200909001c81ea9008007440c4111410b01c915800010681e10000a0000040c040c84015141c001660015901c100c190352400e034040d100c4507141d54550320300c40700810a03a0440d210058280b040380009500d00d01401d44075640b048151080c955a40d024180c0d07a0900640c02400d20785868641003c19120781c1d1099400705004040f9480701d0b01d041030f455100c1c4e11641445410b9001604184240f42d00001509400301d1001446402804103840c0c0544660b00505004200034906000c1107015100b074004003207002400f10208104032660240d0800248244030340d030311a015070300800085813000e1244103207040b610380701d9503d56620840111826480b20700103c052560702c018142c589442044055002407240008595a90131401041103c004507448404030000802100d5800075059081d2421440b051044a8103600c9240500e4201280c0c014120380410b41800b000548550140c1450101c8010b90243c81c0c02c50b072506100f00c580d10045030 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 596368021 1250 596366771 596366773
    0x809120102162d0b090f03030415020a18080c09090a02012304080609061807180c03020c1c0305060607020a03120c08030a0501031a061806060912010f05010f0503 71
    0x200b01c0416240101d0510050107140d0986041407100c8001c2c0581c0894003098896a1000d0108010383d03c00300480c0e07800c1d0003e0401941103143c107503200c040d41e620307401d13203000d24680116146042034010b000c0c541d03d246900d03940300c044039181c11945660385054078185101d2046075000c210505e90214502c000b00d5010703520300d0742c1d0210260f402d502d40d021008130404040c20400c4005013050091000034003c5180101904d035900b420b0b0704000c03190312401d10981081c0c01c14641000581c6450f14640440c5005020111381c201040c41d0139002030007040110381c13023401010040c1b010701000581101024285850170001901e0b2901885a01d001700100213400001008080c404994071420440110009240180a4003101e544070011901700391054054240c5035001030040022202d10f00e0340304c5038601840c40141c80e100001800130400d80b032207404040685000303d410f41d00d940c4102c4d40d44510107480324600148200100d80206500119100c0962501d00007243e081c1055290604a0308014 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 596369271 1250 596368021 596368057
    0x319090e060405042102030301090b0a1203030e0a080d02030603010507091a0d0e030c150603060f06040f150b180a06020a081c052e0f120309120809120102 68
    0x720034000104409003054610310030a01c08610b85001c5c40745100d40003c4503502840c1c0725403412507071a0940e003490340307082e1003252050030030f201d541c1c8103032136011015806180105072260030582d40790500911040281494600241d55803032610130350000c3d400b0b05810745c004c01c125030b10008221030413941809090401a0010342103d8020104000b414103a010403c000804184d0044040d246601c244415980c0307070880c0031400503210702c01c1015980b10034103801500c0e55103000000d10002e100010309092041e03642d43c0882c0c0c400b020a5203c0b050138101441110440b0351200031000301a01f2944400c4400b012413140314540741050301500c401c54285030001c000b1403000c0c0d901d0108640100285d0b41069002c000c0c4685500c01078020759014080901c1c00301c070300c00030075540524a0714040019a4000c5074107207040200c0c018801c03883c41161719807a12503414245500d412a4210060362000010708d46418000b81030003800002402c108030700f228828185070503681c00724241d004030218540100e03426 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 596370521 1250 596369271 596369281
    0x30f090f031606060b070507150201020f0703080403051b061602240402060f1201031703131202010f0e03180a083007150b04090b0a0905030405060703020319090e 71
    0x2802c00802c08900c210b07004030755a0307200c2510040c980c102510948145e44400410001400c040003034001818070b500c002d500e00003840101302064071428a00504020030300340043c0600d40304030b0031350303204402c0e151074401d203090504002c5035180c1c426a80e1400d852031072101c3da843c4500014540c10385240a86210040301080b03e04084060001403003a038014804002c1114401c1d07440000309030f80717402e641c2070740342e90750440c280150000d400d0b1500d201d41003801c0042c044607104035240400c0d02c40d4001200c404107031015000300e014119403821906414140340c00300e10b981e0b0010003e020744004d454992004600360300208600c1217181d10416205030000b90b46592030074160040e5424007030520070030a00d40c1101c151244035641c0112000d88031600740d8600c01017502c103640201901141c04982c01e0040740100e0719100c440ca01d02031303c500055992001e00c03204106040c0180c0d80245401031109840c2e003405d080c088d4030b951103882005c1c0190f8648600603520b50181c1481400d890008070049040e50310b03 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 596371771 1250 596370521 596370547
    0x3330e120a0c1b050a0314070b07080d050a0b040f05041502120109020a2a020111032b18050d1106070509130b0a062006070509010c06110f030f090f03 66
    0x183c2040344048500000108a07038858052800055114149100c01c401040c1c1c0c99074240205030b001420142400c1011401288a50781510444646e403600085c0c80d4440802c100b0007442142c541d290490f0608401f001c8900c7d0301d0384660b1285002701e17810113074074000004110072440b804c201e10071100300341d100502c12103415038054020103001e800c2100680300d0082e8080401500181c840210507040700e203580c02c5580c024219404007015000a505001c2252420f40c5803009027241d5241c82600f0861500d0130220903040344a542c07454a59550b0070b14100d041030b907195131505942c1c01c00326021400c20b4a031088000b5070702d4400d80250340d5840c01c2c9048032040028005075603071140e182c180c490105022079581d4400c44001490940c55801d0f44201484100c1051011222031001d0380c0c1201d010000350503007040403140d54107401d00e084083c2c0303c420702e1704900600300d1a008411412010619440100c80d107402140078000715641c81000d9070f20745a46d1581c400010200c2e0002c1c1d0000c0c80380081800d0 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 596373021 1250 596371771 596371793
    0xe031c2307091d1f030503030a0b1903050d080c0406080f042306090708010204030f140a0b0103080a0908240c270406120c03330e120a0c 60
    0x41c6042d4103501da0340d401d850f00c1c2034032084500912464440a202400d00341180c5200e0f241c80c42c04409003114910344596440b40001412100d41751389405400c0340950f035801c454032101164900c1010b1443d120704080f81c1d80c12002845201003041400800c0c020600c0c0c0d000d81c0d084420540d0b84020540c1c0c1d08419024003038025008a81c02c4076001a00d0b020340e0300b551031020a05503602c004025519154510030300d080e6642e03100c039031240d10400c010304c04105900312035580c1a4200c03041c00b04c0801c00c44a0245010100100605105400380011081201c01c0700104001e03002c1d5507130341031800d44135981180c44601c041a102c000c40304000113000c1380404400e066501000c01407002e0f003090500003001007000d00010000d10b14030310506aa40c194607080c400c074005090040749410342c1c00c00c44d5540c1a182e460500010300310000c90500d141e20540c540c02481c1e1100d8054010000d404d440c0c0e4031035405400c0741c0c074040040380a81c1d44001c09041c0c1580544039098030681d0350915a11190b2599413080d2 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 596374271 1250 596373021 596373031
    0x608040b060d061b020a02090622020f0f040b07060506151204020103021b070914060a06032406080633030a0e07060207030303060605030103030c020f010c060e031c23 73
    0x703480d400249030413280851031004580c0c2070340140151a0a610402030441c100034041c6120321403c0140340f80071042c90201c440700690080700140c0e034851420300c1e52031a00404039071151000001401140c408031a41c045c004040c41038105015a443d030303a0420403080210384800510085c140840c07004103842e1201e140c0c01a006040052038400340205042c0081c0c68440410042d6020b050100f1510a1904c01c200856030140380580007410300c0000203000007807a12981007010749034031140300ba07401988011611911543d0b01c0c841020f59558001d000c01c2c108940040c402d200f0483e102ca0116840341c0300d04c0100c006465100c101614041001c0320681000c0c05d0030180c0307640e560110603040000c01851026245e190010210180340d483c00400344c40c0e040c1c03c0041007150610040000941105d5040c8020303504441001c0701c2480140100c030300030b0503503a0282c000d5090691040e00a4400300040502142c231403400000c0c4052001c5403001c0d604003484136403074804141c5010048411408005400c4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 596375521 1250 596374271 596374283
    0x120b070c230f06100501080106050d0609050a05040303150605030604090c0f03210e01050912030c0d11070902090f090402030f010213050f190303050d062105070608040b060d 76
    0x2402018a401c15011090104065501c0141c40e608102e50030840950301126900c08200c04c18100360009007000d2043c8a079400780305002c0303100080846590407400152100080403c43c6144c00f0100034040c00c0d05680071340220380f401c03010800544200c005c81c015112251125403560311070000340401002210b20681e041c004100f4041201c0c0d1101c00003500850003010200e004036081c00c419007550244000d010140aa010021011640c006042d5030400000703c950306031815406406130700314841d081005059004650409100c103400a01d90a15203900e030342200d101d182c0710f400310001c900c1407464859020080b200d00300128902201302c82d40c420700c0a0282d0742c3d00300d50221902d0a80c0c0110030607003001a0080d2040c801d505110880702071000c8204c80320241c101451030300d5040c0f25510700001d020001e0001c0d40e841c0801250708900300400b03403400e1803083c601c049616000d00900c1072004480724010342da40004c1203441541801e000300d42050f80a42d05441d00c40c2001040d00c42200102c3e40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 596376771 1250 596375521 596375543
    0x5030c0c0a05031201050307060c0807110301150f0f061b080903152a0a030504110d0309031407030822090e0102030702060f130204180503040b040807120b070c 70
    0x180a03414805003492501c91401151555880c0c0780344030408a05070040350190380619010449598080302141c001500900240d82c1c400341c07405c08c1129141d4601c85240c16609105509002c001103030f142c034085440080c0100903e903110400c81038002d010f44030f080005482c0703d12074504405580100d02501c1d00c10090700b071a0488182c0880d04015030000200610203001c4c04000380040083d54100c08501114008503440320180b032071045038043c08900340d08059840c0001010007082c07c0007048801d000401801070b0020034900102480001e0004407a000859408030403001c00008102c025290f1010405041412140d40e0035208010304000d0000d0400d080c2002500305c095210f810f1a0f0b44201001582e61300d020305010746040f1000c1d105c411041c1020040200315411803010340651981141c000c50340f00310400700c100501a09032170140c114000018009410a1203e00600c03c540000040e1404640c1e100d8900365451580385015001582150026030300600c90303d0003040e428490400c0400c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 596378021 1250 596376771 596376787
    0x501022509110301060207050105120f1005130f060e060604030201050309070e01030c0305160e0a0f09051c0801060c0506340e01090902090d0809011215030c0506031605030c 76
    0x989195050b201a440c10000c018407a0725410300203039001c1c00702070900e07138944421000c80000c8400e0041841c5c01e500c03803c0c0b001c5070028081c01c2c00240141002844003000c00d6804402100408440c850096941c0c81c02c1030000d41c980344124420f1148000800050030b051440d0010b5450b070388000c20660b40c901075030320089115542d2400301c4d80a5402050307644000d13402d40c580a85800d0702e041144070742013580e92003003003211051050668003000c81540801c0d80c90a41d030740da8020304103803030700280f15000300345284000c0d0f10b02403941950742801d5502c02c00141d0b41c2c2c040c10f03030b2801080c0d0005031983c0c00260010743c81300904038024a20390781c1c003d03c3d084040610107008640001ca000458002000d10062595540e84020a813001d090103490451408088000154542749540f02c01800008040f8001010360701500143c401d043c14488103118404c0c0b6036802d000000803d0108603500010140041424203001c0c0c244d0344648003011000b142200c402c80b00395500c2d040200301c001d02d040704100000d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 596379271 1250 596378021 596378039
    0xf1a0706060b03042a0312020c030312060a0b0403030c02011d120109030e060405180703020f07060c1d090f040804080a150c03111206010e06040e041b05010225 70
    0x1400900074482c44a0712401d051a200442422000403104001c01d0203400c1c69603000034104442c11282d11280350382144034484d01c16820816424040340c1d1500001c0384140720b402500c43d400e0320030750080310344521031921100080307070300d0082d404040c000964200d440001940a0142c5088105c25001d08081c24400e000003c0d0324016803030b00c40c101c9a5100e1608908041d0410072105d20204112002c80c04e040c20b240100d01032046c00503000405d80c8100340401c0d0402d00070340c1264402d07001604a56510929810200050180300000d9000142c40510340b042c4201443d03d800b0f5100e01c000e000d460709803204d0400f40d807140d1001d402590fa80c2020040007903114000c100703020203e40304103056501080c6091100d011580ba442031102854200b40c83c03644015481e034100d46c0c51b583d410b40b051400e5218040102e8031020b5011949410800000700410392900801c0040d214500c01c01030f111109240741d10006180c030440c0308443c0984e12814041c030014906200d44140d0310f030b00200c107082c01c0d80c2d101212 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 596380521 1250 596379271 596379281
    0x507030f08161406090c03100f20070b060409030c060b0f04020d0c14030106021c05090a06050408061803030112020f0a09061505071205030702031b070609050a0f1a0706 74
    0xb120185201d44811500000030b12540f617000d800d44001e018510413460100740c13907000808a0702c0207507903590711b106100c1030142c1c48141c40c0320080b4207041030055800d0341c0c1c031500c2c0c0c4070080642c1c0c4020b5050010b91649072074011f4410786540741d40c45015041d080e81d1030b00017400c1d5501d14a5402140f4140c40259070701e443c409400c010400c060007250300180c414010b8501c10540c01401c2804500708014800181c0000c0d017103c1c07440c0301c0c51509001809151007154030780140220a039010050590002d0350a9005014000b6141860162481a1141e800e66011014040a0440140c00a000400a44e040102c0454203140080c240d0012018088009a40403400d900000005036503030600744001000c10301d020008941da81845460f1842680b18403145c0b4042d0f00000003007040000004801030300c01c0c02a00e03401e102000c3c0281940004281240c2c0b14280c5018889c0010300c2c4000c0002c10341b80080001e003c5603c61922002c1c0141884211522280044a2804481c1c001c1005070000394140c829 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 596381771 1250 596380521 596380523
    0x2603210109140903091207080f0d0e040902030a1209030209040506041205070c090902220e010b030d080c030a0914011b050c06060f01020127110307030507030f0816 72
    0x194915814201240c0880c0e000203200c2544090900c100a000b0b0300020458000900031541b10030721820000310340749002e80303541012141c0d001c0c03083c0684403404002900103c102c00d540b0342105011000052104507200254007940c507901500d00741c400b040761907480b8100e03030700e152074510205912a00812005e00003518222501d602850400c0180913004031134406d60b060901e071061400c086505c60443d411440e008071900c02c2e58855a0300115926803c40d80c505520b02840241785010200b40900285007500000a440d420052562003514001c501604d0391907194442c0c101c036032070b5400389040030341000741102e904540e901e80c843e002c64030f0f805400305011141000480c0e01c000e5640c41d6002c49100c1000d40d000d1060500c0941039806000c0345060340104140c810031400c07085600100d000d02010400d000c07030010603000e040c46040c141414800306901910740034000d54a56004c1c90395603900c5100240072500642c00500000710840b0b139280945015107003071070402140b2050603148802000c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 596383021 1250 596381771 596381827
    0x910060b040503070503060106140f07060c0309060605060301050102100e030c16060311090f30010b1903050c06070606030b28090206090105070317091e06012603 71
    0x2420002c0e032408000355809024150081c05865140100150000d000d00700103030207581001c81c0f41c5401c00e05450035285142e40202c020b000c443d883ca1030207002420040f9058039010f040070b0001c101c50a142088074100d980603402020710048448591300248400008502c2c1c1c4e0008100080c800c01040001c02e422031003640d03586440c940b802501074103d0301e6140c200c02d060103041c00310422079594004c40400da40c000740c0b03108204000c8070040442210510020250a44403a2280c0c01c03407130300550040c014560181d03000c80f1071380d27400561048101d00a100051850b4041c0c0f103550714a0900602a0810341c4c401d40001c5a04d507200c3e42e0f290f00f00e2504507140c840744031502c41007410900c004014100c2c2c094071103104000d210384a801040192142000050502c0000102801058810b0484d070b11035481807101c00106080c00380c04241c5410444036103451846115649100d803000215090b4100d41e04a8601c10401d80203420f6900074100500d03000846000501c808007031038950119006034404402 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 596384271 1250 596383021 596383027
    0x1b01091203030c11120403120513170f0f0601090c110f06060108060f0a0614040b300106020d0c1518060f060605160f140d080106030b010e090910060b 66
    0x80003410b6040031413841d80b59a02803d010386500c404102200e058a0700410000d607016003a02c81980d4a02c24074610201c0c60000300d00001e42d03407801c00001c2c500140c3e800d058854003000f000056607038510b42c0c0b000c00040c2d0007400042118085652040f8403505803030400c00d844030503000d612030070303c00b0248680c2801e81011080000c1580d0001e1030a0f0700003801c84d04000402100d0003c241d0160240c0224402d00c41c00d0400c0303840503d01581541d000388880e08000390f80715400c3c0300040354034149a960f10030440381c05d0f41c0364460204e0b400b40745050391070560060030755050f50758084440781c010440a0b1000a00d0b010f00c0d030341c1c000c554001c08400d0b92040c074403030740781030b5140c80d00000310380c04542344950903807900b4000c0c44819444402c81d2401c900e8079200e8099a1070a0401d1004034404410084c4076414000401c000850301190030b150b035000c1521804001e03a62076905038203517020a007501d800030701d41031644201ca103052254980c000c20308408403803416420031411411200075401c0340001031004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 596385521 1250 596384271 596384291
    0x306081c1403041a150307030606030b1302241b01050411090712051009090b04030e060702061603030f0c0e12010c091a0903031201180506031b0109120303 68
    0xc034100c20039400d981d80c0c2161440c900758580b6004c4000c415440c00306865078102090301401016138129000200034141d403102d0366246083c0c0004d055510084501d1003d000002c0d540051081c076150f4003d0b00074103003005060b0107024000420114070140341c1e100805000d07080c0104201021200318410342000011503040034246070682c8100e0403240303886400d6513010021034550001c50708003690700108000c5120b03110381507940320703024181d00200d03074182c54140b12900303010318288920300460003a120700640b1402d075006c0c4074180c41103100103908203008101c0c00582964402d410581d0502910f800102c2c40c014104402c2aa949141d2120018400c400a0002460181448149400000b0080140c5140b446010b02601d0581c400c2c2c80001030300390303075070305205400908550803c1c03801010307a940d43c0900d4203a446017003020702444181120f2220401d00740c0081e03104032400b0707203401001880100c0f1203004108000c409040710320b04210019400103900c42c0e10950031a000d51180e10040b40400c50 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 596386771 1250 596385521 596385527
    0xf06090b030a031d0102030708030a050f07020a052d060109051b03060a2d08071d0402030c061e030112030318031b0c05060a090513020a120c0306081c 66
    0x1051030400c1c480d800c440d44401c006604015101071014511106200503489540140e00f580600040504000400420460442200d9101912440701159004401d880d5002e0890f80c0e151034020081040e4401d00703407400c0700217140712124806003e181c0c140e041c40c20131410300ea00305042a80a41c42c00c0b903d40c418018240d110340349000c8100c0b0341c0c1c0515403d514100d0700007000b4235207501c2180b00c1c40d666050300307903080ea500c2d20042c50100d11000504921320750300c0f80419501d6540b84140720030f00019904000081d406010340038051034004004280f1a402003081042d08e42c0030107042e0b003640c0e280e200c86040c0c015214024600800c1c20784500c490b21289820090181c44000314421214545500340e203000039000000c02d84a170007882103034449800f052420311030420007030300280d40c046400703c0c580705031030391107209101510300c01e0343c811036000d104664601c180c6c02462401d4001c940b030080400c03210446a400562040c01a160102d02d10785d070740a585051040a603010310440160344039040c0e060760 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 596388021 1250 596386771 596386781
    0x1b01060501030f0207050307140c060414090a0915050c090d080d05090a03080406050604140c030702011b0f030209030a0c030308180604031725020a1104020c0a0b0a09060f0609 77
    0x7911110641c9841015070320140c41e80310303110f4010005502d100000395010b0301004010131904026046594403501e374880e407080450f5411207544a55250000112520350381e003c0c60401a5000e4007040d91000a042d1420180c200189800302c1d01d41c09011400d15a52038030044d0007049e004420040c0c0d608549002c000c00d440d0300a0422800780d10900045000a600c143c4003540a074010178001210f495210000317000d800b006ca0007020044141c41406a030800f40e4000b1405048640c0081120f0307100130003a00c082521112184001c940d008910a1109010b500107002c103540040580302544183d0f518480000d50940090700001d00c080c08121203181000c0302c003a5510701c0d01c001040c161409980c020b24522034000c04903940c0d00c1c08004100d00701c106883d40f804200c03621100e003905c00c03004000255510641141a00c139441c1c0ea9010004505040c4200c0d0700c5c4580314000b030a59421340b80c0310a20051406041c401e0703099030f2041040003041d51032080610003040140085841840c000000059071 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 596389271 1250 596388021 596388041
    0x1006090f0f05060a030905010515031c1b020d080f1e0f040b070f0c080607020118020916091502010218030c0a15030612060e010e1507050306061b0106050103 69
    0x5200050a1110320251078420044500440b0f54665480003110114082c000702d000c0200030b0b60910081c4442e6010a403810318004405804407114806210390b00c080c041080e01302d042c003003018020385443d01513860804600d803500180040d100c0641c60355409481d580880e4030b005c40d0810100d00134074131609441c0584048181034004038200021003030407075424880c030b00c201641618000780c4c42c1d007000121280c260015030024403403200d080d5030304820341e224041102d41d50019481c1c00c998a90300d00d161000c80f548a60003500780407031a41e030120720b080f02e05020020f03070b000d1007151007001034910111034070081300c071411780d002503110910320315480c5681550b124602d100c0d40200d0051032550f01c034070074050111503101c2400b43c084441450160000c2c2840c0d08000b02c1740c680b000003501031041a402ca40c401c80c00f040e00130080f40e0360008a0b079454008441d044105412210b001c103501c50700c5100a9500b100005000f40d182612080300903005800c01c108100240c1d46941e0100a00d43e050311a0711402 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 596390521 1250 596389271 596389289
    0xb0601033617040e01050d0c0b030a0b01141315050403170901090e0c2209020d02041a030f13020a05090405150108011b18090e06090f01020a0507120c0b100609 70
    0x4c1c2041802c0c80da5a40501070b083c0140e084848010500c028280130b2001411031000259a80c00c1212180c0301914101c501240800e4400740d009042c400c0c0001120400080181088089401c14103002040030b0842031a03010080f0074400403011510100f55002c981041d5005180d0f9002c4070400036084031250703072110030446008002c12609007103540449445c15120f1001e0f41a00700c190300007001e2a086504801c1495101281e00c2800100c030381d00600a5450740000c3c42d42e400d202030400a03251000311484411084000c02003451401ca004812141601c000d000880171a03c9a000c079014800840b0191141d5005400c203007002510341d04a140584181070003800030001d101142043d080584280500b0401c115252007010000104d4100c013429041e0404c0c454103191a25880d170390341041e9281c6080e03008002d0041c00003103051003120300310006038554905044682d02d5140e408000b0f00c0351101880320480f00ea03c0000c503140404d0384a42c0d1040b004014050401c800240781281e41c0d0010180 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 596391771 1250 596390521 596390527
    0x306111204080a031104080f12210a060302030a0602030708100302060a051b0a080c06071d040b01051e0417191e1b140d0b0601033617 59
    0x6080080d0005039400380d009000107658182c41c00c4214010010600d0f0307204c0c1290040390124000074081410389005198200f120342c1003000142403242841000b115000e043d88015543c0c41202c000c0032141d91002072840009070b026901d0300441d040910004044852075030000811607503541010003c2c2e0840e13600201101e0860940c0c2c08101c080c4151030007031040c448007051082c40c000f011003c096460f5000d40a03101c0200e941e00c1d14421680099000321040c2c0501c0000079080340c45034441c80440c0040c40c0d400303601c1c1c4484405002c000d2008010960410104010381443e44c01e61140c5a12140141e4611075603d80c5094001e20800340740c6e2460604c0c07500006200c0d807084d0481d4048030340080d00304001e80d045004040e1019540508030b40010000a13070102e2401e840313401d040610088445110303a0b021590180030800003040350a0b0001043d885000d80460119407090b0b008000c800c04200204800601c0d04804062040c4030041c61000300d207103d8070110804c02e0481c0103107c41001001d013141 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 596393021 1250 596391771 596391787
    0x3c1209061e0b010e190302031b031e0309060f0c0a0309030b060301060b070209090a0f150b040b010f030b0439030209010203121306050405030a02010e0309030a03030f02041e030611 79
    0x40d030400f071290364860036040386161910713a185e1a60800440c0d0050807038400040018030125569a03410f0707411701c00c1c001d407000d02a1079614010b200400030100b9005d145011180810042c05d60042000c0841c440c4040c840c1b060004810041c40c402d95000b9242c0c40d0009141d0f1811540049004008a001e40d0501504221880040c02524076035a8111054402a0307614040a403501c06d03259400b0b052942d2494411091041038848900c011440ca00240301030402071050101303403208045040c0c0082c50100c426003404d4480d82c44158820401403000c00d5180c101030347c00c8000c08401c00f0b000b20304001c2d0300c50300c0540f13403400ea070040c2c200d90507080550518144000103500c0c2d0180541c0d00c050050a0000240340c42d008a081001e0742e80c0c001d20800c290b08144c00c0c555035070741000c088a07002d0b610b0200c248050200c0001030f103418050007802000442c00c00e64040700940000901102802c3d02400041254a00c115001c8101e000036001110403d1660810000f9030708005480140980308101d541 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 596394271 1250 596393021 596393027
    0xf0b33042d08120f09030309040501060c060f050609060424080304050a05031902131b051206010e1f091523030105030307140a0b040c063c1209061e0b01 67
    0x181840d684d91041d41d40b10226600030a044d031242026465000780744c1000416503540054442e503841c3d010b55820004500c4510351442200c4007504e915a02080000002e41d0707900c1c2981190119103001041c0c0f1181d48841c00c0881c401031131641200709036410209041c4001c0c10302240e140d000300421401030140c103c2500030100700000c20034000c2d016100c801c00c00d1440d45081d400200d8240561030445960071908100204542c00c90791040c003140c0c902d0b102207083d80d0b110b0b0300d4183c240407000300b1a0225400d8050a0303020000089a1074080c42014580007500e81c80d0000e00ba0201081900c440346402c51150340802c4001480c0f40d04280444107000610150300c0000036541c14550004640c1c803180c01519100303141407150030008090720a0380007000304201c500b40310081141c01c69107848126090040034502e42e070803401010364440c1d00d00801d0305a2a9004c4503c0c041b05d04070ba04041016001d15040070301500d00c002c0c015102d007603c64004022440001040450740c502800e030801031440d0102c002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 596395521 1250 596394271 596394277
    0x60f180303130201050a231e090310050a060518100605072d020904140f0f100504081e090913030804020d11040903030f0b33042d0812 59
    0x1c0e04000c0c5c04113a46c051343d40100100341c400810b0350b01c0c0c02800c081c0c102c80c0c15040d83c001e1044284551140000d100c064600c04151880c20358018050102604981c464000400004068ac0031007500d0b13502c0002e00f40c50700a1100f0303042c88200c1c28407080345041d85522008090035030240003080741c1084500041000418400030440407840d0504942c0d100c4204803450303a070040401307075101c4d00501c148004c026254980300351000300c1009654a40030180003098955080d0380640302c2c2c50300b000f001e0000d004002e90100368018407032041c8030304000b40d84840c26101c09403400c2d054100000040c002c62540f5003440350130361080340029212029134003642c0081c01c6600c0a003000303016038a6a002481040b546440107482070601030300030024416241001805031403070440d200c0c2c215141031460304242c00c0c01203864403040080b801c0d4140212800d41c5a090f1241c070940c08201004040c0b1021407048201584181030003a03039030b1420b81222106c0c001424000d1680e10003600781e404107100049c0c000d04403090f = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 596396771 1250 596395521 596395523
    0x230c010b1c0206030f040c350106180b060d0c180f03021809070b0f07020a170a0f110a0f170d14070302010b03060c071a1306110c060f18030313 63
    0x190005840b64034150b00c0c1c0003141e81000c0d0a100322142200490300740c84003090a4200b000401800440c1c8480526082b03900324042c8142c08203140d9059120010a03030444aa401e0300036000d24a000c4034011020102c45840303000600113605000260340c500c607030410007801340c1820104524103504d184c3c0019981540142405100124a000104129414800000185007964243e556040a000c1c00d283c5a03001082c2240b01c0c0400d050301150702d80e00549201900140d003002442c1c005095290004c841180440454180c51081b43c0c450b803039220000c42d0001408007451000c600e0f410314000e26080002ca02c2e0560565001845400c034060344220211a01d00801c01c442e0759440444c10101c1c058002d90a4598140c03007100c0a0048048405009240c51805070010603003000c11702543d280c8408054036407440c031002c1d104114003c10310305d611605000100345402d514004080b500303913041203011201071070910031030401c0001079030407850079009884003a0080c0d440c0d03162000e42c26010005802c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 596398021 1250 596396771 596396791
    0x30b0108060f04020f011803081c02070f17071707060b010c030207090509030d060e1b070b06060f04090c09170a0b04080904150e09070501030e06040201230c010b1c020603 75
    0x2100002c1c0d0003440c6203c0d202c0c7c42c800d0f41c803602548070300b800d11007940030662220300c400c40f02c039800a5820003403090b65404c0e684002420944e203059241d00c2c10b291360310854120380d40000c0103110005886285804800b4020004d5662a00300500b007106c00c850000f04840d0500c01c1c0505107a00190b40422140300703803440300f400060a034880d40c500e10320b540a0700c0300d4000310a26000000c02d00c424110310261040c04442500d43c410089407c11554500554200034541001000812414a000806040e0020084000600300f81e40c03403400400b61890100d43c000840c4111000303205801441d861b8602404410b0300034038610542d5a52408003540003080603203c0000807440a066035250b40201001895607441c0c0d0b81000e44500850f100301c130058030042510304c200500003440354064000e800e510715106002e0526580d9640044d41c20078204d50b082e203000705108020041c11141e08000c1c05000800c4030000440700c0d07200d0207121800e50700360f00c400b0081c0040125400103a4031801140d5100306110 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 596399271 1250 596398021 596398039
    0x7031a040906062d060e100809030d0204120b070305060a0b22170f0a0305030703390306080309150f12010b0a02060f09123001030b0108060f0402 64
    0x41000c10041000e608059034048111040e41142c1c09050000b00307410304d03150101c0c1081d640e100e006036800181c014115400c4000648140032003409080c802c0c1c0e010310400140d0f460240c42c0c1d01103000b05ea0003500f05640c54074101e8042d90a0000b0110b40c00d501c4a82401d0410250400c403000441310280c6200b5142c0c0c1e031400141c024006141c0c0c2c2440b600940c2155a210441900c585452665110440314508184540e5039426809000010b80c0011a03405485940c51611100c0c004c5007c0d0100d10000142000303442050781d0905901412880c2c40544540350b0381d0150000d500050540700581d1040701c5950050220b0f815550320340d080303800106000c1503003694030782160120070b021303006450000c146881c018000103448500c1c4401000c6d002075507401e07162542e0b01c0c03e4818040100c1504e1015903540b1420b03104104d550b110000340b4920320003406103090104035030f210b014503180c45003c0550380e9400030010010464071080300d41c09041d2444c0500032030305d0844407a01c000d507401400648244402 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 596400521 1250 596399271 596399273
    0x5010c140423040f0605090903163305060a06020321070903050a15110a0f20120d0e0a05100504020d0218040209010f0303200304080613060507031a0409 67
    0x42142c030a00c403000604148944504159644028903d501ca0140140c180c8000148504000700071910400340e07084007002c409400c2e4039035681142d0341a010304500d12080712440000c0d00580d60a0401002c800f03400b180c4d502d8408103200e500c01542e0301030001d541c070a01c510710002ea115800990060784548d170b9244140d682c120102d800000643c030240140c050411030b281800344100c0c6542c204071a401007402041c00002c1c02c1e103035600ca44048080010103d461300d4501d907100310407078030201041e05400303078000300c01340380c0c0300d00b403210112264008081c0040c03c00031003101801407a0800080c0d078007410241180d510360300d4945000f80050201c1c41d5550000600315074030040401450343d0090b000d1110b8104c1d00c50a030b200758405907010791203001000c00000715a01d20500b101c050301d0303165803120708a08506020303c10f14880c4103c01c085134041408080f40002e070412201d4420803c4400e540580001c03410407030304480010301003004050500640c5840c9030741c0c0008480d551007096070001220819 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 596401771 1250 596400521 596400569
    0x615090f140f1201050a11040b07020f01030f2d0204030510050403021e010203070e030d021005041a070207180c0c0330021c230703110a0c05010c1404 66
    0x4040465903ca01401d0316a0340d40030055004074810a58010104488071042c41d00c00300c5401a40f04c0c0c80a05181006100018200482d5030340d030080060501061001000b001031050724a040d00550030702c48110607a1044400c40c41245010381c00b079840c01c510f814190344459460b0001c62104440c4075441e1b40c041010544200f09400364030030514a01108c1e071145043c054080c0d03000365103e03c0024240b18540400385408235020a035a01c15400070180ca04102c02d036200603140040003030340ca000c890b0f4200c14040d80740310080c0c0d202d8000d03a40507010682c2401e4a11819039a0307044c004100c6458240458034143e04a4006c00d10260941001c0c1c25240c0703071303100d1461420000001c5456a8070086016400f20446802800e41285c501c0c43c00314200c1080e44c00c060445810f0700141e220101c0c030310285010324400c001c0698002d10680f40c085003c007140b070008003080d8080e05101000800450300641840070071320509510000038a00700360780f101c2c0c805086136540514007403c1154520785c480c0c0141c1542d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 596402877 1106 596401771 596401789
    0x60807020f01110d0b0f06130302180f01033002030913050f1305070803040608070e03010e06040b180106140a2c06040b040207060615090f14 62
    0x100c11403080000e17003140200303160003140344000404140c440304020401c0d200880340310a8810701d18410300403001d588901c0707108183d107580140840b0940074680ca90450750808040d0007405c2402144050121820480d030400300228a040c100113074020020b00891241154440c0344e42c20048212000e40380125140b0f00400306a5000502600d020381d414180d0b10300510844140e940ca54080387d10316403243d000600032500390010080a1548040d0107004204150002c1c811440903000c4e2569441d0050001000c0f0010400010300f40709001c090b203100c120f0002c0081c400c55a50b01801006103c42c2c40b420782c0595100f22001c102c41e80f854603151030702035040c1a00c1c021008100c110354100c5201505a5511070f8035503054040750354903400a0b148440c01044c0c0000c0d460f2070300d4160100c28805900d000c0602403000300402c88110540202c0c002c0707820101c40350200c19040300c00140d6142d = true := by decide +kernel

theorem cover : BRFrame.Cov 596223021 596402877 := by
  have h0 := BRFrame.cov_init 596223021
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 596223021 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 596223021 ≤ n) (h2 : n < 596402877) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
