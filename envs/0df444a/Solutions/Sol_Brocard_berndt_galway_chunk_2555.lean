-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2555
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:03:41.448458+00:00
-- url     : https://prove2.me/submissions/3e6e8534-f751-4fd7-ac02-791d5472ce4c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 459352517 ≤ n < 459532374 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 459353767 1250 459352517 459352577
    0x3060c050301051e0301060b031e240127031b0b361504050f240a030b0d060605030c090c0f220603240803030a0b0d02040606 55
    0xa00715418500012000c03134024880812031210414001140d0750250007500041410f2881c45076282041d43c0301e811000080544801c4021000c03002c01c01c256021240358800d00d071400c0d2100b02186101004540750306808201d81c151705100b011020000c103140c803040b00154401c548154045541c0104500c0c190b01e1a0311038080e8410a201030000c5042004d8000080c20300300d0082c86440d06950000340301c44400b0240038be00141050314180030400c0c040020820b07207104075424411201e4440810020019103842c0c12850802c200c5070f2586021148042c0010078100d05020400c04540808200c5082041d4420b48010351151b03010001401e0078404501e55010070741d41c10341c1c075241446030700072140708203090207800712000200b5150441c000c01100101099140741c0c481307850ba8074000140900119000c0003140407000074408140458440c80c4401c44071244061815656241c11060042c040111000e410010708000d003c0140e4484c8240e0b0003a110075202ca58110114540c07030030040410300060 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 459355017 1250 459353767 459353777
    0xc020c0a090b0102070b07141506040f090203030d020c1c0c0c0e071707030908030405030901080105090415090206280905040902030307110616050601180203130b090111040f03060c 79
    0x614103990b808914002500c0c02031071819a20449403034062082c0281d00d900108c24050040359110450243d1949802110100d500b88200100c92280800311252a20001c2d850361003000903240034a8103802400500318028281c9014903002c0006100382c0031010354240006200c101d0b040100600d402290010701000d60251a0502e860800030346541c4a4014920910442500149407503100e500b00d61544c5600060040c2c50342403504e059030b62600b007000800e006c505400c00204035030800800107442140c1120500c03100402e03004910380208040841030341c20500402a69a182441e0880d020307080048881d040250020000c00a28040441e04501d11550510701500b0140c0c0e07001003610f802c1e68000503440d112110840001d911841052400b03000d5491012a0009002000c0b404504030740c200d4445103005051010b440b41240310441c0c0d81071000b44904524008101c07490034a5900c4400400002a00c180b2406056020f8105034403000030b0b16034084080c800c0000b5801280d90700030140c180 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 459356267 1250 459355017 459355031
    0xd050609011a0a03271a060301140a18140d02060702070f170a050115060e0109030c0e040f0506010f0f0509270c06040303030c03050f0c091c060c020c0a09 68
    0x3442c1d19a201da020164205900d0303014011801080b50b840045180030f2501040c109919854a069034915412400710000c00000c0080c00b0f0342810702031440c24480c0c0005071002591000b031500010012004082e11010801da02e41d00042e201c0030390a0802080c2c20300902c100001e00100038a44003008100e03c0c1107400404080201901070104c082c01c0c0e61800f0012451400e49204007490002e0400d800342ca20f60030031f40d00000c0c04070222500419614182c1c1d40b100303100c5070000151191034a9100c0109045280726040004410b866030f0103070401c0c07195220504261403a241c1610f440000e0308820688801410f0400804100b00740620050030141c4101101c0d1a040c40204241c080e41c91700703140001c840d6200c0e183c01040030300c03032600a45401810561100e480c0e0034018018041c40c0e07803d10110380f40c4008a4081d08601403040d220f0090070003c1440c00d0703411014012490a0320034810481e11800c0b0300300d40010024041c8a0583d515a1b0081030074401002c200000790203035500098003140b801341 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 459357517 1250 459356267 459356309
    0x809060a0e030d020901021f02070312020423030307020a03570e0103030e01030b030f070303030c0905041e14010f120807050f06090c031207061a060d05060901 70
    0x8240c406039807000c20010303240c1c200c40d00117030309112114911003103003907a0301c00e01160908c02c0c0e406046414081c3e03494800110344072141108a1149000d80c182010080c5200c09070f2401012000c00280005010703a0300b071201540c003081d440301c0d00f03810440c0c5030508898985403030300c54412154600d8500340300c00b4692591042074100620030b150805800c01e23860042d1640c2c0c0e86055100c0100805102e4100e1805681d2410004c16100c03c540520b40024109621090303d40b0f40025800e12600740d20000d041180d1442e541900108490503080052140301040096507554178440d1280360100320415084030080e0380402000c50b1240d61010f0019501b1600600404500701659402c2d102105801c03400e0240c1c40c2404489400741c5100106548100d412403401d40c4804a141805aa85d040c12201d1589600b810552101440c0d0450425241e0038808d2401003800c1c0d8108500198084604114600700e080c04200b0b00c1e403010b85c18141c4e19440c1da003031103442e0810803c854018616000d5224414407409 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 459358767 1250 459357517 459357523
    0x50702070e0609151c060513080315010e04020c010603020a0504020f0d05130c1211010503092d060903070b1f330c0507080304121203020c0d0809060a0e 67
    0x781c24a4000e94028000800b2158030503103148180b10010000b170140d00c1c09894444d0705a611001c00c8442c1d81c240004140b03034850700b1100114641c0d01a100c10b046da91090481c10f4041c1b0200d54090401c0402000300c145500d51b4401002540c403424000300e034160031401400307c0041030f940100e000301c1c07041002ca030301d010105040e02d20b914503003071001c204c5840c0d088c2d000003000980c10000c0c03e2107000250014a0340c0f405483c081c00c20f4490402495101049801501c8500003259003a074179402c400c0d00c0140c40348400080584040c06001c08d148003440d550509840c0003003c48098080380e0000488405100d50301c02c0650780300002806a21248030f180c141109844641d21a43c007040181d892103da0990921001d04004c42d10304441d03541440f0240c2e001002d02c40000c0003a18280030341130b40414103940c00310881c0c0980703010ac098100c0400c050798a00851034200c405801c10158203000d466541e5600b804940542906561100102c4c14903c207402e007050400b41c1481d014074a415a50302c5500404 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 459360017 1250 459358767 459358771
    0xe10121506020a0b060a0506160501020708190f180519080601091d010209361005120106030c050f0303040b0c0a120c030c02090604090204110c2515090806040c060201050702070e 78
    0x1c8009c500c000c01103031408034064014114014202500400c0940d000040384145040224075517841c44030240074510140c800085122090700c01d0711070310744140300500744001c00a00c540300080803181c220b50344440682c1080c1c0c080e0001040c29480d844030300203003114520329610301c000354070003149800c8440b800102000010050b007860740c05040b040c580d91b003600d520111031001c40d00808440c0c500d00a140c0120310149805070922440300720010403403011051040400392a4803444041601f0f00340070400080350184034155505201c10080400c010f00c04001404142caa138500809042c2d2151a0a030090340035240c3c641c003006149540e50000c0f0754080113002a281d01a01c41c942640c403000082409440c04d1040650070a06020100764181000d000500e201480ca4040d94900130f00392240110028603c958100300c07010005090000c00798074076690318196845c2c108500a01e980320849428400d048800351092102c4403c00c125064081c017074280d1095841c1701401c00941007030700c60382c074400300 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 459361267 1250 459360017 459360037
    0x50f0f07080604020913060e0c0f0d110c030a020a12080705030a090203031b0a060e0d020a06050601030f2a09061b2910060e10121506020a0b060a0506 66
    0x16040403809035143c0382d04540000c400a01982c40841c0c40c5054030005d08400d203d048842c91f0b98800061413440400199001c01040500700c0f071070515840042c40c003405c010091040c2c080e50070818000662801c20023041203c42c00d801420044030141002c0102007030b001c05c1281440944c1040104099202048130b07032050000c940021044100d001080c55409032070190910314050500d40c0703000303210000700c122040d0300c02d0506000364210341c00165102d8036490100c101683c881d60341580000d40903040140c3c8a50185000500c00c0c086080314030a444d910000a12401e02c5200000d082c8a9041e00f02801243c0c2e500301107030880e24008004142e0000d800c1c00600086003802c04d902040000c0c00c2240d007900701d004041d0101c5440c0c0410001000d07054504100c05602c404000500038010103d45c13000b0030008051003194000e20406403440c0d65600c1e41c00c4280c513036a0030256031049640100c4400303002c00f030307005210119651800c4410302c0c0e40034101c0b61082c104403c041000c1d913503000c203d451161b2 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 459362517 1250 459361267 459361277
    0x40c08010905090708030301090b031605031513150207050c040603020a1203031103101e27020c062d010b0915040807080d120902010e040e0c12030706050f0f07 70
    0x40c4082c5003a0400c00075800a1115003c0000001809e510941296008610032400e5905000111f41405d100b800b05100f8241c00d0340204a18100c8854650b490660016000c0b103080d041c24401c4c5e44101c4001003101d82d042030280d022418000b841002c00c0440380c400b800307a80130091603046800080440d402441070030b00b1000b034021200201840f0343c0210278446804170007030707403a42000241d5400c500c029009240300702c620742481c0d000c0f04081e0355540d800c5031400380c4a8070761000744c81d00f0743d074603206a0301002e04074070740820090b00e11203420410f00b0310a100d10b51036054035444000c5a404103600703001d0f1030f24550b42e0300c6005010141210048448224049802600c1c941c8213807070010f511301030f5a004030064003a440d800140244003258506a040080d80d403c00c0c0f4100b40c16146e070481c4c9c12070701c0180c00200c0700400c0f0f000c1400e0503886440c8143d00c1da412a0322000c0c809000480c0000c0d448803070a000c2c0c2011401c3c10400440740143ca40280d851001c0350351f10700e07026000c07007036021004043c401041 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 459363767 1250 459362517 459362521
    0x6091e03060c1214070e150a0302070f080d06050a090905060a0c20070302150f03070c0c0b040303030219020106152307050307030206060a06090506070206130e0a0b040c08010905 78
    0x190044a000803202d40c1c44a003031080544d42c00408501007400c8036420301164101001000c94034000c40307600080c13022901e1080c1812440b00017200250031000d0100c0301c1c11180407010300409c03a41c4014000c008554030011601c0c81c1800c061100881c4194064089942050310b104002040414842d80c031003814540080c2401d011181200c80d0703040d0080304d8480071480c00c015908002d0100364113050b039000b0345101907410041d183d540600d10841110700da203810b0030702c08241054425400300b40b4450180480c1d910340390300c80c2100002640140e008074042940000d248140f02009164245c12860703d0000300402c61410140c4400c0d4400c6281ca01d08202c800041c110301c5c401c180040760b8000d0020201c10b45c8401051404c5507582d84050001d40c094442e240001d0301e03a190100d0250203980d41581c911041038500000d101c0c1d180c02036602240e001e0f50030b100c180b42d200703001d009040042c08201001003d9052502c812402c403240c1401c01d80c0628204904080c030303903130003840280c1103c2c41880005240c0d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 459365017 1250 459363767 459363791
    0xb1003021804060f080f06070f0c02040609020a0c060e060112020112020f03070c020f1906030c170a06050108071d0f030a1a010807050607020307030602091504030c06091e0306 77
    0x1900a07203020541c46464000003242c08031598400c0019138035450101c40f10f2803442c4601c1560b80b03a0031250000028082c20a181000d48a40f6041c0303400c0b880548003040090b1103500c002d0a90704031500507000940c020b49001300380440360080d4038820140d68041d000c81e5040c540c040a407250000130181c180305281200c0e110951083d8115120049000d00075a107030308112600510582010900744d1040407070101d0414646801c00c0002d00c3c0800002c640d0380c001e440c01e04158050311800384100e00f071203900c56281181d2803141090324841e600d100b50010b01d031400c0000260040001821010030024420b40080c42000c401c80081c0c0301c403d01315003488409001c0f80029150402c80c240c014456443c840016512101204840d41071355030712404e81303a07003540721028401d00340030b580006507166000b0103041021401560090090102c09001c1c40c00071000d01c00d5695013688503620480300e04140031070421400b0741c0202107a0150140c0c1d07441d856148003807020118a10206e001c098103c90351201a8515 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 459366267 1250 459365017 459365047
    0x1050f030f011104090609020909161106041514010e04021918090b01120b130f0206030f040606060f0e09070504090608070f090e03030711192001030b100302 69
    0x42034000d024040f1440d20f00d0065030818402d03002440d081013000301e480d600500030780b513071104d002c1c2404003560303103401c011680e0100032000c003420722100c206404421101805074a1045016808401000304450450b800b101d8548070010420174403100140908040f0341d507401d07001901260360306402c501c0b00b230450042640640c0041450341000d07284104040e0705400c401100d5000b40741c90b03656a03a80e005030900d200780e00040100118008030000d00798441c40901c04803454014049589507030216804500160f0003951a011319210796402c0104100e202c0c094100034200c0f07440c0200f8082460b000280c40d00c000d850b0800e00c500f42d200300146040e4404c400751001800842e0050290382d9840e04142d4496001e800358a51030143d007134012480fa43e00340561030000c0d502000441ca5551800740c125084150154801032a00407000302101e42d03020800c4000500d405000c210890111020001c0242e60401416505042c100141c1d07100b20780c0c40d50f0a501e44149903040c09030703544a60380e2011407 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 459367517 1250 459366267 459366283
    0x30c0901120308060117010e070e3f0a050307110411030c030a0f020f07020117071e02030405030618010c18090e0106050a080309240708090103090b0a3201050f03 71
    0x103019641c1c0009900041c0f90300310381c0a82141d4843d041d0860401d4248141100f001380c4bd104400c00000b40c146298079010350024546014014040340c0741041000382c1d09015401c1e00507292a440441d4540500551411000b44207030125010807543d0002c0600d01c419000051201560706004000112480042d400000c0e0884903070004556038480c0d5050102282c1001109a002410048a407120043d210f80c840740109410707141c0052000c03041101e0070000c0042d048900071804240000100c644040150902071102c1d0a01615a481d41500309401c45001c56070720010004400c480032080c201c25540b20702070340d60349003010850320403038608640502110703032200b900000030250000b84840b000c0090140c00781d00311740c0c440b0320140003030440f020414a8030150b0440003003041540001450703800208a5180181004582c55901c0d88030100b82c00e0b0101c40ca650041c1c0ca98410642c6c0d94646125074a0303030403501641194040941d52030700e50981c0140035460140c0305d03007605016182d43c2044258 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 459368767 1250 459367517 459367547
    0x207050c27090607180509060d0f080d06140102031c0b0f03120a030c080405150a14091e0f10050405030c1f0b1e130b03011505030c09011203080601 65
    0x4a541c1c02c2540860ba6a010204c80780c5000404890b02c1a409107040a4040200c3d01c0c014507151842e1a5081040110110301d08220b0b000e000320319081d000141141e0290511144500c40010210b1030b083e140401009a0342d038a03411500304001040400c54840c0c0212442d15100900090001c2503d0226880c2c00040f1445036061194003d4410b02940c0e01d401401900060765042c400c1e0f10105500781e030100c0301035800509903040500d601541002a124040e404442600c0c00310300051346481708980c000b016070b103c1c8141d80060504801d04041d050401052061034002040070000d03502e6902d0b150214905c0e400c42c003039250408101408801c009031814401c0c03040a41d1070201151814a02d00301010340340f003400c0c50030601740740c80346d19140c0c0c02001d5640402d40400540b8001204011a00c2800300c0e60301b0000b0766070903107185036840900c074004040c4000114028840c1c2404200740ca40f0035050740140c0b0031580c0030010300000502c440c981c1107882d40b508140400d40c5540c00142c0e800c01c5040c0e183c0c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 459370017 1250 459368767 459368839
    0x61d030a081906080105060a050405040507060810051002100507050315040207050102040b0c060106111518100608160b04121e0b040b1e010f0501051b01020316120207050c 75
    0x4104c40f00c0c1944102d01650007103c1034100c681e51a800d100595008071409483c9401c0000c2c1001110700400307181d03a0102044000750344907512400060150143d2603009401640303c01d11144424506e40f0034240c0292850825505604d000581500e0140041000d94059900032406a041090940543d8094040070000a403070b5120940c0d45d580c2c407402403007640001810340300103107404140400e0f02d4841840111070881e80d80c0e00c0054103140c0048195003220113108032050b520300e241e8584240c9001c0d20354171001c0c000360442d141016101e001d00c0c0e0024807030014100400c200950300c0844c00610ba50b84000d660320810480c490b62408a480402c000c0d01c0903a1890070403082144c006d00342c13031140d042030442e42d240c80f40301d170302142e0300450034042c000780860100e40070302142d03000d03c010f40800303010000c26007000e844460307884d802d80c1c0060700d010034a100c91405081341c06410031410081030b41c8080d0110305100c43c50300d07010355920004110502880140e084480d01980501651a00c01072040720 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 459371267 1250 459370017 459370019
    0xe0f01090b0603060a05040201020a020405040317360a020108060d0602030c042d050f0d0204060801201e030705121503251a040f0909061d030a081906 66
    0x91a090007040b96020312a02400c1c0008120030a1031007102e000710340680c004e015048095003070000400c40a8000d42c00e124135500700d071003e0900c1c0b0300304522480d1580705040001d0403490a0b400f4034226a801451000340c8680101c40c401c400041c807020303031030f02441d04074503648440c404104c280e000348802401441c000010440030000d05e0700140201c4041034450444603038400700e49401c4087d406400340c0d1001e2214800c21071450b004401507040b0340e005000310b07c803803a1540018111442c40d442104265122081243c50082c00d01d5080b040710800305200b454400c0391492403c0c0f0b00c500103612095880040041040a0300c03070000d940480075170402c3c2c414981460300070b01c20000c005081192081c40340c03918120107003107451a0103410131a4806a200e166040204c0181585500310140042160511001800c1c845080c070402c002c00e00c500300028108054100003081d030b442540b0f81e40080c14000402001c1e0803000044400000d030600d84140240c4614601064041450491007070a03824018 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 459372517 1250 459371267 459371273
    0x180306070207060f03020a2049081807030c081c0e030c150903160608060109030b190608060a02120117030406050f04150e0112110405040e0f0109 64
    0x2e01c203070a48000781c8035107410000f1280c04034164400c0c030192a0000301149040810340d054010449607280c00c0344141c49031025518008104090f02d07650355100ba03507100b1844148500c0026074001c0042d440f0002c1242e04403034000103041c680c00542029811000051030380d9280c0f07014809980616441090001c0e01940e8800d0182d44070340383d9403c1c00314005802c0b00700d00c21038010a0f445051f81e2025020b00402c1c0000c1e001c100800408022220b0110010005002c0c166801d108a000781c11511261640550401d03500600040000303191a041c0200000c0c180040390882008640c456507030740b203042d142008116070b4000780c2690342c8000003030711844007840040d06007038010700706011200d085585503aa80f00100c640b0007010040c10305c80e43d0000c0005100291180004044001641c0d00c0d40346855551036500c0c800c00c0b294480c01e000640e0342200c10b1025030b80250719524401c0d803480c0c20700c003404007240840094810f03849018482d0365944002c8000c0d0700103004400ca50b81e201002048201c980b81 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 459373767 1250 459372517 459372523
    0x21e070f03180e0a0f0c32040e0c030709060f1b080910030609150b0f0304021f0503010e0a0b150a1403010e04031e0801050415030f200a0b09061803060702 68
    0xf01c1c05d184150600d000c403107015208080503030340b050751401c1e1846020100700546500400c0c040031011081c1d003c0101180280c40d040d001402000741e944440d503245031104008101c07601d290000410084504880c40000e64003140c2c4042413a000090100c3ea8200c0b071500c02072a02c10160165045201d00d001c496039660035501c64422150401014400e44c10024000d0400f40b415006040c40380741c080c01801044010324001c0e5920a01c040d161603501c01a03085403088240c0c00d20800030000d8400401408444401d8142300d07000105c0ca442407001205041c0080e005001030244080070f40c10224084885030304c5461402142ca540301b0441d40d40b961586850014004201c5094000c140500f50305081031011004040d2040d40c295155921642000704000190212200d0354401d0031401b0404008210f50b5030a403828648580c0e88208001c000c00903000104040c006400d00c60b86070300d0030400c106000e401c1142c032001000c45001d40e5a032044a0b0f011410442e07841a070b0303010320903241040310703980d000 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 459375017 1250 459373767 459373781
    0x21021b0a0f060c230c03070503040b0304050705010908100902030c100c0b0f01030b010b0a05070602030a0203060a05030c0a030b04050325060e01110a210f021e070f03180e0a 76
    0x752400e100f80c1e16404030550b2056103482c818448031303c00c40011580c68020402408080754844245c0e4503044940c0c40f00342c034507000390b0000702804030000240820824100083c0004102c2030a21a1040d450300450b15281c5940b100d1420140d603c4261150856405000309044000010515012030604d420001c00246155804489008120022503102c0c00c2c4401118102d0354024070b502656806c0c160300103060740001590030b041c440d0034410f2000099250000c0e510070402c1c14401a10780c5060f4041244041855110303070b0080d003086a512400e030b203800450209032030300449032041c1030b00d0b180f414a02d03510945400300300c002141a11546c64408481c00240c089019901c1131101c0d018210f050303422035030a180507603885e490400a22011a000d8031002416a201448154107c440c03000e400c1c05455542d18002d0440303a0014120207031a40c0d015030303100d6208800403402d007018610b6032401502e0300b40c90805000c0c4090030800c10551082401107a02a01c04481c1d88a51400c01058a50141c215 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 459376267 1250 459375017 459375023
    0x2403110d090201030b19051509031c050408030304120e0a08060a02070c080f06010509070504140d05030705060a0510060206060a1202150c06040c0512060106050d0f02030103050c0a0621021b0a0f 85
    0x41109001c0c00b0349908c4182c41100f0801005003841a10161070840c0ba8882e0b10054818002e091000254040050000d18400e41c02491144010f0811190042c82d940720390204600c210789205040c081d03c080058a1680503285000050761000c850406100106d00d0741d0018010344526110501020008a801412600c040e21075001070780341c10b041581c2c03501550041070030004400b801403800c0d140803008107101c1c07402030080e2454841281c6600d0b003000c1007210f0483e010f68841c8107210504818102c41130041c407407840901001e003403001c0043e211040d54400c0040d8000000c021070155034414840880340e07400c0440030350780c907100942c2007038803044225070070f071051030f10890f000400e03041610317001036001c1c03188014141aa081400544081c0c1282c20050030700c580d80c041f15005035516200a5001e1400707100109540c0d05214100300c003400d020303005501003040040541040038190251041d00013503114001d6111140c00e03e920481040e000c01c1c0082d18440c43c010300041c410303441c1c2220a0940 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 459377517 1250 459376267 459376279
    0xa121506200303400213020c03090f0121150e090307240e0a21020307170f03070302120705030603030f03150a2403110d090201030b1905 60
    0x4400c000c010300d141001c100e0103075030b00200009894401070f10366410b06080780c0c524880c03a510502000c6542d200900d150360380b00194101e010403c0d443e01a5011071103403a03082d0298034001a03070108039100e00030041c2c1c0ca4042c1e205043c01a409070300801c081c00801442d1200c1c0814282844a10805001da00600700304400b507180380400d400034400702c0c181c81030701440c00942c5068a0390b40c0301c000c410f45c80f41c105402d01d0b0100340c0501004d01c03240140c5001c7c6940f540200061005402d054a02400308031072040c034030389190744956082d80c001c001d451070550000141032041c0c0120382000c41c00d21414042a1100c1000400c00c0074868150f0301401803a40e04490340c0141c1e5a6080065400b880185c84d071551660090280b00c03080b441100040d980714180d04201e0100000c40e0001c64280040d5800031905072030b4404115441c4030f900c0e07580740100d20551806100c242100c800c86013543c898103004241081d141e05050040d64002c0d00450070351940500400304541400c0204445c12015000b4207100310 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 459378767 1250 459377517 459377537
    0x40b0f0409050d0e0a1d04020f090112050111030708070f02010e030f18040b030c04020702060c07031a0906070819020c3f04170a0807081b0619020a121506 68
    0x42044000072061ba41c144504180b41580030302511100c1000800880e0301101c200c0000c02c494440303800b00d500900b000380020804111900d4114251003180c20b40d104500f40c10701c01c00280d9544281c3c201d80003000c50806039005801c80354100c2c090300300c0a040c2a2544400200d500005100000070b02d24180307001000d14080c502d907410042030b0340a04509a07899400a04401000d20b819401010300d20710041069203020780d1080e01d58106442c03644141c4044403010110607800282d40f0420341e10829900182649141161000d800080e028010304100304245140b43c1c01e0b40303882e41c12214542d080c0070032540e1030529101905034558000038050038007024800e166242003007003c0050a0110050221070801c0c0c2000c42e041b01d0202058400b25240c820400008007244603040240171081c0101c1b4407990b981010b04854886540300020a8219440042001181600010f4001d103607500c4034009640c400c0103a03c1150303007803441000d903545030f840e18580300840100b8080b0402190102d2300e40030001 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 459380017 1250 459378767 459378769
    0x70c02100c050c060a0306030c0816081f02030a0209180106090906050d0f0503070c09060f05090408090d14070806010f05060a02030d09150203180f0105090a02040b0f0409050d0e 78
    0x1c0e85003981c006040b40c0c0405041e10340c2d0b25241001d04040d0f9540e1400190030390f507984444d6222013903a80306180302d4104807610717000c2c1442111031001802c0c20400900040e031203c0c02c034141460350a2000d4069603404804124095440d40440c2c510300e00040c060f40b4110031030015850b0905c020f01c100408902d040c40c000508401c1409440100c8000030291b05018499441d81c0100361b10607101228140030070021140087d40c41076445d40900b6444000150007410000d242c0101d0304203411042c1b1540c0c181d170030000044d081404490b20385d24103a41100c6005620301d00b1191441e120015810725004424010030010000101c01c3e0494580c50b451194071a03a80080c001584615802200182c10402c5100b040000a40045c02240d20851100c0e040310740302c5c12000100d0300281c4948010072004183e525044a0400140e11040c1e4a00000c10290905502441d40d030014810001d0045407105801e125980c0c418901e11095100500f040c402c0080e90301d4480d44801007032640501041c0091024569 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 459381267 1250 459380017 459380027
    0xa03030806030f06011d0405030705010c050309011a1e040605060408010e01050a06060212031905100e1e130f05031303020328081b010c02010b011223071205070c0210 73
    0x121480b80c6c1d841c46034070405254400d10031800500a49251204201d2440091000d100b002c8100500e40c0d9256202e06110f040e40d03080d201c4192194085482d10702c000086a61226110a01400f40d001001101641c440c0414054500e030350040368407080c00701d030020b207101041d0404c0401c1041b2000030400d030b40d58540110110761a60141e1001a441900d400c0c403403600790401540c01058010301d80c0b8241c01c6170403040007940d200b2905034201301c0d001c01c020401040c0c000d4104d41c100b44801b24020f141c1c0d4089440300c0c6442c44c01004082a500400102018404224400c503000707a0000c0640743d581d82407250070340c8081078034403049002c0c1c41101940440907007005400c0d0061661700c1140810154a03031504030803034100918145016500e143c245030302c107400744140d0703011545580020400000003030000d42007081d90440c80500703506190b4104840140c5441059240c400e0000011a40d207d2342401c8540b12000b400d00044d4610700014805000d8004405202c114030888246040041104084407 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 459382517 1250 459381267 459381269
    0x2090f04050f0103030c03050705120406090806060108150a03020d060e0f0f0d0305060418060c1b020a030210090b280e030d0309050f0304090e1902060a0f030603020a03030806030f0601 81
    0xd01d10b409001400024400d10030346550341d0091030250f041c0201600c640b0b04004021950b80840315000404102d041d03045121303040100404000350240e880d045001170140344008189160b101007546540c90b4564503c10840301654001c0c22600a90030240f0b00000204a02c0f4140e0b041e92044216200b02c00340e0003d486840c001c0b14102034111500820b906902800014248592264880703240840300d9144484c140d80c490f004040100308070901d03080203441403034502c2c1c10018201144039040090789540183d14101d80e410f5a4492282c6585070f800c80d102005d036041512804000034581c5a4811021400c01070f002070143c98110003c0341c980281e4507806c0900d541505070f00200c190b00a881d004c0d500144025002e01d050304d111403c45800366081d076100c0c0c0c0085200caaa0352049541201d0700304030802001009440000002e045a00001d005001e505120f0003084540700e43e1f499003a203e600708900459000c1c02d170484171364072490040e24103501101c000303001c2e1103800c3c0c5501c445140001c82e01c1c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 459383767 1250 459382517 459382531
    0x9060501020d1220090f09010501090e1503030a121a0109090c02070e130b1305032205041a1014040b07020f060d06150c03080604051e07020102090f0405 67
    0x1c801d02e0080e0054404643e04500701c003000b5030390b64500c0d0074002c0494008013040700030000c2075a03696103041007154680365216003d0103103044800522481c0d07045598001502d021081101080da1030308901d0040b1000c2e001880d4160101043c02480c403a081454407080c6046001c0a000106100b15a00034501d4411100b42c0020a540420000f036042d640c409811112030303106076681651200c620440b103000c1920143c081c21403049404050007140b91040d9084055100034000c0340350399440780c0d940c2c0d010321200b1400c500341911a80c0528003280117403900409014105001004030120019181c184101f04a406400e50341c041c00c3d0220700ca1004011070909401d429428141415600034241c0c1003200101e0300002c211250010954505016080006201601062841c14506c5d41c0b40118401c2250f60140300c01644180000780c0c05c203d085501c000d05a40019460b51040b104484082eaa007101d144075800b1a4140016030313034190000c1054541c255203038940e001c191400d120894000301c5144d = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 459385017 1250 459383767 459383773
    0x513020f0402090a030b01081e030306102007061d0a030303050a0609020301031b1d060f0a0306020705010e070f0b07062c0303010315270512220906050102 68
    0x440061600000854003100d01400041c1400c0c403a401150b110000d039001030b551080000c0040082d80700400400c80d1200700350880b00d8414400d01074a541e6400003600c03940c41047c9400c42051514420701605468005070b054020000e01da000303025841d102c15020310f0001071074600b4000101411900d50030b401000c040c1602880c6491514101c000f0b0001403c1010410b803613042c005400c0034940042c4d0b0113540215002a21542d01c441000c4110f04030745d2040303400d00f840f00603000002040c9c000780c5070700600a4403403004102040c0c0000d03030404800d4100a240500c0031502c00203200b415801540c102c2641703030032180c00d240c486000f6a080c100701d00c50022510390030005840080c0694100c0c1d404500719034046807240501407044070081c100c00d2514802030b4030103c010818090050400c180309542c6c081d040005114022001c00080035401c81d410034134042d4841c410401004111031602a0504240e40342c4400401c3e0032901c000400105d040401d00e00c1200100f008070840c0300d4101103840503001 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 459386267 1250 459385017 459385051
    0x705090103050901060504020703020309030f06062b0204020d1505090925050616110f0904080c0f0d0306080c040e030a0c05281a07020c12030c070e01051305 69
    0x460242c2001032203081255203404002801d501c840c009040070a01c40d40243d0781700c0c2004070901d464000880518801ca510010501c800794594070710300b407100807945d003d400c86501070000c145110342c080b11000313401504c0082c1d081380510040c5d1050b08044404401301401d507130396400700a04420300390f65408481c3c01203c2e2500c0c015041031540005a80d1900301940440d0786c9500080f0150041d8001504003070310040c018040010042c0c03022807502044451a03400c02c0c8840214080e0400108000c0c0240400240c6660f4a80104108081c0b680b901081341c104104040b8010003401041c0300302030a03486032100600301303841c09008050760000104011428403400c513008860300281c142e0187c500f400307200b440b810010440b02945032a50300d46120348012507800c0c5844042c2d0740008401041d040b5400084c41328580d03000c035030314240a0040741c12002060006c2071440c114400c0a0515010b0300c82d82000184c020381119004c1c1c103c0e04111072000b0140d01e803064045c00e440045070019035400300124 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 459387517 1250 459386267 459386269
    0xd03050a0f0506031c140a0f0908010e0a020607060f0f020a030e010b06030f18101e09031418030714040b010c0b0601050304080c011a0a050303180d05030721080708070509 75
    0xc2c8045144510314054080021b02c0d1005142680082c0140c2c0008030a4503039030001b00e030400c5c410802003078030400801000300310031410358844010101c000c0c4107039000078109080c030099401c41da1910203094000c200c0180d400720b182009600c04000f5101017400c1005e15032000006100b11100400d020301010710755515002d440311551401010b0b4032110b055105070300086003040050303010000d445500045d400117482503035040b0307807511003218015600741001038000036400900d260304082c1e8080a6501da00300c40d09913014540300414071941500c50f008001598030962a5001001a02541e0801052060900440e00042000405400f030400400400d003154882c02c002c507070040c001c0c2006400c0600040308076003501e12070045030480e9400c02c1c2c445070b01450261000b00041104400440c60480c15441d500030b02c55250854038860b8220a5034401840001e10480350040e40c00f440241180c10500c048040909050f0a03030000140c034072000444050094503030318080e08a036250f050a0804e004 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 459388767 1250 459387517 459387553
    0x3060a0605030c010e011d060723010b0d02130e0c1c02040b040213032004050708060310020a090b1c1e0608031e0c1015170712030f020a050d03050a0f050603 69
    0x1f4480b80c120204101c8030740032a02040aa441e87e100c2e40e207560440520175100e80d070a6078400c0021901c260790310414a070059940068002010707103640c0000c140040107501c02c5040ca0740c11001a500901c40e98204d4480d4086985d130040b000f442158104614488078085c00220b01542e0000040010260310a00115002c60b99441080010440e440e80300502c06000c5420354400703a8115002c6860a410300070540703130034004070100142c162011030500d40300d0000208419098460301c1041480002c001c42186c0d95001000005061284180b00c120340c8040c2e244107851000303014070559480e100e0081810800842221100140a03040640c501035042c0086501d0744801403041c00ca11a240000003410014050100c400c0810304e1179540340c03840c2a010542d12540e0040c00b03043c039040607a003480542059a00c60104a41510300400c2c000d0300b013801039242940441010b020b07803191000b024041c6178140c10261140c940c050052101e600746040c00c105503901902c8555040e04a040406036400d406 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 459390017 1250 459388767 459388817
    0x3070504051c06060b0703030c080402090a320f1308090609040b040c0906030c0201061a03040f1509120c03081909020402070b09160b09041a03060a0605030c010e01 72
    0x2500c2580089001951840225401d0742d20000300068041001b0007455014410344100b004035061101c1c2a01e0694000b40c0780b4080281882d150950b0360342c0583303041054405104030121703104c9280c44d50b40d0510207001c510000c2119202e903191f0800d0001008000700c403e0941040c0c0d8088902410718055070104035264100b010181d4001d03569550250b01c0b9500d40c0100c0c01411200d440f000049401e0203001010303280c1d400b04800c2560b040c80e004026241d0a101000000c00b800c1c6a241d403661550b1900d00a00840c041018000ba855204000510141680a5420700e0b01c1080d483d428003090074003c1c0c1e15080062b1002c3c01042c00f0b4070010700040d6140f42900139501ca001c6001441110700c0e400241242c0000300d0070b03540c1512030f0081010b442d408003c100ca12a0348840d0000380903142000600091045840700c0c1d00646d182c20000c4c50604060149080c0d004009058440c40c0c5003501400008110078402e0600c00d03c00d480d0b1000f040e502a82d01151080c2c0e040c0e681c3c07a0540f443c403a501e9a40072038 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 459391267 1250 459390017 459390049
    0x30d050406120b0316050f04020702030a06180807030e010810030506060d0201111f110903101a0406030b040215030c16080f040308070b0c040501050d0e0a1401140a020307050405 78
    0xf61000c0040580d01407001100300500d4101c1d94212034206070030300101281c003090b100d000720700c10001e00c005a50000780c20402184d00c07030004500300226030741003440e052940c2001490300d400821100201a005651948200c3c403e036984511541c070303c0107a010000c19448091301035000100420018201410000c2c1c0590060404402500da0b60468910b001c448038174100810b00075604d0f401c9c49202ca405040c03062086151114100f00c0ca81e80080c0d215004070000c04105540c8004c40811010032041b040b054920003002080425502d040451221400322001c03449840100c2e0890542c145040a40b401009101d140c207042034041c111020402080c0c08051f01c4001050007507400c110504002031000e10721179000652610701a103454201808007074001e010f181414002400282d0b0310405455012401d00f001007404c00c25110305a0070054244005440c103002c21650300c20700380054118440044002c0304c0b2a0303203a911840801f00f2030209071000000104100320800552516810f0440c010300 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 459392517 1250 459391267 459391271
    0x504120314031005030c0a050108191e05070206060409110f060c030a050405030709090b0c090f0a03051b040e07090504080f070c03020103050610090e1801021b0705030d05040612 78
    0x30507285a002142c0f82e1020350a450001c2c08a03040a00100c00c0c009002d031144d524081c20f050000e425040000c107501c0000b030315002040d5035400c00d50000ea08100c181c9903100a00303103a1212802c09000c089440d0700161080b280071414a040500c51800c009410128980030007082500700500c540d1080101c81c0d04c00e000f808182005901800140301404075612400c3d501c5140034140342c107180e41948001c0d904c80ca88840e10000c9070042440c80c0d03001d1550340b030896880b2450000501c05400030784581d0303006102d01d20040300300900081c6104001110103010303042c400c2c0000401c010b6400e21091104c3e981c011400c01c003c10a502d0b040241c11038420222503041c0000c1b111080c5050f084284151940081c2200030419560144203242d0810020350342c042025400703074070242270380c45584645034030714600c0741c0003800b01c2d42584a6450b19030523900003550360f8141618402c94900d44a0a80011401209000501ca180005483d5040b40c02074903043c1c01c0504e0b1940603601900c841c0b0070004095 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 459393767 1250 459392517 459392537
    0x61d04080a031d060103031b1e0602040e090607180506070611070f0312150e04200d0807110102010b1503060126190b01091a0405091e130305041203 65
    0x103500f00b129810080440c0c0041800358076608008001e2599541c40c803000c800081c0308000402e501031014060480400c01d0805482002d141c014000c1c410350740a00c0c4e800d1611028021018804500240640450343e034011602040888642e003030782d810700ca82544050b0411002c07000032140c0e00a170040d04446485981404840d4456040d0211a110304900054071301c144005240b81034451100d11007151966a40300d81d04105a01840711400340020f042d0040503c180031039030800c66501203966030b02410420000c0000d00e4000c0c85c580202408582030212589480c85a500c148501d800000780200b0071503030790004014544869001421480c1001040801800c03010900f800c1208032085030101d81c1d07003500d4502420480c2c0b500542c100f88040d81007100b601016a405042c06081da06465647da107465118044190ba0b0300c40e590200380c2048140080100d09500709106e0f1031041d0a000c5842950707034030b810b240040d8012100008000c103205001c06d101e4500401c02160010b4460b0500640360 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 459395017 1250 459393767 459393791
    0xd0e15040801050f040b0a0b010806131d030405270f0a09020406150201050f060a0b0d15030311070f05090114180a0e0f0604051c050f0a0f03061d04080a03 68
    0x90f402c200c80503001c40c1800c070140001c002d0314045140d4024284001002010074150000382603d1000e400b0612440c052442d103100309000b80c0c13140c400c3c2d910140a41402c082194400c980740d40240c440c141c407403140b558130030102040d0303044189603214109003120041e55070501840040c200292004111a030388003280401612648650006812240f01d5562240308503c402401d441c070003404408696003101c00c0c03011549900b0503483c1522020241162560f00424a0400910740681c1440000450034400414160055444521211070b41c095450054460b08a070710102e80c11321a25401000b4800104000c02802a900d8030410b0000c01550400f130300c4001e0303501c41c032005071681301c101d030b81d03ca85560074200c08100009a0f015210b014200f1803915898290310399698421541400b100342180d0000b2074455400c46038444045880145c807440f142200a1240ea02c0f0200c40e0046464400049500072441500302c907400708070030b03080040c0d07517840c3c0e910010380d0400d012080c00d140c0c80355440500 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 459396267 1250 459395017 459395021
    0x3013120f080a0507021c030c08030c0d05010315060602060112082803052d040b07090f03030906020607030908190219060203040203011404030207140f060711030706020d0e15040801 79
    0x100038003d584040c0c407500c0c240104814001c203501e1440a0300e07209000000066084003200e18815001441c480d12690b943d00009098880c0c02010001e5500c0e1030004402c004041e80e0380180c0d00342070f2108210250701c5560070799940b002801250400403258052070006003180008107102d1544108040c0c400c0c001500040c0c01c501c034881c4500102e5100c0042140362041c4885403a0a01070307203407191584419502004c0880180900060700542d481400105010b004002550050032030b580c507588500c0d5130f81402404200c1501450005004200104404d2446800741c0003e054000007254640301c980441c40c1d00e09040d0500e080305600450360380c03c1207811212241c140c00c9000f07810150392887c00381b042508550917150a5000d01021000b400086640090010190341242c8405c00c84a107030000000c03034440840e51081d512500003e03200c010854010000c42c0383c81019002c031040f90b9110301050707032143c4201c8030400010b901030524040711b01e41444c040e5041c1d43d6030040c603454a501d605990342 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 459397517 1250 459396267 459396277
    0x40308030705030601020c010f1b380a2a030f05071101060b040b040e091504060c180b190311070f031d06120a020c3013120f08 56
    0x201280000c03042000340d50f01404030382a000c00920b40446144180341024107840c0342b20168183c605a00c2010b01c003000a040040721485041000192100c2d01e4200842121500f481004188000080c080742c00c6c2c421074041e0200f05090b5008590041108401c22102c9040ca0b64043c010151103618100703602c9550310580d80a1441e075604d500c100c00400000d9130940b07105520102c5c100c0302c100b00420102e00302c1e00a81d0266284880001419220404884e00e40107400d04903a0f8480599804d01003040b103594001c2c21540c2c4940c85600192405200c800901c1380180b040000c182c004000414a010440d004062401818100000c22100d000c01c250b0075908080700c11500d103105954144103141d0800d688108000101580c0c1000745090700c0454000d00601500d01444013003413020500304d4603141c056400550901040352130405810000c0090139500055007180b40300e015010302d4007190000c0480d03000c0c00142024030741003072a2017219090004c80c00c00682e030b0110100020030000781c011000748 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 459398767 1250 459397517 459397531
    0x71b060908040f0b180f060d0507170703050f07110f0f03071a090c0105160803150a0603110301170c0d111938040b0415020c03061305010204030803 65
    0x15202c40c20000402c100ca0919003010803803040910030f9610704840c2c44240c12070008251026080303403c43c940032407000d001e00c255180d0040e0404042000040d030100e54488004800b042c120416114000103400b12a8251080380101e04200c00040c015170240c011840a540f01c0c03070450b641c40240700e600300c0c10100e8803081e210068200081d82800e01080400d5030746610464880e4400a0030140c40142c2d40c0c405840c211414010045200402c001c0100c00600e20a034103e103440c1d81e2480c00c0d546941c0c01542c020f410134411131007040049100b600c0b030300c298546e0300c0c207040e54945542d0a1508200c0f8180500c24110158480d0800c00815900ca24640440c46480380d45541d821080740c90802c04020004c080013a5500d5124004105201c03c0d9003a2409403192000c0c40011614088800304100700e0007943c1505002c000140080d4801c40e80e0020411195203441c103000048110208a840d031924040701507042c0e10a1001c034510040307148007800c4003481100010700e065074a68400d0b00f250400c841d40 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 459400017 1250 459398767 459398783
    0x30714190e040605030d1239090e06150702041803090f06020a0218090a120509090105040b10300c0224011401090504060b040512030301050306071b0609 67
    0x80480c0c2d0826000300005003800310080c200b019541600108500303c403851030a28103848041c1e050005000d0b6942d21282c2204c080c488142c1142c5c1c0d4058161080300841c0b0707800081074400002080c483c0340301c106004040080008200640d030030400c1915420405007640d100b613031901d0804000f8110790590014a204c0e45900d06c01c03e182c02c000701c821680d140e0105095400c4014802d00680e01c4061014000045011204490b00e48081040c6000c190008c0240540c0540d60000c0c0a04d4000002d400400d80840300140d40b80e07202e0b004c1c001500e9000003555004a038510840c40700c2800751054031803545140c03021200d2910303124502d034181e40800d490490440d581d01e986064040d8180108103e00403035111103000780400440800020105108804517080c42e40b1407027055a114240010082c41d0040c024001c1c181c880c6500d0909a109114043c1300c1c42006420a40061010041d28101c51004000d44009d0341c4c0c251042e03a1700c5000d90408030368200021041c40c00100c00d0300c90750707103402e0042c000 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 459401267 1250 459400017 459400037
    0x20d14090631080f010501150f020c030f0610050a031205030613021c0b0102030a0c170c0708030d1508030403020d030c0204021911031201120204092a0e06010503071419 74
    0x102e40c2041104801940320307906207001407181c418800b8421508d0078241c9024001111070b01d03003c0703040036080042c0c1c07a450300444060400c0e000f00000c0460103800d264030640400f9942d00d0401c1003d60580c440108201d6502034001d039840d0051b000356612100c050009030712523043d00321000490f8071640000d00c2c400c3d00c00004441086144c89458a2008203000540ca040c1c1181c0340a040d4500c1000c0040c018501c0c10303002616541c209050f1560958501c1c211040035485546840d143e07000100d0403084503103847c08400c0880c2e980e40710b5a08071411803000d51b140509503001e0200c540e04888041d42070002c0104510b0041c0c6482c80182180b8511007003c9000d01c0810000400700b840041200405510610005000a803250492811a440c10740f07400b054035141c3c404213000e00800c0f103001e0000da4504030610550075103840c5c502090300100100d104265214242a00050360907540b45000035018130000e26550300030002c070b070503c01350b41a0b0030781800d10b4103041c40e880c0d046e5500c441c800200c1e4828 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 459402517 1250 459401267 459401279
    0x70e090a060f050c07151d01020417071d06030703080c010e16211104050f010e060118090903020109051204062c19050901060f020d14090631 62
    0x308200080000100c2804213082201c0020124014810080c16680c680341d203c080001d403c1d40b003003458180c80851a000340440c0b00c0214000c3d00a172103120203900d20500c1c0d0300b0305400d020409900341c5029059156941f0001040032140500007000642c040c1314400740400461007410180080e8403101001044135908021054203100c1280c400550100c464442400040f0f00712100340303580301c07015030220040505030506150004c40310b0300b60b0350028500740c14411441c41140805041c0d401d581e003000c0180e11000011600100c001d8800c01000300c2c0b43d178040c00203104036000856814001c0c4000b160040aa0f11001c2c2880801459040e10791000a4100440e5401c40e198007100c0104100078a543c001c80f01d4282c20465058030745d980b0031004240303112040c007078400c180009060060881901587c448001034051166010200050720a407441c0c1440140704103090221a503117482d1040c1052001028402e29412904000c10603095a02804c0140b280f0749098602115812070001d000780d10f081 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 459403767 1250 459402517 459402521
    0x181807180e0706140a1701030b0603060708061c02030309090703020a0e120a0305072109091b020d0e01030e0f010c180f0b0d09020414070e01030603170c070e090a06 72
    0x8244580c0a810a000411060380c001100ca55418040c84c00c0c5556401d180c80c044456451481306a04c04480090000c02806480791226210300c02c26012502c0903240ea0b0403d0301e040c0412500070303500c07400d41c010308170031029001d600000c407a00c080c044905003503054000031410030007100c500000070350104520440da5800750303202001403003c1e544812041010b0454540310202110080e050140001d1036400700112000c00d1047d0001c2100005c821341800007005140781014400c0102003400e102e480b00310044d4441d0b201d1040b441a800400e40800e15120550341a039900c420141030551741d801c0d002c2c0055050000c0c0d01d042d810640001405010101c0192000300d1401140d8078001082c0400c3c082c11120141c0d007410b0f01d409056440c2c5412484841c20b001e0030810000940103410242d00412610441f41018000c441c182c94003078036071003520f00440803110648400707002c100c100b804107200802a10014009a4001c0701540c41c07150720f0701c042d071003a05010b841c01c0354030354003162856092207258 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 459405017 1250 459403767 459403781
    0x18013c090302030a110f0d0321060b0d0518010c110601061e050306040221040312020c0307020f0a08060907030302010f05070c02010e03072d09020918180718 69
    0x19040024003181150003080c1d0780c0d20624030040041044610906460b0380b6030441c0368681100a111100b940c1c0c19250080050400b6001003044000e118101000049a4020303181602d09200c1000e00305590140508060900a0000009070500c0c080d450034101080c041c5000002c3c00da12100c840c543c0410115140500c164050300800c01401c42106c110440d40171070720846111490055103035228500020001d01c200c2d40301c00c40103c10360b4140c403c41c1154050092042d4000d80f80e04111450a050010a0707101e8905c054026030410403441c1c0052030003540582c5080c10181c907030039400e504d03415410316060040c0e840e41340c603500c890707001c104166090007004651280f00c0c1091180c1c0c01e000b400035000100988000341481000c44900d400341d01c0401050000f4021481100030300c22801c0001c00106414a00c0c0603406a0180c00200360080305008035804008068581001007001c0b5507204864480902005c00c40c0a40c1034002242120400030310300a8040300c0821803402044811500485e055 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 459406267 1250 459405017 459405137
    0xe0d0606090225050606010804081c0b13062709060603060501031218030b0a02120f010810050f0705130b030708270a0303021c050109020c060112081801 67
    0x50003440000040c1d001c1517003600b010007802c04803066259480c0c505034502480c00030f1611004410881e90b0b8001080d000a086410180d0b0b00e101c003404070701d1140c0f0907140c3e680502500b120600901c106455010840100000b21040c80091400000c1c4c1c0c2e13500540780e25910549016459070014000d0043c500032040ca801210f0905100104890b45500c080458621018040e0004240050001c020f15012034600505168036254189008421290401c00c2030050700c109200c1c1c0440005150564819140101e403040d6156041e640c40030011140356104110b8142940c1c0014030000700900b11002540c01004181c031100c1c010f01e00000014078260500c48680440300c000904064100c0020400700e0361340c0c0d09851f0150741d0344d90003d0304520151a012825404034500000000d050301540c0c060002a4016029155241da895a8641541a07460740140501c10208260a07900940f0300c8071102048042c1044030b00300b440c2c502036000c02d4005180c1e40208141ca9190b440483d110300404030b00c0707441 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 459407517 1250 459406267 459406327
    0x6050a0e0403030b280e101a09012606130203070c0f2d020301060b04060f0e180a05040204061502100b040e0a0f060e07060f0e0d06060902 61
    0x218100d825400180d01600207028181d690300b5100040c0c90f000f01d15a50b0310600804211400c4400342c40e0040426984502150b2281c0e645c0030510a08030070680c84100c9803803098200c0c1c030b02c0da1841c0c11102a4002d94101e414061941460713085010f451424504800f40c400783c4c50300d41d1a06409006048400e0310000750142d1040041190454005d0740750b207009a000b90220f0b60ba00100e151100301603000703100303440d60010a03002d01907020b83c00d41070304c1808900c250003e0100656922000c2e000b40960302610b401f003031401280d552801d100301131f14000528020441044100380e0b0b0460b5409172025141d003200e880d21227081201307505140c02203900402d602d05502100321004500252a895984207244490f6294000c108080c3e59541140402602e20016a4090040d620b003615a2001d580d1089817883d050000a003000074000c08c0c20011590345441d140741403c0740c000104c509500e070303000d00e40c0c0c010002c00c401408105240f1440d0007514010100503990042038204102c60035544d404020151 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 459408767 1250 459407517 459407519
    0x2070608130f0b060d0b0901201206100512010b0a0e01020c060409020c01201323010503040813080318030c0607021203040b0f04090b060702101d03150a06050a 70
    0x1149059030004090f0440d458020341d0b00c0700741c00510b948089042c083c082d40107400502c204048103500841c241e10488000c18a1228001100451030043e801700601c3e180c000000115603003006081040350011a02d40355143c003c00c0498881e1b04802030300140004040841e0120300550444000c002d145024001000b19030044d00000300c1a10540c09040d51194020400300368013103007500a41020140859401304000342a030700500280c1201424440021003050f000501403090407081303c2e00503500110081c001d20810044d6010303440680202c40300d0748100001102d042e60341c0300b10740140c040007014540c2c4d03085119a0a40d244500103c1c035100c0c0d0050340300d990b030303607981e00c0c0413030390702ca40d041e0f80c0c1248014428803081c0c1180100c0d8400c450500340062140403014180d4010400d8509050f401c00c204664030090004a01030540025000f1858000d140812805a01c107490360341b800c8a07021700703400034050104c0d0034602d00d9003841a00b1081d02045c4804982180502e00107014151a6502c180f = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 459410017 1250 459408767 459408773
    0x2091f0f0611012c0a02120607140715110702100e090c0f09040f111b060a060e0402090901180503032a0f0a0207050901080604060507031e0b031c0207060813 69
    0x1184403190004d45a0000304622281600c14004c80f40310b160014600c06003084440e2901340c4540c0201d402d54005018035104030391084a8000761103100b80c0007010300441044c580030302e5001f040d901e089031180090030702800c001039481407030001e6588090360318090240045002d00c90007400160410513002400d221924031943c0070340036600b083c0e00890700442c45422100d044002401c0e180e10880340d2020005110004061031028021581031a004a038181e0b91203001c00c8040b21a940500d48881b0840d001050152500c1480306422503c80d0740001030401c001d482040c040400a01300b112103400c04401c0125503950100710301914a121100810001d60400c0b10101302e1146c002e09202070800400c1d50b40340640b0800030040541000340201d02c0300c2d61200c10b2542c0c2d900e0200c070211aa541441c00040c5018460b00880004544c080385446002c07001d400150041d0003100043c0e42c0521854003240c0ea0f0406118140401c003620760090840a0300b03000009003541802004881c0350f20042d2400000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 459411267 1250 459410017 459410051
    0xb130512010905010b1e010c060e0d050304030f0e090403050304020f060a031509050708011503061806030204051e061e031b120c180703150603060f05090609010302091f0f061101 78
    0x54810b091030203012208c6030b85442d2004110710b8620804030710804508001e041c1d005001035000e00e00a803600c05000030300071000c94180e010a17952503004a22000490300281c0038102541e00b00b407001700300b40d601d000e01201180712500888280c00009444240701c0d09014095901e84001d401c1c078000c1403041303180a240144c0500810b1003140d240500d00900c1c0c1d40e80c24466401700014012509000c0c100c5520180440003400306400300741e01c43c03850f14006c40c11498942c0014800c1d43c5031038040051680d900000c04c51030069110305490780441c0412001019a428881550203014580451034004c0c145014080308521105a15105501440170764074107541d00c010314080000321030191034483e41c802d40102c0151000c0380c00d101e802028a81c0104190b50990000300c1a5420800030307508560340c0306c0410032070190544035a6006501c020052015043c04006c007540410f40c0c1c404285c00d81c3c1550b000142d80681c0354024000002159004c0c0100ea03440503400001e18411402071003000d1816003442c3d0 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 459412517 1250 459411267 459411319
    0x40f0e06090c09010203040806010b0a090806090c0f0a05090c030a0b0a03030203030c0a030612030c030e10140d060302060403080901030b012a170d051b0f040b130512010905010b 78
    0xc0c42c050701051098890b80b08204940180183c3c5042d9065541d68802602c1c080e00148602c102203901c060b0040307140240004d00c0c1e441481004001c06160740c1940a0180203040310f10034a4010300354020114041c0c030344584480c041c140d401010b603503902c0c250300d0b050112406200b0044c40f072060000100003199000007600c3c0c001409140041d40c1c1c0c440541c0c158020b024660080f4244421903402c80c0c1895003200094070894002c2d1139101003140040b0410044503c1400b041000c43c403500f05040705002160043c0c4030440040c2e00010349140c9a030001401600181e2044400c06000211aa110b580c10701851103044820708190010141d1025a81c0c55201c02d051004245403e1307410803070500c4205c622440d08181000511552914034102c104050b1034121403010700d0b00314940b1580000c0103c0d00c1240e0500000040581c20700b810b0201c1c20815900c590902001c204d05030340081039590b1003440c114212498000005a60a0946485070a403100801501d01c112407aa01c2904400388004140c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 459413767 1250 459412517 459412531
    0x2403141507080a1d0c0f0312120415180501140114040506010e09070302040e1003050a0b090c102a1214070c08011d0f0d0c020409050d0203040f0e0609 66
    0x160b0141c1c1d401002d0310003410100e905624000024103104410360011070361103440c04094407020580000c503c141039036002a402007a0701c8510070000ca403480e0200c00035040e001403040e116912100740c0c8440c40825145024002c0c0209a00c070f100e02170803c4000d00c80c00702ca28440c20003806180d071520b019800010a8103410900851711000055403503032082c5840303031541c1030050141c1a00d00700604002c000b0340040c003460704602c4a0034082030300f41c4060601701c021281d1110042032003001c2565001140d00c00a800000b0301d2180c6050b420340c1da42c0c2c43d80506041801580c811200458004c01c0c00d00c0c10004480100c500651480e81c140400c0030014100d81c243c3c400d041520500164007100c048600c170f002c0c030181c4241810800440e10743c2041d0000e0164822660400c0c800080003c025501d03241341060f074000a0b440a0104100c041c01411151b19150005000007101c40c0306031199410000c1c980300c040c3c01604001414000c0b07030404000340003d017480000710000c43c503040021030085440a0300c84 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 459415017 1250 459413767 459413777
    0x10509010311070228120f140f0609031905090f040b060403060501150206090334020303070b060102060702030f03010504021b0a06020a1403091b01032403141507 71
    0x8140030790700d160111203d083d406030a442c072407800324100340d001d400302d51045150000041c10000d01d0b00d0f00c0900e1035405a40261505502d018a60398035000307100c4c0100b8100244c084c000c04d00048013000d200003442500c107400a140d461040850070303080341d26200e2980c41400000d1094850a865801c01482400740980780020800ca0b00380000d00140210342c0000c1c580390600f8000b1032400a0b07401d0b103041d40c62450302216496107030941040e40702d004004e0382002c540c080480f24030b5448508002c80d018010030714810b000a081c50340209045512511090321400c940400340141564100300c41c0790310404500c09075041804400d81a0035600c4103207d454070894003c2200c03004000c083c40203e01900300d0004071120b42d4020711f00f80020350481d030718220124003050031a200703546820040b64031aa0825001d811494000302c00c021540c04904030040c10142e4a000704048020074011034000c9005000b242c1c940e40b803645c60541c03d8011262801e20141c0c0180103a80d50f00035540b0340541c0c002d2418242 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 459416267 1250 459415017 459415031
    0x503130e07020c01110c060703050414010c080d0f0917031803211f031209060c0b0109020d0b030106140a051008011502030c070e010e060d02010f0e03151e150105090103 74
    0xd1070310105004090b484040088c641003015007200c010412907001079810321141c03040b0401540d0280700300002a003140400c00104c0324a10f01640507980c0c4810350040015991000c4e261904080401025039071040d5000040c021001819000550380c01210401180b8041548080800311405411010910b22800d400314020300d200c0c0750303d03032400f02c0304500640100e540d0b403d021031807408000c510804a149880c0116030507108038002c0b200da58215aa89200b0392174034401e64025400810313804005a80c91f00940707002d980a00940c002484241609442c02014004120061402d988031910a04203034040b60741c1350307800200060444441c138080011001048800f030303045118001d01d903001401859000704508514001450603106d0000d003106140c0e441c242800448220002c02030b0120304180303868800c061055014902034178000e001c3d9003401141080300f03940030100360b1700a01520450b840c0c490b8020714080c0019440000b0f0005601120714690000c2c005101d4900c0d024101900ca0b16 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 459417517 1250 459416267 459416297
    0x30c0b0a1b180e090d2012070516080c01030e06040c030b04020a030804030602040e01060f120b06070501050a060905070f0903021c12020708120f0d0f090f0503130e07020c01 76
    0xc07900040c007540b000c80d81c841c03600084064480c4110185c4402184035801602d80d2051402a005030301c003960070013003600058088080140b0780040c40c046480780b043d501a8414656095004401024440020b04543c01d01d01c00241c1a00d03620b400e081d0096105408100c003241c04c03040c9203000c0300d0300540380034001d45650000c030703107050400d41011b800d21200050000c20004940d009104444080720340281690329a2011600300d9405080d003c0010f031282e541a10304001e55118095622005060605c4d15800f0740d60075080d260b049416480140d914241040b8116081c0101d582c842c02c9407605104c2030640003006005400a808041c1c090040191903201e2480c98600703040303416800030300d01c0800980004000350703200104c1c021407940340200105020241d4044003074500325603560242074104114801e000006011194507020003a89947c40c0700f010984192814214030301a0300030f1a0b0b01c0c2c080d801b026000d00e2107607000e845442010010400040d50214800c0750400003440e00050f05949a0 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 459418767 1250 459417517 459417557
    0x100b1302071406150406050d02010816020304171506010e0a091e020d1a0105040b0a1110091a01080303011d060f190612050903070f06110304030c0b0a1b 67
    0xc100003d100b82d03000d100f0311100008210036210303800c0f5030a10409450318140100b010302601e0083c00b242d8202c01042d1840c102010458621541748112400c00742e4801500104415221420502c1e1700956070f00b400f2540184902540314000313080840380681c9250210b52410074520803151341c165521030300c09242c030550003020340300c840b00071040d500ca080098250000f07043c1c0025070035140010703008102142d40102e0a031000c44110548050400750000f000b0358101d071000b0350460300c03030180c4490b1044442c0284204d105080c00741d0071003154500101048620903c068000e60758540c81480100a104011003904164074440200c550040c4c0321036000ca18941106040316500000600d4000025545c41c81700c00125207040d80c1c1c0301c4a190403144a00200e40c03017070341d0348040d58004200d1400402c202c6400078266500c100c10018640d5501501e0304920303082500c0440001e4044101d01082c400340090203600310829003820040b55480b03080c40d0520030000003072481807104440607000000302207 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 459420017 1250 459418767 459418793
    0x50d080912040b090907020a030228081308120c060103030309030e0405040602191704110a03080a03020306120105152103070501090309081b04050c1614100b130207 72
    0x41c0354455107590301c0d14980c22180d000450300b14000c00142d0001099184001038106001d505900580040c0c035000c1000d4203083c0d1840c0c80e4074903010360b02c0c4c03012001a0150b00102003102006034001d00d46410700617054100302c107500c0713241005032051001070000c02011070f006044a40c18200041c03281094038023521810700c130300384455000f4503000c1080144905034000307000941410200e9503160b510100d080d10461200c1c0300c04242c00304260005070000d5003400001011080080500002e1076580e50368505c2a8014201d01000940100512550f4240345583d649107550b900001e020030705c0c012080000340302044800c42d12805c40a820040e0b0521031074821040e213000682039998800c020700703080e03020b040050030032400100459800980c124011a00c1ca004110010050703284c0c010304410040a410050804a5400f400700801a10840b80010801751544900d1140c5c40038213140c001c540c244800201c024142e241002500c0080d951006103030103104c2d140c1e500050705e4201e03600380b0401d11504 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 459421267 1250 459420017 459420043
    0x509011e0906020601050a030f08180904110a060504060f0e060904020429030601050409050403050d0c0c0c240c110a03081e040e13062004081603050d0809 68
    0x2881a4900a0940c07210803001542c0d69074086803400d9030b880d800d100d80305680e480064091142040e2200000e510440100303206030700045100c1841d41c11070b00041550b1804e80702158100004a1008891f0400080910060031181801c40c106444c001024040b20300500303101c802c000341e030b07038500b80c2c680d030348000b503c0240798090300c115102c5032074101c1c4003211030740c219a02001c0a1098000d0141000d020210782c46010180d488a040c5458a09084043c06c0d0160080701488020300c00452210300340d205484418a459480f00031244441c00c01e54002005a0420100d00440004d4000002c003040100b02c0c035410785181a00d550406820900034040c100044903900202c507880c00020700c5427032000340241030854100c101d180c407410399111405100ea4440c0c0c40500d42d20350001034070000c0c2440f00c15842401000003185440c10b42c03400b03007221a410445190040c001040c24000c4143c100311010031b48822aa174036a0607820361325a19540c490140d40d4100304510540080c03000b1809112168a04031 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 459422517 1250 459421267 459421307
    0x103030f050913050702151602010f1a10030b090f04020111060103030912050708010204080a03020d030207110f0409121e0e09130c0f03030518040203100315022b0b0d12050901 77
    0x105011038008c0b80300303c01140f00040d0700380040c00009c803100c0e00c81c1c4165400c1c80000501e03000180c40520070115102c00c0b401003496500c45201d407003500c5412503544101c82d0b142c50300d0400e1410740f0014003c0a85000c518150b43c0c05400180b00103508007200f401038a442460082e04101d25103001b81c50058240c000daa125400840c000404c4e0200181d803420041c400e809503101d01c18094022000c1303020b104005454401107546c1d08006007802280c3c03008030800035002261150413500c424011401406802c1d0000f0100850045400b040c0450300d40a0806407034507100021240d000100001c1c8007510040e08070014440d44000c2001e1250084c2c000e029014001c0c6c480c035582d09016203d50003003103090404010014280101b40b03050720880707105915480c01d0400e200d0560b1100b0701460038050003889400d6003000b03401c0000590041402601c0c20704480d0400405210b0b0021081d140000c00c12030055215022000003d07515594900c0045c61a15007281c071074a100b80102c80c21240d011400420b0a = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 459423767 1250 459422517 459422521
    0x180b180c0406080f06090f0607031d010203160815060f0c03130f0306051819110a0b0d0c03020a0c26030403021c0906020c2709060103030f05091305070215 68
    0x501040c4c40307404034421800d4403060b980d145030164903504100390107a016000900000c6a81d800b0350b000c02d41002c1b000020702c1da5100401c0c070450072648240c503c0a101640b0445162065070f02500140d80500c401c60041981401c00c0045111070090100700c4070170a03c0400e085002410410603111a03054001d81440202c0d03441c14110901506400160f44240c00d210006064000305498811000b044030014075050704000108450000b030403804881440403c000503185d0703581c00c420306019000001002c1c3d920700c1003c1c460401c403100b18004d0818140144008034403543c000403c0d0302416004401100070303052081c040d034104000c807c900359103601d010050200b819400070f103029120001c20700c96100341070001800e03034000525214100051307100f420314009500708902100e8420600da40c503480903d44098a001e603104c4205d69019036540b12100400c1451303070004030441042501c7c20458502760642c00407070341c80740441f0702c025425511b80d0081406503100700700300c0c41040000341000440d4 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 459425017 1250 459423767 459423779
    0x110a03030908060c03060a0501051c1d250b07060204080105240306010e01090e0c0303031302031c090302060705390603090a1416060909180b180c0406 66
    0x20305000c2e00d9090b22401c03001541446030030b02181c0c001e00d0014400c0f14100d1504004644035404003801c91840b00c5040010044032180703014442c400c51640481058150003205e1032460305410324040d01014100000c550002c40d02c1641d00c41c1a01d06d4040d11302c2d5500d0342c0e070410801074841c0303900c94100d40d1328000400a80140c0c080b1000054424042248442c3c1481000c05a03696020700804051b803402400401109405501c84500c2d025610280d1340349001510029045400443c0c0d0110700c2d00d0160400b00461505000044155002081422107181540402011083c0c1c03800001d004100c002084003e04c0020425402c002102c2a8015154608243e404c100c0d03240c401d103014001214010500c0203840c008040d00e00c203d01203002030041007015142c00048003018034000313007e801030310103a01003403403001c0b100307005440c9680307030580418582020030741101c0c2d0101210b0340a0b440c0c54101c07000140186009904540001054040c050307144400c40d0400300061003aa610620f40880001c0c4 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 459426267 1250 459425017 459425027
    0xd03091809021203090306010618050a031109070215061c08130f0f080619060e09010516030e0d0305040206270306010801110307081306020703052a0a0b04110a0303 72
    0x100c148240d0f05520322500881c0529924045c0c10301d0310b03038103412103001072008170701c141d114200508054a4840c01503507075130045106154250003da84100220208440a052228006400168620007020314031400c08120540c01c0000d00458810366580203a07400c014114100081400c0d00300580380e42d103603540320102444600e0342c402d49801603159a0002031031140030210304101c5410340068013a82c7c1d11200700590314240c07270855540707040c0e490101040c480000900316209030184000081d607030824a0356078002c0d981c901d0f582c1c82014103003044840192004217a104102200303050200d42900d0314800140140140c120040b4881150002d600203071071707030301c5a49180711020b5055698a90701c03003480d24240c850a0701c2c4260881d60400200f045244982656079100e030f050440e09080300382c0e9680f50300690380001c400307a001440218038848404081c050505128900b000c054400d2840405e40c0b94842e9080800500245103000009043c050384401421481c80700820020500d5120702d80605 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 459427517 1250 459426267 459426281
    0x9050f07030b0406050d061e181103010b06040b0c0f03030903070b06031b060a0507120302030430110f0703140d0315051c140c011103070b060d030918 66
    0x20b42400c0c81da60840c1030520070642581c2d805029040484d01c1619034001800800c1c040c0905020075021a052034601c0e1300c00c0d178410400c84070440b0040790b040d040c4856410544200340e0b2103a45009002c1d242c541d2008102ca08a6240402c0180c540114041a60401c6811030740680107003c00010480500300200042c0345552080e00d40850b5034036041e05040e90741800251018208042400d824024a4000080c0000301c01604d07042c0d1818180ba51141c00b00e0310a040c0c0c00340480c5c0c010052008001020009241c0894586040c1c044002e12040c9034030203028460041c0306000c841010000c0020b410300480e00480c0740d0008071100640c1e42d00d001e4400000d08819043e180c00f40e02c40d0210301c43e110340603000a42c440010f040c0c140340e040c4010000f05c02c41030168a03014054a14002001801d49480710718420000006052466104000586810b11100c0c15000c243c20401c1040001a000c584058010b4004d075907419050010307180549041c2404c0d0842c05482102120070f528803403603034002070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 459428767 1250 459427517 459427531
    0x120723030a0507081c02070b0d021e070c030c080c030a02040b03160f1a040803040902131205150105060901081b070c0b0301090f140a0c0306051005030604050f07020607050304030909050f 82
    0x5032034613003010806c90f15060302c1d000310b03402c20340b04028102c4601d00580281c02c0710520300703a10300d10508818581c81c5941e41700c5101214200c0c401c5604009000510f00c0d40c40003494900082c0c440e82e005000080e03120006000024481c40d41c9404159040e24100141c00d04901d03140c80d00d000e000e40b0b41c1410320107241d9611400b035041c3c4c180c07403072216512580d030181c40c21111280c00a40c20141404510406904074520400103051400030001c1e1900c6405c90800641e4044c0c000f80c07441e4489200800211f0105030000c600845003041041a103907071000c4403540c00518403e2201d071018040062403010f200703501e40039201c10300010000c110030010310021030496006040070004640c1100402c01a50344000080400310311a10000c0c512049079000280c51400c10716000400c0d9803940c0014000da01190b2080000030004002c00000b810320380702c4c6039002010a141c400c0da41c9081c60000b5640e00004000170200032011000c1001c041c001c4036501c02500ea03550081c0294981800c0046410000311005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 459430017 1250 459428767 459428803
    0x2090406080106080303280515100306050117040f020627030a080a031503080c07050f09060312071a010909050c18061215040302010b120723030a050708 67
    0x62140740c1403040c2402c031814000698119683c0c4000340c5100303242c4600c8070381908041201c000b4100300c2441414402c0c0d4091aa0b884820345500a00c1824000b2095110600d13142040c107000581e00002480a0700c083d030340c56a4420740d035918142a5044440800030340105c0c020503610305900d040c0601c029031034031856000e959814081f0400d59a80d40442002d02075650800039039801501c030781c1001d040c09e122800381403041c0b0b68136500c0f42d0395580b00b0f0f0111200e6400c02d800500144c034141c2070134a840c2c01d0454000c0c031242003450000b034a51100e100b040400d0003000a4030410407843e103040108007502038541486039a980d04009001c3d0075050f004458030f00880340071070a0b0380350801c116071000030303c14902c00e5550340f07603c01c3c866101c800450902041c800c00c0e861460b691512014140702e18030980c004101c1c1c42d5804140080300b404001c4503100c541061105000c5c00c0f100d02c503d66404404008403014520421000c28109000c451000c2c00701d0040420105103000005101c4080392100b12003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 459431267 1250 459430017 459430019
    0xf03020316030807030302090f120106060e04020c0c041e18140114010e061302040f05010219050c1c02040c2c09040b0402011107060201061a0a02030a081b040902090406 74
    0x401e401d1410070b01009203840414403007103010038440c1c0d000c0c00d090700010700412002c0c5222000140c4034520038441d0840f9a4440d4828402c140d800200090140da0039241941840b55502d086600c40b010041028011650b070054021101e600070340d0707540c68818041d010440000d07140006840c00d12142c0050307410720b07800c044001c0c3d052814424043d07900036062207000746900380512040c07441c0e80686865031140c1c890700c40c90a001c1c03661005000030201120070b510514a084000382c103089003c82520305101c424401400407410106441910b1042100d0b01d030510000800003c206d0400d00c07202941140c42c00e074910083e0780d00100c150444155040d600c40043c0e541c1c0140b413403807904801d13023250402400c501143c00940c10841640c1c02c984141040b1414208030309006241003166441580142e4441e2020440b9080c3c000d06108a180e081151500d061003410029540b8818400c00d0820410000c0004562440c4080ca000c10640301c98080e56499a0f101c5991010f034000300f210520961030694 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 459432517 1250 459431267 459431293
    0x1311060f0408070f031e23100e1507050901020a0807060f0b0906060904050a09080a0f0e03060c1c1b12110a0c140c0901060809060f010b030a0c11070f030203 69
    0x2604049036408072048020008500d5400419543c0ca1b508496804281e4516071180c00410219000d8070300d00e0b00101400c02404104406451004004c003000c1e0f040500d440800b0550004819030211503810a1641c841400c40100d140071610311024052480100b400360030044150045080c50480c0c800c24860b2103008070800030782d81c80c1541e0b140d503c00300400002034203003050b801a42c0e0082040c840040c44241e10780360010640c0c0103080c0130001441030400c0c0ea0400350403110301d110568050307008000501c0c000d400b00e84180702c0c1c48040040c45102010150341b1301060781204a40000070300e0314210414070382101424030000c58a072154450304258500c140031354840700340c400110981d0b4039042106001d07180c003050b6482d0071041c000b15018010780c0d502503844861225008080079981c0f9041d82c81c4c0502c4050400070090310a180e908079280040081d281d00000350394200b43c01c0440041c0640c041801035400d00f40c3c0c615020010302400c3c030002407440c0d8564a1000700d0740240e0036a854510038030 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 459433767 1250 459432517 459432539
    0x605070f020c010f0c0c0e0405151308090d0f02040f021305030f030d0507090f060203030f07020a1110020304031e020f0607030c031d0418150c081311060f040807 71
    0x2070403040c0000c07000b1002010040c4280000f05e009030048a2140c80075445090500010360201c4094070554803462039101c4500b0382c001580d03801120188025072024184d5901000c0d48a10992103206140c2e014091061002086a102080341e00500c20040c1007100510000650025560f80c2c1c42181a00c0000070b6504004c24402c80b000d131110091441e180c1d0446040d0024140034005000b0024a414003046207020751034403102405003a001142c59203001c221b16156004020007150071900480d18070310000b00d018031100c1564604403031f00180c0d055103c03012440c500440d40050040444204504103020040316115082402035072000500051001842000e1052180c0100056881802800802d11410072008c04544403040031342c41c44403c0b00041c0a403180700e81c604403d40304101080003008441c2e605901c03104402e000a100d180454100908060070040c0407011070000c0b4900c031010019440c4a00c90b04a000600b08d68855810083e01403254101d401100c1c414820684041841d29080c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 459435017 1250 459433767 459433783
    0x5010914090c13030f0b0405060a090f020f0325050907020d090e0c09090a0f060807140402030604090c0e040b01061d060d060306020f090901140f010c050f0601030605070f02 76
    0x2408460030342d00c0d004900011680500d40d0480c0410403641c001c0b00107804410134001c0380c1e0180710140ca4904040c24100c1c1800000360649504a14001c0d03030fa0300182d1003202c5141e803c0e030103c4045e8080503120010038280308404042000e03070400010800c00111130040c1000540e5010b48443d81700350b50f4040141e0352004421081d0002c42c500030070402030410800145d035440001d4038003050070055007401041985000751040700c1825140d200c1901105e080b4442c0b1801010044000e00500f840d00309400e40440544000d2070040d60000000f4020b92204c0c2c00a401880d4091200c10082d6642d03128068241000e490883d03031003114900001d8850b00c50401d001c035012004a0400b00d2100c55070812080d84c3c814400000c05945410000020803214400740c00540c0e846400d899031a0b50340000c015166405030020304c0c0841c442078140c4a607844540c086156001c00382072080c0c503201203017012803912285420b42c540a10801001001700308035604414010b1b6080e0f21500c8912246040613a02c031088 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 459436267 1250 459435017 459435019
    0x1215080c030102250f02060f18150301090c0504030b16080702070f121b06030c020c0d1101030b0303040b1801030c0804050a080f0c06010b090a0509041707150203040c05010914 77
    0x144001e803410103984814003041c07252148525001c1d02c140c2e80c6c0481c00c41d0700000121411050003160604620344070440b007040c146811911803e1486d402558064240010300920102550301d451000009020307008441c040c40c0c2065070302e8401d180450240000601200f000c00010f5440f4012840d00c82c000284102a200c6a060a00441d03050012100da400c1c000c00c000d80e14154805059552507168012400103400296000f1607070041544000e4a400851030313190380504240860b52010030001200010802d07024a40401d01c0b4202c403000902d180a540c1001506c0303c80021070f03e62080700c800800315a05001e0320140105202003030141c403086801c03100a41660040042d03100058003c000821103408060a8503042154a209441ca040400d8101803103002c030000d0455404c1c90024040c00060004903041001440c01d540e4071024011160003004981a01044201c2040b10810b078800705e014041604648030f1506050101c1041c4a5101d5a80800c00c101d0f804568012410304503082500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 459437517 1250 459436267 459436297
    0x1005060c0309060702060d020a200a050316051e03030a060b0304051b011e020309190612020a050403020915120105060105121806101a0310151215080c030102 69
    0x1e1102d0a1104035442400c00303e900407070800c280b0a5400341840034000c800d1841e900d0408066001c45010070303002c032160486034503510024005001803000422200040d0000350303c07100402c4e552400901d03080c13002410748282c03400c00c2c9008410002c000702552181c4030a6909101051342c40c0d14000b824801130f40c029207203400039810180d4083e0000045e500500c0103162201850607030a00d0310b0540c529070151340d0016003000855019a01c0d00075041100140c13403a03043d102c0300746800d0014000c80f01c07149540140c150085244101c07a4010f0041d1001141c000d85a0070f564500b003840c0300303001020b07500c10350311458602c03030802c1c04032105201c1e1610446041e1583d5140c40460040c09040c0071000380100041642c20104c0300004106000d410300400f0f070444260300742810405440c09464018003990034a1100b841005016400c2d503982500301c030303140c1d065021305003245170782100d0006031111840401e50601440b66036050304883d10008648404064070388401e0908101401c1c2e100d51410403620714 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 459438767 1250 459437517 459437527
    0x109031e0f0f03050615040906180605011704060e01061502010e070b0d09020303070f0305070302060a090506010303111005041412070c260f070302091303080103081803030c03031005060c03 83
    0x76019910042e00403c000f80010501d0140c6806c04805501a03048504265203d03402000a901c6543e08694480c1c202da000744089420700d400200381400d8143d60105c0321350440e000c2010311480703038801b041140c0032800078007599494a10032100b02e4514500c0320010b61922144410218001c902c1c101521502c5100c2407034911201803400160480240990381800200b040800060300b440030942c09920035290540c031950345040c00b1381000002008039a503181404c089000091011440605580e81070400824401280c0c50743c81c9059008060180740d2840c103801d000a0040c4940c01000750503c100494460f29000310001c0c0d814050703030400a00c0b588100720107114071031112202807280d009401092482c0028558568900750304030a4500c031075000440b0500c00d604000703603480d40c81807001415860004180d0b40042242c08144405048000d005c0340c6202003444100492500c40c1d00142101c0e03c1d07400030148180c40340d2064464542e540101940010300303040040c180c0d03038500080c0c005103080c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 459440017 1250 459438767 459438797
    0x905041515030e0105010e0a06080a0b04061505031f1a0306060607050a05060703091703010602061f0b0a200a12030902180a02340201030b120109031e0f 67
    0x22000301c1c440d203418161912581d0305004401d204040c002c04031125003007039504003660200c00700d580c0754000d2001c91b00082c0400000ca148010701d035800c82d9104000081e0900141310711030401d04150080e5602d402a6014030392385c1c144c075443c40490359000100c01c2190301c2e2481d85548c3c01c080710a5885401d50803101c00908246001c2000c1c201d12405401545c440301c0f03481da42d403030910904030703200008642e8443c568814041c040a401c1a0200c86401c00d919550400c00065a0b0b001c00908591b07901591240b0140000c403500b0034900140b414802e41d0341c07030388440807000d4040c0c80f03c06055800c3d10303803400701c01440c0310f00042c0c452240d0f03400901200c0a207030981011000b40c030114400340c1c1c1065402451060001102c2c4040b03102d003800e0400140c6698117000e807580c1041280540c80e451281500340d28103e12240d0402118007603090900081407541c000100395840070b038a100b07003001d510b801c100406041c1c021510300300340c55105501c8004407802180035202203a811a004e00000c040c0140c0c40c2a03 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 459441267 1250 459440017 459440039
    0xf02060108120705010f14150103021e1602030303010b0c0f010c0e0909010b0d0f11010c030e060a030b060c070f0b040b0406110a060c120606030b100f121b09050415 72
    0x20700c5004d07100101d000d0b000b4810072029110140004d00702541d04404202c982c41d003a007042200103409280070340c40c28100c1401c4081c091100140c48a03401000140102e41c1a003170800308810541c00b9041d00d850750ba41d100550140d4022108800d214025002a40e640c3c1038180701d00041c0c000c2a0b1a80c11090b5510014071540410041c0140d54a40d82d44440c031034150303101c004944000e403090103290400301c45440c0007880c40c00c40c0840316040c405103036581c1c0002600300d50151003201d4151201615040030358405c402401000044917041500006e1000715000301045080c10b85801d913040c1142182d5403900314441d4030427885284c080c80b030300344024070030240b02e030440c0c0014440700400c1b9190a02942c40300002c5031408150200480d449940d107001d10802030241c80c0c001d10940c2005c02054040c00c0108071040348c403001403000c000440690141450040340c2c0401c19840c01c0a040004042103030001400c0d6149084810200b1445800041d03185060700134071500c0c1c0ca482100100b0180380c00250f0003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 459442517 1250 459441267 459441277
    0xa0b04090908130305060a0c0528170f10050a1202090a060312020f07080a08040e0c2503200d14040b0706050105040b010302041d07140d0207030f0206010812 69
    0x96800c000c014541032244850210b402031350280c030240115040c440e0515049900040c00e40c41800000c4c440348450700c0303004804501c01c00344191a046001c501e07500440e0f02d400c41d0701444020051510a00042c02036103400c03a48102605000300210380e07210410000444000d114064078031301203a003054010304000840e650000031081d404101a078072070343c0303881059400030a810010303440000c0d500101001000384c00c005200e203401900454804d51240d090904c81c9000c0d00d40320008903170105d824055510101c0d00c1d00880d020002c0010192800391020f403190f0480240e00084081ea8101010011034901464405003240200305440090300700752411042d4a9110070f2000b000e000014070050880010055503208402c00070f03180d8185001c010071981113240c0c1604151040c030003403040d0171b500c3c802458121900c811803501c03542d40b42021200910084040d150300e00f804a0160303044801900900541c2e442030311000003541c4040f00490769410309109680082d442218512200001c0f040106 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 459443767 1250 459442517 459442523
    0x15060405060f0d0501140a0308070533010501030b061801090e09211227030a031a1203030a0c110304081c0c0302030406030b0d1704050406050a0b040909 67
    0x181819580e40010750030350007008088200410008100c00c1e06840391080e42e0140c401c04050001c1070f41c0d0303a004070344406043e010003002003c00090301010f0000030884680391201c80d00c500d15580d42c0704c0c030800044000400d1402916100135001003265806401003000043c0050b00250902240525060140000007450b0307060160035080819445804280e20307101d0000c410041c945600446060f000e15110b06402d108943d03c1813054030340560500c0026904000400010b188400c416807942c0e0740600e00c40070b500c041344000100c1542c1d49805411480340b560072060309200c5120160180692028080000c000c2a001003002640559260740020f07641e8815107045c4c24001d1101900030f01c0e60740325030400340c5194003d130f50440a07003c400f90446504541c5203060115a108d99078065600c2c02070b4081e490516803651000a25611032300358605505800680040e00031728145140da40b541c1c4a800b8941c00385042c260042407508000103244115021045000d2400d490840c00c60001d141c50742e021 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 459445017 1250 459443767 459443779
    0x408060412180306060510022109121501030b0c070507231908060117070e060d080a1806051206240a050c1b09070f050c0708030706060905090615 64
    0x40141e0321a0008000514401c04d800a803140c10034041085e0310030104039190443d48842443c0140d110101c0045076900410318015850342031a00000e8168950511202007904c6107041c7c0c4104480b03120385882c103c0340500f200c82c000b9180c0946e1201e491251540140070307a8003c4800b0052146400c04000302c8000c100c1814034040c00d40000100000074240343c113400c0002000c070a10400e4400c0c000c6c1d9006000e03d03808041c2851221a170181c0751001846005102400d62000450a480320602c02c4034042d41f01c040d50b40c0d0b802803000b02400450410344010f461844001001c65502d02460032100140342c03012100c02c65944510030040b2100111103d0380448002041e100c00006144011308400012901c4064403040ca40124034680075101c3c104606080603024001c0302600c503010b40d240c001506103420300b15804022010b80c2d05124810aa00030382c4640c03100010a85ca010016004880c491403003400007541e25040740302a201b040da1450300c0c41d000040071a0380d144a000c2110704101002d088 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 459446267 1250 459445017 459445037
    0xf09070219140c010201020a09090915110703020106080c01020a15090503130603050c040518090109080408012f1b0708070e0711120315040f0509210408060412 70
    0x206840030316203060704980d8a00c01c0e04114408603014000f0207480c0c5020302c000c6007000303e040f030002c0030407003640f05e0013a6150f520307500760003400201c00c10401c1e80c2502440a005040c2c0408a90b00369a102c0c00040d00107501c0e250000c41e040c800070600070414903050b4002e001400d001d0300d42c050558420454402807a40d68890b007070018200344054509c01c2468807414402d0b5143c918081d040d15001081c2c010780e00d804110520180e980d000b0040e42c040e40a13018503a05998003c070441c010450004042c19441002c103000483c21015000344008003902c070303400c00040401007440200404c0401000403218014040004000d03014011401800100411a28141d507200e040604080264000444210b000c50070041400d4000b0340008007001c1034002400c00041c1c001c800409400041c1038400d40e4407a400115000c0d40c3ca54108602c1c1180c451020030043c1050102e1503a82d4181280400700480c040c402d000a910a01d42170301c0440c0c0600014007156a525039442c5068845e000302c00e000d101c41180707 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 459447517 1250 459446267 459446293
    0x1080616020a17040e090606060d020901180b0406030605030105190b0a0b03070f0807180303081b0c06220507140103021c0f1d10180519020901050904020f090702 71
    0x3c10400c40308003115030540ea850401482d0000307400010b240c112950f010400303000c86034807444d0031038240300c000460040c1c0b01d00160004807110001c0507002c965034a02c00b203010461718110030003003040f034107140c0f07003006441d554a05050989400302d90104242c180303c001c41140740d030796400a2010003002401d14803466210340e1210741035003040d220303200018400c06d407000380c00390805011b64000c415411305104a85002590700b8a00800f030100904100300d40c000b141d00000d00d103d06a007001f405000883e00c0c2c200d000f091700e82e500c1d021546a04e9203031070303914502882d550003c0c09204164200c005000302e14109600340b1403000b003058040b0b041540c2000b00e4860306095502e0354031140b1b002c3c0d00205410814100110580c0c07448454090300800d0b144554a800e01d0009200b900b504040c01e01041885840e0442003a440016102500c135001c0c00c903881065291441c00800618400ca8200045907221024041d810740c003101d0094001a125218812a140c000800780d80301409104444844008207 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 459448767 1250 459447517 459447533
    0x5060c01020f07120e0d0f030e03011107140d0801050603011a090d0b190515010305040510090b2409280c1112090102060610051e18040501080616020a 66
    0x81002d0b9004410004092441c990211100d000b05074200d8403c0810b500c192034041f030f40211108001d05011000107281f001d52000c9d003082100e5981c1c031403c661030304c41c0742c00c1291315040d07030700740c0f000aa00a8660b07402d18180240d80740c40c16514080d0079241980c2c2080030b034100040300d58001045042c024040340555584110040c400144110a008810304000c10510400c4050001a45000f4101002c01409005210b60040c400ba001d103008100e98840d42000d90801071110040d003c61804e00d010f8205000101d15024014500b1820780ca1040c540c01a001c104078807864405588060000003041110341283c1e01e9412494804281032585503030381e03080c0c908440c441c140030300100c0d801060120000000f844184044c102081d2058030700407072900001d441f040c00a203094407a0202d030240c1c1880511500c2658180d10b01400340c90000c8070391000494054000003070210030007501c110f9803091800c2070f0040130b048400f0800140aa40c1358000120304000c212182442180700c1c3e01c4001010808407 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 459450017 1250 459448767 459448777
    0x109230610080d0c0615170606031203070309030c0206030a0b1e01090306020f09030607020c030f07030f02060c1015031419030305130807140105011233090302011d010b0a05060c01020f 81
    0x1900c0e070b100349881f20440383d400c0a80c0209054801d400500804c1000202102103e601402030301d40020080d184e45025102e400361190042d4014034040200440c041043c0e01900e940141104c159002020b4403d01304070700080302d950035001450a00c0b0400c001961500034080702806c0d82034043c100186440840c1c50074804817103110042e0b10600c400e84840c1003d000020600014801402d47d481c00c503102d030b490328066a60001d0140c8000541c0c94000c41d41401440b6040606480a102030402200b0714400e044550005030740001e0401c4882c2070752040024500047c04401450601c00307401501c054004050051840c80075002c030403039100002d00e04a004003000c51281104440c031a02c0c00700a1421070f00160024400da41c2541030003000314448600d01c42610075440d0120b607001110f030b04038203241d070301c0b04800c0c400c99400c0c4075485003010780641004041038001e0f050503000303600c04000c403400d0710404002242c104281301c60501c074904001d00148200d054000003d80703070540e0500c5864a41c1e002c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 459451267 1250 459450017 459450029
    0x9020a0305040c050f03071211090114013f0b1215010905040209011503021b0633010c02062115090c03070309050109230610080d0c0615 60
    0x1c1c0e00304100402002500c0c1d903002d480b06503607100c18000301e40082642d0b007075103001d04d03401c0e04143c00c150380411076003040c0e00d600d1f400058441205569180207188c040e0000003542808695a44541a16546501030800d2240b884880c0c0781e004003440c042c1c40d01c0003c907a0b11001c41083d1a400034655648440c2e0382c00b651145030200429440b4104816050401010780010020078100f00c184009a550207001070b041d1004941302041d58542084254000c0c4101701d51460043c1020003010702c83c031408070b8034911590b0710010f4100086481030700100410541e05260849028011030707200294860101000c0b03c52016080919225107039510781031046030340c05004000307541c4604215a903002504c40400c0044140c800c012241401c504104280c0030040c00c18003003580e5000b019062000941104120b50303005121594090541010345041c105d400c6500c1d102441028003041d009000101c811080744e415001500c24290b0714213080721811300c141400e03070324203031280c22203040e90306000c2e00c8800a00c2 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 459452517 1250 459451267 459451271
    0xc0e09031206030714011805040606050a110f0d050c0a1703041a011802030402061201061e110a020907110d090911030609150102121603080903030108210409020a03 72
    0x407600748400c4152100a003001e020341c100280421010b005002c40c060000002d081ca80f6141c9010941d003e00c1e00101d5016680c8642022000100207030020010b20b84a040d950300d11000c01c9101e0ce0580c3e4442a042c03440908da40070040100c0044d100d403001c1c0000800c21025034442c50071b2900d41c104090f05040c0d4032507034403070000103000401c0341c0380c0305003250290120421800e80d8913200781e5210804030b88011110a680000018003199118411030b0206001440d280f1017558544c0e05c000c0c0203002c2c00d4140203400020b01010f9001a01510f05000300e40a90401050381d40e43c158284110040040e2070300040c030484486102e2050702c140105610070b50f050340c030700050b5460041c1e01c00c26259800b0102403018401c10504c29036460715200a80c0c004110380300f4449900004c00101c0c900440303514451103010703000c6140800841e0110303006180c180680e803082d0407138907030407041903c1340700038890100b650b0311070306154092015080200c1065800c0c4040d403414540c0e16403004083e40d22440240700025 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 459453767 1250 459452517 459452527
    0xd050307061b17130c051008040b09010209090a090804030b070c020109060801050f040b0a05040623062104032102030906010f050a03020f2b17070c03020d0c0e0903 72
    0x502140809180e00110724250783c2942c1540400008144081c207001c006140c80082c0ea010b210000500e0701c01440040e0400645102c6004000d059400903101101c13409104c201090409005000380c40c0c203554024465202612580e9401d0010101180d01701c45c200018000000481c0800d0b013a103100b21a01d8a0f00001c2e07521170300c00141011600e07000310702031010b07001c01032000707445a43c40307800d0b0a80d085d103000030514440c0c000640710b82110307401180e00c80e0602c00701090401d10424803c05103400d0300607844800742c0e10ad0410900707000e03040b40c140c1040c07196411545980c8040100710781250090034410f000088190112618003803000c0f00e814060380010031311040d58802c01202d070060035888031001d03005003000002902516144000780c0300d04d0410b4200f201c0c1e030b560310700e481559120302e601703c4501c1100c1d09402c400031500441c007a00e0510000c0d0241c0394030500e004c101e814903a4000e04041f00b1340d00315403c00c0348920002130261070b055058080400e81545041e0301b103000d0751000c8002c640314 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 459455017 1250 459453767 459453791
    0x403030203191b0821070306061b050d1b051b19030b0c0f090409120f0c020a09180203120417030412062021010603090f020405060d05030706 62
    0x2e052440c141000300003201540103420038501c9441210309034019600c9030713200c0d0214500a0311050340e003110207920621005108140c0d4240e171101c8116503ea4440e2160a903413940d410506201d03480018006400c4a40c2c1903420910034181c071412115505600c050012480d1207482ca806480321080100500302100030701203213000c2c1004c0c458061040011f183c0141142d40c0e400764040701902c4023240f100049200c141b486641400d40704802806042041100f01c14104000d00300b10070045800410000d02c8060f4200b841003105950668014290603c1a403800c1814001080c904501e030382c010841c0104140140e0b02400400c0f00d10025440081e1103a080030a51510005c0c2800054001d9008000412022180c29408100550060400141814a01201c4581440307013000704600003800254045400c0110302c0d000710b040c41421101c41140e13282c2c00c0130340c01c440070014007a14117920b028150f0010300d803a030080d0354000005805c040d00e83c01d4942e141407964100010481d01140c9500d40900c2c1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 459456267 1250 459455017 459455047
    0xf0c06120b091302100210090b0a1b050a05090a03120c020a0909020f040b0d0c030c080601050427030201020d0618050a020f18010e130b1201020901052d0403030203 72
    0x10403080300e504102e41080c2c07820050090101c1d4000b80111480254024024020311005241c41d100d0602030200c26011320704007241910441c2d0044905161000c8100700421b20b40c100c542e0b181140d125186803502101c3c05403540d4100c018031030740c4544c02c0f03003012001504135409109650141d80715035225414a204204000300e90f42c001490309071400f504030025946804c400e8441000541c0d000550b14280b1020940a07281100040d0034035a2030080041040503400324501141c1148060702c81503622a070400c41a900c00800b00803100341110506102e0b021030407122080311344607000052074845400c8020341a9a2140d00370b180c00729480328100b0f03030b61000b4080d09a104420200452501c3c03248617054500d8092500200b0400d5020f0662551703603400b914450f1043c80009190b12007548140302010054a00d0703090290050750340728828000e01c0014002e0b54845101615483d06108601040a4a40ca0080c0c14161002c518842500195100c44010006180281c0c05181e4a20310440c1081c6 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 459457517 1250 459456267 459456281
    0xa0804020a051c080304050c03190302060603060c073207050f1c1401021621020706120f180c1a09031207020f0a06110c03061b03040f0c0612 62
    0x10103400c1c03841425481c503c0b8224000c61641e03020b22601e80b2521030b400d0a07031502113038506854051241c0300c1100f45070391144400c03003d000d210b0703800c031051551103506158803541c0907114141092418026840000c1c040c4000d0203018030401c1120400d072400840d4149001c03c20030f0b1003002c81d080a0401d001500344030541d44111001900c00d090040b00407108210340300c205a1020b4464519821101000b420070b40407a04100580e4490001c0d0034002d0808400c80342e400a034030107440d0040714032803ca90b40045450812110181c481c07000c82d21035a0701c0c500c094035214400d001c10301c0d40e0720604403a660365103082c540094010705d1f11102d440c2c10000b40706403442c801e4403d03d2560303c1c18003c40500f0307600019604000b0803040900381d01c800b21403011544111043c2402e03988565504808a44154402c0045d103190a480080f40e4060340e04605154582c94103030343c14010322401685d58144101c60100450f08a0300c1401c242c041c50890b910f401080c520650004000605031035069120185c05001c0c00c1 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 459458767 1250 459457517 459457519
    0x2100e0117090304170a0b0a0b09010603092f030f010c030c0c1101031107060207140c0105070308060411090306010803120601090e040210030b04020f03011d04030f1101020403080a0804020a05 84
    0x141160030144032003076403070003130b07101c0c3c0d4141a042c00f8548800c60000c0c45000441e43d80518003a0341820092852000381159501640c0110340200000030118440d000e400255500041500320440c070340385880f02d90001000c1612400303043c0803103910b900d84082143e5040941000000102e038107a0b008000c090351080c8018000304240c003e901c50114001e9001e420480102b401d000648070070760041001180100030703000d0a680d1006c14142d003070060099048040d04010819500a40400e2005503007600550303d01a00003505c1c3d20005005041550020340034550f000120390400c158a0002883d01101b6081074a007508007140b032040022030f1412081d040750013400c18804e540c1c02c000001c0308124000704042d00c945660450340b4405030199019020071f6001610555035a0b030040d00280d0035600a12401c2e8503140404403502541b0369000840d801a90725580781000e203110b0610856004a100079a90955542044004006000c1e1401000001b0950f11030126030b03d483d0041040c1800176900013 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 459460017 1250 459458767 459458807
    0x2103090a0f061b0c1a0a0305060306070504051903061d121c050a06180903020601051507230115060210060602070504090302010e0105090328020705040b040902100e01 73
    0x1c0c0030180e004203e20700c4042415021031098582420400e5002d20701d60f020222401c800403808055207031500c0200881c1e60207840910684c1ca4603424540d880e18112030500008400b071005102602e42300542c28070b95185000007662458803a140c1d14115080c541100c0b1850648105180c101403080c84cc400030440d41440d101d00305200c1c030b801c200c4903418528a00b420340c1e9440d00003840444c0e080c1e00c120040c100540350cc042c45d03400d42407401c000b44000d010a50142c07250300300004013450b100700700d911461480135009041c4170140d5160181c071000c140e011000040f50030f10b40a0800000d106003000c4600d0740c901c1c1800310386482d1010381270107180050500424200581485840d40006104c82140d0041d41c000a6510050504074010310161011880d036508040034010303030800c000090609000400582100d0700942882e0219107240512441c0c05078012a004210300d00c1e0581c000003460201401c0841d0300c04040c0d00103070381101501303980c030003090b40c2c070500c1d03490340d41d0044002c82c100c5406600 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 459461267 1250 459460017 459460019
    0xf010e0c0711030a150c020708061005060903101a040f0b030715052701030506031b06030408040b130911070f080307140409050601020c18040201030b2103090a0f 71
    0x400c900c0c4109030740640003140000304010742d0b8404002c0f40d00755030b4004078103070183d200e0301c0400f40182c13514000600040c070a2a0020031400008104540510102c0c6204400c40b46410140505600100e04040c0c3c10f006004e108543c40e60350303000e00c000c5801c940180320b5000e51442c0c01c1000315000c0710b001012280c9480441d09541d100014442c046d030742d0030000c02c041d4054a000071a051f01c120700b40018845081440701040b49a5584024003040707098078184510707900c510904d40d40d40e20b0350060384003039004080140202e0a060006541060041118034601a2540c0710b20002d580400343c840703803203129140100305814030752089000340311000d00300750324101c40d60311031942c08103107480d010301858400000308064078056000714510185c41558240c41c0d6580349040070082204075101d0b405400b400c011071020385032441a8403c0040f404042942a40361900110001c0103090383d155001a100c0b10b54041003090b00ca503010004500c0d400641c0d4541e800c4040c4000c080556000369885c85491070 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 459462517 1250 459461267 459461281
    0x503040b130911041d101a120f06011d0a090c0221040b1e07050706020d1b03050d0905010b090c07140a030203071b033806062a0105010e0f010e 63
    0x100030614002901040c1d61941c9643c3c21624a80034294002c0c4c1c88040484421f54074801a50701400890801c648440b0040e610f145280c41104000c4503180e00140418010b907010000500e00d0100503000580142c25040d283c0c1c44260072901501c51a20143e4800c800c2083c1c0401c006141c00308001810110b141002c0c58214013080601804d0303803402c2da080b040502402d81c61103080588030040e4000044815440e910a1701075110118892030400241c071580d55081e4103190f11070400230a9501d980d1b158685821982c1c2d100003410a048100c68954030740c8407140156844804d69806480d07010170095840f1680c2c0760400221031004c88402854018142c104c000c2900402950056604501540c46c0280824900b240b201d80c07680000300b519954800c0c0420090030203010036600300403642d550540b00b007001084034a003d022940340f507110030b040140d901000c3c20300103c055507641c41d5001041d0100c040715032509584003600402007400f40201040388801d0034042c0c0c03500508030030750704c0c00031814561 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 459463767 1250 459462517 459462539
    0x8030103050606030714060c010207020d140f06070c0b0405102408010e0303070804021f09061403060d1415090607030c0c080a080c0c030a02010b1f05030a05040503040b13091104 78
    0x110500e445842d0106040d08c003200290100c0b00e0040d80203094811940d070b140703007400c2d40c15500b8030781c1072492140a0142001d40310000b809401040c0948070000d0518660340c0c3c1c0707416010001c000303c0c2d8600405400c0c0c4c1c9224a180079060404040741d45400341040c40c1814030f20420003551003900c50f40c3c103200700c1030810000442141d0b001072091428070050303036813800480e410603e8413031442e205035881520786098690207001030b401c0d1151503542001d169880d03501400036010a95507103601c503540c00640c40c005100403603001401b03018901950518403520706042d96540007120300e03803010342003a020440d00940c91300c103403c04c10031b1700c2c1410480c1d40f107140c9a10140e401000681001d100d00340012030f0340c40d4a0f510950341c00440c604100c941d6007107250310083c00303041403800305400f4100082400c1c448916007108000241016510f2030304655a0b00c28400181202800655044c00100000f28644001c14014181c001c05c402468460714a05404032048803a511880341a00744203100030320401c0081 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 459465017 1250 459463767 459463799
    0x70803161e080c0f040503030408070e0a060b0a200d0e100302030405060a02030601030f3b030703030f0207050604050a0c080105060d030e0102070b0313020913050a12090b07080301030506060307 85
    0x30f981c03060780391009042e0100c0c83c0e206a030407046e410310001c200041d5040c80040c6100590702d0100000c507140c0c413110758840649815000e0001403034014401c0c060607921501c07503024242844a000085c1b900080c00060901c000303008030500141030712002e680315050100c00c81120042070300e07003149103261030f071142b6485203006407014008507000000301d41141c0c03080d006120180c800d410b00f046491140c4c0290b03074400145409101405641e65584e455030019803a040240c03415480c0a180703010450741e0f08070f0041c00d0700c0580f00710030f590911940d00400d20070802c81c1c4c80ba40c850360088c0740403a12801d144408410341e03848040c0aa0500080103016110031003011320042c0d1504140113840c5403100143d0501c0d400350440b064905000c01003080b0070419282102c42c0c13500a680003141611404034010007244450000303001030344480140d50003d80d02d91441d000401c07941c03404030812074440d80b80b003803558804e51098401540100c01441446400c0c8800c5800c814114000d0a0351071500000489003440c0c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 459466267 1250 459465017 459465031
    0x90108070203040f170d0309050d1404030609030905010212071a07170705090111030301050d1b1206020901030c0e090610090e1e1018020708070803161e08 68
    0x18000c544018000c10030749000d4140c915110700303002d80b55002204603024520500d038151144022040e40305010348600042c8a40110152140c100c0c05102901c0c900440c1c07016285000c410803000001c10920b21a000b1a640300703940f824200d91909000a03d01005c05005180b0103208200c41c00004140c041e4000d031500c0780daa000480740d07441c00c10581380032800f1111070114500fa41d00b00001039600c00e0041460b030320240c9034035500c0070440c04003661b070340402d000d202c0d0441c19403032603540859001f03002840c0001441e00c034180c90079295002e2003c441c4108804035080c68002c10361103403a6800d4050703900c440c400b9140c0059501d0207600014004100508454094000300058407002441581c060000e0f14400d01c44100500f40f540405811400010041c0203603802d00f0007040015150806d113100301c40d0501034680004c0b5824a4880003580045000c440e049000c001c000005100764000d58484c1000d03054507201c12241500c0900896040c03149040b202c01d210850301c03102c40d00700b00da10b0b4204071 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 459467517 1250 459466267 459466277
    0x6050f0f010f05101101090b0f090a05070b07050307020604030c050103231303110f0601090e0319050f091c021e031905150c07050d05040f0b21090d02061b0901 70
    0x50101e5080e01c5074408000550046e50030590480207201e5451885402801c54442d540795039030307441c0c2071103460351903003200102550800201006140000300141050030300a4003079900d494030503030009880c1e90107540212000745010500304019a0988070300070006c0c03142c41d102a46c0d02d01181a040c21658018610380d442e540da03800c0c1c00c060511660700c6545180106088640b038012410700c06603120424852031a03d207041059100e030001c0c0200540d500c1e00d4040181c1c1034031920610342619540c020050346c03c154041480110070726034420b1481d200c0400c021084021421450041c401d10002d100c004003d5289551050074054400113501c5407000701c040c21200081245251150500c40042d070049400e00d014424080034201c03110082200c244035a003181c0ea540801c4ca800e9606000b00c1c8945100082846020001549603000810b0000c01c00291030400b10407070030800c0d62001056942005592000c2a4003548540400803550044806204407150001001d2110054880c0a1000381000 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 459468767 1250 459467517 459467539
    0xf0c150d1523040b0607031b060f050a05070f02060702030a0c140307063c020a02010e1002090411090a420801060509010c110a0f0306050f0f010f05 65
    0x81403800c500c0a401900e41d400034180301c0340381540d0070540001401e8456842c2c185519883e11700b400c1101c0c02d50354180c031200705005640e2020304004030340082c00d680f019143c0f03030003000b11038031803007000e2044031082000110350410840061100c4603482180080d0b50051050000080e00041510480000c1c1d180c41d104000c07031031400c10401c0c5503460448042d44404150f400030400e05811440483d1710381078110100780c1c08010302e00d030750030304004101c040628030350821048806513800414a01c00c0354000071418502c1641442e00d440300136010349000c0b0303138040750803141480c160040a030b40b01c0d01b25507407a081900344000101d041c1c800b8859050110304144030103031104101540c1384000154942c0d90601c2c82101c3c02c20f00c0c602c8a4024140d0001403600d0004280140144144e13004050182c0d10700b14000101e5849280c1d40150002c02a40020b6242000038882040041c202c05184521408107250421298141400001030140c0480c2240384006100c46030205656008403101140c240c0e1001c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 459470017 1250 459468767 459468791
    0x2030604060e0901060303230a0e0f1e04050a0b2b0c0906080106091a0111010b060a03021207020606060d0b0402282c120708010606020f0c150d 63
    0x18001d036403003810360041c41c0040054511040d0b000380304a03801303500ca10400d5900159404440c01c07260041e02d10203001440380042c450311651088080807005040c0706280540140003601400303001f6000c40001315821350008480c10107008080d0480715151040c0200c0140d03900086440d01c81c4140400c4044200c1c1d08c15004120010300280001d4000300740e4103416449800c210003a04282c0a012010b600f462000542e82c6020710071960042e1945151201c0340d0b0403400111187c411800704004135648500d4042d81c02d070b45010050203072007a5500c00581d00c040c0c6844819022070700410704c40c10754011038100012610f44104483c0c3c2d5010484d00082d00305400310028000b07026030420007500360b01c01d802e0b03281c0c560808030001d0301d994842d4071032004000c01d051030b0144d001100f14030002881228030300d41c07005d0300708149899030143c0c40c0c2c4240c940d220307110158542120420303400f00c001070344000c18400c4050401e200301000710707500380d81c0184402003020100a6500c5109421111141e0b526a07135403817 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 459471267 1250 459470017 459470021
    0x9300903030f03070903061a0d060e01110414041d0706210c2c06090607080f07061d0d050415020c030a030e01025808011418010902030604 61
    0x2d010100722000d4690819000083c0543d12600085034028075001e520603c20035010340800081c00000c0c028452207040c0d94600d0080d1000c01d040705860740d21180c1c404c1c5200300f001c014001400300e5166240310026880100003d845c1403041d2442071080414540001f440085641403d07200c40d410520f014200c1100d03032815513103108400030b0b001c0e03161070001040254080203d070300903840c04030781281c010341a02c005480107085052855020790100103400407411f002c070150034807074021a081400c0c81000c2010480c1c60f844180201d03403543e5220f6a4031134440340d148a00c640440840f004004140b11443c000d441032055000d80540d84851030841c0a810717208000e1207116020160545050040d01e1030048c1c00c81143c0e01403240076014150081e84054010301940202408801100d00b0803088461703e000b0882d44159401102d0014428514041c0d0000e103d181609050741d6034922950300d42410345442c0c0da50051158441c99680010000310303d13828044505586050400603130304d0300d4440c00100 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 459472517 1250 459471267 459471277
    0x403210203070507060f03050c0a020c040b121203100b0a05091306080d020607020d0c0c0e04171308100506090a05100f080f0106210809010504030b0f0930090303 71
    0xf510034560040741035076024410701c524000303580302031060352101c9100400500400281e140140c1c403010035030f0220301d401c2d00b2601072042e0140800030381d400c04d00d941c01e08081c0900200c44c00781318000305004025841c140401d009040821501e03046c4809018014918415900b042e4802d00700d203140082c0000c04c50703018000a20840045848502040d0406034480b2421034000001d40225010440860301584810381c1d803550101030030701c0843c03c1440604044d900034005a03841410058501c4029515600609011175000302d1905c1e15880c1c400d055181c080054075950303c150611013403103002d80300c1028a5412117000c5001158aa44121645854407015442440c0b12942d00307400084800000c1505071101c803058000b404400c1d112428180302e8141d64032081102d6648051100129810340064042000f0525142c0d03c0d0994036140e46400800c180c58282140012209001c030b207540801070040002d460084102c0c4502c081c600c400b0345110000043e0a00d0700d000212140c40b5603040c02203031 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 459473767 1250 459472517 459472523
    0x301060806061207171006020304090213081207110a03171803120d1508060f1005150c100920040e0d0c0c0801050c0906160204090506150402040321020307 68
    0x14149446a0028502145802150040c400040c082400d840c030a1103100c082e107e0a4000318078280c9414410300095120a0002e44600c1c0c0f51500400c1d0b000d81840f1942c039030403d44100c1c5031281258280003960141511a4510a10313036248100001017481000b4039511100fa190140c0350f529490200c580c6020300381c0c3c02a03044c007804070f0a01c182a6070ba1302410000341e001c401007240304003030860080c11030082e01514501f68400c600141d40030f100b1000a55000b40b66242580e015540d0b070010503007285e2000f00c501403445020031414402841003051414034413a41505000b04d01c041e031110201c400f040a0b0751400300c030484c82001000d407a290440070500e050902142c9140d07100d2680100f500704d014004072403200c4406400903140005004007402030848035030b006c0c50881e040c000c00501d944920744038003518803031038102d50260b0740d140304185440340200081e09007894040401e514041c0851803d61040c0d01c103000500105420442c0d502034002000c0c51171038002c009a8050303246000f00c003401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 459475017 1250 459473767 459473797
    0x70303032417010608010203090c0f01141201060809010c17150603040b070906050a0806040b120604200418020f0111030c011e090308131b08010b100e010203030106080606 75
    0x1500760b0100d12495005510030003c1040b40c2d02c81c2d4602e401c0c0e20040ea6225955801412640c0c0c061920342500c244c081030504000e500480120744041003500582019a0208884001041559000300086502c601280001c02c003080008c8009400c02601e00c00c12886900740c0000a41c0e03500300d081074200381e0800203101035200c2c0381915041520460864002c40054448000001c010703020b00203803082d6100c00d8980ca505940c8080901008000d6500d02035031214a4040c02c4c1c41d108070078001d00b4000c9016040c0305401000d01d030003200c0d442c0701c2498000c2c01585400148410b03400c4402c00117038800c0c3d044480c04d00e179000c0880100c44100e15182c1144642c0800508080c1205c0154484541c0d450f40c0120000034038618403d01085448040000c1e0100380d00900040c5003404000b03220840780d12812415004098040345050070300314540021990307030741d202075961a0780780100003d0a20980c61a01260400221000070f48a002c18400e00c410b001003800170400955400c0140d480410f4a2080c2d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 459476267 1250 459475017 459475019
    0x210051f03081305040203060105030c0d110307110106050a08122d0a030b010302071509020103090501230a09030215070504030501150e060d0c060f230405090c03090703030324 77
    0x202c4800d50281e40d0a100c10900800c00252505140c02078911402c016107541c1c1c02c41d52100344d141c03510b40c00f4101043d0b00075541d0300600d0280401d10302460251039203581e131407002d62580c8005d600312071158021300d11404109504101c401c0c1c0000e9403060365040f100f20240c585440c007100852000c4030500071190446440b440c0c004201c0e410380600107070b54599070288003405807080190101d21030041b020b0202d030881000900b0701141a04a040c0e00c3c0d01c18500050700070810b407909421a01088070301c06107005004c80b050003004c00c0509160300702d10540b50800041c100b9503400380d039170004500c92107160145000041d401c9801442954020342c1c0040003844918504400140c186140b0f0085000030290040869a28182480361701e406540c00107480302d0440c1000702c2503961040f004680c0040000780191041ca40c1486200c5c06801602c618026803224100400c00024079001001107071000020b10401c4139402c0d0004010040b20b402d41800103260241e40d021240300c0403024188070300c440c01e8500c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 459477517 1250 459476267 459476273
    0x110331080109050d03062615010e06120c0d030806010c140606090a090b04031d060705060109051602070501140f1305120a020108060f03010b0a0b0c010c09060210051f03 74
    0x82da8415106400f610940403541034140d044030303618080c00e98141181ca40300d6401e0021111040c011250200483c0e180743c00e406510154a6401d030480320040d58950184403e41c2417480c20100d443c1076000140c001e00c5103280102d82a111040c038060300b04070703041c2c0c0401c1550f40070340c40d2400201d030041c03050660a041201c642d0394508041c0e6031f00e4003030303068a4000741050240e486145642640140d1142494480b628200c0d5140b98604500720300c6500101648802e6841000400702c061150003d0842c40d1300d003c2000045500c002c141543d01c518400d00c0750490ba40c00f00f203201c150303002400c00300c05004207591402c019000349024010080c1c1c0005501a500d03200b180c10300221802111f0309603141000c0780c007107525114aa10002e0200349400080340140ca4819000c6403840c40c082d00004681d05074000044090003942e0101440f800000741140012000380a034103001381d0b0074109032407854074103034000390f45042030f04a2280082e038910108010300c8140203c9610b109403215040c0b1419200c1c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 459478767 1250 459477517 459477521
    0x105041206320403030c1407050c090117031c090c0608060a0605431a010b0306210f120a0201050a2f0705031c0b011103310801 56
    0x8840002c0014000740d061022a8919140508526040d01c034140079440d20740d410b034003038994403442d84140900790b00340e010855a8600500342c01d038081d1004203070076000c4000340400c0c0c0006030004040810007215460000303070700000316a080b410b036004101c00300c01c048041c040205a0000000d00b1083d554100180496001801c41c1c05000304590204d100c9948640a40304c5101c0c00a6015044003526242d904400c0e8000c182c2c9010034082e0202008000820780d8a4804038081d50f013214628000344108605105200f00d00d40900081c060007460350908000243d0120783c0441c504c00110440b01c8486040d0406101e0400c42031101400c90fa01080c06105c01c0d442a0840119400150318100000e20302d20103030700484880b819130185070724104001c6500043c07040365910b0040744045007007200c01c000500400040c00e26815400b21108a420742589201c03d03a8041c0000504000003180702401003200801160646030302d03500d10b84804501c1c201801402990205110260741080c540041c1c025019 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 459480017 1250 459478767 459478781
    0x2c0307120311030a14070819110732030a080a18021002060718031a0601140f04060908030a080c0c0a08270a1206110d02030a09030e01170c07020105041206 68
    0xa52056600343d0f921503080301c040c40108c90302001c0e5a00d4041c1d620030250140c1c000002d0009250340c1a1525046490b215010504024549648400d5461485401c000051081d00c0c2d040300c130028602c1c200741031000514504018100e0700d44203640b481541080d900a000c0700c0201580580501122205101e000e922010304858580108540d951030041908030301c4072000549038010f03149581c140300000c3c1880c048500401050502800c00c0341509100c3e40c3d0006404130084403240684e6031410301400901d00781c0c3c541e000c104a03034810f101c08646580c001320440d0744403260100e9281c90381c00d0f611203540340c103c46403800b03000100c00242265800204608607000c000b02100d190030810b0030b113070610a00183e94400c1001100320701700408000741150300811041c40c80c0b910740700c3c00c0410501d5444101c1c0c1c422303030788480d5203540d60758440308043d008004000c5034078090800501c4081da03d40104003001c0014000641300400040701e0701160300841c140d801a204200604111002034134010b00100030b0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 459481267 1250 459480017 459480041
    0x203011e05070c050a08030919050f0d03050405061306020913150503190b06031c020a030225050415030609080304060b09041505090c030f012c0307120311030a 70
    0x20100010b804034041c03c0301440342940b140007050340d40c400752204100da41019280325801e0190190050308080c41107800b50200d40510007820a6890242c0304510f808180302010081c54202420040070440104907203901c4030310101042000005407910304024400c080e03e103a40200c0003140560a001c00354403404d00080c0028940d0125500c4504040d615505210000c141d5160a0380b03400c000f4000c002080c3c4c024a001d0704940100903d907a04850003110485050010f81c0030280107800c0c10780c100310300200311708201d10001114040141d12a140c40f1180500b50003641c4481c10001d410020641c01740003183c00010030405490f40707103800032096005440070303aa40ca04202d4100390626049815900540c0d00008036981e01d0120110740d8040c6c44024601144c0f070107440300360401c5031000c0c44220302000c90310000281001500040082c500c030740c9800038000c882055a090182600001101c0841ba0800c860416910702208114090046440c904400740004800d000010f4280d4015030306040d0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 459482517 1250 459481267 459481271
    0x1e03070902131a0c07060f03060504091101030506100f0507031808010c0906020c0d110319030e03010606030902060d051b04060504050a050105120103060e0102070807112803080f070203011e 83
    0xb0500d01c43c02e003c0c0c0208900a0520303009404200304c01ca0195420f0b21901e8410704020651076501c0700040c00311281020203860f04415442c07055619a414495a42c2c444030490312207540034494203004010034080b4240c01e044c464000762041c245800380d04010400c440040c2c0f00c034034464a50f801107000c1c16502da80840450410000401c003e4004551002c0c2c0d040c1c098035100c0303143c40c5602c0f40c3c6071030300c0c1040d01181c040c000e103801008005001c01701692100d0080e1100340041c4400c806040c01c58007940c0c880302c00c0510740080d140042c4c1d07916040b1260440c1452001c00c4607211703614500801009031044440c2c41c00c00040014003a6002005081100c0e001c44982454603a01d00044d9168807a2000108001028000510018070581d0082990307180c141c0c001070070140c4660310082c0b107900282c026910240700040b0b1030a54a4503000d50700c0880104922203202c1040e6500d0310f980f21186002c02000e514002c251622158810001d44042e950020002e20441500b064051490a0982c0f00544014 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 459483767 1250 459482517 459482549
    0x210060314070f080c1c060911090c04060c02040c0e0a120302011a0102030d0c0509061201050a141c06140f0411041e0902040b0411040906090b1e0307090213 69
    0x6000b203e610001c0302c00d2840074102214100041041103e107008916140b40c41600c2013001042503841800c04807841088580007015100042040c2c1e41c1c002000d00c0c0b0429400c100c18008264003040000d1100e6042d200816001203101c07003910440e4224a015030003842d45440090040070151846070090b01a40007080703100801481c0445100350581d00c1405a44104075003005c0307900d02d03809010301e000503180083c109644600011031075400020420410410703d4014856450149055002860300005c10801c080001010030810b404d2401c03242c0b0100b007845901020f011aa82201644914a0b4072090f00c80c40c015411640059003a602980d941800c1384072501c0c6030509200725030014911501e02a061a94190050042c08091340304136001a1646600b9440e034950340180c00000c1c5c2c42c180029103990504c400d010071601141e204049441c00c04200f030b4420740f01d024a680740c51991519002c0f0040320000444d01d4002140c4c0400081480046c0b24a8521800701c140d1095441d83e020030b500e58 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 459485017 1250 459483767 459483779
    0xa1a030c0922050609250903060c03090632090c0405070f031401030201050423042a090b030406020906120c030702163f1b17060109020307021006031407 67
    0x1c2400c1b0303a5000c04449020085c07030703101c2000c0310042c1c0312410761070405607844c0c4a58483c4290307803040711000c0c0401c2d1140c10708000c100765801a40301c010514010b8141440d01d10352154a10b01301900c1118071900c800c1c002c10103105052119000c13142000c3c1c0184104d041c2040c008200c003442d4203402c00013a1030460103612049015a0145c101c9030140c0d1154203050074105a10010b1312400b09907084082000341041300341d2200c0c0243d000d0342d007280a204906000c005610741c500c1146170300d80003c01031203000030704c032800c1d152060b2500540c201100580340c50442d4040b456074450007140751083d401d40c20400c00704200040065104001c580d0075618100c2d42d00e81d03000155a4140508110100000b401c28102900074010340d0250028004c01c1c9500aa5028984200e101e100c80503900c804584604c281d1a074200c0e03800d00020103400d42c10b43c025a0829804980b5480180200c00711135400201180c455882001840603d4212043c20030001d80c3d01d00d0403002d0701841c0c510038151401035031800a10 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 459486267 1250 459485017 459485029
    0x304030c0e070e091e2205070302030d0219111206191d15041703040308010f0e0c0a080901060b040e09010c02060402060706050403020715030c0e0a1a030c09220506 72
    0x42c0520307030400c06010400c0030b00700c8003001004000101100411101600703803c0915401b03800c080c0a24090800c95003180185030038004120221010355102d00900f1065070a85210b079015543c00903540107000800500207140180f0356800703101c4038401c2400b407005080c10350262020b1494065000c100d060102825100ca07400c48030090030050704407025a90b41c158000c882903074454821031003c80d2118558024501a070410f035400d0340081c456a005001c10380200500b031001e0315000c40c0403d49441e00c95401c0b130075841a0301d8164100710103c008a81e0f400c5094214401404043c500c140e2507903107800c000490742d60120f4440c2259805e0011503003a0600100344c3d01d0196801420080c68064540c580001510000c2c00071401c511858030001040459140e082540c6072160f540814142080d4200400714815091094841d00040c40c040110925001445038004500c12007652280d0781c05000510303e01984131201c0e00486072442940844000c48105580080e5105080255890f03800c01d010f1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 459487517 1250 459486267 459486271
    0x417040b0a0302031e07090e09160b0a110604080703200d0c020915010c0215040801090b09010b010206330301020c060610090506090d15090b100501030e030f0a020304030c0e070e09 79
    0xc04c1d9030000c28406881080d00c80c580c002c02741011100c480030b1110362001c085010340d0040305110b00100f070b0442025440000c902c401c00c0403400401b02820329850b0304100d841410002010b000c030004900c80e8004400020400500c034800c25980c3c010807041c0050060a8090022071207040481c0000d0703038011400700103100407076040e503c2030031384025a42400340d5800170098121074000140030008a5903000d000307010030544940c2d000511410302c10075131800e48401742103450554100008200101c0c82c6207a40c10480c7c602010b60b60380704000045071031030301c0d1004080d59415500000da102c81c1c5510000322a4028a01541c043d803208001c00301c11280398041d4080c41d039006004100b025100c4c81c1425940c150b550203015540188403201014000722941d2175000c441d4802d107201003040004213221850010903003820180702c212014030314283c03648101d625807510168040780300c4042c14030800070b441c0038540c000e05610390703c1c4d100c02900d00704036011900c05000514a040351219400c1a943c814 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 459488767 1250 459487517 459487531
    0x1306050c0c040b030f0a06060e09030a080a0216082d040f0302060702010504090e0703051b0a21021207080705060f07030305181515030c01080417040b0a0302031e 71
    0x8034100d9401c03020840505000c040455151003803220200c80100c0c203011000030244500070002e00107180032940b40d25010010321000703a80e0414000c0c54102038111360328075885486c131440180c0d1640401c1500302c4031384003010080e25406011402e11020110b02c81c1d101ca01d00000c0709842102e81e82542807090510450203100701c88588140200010304000700030303014a52050400c141001d8035001c6000461302005414850f40e801800d0400a1120900c03001d1350310380c1c5030100345000141c0c0c9c0c00030a071104050720900d09843c1d46440c050155a05841e602c10410fa401021f110424104504c51550340318180512880f41c090000001028a401c50403240b21000b0301480c54280489030310706400a0100800d001403c8800703482e04c0e030005000340f0008403424100c3c55a40954100b0000c5075400200201032a4000e0f0b0204040c0c0a6030303a0080c100c150312070750000a003048140e280f039581881d4040c0c3e03485440547c40204039070480603010380185101d245030000382200c140c4a002a00b50100040d03c500d = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 459490017 1250 459488767 459488773
    0xf0603060c160515130b0f010f050d06020c06040305180108011d1f0603060306050a112502100c1e11011101330902040602070b03061f051306050c 64
    0x7601546a0a800303014600f070203141516081c0703003034405441c01c2001c02c40f0713a440d503801201000c008020b40824859084160341c5011541c544c100b4000c4441c0400178028948030b060024244003c000b550b4040368240618101500d80e982460b24014002c1d407c11040c41000c0400502005c40382c0d44145001c030b048462090784c4503e6018017910b045035a80c1e0243c00d00c00050507950b0011000f0054088000040c12603640010340a840e40c10070034200d403405403020a0590030f1034182e01000040ca025150341c0d0300a03420703c0140e40095010150691607510b002034100003896039500c51550052803a40089000d901c09003152749c1141700da814140469070009011143e011000c0f140ca510880c0c0201c000c501c0c4100010300800c0c07440c001e070001040c07008410440310800350349408449400c0030810013010000015820982030010194039144240034110103a80c010000984076600c00b0200300c0010001d041501c88480c040d0001807065001132061421035482a6002410a20550488810243c01ea020f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 459491267 1250 459490017 459490027
    0x130902010f0804020f09070206390a050417010501060f110a120905180601020715080604020306010306030f0f0516050a050910030c08031822150902040308030f0603060c 74
    0xa0314162400f41099070840d4440c00c00c0f440179121440b041d4011419600200704624100c1480c0180c541150b44940948500c40040d8160700c8000074001e00800010303488684a44640e03200b00c1d0707a801941d00007490403c100f111445c0c1500c042d4881e0b030603a2882d0b80c49401b0030750030800960700d44900151159881e4401c40995020502a00c0e1070b8440c01c24604d040c0d03000ca980d03140001c2e001078107100500000e141c0081440b2840d0b030108880c800500b04000002190040c140e000342c088130b4000c003014012900080040c1d0b05a1090b8000c0002d50782c0154000704032041818004804003480504903114440c0d61050319070384a1030510344007180c02c0100108100b500300028041c110001612039507103540b484001100050403207110300044d1400e90021906d4102c3c4414411208020542d00782c042c2c6c4e4510310726006070340204036035a8400c141d1200407501b40100c09249000e81200c0c0d01c0842c0c690b201080210800440f180211702403107140701120216150340c42095100c0e030040d5070113000303200d0402c1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 459492517 1250 459491267 459491297
    0x4180504030302040510020102040801051503062404020a03020c1522210c03081b04060c0f060c0e01170609010e040809212505040b03031e0913090201 66
    0x1129610a1103450003608240c0d40e100032030b00b61280c0b1040c1d540580d4011505000e051002d20a03ea4440000308205401440c0c010129454480c00340c1408007410340060b400d210071131040500a100701e40070b003003103544241d2110000c00035001220014514012000b80304a10072a041c000d901440442012120034441c0004140c5c04d000c81c9842110040c41207c220400e905001180c00354031381441c0c03a0516140c0203403038000c1030840d0040c911100c0c802c1d241c3d2407030724440700c0380d0a482c02c1d11044d040000f4502002d04040d0040301300c8400040034603080001c0e40c81016400740c02d02206c4942a01c5039000100000d00344810b0701c50446010f030300202403400412072000c0200c12980c201d0302a1414a140c521020041480104020001d42420410115148003003e0030044001c0b2104901c151240340c52170758010b40050541881503070301c25615000060030640d001e100312650004488411441c3c0c0489045507041500300f03c1d0390070b02c19507003800d860f200030803940201c85119505070f4407111a8a00d0ba4 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 459493767 1250 459492517 459492521
    0xa15030e06070e04090312020c0a0b07021216051e031c1103070f120f05060f040504050a080f0d021801020d051905160b090a0b090a1115090a060309170418 68
    0x1c019000c0020300303181c909001f00507100904d1030f90444400303024120300504007211487c20181c070314000c551000b010308081a044c0020b54064400401c031711174891841d4203242d0310b4104146901880701214441c4980c429800000600d40c900d0180ca11301c0104540a204074200d4500b140d060a5a40303080002541007881a001e180e120306660078000c6d5190319003000070b4100c0341c54600c02c041256540050101a241c0803010b44101c56044070203003c145480e0342d0359900c0d042c5c0c800340100311135000b01c0e18805448003c0705581340c0b20781580d003c540321400d8020303c0d841e503e540030485001d07000d00c1d41807070080e900c140115401d030a024503560740d5001252000b2245503000b00490308010014a10303240c0000c40c0760951a00983d81540146034034609410803141694029000c5580c5500103d140c0c2c000900015004140510031980c2000000780e0045500b828800c0904050b800030b00e00c10041031703440d01507220f03420050081d071150342c03411496900c0b03c859100da806003529101032924480380400e019 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 459495017 1250 459493767 459493781
    0x30a0b0303190c020a1424091207050a0b0c2104091b0311040807060c02180403020303090601080106060c061a0901090b18010b0909090c0a15030e06070e04 68
    0x581203a242034400007100b604128107100040c0001c81d128508815440e01007840d4010302848915050030309203aa0000380380850000c642000e02c2000000340d000c125441b0256003170240060141c001604070081c1e4075440760814002e240c03265420303100c01f04c0c032410340301c1c00e643e01c98031070900070007105410f0b6140c403081c940041d1520820035000c004c003080700d40003070041600c034440080c090ba51042c0383e00805000d0780c072a107400103c00c0b8010b220030006181c0006204007210004e00300b0401026450012500500e101c081c1112031501c81802c0c407081590000c000c51040d0411000c0c0c401e2662034a94031400d840980c820200010b01941644010a15950001c0e00c8641c0b40c4000134200e1403128046110038200340c1c440c0701215620413081805041044a620501c1c0c5007140c40700e06903040c0b011420850140700302960061107608002410720404000707102c1c0f200341c0109101d02043d51115a880c9075022000c03024002420040b101c0c03982640024542d02400300394070342d04004841d40302448001d06607 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 459496267 1250 459495017 459495019
    0x9031d0307031b080a0b27070522050408041a0406020c060c010905010c08061e0a1710020c0c040605010c0f0b09070e010b07021503070c061104090f0603030206060a0308030a0b 77
    0x698400140404003000704c0805e482c418120306a00386004000442020f0404541480400703491298601c94a0082075120aa40c2c00311681c10005031001840600002108407080c1940e1038481844207205807100540212061300100d582d4240c0300020044d0580124401c40000d41d01c01c4a944030585441000b50508110807000064482815210642591000c40d139020200d0005c2042c0300301d41c103043e66001100040d00d650381d044580400701140c0314050a1144804c4068081c59814540600340820108505e01c80015500c810040c4803c070307114466103003044d00c203510788040080c1e90b5004030908020740d604045020940c0b07101d5101c81c158140001c0030fa1701c290141210210b103d03030903000c015000e07040300540291104c421f403060200d07040b03881c44c841c4a051401c8c070400008a0f07210b06003850340c0794070400100382c08207a8031008c03003540681d07000465024107262010174500d220b0391242089900039404c4548946401060215503c1a4000500340840800009060703e01ea50401d15030860 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 459497517 1250 459496267 459496313
    0xc10050403350313030e0406031502030a0608060a060609170a02010c020f0a061107060302040e0711010b0402070311010b0418061a060403030f020c01020d17090a080d09031d030703 79
    0xc0240d8440550040361040c3c2100700c134440e448140f55000e000702010480541d410406281141c44006e406581841104125600000080c11848190700098000d00c0c098003200d10608050301c49070b000c0c101501617500025942d600004203003411101400d040d540303000103051001a140c00464041d0480d500c03c1c0d0300070140902c002c0240e1034200c0d03001d00030051555100c00c030100ba140c0585c2080303016842001018010b00c402c1c80380201c03160016402660034240000d001040c0e21259000d052820000c0340e2243c408500b1a0a06411203450303210400b81300700030081c410900c41000219000c0035010071003c644800350380d000990755405003000043c039036000c41c025501d090008401d94000e0300100e00041d01c002001e1800b07038041020107211031003400501050f52007510010600325110480a43c05240440403e4008009101d0140b240b42c220a0a6540d14580b040542c084d24180314101d00140102c0e4903c083c5151200c150b55040d440240035000c29451619403802440b901099400410 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 459498767 1250 459497517 459497603
    0x3140c03011506030e0307200a270e0a11120a06060b0a021e0d03020d09050a06020c061302060304150b030105071e0302030f0c071502160317191116050c10050403 71
    0x601e802c60b0720b9484411040c3c07003040c0e06080c110404164bc038201001080c40d8030103501000050482e13103458000038020380d503030300f510310031100018030f406078411002e0101442c0030400715003010039600521510029400b25400444200c04003042c414070641502e51725080000601e211a00c03c0d0002c140084010502280710009038584900700448814205d031159030020708880304503020b104140d40300442000c6848101e800d6004551180300080c00200102c1d6400001900c00325581e1110510f0403001d002088a0301e4001c5000c0c0446800c144a0419000c128801580c0103100307001312440780402b00703030080f200d4681d000d641d00c403500f1000c3c0c216241110b50f4810014481580b01400304400606090f0442c95410704020701910340d41114810710702c1c1e14808210318500702906003034040c030503064000340b42d10481c0866000d45c080c8686510300c4c400b20030100018494001400d085c2c582003111005042c040b0100d040d00e440c4202d01c0001d065a17884541120b4603408503040c1102e400407032a10134107078 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 459500017 1250 459498767 459498779
    0x1605070f0e092517010c0818030301180906092f0604120c08150604050f1303080601110a06050f0c04060c0b04080d060b0304030e0301110403140c03011506030e0307200a 74
    0x44c0c81500d0485060780d584c440024049610244043d00300c0c681d49602000054004c585649900c8140524142c1d80b0b407100460720302503400da02000120750004020400d45080381f800e0490211400c4040000044c441898201a00205038209205900038441842d16140c01058951400c0040b01503c04c05540c280001d600d003c00d20080b5490342c540300003010703685080d00401c1304540b000703844809105414001c009003150038511000615400d030a202c1925900d26004840503102c004280740c0c80d0150107000c00400c005034200c0b070700428552025a0b80c2e5520541c500c00c4030300a511072100080c041e000200301040c80c2210450704180108010b624000c80c4000a03004e860a541c048600c0a10010030082415400241460032800441c000d02c0743c18110a0542c0392805980800f40030300c001d004030780d031403c4400c0055020303a21029009007c3e072060340c549528200c01030320445010030308041100400460103c1117401c810b81c4030050704241c1060811880081d400d203502e994001e55140f40100306 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 459501267 1250 459500017 459500039
    0x100305070602030c010f0b012001091e022409060a110604210c1106160b1006080c03011d0c0903011e0b060f03010308030603031605070f0e0925 63
    0x1a0400b500110750b19040f51042c10f00311456084002c1074a40380141c8015a40c1e48460043c0100080e40181c904414101049a0040200344402170424840c528034100702d03442012030203145402107942c1441d40315034510164103a01002c0f02e43c00d202008210892040c40d004024110209081c540306240d01101030710301d0325014080e201079480e0702846103d9190a1242c2c40305007085003840c60100c41c201601e540d42e606068116a4040c81150086208421000c0c410581d0304220380256141c8030380d04003101082010541070245400240410b80002c10700c0110383c7c12030b8100c0f01d52108100d5520041c80c036015001c100903200075020b000c20001000513035824000c5400094409400403030320201e0f80c040c50304403140a0ad80b41e000382003e2180310001000f070001c2d681113a400210081e620359807000041d0035880307004e01802c4405500600d64049c41400904a41070722030802c1d103d00015194600c04402c64000c5070505001ea002d00750910f401100d00010001c444202d09412881a41310481411 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 459502517 1250 459501267 459501269
    0xc03050d090c090e1507031a090109150506041a160506070f0e0f1c06020405060409020d0b0409050309010c0516060e0a330c0c08010902120c031510030507 68
    0xc0070b000d50b500502200016120b00701e0380c074240d28010080750f08441c2000c005010010024414035540c1d0f050b10414210041400140e0000101748055941c3c44d41901c070001d11039030841c050701c84130a40303010441d03007052004c40b02510388480c140080600e00101c40c0302c1da5404890341d070500f02600c40c03074507000550070440207000c0d0446445d48001081564402000d04440c2000035108446030140c0742004e458a09880d42d0103070083c08a042d40080c0c5041c500e01920695010380c1d04100002030000d00480075601070400c4021842060007454000e0082100745c802c10760001e0820740041148605545c000c0c07041a421902c100180d030380401c602031980e00c052889600c5440400c00c0c000500c43c3e40e1030300d5511003010300001031895640e881ca01c2e4003100c1401890170020601c4682c1c4d604c050301d5500039801441c807564410b010281990301c808403e4041d049110303040340620381c01000482c15460128850210010180081103641414030b8400e0f131000000c0e168a501c002e810202001160b414001d0301c0c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 459503767 1250 459502517 459502523
    0x171b15030c091003050132030a050f01060501030b010e060c010f021903050108070b121b070609021e030606040c030b06070501050919080301050d0303020c0d0818120702010c03050d09 80
    0x3a15892030b0010311843c0d01400e0700203030401d4070307107070043c42041840403400301c21040c07406001031f94040c000c00d000c460420341da0000340d151044042c040d0030040d0000c1d90388007a2003010000c1c000b407640c41c00194141c03903841900602040350102e255131181000700280c20002c01d04800803ca0382022962401281c3c0443c40b0b0303141840b407840e9000c4005805000780e500400d0390b0b00090440b6840e00e02003400c00c1c00703000400d03805100d040340422100391114076030100d9a0130822413107980d4813044c5464030003042500400ca0180f6040780b007250461210750400820b6036000b4002d40510b0351000704200003407000078400740c18142c0da0485162244ca44901078580e00f881000000741074244201036034a096001e0344041269166038079a90700142c034407001e40f41100c81c1a62071124044c2c8a02c1c0960180c0210803078204a4480c0b140900403440d400440140103010751900ea040c0600c1c00c4071aa51540701552242180420800c90000154421100070f900d19010303260450528483c10500c000780c40014200b9 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 459505017 1250 459503767 459503791
    0x2a0a110d0c0303230f160f0b0901060f0504020711010305091203090a050118110d02060d02030a06091b020a11041b0f020d0e09060f011115090106171b1503 68
    0x340844c08044c14440316013449090f20103081910a4951101030321a40321403003c603600082c091010400d514410400c0c00398044405501460010801c900a0145200b806c80443c051880001c480c1010300c2190300943d0041c60035200c081a03d0010742c090640546112214070841e16180002c01000c005940610104c0c00035080700b0846081107403c2d51a400c1d00c0380c500102c51010100010040701242114600940386807200100c039000081240c015040d0305802c5500020411486030b8140d4000014bd5541f184108010015100d120f01c4a204555010025921040075000030580b0b020503e045900c0082c030203c0c50740c0001501510580c0000300d040b003c078269407001c00c0740350380500c0760940110440c0b60004d08450f081c0300080d10248054031050085014191059441c0d200f440800f0080f1101e404550300c1c612162a014500001101c2c041030039445c0c0840450070169003543d8808500c0d05030001e01401c1a50b8200140001070040c40c05c0c2d110070354074031500101110030051403142e0310728620 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 459506267 1250 459505017 459505037
    0x60708070b1e060909030d060b09040e12030a0504151a101107180207080a0512070302090a05011101240608090d0f050a05091c020915061b03130b2a0a110d0c0303 71
    0x2402f0540f1154a906681500300d00300c6465050ba848040d6540080b81000100320783e251070030248800c41c0c2050202540034204408018102d88000003003a6204042c1d440c4540c13040a02d50864a00b023100040c90302e0b580246c0360800c12000c074448556001128030340c0040c40d195440e40c036105d15600111070040801c070041074030340038100d10700c0b200d80e400001810203624054885000400542103805404e051001e03000040d00c0500b0258003030704641380010141079601544025510300780040d8401d1000047d4104005814001c0c0420103420110943c0c413045071030001c130304054078130390080104001001001c1c0414207081d681e02c081d0244c0401c1c044841c145a250b0780c018009507000042001c0b60184811b44140003c1c0c54540807105128180820755003070030030013181c1d5030941c4502c6040b5803050310712940114580640100038109000700c251b000342d1000d114041c3d8100c200000d8a500c40d0340e0001000b800c04a00107403910402000010484071484c489582d80d5092411640c00c203500260a03215 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 459507517 1250 459506267 459506269
    0x3070302070e090a1101030f0b090a02180117150102120304032d0918020408010203040818030f07030b060109080610050114070c17010b060708070b1e060909030d060b09 74
    0x405070010b209801501da580340756102c0c1d034500c00103141017504059031800442003603840d070f03031006000c890300602e44035081c10495640c0011350003270505000c601303c620720320700380319801881c48450300003a12107085030990795694243d0a0610b01070850781940106030103400b0065014004520480c801d845440e000301252000340fa43c050290101d00c52801d000741d0503080c1c80d030450002030803508085103811410001020040190040b6488207034158000b100f44800c000c0100d014103601e01c01140c403008545d407210201030f07075542440c8540140d40c00c10740c0140041104003001c41e901140c18102040015541c00650f807401404071501801245600410f002039a0300055040e08508036148403410991079498170715080c45148540040303141c07072200794185940c00390004800075800030b107420b4039014a400c00c00d00c5548403110031920075100b1000035241d03031406403100e082011107090300e902c00d54541040c092440405031a00140c2c4c8024401c42c03d0300398060090002070060642040d490b000d03468 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 459508767 1250 459507517 459507539
    0xc070605040803070b1008031204061107080403060b060f030a1d060c0f0c150112060b0402030c0a030c0c14030d0f11220305012a0f081807080307030207 67
    0x1811010411008000800c5032110020030740d2130107900b100c2c4200b01902c03080306941d1003100b90341c44240d170b602020410200500101e031105100313600825062100113018020001c0e00d1150342c4008194441c10703c01072011610b5035020301115030005e0191031034010145404c69691f0401c41c0c0568540303031035254610b8492a101d200d00c1c48054800024900f9040c50700040701240a441c036909000398000c078000c801c0c81420040b080c0a00000c804011080d40c448030030ba0f040c080c0300741050ba050f0b800d00035507540c3c5003028400c807482107008002540c20114003540c01c9004e01411400356041010580c03e41d0040303090384807200c1c10801107100070f55948404501c0007080d9102107402e482150b1911000303a03116015201201d400003c01d03403110440700052101441c1e00402c94001822540ca000b12010608040f044001d100300c0651804c0c1c02c20014601081b00d8400d1804524800181410003064110342d1403002d01241802080584002644175420207265420680b010741c0181c1c0084c404014079030042c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 459510017 1250 459508767 459508769
    0x3022a1b060a03090503040b0c01140112050a0f02010507020924011b0201181d01050f0f0f0609031203090303040b0907030b04120915090f0501030c090519051003020c07 74
    0x14250903600300038a00002050750081c4888002815200d0240c0410800d0520480c1c002d441c0c03d800c03007600c4024148584d40200301008004002c2e00520300041444054a04840d4450383d0000007000e580c00d0554400100310100e42c001c83c1070000034001c1400690754840210710443d184040c3c4031010354440d2200d0481c3c03041e02c94403030521084094403503064200300045d91400c0e4081c2040341d4140312400d8a0b9101c0e40e003942c000302000303200441024020303131003480d6903041f900c0481d040c00c0288202010070007020290362a0384c1c0c2c007441d4081300e00c44500b40200600b818540043c140d40606280352604402a03200b2a84001642c1000040108003d032040c0e003243c00249000040403a14110303911582c1800c1c0160001d0083c1640501c250200c51140c1485805084041130f10b0002014032907019001204038010907280714499034001c590340d44244a581002d4200b640c403040079070701c3c0105102d0a11180c01042a0703174000e410020a580e00c0d15000d0811502165a005a481500d185101d04003041 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 459511267 1250 459510017 459510043
    0xc0d030f0b01050903071203170f07020c090c0d0b0a0504020f040314010510030b06062701030c0e010516080c0102070c030c0909020f09180d031a0a051503040303022a 73
    0x90000307004d161400582c41050b540c142c20062005c1e021801c0a1303501070a03000f0603100b08104041004400500c04410700d0217540304c1d40840308140d2a010070401001c5085800c00c28080007409000c2507070796541c00640745003d0141801500a44500c04607007664804a680103d140b800101001000710b2000c0da907610b031200000070042c50918552110201c2c60303900c005807960b202140421142d5550000301c420900707a010402c8190100f201c580070500104010080c082850301c8910311006006107121550110140c4d0b070f40b464081fa00c00f486901d01c1e91030f502a14844028009d40031104400d20080c11202d00581c070309070000c0d2840c40e000c40d41e40c20b140c000800c3e060503d80e20a00584400d1800302e1100304c11501c9000302d070b4489240c000d02941250381d091052040e25012001250540e220800660020104401266030441801914603d600c54190014078085501d044d81c1c00b4000550b4226109140151503c1590000d5210201110340c03d04d020032200c003401d81291504010b03004031111 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 459512517 1250 459511267 459511277
    0x150301021b1603240e03030f01090e070312051b060a02031807080312040609050a080a090608060907140f03040515010e0609060f0307180c030501080a05060c0d020c0d030f0b01 77
    0x1c01c654403050200001441280704c800c5a00c030b40c07042e8044541001880b100c0f40c2044070f80386d1030080003d586a5900380b0070010258640040328600038004145507060341c0d040308824400e10742145040300c807607212440320300a0380b801108640e140d200c10702540f802456040d1001d0784904140c0c0e21000500b04c00021818154026070b002c0144038400300540e0178044842142e0850342e61503042c44000341240103030060541c02005003da00700301b4500003030301c40b000840c0e5449803440d4840b2402c1e02c2c030b582c080d910243d209980800044d109807081104010910f07401c1201400c2440d0008407441c25001a10101c030540c00c40101c03801d081c40c0c6140740c14010081e45d00c000381d141c1003101c04101c840c0341c0a0070080c016905680c880354141c0b810007900c4010046500050010401c1c41d1b6942c0040140c8281240080e040100000329548006600f84040d60410081c0c0403d40301c5030003402c030360351103642c0030300142d50240040032140c8014409001d03000034940f0b01090724a882c0d110741c82290384501c0300d10b041c0700d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 459513767 1250 459512517 459512519
    0xd0f0b09060a0e0105100302091906110109031403040f020d050601030b280c2106030501140603120d0b061c050c1602220603051c0c0f020405150301021b16 68
    0x5101490004c0c11a50f05850a086002000608402910520a0741c0750003d51004480300c400504e003994001302d50071546d410b0360410310114002e09942040a024001454112041c5040350042d0000c40e0850301c1007816003500025540801c201c000c018009507072a411440c010030a202d44007481950115000d0003541c3d031124140d0350b81a1000c0740452081c0c50f10760326018180220300561121007403040c1c00c44000118441d1000d45805414140422180c1d035003410024211000300140c510b0141c0c0c0c009019003140ea8544401c2c0320180c00c0044408445925024a0541c0362904002050348550811401504503007201011060b82c0019042114031101009000700c12000d144c3c003088490b5049410345000c400480b80030b810303030120790303124961a031400c107001041010001d03c002c60b00ca01d805102d0326032140b6844c01d40c1c6940111070080c00c944100b986000051803d07a00c07a507070009011840501414825021038226080100c0c15507802d040c620300300c0841d000030801d031143c100c1c914290380406 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 459515017 1250 459513767 459513779
    0x3010609060c0201030608010204080a05070504110406080c0d0c03020705010c180504020703020f071707082b031d060709081606030b01050d0f0504110618011101020d0f0b09060a 78
    0x4840e510404081042d8401c40e80210ba200b0340111000300b021800a40d12a9100d62106843d404a03c40846403882410800101030405000382011001e00c8040e0034102444c0000c00e850a000040642045940030040089100054800c20001d110301d0f40d40107880364221715200d401c550400302c4410501c4a101d03119800c0c1465848401e0513240107072805a1101d10525040e880c1081e0711000042c03a004107800891211207007004c0c9029800b00c40129201103556024458440f6003080c207a88074204030100b42c030911641804140c00011240c0303800510f0048407007402c014040840e541d81003079007018080c455155400301c4600041e0040e103000c3d010029110310718001020705031007401c2c00c5c5619100e40324444d80c0190261010300900181c14003410800110b20401010f007200d0031101040141d50075400c900f40042914175848c05401c0501c02e0119650054545442d002c00040441d07400b080034000d90011030069004c85400c2c00004201b00e20340c6800c00c070740350400420b218001e0305009030800035 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 459516267 1250 459515017 459515027
    0x5070f05031504111305040807020a0b040807120f0501020d0501081006082805030a050304050111180d0215120108100504050d11070504020a050a0807110a1b0302181506030106 77
    0x1c60750040304d11182c0c040000110302c07000300710321341000c0082c9010204000d00481c0d100602d0070341c1c030844002c9007442e1180c1d11810280117a00401c0e545a10410013804103981200d5000b2060b4028a0000091009075441c0e5007645d01c59450342001c651264010002010204181075815003454014032405007000361503a940c0c2d5048084c0415415030078840ca2201401d514040c000d1504030040d0b0f0b0342ca5440e4100501309510a0790200d91b41d620f80240c4003612080340054070b8840c1303024101e04200d01c2d40e41d000c0082c21121140e0030780c1d2140003125104113615815004020240c6852964550f962510b400e11381028000e42e407d0fa211800e01040100280f40422001811501810034071082c046803881c0925140840e042a0380007440041c840e0051070b0800090417070f01082e41c2d100107a5658001d4110340035240c51544410f5940324101103000283c256011140c98880103034801055583e03074000504800b0380c400780c64880c004040c1408400c07103c030109140c4488007510110f1865142c4800100 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 459517517 1250 459516267 459516271
    0x22a030301150302070c0b0a08040c12020d08030a0e0726070e1602120a09150f1e02100c09031e02031522120f0314070f110105010305070f050315 64
    0x200b0543d00140585c01c0102601003180606404254640c803a41105006007155606960907904c0300d22103840092511a40d007070a198596014100302040f41c0181d5440740c25030009480103071510346590888400140820000c00103101130b403801d030383c001e6098880004100c9616445000c2e600f1640d002c5c03058658403e0f5140c1c101c00038016450f8426166a412420441300c18a00003944a000a00c020059848140f6a041e1420950030310f42003000540d0640d0240c0d10450505c01080d4000000c148101c803d0707040aa08001500560f00d00080144c00203045485022100000c228000360500c10700c540b1102104014940301440b076030413921500040c1d0703681c1c4c0d03c00760030516007141c2001030b03003880003054101e02504081030303c01c0d1848240d24141104081025520b0001a440038030701c90030500c41d008e03100c0200c034418150412605c5000c2c080300c4000c484a00541840003604466813461400d200d464001d5004601130302e0250b041072140882c5004550025200f544280100034400b0b000d03e445175 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 459518767 1250 459517517 459517559
    0x112180b0a1d1b06040b0313140309030c0f010e12010204090b0a08030910050d18050606030a0f021e060406030209190518100f03051c0f080711030d022a030301 70
    0xc0140f101d52400100244907070780002e8144840401444005a850160140700900c103000040300fa1704501c92030350b520301036521115810391200c4a10152030030084607050443e10189080320054545201244421440d850450960784d400201008208001d00c24000d0880084444c030b901303c0d01c0c0c4041d4039507031700800e103a041c890440d00d1003040185008404440e4603044070502446401e4640c41e0790b02c2d103030015240640d00c50084c580040c00ca031402140c600b00740703580f00f075003ca6120119028485448004681e00341e040b440154241c240d235517014040c100804d120741e0003581e101d04100a200a0b514403221807810429080001e20807035613551000004001143c0080c81ca5503126041902c100e041d651103240800503c04d4044280b28020400c0ba0a02a2599030703201114081c000450b91104d41c100050002030ba4940401d49071842064120005100740046074103200103040701c0f808a9000481e00c1d0f41440c220382c4002441c03422212040c001d001d41c04060760031503141c0b4442c1c8400b868290099 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 459520017 1250 459518767 459518803
    0x9150304350310090f020901080f01050105041802040308030921071709030a06020d0b04051e180a052e0903020601210605010e010314010c0e0112180b0a1d 68
    0x10f1564070340b0070003407002808204002d000303250450000301c009501403d0442e0000f0302002c00201816281482e4074102e07101a500e1034074040c50185402c0314000b00841d07203000b1680800c00080864222009540580d42990140510b1078920303003412a03c020070180c003d07441506201c0e0b240840e1000050160006035012441d0355130146000003030400101c00c400a00441c4081005d0404a4182d0320400c0201d00a8130304003c16200c143c03180200c00c0440030740150b0454000300280000c0302003981540f83c11910030880744990f44950740c00b8100f00000745001081500714503500201445460364400503075071134404120000c1c0b5510002d440710780500800c0c0e0104d0300c01a640c142d50840c004d945640a4218108116958561241900c408000c6c841034a90804038008100301640c11300c500c40d010041c68569810455103140151464400d1100e000003803950b61103400003500201c851101408c0c418254451140707040e0b90000c0c100e03402e01c43c00d881d6892406420100c800e900160800d4003000c00301038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 459521267 1250 459520017 459520021
    0x515010314151603090f15061809021c23031818010623070b0f100b04150507050a060905010e0109030903020d02031c03020717190311091503043503 65
    0x110700400300b1400014141e90b00807540c84824905544841e040d06c0d005010785811146030910607013a07030440030700079602942003008801040080711a00084d00e204dd07586030320702c08070400100076402e0f02c408980001c0e0800100c007003111628240b60600e040d030031214503404910424800300b07074060501442091207100008161283e000340c40152540340c00451665031855503162a00701640c0986560b80700350b0b0204085401c000c001d5000d88161040840081e0030103162a03081c001100f858148501800410000e180c040380301800701c000c10a000303d07808103d411082ca030203801c43d410035502010030707413516800e00c2c00260322081d058101d940480d40810306056500003c0c1c1460a440720072401d0065103020003a500350950058500103018000504c007900c00300d0b80c0c01500d0700c60190041540e6002100c1c02000074000d0b03101c0c114641608041c07a06090b40715010030b101842210070f006070450302004000410040b18440d613040503c02c90203201e25000c0c0341e142c80b8840d0464410b50103544c00400 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 459522517 1250 459521267 459521273
    0x24050a0e19081b030606030c09070f0903060e0a15020405060f0c030c061006020c0102062205100c051309020f0301051309050106060c0312060f12051501031415160309 73
    0x10a50020304028010b40d0b101400f40b01c84000040081d0741002c3c000e00902c00040d5882c070303002c645020000809804150560341790034046074200300710800c000501107034050100219440d0b204103401540c220004000b81c10380c0e41800c0c4000002d11030021001383c010041404aa101c2100f50b58078407403c2c400090b11507140302c41090860158a403103003407078890002000300f03148400890078100e40b040e80039607400c2020f034801241c5404044a18410a01802c03903c503100ce10b4001070a01168041c0040d51000c5130b410031403205039801245500c00086000c1a403001c1c890281071200c00500c201541145011004048122107000510400e8810f200d840b00d50002003000b500000342d10b03544500204041d948551001d02410720402c1d00740e0000c1d60b05001c0d03020f07000d100d1082c0d0040e611550300c01281c045c5420b00c1c0080b00003001c6004c031070600507180f1100915000007812070107075204044078030030034803842d681c507181490001503070090410107410700040c442c0d51940300c8020300c6680380108821403181 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 459523767 1250 459522517 459522559
    0x6010504060e040617030910020d1e050d0603050102090f0a050d0f0218071d060702010c0809030708120309011407210623120a0809090411090124050a0e 67
    0x16214880f00000c0305e402c0070000c0404002010b252204403401100c2669a0740101d07030b65a9507654110118401108044040700e2109940840c5903c500d45586040d0480350100162007041e8012201a0340124564106103094030300003640340300c2954048030541c0303003c0000388458011000a03040004540b40b01c01503460303560200700c03901c8161907503c1160808450040206955140425141080700f4698040d887e01000725405540c05035650a0050304c10344801c8504e5000b8144d041c1e25201b94400090206400c2c0001100d4a405242e01d946a14005000b942519561005441e2002c040c1040101c2d40d60050f0a004503280c5081002c0401002c844400000b0401e64009192002e15034468001011440345501c5c5203c0c01030f40c0300581031450318180c51ba6030010031402000c10406100d404182e0a1032107c0c2c0342c0c0607000d19822900b1160150106020000c02e070000b0120005942c0100b8a030310402100508400481c6041c0385071262801000b08000b4074080a244102811840380b21004480 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 459525017 1250 459523767 459523769
    0x6060305070e01020a201c03090b070b060f0102010e0d03060f0609030c0608060411070f021e031506030a020901080f070b0a0804030c0507030501060b0c100507350a05190506010504060e0406 83
    0x290180e005611348140c407c0310400e417008102c0010340ca902010440040324415520082c0e4448d641c02d0741c5440b444104441c1302c1201c0c200504541d82ca000b24030305820100101d140c8024552000104903050001e85011105141c01c0081031204035201000021074000d00c2d00121405403030600c2080c4c031420000742c05072582c2810540c0034400450002c06008030b9220300f01d41c1900c21100c00702d00c1c4032888403601d0b000040b80c1525a06411990381c1c2000740d00300c0310a45500000040a8402440c900d90004a05070403e0300801c840c1d5001c504009404841008103e000d0301d2024069420058400c50003044140010070040c1042411004003003041003c2141d88041c2d907200009021051b00e0312084130f00381e0019000498544145510003420806030f00c22203000d001d0035070702e039860101210b1071014180005c00c2040b10500314200c0c4002c402985010307403401342c40640d4002c07649003444424084845c00301c5012490b0344d4500014040e5580e01722007154201c1e44d00b414a10300c030120324400503005001c5 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 459526267 1250 459525017 459525019
    0x11120909100e07030506010e04060b0a03110f0406020d1d0d140f1f0f0b030a03030905100203090109030e030123071b12020f160306150305010f06060305070e01020a20 73
    0x8402c1070000b09034158019034801c4900fa6150741719101e2410800041d54151320804214079010441600030364820b8110050021311044a50305e07000038a596030303d0591182c0d00520058000c400d4510009034040c0021090b814040b0080f54680042400a0083c2e404048000e00620580b041d040399400e082c0001c1d02c4071200942951080100c80c40d41c818810713099102800010302c1c04900d40c0a014083c801c404001b00040d00402c0744d4909641c0540007400109015682c40c4645861160344e8036080c00214031a204500010607190450315003d44009030b4842420700c664100006145031007918890f64000402010b070207181500ca410054030828503032480c100c4c01c98680d450140c140070408810b018450119401c882d054464088955101c900001c1800c0d00648003050801c0841c41c181c0110180305000540350300896900c1e50b4030780c01c40e10308845040186454003c01c01a2399014400d2070342c002d0090402015048403000000d44035a8803050081580c03071885414142241c2c100103404440308 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 459527517 1250 459526267 459526289
    0x3010f0b03041e0501140703090c0b07060b0603070507110609100e011107080313270e010f05040b150f030c01081302030d09210c0302090402150412031112090910 71
    0x160500078040c01c1b407000319114240180b8040b84650348a8800d51181d140c01040c00c04540e800d050103c0415440542c0a43d038090300c0d02020101e0b41d903580b000310300481040e25038030380e82c096519007907070002e5840300d60901c101818400c441040e10351041030703128445030b40390102e01026001c0041ea40012240d80d014407502c529031002c6070b003000010050400f08101008110744c00d60b941c40a0051000380000ca405a00b6898281d0b84100129007003440303050028030010078204524484078040306c3d4116019292a0814400d100c407040310f0450988415a0980e507104075010404003007565030000d0315a99040000040019051070b00200c04100c0d041d40c001d0030340c0c0490710141c1e0020002c05c158020394520310380c202111000e0120002400055a90015680c0c41840c956000c001006100134026a00305103080c0e820010500d80c00014006070035a1140d0303948940f0300d070a0042c00b134139010090500951001c50b041f543d6100000a450408800300c0c1c58050598400307034040d094018036485a070100b0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 459528767 1250 459527517 459527573
    0xc160b07030e0105220305130806150112090512091807030203042a0317090406060f030c1805120f0a030504090b0f01120b062203020301060b03010f0b0304 68
    0x10354550007244400c0081002400b85071982840c051071458440c1c0305c000820b403104001000a8080d0b00544954403154001d00d801030f030b44400580c1090300440e030000b0b024071644020700c40342d07030002155040c005c0c00b076004202c1851541e9889654080103210440d4800c0302144000c003a584018134060050a860112049070522950141c042d400907241258514002e0036901460085541d200e10113046106a00c8041803460300c13842d0740412070020302080034004000b0346c020f0f0744a50145030000c0c40159070b9011554202c100c0241200d810704452410041d0000b1140c00a1410351a07400640d00102c500418502d4020007a51801610300c0b01c000490055200600506030000050011210260410f1120070010307030400440311210100c05001c940c3c022090a0a9803103035101021014000d00941d2400c40000341e44c00d0340f1550784103c51f801e60340242040c41141000e0145000611002c81800c1c151f506149400088551038002c002c1105000300005003070000c1d804070740c1c0440f407518407907408007 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 459530017 1250 459528767 459528781
    0x3090a15020702012c1509031603050f0708031c0b0d030905040c110303131e15110403020a060e040f0f020705070641031e01090908030c160b 62
    0x82d40050700183c1c04180ca844001a144404600c01e07003d40360581aa214269a1801080310080c50f101c120460030405000c105180e450401c11021040f4460410048440c0385290040c504054004141403542003200c0402680030300005883c0451000c1d0011146521034402c0c0c0c10060450440c6180d1002d02d000c010014581c005845000380c5406503002c0c4000450340000f510020905c00054510f50b10810001c0c00880721200403600152140c00d00300000c15904001c0342c20800c1c081401d81c1c0c2c0b803c1c0f0560301c0151980700d22411850750a0000864140782c956000201c03640398500c281024071410b254000a80d681e954042156402010400c00c5042407880e00003000b5041034508072030781c0c0b0a035200442d2203401925440744041e48042e1f030780c11000502c07210801c0c11104050582601c0c04010082c0300800303081000d1481008200707042412600c120048842d00d020680c48201040d241c4012100070a4815013265480701401d48800e13134602c6d034020034440fa0117500d42c014000b000140207201607 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 459531267 1250 459530017 459530021
    0x603031e0d1b081605190e301b0307030f0503040f151b0c05060a09080a030302070317040317060f0406080303011802040b0409180b041109010617070503090a15 70
    0x2a03444400d01c80700b09003000d10142c980744602c6d9101c0704001c00f0030840400d0036104088480c1c0f0080d0150044aa401642014010300c2c40d101a01c1800b00051440c48408900e0421551400e0312004524220110f20040820780b505068000602420001c7c5190002c3c06001c1044400402c04003000613161661841c820b0a004400d040340000246a803160f00b86481d110954008041d42000802840501c3c0c01c08021455011081a10a001002c000010340041c00d00511959a0294070007681e40d0406286c01000c0c4003509007102102c1c01000180004030394411b664104040515608400310b840f5500020340010401c0c001941c01400c01034003190050303000c0003450403138211543c101491740c0c05130010402d0380a0781c022114035003000d00c010025121250002c0c6600440d9002442501244c0e07214000001800ca6080d596010700704610021070400b0302d03086004000314600015911401c10a40303142075400b500c2502041408000b1581c1200180704941b002c0b54000c0e0103400c0e240240502c980 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 459532374 1107 459531267 459531271
    0x80702010e0c190302040501030606080606220f0605060d0f061403100504020f09041a060409110409080c0a1103070f030302120a050702040f050901050603031e0d1b08 73
    0x10158031b503407250f240a0741c096400812400d0030100e00c641b40842c007410740e5000361241188040300c1d01d0180c40c3c914501c41c442038042640c41202027004086d0906401103503019800003550b041c00c0c615503001604440e0640d03070510025598140384804814003030140c0381c02d80c200050b280e2600b0f07174543c0080d81c0248014000d02c03046540c0707408140d0b410030450b02112000307410f002c5040d6101c2c1c610007140d8080e800b20360500801c41159501c04040704801390080c0038645500c4c040341086001d41c1900c8941c03031000100d0741c0701c103c0c0d070a21071702510004101c20301070f0152100100381c09010150a42c02e0342d170950003c0c40340f0790328048050f2041d80030f418050704102040c0b04142c0180d4580c00381d0b09150100740350225039803c241c144d0900b180d00140103207200c0d50040250b1500543c0200706d0b0181c0da410301507015100e0103200200c00207015144d08003203440140050008215400c003100754 = true := by decide +kernel

theorem cover : BRFrame.Cov 459352517 459532374 := by
  have h0 := BRFrame.cov_init 459352517
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 459352517 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 459352517 ≤ n) (h2 : n < 459532374) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
