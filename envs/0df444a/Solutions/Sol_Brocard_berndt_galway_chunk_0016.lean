-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0016
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:22:40.162918+00:00
-- url     : https://prove2.me/submissions/cfd869b3-2b8e-4bc8-b1df-9aa32238ec0f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 2697849 ≤ n < 2877705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 2699099 1250 2697849 2697853
    0x90504031211040f060809061b0703030b0604050603090706030c0302030106080114010c05010f0c0909050405061b0f0d05090c010206040b010603090302010b190302010908070b030604020304030201090b09010c0908 93
    0x24000025070200a4651000c0c41180224581e81c4449454900348116070006000080c440030025038982c100c00c3c020701c40d51403142600c5003039940201c0c04048050340b59103603c686000f0040d110000e8020351100561080c0a000241403940f280c011611a50094034000701e070358405401000380c140d01d401040080d01142c5020740c2594035200d00030f40644018083c004603000000d1240705240d125941160503550098024130a021804050f100204041051200003440d0143d011072041c015020f0a80100e80c03080081c02241d44241031540302222008005101c2c0004001208e20f40a54401078506200391100008507800d0951920f0303c0c14034510401410740d0005420800412951610b40d0b0464405040200c1c0300741c1d2a03d400ca00410a40314031b41c0c1d1149480500c1052a0707044440300098074400e0300d510441030713101c0000540d41c940521441c600150108006401400d01d40c003c0c54216104e80000308900d0031680e94401055403c8a980e0344a81d5a47d5418880030743c094a02c000034008200 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 2700349 1250 2699099 2699101
    0x40e010605130302131404030801050a050306040b010603050402060f070c0504050a14040809010e120d020607020f0606010e01050c010507030b040f09030e0405040c03020d05030301060801060e0105092b060b03070905 94
    0x7209803002e210a03c80a4032600b5520f0b07401400484540040c0e4904079412800c0300940b41601c3d0250000e01d0a024035402900f0f02940800d450500041850240303410002e144950f13844c090f0100c016101c0284101d07002030781440b68440c032030706182c00303042c5451083c08103c000c14140001e2004850f4010514180107007811210124501070400340f40c2c100d07401c0070071076039680940001a02c14800c40e8041a810140301280d0b800794100c0411440e400c83c00d00d600713565060b00c80b1102244c1d9041d86041c2174403141c0002020035000d6020361241e0081c2c103018100786082c004e041e500c140c01c4500032652007001c607848010b0070720130780350030711a0014030036000c1c5003000019010b03280202609003030301489020b941d0703a030301090500c0081c140c02402140c0c000c290b403174440303820305e809a00e9410038454030b0049522040045050f60003400001001001a981c507400c00c040300040014143c0b11007800708840c2001e47c92545000100c2211500d40c9005200c08200409202c0038189040c0480d4407001020f480e06c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 2701599 1250 2700349 2700367
    0xc03020f0702010315120506061002060103051902040609020a0302031b0309030d110403020429010905061909090e01020403020306010f060c0807031e0c03020105090a02090a020a02030903070902040e010605 90
    0x14007562600c507020310300020000c0305041020020081500544000b00c440b0300701e00100a40060050700c0f442043c0d60002c040380038098103a0380e801c000c3c04018145e0f003000714500030400000001d0380c0e0290004001040041d5294440400c0382c0c00041504000381e0000104104000c20382032071a803058800d11003a09d90b2038454801130301c900400701446036640d200c0c410540c92034001d000381da01468000300104841034160b11941c0042e900c0344540c0a641c190403680d04065030140400d0421140f000e00090b1500840062501803440100314000522500e4440803030400010711450b0044149000010307546e6055004042c80d10300168032200079540d00210620100764406c51101d58143c0c0100c040b07450b9040340c5000d480015036000242c100100710700c41c009550758810307090100c4c54003a8000b04280c0e150400b006849091a110207500311140f1400320300d00784020740c0200301003190303413060702d003030010b0380b0b00203810701c14142d10240c901900800e052001e25038840d031003030040141d81411460301d6529 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 2702849 1250 2701599 2701627
    0x2070b09010e030708070603020702090a0507020304121a150a0902091c170a030204180207050a02060c0703050f0307050106050108040f080901050d0207050a03030b011d19080708030408010c0302 85
    0x103600504000141030b07190040c0e102000490050000d00054848543c5c50703080060081d0000302e000d070b01c59074040010560100c068410680600c040d54040c40c901410a2080601d8050040c0d041b00d00084000000584800c1c6030b1074203004031a4041c00b100e0a028150800c03102d1041030f00407003d210b00c100301c0c5110540da0400c101406200381000075a800f101d03401c00c4a0030b216842e4520160180005211100c40d61542c01001915141100700c3c80054044407410100e010b414401030456204501403409450080c0103000c0c0040c13001d040740c46094580da2100e0030000031100e0003406174000725200040100a00490001d050280381c07250390f519140d1108040a82442c1001d801e640f00011010b50a03403094046403030104185030295138801c1e0038074001c1d035590400304060f800030349000350030701c171540c810411040411041d11480c2515001c2c00304100f04000d032112091440f440d07801c1c00181580d070a0004cd401045a44050341c0c072180790084040c250340100d03240004051040204603a89500 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 2704099 1250 2702849 2702857
    0x302100e010801031209030803011202031006060509010e0f0a0b0309010b030d0c030302070809040203010303050d1b0c060e03040305010e0d030c021501091a03010e0c011211090108090109080d0b1002070b 89
    0x15044600c0c1750101c0c1c000da070141c8458101800380400007002142d1a01c0c400c0e20f20700d80b180f00b44c0c2269582d01c807050b070480841d41d0a002d0320001600800162179a50f12407082c0d07500b00c40c00188400491030410300041d801c5121940040300d80d400200802a11030b1082c86014000d107825406002c03038603400c0c0d0004001074401580107061643c04030301b8000f441117007800c2c1e40f04218042d10440d03507561a802d01601940105561042e06820506000012400344146100040860701e8803c0a082c0d2590741d01c000d480c444a031071509110034040080803903000d0040e0344502c40c0d840301411b039840c0c20720743c01029030305402012000e5600407001c82c0c1da0f00903441e2540c2e045888800001690f05c0307501d411003007030520b07411400d039241d0b091030907200220601040d180c00414003600c0b50a20000240b1140d0180c0304180d4034094600c400380003c00c500d5016030001d0f80c0c006001d100000f040c03d80b81d65070b808660042451400b03030503903440c025049410301600780d04083d6004d00090001500e841c1281312184a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 2705349 1250 2704099 2704103
    0x30f0309090a0209041103010314071503020c010906020301030602031006020303010503030702010302090102010e0d03020307020c0901080304030b040302101b08060607020307051909020d020c01050c0418020304030c12090302100e01080103 104
    0xc01000050603002c80354141c1c1e4130920028014000c01c40d040707a1040245d0020b0000b03460340e24600428141c101ea002501c1c408651001003140d403031485920041d0002e4009025039181d40d501c3d080174500150f011720056000c1d5124540041e10307414485001c0d1030001c482d40003101994070400061003103941c000240d440850342460050703550581900101e000d0600071088103098880e14000392010b580603006113100301069030032600407154040800c0080f2070280719100241d04108028008502c0031000c466205009004541c0d4401c114240300003200d076240d210064212080641482641c3d03c200019001101115014104212038002a440d12742c1ba00c645441034260481e501b0560fa800080c5000600d04108110345949000300180c0107540703c82510541546018005094400c0b842c0c20f6506403600590342c00840911070401074004d5201901c150f0901170050b04000000c0c9441c8030481d80385020759144003407a0328610502c201424251612002c0c485500403000c101c2e42d00110082c112a = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 2706599 1250 2705349 2705359
    0x30708040e04080702100c0b13030504030b18030703020a050d080f13020102070510030204050306010609060c060203070306030c140306010902030114090a18030c0b0601020318040b01030605130c030b030f0309 91
    0x14482c1d140800c2c1e24404c0700e030025002180c40d203d040040b60407204140e0001e001d0751340081685c0d1001400080a421a400100400c00134801400860001c43c02e01390700414003501c80b80c000c40582d5515140da000b082d0101d0050b0301c10001402004014400c1030b00400090a1a2a041c1001841c100d40c081c8024480b480444c03400200c042560310030400d02004001c00307483c20240c8000140010080c1d4040d0003214028840d0381d00014403980300e03004080458500d980c920142440c0d96603000c1c00b80d88007420410405849101c0172001c01c0c203040b100ea0051150a209450058200c5c080c18100001684580481c61040c00100050b04401210414444084a50017201c0e626044090014103100d4500c4000014110b10081019040780a0740e0180c2d000702007202240d0b4408004a0340c4c4e2007418070920040a2895890005003042e40200d003c0e40d505040c0800c840da260380210380080c1d821b000040d0141c0d165202800b9258040c810381444030000d03000742000e5068031a505540713100781c1201c1c030700407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 2707849 1250 2706599 2706601
    0x60f07030201140109060905010e0402150310050306010f090f05010506090111030d0204030804030209010b070519050f0a1101090504020403080405010f0908010204030c0321080c0903031c0204090b0102030708040e 93
    0x3610039440764500642c95540080c0e5035071107100c0d50005140c1800b800d100b141c507045c004035070711102c14511407059500400d1180b24416504083c050340d00054215000151401000310b05986c090001a000e0300e0790b00d0540780300c81c0c80d0200c7c0d007003a9110010b21084251a101c01401561a030304101c1e80c03421000ccc2019480e00007003045041c510310640076071103815403001c100403080115000041c801c0702c0c000c03038010300c6076609c1c1c1d80000590312074421f0007442a4881f01c0c5048180e242c0e014500031032801030b000d03501d080c1504181982030a1580c10101e61142c02d0001040c640d41c2c00844c407801610040c2c404500349401d650fa2402a403199003e0141401000c50905415500c124040710150403201c0007991903980d00e1414900a02d9103001c2110382c00b4010102c0400d42080640011800c001c0f41d03105403c0e41c58002c200e116950001014070b0b0036001c10000010001010030300f50910b54903180e00140d5941c038000030300341120a24216107045400c2080581c02251400090310151200c6010f42d441e6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 2709099 1250 2707849 2707853
    0x10c02011e0509030613020a0815130606050904030206010302041107080d05060301060305030705060403080c03040506060d03050c0706080f0a020703080106030c02010204030b04060c030b190b0309210406030f0506060f07 96
    0x42401502c11035130b454403c00301089900004400c1708641c4074400e840a04c9601d48601b811900c906500b0a10040c2c0041c690001d81200c88015940455034002c410005403680c4070741c0800d0782843e0444081d4003581c0504010411814a441800106410f0603102c1f410b052050345c50f05410b120303001c0d4843e1115142d80104140d03076401e620000c02540d001c400c484e0341d5042032400540380c4104035015400b0886400000e0108460f0204803841168484050031007030b5607200810000211081065040110501001c203402008000490140c51251a800440d1808040e0502e0740040100303400d24050041c0400300000c0d400c855141d0642d082410007281c00c0d207d000c0102d0081c0900e0b0300203401004c0b100140024400343e64802d0210080c02c2c6d50504c22452201b081c083e440200c034001e910f40c02c41c2440c0820024905001443d0044d14440555103070310310050402c1804180e190f9004c0741c5840c00241000240d40610401d01d03041d00045040c0943e250035030003d802800f801083d195082400980f28007 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 2710349 1250 2709099 2709107
    0x2010804050c09040507080c0411070201050d110309030c0c0d020102280804060503060909010c020303070e010507021003020408100501030203071a0d05010623030f011202030a0506010303020a11010c02011e 90
    0xa0b00d540602040414602414800d69a42c1c2c00d2180c0c83d61030092803604c2010b07003030500a41010014a8030901c2c40d015040d03004440f590703ca2031800d80d0041d6100084114030384990000c50050355003000450321803042140e0139040404003004944101590920100107076004140c03060300002801529410465102503502004660071005118400004001c42d10075000405140600001e035508040b80d03440c00200f40c01c856540da000c0001d42e20a000050310141300f280005011003040c5442420300351550b012410790940c200784000880d40109003440747c3d000c1085030798440c40070b4120034032039545940c0103e0b440c0d008901480080c601c004441400c00b0031590200c9400501c0c600f0f04100e01e40c0e503110010481c01000414148905070150000240e16050046d070f4050742108901d000e00742d2804000b1011200e040004907094002c16428002164091080c03a001b1802500a00111402460b15540c803c0010741d90034140080c026040f00541da01128078805103074103210341d104080714110196 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 2711599 1250 2710349 2710363
    0x2070605130b09130903090e090312010b030703060b07060501030201141903090816110a050103020a05040b0a0e03030703020102030601090b03070804150209120c03060108070e1909060c1e0201020301120201080405 93
    0x42025410500d1704810140d0000b4101d0031982c26401c1d05a40340c41320039016489200b002280d58555179020010300c01c4804000c02075410024a0600003849951441e505486402104041c1d0750980d80700700400c04c0d03581100c00300a00c0c0c1101001c5e94a000b4841208160b90500c42d0254010542c2d0748041e01c08020785503003102d4661042030140c000c04020351502d249501c41c0000494002d0f03000d28400505035001c0c0c02500c0807803050b5100c19040038280390300c60310103420000c4201c0c100002002c0549030380c1c42c18030043c60035a00a034000340c4d40707140500c0094284140303640b0000049404008000b620341c2c0c030136000c0e50403a07070140c42c492058421001e02c0005e801001d4006610051011712244c4980f000695003000e1030302030b800c0d1078042c1c1c1d8a20740c1988405451007680301680c445400200405986c8505202c4541c117004000356071702550b11103008552070000408003260541840010784a2a002900442c0324a84000e5203190f05200455844200340c00009050150713000c0400d04101c400c0c4488 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 2712849 1250 2711599 2711629
    0xf050c040e06150111070302090c040306020c0d020c0303040302060d0510030602040f050102011104060c030f0201060305150103060e01060f0605090303090402030a021201090b0d030f050c0a03030c02070605130b09 93
    0x1404001024016142c94203402d40301c1015031071405103400351550040700c2c000d50a04ca502d0251549500e10307002c0c0611003a000341003141c00c80b01004048001002480a0701010344070030020324800c198000064584078032002801e101307900c140401c200583c0d0340000c40d40c1580740360743c0203d4281c41e103c81c0300d640c071141d070b800042c141800418081400e81d202002c10b002c91758240d00900c500101203000003554032881c050f6000041e1100c02c100e0200b8000c403800b440b42e00070b51000007443c5640e0f407981418010350315404901e51122074010020702075035018880035607030002d000b0000f842c540040c0d2011282503102d00710500102003001d0b49aa68203006a036601d15025106564919145800cac07002513203c510241d0890100344e0000c20f2034281842901d11032100689521202541ca0728281d80d040082e219550030018200204450100140f260302540c0b8480c0d100421402d41c42c0c800a410039038a500024100b02045c0205032402c00d01c15468801c40c4c90350440756550b00c12280114001d03803205801 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 2714099 1250 2712849 2712851
    0x319020d0f0606020607090501030501080604030309020102190501091202010e1f02070c030803010f0807060c06050c040312020d02060a0b0a12020402040305030403080711060a0c030810050a030507080708010c020a0f050c04 97
    0x6443e503000714013640b0034119580e4001005803924015801c030b44080c0221192688034400050000c1d010b40d00c8000610b005004440340c1160020303005880c40400442180c0381d0751541c105800f03700a07448040b140300c14030700080c050010413640d240d0fa680710180010b210b10810240b07412104500343e0407110f0031a0000d081d11a03031a1a402c05011980c002c1c418009401d51004000440d5000421500c090f03039050b030b1355004003920a403513403005031501400075941100104000030014202c0044006507001c10b030007408403c1175007030010781042d90003052060400d0400032060b000355141103215051fa02d5000c074542240c04103002160003809a038000615074030001801005106020000c0c105082c8100c5e41068500010424040d00d8000c01e402040400c00c0b02030f8481c0080d00031404680c2c001c1c49601c550503e180d60703200007464421303694010342d500c0d0800700c02030050001c14030814020f04444070007407100e40980381d0020360b58421050050500401c2222030f0007044024802ca04030b911001300 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 2715349 1250 2714099 2714111
    0x21302070804080c0102010603080d02030a0b041802040b04200c0a0503031003120c030c0308040f02030303010902180906010504060c030203090d031d030c0f060c1504050303010305070b0319020d0f 86
    0x191050041c2c2c4603006542e854460002c0c0310780e4661050058a05a980c0440102d00301480182850041c0d00007502049103a501c2d1840500d0301c0e2a14440ea05007004148024100010315005000480f100b5060060055050a45042c403541c5002c141c800c00c84880d0038029135841d0228286418a10340108c020600c0c0000420b0040e00c0c0c00209141040e06d001d6000ca80341d40e00419003c1e600c0e80e40407d80140807807019101c000100340110403060740903029140c20044208980e0000341958000d0b0441440154040344403214a0030000e0003403804182074807010414203007040040c0540c0220b12502c01000200780b2001d0805100f44182c9201d15005401c0c6079140045180180060900756091600d800300795443c00c11915000501d180010350240c12111090544014061903602c03030340d1917103503074802d44c0c0e242103d031380511341c44901c640c2c080c0c00650b45a50440c42c0090412f520760f4401000e181043c0f09000b44a030607050700c0c90494a14401c01a03494200e141c000014043c0c0e5003011402504d001 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 2716599 1250 2715349 2715353
    0x904180506061201090b0f040302010e0d0216080304050a0509040206070b070c020114130603110f070b0105090108070311010302130803130612090f020607020105040e0a020705010c03020306060901080402130207 92
    0x4201e0b00074001160000d02840c2401c814500f00c031801c04e0f01030168105813020031626066655407982080c0680300200c0c0900b403d044040c6080103510350400141d2049084c070020340242c1c5020070140c02d10001030740c035207850304001400b910b000340100f5201c0c200303ca000c182156903010442d2241076208060203101c1c9007011003e01000c55808c0103a0115050560749011603515070200c03503001c0c502005080300181018800c8008003e00000a100308808202003034080d40c03403d0240051511408009100c0e60401090119880703040c0c0c0281800d0303000c41018000a0110551200342d94401e10f801a11401c002241d18004025503001c00340074000055204035407004444188151145274071000501e0810076181011181d017030300060700d031020303980c5910300600d0880c4c0140003140c0145005410140ca401d45c0100405054800e140159400140801040800c0c052440c030058241401c5003076103051008588148074040e1101e0402c504000000c0441d65690010701001402070421503c4031114 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 2717849 1250 2716599 2716603
    0x200409020904110301050f040f0b09010e0f01060503070806040302070b09061207030905010510050a06030e01021201080304090606020705010503010b09010903120e01020705090c07031b02030a060b040506040603020901050609041805 101
    0x3c2444a000e54203043c0081c40b1003906d000c1c2d05010b29402042402e0b04411a02c071400e903881c0103018003901e5501c0b2280003010400802112040101070000065981c0c60701c020140360070074503800701041e504408200b00c00309401044503000c60311082c400c6651440400e0000311203228440f03280005904040c180311503568141d00501d412403081c00200030985038032080458070b441c14402c4036880354100701c0a00c070f080c1c0b20b5000414002d1410b00050b0900080e207a4030303000000241c02c228215880450700f002101e04070f0154000070440b80c00504484c1d030410700020a240300501850841c41030018a14106910032511100116007200c074506a403e1030030f0f002080c103036681004038012722800f400440d81c0d03d49040d00c1741c080e620140031180303019032540e016a910910f9020701011000c0124010300580c40510074680c5d0148554800581c00f1240da0030042114009024140118a07144007840144c440c00c1256040d01c03400c0701c0c1c07192035901000004015040c2080d01c00e24454109c0c13200801c1003c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 2719099 1250 2717849 2717873
    0x5010902030f1308090409050102040504050c03060102070603050105030303060d0f0c031103010c0908060f0601020a050706021006060c020a0306020f04050a030602040306050601020a050304050d020105090301021201090c0c200409020904 103
    0x340c102c0c1e980c055114884004580c0c1c00d1480007900030901045006100c2c5001d074081c03141144a040054182951200018201c40c1e041702c40e4020450000104506503a0500281c4050601803d04000355410940465a00c0c0402848a402210070000c00d005006e100c005990340581d0164519078899101e14001c8507625014541c940250f00f0320072092038250141802d0300a6804540040200d13503502094500c82000c003401d494154003d010900000c501d0078001070000d0161034008041d00c0c8040400602222516070010080182614201c0c0041e600c02e43c800b401c0301e801030405a183c0680701d203400c1182c42103900140d800340d020200003040104503009041101c0c003649041059507212401640c603110450f000400356002080184507500e003041c2802801d60040c07400a007054070f002d001c642203a0083c0e41c3c186200350104010440c8a605006101441841c3d292001c5191400c1d940d500c030704010405058840d460114003072500792100d0303014080464006220741d409090a007450303a10040 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 2720349 1250 2719099 2719111
    0xf0c02010b0f040902010c020904021503010311010f0806091f090216050f0307240b040e030310050f01020d030f090804030b01030303050a02030606070303050405011104090c080915060607030908010501090203 91
    0xb500c0102c4100c0c5010710403020344540603120b00c80860699400c0080b0440c00030800c91f4800c00d0b01c030300c22800781500fa001e0750103180b2031814103406000c100c0014100103c903a54000c2001000ea04203c02c54590504091b04003102d0114010065a84217140254000300d03003003042c1e998404540d142c8030706800c600014905001d2410784001c0401c3c02182a1248501e51015220b03000c008103251800e42030016107810070011420010340c1c02e845400140503110700c1d41201a80368400b105000d0081d51240c00c24000b4182114180c0661100a0004c1d441e0040c808208050581c0c5100030081700030b02d5049a41261f40c4542c003265074540380d180107101d101081c00142c00092801001400c0407180b0700c00c0360b0107980c1c010f01d1a41030600c695001c0380644001442156955203448244241c4100d10020f440a0b06040e000460340644a080061401d280144240041d5000b0106040e440d20601031a581010040d40c0e0507980d240342342401c3c1e50811103644010100e601c0d02c0000140d012041c0d0213140511 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 2721599 1250 2720349 2720359
    0x14030a0f1a150a020a082101030303050103060f1a010518060a020d020d020a03020304030215070b0405030406030e120901030510030b07050415050703020d05031807030507080613051c030f0c02010b 86
    0x80340e0318a1640703a600502c3c00450160b403012104102044a81d00948114000c242d030290300542020368942007144203900860110351140018003c200980c010044a451785d40002c0100e5114010fa1101155030b44040302d061120000b641c104803092010a1092507502034103083d038034044903000030350b141203030524900140522000200540d1010801c0c180701500741c1d00840c105400e40c0c00304141b0000501020103845020024100041c118542e0b26220b0341c0160081c41c0c81d14546040502a1400d485031004550042d101d4005030751100700569411b02c4080c42d00090740d560b500c101c2c46945030183c0002d8040703a000010400c6060313100d03001784141d03580c075510031041a081103420745250180000050151308994410442e01e481140510ba10071f40010f40384014540364041c1c1c50a080c03040c0c0054a09420449061140300e6041280942042c041d5040c180184181d4036040c0c1c550b101d00100303002ca24580e40c0d05420f0f0354400c2d0030810020404003010020310048900c013900070065a500a8015 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 2722849 1250 2721599 2721619
    0xb0402010809060f0105130b130f0b0a0e0f040303110f03010609060509060a0305070e120c04050606090d080f0f0a020109050607031b11070b0301030b07030506030a0314030a0f1a 78
    0x14071004200c0d64000c4c4545200c1d8002d59003440c2c04c0050b8401244502c608860780c60081c402d0590312044004c3c01d0003000100061444851009107040d1440502a5400398002000412a41861101066020706507503c94022031f00d4500e8124040c00c540f80101302c1d0b112000ca10f01c224104a407004604817005900c40c5554103684081c02d6078140121000d49038070140c20f01c80388500340c1c005e410441d400ba0b850f00c0c103040c0101d4080009028141d007021a140301364400c80c0c000760f05040074468103411280403a16141020290341c0001c1c02440c40c040001d01d0410301103601c0c03004580c1c09090310f40017949042c081c0e0315035281c824002c1c000d00300031a050b02c0c02d106400204018602038460000380341010301c0752254100c090380302500c2050480346201340c24401c00c00b00055044003100958003952140d0a11441800c20a20050990300d02034540b81c0300390001034036600040c3d00900000c08140c2403603000d90320703545c408180710010405400381034034860410a05d003500f8600c00c080c0501e81c180440e540c0c050 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 2724099 1250 2722849 2722861
    0xf01050f0603040308090c0a0902070506010b0301080c0105070804050405010b030601080717070e0a0503010501030b090f0d05030f04030c050105010305030c16030209070507080403050f0313060503040f02060903030403020406030b04020108 104
    0x6036500c00c045150021010000710340424401d910711688103505404881f0807050760700c0401d0b10b8403401c2d440300c0765107035000c91000200441488460f00421012841909550501110785c0d214040182058107100b00002e110003005281005e031002404c00602c1082290b07925000a141a8412540e150005031207800080780503000704d504d0b00b0f52132005259000ca50f91050301c01c0d102e15147e17125041d408006454001215502405500e002e035104101c030002c00e0a0507203c4515010500f00022020340003c00c100303c0959005090341e81c0044070f204092080d49a0382001d403010301402001070019400c000c000700038020000001c096080300710341150f0040003068410340042d03003513000081d4402c034403a020400251140026105403801458800c0c60259a682c076035290200e80170740c04640b43c002043c800c85480b00182e120b0001d164038280a491843c15540341c50f00f00d840c01100070f00c0f0309400704180f4800e450400030b490141d40e02500402609490b810170181d0901c04540803070004413808005a4 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 2725349 1250 2724099 2724109
    0x1030207031d0402040b031006030c020d230f0c0106050a0506041a090f0d0c030c05060301080312040c0f06020a060b0d0209011a0d06030305130f08070303030b03030408060f0f0105 79
    0xa10290075680e00c0080d154595452000780d00e001882552140d000d00c4041400c8000c0e0000314054500d40c40c101080c107280220140c1600ea00148040554108003001c01d1038503080401c4030440e41d41f80e0306544107a48140508a014003a40400128804000c160560f25505c1540540141c40702250800411680c5504001e80d40c800c42c000e44515040d0b5078410704003e80c50102030045944001d0103200051006c0b000b01706040040b1300d055410710054003040050017000c15441d4041c1406417000d524660402c840d01d69644102480c42c02c40c854008005000e000c2806400d0001c1e14800c2070500000755501c4d8029a203110084094511500d04002c9407194606030f4a0030728541e034082c010031116845c1c00010121085213100406841c8810099a4801c0c2c03030920854010703520949540d5221440917482800603e800d40100c41c601148034400d000a04000070381e907007280c0d4145000310700c200c2c020003c00d065002e0f80d440f2480c944074040920161040251030140701c1c680c200300780c41c0f490380e884007009 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 2726599 1250 2725349 2725357
    0x7020d1418041a0904050604060f020306010c120c0206030907060305060409020d02150702040c0309050d110c060f0d0c0302040302011101061d0603010b0a030b1905040503040501081801060320010302 87
    0x410200a0007405000c941450303040031070b03070035003020349008001908400715850100456045800e60021810407040186034803c2c11240306035907000710306510340400060030001310362801521403141c117005411710383d10035411075030074550251800f62030341042d441c201d90310030303042c0510000b1909040004020382444d02c95030b1902600101220801002602449680300855145421546081008401586850064061055055500181521290503c2400c2c044566a14010400c0f0000f004011400010303040981b5a0211034203507485480030042d85031072051450340b1140c0c40c107111200c1c90300b5400d07901410840e4003c1c0c942d030005a04001c4094200c2d2007034081d9407045c02424101000140c221001954407410150000038203006c400001142004954000c07600d150011007006141c00210301c000440498003c2d00b800704c0e04095413070684134080d6005140c10000c517180054031301d1080c6290b100400311031a008000c4980c6a0520b02c200d10007142c003031002d40700011a4009154428401c80d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 2727849 1250 2726599 2726617
    0x409060b0321030109020a0207080f03071109131707021323010605040603090206040e09010501170708070506070c030b010303050703090b0f09040b0a08030d020403110103050105130e01090b07020d14 87
    0xf46185c0c00c14410341d000750040203c05003148600391003c03802140800c450b41842d403028000f1174680308907240840d003921100c008a8024003007101800b0038021113010885019a024a44204d14104107a850080c0e01070100e0195010795541406200340056070321944800d5519603405003001510402203915036003c0c0b088000084042208000c024481c0e8401c5004920040c1043c1c0b51640d01e020040030381e1400d035401281c596444004220641000c0380380381d0986561400381c4032030b41c034119640340c980e134039440f40900070755001684a0801441005980217190302032408a01940c590038002c01c87d41089000310086401d440000c506201684181d41c448d000a2030401d00d0812000d00784000703001d2282c60309402c280c0401c07002c2030368081400984000c00000d03c0c0140c03158598103202541a480d91002c0d4141803a1000600c8103854903235014008013103559000c03c0e10400c0c21000c0e0b0050600e4000500950000d0052100c000e0b80401c2500e40400c4941d144200003100e01040d1103548110a21 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 2729099 1250 2727849 2727913
    0x30301030308060f06070308070e03010c0903030c060b06030c0301030501050f04110607060e0d0507020102010b06040e0c131208030a050a06060801060311040e010311100903030804080708090409060b03 88
    0x42000030b201d1050140c1c4100090021000380410001003903a5402044d400c8010482c04410000d403203038450800c0c11544001c40003804070121140e40a40403440e580000b804201030510501c045c00300541200c2542000504069600c1c81c2c02c2140c0070180d0404c2c0012186542840c0c04109840ba00107031032030103140c00c60b207805035021180302007213582d0380008002c85100b61202142611804240040c040741403464035030765580d1205200090031205d28038589442210180810300041050040256000d4010028255500076046503000c0036070141d4001c00640311080740300410842c1e1318007d0360042074000404d205c04d0719010142c800340e07045400f4800c0000c200500400145200e9000401e0502084010610b45500d501840c00c0c400801d030816a1000400c2d0070f03201f150b003880515540c40140501e000c010b124259030700140130103c040e00181080304041000c03003e214142d41100d94290004104103e600703550302e0b08401130805c0e444034034460f00074240448180402c485961880c0c1d030714080 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 2730349 1250 2729099 2729101
    0x3160215071226070801051003050103081206130f0c0305090c0112020f09040e030403050d0f090303120e010914010b030304050310020309070803040303020f010b04020a0507150b061303050708030901020303 90
    0x11104524038601820225008500300f01c00144080388003030240e0386541c1c85600660401003803010000d455100e81c0304144c030f00001040400c040d0003e41d0606004120f0003011901d03448001651001d80e500b07181a118504a400a1440c1496003d603c000000f510301744182d548010b1583c1d1103d0841c0c3c140c41c082941e001010f07041902a0f0700600300790400030307030083c20580d0310300204044483d030910035006648001014418041d080010018801043c0b4040c819070010030030040a0301d11900c40201803050140c0030a40b546a250001e200305034600000304501c1c0714604050f03100700440d00466806500e85182119542404021501030307410144c010201d10000f02e402e50000e40c4010005c3d80607005900020561160030300041005500940c02450310420451820b402c444001c41040d2003980304000d41080e054210341a41c2041d5002041c05591225500310b80c4003400103841c1d01d82c0d0240c800030300c4c02d0340290a01070318030030389010390221b6204c580c45600c181e54a12601001901591040c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 2731599 1250 2730349 2730383
    0xf08060108060406090c030504200117070504090212060111011104050105070206090904080c0106120b01030206070309050402040f1703030403080609040f0203060403030b03150103030503011404020c0316021507 92
    0x180ca01500b02c48082c000041c0302c0c2d1346046034822501441040f0b8002600c610610041c0a020f80842c2041510711100c8611401e5801c00600f4600040450300581ca02110009420394050025a0300a01c03442d2030540d9034106059980002030003c80714a8041240280f030b08068000520540c01000b42e200c40142c9054104401074807180c01544040703900400c10014168a62079900038240074034410b100c0140c03a444404002403d4580340d8001d401e00e080045101004a0881ea0b4160304503a0180c0720241e031600f40d401c0441e515106078212a4216000180004104035880300000864070501a400554409035446c2600c5e48070688000e00011007113808225a45450300200b80c00500c0f0741039502d0784203e1680441c7c100b0201700c9003540801e0765030310031020900301032003080d002007007002924480d581541d1340070f0000c0c0410b01030401801c11101c00100144c50701d504548011500e401100c0d15089181100d5141041640e012030203020741700304403160540b450040d00d10540c0c0c00210045505405 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 2732849 1250 2731599 2731607
    0x10050702190606030812010302180f0a0b0d0506010f050109060201020301080c04020f0c010c080609070c020d0308060103090203060c130f0b0a03020a0504090e06060102010612030503040210020f070906050102010506010f080601 99
    0x264200382d404550320380001000900d0000144a43c0c8400b0496040641c950f0041011400e848024410190304031410400300866002c0c000d507100c406980c0000350103170840041922800340820051a600ca12400400d098000c40d02000c02c03108241d9030004215140c1104900342d020030300c40c900c03142e40945c8002c18a454150041d203044800102900c0c10142140f07070310703820340c0c0103508900c0100d6103481c00d000e001e082460070540c2c0001d00d41800c034036000040d804101001001d1a001c1c0030004000d02245403603221b40c1040c840e0700e80060455080b400c00040018551b8420440ba8200000c11500000e007119142c81141c03c68442c00580d45c1489802074003540030703511019543c410810104404108001c2c58231400130402c01e148010003d91030000c00290031907010381c00030441d013a200c521032800203600c4812680c1c06541134894400c62110540164641a40415407900502400c6030120348200d5a03441001100c000360b00030700aa894103801507581c0506003a088000500c4074001030030035405 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 2734099 1250 2732849 2732893
    0x60402060901230405010e040c080f0c04090c0203090405010f06020d05180a0803090f04020301140f03010f020c060901050f011d0601020a1205040317040806070809010f020304030c0510050702 84
    0x2042c1414000719900c03249810151600b071000f50800000490103208075640440004590780007580d04000c441e121400152840b1390041007808030310400c40020301964841010fa500410303039014217210030a54100080e459030480f07010203010381c1c580000080c52503a52541c03030382198480e401500304408403100c12101540054403a240c1060100d4031240d10380c80301c2c18104001c2030150059070b110251142000600d00030403170810320035401400107004620402400003007100003100c5600c045003540c0c010901404020640742ca900384003081d602030080001c0b54881c810a0420001c004940c4c1380380409038000c100707000310549107249481800f4144100e00d09aa0442d6050044a45013611640d86101420781c0154410002d0000b0408004101082004102c882841004203003414208084195101d00040c0014204011100810901c070020741c0300c0035280034112004d42da2032800e4100509101c1d00181c01311114851521307220840c00c003a03c42c05010703400e03a502501a9551a00c028102c7c4c80e6 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 2735349 1250 2734099 2734117
    0x30c11010219050a090503120301050102100c0503010605070507050d03031d0102040e0601260c180108040f0f0816050a0c05010e030604021210020d050a06060203160209070903020d050c0405070302090306040206 92
    0x20080c02003220380d030230025041100740001c03c1c65542d40c108400207040c000c03611120100c050811035454107040e0001e007500e041d603260b8641152550943d05101c2e01c2c1280344d80c002c2e600b04403500000c005266041e08000c5040520406800900140c0341000e0300300c1c462403160200c02a0381c007011139100e43c4501e140f07c80da2090045d040e0a18031081040400c5410156200b29946400081c151900019030300c02c00b00c2c484090904050920f0305858003201003440480040c901d4405584c00f100300f004200c01e84905a00b0300c018030804c9100e03880c0c01a91041d0048064452294480c0d0000e1990700c55200d640d920f450180103004c0c152103650a01c80c1103c800900c5000900550140e0104810144060a11106002d40c040307150b0501d50198000c940d819007100003150000c00c41081210b5a00e02d24240003541a50307103440d0740d528558221104106030f04004d51240b6501e04004c1440000078200141e80c0301218200446e8869400903401c0380b241c3d0080d0342d010380010000402602e0700030040d0501f91 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 2736599 1250 2735349 2735357
    0xd0801081207140105130506060103140a0905030f040f060219030c02040504050c060703031506050306031e0309040e010b090606090f060f0f030403020708060f0f010b031b0406030c11010219050a 85
    0x1407070090b419800d445d811a000b0a0751200c20121034140300c0200710f51a040b49007820100404000c3e0605d544a00100908a406450f1500d030840100078007002192000c1c20400b0714251103a0325418140d182500c60700c16000140300b040c038071601d070500b0384204840040c1c4c581c940d0030b81244582d00344009054001c02c03e85880c00340c91b6030700501d515001700030005188a554002030f542d06c40700b0131604082964100d2002c00c4014010000c01d5200080d080c0101d070f418081c0c3c103a080311014186861032041c00f1010b074110781001b0301500e000c0d40541040c4040c1ca02110140c60301c2e030300c040074800a4000c03c1590343c0d22400c21070803201542410002061035150f0442003520b002282d084e0780c0e440f070b803059508800603805410108015070044c0012904074403001c0c2000254184816108181841802804007010b00000030600000030a4154200340480bc0c8070f01d80c64035034070390000e001007060a0803400420445502d000c14400c06200b21060002412000421060211812592380d0440e80b60b62040c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 2737849 1250 2736599 2736623
    0x50109060620010b040c0c0213020a0203090d060605100507140a11010513030b01150206090604021f0e03010e0601060e01090305060403030207080705030f0307030c030b0a03260f0a020d0801081207 86
    0x198480d4000d0340c6400406491f0f00003440e099105012031407a05400011003148180b254480c02e6501100b00c030aa501d00f00d42c8600151610705020005250b01c1d84400d5000404410040020f0b070840301801e10180079800c0c103603200700d10524440d264525004c0040c009103141218071015801400600211045141c903442d03455101d540b9000c954030284c00500448690b20324140800b82c3c1041066400b035041c1c0c018048508095001c2443c4031482c100c603800d03103542c030032040320818803884440002660041c020702214011140c0340e9211075082c0200d00c0000c83c030790151003055005c0d80125084030383c000b000381210740c2d81d503c0c00c4000b03400400b0f00300e41e40e0f841000601d002c03d404102608150090070b251075035a00703120ba8003a00700e403429010310081c10308140381081207603035042510040304e40100017500a00c580c4841b10081071400300c0480e0304090085981e9400b66203003c040c02200c0c045408581581300007200c252030465003446052160341c403586612140910390000703030800a204102d05081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 2739099 1250 2737849 2737871
    0xb0f09030408070909020306070221030411131406030a020306041106190201020408010b0a031110021204030f110103050903030703020d02040302090406020d050606090a030201140702040606050a0305010906062001 93
    0x2800715a500c64204d40e0740310001c40781540380c14404c0700d4000e00240014407400c5d0f40750340e4049204900a4600744107030030100028040c469a0007512500700030050045400358400c80d82d9600405074003070301501c1d65a000c800a0035604000500c4000c60350001c0080c80ba0743e40e01d40e0307030407280e111b1017a10b25000b0310240f01a400110110803280100d04aa40003d81c441e07040c185951b084030401c01c52544520426076040011034140c1c003421203981030949107840203c5841c0400ea01e0a410030f003046a54520001d000010b0060680c2404145441100c0d42038801040350011401d4400942e2918038540040000c5950700f4081d5000b030200801145007d41010b83d650009120050304950a850840d00001d00c0d800c000c15522a183d4400d408840090808070190702084100c981400700034144045030210307507030140c400d10030707141020780c020170503c51961100c0c0018510f0f00681d2010003c00e04101c008102d8070218003903c019240c040d9900c030f01c44984a50b60410b186650513042c0c000c1d550b0344d034440d10 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 2740349 1250 2739099 2739103
    0x5070b0703020709050c090d020103020901090e01170c0402030601051204030215100905060312040b070204020c01050103030309050d02030306030d05090111161502060105030703020409080c0703050105060901080a0b0f09030408 99
    0x900340c003035009003110f1071030840c0c21300c182c0d0720003022036241c90010000038060784d035400200b160458081c82c0040e2621030010041c0d03040c003241e800c1401c0c0041410b0000802d421001aa00115042c01d000da80b4103030800b200b030009034041542d44d1030200e00c0c2407100100603d13091402c103600c18001d104403189000b20038608840d071502602c403040c55000001d428448801c2c0c0d80036a80c1c0003042680203001c010224081454140118001e10300458000941031054bd075441e01034034a005003001c020030443d43e42c1d2401a00602c0480302c100d071180241080300541500110561b4420303200a405840c01da18020000c44441c0c0c05001841d0502080440d500d0207050300f00810f0249a201080307005815042c4072155441c0074480b040d01c01107602c801c0040c00079031004903803407048a5041d100030642d01c801340b40c01c002d03500481c0380f400584c4c8100e46001040c08415080b41c1d00414040e01d0568542c1d80303655441da202c0c015002c02801c141e0482c07003c101591400c80a03960b0000200c01a0303820503840b5603c681c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 2741599 1250 2740349 2740357
    0xa06020703020601090e0604020a031113180302011503080304020402030a020d090c06020c0d050c060706060302060f0703090f0b070b070306120c03061b0903060c0201020708040b0c010b0303040503100905070b 91
    0x90700592003803005000c00d50083c45820103881a080c01440c04d85020390010305044081c0c000105034650081e8006c480e0b4444040c070b61421140c9540034055000458100d1980d0403161400740c1c015030900b4240600c030156441242d0a0ba900001c4451455596409200281d84058401f240c51035080040a0110155201c1c004101b4400c090b00700c840c40c07402c10001d1a01d026840704912803000080c60500240c40020614503070442a9200c1c0d4841c0700741e05220004000c10340c8003a4102e8000200c400d0201c40460043c0a1948251039000241e034450050310385464250203442150281003080101040024611690042241c030700810b0320743d20f8041290b001b40c2481400c403001440000b040c0100410350084a00c014414419542d050015a000600c00402844003800903907031810000b094a200b901102d080da074000c41c40c0c1c1e64999891580c528a640046980b0445500e88070b4a03816614021003198102d8030000c00038841d2a441780c40c2c6000920b0381903011903c1d80314044000500800080c050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 2742849 1250 2741599 2741603
    0x6010c0204050405150105030606060405010809070503010207030504150c0803040204090f020301110901120507020a030c0503070803070504050111010b0604171005010602030702090f0105010c0602070317040602090307090501121101020a060207 106
    0x1c1c1141c1020412080d03a17421040c1c204911982061041100790303110442904c0849109103400d02a40d147d1214850500c94039402598040d400090850103142d000001441240d00005004000d0140020101d1f5822005880100b01c1d040402c08100985450b4022041890041c144110b480d800c540c006421070b8420b4205404101d00070a01000d1036801030000700b1200c20342e201c00d00191420100003034458100709001002e111240d6006000d0200800599003169070201c0000c0d503034204914040c01c0ca0300706121315030001f041c0c00650010414107005196882001401c09800d04e81428161a0200d13604840c0c0381c024420000d04988102c414010540244804c1d0040d5a8403407443c0140048084001d21500005807091700400599a020480000700758024500603100d17541c9203011a482a0ba484461888000036402d110511500b50300403e00144101c003210842540d401555044d11400d04c684006000204091404a0159400080c1424051040da056150740e44e65400403a0040c0d142 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 2744099 1250 2742849 2742853
    0x220603060602010f06050607060c0c05010f1401050d110f04020c06010306090215031006030203060103090b04050d110d05032a040f080705060c03160212070b0706060608010302010c080306010c0204050405 89
    0x411400b50207202d082c20304906144113100703003424440407600328882c001c00100140d0f40d5401c203000a07845800b16002c4154000028010408040340d00c501411740e8400001480241d440001442c1c54160b125a00155000c031141500314000343c200240024080001a04641c00b00507500510a09004150103136104000002e003080444c014080710040100a20881c24002c01c14000f014002c0b000ca00704540c03191802590700d50340c0c4401240600b00030603004013190385a0b418041040004920307490b105285a0f100c55a9101c1302c00c801d82e80f14400842c10b804204100003042c0008a0401c01c414003034084040d611b03c2560706074000300c8550150f40110380d109403407031080c00705c1c1354207000c84401400211042401c1c543c0000144c0c2d203d208080381020b000001661701d100f1500d510f100d002045d420301c000c5e2808103907a0740705282030358003954049504a140c908086402c0d0b004084030b038142d0f601a96800384003041c5641d200042ea10140c91181404002c040c40d4005075200e0040d40c1c0706510840c0 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 2745349 1250 2744099 2744111
    0xb0a0201051b0a02030403060b0a0f0902030a050702061501080a15080a060f05072a02030607020a020307051905060309010204080303040c03020405100302010e041a04020c03040609080307030212220603 88
    0x5041c40b5024685044400702c0345080051841e403603400020344003902d070480d03c00070b01d000c0c00000190a640d099404591052031a4900080801059014510440c800013040c00740b50740319a0100d8844100303c5110080e44103155003501c203035128458482e031044070341d140011410349007035007d00c49183d140c1c03002055074485541c01042124a01581074500c820001c1030100d4100b00d0030180c07420b654154803018480b03c0c0c0d201041180711985401d800550042c0c183ca01b81c0c107048000a4607041045001ea0003442640350014441c2008a0003d401002d4020907000c202e08240805c00603900c0644060302c250b409000100b000d10041c802540203503c54205102c2c1c0518510501081d610020311540c1189050401000540d8201640201c999000c59002403240c11201402880e495107141c0c09401c1417000c82c0b007080c1c1d00d0f00000104181c0c2c210391680901d482d03075116655030700c0c4a220b40080048c0c00101e1681045ca4400307002d0b010801c0c07a8411840c22001d0ba942000c2380c1700b80c60380034200098030380c2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 2746599 1250 2745349 2745361
    0xf030105041101020d1107090e0109020d050102040f1406040506071b0605030105040609020c060a0e0f01051005041401080316020a0302100807030c03060b1209030f0d05010e060409030c030809070b0a020105 90
    0x743d500032065811b000e1200d180804907030307445401c40c1c491040602e40316460f924041d50290710143c422a07000b4026003610400341030141c001e400c20b024500100540c54004101082444610940400700604881c5000d0604040c0b02651700300c0e18045510301811040003090000e181104c9000d0401a598140c496140900300000e58515234012481c040c81008800a01d43c408150264007800c05207000c6400400034440e94030702580c5518941540d403174003044c0306000c0000d103011000c0340d8088038140302c404c00703000d501d8013040300a100790340c643d40c020000d020300b00c00d4182e195010180014105d8080e180e49130003040c1450386e503400010029580783c08010686415108264031245070b07180c10402d035810000790950300d10514010649008181d000100d2840e002c00c22600b401d120441c0c9140c03a01c04600004010702400e0141184800614000034150b003024441c2500c1103815035510303c840509910195241c40024054600c0f1303026141d00410040491001885400c0031a4000600e52400c1c4c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 2747849 1250 2746599 2746603
    0x40f02090a06080613021201020a02061006030203070906080406020f0304050c0103060e060d020103020c0106080703050703030305070e01080f0601030902091305010b0d08040e0a06080d090503060601030e070b090f03010504110102 100
    0xe001e20112032038508180182400050ba02c0d03072105240d54011140c4100d400040d82840310082025070560000841c0300881d9400f1404600401c00c290301c004066850707800580690108880203400144030724420000d1610400030320b034005000d43da0052410141480005207944101c8094400d80d0012014a515581c988142030060185101c0101c6a0030410300280000c103c1c00e101070704060700403440480c3c6000030341c0658000e086000072a0100395580c50300e41d03120260703440250013182c81c000c0025520b502402d60343e130900034141c1d5135200555500e140c44501002c0980080c1c10942c0e11039504d40103031140c9006d1401000e407044017401c080807a14150742990501a10b1a000d411a801200000b6034014192401c0e1050001602c1107503489100742402803d042c1d2040c24940300300702040c400542c002031400147c0c1c20503420368415507141401074040e14100740c40c00007203503c000e000708800e12116020700f55040d0700600d0300c1200e080c060700003402c0da5800da4040d5083d0740c1c0c10307110304825030b01 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 2749099 1250 2747849 2747851
    0xd0507031106060112020a1101090b04021e010c02010507111302040816080d080402030a0816030e01050702030a06050a1d0d02010c020607120c05040801090c06080109020903120702060c06040f0209 86
    0x40d00000d0402d881c103d030008188441e800302d01032110b90049001d180c42405148140f492042c02c01c0200280e00b401e04082e0304c3c101e4155410380c0240c103024051030701603e07084540c50302c00700182c403030f5000014503900464156001c00c1d005d499070b4070f100e01c03018a250766031076080803604140f290140c3c40324103001c0348909001002e514151032210f00641007001c02004a10588c41540c00d0a00754400c0c1e50381d0002c2800e01148400041260200180480c40c00115801e00b4002c0c0703000303a595000c000c01d10700040d10a4451150040d515034040341016002487c281c0040d40d006030760f2003002c60603007413071000203d0744848449940b00e40d40041000203070300707070b4244901090713450070b880188840e00f046580542081403040808003c6610b40f60517022a41c0524202d03401000c0c040c000300440c108606140700c1d022018001c920005410800001c2c404603d40246e41960000030098401c240d440c080940d05580000030481e04540c2c20f00c458042c0107001e110705403203030340661064201a626441000314280c0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 2750349 1250 2749099 2749127
    0x609060203041206020c01060f0306020a0305010e041a090c040f23010303080411010c120507140303010b04060e0f0a08030c060a061a0319020c0109020f03010603030f05030c07050d050703 82
    0x44140001c02c1281000404010f283c0c0d040280140d0350304034800410b01420700340d007101280d8001e026001003003020550092001c0440790b90208001c1c1d0700e8801243c3c0201c0151809003405042030402e00e0324101e19030300700340c208050000710b40340c07084800045070a03030702c1c04425241115501c42d840445421440c0c90317040c2c20010712044001c1903040d682c000d4040b210140010b4860483c5e1420021181d01a01c10781c02c00c079402c40e469003100b503440d41e0300138456400301404450603031212185000805c0c000094a0607034001401da1420141410011505540e074481403a60003280305a040b00d041c1c4031210100c0c080c21490024650341c00b800041d0034030345200a0803c0d82c00c1c500c0e1038402c1000c3e83c0303102e4407442c2080c118400641c0d280c856011050369800d00750b004401e04e6200280a19055005511040440380300395105000803003100d040508031951803002030b01044010707101d602c2083c800c00003140e1001000001600700007058648928019503110301401003400028080149500300d903004540711 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 2751599 1250 2750349 2750353
    0x706050a120c0503071404080601090204150206040209060607020307031401020318030c0d0c02030109151505030109020a030f02031002030a020909010503010b03070b0f070506090a030e0616020906040908030f0106090602 96
    0x3070000300c01003292100600117420401c000869040d0720b203600d41142c0c0104640030481d005940c403038420030300130b6206d44603000103a0640900080003030f0010641a100c1c0383c005001c0366843d40c0f080c0511605a0115000701d038580a044004000540c1c600c04e04480c1d23080c140700040e200e1408954501c1034003080107148006030310a1004010a010008030b44600811070314000d98940d8007403001c2409003006640003408041030032a40564030080d503121820f442102d508541c0e59603a22000d040c00c94a40c4840a50065840081400400c0c03c00d03041e4007485201404988494032003980c0442282c209881c0c4034540d503000692520140390611180f4007410b002c8008000440084d000240d45991034480c0041849000c14807442102c180015502c205801c4003d40e85146091500192903502c0c1c42400c134007007103854a00070b6940c1002c0007610303020103204407030080c80c0015408101031404014141ca42c86911482d001d40040d51060180d070003000840c0032f1140c2d550401c5405000c40311030750000b40c215 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 2752849 1250 2751599 2751611
    0x4060501110a060c1b05010c0905010e0109030204051806040302070306110c03070611040909031205070801030209010b0c010f0204030b06090108060903040b07170406020703030e0301020301050604090e0f0706050a12 94
    0x30410204600150720351243c40062804200b900695603151008113020820031800700503020b00806412401c204083c59503000216916080152481445c2c41c1c03c090000301801d4091005090650005801003aa03201c5d940e0a2034850707024900d40002140c1c1240140c020030810001c2200f0b0740905050104101845401c24020045e690769034003611030701400580e100d44411240300c15134002c84001c0c040c0604240300340c140c98200a0030780d905a19202608615050014240342c3c440c4a0f41d034140c0f40e0060030454964a0050b0260b050703080741c640ea6101395660901204025060700c01000254858004a0b180c0e283c8801004100081680401d220f9001682000500400841101c042c0c5410001c0644c607415607082c0076505a80124154801030000940841c20f581c001038200c04507403103551806191a40102403600f030b8003080c89011340007001840300307000200380c0e0341141c070720748480c002212950f40090301c0c3c240c81d01d58242d0051010500c006121380d90303036500407681000c103081300c032080c810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 2754099 1250 2752849 2752877
    0x7020904080702010314010b0a080109060303050a080a060509040c080c0d2f0603040308010810020a050403060c03021303060e100204080d080c04150203030109180c030212030d0509060604060501 85
    0x40508000c000400141000400104580c043e50080000341540180d2502c80e42c0c54102d0454558031503099800401c520000004800c4031a014030003c1e00d1f81030f560103040c00461402500d006401030154a6040d848501c0402e480d20781d08409442503002e0b00d00e107050079207002e16060410314817441c0381e4000e24107142543d02003a00f11710080458140c540b88002c02112440c404005110007081055011000005000034107600522060581d55201305890040c5e0180c0e520340100e1207003842e00b4011800504c020404540c03280c3c841124030107642009440c00080c0c019034030800301103400842c1c000d6500d004104104004010000e8015100441146441c0c14420300a5840c1600c07d440801c000300c1800085c018040c210698004100c111245000203400d008041c1d02c90304240502142c0b2860140812800e40e8060809800507401c0b0981b04030b400d081d50288007003084103005050381440b04000262000c40c00d0b00c01e01e480b90b00079001501d0242000010802629440c0d07001c281086201c4044203d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 2755349 1250 2754099 2754109
    0x60803091f0201060b0c03030402030105010b0703020607030203070c0f0501050f15060706020702030c06161a040b070309050c100306180203090d0305040312060602030909100f09090c12031707050702 87
    0x1c0210031a922040898041080340582095080340039043d5011a8a1a2101c0000f01860181d44224024089a0380b500c080e4822805051030240050f8020310118035240d0007a401907402041c1c62900510344861500e9464040390185802c5130b16a6680003009142011004016040405058404d0400e5040e42c0000c1300b0340104980603220030343c0041c030300c02103541c00c0003441038116001e00065110402c03640c00e0712103d281040306491815400c0c1c4c020390070701802c00f8814072640e8002200c01c0d039a1a078000031001000805000c455038803460501000956441001034000021b83d0f40105905091984182e49400c1e0092460303520b0b070041c07080c406000d03000b0131445c0050358286000101030b519410300b2a803881200d111700c0b2100d407901d0f9011034900d5000c4010650850141c40d000c0b207548813620b4410311200140300f1145412442c0909010100c0350303800007500140121010008161903903144000c3c0181d040302140403e2032213241c020b02c031080360300e031603407106043c1000c0d410002e40d900865 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 2756599 1250 2755349 2755369
    0x5010903020609030102040e010b03040c09020703080a0c090f0f0501090f06080f0403090302040203010b03010518010608070c1a0708010f080604020a05060d0e0f010c020709110904150e0408090406080309 89
    0x284281c2e800300714030040d914254161030050031125100201541d480e103644c45c0e0b41d44255400c0c1c5603107070624000300e0102100d00865400d1649aa00d03a1075603520040403c00500107240c42108210002400085500700c40306800058002201c84000c400c2ca03050014090074110b90008240c0268000304200d41e9412007203942e81b142506140c00420350380c1d4031302200c0500541c0c00003035029201100210300b0108100245050300d409035403003000c441d070001e0360301d456131400d100380d00004801000140caa50303c0380015454243c403482c140b041c84c4c0a10500d02060400c220784460000d8040e0004005400c40300808030003c2154401400c501d003001c6c0c0116640c0c24030750142c03601496000891410500551303008641203030f10700013030303496200092030003502a0041c44e4100d030061250b035401084400c500d01c11082e90b140c21881c1a49069a40810302019081700d11014017103109000380040c510090190552080e0f104071042035072803c1240400084502e10380141c400b17940180107106098459150003 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 2757849 1250 2756599 2756603
    0x30307060b0616030309060b090f01051003020708070b040221030a14090402030709030201031a010e04050901020903060906010e0f0606090d0206090a030c0311180a020304030c020904050307050105060a05010903 92
    0x1007800700a06012031a680305418020f14820001140c5506140d4154003a200e032921581050110040701401c00001c914181ca14110b00441c49004008034138102850080c85141403c016051030105d454000c81c40d0480d000c00d850b03403100481004114506140900341d40300c3e14503400418070014882e10780d075074082c17050008140800140d10312103407a8441c0c01c0e02c0c0c0d002002081555a460268402090344c001840104d0100c0d00340004400f0002c680c00000d502e00b103060350703100c1007481c5500c10800601800b0301112102e550807c01610780d07031001d01c1389612031032442005001c9545040100c2045041c000c1c8444a0a0550b80c1031040a0b650f240444014a0b4211070002c2d04100900010740c0c0ca00c20300d10b00580c409245a0000204035a008c0000100da02940c20030810206440500040442c0d40c40311004020b25800003030110781e602c1d405190054068035107034041004503404500202c0003030707805480c2d961000c40d8100030440240900c2c0c6c1d004100343ca65004407454840080c0c400c0800d8000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 2759099 1250 2757849 2757851
    0x10207080d0c0903020a06020c120304061202030a0e0106030305030403081e190e0115170102030105010504051203090a060c060c0306060503130302010e100606080a020405060405040507020f2b080603030706 90
    0x4002001d10803450f0301c0146400411403003040e030f40c80c003000c1c1d62010b100228070b00400300203882007218000403041e44c040300c0c15625120340c4444592503030700080d48024440c101480e9605e0945035820024819039010354481d4841980c0c6c0c3c102401c1c0605941c100500203078001182c0105078840f5101081c006401858441108030600406c0742e104016204981d12a64158604441e030720800310003031003078000c0310340c9000f01602d1890000b400c60300341c2c802402041d0109504000070011824180f0140c0c4102c290700040e0713824401080c0006080716010351041c4000b690600c0f4110a004051166a90084a90408111003494003c010300f80340070041c062480150021090310078103000307400180c0c041d500d00084c0e0b01440f249034140c0300100300900071000040c03018000144040d280340f00315000e940e00200590300b13085c0351208010207401c004210000f14001c090802220b803008028546c01a4442809402c004420600c24460309001040302c00411840c5070038000c681c1c030040f04445141f6080a4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 2760349 1250 2759099 2759111
    0xe090c04050c0702030d02070512010e070e040f06020a08040209060315040303020906040905010308040e0108070e1303030b03031c0b1e040504030c020603010305010509010c09061704020102010b060409020c0708010207080d 97
    0xc40000b0074011241c019405000b40100c5803086e80d408078038501980e4088540695040c040d103649400c0301c02d20034603644141d2181b1024420000e009180c40d61251042000314201d003101e941e00c0d42660441c0c0402d002040c440410300045140405c18142d00c000c0c154002c1174800d0709100003501c5150050300140c141540000c0c4401c2c1c684a4404a80280510704002d103c6942d50b032802c441c0e140d10510400b8900340000c400403654010215482e802c40b00f040d2040310f01074407200d202c4c900070210403000701c050540e02c410030011914140081c101d4403402408049a0b000b540c0501c005803a81243c0b0540f00d5889180e6980841000c034603c021481c0040e50001101d03503c0c0c0c68162140404600013075404400480000304014054000341e00c5001610001d210f00d100c00c05c829101c54419000d030742d02081d022072001841c03000b020700395544240144004101c821420010902c0e580c010340080d0401a00001c41c07a4400381e04109000080070008021032500095448003407445c0107042c10541c0180d1962 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 2761599 1250 2760349 2760361
    0x10201051b1206060d0204030302070e0604020309070e070207170d02010b010513030305070203010603050102120702011a0607020108040c050603090c030111040e0f0405010902090a020705010b0901060f050913060b070203070e090c0405 102
    0x4400e0b101c000017842c00c00c66171a0b8503401e010f0340d070b00914401c43e1140801e25002a641c0c2c24603000362400b40340600010328240d0700384003400c49944c02c02000a811441034907000074130300d0520030f41c0040f40c1c80c1210240003d6040c00350000d081d01ea02c01c2460b03040c00400c00024001485800700501102d07003502d0034503229a59440001d01400e070b03c3d440907055600205d4034054001038271041c1c40c01840c0300c1e0000c02c0712005240d1080d103015002e004155201c4c10074022240594000c003600b81d4040d100340303480100c0545490002d07445400940d0100180c0d030150a00d41d5050900348900105c9110790425582000e04d8010144d03040900203010b1407551611602180820009410a8281d19401040c42040340b03803400a150094200303000981f410341c03d03da98180e9500b02103003568141c4503a6680c051006003403131000d444507800080c0040d044032040484a1a01e0b11512900c03014003440e080480e5110301d140101440d1000a401c420030150454040c030400130000a00090040750654000c2115951a = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 2762849 1250 2761599 2761609
    0x914040605030706020c010801090e070e0a021b030a03060602030f0306100203070602030f0a0605100804030305090a08040305010204060e01110a0f020109030206030a091202010c0c0605060d0213020306010201051b1206 95
    0x50351203282c0620503948049441900440c0614040e0002e0b0380b020000c0e030b84c0300c0c09403080e90705000c0080440d1700013076000e101a21181012550204031460054549100c40410914002001c0da07080c905400101c0c20014003645409090028210b601c0118204920340790f00c0c1c50303940b1000e018144110a0050107440c0c40d0b0003032068030000f80c0c00c044115242e180c0420749145020381181c00f007560070320b080c4003c9082d185c031102c04e020003010340e520118241d40b50b503800c0e801000054800c0c1a01c0c0700320501d810000d1011030080006d10b200d10009a03e95181050192a14143c0ca04140c18070403518206451810001071007910690881d254031080c04240c0011b075111216a000603400076000000c2142007101d0741c005000040c4103003403000640310a084201d080f070f402c40740d1050015030f844015901088240c0c1281d60401401001940840680e50009441a1000900146070781c0c02004204a968083c481c055000b00108801e83e03941c041c00c0c0303003004135208081e1000b01c2014504007087c0983c4032 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 2764099 1250 2762849 2762861
    0x11030406080c0702010201110f0405030d030606050a081801180203060906010305030324060301080a03080105010203090f090a020c03070b04030f020a0308070305070c060f06030c0512030405060d09150516020105010303091404 98
    0x110750192940c40c030301c2801c9d1071015441402468000d100d00380384446581d10900c244400c45583c0e0356403500700078400d6401c503030005c070191508044648411803000c1409081c4a104000569900304034440410343c818181041002828003072203400103801000456004401c032a0b00043c0c0b0a5450341c00310403a240d00081c044461821900000003000110340840d0000e040d911780d41c040c3d00c541a09030703030320350049981380310705113506401c001624040e16580c2415501d16400c0010600302505100c90b0302c04c0c10b07185402c45481a66112a00000e0106050300701ca845211520144041c0603510350b291006044810f01400324420103a80c0c2e800124001d00c00d080b4100d41940c049020703c40b0810390049880540300c41d00058500b0409400001000e11b4040c0310004a500208003860a283c0f4110800981c0d404c40c0d1030800d0381e00d8458140d400003851122510102404041c00016a8204444511581d480c0c2440301e8040da8542300043c00230039044030100048458000400d42d080c290350b4041400303006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 2765349 1250 2764099 2764121
    0x2070306090c030201080f060303040501050703020f06040309031407240e030a0302010509010c0302090f010f090e0c04060801060e0f090903130f0806091902040f090f03030c11030406080c0702010201 87
    0xc90710050804004415582d8000c59000741d0342c12401c2d441d0007441d0085400b00303031103050b4558000c200802407540030301c014000320350007070054070707945480100041d0901c6421101200010391140085c801c10864690403880c81c400b0350010140c840c10203ca00b90405000d411188500c0388902100d9096445800800c00c8950050240c400a480c40e25019028200c1a19030780302550919128106c0e81c1c0c420310070fa800200000740800103001400c8019988045000700709010441c0181c004030b02c0a00b5204c0c5180248402c9118594440c9000ca005083ca00107802502c00c00c504031440e9071003540c0d6014801c01c07801040f1400710554555007165840c5114015042102a81c4440c002440c085480201e0045a81c00c03001c0e120996610404540c9070f80c1000340c5584c3d003030940c400e07041c05810107a10244014100070000500030314142c54145110403c10002c500084d1200900440075074440301d24502900c407074004508003810a100580000301c014203d000500c1e0216001d800c0d0380c800d40246400c08 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 2766599 1250 2765349 2765351
    0x607060905010f06090e031c150b0904050106080403050702040c0509030f060a06051917030f0408060601030f06080309010305040807020402070b1506030f0c0a03060e0a0603140105040804051002070306 88
    0x1880c01d14103240a4225a000351241c1840c0280c0014110f40034004c840c56040c0100145103022252001c1d89404000101000001540c0d1000d49010001184c2e05801030568000c205450b09c84101c200030550710141c21100800001500b07001c0026084000c1d40c180a80c1268046848200014200da030f03801001d0f0003e0781031003034080507041c621010480d203000c2d00b443c050920040b5110030622a02007a0340ca085c103080006900101308462400e0320302101c808401044d00d16028140c041d11800d504a074020002c10303003090007030242e10340e00f5100b0341c1460101c005041c0451031400c10f030541c03240240c0070494140750b103440001e01044440011a910340740e0040c4110b4841c00c0310b083c1031420780d0f41214505015020000100001d252034410b884c0308031440380d4954130503a03480c4800703038454020403440414141c0f00c21002c240b00810303000041c0f0656180000040c00703451411f2191401000c10224840c692500c020b1101144a0707100b11000c2d69410b4030544c2e041100300004030300c2c1400d503500140a0fa = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 2767849 1250 2766599 2766611
    0x9160605070f0615030c0e04020609060a020c030307080c0c0301050405070603111b03030106020f010905030301140f040501030b061005040506030c0306010c0c03060207021206070804030e130e01020405030d05070b060103020306060706 102
    0x3040c4c04040f00c0301628060140040c000703841e001106000101650081c4d0700c45414020816286450300060081030103e105951001d681c0d00c0c0420315640044a084540c20340102d4040d960660030000702c03401c070a00303c00a0240b408c1c036446558503025207000c1c0004264892100e40c098039011300840c5c2c00c0d0500703804a984a14242120710b07441703410030b01908005008016540d40304a9050080342e806030381240c081e510b141d02e8409001143c4075400e1071160080c44100081c6265034992144034002e600800d04034040e86803840400440a0042e8840024070000303103c00e0005445034020349074840503111000d50b503601c660005892007400301c0d0000b41480d140140c00300c10410160040d00c04c5a100b40c0c0d1407072030369a100d03036801d80702d40c0c0441ea0140003400810000e0b01080c45503100e804000c1028103404200c02c1c41100000035110000075485842c2e40019042020342002c00000c1c541005501d0440c4c242201941c503084202e0b07016113010304154020012841903512401107804455200c0010004 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 2769099 1250 2767849 2767871
    0x503060a02070302060606030f060f010903050a03020a051608060103082a0102070303060608010b070308061504030b0402090105010203030f0a050603030d020a030507030b0301050105011b1a0106080f09160605070f06 94
    0x10390b10004089005000c0d0501140c0d80f42030a2003500d0040c601030320361101c5a928941480340422101500c0d50400c2044400000130507000d1003c06030590003030b40a0507000c1c2103030404518106c0360480750420090002010400180c01141180c10340354802141d03950b481341345170108082e03d205111510070190f001e450302d54010055005204542c42900c085c02625a1107505840740a400d10a00c3d0300503d04100003070000c0d00c100720343d9034040d0b001080c00320940d03500c01e010381c05034100b50411540405244144030540c40c01e447d00500500d001d01c0110b1642c90510025507007a2005885459184e0701d8201113003076540c060042c1c8003c0c3e41c80b0702c1b0441d2075a118800041c0540700540c0c1000200386004c8030020306007818010b440c10303500c043c2c488000c40e4902c0c0030005400810000144ca07501e50000c18a0500703200d2180c041c1c005c04040d5604845400d11507c101160100604100312942c01451440045030200d0500e10032541941002038540b08681007030444080c01402c010f082c2894188030342c00c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 2770349 1250 2769099 2769101
    0x1207050f0f12030307180515040902030703060e01180e0102161e080d020a030b011719021210150f080601080408070501050702060907060503040203151008030c0606040b0103052502070503060a 84
    0x4040012440203e141e00e6481e011b2110300043e580d48c0081e222020013051007014440c0e0011750f0000881d2500144c0b5540e0340d182080385550a03044036a00b00034001c00a07018541900420444005460007103190200da0b18500011500348074000713110400070002e546882101a0200d68256000b403102d0b50359000310400d8200075888680f4078000310303103010941000c1e5442036001820800002c206420b054179041c400d070365003054102c161000300b03408000220607961380320107550042c12030010800031740b030600600912120020301c2c00410403802c1085e100303110340d110154582006013802c0807c880d4555080503c8540308403c8040c1203903080c04184200154001482c910510002c41520001c94449a0884031071000341d40295141d40300c541000d10240a40075102d40280001d0080110617076200070361411900071814560381d80d002001085182d080c94003524044a109103030400080c030b4107013801c0000817000030300340001c190700303200d8012658020801080a030200808039200c92918515044c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 2771599 1250 2770349 2770367
    0x170601030309080d02070308030a020f1206030114040c0608040809030a050606010207060201090302100c090305060405010207110607030804110301060f03050601080f0f0a030e06070b0103030309021207050f0f12030307 95
    0x180003032070300302d00090700410104040340d10b1540d40e0301403c2d0007403560b2510092904003422003207041da0708211024005110400800790602d00381d032108400d1910310109402c4032040d029449040101400300310028803148400c0042c1c1e51075060024564480741850582400b03070135401505031294400030b03400c1c00b44c005085480b84e2000d81c222401e60340c9550080382a10400c81e4003c0259010200e0001641900c0d000000070030785c54605007101030707926201c0d24501070342550b050f500790354002191400d029501c0c00c50729007c2426034403280760903004d80c1d00a01580f4001d0000d8681400250b41c002155020b401440060402450a05803036850307041042d2104d8003031050181c1ca12a25034001c061347d00100e100c1c00c1c1d460b5001f000d410300d410580c0301954018030306011140e004500308032900000c0c0032080c010b40030714003ea40020b0030036a240705202d069002110454141e5000c00001c00441d40e070248590385183c41036855004440000004c030f1096070001e001204240070110420072002e510607030072 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 2772849 1250 2771599 2771603
    0xb09011505011e0318020303190206010b070b011202180c0a02060609041a070309060c0504060e0301061503020d020405060307030b01090e0402010507140f01090303060504060803040f050409030917060103 89
    0x48811541d485005541540d01c9440c0f03000d903a03900840c100240f81c02079004d005030441424681e8407180181d0300190440d4400030765002d0383c01c09a070440e0480c4e40e0402405014102603604e85107040c41c2e0740c03654602c03128144544201d48003041d00e0181192911140d03095240c0b206030044555040a840100c4150810000c1d035006101d0040041c0003854580a880e00868011a0b040e07114598180f8040150400811180c14507449a000d00300050700c0748160710880c3d501e9620a40c840307081c03000040c050450740746610320a1307060a0090100c1c6005c0c0701c550700c507098603040041c0da4800c00025280640555405190300a502004000c6510303059042260707424000d9960400300b0741c80c5d01d1450812003041d1006400030303200b40211000900442a034220114642040310000001c031a0202e0179036074518001c078000b07510380030200100d090602403080500070700d03005141001e0400012129003480782c42898480d0340c07110440c0c0145801940c400d00540f8519816200c40302c48004c506988483c02c3c481 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 2774099 1250 2772849 2772881
    0xf0f010204060e0904080406080601180905010e0a0e0c010e0f060d0b0108010b030702030304080304020f0d1a0c041206021305090103030306080c060304020303030f090f0d020601030606060206010602030a0302160b0901 95
    0x200c10000c0ca0700c010820320850f40821844d087c5410083c0894034202d000345114180f004040300040511800c00c3c0360002080d0955010485605048800c0010348000c0c00c103901690a00c00ea001c6050404201800a11020300c0c0416800e00c03070382c1c00195401d00c0540e41035000440005c85619001d0ba5400030f00b00c04000b0b880f840107990303807069070940310b00c03044400b10300580043c03000c200007072806001540c00c180003d10207008090460000346407083c6070039048801418194144200c03c1d01320329115408001640103508240c900a0701c10300385802890b0003002d140e4001035400598125845e00340c007034440030302401443e60316450003a006201c24010a0401d10541c11080f41514052080b24415a0302030051400d40c0c035481e00d091400386000e8510842406410b20310041c0e440c0c1000040d940c40e0484c0e00034a41d40d4950304000d01102c0c26a040b003000c54110500501085400000f143c01004651500598956030b5402d01c0d1a4440e01041c002c00c11644030080c400c0b00401500901d40c40c2049001c = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 2775349 1250 2774099 2774117
    0x40914010f060c05070306020a050d0e03030405010c090602120c010f050f07020c0604060c020108040c090c0302120105030706020304170c09070302070212010902011d040902040e070608010803040303050316020f0f01020406 97
    0x42c0595141600150013440c50f84580420300009125401238581080b43d81417071070030a4103901080c0c0699030321240c032002651000c0300b00b00c01d00c40d090151030501c420500307180b44401d04049000b0340350880e81e60030030000440014000701c055400d61098002141e210803c0155042040340180b206009498440051040000b413003e10714088040b20216140c030f40354240d50362440d6006440c0040014815606609a0600081d0100b102c0c05072040742d00955800594822200504040660040c3c1200c0e0003984554414000141c0003c2101c0560b4200e010542803514000455440d25891505050b0009942c0d07090046403901a006445050710845122100b0000242d42e24202c920588000e800907903d080841d0444500361a8034030421400380000c41c7d0b02c0919008101500c00d010017030103c0c2c1c1e0002034200001a4040d0546000d094584040c40c40c0901d192802086408094030004149154203c1444414020001143e40d6020542543d18245410f510f0714002d42203440382c503011840080c = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 2776599 1250 2775349 2775359
    0x8010e10180b0d0b1006032003041103070f1511010c0c02130e01050c07050105010f08060a02090d02091e0a0b0102070306020c0309060c010603050705040c05090f06040914010f 77
    0x1451103058601c2500d6081c22207140ca0003010151405200315a040f0100502e18004100b4080555100f4411164150001d5140c8080201141c01c243c0030604c0000002000b043c0280c5500108c0b508150002070070921418190001303410b200240e8085001c00c0c0310908002010414080c854420481d161030300100498442182401c1e6440e004060000501d00401e140051a0203101800c0c407800268000481120158220b8215202071340c0e071182c1400041000c0d17040060034000c803805000326070b903c03c01c80d61920300b840b03a0701e483c0a070403012116004540100c0b40d494000c003600481c0e40082c00b0800300d050200c040705294105022a03180200c0c00e000241c1c480794180100e924401040c1c0c01400784a00d19100c0000a410000b0102030a00040100340460366412010b4045012070200001d05540345203080c3e843c2c40c0b010390040b400f0b0b504090307506200641100940b5043c2000380e90424144810100042c21441103030000d00e0310703a01d0003102c103d0b80d106603ca0113060340c490b003a00e81c48503078940e = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 2777849 1250 2776599 2776621
    0x5130603200102060415020d060609050a06030905070303080408090402030a0504050d03110a11070506030103050d0305090106031a0603010e01021909050a030206030103080f090d06020903010c0801050307090207030e06070308010e 100
    0x1e80001e60240e07000c80e021900156405d20000820b046041d001400d05402141440c25509654801400504203110601c094079050a000000301064102003000340b040396a00341c0c6603007082c0700c090203004000d0300282c14030084904480d09900001c00443d0b903032600003840fa0040c81c06035015121486118441c00501e4001d10070342e1040030302030382880c1c201449841c04a070541c1400c49008203601403007070001002d40310100a0350280d807281e005009481040300d00181202c078000c0514030280c1c1002001c00108501c0c28851007414035015004009648203000f090150840380a01c035029072000400b1000304142e8240c01015140ca40e407802d9019980f0402c0100ca083c00d800003030762014003080104002000d240042c0001180c0003441410301c0440c200055050424040c103540340c1c0e030002421002482c0a02ca803149060103401c04032900e504103804251340d9410b034028006400d900048003410716010302002c01c014032008001ea5030f21462032500801400081c4506241c1c0118800450101415 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 2779099 1250 2777849 2777903
    0x40b04060b100e040f0906060b19020102030c0706090201020c0307141504080c010e12120403030314070e090a090f050106030c0b07030804030c030c0b040605060108060303090d02040906020405130603 87
    0x8941d0b2a20300080012007004002c0c8110103417002890b544940d250001111030007050018001c2c1c031007071a02c0e03d4210071104803e4402110000869104004100c134148859082c0c0d055550003280001d103002c101d10043c0d2420060416865061003452070002d00103001b02c4480455403026641843c203603212242200f91402140900c6c0c85a03000103100d10180d501c282e0603042203110007014281e10f014051015400c4c800b41007c442074a94001800f4000e054160141e44c1a0503050341c2910f000d8a001580104103100b06107840748038a40b100081240c0541c03d0b0850051b298112070703000d550100074504a40240a81d220445c0c0b03000369040c0004544088600780c60800e50191071b21015680d550b41d048030348501000d01101800202003a48020461401c0741501c0307948a00340004140c14880005800400001c2c4040c2c4650700400046015888581100d000d85030f041d200411481e00503d0444060b008541250390803d0480c8001d58018074181c0012040f61b01800907010900e140803071034020185 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 2780349 1250 2779099 2779129
    0x3070f060207050d0f0f050c01020c010804020904020909030c030418050a0603021f020718020703020105010b030705071103030c010905030d050a020f030402010c14030318060c0c070608040305040e040b04060b 91
    0x41181c04003c541892028268604d1080f2030a031070b0540c442e581e1030203422440c070080d12650310024050885580411485582c03074001d0074104040e2900d035000032099140144024011081c00021440c800741c20010b603010002090140d0351281e071510201c100b500320041c4809440f6080c180410b46526051080405998001c4d16a2076504c4800401440d8092100448811885510070010f943c0d50030740003e50400e40300000160380c4500e01e040c02400d441040c0c0200803101d8081051000090b00142101c0859520081c054001aa0302001070305500480d15038030015400c2490150030018080300030683e44480b40001c1005031101c034000001c0740a50380146d41000010001f281c055030040300344000040c810041c2108820a040a4600f56000ad1303035211042c04043c50903025400c000d20220740d010904010140c18104246511682c07071103c0d00c80c03041448004004901458862011200513060320301507800715082501d0300119044c012202605c0080c502001d01d042032415080074503c1107 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 2781599 1250 2780349 2780353
    0x60c020a031404060e061c09030302090306091209010e010207080303040b1905010302030c0d02030c0a080303010f05010503040b0a09050709020712030f020901020604110d05060c0309010b0123030703110c0c03070f0602 95
    0xb02c024401d00040b544102140d6224200d61000c0582c0c65507d4000c07010410f110f5900036031102e2400c070507d803820030081d140d500d2a03086007a03102850001d11080d1181c80b407092034808021030700350006074100300c45138020100c075000c00020402032118080c801c6025540580100b4000e0b02e074403009908890081c04004c3d816040409070505500c0c22071510442c4a000034207981c804102000011110b1025602105084d000070004006035842e02400d00010142070038518994600b69031903161107080107080401c8036548401c00e00501400700000006099a400d04566608840c00c291100380203a03100d40d80000c0c284940c130b400c480200c0c000d6501c2d840c0182c00404094440344d6034800e10490081c441d42d041040010b0389404140c08109040c0150b2490320b01a542c0e0805050f41d038299150300e100395050066040366440c1c1d42020100040d030081072114001e84945501c882100070746019200c0d40c0c3c016070f01048160700300c02c000c80c10003075012003141211507450351031001d4240f1252510a100c09a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 2782849 1250 2781599 2781617
    0x108090d080106031a0306070f020708010c0903060906020f160b060a180507030f060603060e061f03050403020a020604060206060108060301060f050405040c050604080607111207031803060c020a03140406 89
    0x3d2400b0340c12821560240109045090001c880032919140084410100082d03503040034001603901070060102404001000748802007001f5005400c070006440028146507941e200c01042c080c00f0790607500101512020940e9601d051620380440c205031000903241c40c2c0c1800082102d910b40041c800d0200c440c26172018142503041e045001c020710780101000141038803a00c9000540c0b0252080d80c01800d001c0d100007d1250034100842c40100004025600403076a25a003000e6054070100c0000c040d061034078020540da03549240890a2601c0300100940100c40482c000c07a072079402240c090320444007071740d5442c0d56070341d60010182030390494402c900480840c54410300080c206900420350050040c440145020b44e10000308000e03a02a40c8030190a4210805102d07480e0b60121806888625020003000004002d103c148a03500c103e04008062240d01e5100100855150280c2e00007180c102604110311484584041d44820302610200c00003100401c0b00d10440c4e074988259800e48000703549203145 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 2784099 1250 2782849 2782859
    0x60c0206030406060302031204140604030302070b070c0e100503010b0405070e010c02010512040506010f06050705030a0f0c02041103090f0102030f070c0804030b0903071203021e030a02040503010504110108090d0801 94
    0x3552010380b080d00d2468072a0000300160302d007086445c00710028202803d59403490480039083c82c5004a4400b80f10b05000c000030408039600082c080c09440e88030f81c481e039840b01e091800d2808401694810003081d080c00703040190305e501c003c0000d400c540c2c05034000c2c089141039008100844504032800710100301d011045540344e51007201d5440f00c2c2d074410b0604524046810924048130341b4102c50071a11a4810001032003440301d100d007900e00a0600381040c038104641669426200e0090000e01000c01c43c0c40d41342d501d002407040d07035042e4015030040d1040003001d83e0588111255401100c8103d0b040c82070307100b41400a101482140d105182c0003642031b0f041c0e01e0702d1f0001c0b03a60b1104100161003190040c440440440c01848241e80a41d0105001f1641c0e1034180c907043c01d1251010765141c00741031051200306403214018821444145902a845a07640d8800c1d000c100280500d800050300740d0300e0a010031040002400d5022480300d02629502c00650340c41500a569001d0362002c2400603e440004200c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 2785349 1250 2784099 2784109
    0x160b0306030a060e060a0b060307050a0e0f0402120403020105010b0903060604020a02010e0607020d12111603030612030207050a090501030302030403080706060332010204050105040b0c010902030706051206010504060c02 96
    0x2400100c0102a101c000d805510790100781c0310041c1c12003d4030b4015005000350a8071511905060b464156016415440d101c50054858003e6242e1201440184442002c007503481404410102c1c1d8000c004640384c2c0b40a0090041101e42200c04801541c030f804008282500504203460701e1043c014024074241d0781c1c40041c0006500043c83c00c40542d0b40700c410b445800078062160b28071440c0c00c2e43c0104607004084000900c0c15902010251002d450200c1103d007001180044a50029401c2200c04481b03680b07240072070050850364402d00916004800078000c0550203d442c50484000f00c401d041c0640e1210712240c1240c90030b200040241e80100010800146490040c05c10240a045c0018580399030b82c950810400101c0d0040707840c2c0c090b0712024400c0010310350f101c0b507880411a0007142050b04110010303045200d503000d506401080450300340249802500180216036019041d50601542d66002a007a60005020890b0002c00b0100040d00c551041c401d8400300d5019503200e280a801c540c003401 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 2786599 1250 2785349 2785351
    0x150906050d080f04030204050c070506060103050c03010303030b030a0503040603140c120103020d030c0c140301141006050705011b02010506030706020f100902040f0603030f0905030109080301050120010c020703060608160b03 98
    0x11803d0000c0c0000000f5940d28070460b80302d00080303284140d81b404a403a207242414001001181454640030512940e60b00c0c580c1a04c2c103403540b60600103295004007000910b00814494000c20314440081c0200380c00d0b606030440345d0000c0c884018224203490301000000c0a014000c0030b40003080000c80104058540050a0f4802c40c0c080c0c10a80c0d0182225100e03110313070042e1900301040180c2c0c9000d1407002800c09104c1c8880080341c100e1540b200342002100c240b90310455104505c2003150220340c60003405003c5d44140f135038145c6003035107000520780040068040c00c0216805031080c081e071680001c005002180c13042d0740a284d1409846801091410344000740281081a42c2040e82d412922080c00e01130311481c405180291901000d0640c0190000d201c6452508082c2c0680d041181000000da07428041d01d056403006d00b48000030ba440e400c07000b00104a002c0007180c040d0700b00f07851301160341c0d00400c2042c10b503401108140015030315510301d52740e2182d0407a08009030f080c1e21201003005860510241d = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 2787849 1250 2786599 2786617
    0x30c08060618270601080105060c07140f090405060601020c01080403080109090c05030a0302060609010b040302090604090201170c04030b0106050c06060d020102100606050c07150c110a03020d0501150906050d08 92
    0xc04002c401640d03c000440c403c201c1084030021a0a01010350b8000740c0a500616040794002c0ca040f010485647c2c41c2c4140e0701c0b0b4900514510b10700c5080507611032034111011a0040c010013424505410010b07641d00341600c445000d0b010740c10804c3c010354800d4511500c40ea4050711201402c0e482d005c030800c020f0007100019280d501080101103810703a405d005800e00c0354000e500420040c145241001510001030b8006000c9040030003003000186c03100c41015a01071400c4a0028a00c2024001600c00f010101480c0d0a03284058080040000c500000741c03041c1d074018481d15180f03a8070746c4c10a41d158030913032003070600b5944540c1c00604203141103d003042d074841c8184140c40c00c40d09046d410605a0b2615081040806c1c03021448000c4402c04001c144000d000344460700c4a00c1c60040000740907098046d5024121503400c04030f0040315101c0135102d034005e590141c609400c996403424005d0003006021480e074281140c1c6400041d404496008413015102e0051a140034026150341d5241d0030741c4203550b4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 2789099 1250 2787849 2787859
    0x20109050402040303170705041406131d010303020f01062303100e0304081209090103140708030403030507050d09030302030904020c1c020721150506060c06070f030c08060618 77
    0x1000c00d241e200c0380003900003188a5100d00b41c0c1842102c2c00700629160080240007048008d005c1000302440300003517003544060a50fa8595200d00c5581e440000388042c1c1c029504d82e10b14090014101d14003100342d28101d034043d90940782610743c010541801c1e500d080c030036003101c8440c1c90861a203122109203071054094000741106c0c0c40710218401d0343c00381d51160341c3c00390250f0004101040300c0403051214136040f04449074041e1420308003c000078003244040c00050b250071003180c0100b0203c10304000c2403019292160031692150355a00d0010316a40c0011001c540600404401c1d140c024011003030340c3c1c2a02c0d8903401030350a001e400418407009402040034040980b141009180100760740101c02c0a03640e100d94060824941440f550402050a01c10740795034105414051340c0c04601d105100c40c2c075592140f400440c85850f800d00241080c0a002042d10050154905011089410444260b50005161818032180403206d405603001c5400f00ea48035040300b410051445070f103032004984021154001c00e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 2790349 1250 2789099 2789117
    0xe0703051e0a06050f010201090507060302030c04030f05010606120b090415060512060a060e0f07050a090b031014010302040803070b1806010303090911040612050601030b0d05060612030a0503130201 87
    0x40780d560340c0d140507600007625580da50010b1002d0708251540c602850342c203000a001e02d013855542d05544610070712500341003503808004a9032131a5868121802141c0180b80b00320302582e03038140b80f402002244142800b180c6100e010304030030340003409001c0300c022000f0b008010303960342c940701c0c2d0510110b0b1052302100607a5608002c50207035510035002c4088142e0000500580c40c10030a04011103e841c4c005030340200030b5008000340019241e0005a1180c1c2902c1d05548840041d0010f64406c01d0b540c1282d02022404010802806a0014a0350403984143d603484074078449440150128880d600030242141c00410280c004600d05104043e04081c05a010901d2880c1c1d05452b1070030034100b07030030031400500014001c02c03040c001401816039000400d4240c4d45803900c0d00b00040c080100740d511103118251110001006a80a68403404440d04087c040c804041501c5c40c1c203544071a03044034803500c506841c0f890101082000010f864901300c098036114903686507044042c16054401c10700b2810000401c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 2791599 1250 2790349 2790391
    0x103110403030801050405090604050703110a0b040602030904110f07060213030501140901060602010b06030601030c0e040e0a0b09060601081f0518070e030a020102071e03081908010905010e070305 86
    0x200090004600039640e84030302d94100f0781040203803800034200300c8c03080d4480d0341440040b4030089800e4045940c80300c6141d081c035003004003043ca600c100360f0181c2d07009900810300260954010006040040c3d04850800c6040b04180060182d809448039a01c2c50000c28040b84001a40944c000c1c45640b280e007a02400c5e50f5a40e5032841e080d1131405078403000c0401001e05110f0000001d005220203000c09000a0011411080201e0440c2c000141240e0425031260081056140141621003840c00040c006100f00000745000c40e0b555803101900325140004600020307402e4074049103041c000c00d0165100842512010322602001925000350b109144260704005040d0fa03c03d448d4011201840039101c0440c0b82036035000e068490308108440c003d801036818500140c1c1e000c2416019200704207944142d1509040401c90720500c15040284025000502140d030306000302d030841105901c03541c6074085030303072200e0240c802d40300c0a103c0c0465500c449804104424001d41100c2e900c030300e900c0d08000d0f9520f218 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 2792849 1250 2791599 2791631
    0x10f0915030e0109050102091201020901050a030c0c02151c021204020d0302070e01030b0105100305040b0402090a060f030b0108010501060203070c0501080a140a05010302010207060c03051803030f0408030d0f0605010804060b0103 100
    0x4128105c034541e42c0002c2c010046e01b090003092080d402583d00071410400e290001034128840c809c54001015076584403014101d010b88613412015070040c00e074821960755901036101980c015070b04c0c0d0f02d048100700100f01042095000310341d19401c40f800e04040d5a2126400d020806c085404201c05500540c480460f410070340558881c000c5020304030400312945024148202408981020340406050604102c045107010b40100e8002380e044e100502c071a61054410801440d450708200401841058004140154a280c040c11b07a0350b600001c0249903607503881680e80744107a02c1c1c01000c841216804024641c0a801456480030f007880010985400a2024800b0314400315a00c2c0900c9980e04018425541d040245801905490801c0040b078516504c01514500951480c14040050340600c0c17201030b1001d1040d9610641403440d4181c440c0c0d194241c20381c682d08400c4404420314603100e019102c0d03220034010f5008403101078588040c552103d440f4440030700710845105051544a507400b031224229 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 2794099 1250 2792849 2792861
    0x903020d080f030907180608061503010f0c020c030f0601081c02010f05090d02120a0903140705090708090d080403090603020915040f0303021005010308040e0702010e01020d0903020c010f0915030e01 87
    0x200001410b40c042c2000d480008001c40d03030120711002c0d0304d41301f824031010000003003080d00500d03003400c0041a0110980040c0c0501200c3c0180341d60941000e448c501c0d000d80000b10100d100401300c0c103a84400e842c03600d0243e500c02d024402d40c407156110243e14010b135400c0040e0f4044415113440042503011460044106883c0145c0c1d00880c1035201c045400e150541c1409032030b21061080da10949060b0f801140200358003010b00002e400209030940000c1701e00d808211250081502a190360300e10b240c401d4011300104000c1703500c0e110500560a07084019481564114451507043e22544200b40c00d08500300d0081d00303c4440309070010b8400c1c5000350100c0b00ca101400090401d4650f5240183c2145002030034aa44201c1c5510b84605050042c00020b45410030b88040c1c0b24094031101c1c05030307511032049003d000070160031251075200044800c0d041419400030100140aa021500c1d0b46100b00e00450b584888600b40b400000d4415a05000d0001100072080c0c09103002d240c08120b12420081107821150703 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 2795349 1250 2794099 2794111
    0x60305011d010507030605010f050904060f14090903040302060a0c03020f1005070e220209010903080408030304170910140702030102040b0d0c0207060c02011407060504050106030605060301060302010903020d080f03 94
    0x31090710000c0c0805090044075030040041c0ba05201d0b5518103030010741032508030710840c810b0020200705946a600c07254801c81c010120100c4500d2180d030f49170400f42c494012503400b14004c015072000a181148000121800c80303074041d00d083d10342040c089003264400c080c880100e04500030741020020300c0d0003c219644042e00c00a8002a841c28a00000340036800000a10f0740203816088030004060307a04a840252007442c4580540e6503641c40b00100c91903806600700030710012002c100441e060300c000000d584580e00c01c213407400d400c0c10074a0b0300b680c460103460382407035000318007440603901540704e021030351007a4020b5403141d400c10119900207800da030800c0e0042c2c041c1810124a01c01070004602502a441d00240003a0100b6410080c004008400340c00029040c081030070005107204104e01c01b22050b8070f8101c2c90812144c202450024041c1040c0d2001b039514a06200210308030340380602c1140708a0303a058460007002890755080c4038041d10300740b00030348442d08c042c80030a0a10360100f0003144a08 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 2796599 1250 2795349 2795381
    0x1a0d03030c020c0f010207031211030c030c060a0204230f0301090b090c120604140309040603060504120503060604032009070c140a0809060d0e0d0201020703080a0507050403080304030306030501 85
    0x342160074024503101e001119140700d40d0200d81c6600043e6000b00e05401034031741060755120401400c41060302c1d42407007060b00342813620001556000050001c0090a0f051100800f52a981c0c0c4603259030300240e010381d0064140c2c203130a100c03103441c80c135100c0700c50b41558603400f60403010301407101d0740001c0c02c54210354010764090000c8400c0114029007801300050340c01c005c0790440300a0101928003596080020b04c010942c41001c01c086445200130020b461420f03030002c0052002645924084000d00390035201140c890f1078201e0482c03841409001a07034458940a003003d828607187d80c46034406000319408208070300b1794034884441d0644610045512405080d11100c0c416850ba1421440c46410401e400c4a00d4020001000000e4060400c641080008441c0a07032030b006c604c425100203140461701800144120711400d41c4c103a8064002e4003400740252107240c02c80c4d50b400159015236a08a41d140c000030000c0000b132000401d5a03000e0750b000760091070009502ca40301d9807280d084510740703842c0210340 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 2797849 1250 2796599 2796611
    0x6060b09040b030a050d0c03020c0a060f180b090d03050702040207050303010e0a020304050309010e030f0706030606020115050d0602160503070606150509030705090903130b0703090608070e01031a0d0303 89
    0x181060b0040d0121014180c0c002d00e100c09007074540030f41b1004903181c0c000402040840700028144200111a4080001050b1300841542ca0001800284a006885010500070170900110040202900d0111400410264034084e50a410040e4407800e0031300490504c0824012000561210300c0030305500c4d4811801103a481d4101444035040c08401007411084c18010001c000000d1400720940342040402e080095485d480358000a040031801d41000025104580c00043c10700e90507046a000c4a0194000704484c055200300b01e2010f4413940501600030070307034412210000d40c80740c3c028400300302081410103134802c090b62000c0c01c550113910140c86158849005100a01c4002c0d41803070244400c0c1032448ca0001050003181d00c8244d64821188103501500005100000c2402200d00201c03581d2081000a0388540340d09465405c01e400540000c0c00000010400d54080c280a5009100c50340f1111180300d140b00044018080c1030f480c2a5000c154128840b1090b225990300110282c884e450106032 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 2799099 1250 2797849 2797867
    0x3050106030506090a08120604060306050403020109020f0109060816050408030408030a090902030108060402011d06040305150105061c0902040b040207050606040e0d0f0302030901020405030703030207170606130b0a0306060b 98
    0x1074824050480c2c6145e40022000b400003a44040459035504080c103440d440c280c0e9007400090060203d94005000079061008001c101607040d44940c3c0064422540c41c841c40d5a1100111422100c07400365501081000002c911100a455a01411003125107072152070140c494050501710b0700181c0c0000040d030f101003502c3e8031031a040074450000d0318030b5450841c01c5602d4154166620140500302034180084a00701403c076102815042c8540a00a020f1684c1c45607030b4030b0310599030203480c2858608000c2002c0081620303d010812030b03030050104025021591946805413004101000c001c03a8429915650b184298980340040e041645c0140050074452606500784001e4070f035081002982c0360055482e10b445d01d60400301d10341c80c2d5001072800680b240c0d19840054028807894128540c14410000000701f0182c1c0003034900d0039148155080b41c0e0758032004640c0c07130f911b00301a10303165800361001e550a0b104015540c858100c0c03103c01041c1910321a81c9071038440c122056a041013004090004460034 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 2800349 1250 2799099 2799103
    0x1203090311030105060d080901030b1e0901120c030209090f01050106050406030b03010603030807050702060403050102040b0301082407050f0d0c0306050f01020c03060103060902060d051f090b03070306020307050c030301030501060305 102
    0x307656506034024410b9140c10340004884207541c81c00200103140c08a04440d081c1d101e41e01c01c880b9284003805042461200c041194901111008410b2044840c180045440c00d900c0c95566401580303c3e40d180c240f24116802c218041000611000152140c0c45500e0f200351002d00030b0320300a140c55118035903501d0038404010140c1c2c61001005001c0da041410070000294002e0741c0e0f651081161600540780d03410351000070454030840c2c3c00905a07600118021802d0300b611002036040722054011101100407a108020f0082e980540500712501960002646079014000600d08a190301061500e407042c0c41b481001150407aa0328000020360700c01041c0010b003091a00d000e01d0303000c240028441821800d000943d2840305000c0204400d48948011003191210004e50341050010304051115152a44048030643c001ca420810000e450110008440c89a88500615a030014010700601c40c00d540b00c02e0065400a0018804c003c0704103c0d52032030510a2000c0c5010b1031080d80081092440c500f8028 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 2801599 1250 2800349 2800373
    0xa0506010203070f110d0203070801050f10030503040b0906070803070801141509040c14030c07060501050603010b0313030207080a0c080106140a03140a0206030703090b0a0506030309040b040612030903 88
    0xa41558400c11180e00859054901207548690045808640e24000d5020130ba0a21816400a4251003810310100d000c0106410083c4074915001038030301c1c0d541e680d02d0403500302d0105100c040c149070400c000501c6407a036400000c01810301c001d0207080c5400741c20303516020185d104884001c0001d000b640144100442d4640a03015186e08642c0c03080c0714100786410344080d118000b480341c840c0d56540c2000f56172074028009002007004140e0301988900c1c100030310914550000504650030391070000040340e10b04d0b202040e02d060b500d40350311843c1036599080c991881c040801c0d806a06512030104000cc0d0f401041000341c15075442042d45000d114034200087e82510203076000782c110349004104000c541e0316100d402d4401c0300e80050501c1710784810a20103608000c6500342c080d420810001c10801d890750140c21400019218a00002d80b5507070303d8000f507080382c105031441641600108001a8189060340105003241001000055050f80d00c1500b0f50111180140444c040b4820303150410500030710380c1842c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 2802849 1250 2801599 2801611
    0x3040605060102031918031211070801090b010306050a140705040e16020a030f03020c01050c0a17060307050d060b06030103030c0c06020111030f0703020d0e030c0708010603080d020c030706140a05 86
    0x2141820b0003590b0010003402c6030103151040146c0d40118840300080c0302c40c1e800041d5040300f140500c400040400600120321516400c5043c864108000391241052040c0a01c058001d0356500c416400c3d42d4580020302005804480078545078034041741000c01d14448140078900640b1810b60b00c502d8000440c11a0400170b011034040310720115141c02c100d07004200344500303550524100c0040b04041106400902071700e4080441503191104002c0c49506040c002c00c40d802c1e946d156000108031000085c00b80220031960f40e50142c001040c1006136007441140410070b140700c0c80c0701246410164011921541003640107600151420b506507003842203502c4510082c0000c0c0c4000d1081e45401d24804440d07201c080c0140e5051107680000440d0a4820b80c19607603103941420342131000d640d003503100c55601c0d004440350030410b00445500194054051103000100d03540500381500784624405684001e41244401449038001002840d0000d001480359040c4140d000c08034000901300080594101d580003800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 2804099 1250 2802849 2802853
    0x2010606030e0705010305060102100c0e010e030607020d0509010207080102030a05070e030304030302060105010f0e030105090c041112040609020f060a03020c0610031a04030216080106030605060103020a09090203040203030405090103060203040605060102 111
    0x442c010280031480038280c580a00f00840c45445070b8004030300c0e1140303180f410022145040d125a9035264070640c200320041c400d9035004010210130b02010786035141581c031980942e109440b0303448904e00410180c00d44c60300c1401511070256842c0401e81c2613038401c48400a40b140d850301003080c1990014090240b28400358002c60401c0d0071554003954070b020600aa5040c041c00340d400d1402144980d00d0080c02c400041e001744800d040c5456019941d91030f81c48041c0c0310740e0404d2a130507068030b000d80c161403810310440e0003a10240c6a030344608005040301c0e402642c00078000311308204183c03100300040c034032002c0b103a80040c3d40b03d00e110b2803d03080000c00380c4a2100f9080c03824042011418a86040320b40f0303013a90001100b00e84070340c030b0260f281c905003010b40b200c50b4548401c0040d80c07510641c01417045034041d1200f48001c1c2c1d00c0c54011070403440f828080f1008281c4006c0240310901b06c80d8043d541c0300f071020701100c1c5070589481c0001c4481400368000c40d03074240c00200b00800c00c6880e009154000000f800 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 2805349 1250 2804099 2804111
    0x71407090207151802040207030c050606010201020a0c03080a0e01050f041103060106050904020d090203010c180509010609031b0b0d09020112050105060d0b060d020c031902060105030a0803060105090307090c0201060603 96
    0x143d10210300c541e4070450714005880da50b10351045445012242c0000e0390040c0115a6158145409003081e0031007041944c1e5402490005406540103008842c00d1990700c0d40ea80e814900c44d40d07029600e401015001c035040c503a44500815034180c00740b16041c0900c110100410b40c81c580707450402401849140d64034002c0c2c21010040040b0b072f8104094403410041202e0250301c611041041c0c0000703022489002e907056003002c4031b4202c8960004076a00400d202c0c2c40400c1c1c1d403191601d05000107038000b0f104140005010b05070400c0850a541e103d408000004070080c8812036651540724482d4021840301c1c47d2041e91850035204540e001142c80c94840f00d1000144515850b1400050190040b0104859410b4951a1490040d6100340c202d4249410080b0115210651011a659a03401644c411004602c048011002072400010700604a035001030003407005154503039540540f0341020708130606010043c05a091300341e40034860b0358050041c0141c0040e211072403400003401d49260b64841800c1c5498a0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 2806599 1250 2805349 2805353
    0x61003030203041703090a030c0501091a030103020103050915040305030601080a050709061101060803070c090507090803090d0606180c090909050316020307030c030503030609070516020907050d02071407090207 92
    0x80159411564812580904d100c40c402d14141188185645981e100e1055940401008808503841040d14400e80c0c407001c042d0307120141503407071207070340264550400403d00c01000158070075081a40d100c1d000d101542c038001c01f20b03241222400707015030342240030610102c1080301e1355034000c99450f0712085140050056081450014003411014041d41003041040e0308803024070f0000350402d000400c1c1c50005c032580c0c3c1c04c0c0c50402c1b21011105000b00c0035000c3c20311002c1101284240165010343d14844080c40c50054080104140136000c804100c4880d0384410000480c5100c41024050181c107001d0046104402290028a40c03501c50300559944d038900342c580c802145001040c1e903542058800840d0702c0d001c0c40d000013440c1007480d030b20007424080340342c10200030404044007a600600007034172420400d0326884002d5504d801002060101c2c195025480b102601e02092055040310b603038201a80b40c1100003c00100742e0b4402103081daa10316160360b144115010401220008100820003181031008607 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 2807849 1250 2806599 2806603
    0xb0702010e09010e0f100b0d06140d02011b05010f0501060302031501020f120d06080f0a200d020603060112050a0b01081605040b0c01150303170601090e0601030c1709010603050610030302 82
    0x707000540c0380c80c80305c0d001880030003408441d240a0a0300c551070946651001008030087c112500030b082c0080d00480b40a42d850030400000b01c0b26580c141c4400ca050883c000a10540205510f810f03615036403074040d04a0041900d1141c540a071800742d80159407450018070569400a05100036811507200910700141c1c00c0340420011602448840213030342d00e81c1401c0720705016000702e400403405401048a115850b4400054240805104000351285c0000f4010100d0008560550143d000300402c8111401840c00070700665211605062147c04005c0021020701210340c200c618040142d5112130301c44140d03820481c0c4551103c0c00301c01c1c4440200713403880d00400b00c1c0a2481121460300010800c2d2b580481c0070b40010303994050740400e080078640d07213050081c100e82d00c01200715807115560700480c44552164034940301f0380b56185103071600398840c1c00044008010041580003000010001420b07203003c410750050045114000200301c150450401d80c0c103107032010b441d516000241c103008000103500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 2809099 1250 2807849 2807851
    0x20409060c03140c09040207021906050703091401080a020708070b01060908010b0306010803070305030714030405060a0c03020306010905100203040308120103030905030303040c09050612030d060f0603090209010e0403050f03010b0702010e09010e 107
    0x100f46c0307016865001600c00f0800c4c9444e1070070303860100305000c140410322940c08000f42015900030355480710010b07a07900b00043d440c01c103103903800c1c0081c0034000010130a40342c54000f8102c0d94030500700246032040a071601d015419003a000500040c3c001441081550024000c42c500408100c0242c9034075450102010f55a1080710001000d002011000a901d20300075181062000102e502040c4c0d00d290601d4050b4581d0030480c0c07103c068524102d0f496441c284a4801d4030f11500040e118918460304280800800315044103041301180f20420004c00094649405000001380407201145c03154110f01c2e000c1d0844031aa04542e000358000d008000100d848114103804407008440d0020b034a86400d00822445958242065000d01c00021000070045e03061380244104c1d200712441d005141d803a000106d003540e604000103580000c20400601081c404405426002071003400c0c19480c1ca08504024161500b09a2000f0409000450000c06650304220b81c900c0381c82c01284c403514198140107288c0d2901030 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 2810349 1250 2809099 2809117
    0x2040e01050904020303090a0b0a0305070305090303040314090604090b0405010b07150e0703080a050304050d02070510050306040204030606030305040812040308040308070201020f0106080717060103080901050307020109020409060c03140c 104
    0x1c46103000c0350135500c013401100d9282c040038050030b01d025116101d003000e40c0d00051101c00007034900f00004010714824030440b03009501110145103503480d2500d040350205411591110492000c0003c1149580c48100401c0117281d07206012544c8894803041000b180d105070301000300d06000704141400100880d503070b00a1560160300000d0203081003801c1510302807003070704014413400d40060340112581e0040003540c45280304500321b03040030b1110a4101d0326200300c0c0c426075030400b420882c0b528095000314042c0d40d0100006d000141880d030380745c407400203403020f030340c010317004108001400d004c0580700b8042c3c4d0007880007034040240351500d0766858a02c01c0c803070381c800903198140c049895021607100744518900b00d040340c2d000b441101d40380c003840c41c1c6a41d02c1e031050301c0d461051445040e1007001d000c21554100c1c0d8229807560304000740d8000566803a8402805070085550707480c0c3c0c2130016a034900c07625070202d01032000003c000007500000740c11581000d252240c208005010488010a154210358400c4 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 2811599 1250 2810349 2810359
    0x10509010302011107050a0308040320060a05090d0203030307030606020706080601050403030302030603010f090803010503100e0c040b011205010602060a06080328050c010204030506040302060c0a0801140d05010f1d0102040e0105 100
    0x10b104000c8a500317220b03481d0801c60b80b00204410000038004610302800a0f00d004051203881e0314250705140380004950541b20f83c0003207080c441007007034030301a501030a00000003a007100c070110465030020341141d10031075010b0042030b078400003400110340c10000c1002404103030800003058101040040c009000724030000301050f40000020324192029042452103413880401400301911030303e415a00e68000b40505400303440340c2078941d100c80e092401407200c0c41d0010740c098014103411500788009003050107621410b1040151700310564022ba4440c8038001d0085a002d8a01404d1208064055441c0c80c0d002c204254070a1105004404800070b4590408a041450f01e03c112041c03c000d480f1070050900610300d80d427020400000303000c000b25107184120310943c01da60b91a5610746045400b40a172000000c00100d0050042c00010501c14600350003400040ca1808540c0160756424203481d1007400e48030905482c1c42d04c92106d0000d0001a4021031131180c025030505040001c101c200450501c0348500c11 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 2812849 1250 2811599 2811617
    0x708070c0503010518010b060a05040e0402040605060703030902040b0a03150509010e070b070606060302030c030a020702040207020406080c0f12100906060305070608180303040b040f15150501080f01050901030201 93
    0x8020340003403004100240081c003480c03404400b04030b21800b10000c0c040941d428145810300c985400422200950b1040d20340c6c2c1d0a041c245565402203c900400880e0001e90b14180820517a0369032010700102c170320a607804200380c0910b105110544518815041c0522208107060000403441d00038070740c0341c4454440010300350b55043e1100740542404442c08200d40207519010409401103402024140c0c0645801d00c1031558680d8114224402140c040801040038008600e2540d102d1b002842c0660000304050304040e0141c00107412244168404042640461b85203d41c900341b08182c00d4540030211180750040c15118000c54035004158094130400fa6a0f408080030041d0710743c001d030080c54000c8110780fa00c40d26003170050600f01e4196400c10300c000031560740d0085414000100c0748165441031182403035071100d6403540e4000401040884000300c4981c02599034003024420409010a014142c18050b894400050100b01014110b0503d41503064014400da840b800001c60440c1e5081ca413058071 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 2814099 1250 2812849 2812853
    0x402060c0703150c0206060303040b0a050703090e010b030105012303060409050304030803040311060108070f0302010509010c06090501051806010302030705060a05040b0a0804060b04050403090b030903040e090d030c090605070807 100
    0x820519401c0104507036204482c0f00e28469682e0b00140048403981c00700c510f00e07240c210030182e1324003482c89005505031041003214a0360740701d0400ba05010b07100307040828015803190552100214244c0086241980100040000390382c401d10596951038049892010404c80c84a80301d694800140441d000e00e840c1c441d4041081010800c40e03000f50b41200d02141c44e81040c1c40c0080c0560b8000e8a50883c42c4070301400413031548800701d1010112550328110f541103a28660041d0390315005040010705003d0402c030940081030950040240d282c0c824000040c0d113181c0040f04080c100100700500b500740d40080c0061005880000751141651012521580c480b009584111024821a04545c240721004914602c0041d005101d6a0107503101d0b580c14041d10100c1c4090108551041718003400049480804104140c0164029034001d80f40304283c030300d00b54458414006210064880c0b441a81c845080400c45540c144140383d02c400d40303482c080602c1d80c90124020114010740202070b124200008914003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 2815349 1250 2814099 2814103
    0x804020f0d06090606090606050f0a08070e030a0609020406140306190e070909030801050402030c0d0504020303040506071b0b0406090303030510050915030106080715030b0411161b030201080402060c 87
    0x251541c0080c042c0300c0f8004a1030103d0180c81179108680e859820700c03030081022806241503a0600030750700b03045401c20080070000c5521840181c41d00b024880102c887c09050385040c0880315000e401028041190030591050004890032680220019140f41d560000203681c040303091504002c0311850007000e081e10f000c4070340080c0300030b07444034820380300306000000e11b0046074001d1002d483c003031b17142d08004d42c0c4c4c1c1f00d083c0400d03413004680d03441c01700c201000f2041105000c0e5001c15000707400030302124280703525100403401035400f280c42943d00303042003851110034452100c0360300c1c05002d40702d00680c14a0314001c000f0705100740901006040c141c0340c600246020800b0007029006220080002c00c003800d040a400010883c103520040c025400d003000400c801d00c1c0021244122400440480a031050307083e0224000d00c045410180d100352100742a0760740101e98006060030001500314122180c0251508545074120181c461841c80c440b1407003000540e0b04480c07503651081d010f640d020740d25918010814 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 2816599 1250 2815349 2815369
    0x3020316030207051504050706020106060315031b0b0c1509010b030604020904080c010c03051501020c01020c060a020703050d050c070608040512070f02090103150b0a0803070311070f0605070c06050a0804020f 91
    0x36500c05d00c00350400041c003100148540803951240c00030002180c03259001c40036141c1000d030500c034581c140a0100700003030020300c0798962000f40008880788607855100c1e980991340400c1d24a400795001303e1120000c101090b14181d04132480000070442803880d800401e44508006101901c540f5800303001800740100c25080303030fa084003032200030044c0054061000e401020180d07034019440034102c072201055400001c0401a008051300181030054507942000900c0d40036181c4c02c0f0843c0200303100000081d01c200003403008045261201d5481e0404001c40b40d00c1c2580300d5000200300140ba400340f1010600c0030070300ca80b900001c4003415030384d880789080415903d40c0302d08000750020b000d0400002440601c4d0082c950144164505009215105081002c800968060041c19400800001c40002e01030486c5003080d20062042e9010a41d6803113034079642c0a80d550100d00417030000a255010403602c2407040000e0000c07401d1060500c4400d4000400c0c00c840104028000d5008011140c003996a00341c1070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 2817849 1250 2816599 2816623
    0x706050a050f0d020a09050d0b0402040c020102090a03050703050d05040b03060603060109030506100306050a020f040e0603010605090708040201030c0512040201110709020d060305060709050d060b0406051005190302031603020705 100
    0xe40d9031849400c03140c000070340c00250003c0001b4071082020441d4036105c0300c8200140d40080ca40503e030740719074003000300030128130b41d0500a40d0b50810004620f921081e000100640c040c0c0c02038902b00c2e00d5424028181454408000c04008013000305112100c0c8500543c0d42111003600c00588175520500183c81c030042d03a4002038a40d104620800c101d100801600c0780580740700f014180300f951181c0d100035007a40150b404c45403c0c41c80c04d00080c000c03469407070075041e13120400800100310260b64401103101100240c845a0008a01000700000d65802d801042101e05c101c1c2b074540e203000d43c903603007947c64a0b1014000034100002a150584091810032007803003c0c0501c004119520511a4a0f03403001b0641c0e84400c81c2c1600900c00083c178114080c402d60303001c6a00140002110085540d9004010201d191005511a50f60040811141c0f03620f24003000072412500c40d15a512510400700942060400d40300301050300410401c0b4020049207004105444913040160315030f116171400e503091226030001 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 2819099 1250 2817849 2817877
    0x7120201020312011701060801060501050a0e0f0d030507060c0e1c02150a03020403020a05100804030503040503040e01090b04050603010b060a140904020f04030213050402010512041e05031b030c0706050a05 90
    0x4540f601980550146001e1172200800c0001e9950126a00382e0741d81e4450140810400d100007008a0300540c0c45a1181c0030050409461004140000303203460314100007940001e80c0810341d101000501d214a010001c20b50030702c044d409028000141a02c80020b62850758024444288000c546680c4036004a5207424189261280042600180290018441a840381440701c400290740d0400c6400441700120541da03290305981d89480c02d4030f580e80f010b40111141d2204100000d80c0d80708000810b030203400c0c8960003180c10140102044107441000d04181d00c07907407400d40003605554444c01200c013283d400b420001c8007075001d041044101c3c003030380d080d842c1c015000140c1d521a41030040014802c1e45d108980b00815043c40e0601802141d030119802400b1036410044005c018000e04200c0d6030207442114104801c1124501c50044400120701c103c4603944041184114a2400d0b45c1c90100144c01c280250b040ca00d4074036246582e01c120380726500c00d02400052120800344a601221400048140 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 2820349 1250 2819099 2819101
    0x50601060206060315040c0509070207180204050a090e0606010807030b04090b040210140d02070206070203010903030509010f020702010e06130e010b03010602010b0d05030703080c090a0308030613050907120201020312 95
    0x14010b51200e6007218251310a001e02c01d00381011000e0310004601a540001d07610501c2404c107070920801640c081c2911055100c0d0410004004880f01900c00d00904140d1001d07031558544001d110454100d60005600c50b400d008014001c07045c00031b001a8040c2d0240391403142d41d250070606400906645402d40e8105040c100c907034041c0a42194501d0149200340c6503902c0050814904561041e58101121801c207070030003800080d0005074000d0302003503000400d001e05d00417080d030000303084643c15903048010036120700c2000320400e420f06ca40c41c00c0341c108000079454440554002031070b02d101c0055852052a0205043c05683c44403c00c1e0b002914402d00046d80e0b658407203081c07148580007403181900640c00d00c500c4003818144194500c080d10b602c00003c505000c8943e5064504070030007840c10070350000038030400000d83d41e0540c144000b1405074001c2d40d524100b102c281f0501c0c490350120382c030301d0600700402d01058000c0027800c0700813101000e0180984500d039100403421449012000000030340180 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 2821599 1250 2820349 2820359
    0x100b0a0305090c03030a02060408030402040f05090c13060f060513170a05010510030309030818040c030c02010b030705010504030f06020403060203040b0106020c0102070503030d0b1c030206070909050124020109050601 95
    0x1500c818050301c400c40c00c4400f1044100c0c1010b40e6441110240f00041c0c2040c4040380000300316402031504148010008510a01d1322000742086035002c0f5022401980102d0b060b40d81030601c2070386521503040502062283d80c1c14182801d03440d81851155008002c0006400f0361941d00c034060090240c00c550721000000f00383c5181032035980001920560300c030752814002c40d401c00d105031900c4085981c10713103982e0f04440c5507854042c029000070501c0c88100464241128055595224901640070305403070009076072855a000a084078500700300b02d4081e512103030091086070303040300907142182c2e4440300c16090090645003080290040da0f00042c1010300210910003003000c1d0700100e9060340d291350b084580b0300101500480e40ca20151281d150150000c22201020b032107180c2050080810150124810514076200c1e0002a10700700c1c015001a0481d90500090301d41c0700840c4002001000c01c1070205504120168091000c1c00c403800717a6000e01e64180310240e44c000c0d0005580740e508102515125a914 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 2822849 1250 2821599 2821601
    0x20306010b03100e0f0a0902010201020904060e0907080304050607020d050f0607030603060c0302031e06010e030f0a030305010f080304120c120b0103020103050105060c0703021005040509010603021201050d080909100b0a03 97
    0x2030707907403800d0b04580310750104640c0c5a21100c0b51103040c1c5d090400203a030f10341214075401030544080a0381155000c0110710429100c074000c1000130414411580070600d4400c43d0182403076030b550040d400329001040200070540d10723071054440c0550101c07950003444d400c0e864035034607126009403205c1c2c950217604100103100e60564410000c60780035800c00e0003200c410076001c40c2240b004417441c00e1700d800c220302128102a9070900c001d40c00f00303040c1001072803703031540e00091804920844034005070744403004083c200f43d0b050107103034010010724101e00203181c00c00c003030b1940b2801140600610141c04031a0383d0700380002400800010101c0c1c9000c6500d1003079030f0600a021110902041c0d01180c28100006541e080c403000b20b81000c012840905a442c1c11344c4d08004a030385421450208010041c0404625a514543d10900038422501c0050350b5400e462803076004642c1c1644500c0c800d01c0400b8043e4003082522088038a20002102d0058565580025020440c10b150300718620712034020501c10005501 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 2824099 1250 2822849 2822851
    0x2070c0602070609060c0b18010e0a060b0a06090302030601090905070905150301050c030705090f0f0301020a02030703020606010f09090510090c020304180207050d0c050a02041503031e08060d0203030403020306010b03 95
    0xf581c1d41e44030002c2e220070050b94100c010310401001c80020800003510140d40796440c00c0140340800001c624600100c000760700e0030348001002e0b105256506141e480c41c1c034266180000401050501c184000d18540000381c940d40144600b030b5459868012400400005200300f00203801c1461041203282400003028002c1e0075103500440c000e61074240072030b0304141d0300c9060724802d282580e255890182070a060204513101c800d2180d4200c41030200e2141c2c16a4203001030031134042030b07500642d100d000505000b031400c0c50140c00349041c040c4003500e154845a03c0850b00090718001000800c86858198404114008581c40811344a1401203000f040c10350110051040b2090481030a0b90200c507184040100c3c0300c0c041d00101a82d02c10707190030302c045010744001c0742c185005605841e0b900c032140d00841d00740c4036109414165000380d104144101034200c00203240400046c200315645401607140a000814044c001300c1c441d48050344500c0440d0780c03c0040340c01840d4050155550355071b40d40c00300c2c1c8803900 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 2825349 1250 2824099 2824109
    0x203010c0c051b03030d0b0612130209070801080a0602070f050a03110c0307050d0f0206070618060606080f010303030506030a020d2607080403020402030606070b07020703030206101a0306010302070c060207 90
    0x1e1003c1d03041803080700b86801201c128008005e980740c0f4810010440c02403903001d480680040b4180100d01c510180240c0151081450b0f02d1a16100708c05813040007121000206440c05000e48040180070031680001c051900320742c44640141d554116050040343c4014105009285200f102489010550702c50f07011140d51480008030f4107451204020180c4816260090741d03081102c4010700808600c400b4030f00d07140745001400840ca000700e079440712025a5245201c0321210b00340042c2807810041c181c441c0b80010802850010000e042503400c00807200010320001d4101500e40003c5241e40d5801d01910302040d034010720f49062441c091070004880784005907040714011140d46040c5c47d02000784200c9109d40e034080c018900c0c00d8255400c000c02900003910a580103482413100c44006004003903118050512074000341100b62440c90000e1404600030542c50301c104110200b0050044111403080140080480c0e06132240d8481004800030700444901510541591000207895074021076a40c0a642c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 2826599 1250 2825349 2825353
    0x3090a05190203100f0e03070609110402030c070f06230f01060801030b040303050901060b1b010b010306180b0301020c030301120302070504140f0703062403050f09030301050105030709030203010c0c05 88
    0x40d5810001040c2a690748080c0d099045a01c404d100c209103035000b841d05c15464a000074480c120034029a01c3c0d904211421074241d40c3d240780305024094801c0c8a2105100c003190190702d54600798281903141d010f4a000241360610060020003007040e43c2d00144504880305038420b0b400c440a8204081100c003d403030418119015100102c1c00b00d00c1003141a050302c0c0c1003d048405c9499641e0120b00400c0c0040c9070b5022956101d0b00810101441c80c010208907144e8900302c2081c001010345682152881c0c40300a05143c03030100c0c00c11000428104002e032000c1031400c000b03483d0004030301080c068800c1aa805641d07000000020960f0340700e60130f040c000c42d4041d43c00c8502150302da8003400112101300000080d50f002d5440055075040c00f4803010b030f03401003191074041520740d41d4450303031407c1e0401a00a010100414010b400c112541072203143c0e40240014190342040c1040c1d4142d45c4c0324070040c000c42d4100100000024403040c0540d04c41e000440d8040c008100c41403113000d000300031b0070201c0c104507818 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 2827849 1250 2826599 2826613
    0x30c0f210702040b04020a0327050a1421030103030e030105190902010e06040306060f0603090302030306100519050d0e011a190b040905040611091e0109080f010209040e0a080901050d09060203090a05 87
    0x5010035480d031001b0598082c0090108030300035200e1710900c2542514003100c80c4937000801d070001c569038010480d102da4120459840794154a0050844180c22421a0080e031500c8100842c103080c0c1c0c241010886a200400511107005000489070007622400d01d50300003100090000803c0000e40c44070085400c48280820ba064071100101c00303072816008098016132040c804603c04e442d1184034a1184045800e00c24070300104407052602a82850b003111000c01c1c40400c43d1170f11000a8000d540c0710500010007000a602071403028000740941001e52400790005120b0800601d0303501180c01d02a000880f62607480300d59440074500a890308840444040e800c01a01426085c0100c0950b0018140106503109500e61503401700981d10340002c1d41e60400c6021807002132001000d000b45124010f000300050fa0701c0c01040300703000c103940641400c04020f6100030380e140c0100722404d040c4d4043c0b8009181807999200c0785c12444020703003c80d20300a48106d02c000140090400b0008200c0c1c0814440d000751820 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 2829099 1250 2827849 2827901
    0x20306070203070b061302040302090a06080d020304050105180609060c0105072604020108060102190b0f0f040b0114030a06060608060103050c0a0905060304020310060305030c0f210702040b04020a03 87
    0x2ca000e40400108401c0c0c2400110715181b0704401020090a0507070001418207680740c00280c2091030a0b941070341070a03900c2f8402c1c0b04101c4148241004041c0c54002945000d14005c002481441070700c1c25018201c010310391010160b680c010403a900e400b0014180c60b210039503010143e0003810261444030101c1c01d40c242d082c941c4444041001f944004070903c0b030b241e55845400655441600030540e038118003a40d4407094060740d800c030b40901e2027402150700a00c0e0b8a042510484902d05c0a04119010b1070306204110000d03401404150544020240c0c1d414103154250101e850081d00a030020003003828040d002c11025441084070b48201001d903424049515101240700c07a5100d040c1c0c00100141c0640401d0001c0d00384000110340052001c0c1c1103030008a040600c003011100365401c203e6480d040081c1c2c0c1c05074140d00300306d1000e03100311200140000b20100440302c0e030001040300c0050340600c0c001c41c00000359900ca900802580718050002d5503500709600c00240140b0001504c4102c40074a0200b03910 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 2830349 1250 2829099 2829103
    0x120306060305011805070e060415030e01050402030c010c03090503031908060d050705010302070c0906080d08070e0102060402010804061d0601060906090305030403030e0d0503070503090406060305060d0303020c03160f0203060702 100
    0x20403140101107001d0010101308000c40035020091215040c01140102d01010340c4810340200014801120124049610502c0c0103064842e52200950140e04041c03d00015075030104040c280c001c000d0070004001621403a050760300c0155644100d501d03000100386483d421072001035040101105030b544415660340c580030041209103103407004d055035010350011300641d406030f070060042034006e58105070740c40d540d0010b440c00d03140b00c0e80022a81c0d4101e60515544540c003e403800350003145c0c904003190344100c000d0000755205c000606c06070400422002041c14401d1581c0a92440306400c0340140d00780d400d10801c0b541e117130000c2c030540300007544054000a0f02841400e0b80b60540c0e0b070000c060f40c503051454408482c1c950744d4418541d030002c0a00d2003880000d104000030b091452250001c0c68491420f801080111406035101205060a0004112040d554040c22a48081e411b050041e1206164480141345029048021049401d0407030043c0c103000d2200128401c40344200e0403201ea9544219081ba = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 2831599 1250 2830349 2830351
    0x10302010305090307150209031204090204050a060507080906030604020c0a050d081006050d1a0a09060e10030201020c010804080c01060305030c060703142a0307030207020907020304060c060203060a0f03120306060305 95
    0x146c42694242c41c09252103002d50000c000300c0d40c1c0201102c0040713407011024503642e4043c0c0d004052240d80085c0030080c9050030004000146810705005082010540f984100c84c46030500152149400000007000c540d101d030305540301c1900e250101c88001c4140e15055582c4d0029030b0410000c50141000a035101111601010650b00e00b941c1d2a17080c00b2540c1e05401c0600806042d12006201c50611000c09488807010b0380c000b45440c1c032000c01e41500c2c1102d00c00e142500139002e074418031680d0302e040c03001d41d80015011407005420718010810b035803542000c00041c040c0b41070344d980c1942000c4000050140020141c030780400d407070703041d6980c50307d8004040d0304607041c0701021158480e0340c0c00000da400011226510701c1064400c0b11180030382446e00c86d800f256000f03c2c0c0000c0420b03408544030066041c4a039210b60320425900040d8503240c103000024004525035107004003600c3d0000005000c64407192840d90042421240c603d400b02d0b124075000250300003100c10381c3c00091a080001030039070710a004e02 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 2832849 1250 2831599 2831603
    0x307020316020303160c090b060f030103030804020a080d09030611040305070e0406060e0115020c0111060c0c0a0501020705030a0210050609010e09010213031401060518010b07020a0e07020303010302010305090307 93
    0x40d45081ca44565004015180a00c1a07034503000900c0350800c220b5414440000301d61041d21042c01450400400f0b07411075104090003030144e00c082c41001c04602d01c86003100d05590300740c1031500300c030390b120300c006203160a10b504481d400c1e000700c440c8810010380150040b021b4a2241c401400f0102540d81028a54040d920003c0d11075071111744104081c1c0c440040c034a400501415001c17900070740741c0c494402000e1080e8044c0b40400314035541c84071480d505011061004209180007441d60003120703000c1760b8421014001200740300000611024007042008004007055203c4002e41d120401c506103540c998004203d44009801501d20b4406410010300c1843e1007542c006140400607401c000751004020300040400000399401c1042c0d030f190302520020000210702ca84181d0049030008082036080d1480342e482203002c0c030b07031030a842502d894210b8001810765140000880e111095400010222141603001c0ba105410a00c240b00f10542c2c08801941603e0007a2428840741c3c03210200181c0d2482640b40c0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 2834099 1250 2832849 2832853
    0x3030604060e040b04080703050f0307020a021008090717030c0105010b0403020a0503070b0a0c03050702040509070302040606050a02030304080d06030b1305010501050904021003050a060510090305060603060402030703060203040303090807060c0e06030702 111
    0x5e0700080408024100f410301a00e451824098000700d07104e920f604c00d840b400c000d40e100010420862034480300c950881c0030507150ae0705841c20107424450f0f40c1d0f00b0718042c504142c1d0900d841f00881010130000c1e9a117003403500c0001d0019580d95080010a58828001a40211148940800d55050010703100341180c0110b00c8a52a283c040e9034100c40100d4103640440c2000300c1081110090707035031030041500808886000d425000e21b0b41c41000100c1d25294005400e02c0010f0000850954000c01031700d41c13190b00181c05540da00708910511006006981000b84211603001c00d2200c0341070a1050446070620401c020451a42c82e941006031401e011640254444000c80d4010f2400b807007600656086402030a01040c06522900010f0424540c050142c00142c2278035000c009004003041601d411410960143c403160800f0380201c1d8a526840c04007170b02454002005c2404c00d0b1183c1e02402841e42c00210154940240d840c141000d07010340040b480c00a11400c020040740e21f07002d4226405181c403500 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 2835349 1250 2834099 2834101
    0x207081204020607020901080609010515030705010804050709050c180316090e0a0c080a03090f03020105040501050304050309030102041d070806060306040902030309030d0201060f0b040506041403010e0a0503030604060e040b 98
    0x100359104420000d10072600290140300a80040e11400c0c4071038081e041d948090407070340c588000c80a00f1240000d144844620700c8050350a05502c010903c0c5003522400e1030001010303036550805610300030b5030350311001e006450501009a0070140c8070140590032000c48944180d60469410140c1c2c8c0c4218525001016a0716402003110741c80b2540140200042502560340f41203503910781c40807103c4281e0008080c1d40200281a080540c0003142c0001780c03101800d5076081c1e60850700020502e02850042c2410711030000086414400200140c5502c0300c0002c000f0340d510381c1c94004840e4801d40558000e0303810244e410102e119a030080030380b14420a0701402460840c0d40301e00800c005880c000724140c0e0140000c21418545071414403c4510300100303600081001c0303190240d18414442c6650110250080510041c45165685403c5400b11500d110000c040469000300003401041c0704400030805120f1480781c002008400301c041c5120f8401214100a1103036102170200c1070b00f6040350010a60401c0ca4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 2836599 1250 2835349 2835367
    0x303010501030216021e0103110c0d030203060105070b04050c0405010801141f050604030b0105120d0210020d0e06070906030518070e070212030108010203041e02010c14030904061403070504020708 86
    0x64068015090504c01c242c680c2526a00802c2e02000304500744001c2100d03c2580c02d10650f05400340b608508003188103d0f140480c500c811944031051020b240c010503030000301081c69070b0b01c61029540c0b800c0c2c01040001d41c3c1c2c1490714151f50703078024800b182030095082000001e60804d0607c00d0840405203150703444170f2659480c0140f454450b000f0380003802d4020441d008241134884a0144c80554442c410440ea594104810810003a1001c1d20b040040d40c13016001c80d490b640e020620038211034dc000400f41c1c07120358650500024100d01450040c030b601c00e000c1000421944003007494203c03909520104a16280c1413103421440647c490065425481007004100051000c48030307680c012143d00c1030b81c42602d40000440345503442a884000941e40201c140400d20403041c19840080b030344038528002c201c0380ca50018006514107100680904030000103048501014412113410300b4008208102c110749400102c0c0348082050b140c20300034422105c011405081c58802c9070100f581090100d414400c0f04 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 2837849 1250 2836599 2836601
    0x308040212010c02100e0109081602060405090c03100801050702070e190203040302070f060503011202060306040b03030d0f05090601030201050403080c01090501060609140906100c020402070206030403030504021809030301050103 100
    0x6481240c1101400c001031900003801e124002240d01654003515100c42c5036864181541c48101c5003030060f925001c0c4403000920314004a496641040c2001241c1125600001d052030041d03601c4141c201c081c100800000c0005030f0700540c4141d0681ea1400d00b440d460302d04040c03c880e8100c070040d0141c0d00c00e403820b100450020320280d0f4051700d842400b203260000c104401060340c0050754103e015a02c40101407000c190a40001c0d4080e02483ca4000e00b07641c9080311a034030b03000056001900598000002c149651074bd5045000303503a2000e02140d0341c5102080000300242010500c10298078603007804030340542c00c00304601d8122a0140d66190030f00d815511580010390115544424966a8101c030340d0008400780682c00080402d500c5883c0c0d440c0c5000c100c0c024109240c01058881e000030302c100300c034564401e200c684c20041c2514241480891500c0031400a200d9014080d40c425404005c0004266054001c40d10651090320540541d41094403070194000342612081d01c590814001803102c0d51003 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 2839099 1250 2837849 2837851
    0x606090c09060903070f06230306010302090d02030105071d01090308030408210106030504030906051e0309010204030b0a020c0721020103050c0f030a0b09010501090503060604020a050705030a0201020c010c090e040308 95
    0x148610b207002c0101001074644005c5500c2080310840202c402c00ca001d40100150100702c0420031100c045640ba210b080c21584001400700303060550100d10b156803034030341c0810f100c9415400343c001c1005003000c0001414001c8009a07507840082c2078042a591355114030348070340460b81c2c0000a242161107650b6113820035049050352000d503141d998000035200c41310780c01142c020242c540f00043d0034141820010000c5203240c2112081c05020041f4100110325009080308070f10b40501441d840340ca032030042a019128641c005080364519000303010b0814000ea00400000103107400301c178043c5558900a48031440d21000424220101d5402140554003c1d0001e03a40407903070900e803c1c50700d00d0890810529030016a8040040d90740c0702011310140c2022030606025000900304007854500c4c040003c0d90b03070000280058000c0782c0115100d0b000340e0042c0700351803100368880152900c079100702c68001d00075000303103000c54000d40c2002414005c00d4026108201503411900d0045480d94442d00c2c01d172102a8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 2840349 1250 2839099 2839117
    0x10c1103190b04020102010605010e03060402040515030a03050909010602150a02030402010201020715090501050609060a0605180411120a060b070201030b120601060309020a05090907060c030309061b08090606090c 93
    0x611000020160980c01d00050081e1250b91900800d00f01400020300710751442c0c000c54140100c0c00b12422041d80c000402562081c4e0480d8041016690b4480741e5403100c0c510705071140c151080382d080070200742d0400c5c0030b0000905c1c00d8400b80020ba0761414201c1c6e4a1910300f1511154010031000b01d41001029001554090700600000d40783c010107558507240e80c0c0000d2040f100c03041ea20b0594204000d401c0c0103003034004038100c81c0c0d8401410010001002c401c0984100d005100c0d0004e001c1d464406036040307003503c4050060080180d40203040c50b90410340e000c0c01031054581480302c0060244002889080b090b1404150b000b130602e00c26600540c014041c0803007040c3c0c0b0100c181d0030500406d6003004040d011f0103503650041080121031051022259040c0c01c01e52107003401c181042600b1100107008421074115240031020703544076081c2600200450a405000e082c10704000c074403003204003120080d44c1c41107a078802c40720360344060245d42c44280950f030075035001061b4004980a00e800b200a40b00c020 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 2841599 1250 2840349 2840353
    0x15060d1e0210050306030607020a030203030601050703030e060403050c0607022406060d0509010b0f0301021206040c12060b031b1c0b0103060905040c0501030c02030a27150c0c05010e010c1103 84
    0x210954000070000c4546522040c0043c400104016040c10184089a007000640c0020010f100255074081d44a01005001d00d04005010500b80249842030f0002c0c485020210141c4240d81400d06000780242d02c0319440c031740944585004220342c12310000d018100698130300481c440071024401281c80c4080f01a050913880841489860400c01c8a4441d0701e004042c1000001594a0000c060261b8072520134220707031080e481880b00c000c1c00f40010304456031001007220b0000f040d11206009480341e4600c602e484110341e10b0501c2c046249400c0c40001c40c090034000111854404025224501c203100d018040040d13744624140d442142c019045903144102c14100401c41035281c1c0407850486804032425980c0e103803002d070204401d50305807140d1088402c440c400380d841c202d250348010b400d50444440f06040116090380c05481030307421802c241c0107810045000c560701703508140000e02d2082c0c4031100b0703607161500d41d40c00130700f96002c0c900c45200213406071280b4210058544400c12003100e1900815014 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 2842849 1250 2841599 2841653
    0x3031202030a0b030f010b01030e010603020105030a0509070314030301030203070b0301060f0e0a12030c06050a0b09040f08070204060303030b0109060f0e040e01150803030f0a090c09020c0109020306070203040815060d 95
    0x1a03130305004049103442448000211040d04800041c01e0b1060707104210780c164540b890034401350341e00c04110303075001c2d0115102042d42c2d12544043c9140610315800038101d0b04d21851440c40c041004001181242e00880489070750360b4541d00c0754540d6110a10564000c198080e0038400c1d8a0f000d40c1d0050000b60008005090150791950120410304009404600190035503010700100641817045640058a0300000c025542d034440109005410140020301021030714001ca10400c4200000c80b45000e80c0a041402015664039003d0017420030300d0401408500304810204180f407085d143c41454040d42d648100e048450f020520000380b4030340480e0b20300d40d501c8126aa401904122240d001824644003e550320310303080400003113903070014101207606070070304c005840411001c0f8404000d4401c2c0900050703481c0e0903180e0850040c521700d68029011300038101040007040e0040090300881e40090103448000044524202c0d14000c101c8a065026050300711010215200e88481d66002111400d9200381c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 2844099 1250 2842849 2842871
    0x3010b012007050310020c0609070303090e130206070b0702010b03060c0a0f09030203030316080c0a050409020a0324090b060c060403050f07050102040e0103030f0c03020c04020306040b040608010207060e0703031202030a 96
    0x30030010017041d5412130b07000034038500488800c015030756220a444015001280c11960010228916480340c80c620203001c0d0089140d4003550f1a590301001c2e030003403034a030759620365140c8210300003000c8034404d025500c1c094804185040109050344170301c01d074403c490702e407048030a801d44640307548601c0d0b03e04002c0c00c0000400143c0f02000114010158071004c41d0f107003e441480204030200c020402c616400040c000303034070819002001e8a098400d00100542c8078041d003201240104070300466220850124400c021001c103d020600d0181c0386640e13424441e50381d4403401e020341e51082c80902010356024500140200c1d21030000740105800c0c1c2ca446500e80034a82e00d40321300b660095040b50f150a01c1c000010000c154115100040c0090b681c01d10000206850320065203803a21f107c3c00038082c540020001c0e0b490b40e0741d5807080f1001100180304020700c54803100028001d40090304111001450583c654600301d1001640000700c90b030565a402203170803441c9c0c440300650030161041e07018503120303205460 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 2845349 1250 2844099 2844103
    0x301021305030c24030c0d020703090501030f0905071205010905030307032721030b040906051504060b03070f2606040c05030c090607080408011103010306060503010b0120070503 78
    0x880031800c640d042642050105402c11410a03111482810b15104a140c074204d410079a9845644401c00c040e00e83d655203954491038480d50401807140351002445070101900805484190362082e60100103050316030301d80004a42c0329402c0070300982d1241008101c0b201170241000502032044c8004900c2c0019a6074a80c51a0015108200032980f04c0c0d10b80fa40360142c00d42a003600d991078860841031a10262a0204103c4414100701100180c1405900c60207010740c1050907003c1024000300040c079203a080c92401020301b56001c44109400d070810107001c6c9054003a80c0c0a8502e00021103180d80c48200d4141c400420442e6620706100b091442030440204800200d0107007582d02c094141240350041c208000c8807400d81801c3c1c213104007481404000e48084040c2d43c40300c1c6080e2020b9580e20003a0401c0700c40743c05607030b029098960801c240c6459054130900558102e03031143d141032008541356000c060a03542840045800641c814000d544802250351840c200045410151820b0a8030b90011134 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 2846599 1250 2845349 2845357
    0xc080f0d020408150601020312062106010605090406050312161b0308031503010e06070c03090e01060207150206090a060207060b1f020c030a080901030e1005040309050a0909030c080d020702030102 86
    0x83c035130300140340e810304150104190310740c042e0091006c0c610744080428041c2180902505140c040c081288030400c6c0800c1a0781055034090800c81150804d60350340400626607031181b1001c50180e410228009a54100098503280b025421015241005122584401260303200da000381c0d00b04041c40d100c401315030400503d5401450041d152541c2c4ca14107040340c1c00030394000d409014000d038505801e8060074080469a81c3d0441a54640b82e5010501400c0c2164000b8141e00100183c41d0003800000300280c00040c500107d0312a00c2c4824148540701c60142c0e11540c04982d200c0079600700b094100005280c550042040c0d9101e0303200010152000c001013402103000d5645070075030341c0780c01008030035607501084081c0584400700d00400205132144c0d11441d50780503907011039060680301c21065003101014403201116040c120b02c00c0000b4078290500611081003841500d0182d403040b20003080000090044801858054444c02c045142580d2030206903030009400c031041c15428010000141d800380020 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 2847849 1250 2846599 2846609
    0x60c03070c0f0c0311010509030709020a05090405090a0b01080a1101030b01090b0d090c050f0303070b040201050405030d050403030801060e061602060408100b04060602010b1c02010201140406020304030201060504020306010c080f0d0204 103
    0xc294213500c0d100107a030452412040c1071010620801d500c540d030000340c040c240c8a0170303903003d6220001c40760191074500451039425803090500c2c1c1000014580040d03c00c2c1c030769001382601c0142c0d036a66050300d82c40d00790000c4094542021205660100d50003504918013410061400c0030120b503541c40801d00c01e401940310765040e10b0f100c90742e000612100b0a14000a460704a07600340c0151002c0300001d60b6031140c41c00041c60110500009415a802134098030001e140207410384131032400090004025600500003100400d10380d000100d0071724440e40d1150f45905d0042c00b014500406404154400607100e417080380d000f0301c02c2001144ca84410b00c4110548101c818020448070b000702c007080281c800c16007240b411a0b1520115000365a103644d81000424030041d202103900c0c06d1400104d01400c00705289e6101001e81d03e051008100c038036070096100b04e00a5008010031a2544100400d92000f62181800290310914900128102000401c91420301040719403511001c0340842050fa0005d42c02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 2849099 1250 2847849 2847863
    0xa0c03120f02160e0408040506030103080d0c050301030c050105030907080708010209030f010209010203040605030a0e010203040b06031005060906040c050412140f030301030b0f04030201020d11030702010b0909060c03070c0f 98
    0xd04990580040c41c00416040034005010700c8070858520000d80000742c0b01d0040c020002e10081001c0c003160f481110080c10000c0c00301c035560342e100d0a08400651040b660315a0301c0f880e0005281000b84600b095a040e03035442480401410b14020044400f80c101801c0c500b0140111040000c1411007041800300521026001507191502401010304040d020082c3c0800c42c0d004102b00d0340b072680e010080b68155000c80c00c0454480d11020f800758000c00c142e03109640998400400e0205102e62008440d01c00d0b40b00300c00f02e5070b14134540511f2100b80c403c16200c0c1074114200402203031042c0b0b0213800908184d0520701e080c3d03040507600c0d40c42c032168240382602a41e8104049214024001040c040070000f42d2000300103621b036524554401d1a415001171019074001c000c003000c642014401c1d0100c1e5280130410314244074090030070b1807031151640155030000156180410700d4069060a44c1c0c02403080b040d1b00050402581d84c040e8034000f0747d000a192404215080b448180000c1c0b0019020503800d009102c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 2850349 1250 2849099 2849123
    0x10060303030e0706020105011401030e0f0102040306021e09090109020c0c030a080304020111030f0403020409020105070203010f0e070501020106030807080c1c09060806010813020f1306090209041d0d030c020a0c03 93
    0x8440e030504a0f00c0d00150110390401006002c02d5954501c03e00000f04203281c001401c640da0b003912810308019904c440030755400001e000080c130105030060b2001401c11102280049c00d80d005440b01e91045041d0142c10100f050010048448181c4c0608801b1180f4030554001b8200100080e040c00781200d011a50104003006002c02e44d64000344003031103c60310600071031628030080c40081d5103002d40c2c44024407483d202d50300c80045920841c141c8658590140082c0041050485810017400400d01544400c0c0302d95000002c0300c0d0b1050059a00b01c030307008180c85d03107400e1840d101c9460740d42c80700c84440e0042c824403151003202d44040040310680f40340d564454020b6070400c04001c10072072025000303034100200041440002021682400e00c0c56a0483e2941611b42140001c01c1c8205929491610840c0c50000000740c1d030f85003900144206401140c0400480d40c2c001d014138549500300c2c01c1c900c115400410696001400703a408000d40c4a0540115003211031a030703940405141c02074104880300e43c0300c02 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 2851599 1250 2850349 2850371
    0x905060405010f05090a15060902030901090201030f05070507170702091608010801050f0703050a061802040504060504060f0e0a0b0306070c0302010c090b190903021206040b0f0903040905091006030303 88
    0x700c240c2e18907105000062004d07090844120303560704903222000d0018a010300c403d5008114030741c41100148418001992280b40014041d402490110410b9000c02c1c240f9030b014001121a128451148503261502803c12400e5107030a07103003101c080a252404d4008200400150340c0307030407002d4440c80308441c48105600080000405191040e4403122403a810300090180b41c09502c6043c3e40d1003070051a00042903520980c208025000d2640b2041c400d000c035001021007030000e900200152602520148a455611014041101c0c594400c0070015050315005010b50502c00c0c250f00d4000003060300100300801c000e00003d0800000365030f00004240d10403001c0041580a00800c04052000c0c282441003501e8515648200c0c070502000c0c002c901e990384500104240541a014045c54015021010420703054003105c3d500e4005440170369000c030a010005503030455064400f8882d0a5590145080518004598002e084080d00d52050f900911010070140034142c400c1c000154029070b008900c8410039 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 2852849 1250 2851599 2851601
    0x4030c08070302010509040c0210060b03011e050603061908010f02090a0e0601080a0c09030b101a03010b0405100909020c01050712090b01030209060f03030304030306060207050105120721090506040501 88
    0x15480340302503030022001000540c1e0060144d8420100584010400c0c420108040342000111410010a81d2902e030011509680d0040554103132844414105003010000c2a14641c004092103055400201000002c50078244030385451904030104c141d5031011600c0e0f1007210300b500c5000d9154807070640d010580324914501600245c0c02400c800300c42c0c0070300703040c040002042ea0100424050500d51152010107845101e80003a48c000e642004510b0704a0600c01000b6000b00d140c0d105050a00243c1942c14400d84944811241203d8140080380c2c41c1c94504030030300104c01c01d10f003440c0d001c2c0b024a94001843d13111500081ca05910318100003ea903242250010340b882030030704800a003062070000408000380701d00d0002815240c04617502c03203007035680d980014000700304024115010701002c002d000c00c164242d0003600940340d16800f610307900c580300c00044604e4007900200081000d400404503a00c503000301c010595600402508554100c0760407045416990b062800322050381c8240100002e015003 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 2854099 1250 2852849 2852873
    0xf0812070f0e040903020a030809070503120705010e010501080a0b0a0204090203070e010306060206010612050c0f070c0305060f0408070b0901110f130b0304080a050a050d0504060902100f020601060302070c0b0c030403 95
    0xc11541080400143d8030001d61f00c000000c0b000382400340000100c0e8074100100403400080500034100d581e41c00c0c0340050a0b641d030f00482e0088a0035800c101c801e03c440201030062605840c550070007410341c00480d84500c0c40005001c2c01c10410136500300400301e51014240003c0d4410300c0c194450341c10301c0c51000e00040032107006602c032070f04540185d0014800250701001080c6d070541451300210b5181c40e84810650a40304540000d084200000348407810090051020700c120390051080d00c9269640c3c03c00090b01d00700803a00281318180800c1400e002440d400b1446820a410b280001250340aa240b16100d640c0301c3e265110a1100120b000303000210520100300150000b902031a007107041c9951101c00754011700e003500e801d06c01e001c03800095092241e01a64420482044c081c45541000c1c100035004042d221410b0b0f004608200c802461b26001b84000314400c1c02c07a90007040d841e882c040084000707411209044900c4a0801c4000031002020740c054503044204074042c40d91507242d440c020380c107240303 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 2855349 1250 2854099 2854127
    0xf03050d020f071203030209030105040309030b0109060503030304020607060902030703051b03030408071703130909060b0303071a07050903060a020306010f1b0206070f02040507020a03030506030106080601030f0812070f 96
    0x110401c410046240702143c10740480d031184010301c0444038507140540c00780c01844401d540543c6031100b04002d0617807050717096086034005c3e88443c40c26600c4540c0c150546066004007600355104001040060030950001d00c1d200d80030788030002e0394a0300d650000b400c249040d8000e541c654426600903115a82d0440d10441d0000101d0041d0f18081c50182981d0300e858039482005059070340c0c400c41e9009000e0501c220f0300320020f1844512081da455036407141c02408200c9069031518501281010541000411604003d812003c3c41c0d00c0d0414196603030222400050206041100500100c0c00743e40f010002c9a0203017078418005a1039282040c0014002d1480451402c200009080001014046040b8400c100c1703030180c0340195103e0107030406892020341c001c4000d411516000070000c03d103501190003002c1e18400e03907017070040c0d40794442010b0a2b80e0582c0034090740d1ba00201c00400000d840301c0b00712203260741328010550a00a400c1e10304100d2171000c50f04000032400d022422120254802c00c0f00319094 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 2856599 1250 2855349 2855353
    0x30c032d03020a12091404020d06120606090501050609010c02210f0606100c03090e070507020a0b1206120d0806030a020603040c06080f0708010b03090f12070204050c16080708040806010f03050d02 86
    0xa280041a14842c0f1b0504500e50281d03a00041220b42440290481e101410240c041841410384ca40342400040103503210341200ca6252000100d001e25044084503402c00c4160740c0c00325030b40440d400b00b0070705081d540c0b00070700342814120200c11284030500c41034a06850301005480c10f468039100348407050191641041c00c10250000c51400250011015400d0b502c580806051030343c0e80c00010b403141d11694001940c01000ca840008020240000400e80c1d0700b01803c11912030b8480f10244005081040b00e0710049410101400380303510b118060f550f62110004003121600741442d00499844d80c0203440585261a40100610406800901481d0090900c0c028078910340b410b02c00040112006000c1c2026850740080410703800716040144840186002007600d095000703040000c4929030100b0700c128000e609000015000c07010310815034420b0f004440030b0310400680ca68070740c0120b0b400007204641d108801c0c000400c59400c2040300301d000c3d084202c0c250f011a811410214642404101410115 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 2857849 1250 2856599 2856617
    0x506010b0306090f13020310050106020f01090201020c0f04020409050a0203040b01080a0305070308060609030601080313060507020a06030b120d02070303030b0d0210050313140604031107030c032d03020a12 90
    0xa494200f819030380546400450708080c0c8800000e0324031340b020800041e5042c4284c50b0446c58801143c0d20150480d800342d02207401d03040410141c90700b40c034403103400640540c1102e03500ea845420640d40502e60340000410041c030f8180c44945174001c4450617200d0401d1170f6400300400c001c0002c165003046c00b50040744010041e075181c60b54000d0042c07040c004001c080203100303000701e961910340e507065a00e2030300300a0035203085684401d16180e80b50400e80c15040e02e040c283d1400182e250082c007c071101d158010f4480380701c85052420170b5000d0030038022040c0c0c2101180e1a840030f00c0c14140040b14001a059000c1c00070203207903080040c2901d501e502103900c203461000703120006964041c0018044082400c04688130342c1d8aa00d5240c0300581480f0160a401c18070759500180030001c9184c9201d1442511049048200007107515640d8050f07010085c0704110481c0c0c2400401c01343c03000c1c216440c48044a89852540399200281c805480c080200d015920001d011010455641c07111b8260042d6840c080c00c03d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 2859099 1250 2857849 2857861
    0x50d02060c0d0209010905090a0b040b010c051e0304080d0e01030f05011805040302010b0a030f0c08070308040603090f06060605070c1707030b060d02030610030b0f060906120a0b010603090506010b03 87
    0x1082c45081e40400059500150021040e401002d103a0001c04000f4561082c41c581406400c014100700c500b0540304ea4642a1030322115070141881c002100e4000004040144240100e0308041400c440c0c80d9041d48800e1000041944081107400601d49141e41d0304005102680f0001d03080d1540400503008090410b001844030042d596041c0c401c031441c10602240d25107e6040c280d0050601094881c3c09c220090004001c2c000c0565403540c0340745c0b10b440c0d16522140c0c0d8020094132241d050100401690080008012480c46078200c0c481c01c80c01503100d4000028036a65040c100c0709580e005402058003c10510107208031811400d00800c0e00c003034041210150300c5503150f12141c46000c010418201100031648540320207154011041d4007608844442c10450b01c5c42c1d220705518482103501c0e504117000240c0810b040141d4030b010f040e002e0b021000b991500300811025840c000e507030500502c0745201420200e00c00047c464000e0800b0784000842d003440b400d2840c00c000c01608000078a000401c14848 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 2860349 1250 2859099 2859121
    0x170124030209010909060b0715020a0804020d080d02070b0106080601030b03070515040b1602030f0703050a03050a02100507051804180204090215070308071101050f0601080a0b090c07050d0206 84
    0x20515094900141d0754016000140d0f0251055003001c01c4e883d1a000300807415904560080c05d03014010300c2000380d00c8084102c0c19059125440c6d14600143c000400319006051640c07160344042d214660702e9007444c0c0310f40d03d050103d0b00301c2d042c15a4144109401044a550040b0301650411405c0c0703000c0c40b0510624022aa0341c045510540c0e02800e00301108410000b204010790b006840c1410a0a030794100c0312509004418155506910134066094006c880c07840c005811011280d20030050000c00b02c150310250b03560b801414141003540180000e048945503d8821940304880c15150142c65042030120102c011420a2a49004a240c0503c04540784103410014604550440300401e81c49a54804070f001c1d080039501f9160a13040c027040000816402100280c480c1e42c842c1d4030741c64072484009425090b208240c3b00040c090078820301045443d4403074000c881e849a5441c070701060303469240010851618045039105070307106e00442c15408101e400d00030701440c0803ca200401081c10300d401c40003 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 2861599 1250 2860349 2860409
    0xd060e010501110a0809040204050411070204050718060507080f070303060e01050301090503040e0705040503030d0902040510050d150e0a0f0606060503010501080106030e010f0203010308070203010b040c05070f0c0305030a1701 99
    0x2510710403000c59040784171f583d150115005454064424000b035a0b02c85039404194000c10401c9108500b41000915120700c0361055010020605120724000b5180030003d5505a1080d0f0003a02e2a0104000901080080c4070040031224800d545c00104c49103040560029914184c100d0345c400e03414171903441302044002003030f203042d966803184121141d25949010b80f02441154001070700740c0804031300201d6004441c1d1100c03184c0340c020b540c00e00041d0f58194800181d600346024503640034440f0111500410f031740e03c4640f050086c0140000494000544c201440e040d82d0b404100c1348071010340310400805c909402003200818560511905650400f00040d0201d04140901d00030036607031f1941302100d000c007500a2940c82141000071075895869041441d600da1001c05c00ba0b0003982410160107082c1400d208851400100d03a60321410a4819554480310468040b800d440c00514071a01001040050004040e0741105031a5030409042c541d0702440c074081c05a12030054200b804100e0403090805034080 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 2862849 1250 2861599 2861603
    0x30501060f020c0f0d1a09010e0109150903030603020604090605030c03010209030d0c06020f03010b0c010b0f100309080c10020702100e01020d03111207030204060e04050114040c050c01020d060e010501110a 90
    0x80400001c01c10003103080d015481101a26490300b80d0303060513420074806c44190094003060000e0041311008404142030364400740c0c0c0204078500144081030741303007080d43c4940c9025109142c0840c2c055034a8001925070303085900600c4032940c0d0307600100207504d010007a20442c820140c00070741c01d0909a00001e91508000d44070001408084102c10f0100a820744c1100c3e00c4004030a9480e49a58451001140c0394101140b014880c2d0b290000d4014a0b1429a00c1841c941c1401412814a005809012005042260002caa4104041c404010b101000303210955040c0502070300181c941d103071401040200800e84030141e00b8005072842080d880e9034041101401445641004160708620b1783d002805d81c8038000404000040c4501844600d543c15001072089036404e40d01c00307055503811010031003203820a204040007821511800862800e16800c001004003841c01c1c0241030140032000c180c02d81c1e0001e1445c000055031488144091503842100031b001d800c083c40c000000c1c104c04d120321983d44500e2940 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 2864099 1250 2862849 2862859
    0x20a12020102030d0903020115050108040b06010509010504030204090f03080f01030f03181502060106020714010c12020f0a06020903060a090203060403180b0d060f0603021309020a0306050603090d030501060f020c 93
    0x8064190390003002110724015600320200020301d01801c000380244810700000030141c1d40983c1c00034203588112516030069801c82441c1da003d4541400542e000d41c041e0300205c0c18000181f00010241e50340d03118180d001c0d4000c003900c041c0f00c0b11618000340201c400500300b060050901380140003055092405244856040c00d20b482c1203030f440202034500b0807e550000320f070300800d4010201c07000e0740070031058101d40351f640846601c141c440c4013404482d4004680c050003c2d000c0c640301e4010490350384150701d0501440c0140d86813038110a99590030a030700d4020548509800069210185c02c3c00c100c0c903071703000240300810001c0c0110342d030000b0f0700c0d400040d1001d42040b014030102107014040040e4036004102100c03007280e55148007180305000d0100da01c52004101284034000503194024000c454845458545007140f407410030b503050000303411207072081c03082680d507030700101c2c1c6512a00010340c004c1c117106008200d088080b200040079100160401c00030003401d01e414116094000844407a0644221030b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 2865349 1250 2864099 2864129
    0x207080717040504020f09090f0105030a080d1103100812030c04031b0b04060c05012306060703020c03010203070507050c0f06090618030307060902090f040308011403010f0606080603011503020a 85
    0x21040c007a00968005542c06880010708694981c24500104074a1100382d0b0714a106555900380c81310880d00034810715030550040d50581c800036a406009240341d0910000c0003800a803030450b4070205410442c0c0188080c0f06580051003128410032080010301039400c00c503441c524003007152180078004e511000f0030050019103c8003d03030722000001400f03440140740c15601c2e55a942c5004250074079644050b16035501c0d100030750300b03207a05500e41081c400d441601415a50b880702020b2151550011318103074118000d000700e000d56a0740a0000b18010121940d95a8548200d41041420403c141006034410744800805813495110b5405492400746e003194011f403a01c5201c1543c1282007013001d40d8641c1400001400310400600303520000480d0300030744050910b680e50680c210800c020642d4050b0109440c000100200340709180c2213402800060000b044120222031154103075040c6420040229001d44100300080c1400d1042c01d44881402840c000790f90b1450b008500000e0b00b0380162440581145 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 2866599 1250 2865349 2865383
    0x201020a020d050304050a0f03050601050607140a050c0a06030203070c060b0d0204020409020414090108100c0309020904030206010905100b0708130302060d02030402090109090305030601030b010e0406060201020301080c030102070807 102
    0x20016610315600a0b14a042030500c0b0b1a160361a5841801510301c00c000111010481c0095000d541040c0d030303032240c01483d840e42803000b0040650802042115080180c8144c501840310a0044030340c883e1052000381002c41c8544100f040c00901c3d0b401580c101481441004691540a5030300c4031701c0d40d003103070000621209400105507070078092200650000e000090000d0100b0181d8000c1003241c00d04903000d2081c0d4695410404018401e1040501c1984050020000516070b0790008481c8182c82c10300040d942819804941a0903003260254056084813004121080c03040c060307650b04c07003a8504103201e401c0c200400070059028441d070160641c02c005c18284043d224981c0714001071500144940d899242a240481c0603500032541280200582d400006451010b80141c4c540560f040e185c403419662683c00440c024620482140d042040c044c8180806840f03500c125800f920b800d500242e0f4a6041c9801d1038680340c0741814041c02a0320400850f004075070b00c038041c0c41605a1056071405100c0b02d0f5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 2867849 1250 2866599 2866603
    0x20103020d06060507060e0102090a0b1602100c0204150602030d020f0417030a030c030902010503060d0204060335040803031801020403150504030807030905030a030209040207060e060f01090c050f07020102 90
    0x30724070380c010300e241c4403000c11400d0700711004d0319555201d00302c14404c160400d44e00600341d01404600d00c0c1c124004c58400c0c400c0c49a104007130802c90003885210f144c172070841e80006d4a072510400c001c1000c181e49481c0c010035070409014201411008000704290f542ca0500005e41e288107814a000c680c5601080b601c600d002c9a408483c02050305060440180a1545200b0f44035400309406101103480d01403603405450013030240c0c2c0c24403a0144c68460a43c0d8502040c000800340d807a10407a4015610040030000958401950300740c7c0030203c400b10341a600f41d4240c000b07292032444986400c06c00c1440100301003140002142d034028075000185c2c4591024416440c00790040340c00051152070400a084103150556006c640304038083e41c0c2d50341680d103d500050301241e0328104007808a8204200e125200ca000740c0090000300e002400c010314080403038403518102d400400c800304413034000e43d040c00f42d12400d00202c6405843e254078208286e030070342c181c0a8001e2040342074043c08044041410400d41e802 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 2869099 1250 2867849 2867857
    0x100203070c080609100c080105010e1807030e0705030304031e0309081c140307090608070207030b040b0601140c06040f020d06140a0509010605010903020d080c07030303020315010503040203061302010302 89
    0x22140c07450341515242c0d40c01d25194401112140e1461146400c0003e650712030340910f100040a903100c1c621541d08003c011903200340a80142c942200701603400e0300494500182d043c2c4200c040303a90029900500c5240603007440f80341d42c0402d10940c024030051012a6040505540d03050401e003807010018460318060703d18400c01c0d4007918140c013501c0c1c88141100c42490003150b0f81c0341c81d9038840e003d41c0c280e820035006500064503220009002c011082c000a4001d0340c039284c020043e401141c0841d9541d50300c4880303615080b1002c4949075140010b00107a541c014544603018a8403404450030100044420396503980001c0000c4e226050300405c880541d2180301112550640001c0c0a02403030800903e4014030000544000e900d1030300d0440041c400080600ca84420f540c030596036100000d14580030820300c000300c0c3d2401d8403420010000700d0151030080100200031480307a1809a01c070301e040a0440c1d01200200100d905010007001000300503a0041034107540710550341c2050b49002c0c0d09000480003070103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 2870349 1250 2869099 2869103
    0x9020304140f16050a060516061d030405040f020406050f0304030c15090203070b0c030403060506040209040e0f070e0417070303151409060d11090c0d02130302040b0307060e10020307 80
    0x100700b40700349811804503440800c00c0f42c000c48550820707502e20a1000d98005849100b0000b81d0900032004000320b13400c04040d00301c7c0211008111644400f4180d446c030580301c080206560f1001408101c1418540107500240701c078aa41141824940782c0064054801c030000910383c140300000250030103004540b81c152054014181c10041941401628018940040140c0c42407140c542c0000d00b070307028401241c008514580155080600d184c5d5040046d001c00340005a110f40c007800404000d031510b1140d103d840f0f41520040c0346c1d50070045900c2d400c0000756003000800303845580400002c1004503420f0a080d200814416540702070b40c3c1000c81c0103194010010400590b04c3c00c002414000001004140d003008560001454641e4000c0105541145000408000d9401c140001610b0015952540030580e08504c0740b900039103400d03000403a4425024a1146044e001041c0b0950800e8400c0000400003036004000160402002038400910300e0055880703a44112005140144240240d510300d84d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 2871599 1250 2870349 2870353
    0xf170708010c0c1b0311010509030c090c0301061b02010f0c03030b04091101020709050f060906030a0507081506030f0c04050a060e0412030506030703030807050307030207080a030603140109030203040902030414 92
    0x74202c0d581c0240b00000c030f4101a54002c03180180c1100b9011100d0311001101d80c0400780024000d100001582c0c650002804190306000c1c2940c020f16a8071440d8981c0d03c54026030b10300341c0da650704049010308043c2d421a95800c00f040e41c0c002504c0140d820007501a083c01150800c007528100b40e107802c030301814480c4422070300142004c2c085401c005e01a046131400000c26020744441c940c41d080d104040300c0044500301d0300d0300441004111142001954907801000c041c0035503840141130340711603280c4041c40c1d2144485074406104217452074207600300c1c9604181c0c00c030040d11807600380700e009590304c21f18510403521603a9190045240e4030740ea54008001130a6030082c6100510b01030900b04610f403403004101001c42d0078200091194a4080740c21000c0d00e0707140d280d603459501c41d1003045491782c2008042d4014541d0820030b110100b0a10b002800c4050100c1e0303001304400e0306501d1300c0d800404148071141900d1b03043c0194000042c2d0040706072005c2c0e071007034135005840384d131582024110f0903041e0b04410b00074 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 2872849 1250 2871599 2871611
    0xc04120f03030b03030703080604090302010b1807030b0109080604150b030109030203040801060509090307060504031419020f0105010f0e060d08040602060a05010b0901080a020a020a0b070f03060905010f17070801 93
    0x40c040c5006800940030b901c0070004504600185034582c8164000100040c5011001450b54582503005001d010b000c3d200000d400140d15020500319000f0184003e4141780180030132491036814051801032803000c0c64400c881d41e1a060146640317081c0074200900c0c0d10806a43c1d01c0d096079142c0e004050f0500b00800900c00c5013860308000c0d4590f40540500800c950a0180102c3c40d810000c0b0300c64040d0b080b400095242240c01d8071004010980908110208144100500010b0513464044d0152080315141c00790000d90015020780381606120305075140344d04040c010042c400c0c2c1c050041d0111408030444030040e50321440012546006100010145540400c0c00300f00968009081442010107000030440350741c031400b100301d03a03025504215001545080c0020600c1c03d554018000c0390009004444040c0e0080c0c1d00d110090104440a00c001008511000d0029034503028003002410721242c20082941404440a030901080c003030b0032075100700300030b001034505800c110ba44000d001d000020808 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 2874099 1250 2872849 2872853
    0x30f06180106091e03080405120304030b0a0204080606010e0604060e0307030602030c03060108090111070809010c02090108010506010f08040b0408030414030301060306090b030c010e040e0304090608060402030d0804030f080c0412 100
    0x90240507000390301340000c1d0010400d6885078084490000e90f50480242030030186044e040188900741403081411901040c84000001240c0c01e16a03400f07100d0703440d0007507200c40c10140214540703c0d004080038100304801c204d0410a031505030407101524102c1c078040c19500310078004a4500340c11644002c01030303440013042000209455000d1741c002c10003660b0380241c81d207030b1115a80c00c1c0c5403003080c07540d80c5840c200201d00001c1c000800130500c540040c1000d41d910316103900011840e400990240e405651914100901903031f10080c0d22080038168100b8510b942415142c00d40264001400205008000004542404003c0740000080741d0000c0803207130f9030340c2c4946004010389000d2141864041c108041481d03140b40104403600740820687d03506044400b0030003044044c019407240c1c000300c1e0004110100d54440305014040261220400404c2d181c03c040c1b051600d461a1a1904d00402642009100c0040d0303102456070f840000a01d86050f154480790070b030094500c03841c6d1001054100582403030f81 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 2875349 1250 2874099 2874107
    0x7060605010201201c06080a0609030807090806010b030403030b130606080a021206090a1503030203030609090d09060e0a051206060907020304060e1c08030705040906080111030f06180106 82
    0xd03154203034024001c140d52409043c05820907a501c940b0070040c1402a0140540c4052403900d40e10251000860030958842c02a4108105240b058580c0c03516420300d0018036810400b2203030005041c1c07030123050031441c0044640d1605010b00806005000010100b400d0500c2900014201c1000500d0303201c3e0488004403802c020302c4180314110104d20507030000f403140e027464030a440341840002c842c0e040301d81e510380c10048240001011920450355861020014243c201440c4001c0c2d03101e5001581e80b400c1000c00c12400840007450301d40240c1c09182200c0d116a03002454100300c80135803e004065101c020006504400190884d6410600d100c2e401480603800041040c02200140d5240c2a40e03202c0940480e00ea200c4d07401050049210550b0704445030905824100360140e40110300c04140d940e5503951b003002d0344191441d5001400c045418807812603640701301c00c02000110003c10034201e00da0b480f031000340002420008400c500c2c0c00040c465403235580380440c000d0355030034040072290785600000e0 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 2876599 1250 2875349 2875361
    0xb12010305010606050307050702010c02030a05100b01090b04050d0201050d0e06071205090606011e030f0f0219020303040510051305011b02070f0e040f050304150e040b0f0a0b0a0201020c030706 85
    0x38901d982460740000c0c110740914120703405039032140d6400b46041d1054005503039034000072100f00d82610036045540c01090080c840d4030f01404510501003210f00c13003500010200000c80c2c0000b808400100400c0003640d4440f07034a40100c0340e0a0034040c0c0c880d4402e0348088000d00000395440424041e08040000c0d803640805076000c1081c1040c0100701944070a64048c1e514503080b0381640c00f0a41e00c960704100b4a5011035801c41d405003070310b070110710440c03504141d90940d074a036109101d01c503802040d004a01c0401c038004048820491004605501e4140c079150341c0d8426030740d090078007e42d03168045041003101051a010300354021000b8400748020755038200390003954008203401801003490104d58030800c01038140440d090f000e0909902d4641d41c480305d81d10300c1c040c00102e51034403080100080c000721105045804140c1358898480c84080c94050200356842a0340240c45280b0488410400d59a01410001921684042c01e625040110780590080c0314000703041c812803001040407020458560400e03 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 2877705 1106 2876599 2876603
    0x70c031e050f0601050906010c0b0705071707050a0c09020c0304050909030c060408040503010c0306060c111c0b06030f0105060306040605040c05120307050106060206010b0a180b120103 81
    0x41e850200303850100c448641002004110a240c00d0b9030f0680d10101c00e0a100440b08a00d03500c2521002d8001d1021041c8000400d400c002d2207544814440500c201b904903076a039803040d00f0007a81e42c50210204035080303078142502003810740c1c550003078070400f02004c0300550a01e420282040f1107400010700d03140c507900c81844920b0804a04000e600d02560084811685e140d04003000d06080d200c10081200074035041140401c0015486000e104074580c0026105110681c01000600700b060130f817003803003000c01821070030074180105018168001d03076044084500c91404640010700741c42c8102c038156816004000040e0108031941c01240e402441801e0310b846081c1c8440c0041c143d0880550711184ca58408641030b41040400d00c10140540b805000401c0c5542c0b42440c0c00e801c5105500c420020412a00e0083c550721000400300e40c0600301c039408a0342c4480100070740140c081024031003 = true := by decide +kernel

theorem cover : BRFrame.Cov 2697849 2877705 := by
  have h0 := BRFrame.cov_init 2697849
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 2697849 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 2697849 ≤ n) (h2 : n < 2877705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
