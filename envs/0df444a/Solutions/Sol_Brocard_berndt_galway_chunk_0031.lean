-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0031
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T17:26:58.71355+00:00
-- url     : https://prove2.me/submissions/4a0c7723-08d2-422b-ab02-b61bb0d7abd2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 5395691 ≤ n < 5575547 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 5396941 1250 5395691 5395693
    0x9010c06090c080115150311070201030b0307030206030901020c010e0304060207050108070c0b13110301051510170108070501020d050f161a010305010c17130212030c01051303030b04020705 83
    0x4004900c190780300194040c800c0e94410340c03540e61070a01d070b401e4541141c03c18420755060003040003502d01000c80c0300d20b1540e4500e0f0801046071020001c0c0a10700603920003904055a481000281d03440800c07441028507002880e0f01d84038681907200070f010394041407a40c9827550800455140100001040e41d003540c0990b0090b0080b1800c0c44011981110020304040401040c0c510410100d016a041c0394000d900e00760f5608481c03400360401c3c07031303600b0035841d40c05020b0f82c9004c080203a8040c4034900704c4e030540c004540c10500b2200400e01101c1c040300350b00c095525003000310000114050005a000d04840083e0291502001289030503a4503008600f0400e00c404001c20844516806484885504a10440c00400c00f00c0d07100c550035040d03030001d800c110760580d5580c40300c140c003540004101076403101c03c1f1580b0030646009074081d8120304104200a010b0601400c10054040301030041d1500c402d0441c0080015203003010a00540b04480407003900441c0c602800f0b078030f85040500803514a070703400070 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 5398191 1250 5396941 5396957
    0xb03030406030510170c010e011d04050601020703080f030405060f0405060c0a0306030501020c0c01090f0f14040b030a0f110603071b0c0810020904140103051207030306090c050c01050a020901 84
    0x2141c00c1d0003901000740846400d2a10301400f02e10310201c48003022545a02000030945030032040005042101d21001150502811a40c0c20540c1c8841810b45180480c040d41c01160365140d12006074a060f40c40d400040c40c50a01281442168071810040c0d44100d004600711042511890300030451048241e0700035100c1e0b000f1301c00181038140c448008082081c8a46070000c0c4842e03481d2109822a003200380c603808250000800340342d8660703002d0009005855503c0c0c08503060362034400c01580f208454460407500e0143c1104030202c0e1754807035010202c1d0000c082c00740e41e841c0915282c101c4000001010441301d601e5044050411400c0010989100310f200d07450712885000d26038142c1c0e03042041d40c84c044405400710440458442c48c10302102701c20009401025031611101d40c00c00c0103459500e0b208511041020300100b021540c0018850f1103440a0b0741c0c101d40d14501400d0450217045a81c002041c054102040c400b40c0950100003441410211002040a500d8688c4c89100342e20401a0103400170b0490 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 5399441 1250 5398191 5398199
    0x110a060506010c02060d0905010f05090307030305040602040e0f0f09060f01050906030c04060807050901080c060708160602070c0632090102030c0601080303010303140a090e06030102090406030501020d0605040b030304 95
    0x25a00294200005051244019100d98000744655000741c0d040b4100710f0b2aa0348401c00c0120901070b81500d240900400e00040c64100419503880c050100d0140400d500c40003c9403e0269507412240905520310410b01a450801d03a440d01079901621040d1240c903031140080e41001740440c0c40e0340254090807505505034039220800c54031900c090011a414080c1c501c2500c01952184260300007403036444090803005250408004100005030702c1a10b960700b05610b03012495071104111044154041c0c4440c0d103070410403203103c04803001810020550751000940c04180441c14621508545041e40d5403218408140c40031074208040f202091441a200e2802c4a81c03603c2c49805420100c6040c81100e061184d100b00c00c0f07203090800c2e442214a600000018400c7c194081e141148015004650300d281c100720890080c00a040307841104074140038200801e106960a404813030707100c00010024800a0340b0b0b030800034004c1d03020503412240c20303140c0030000499040501810f03803a900010055400c01d490 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 5400691 1250 5399441 5399453
    0x20f0109020906040e0c1e01030b030f03031b070c1e050607020901060e0112062405030c030105040908070209041a01050f0906040902030115060c020112020f0d09030203090307060c060c110a 83
    0x301c0c145520150143d086c1c8241d55440da030304410b2142c1a48110041651204030024044038014000d590081d00000000040c007480001120f400c600303100480e2007101480d00f002c0181d80280300b001080f100c410700c00001c0d0717101c01003190702c10300146c1800d000e01243e9074410003165226010000707422640d210700400401b070003644e0358450100181007140e0f01454800c5203004039440354000340708520070300c10308450754445051000303c0301196080943c5175082140c0920058003051040c0c910858640800c0c904011480041d59000c540c0549401021709003868060260b01c0f401000f4490300d03140c5800014541b8194403001c00088018051070f4aa440c7d02c0309010180488440603601507491380903041620240101010007011030341c2d04c044400001d031000401e5002c400c100000c040e4014080105030300100012623884452011001849220a1806900352b000b031500540e458020301c1c40c0042d040c1e821209440c0010300c10b001c1002004a07495042d03c0688007103030b0046099122124010000381 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 5401941 1250 5400691 5400701
    0x402030a020919020f030406060501050703090312140d0e0f1603170705070b04031205071707031404060201020c0114010602030304080c070807030807050c0306040222020f04030302010b01020f010902090604 90
    0x1007060fa001c0d01c84410509290709a82c050028a0f01001c800802c01c07003804135601c05c05014200034a032641c41c0490a8134010050070700360001030040c12040031190b500c0c6005551031800100d03071200c0f06440b100d0201750b001c0104074000d00343c0514050b010000854500c0420b113012070800d1440005800c0703065455002c23605107441c0d55203010110400c181c0f00407a50401501c0c00401e50030011558a904510301010340c4405106141c0501c402032098500041503c83d60240d805100c410940d00c4018504040b15000d4114000d03601c8414002404609180d040d0020303c211440038000b0300820b003070300c00644501502481000300580041c00440c000504007001002074003451412031f011551560314150070207003c0c1c0e1085444035400540642004414005185c00c0c0c20210701510591405401103541101d8466100e40400c03003000e2544205a9140d054a4410310a0005103480381e0300c1e131901030300030720308040d6441c050f105481000d1800c240c140180303c94194081d0101500f43c0742c800520001d00303 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 5403191 1250 5401941 5401951
    0x50910030308090c0105270604080c01090e16050f160c0f0609030c1e09021207031107050c01080a090506010e0a1103011208090103020f07031d120a02100903050a030203040303030f050402030a0209 86
    0x184101f030540c400e0343d1540040e0020b4402034024107200c0041b6030000d801c4000130350054091002440402240c1500b03a00d07504200c90650801e1a580c0a50808000084c030400c2e0310140880c070704510000901441d480b520096518400701d1400c62a2030381740a440c1d29040b841f0007420b900251005001481e0794601c42400d1000130700c0000100c5860b03090130070581c0c02c41450511421410000c1000c2c29030300d80145125580c0050809141c0b07862619001c0d101e06403c1380e0304c0e0601060b0340210302c981c00164041d4000b55007050945a40d96100d81c00d180d55041d083d960f4034005820443c54085440c00d25003100d048904421071130010701c01d143d403a2640c64101c090132505150303082c805182052090f2000307003001ea10a9462031454048840c1c88003017407903240c7d041402517403400360b40d404000000404900b1103404032000303c2c0c0f002036000700b03d82100064000422901413110300d0010540c001001d0b1003a6031290720280702410946001c441150701c00c0b600a985a4480c00184015080c0307400c8082c1c000d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 5404441 1250 5403191 5403247
    0xf06010b120a15030f0506070207050604030803060d0c051005120601020c030a0311011104080c10080c07020409020303250c050409080301030201080a0b03030309070501020609010203010e0c0d06050910030308090c0105 95
    0x42d41c941750f0300c1484c000c989040c0c0b51030b0003103010800d80540c140400405003008513201b42c00d141c2140c440440b0340c00010300c40b501031070310003498109021109a00000514005051030b4010014081c01070207038110b2212103240c0324401c80868060360020451052001001d4024281d100540d14100d03100301d00a03a05a000d95611009407a184000340c0013400500400340040c00309034141c1c014403ca20204491401c02c1101100a002016611701d04481d80c0c035404a07004141880c15000090452242141085902008254201181107500c400841090003540000e20700342c0e8070700500095500814000300360030382c204014001903018400003500300100210005a80d00d1581c08240355071720981d20103d26038032a000810a80d80e040041c4e50b40000100001d50441d49403160350300003180050007200c01544082410101c8281c15480780006040080c00034100c0d040140d0f4180d00300451780000c1d00010031410024096540009039503140c2a010381d991071900642d03000c42c00158a034a0329107240 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 5405691 1250 5404441 5404481
    0x5031912060e150406140609030c04020406210c080403140d05010806100812070201030905031204060501030b0109140606090d0803010902120108060c04050607230f06010b120a 77
    0x900d0620710900c0e0240c40c0e0038801030403e0406110000f0030b2440c600d00c240c80703142052070038050480440442040040156042c64071881c0c0040001c0c1031904104450f40c01901c0460000741c05980314807400f0380d80040304016840200700d6680d040c20340701410b058038003040c03480d404500024480c00403840000224415617041617042118403064038000ea1050b58281e06c600c041c4042c045890709044000c00920008002d0121040d00c050560302480001a044c580d070303865481e0038040244111014007103e014250014505442c0a10003030108bc00141d400203400c800104500c415441800748022600e10010481c1d51a10204260780d0b0046184070b030040341c1700703040707070002214000a0f5018000702030b0701689444494040f508103c1c41640201f9444d40a1824800101041c2d070468058800640d04560344601900340a840c68100700d5010000450140441321070302c0010a000c1013001ca440260740890b640c030400071009001c0c045038204a080b1420200b5882d4400740d000d8040c41525a441e00c0c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 5406941 1250 5405691 5405717
    0x703051504030309060507030b040b040c02071802040807060f030b010309020d020d0507050d0803090c0907050a08091905010c140306011d03010b030604080c010b06040e011701110a020307020108010b030103050319 93
    0x11b03a40e040d0380001c04240c4642807103600d03207031501032880d00750400e0f501046600d030310400c004c0d5a07221714032407944100400c44a401070008607804890190915200301c1d103003e07a4a2400900b0000c18ad04502c0c0060300e03254070060190b2281c051162040d0b0020302c05110011240c0030400300100307000742106d0320320a0110006042d00c80600403032144e80145a0700d034992074800d41c0b45082c02e090b6910349124884400811405c1a00401078402036140c91800390070f40d590303160360103161504075140ca80100944c601e00c4c0b810408150403d0030400d401d81d452140030700e1407005001040c0021b848842c0030aa048201d01826070501031003d0007100d004002241c1a90014042410204140c2d000c1d18404000540500d0b00e11090042e861003c00640b0740c24982894403450114007d41070040303030f10350700000056074000c003425008003072a85850750601d5901d104070840170355294000c240480c04079140400005050b00c403581070f42d04032034014000e180b91004c5010348610304402c0c28500c1042c805480c0100c0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 5408191 1250 5406941 5406953
    0x9060126010906051e01050301020702030a080d02071e0201030e07050913050a0204110301170309090604180b0a06090c0903080702040902061308010203011805060102100b01050d05040803010501030e0703051504030309 95
    0x6008080c00301d1110445e21a0107094005100c1c140c01040c0282e004000300310060f01c1c006150034a40ba00b00c400780e40c2790850080c641c4040c0c800e90401408070f03103284260b48401c0320380842c0642a0740c401d8804001405141444680702e1206220701a030040399400001c0641040c0781d02108143c1c03140c0305441c80101c0c0e55000400300d402e6420b4048900d0f0012005021000622032041175007201c2200550404003110006030303440400800c02e500507600c072044074810001241d00415000d84c00214000c1d14548000c0c102c008080e80d2040d20803180c100075408200314003c0111038107881d04061316529000075a001d10000c0c1c4010482241c1042c42041010607035000d014450300a061401d001596a5240c079507041d050068440c0c0100280c0d1821090124a03078002410040130a1912000304560111800688250250400c0003000c02d00341402c02c1704000502d4029410303260b003600c003004101c0c4408000e517035074102070200a00d540d01c000c215840101101510382d40c080d01c64980400d00440c650f0b952 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 5409441 1250 5408191 5408201
    0xc030409110304020315040807030c0c0302091302090604060602070915050907090501030b04020f07020906060c010207060506031b01080f060303040b0409050402040c030b0a0b0f070f03020d0809060126010906 91
    0x1c81c1d0000300c144800c44c642031001540d1070b001c2460008240c18103032519062403041840c000c017400b501014130780070000c003060310342c1c015900100256241d00c1c068840712800c0e100e0f20012031045a000001403643d2801d03101d08000e41d595a03000704585030074904200000d0268000070703040342c001040c001501d0384e549500144034840700c0d0b640e0242c007480c190014003a00c00004880c0d101d00d00500110761070421103400d95010503011154041680c0711107000c1a010b125860303c620305135000040c50800d02c4007540041d0b00458042e02221204000f12029441110a030341300940042c211030b01081c10b400d180345402d50441070042c283d81c5081ea032601e100d03003107901c103900a03044642c071503041106620302403255a5203012541424031000c003200c000564007030070f83d00690901680c00f2503c2d00c500400c2400380d9a05952004014908840c80c0c100079507940f121000180006862000003580d8010100e0001d040b2170317054a0030481030229070b5000e001c8070a800700004141d0b5a8045c040b0110b4074900034 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 5410691 1250 5409441 5409461
    0x30e03010204080a120212040b030a02090f030102160506010b04080303040305030a0b0901030309031a2503060513020c06070f05070605092118030a0b0f0403050d0e07090b0306070906050c030409 85
    0x14191004c0b000005c00f07803c0048200000d401c1500c10f000800081c103004080f258045003404005a8a0181c00000f0301191515451560998070201d9061400c1109a4070707000441c3c000e40440300e060b070780d40107401c9840c4914040e07801160010310102d40024014800303940c114001d01c0d40847c1c05403c0c1c001003406a2002d900a400094002c40204148101d500010700c0412004182c1aa540b40a00680c0d030301404010900c000c1c550032040207031003213100303a001c08040c04008190203605200c0200c0400030b90884245003207540200c00104406500032811190161030356150745082c02c00c60b481d406c0050030700400194250107040040301c180c0c0d149000001d20102050401910380b00c42c1441080c0c04181e501c0000e01a500546e10071021508400216510280000780246d440d5114901101c9901850014000c1c4904109130f41a1000c000b00b185000d541c1880e60400c87c0107400000c06640d61815510700340415803540091080b144524002c012800746002160315007a651003c1004403030204c81 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 5411941 1250 5410691 5410703
    0xd0803160f080601020c010807030f020304050d091d0604021602060304030804050d3002040b0a0203090405150616030302091801030b01050301020403030503070c050109020402040801020d110406020703030e03010204080a 96
    0x10300505481e410400070329091120780b40c403403a540380960020f0341e1211a1407145046c0240c090010700024072035005409442460b00e03065440e82420701e80302d659001800343c014080f80701800d022a041604141c484010401200740813055151401488020f6100421480f40c2d24540441e030000b5890706001140901e2081d900e45600303107042c6c203001c0e05080c2e6981040c020005007940c0b0440140325040891642402d076000155102c0c556814840203104652210000c1c0c00c0c0402c03d8901550040080d100c0d41006840512803903a03801c11890040c00d1000030a41d000e42c00f0b010700942d0070204200c81214600c41c3c2001480c0a4006e00001d03046840b03044800001705a101c014003c004408200350300422055009504090075560050081c0c00300a204004004035500b6500c2400000d41050032015009002117564640702d4203c0e80c082d5001c59540320045041c00d80e030441c1991160211402c0780c180e40d02800e03566045035803c07130307041040948032640b640d02804040b908034810320140f1419032090b0 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 5413191 1250 5411941 5411971
    0x603030c0501050a0209060703031d0a0f050606010804030906030b0a050909010207061409071e03080d0509010b10020601060f090e07030902030615090103030e01052a15150105090d0803 81
    0x1281290940d00028131000e103150051006014a4841c0c60070759041503030500b0007261a00d81d41e1120614034400102142c40c0f481100603c40c1480044405110b100307003c1e07419515a0381e1514010b5524181c01d0383c3c02000500366140030400544240e2082e000d100c00105844149507507540020358440007a5903521060758006920300801c1250700c1040d101c4288100300c08414500301c0c2003280c403841c3c58400d000748429050365881c2004688040d0702c01031039000e0300b210703210341f0403031700c250020701d42140ca0744003c1d0710b401650149460500c00200070300102c1c0e8000c12503682040e4003140c07908212005c0600340700d500000400c281d104590007a11a001607070300092071580e01d00405140410103000f4856503c18445107000035225401524103480d00741c240844480300f1800101c4035071285840e950103540c43d000405080542440e030b0100c40c5041c0b8421588001d000104844444006961401204e400b00200080650094018152644009210400301c400c0d80d2101d621070b500480303084510050352 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 5414441 1250 5413191 5413193
    0x50a1e02100c0207140907020307050102030405010b01030b0105090901030311010b030102070501090b07050f0a0e120a030f021212150102031603030506091302030c040902040204080718060b0a02100c020c040603030c 94
    0x41e10070402c44201500c0102040741c13a08501188003100307004294000c00100000811442c020030450b59180d6003c40210342d685490b0429070f00034401c2c901c03441d00080c14107041070300c558450029602a00c03030062000035283d2960f90252000c0c03402860a49040d500e503000840540e400380b02400d0722600070000400d0405081c076103850101e20040c041d20500106000034076244044100359140d0f0000d9041144014040100141101c00301d14030407041c520440004108241d8030030815600c4c4400b68086410039085010072400ba07003c1c0264032012506840000b4071217078500342e450316000c201801980d21744131081000c0c451150000d201500480d072142c00b0322800342050124103034040300d0002c10400742a0746500084d01d40410480942c416522039840303400b99620b41d41110014503441c000ca9000d02d60b61510303107003900307258284160003a10304580020100340840480b400c011250b4040d00d4044003d0341c01000410f68800140210b2164003480d03441d685a03440740d50007441c025202d0103000071003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 5415691 1250 5414441 5414473
    0x305070e01050a1508090102070b04050102090a0605031e060d05010221060d03050706020307030605040509010c030e030c071206200301170706020d0302090409020a03060c1805030c01050a1e02 84
    0x10607440180a1440e516040140300c03004072450244e50601d00c0d2102d20381e1034001c40c40380039010300d40300500940200d10a0108002c1d0540c010008448241d0b44400090fa641000f55607a000880342a202595081d104542c1c04010b005520351200000304458001303c02030310340780d00326000011040202d4081004010340700e00c4141003075500850869509580702d5040c0e400815030300421000404141e004008075081e5406504220003034840508108818545003401c03501a0420303000b6100420b10340040040c2541001c011264417030154801040e40c48d180170f03814242da40940005a941668500002d01a414005800908031022240e05901da504002d00c010340b80400707100148142d44030b01c108015194001c500d51400884600b801a2500c03802008100a0260b00b1402980300c4000900031081006079800400914050b030380b81d4401c4035000d1058164040540103559040d4801043c06105600c284010301d07440d807040c581240e881d1212041d401c000711042003044050380140100900c0001c0c = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 5416941 1250 5415691 5415719
    0x8010e0102130b0a09090f0f0e010f0f02040509010e061207080c090702030703020606100c020a08031803030307050706050a02040312230f0702040209060705030a0302040503060a0506030606130b0a030507 89
    0x40c0600910781390820340c41028006400a02c545100d054603181c144001c1303e5194082d04190b5a0710000f032004040c240d010794000d0030001941c444140c5030240000040b2480e20945066890181115038141d0811f030b0a49440c0000910895001079007144030140740c08140141001850b014005010550391041001401007005017268115032091040c000880d03130000e0441e8004805490152020a030220100c0e490944980003941101002c9400541050000010070000c503140c00c4d0000140c4014040684031310080e207044000036400d01c074000204801d980710701c0d000092030720018609550396071180c5200070142d401e80003259071208110f84422610b44407001e800342017003851746019041c3d01c04103000e004035100a801181e001c203840e441900c3d4403040710741980e008021240c880d442d08400401030751080c010303a1300a0084c9004102d60440e0381c0075290046000402500303607030b569801844491146240b508103e55110752090700d45880c0c44021102960007000a002041d080880e1568100 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 5418191 1250 5416941 5416949
    0x60c01020702041407020a2010050c0705060c0a12051209030a030509010501080a08030603012a0906080f0705090a0b030703090201020106050f030d0c0c0801050a0605120601030c1203020708010e010213 88
    0x43d11000c0213180c039408540140c4c000d601010703100c1d0002302c1c030340c00070345031803461100c0c3e6085800041c0301d2071880e410001800000302d1200c01c8034020742d116414445640200c02c043d84aa50101400c0d600240d0043c0c041a80c024641c0b400f00e00f40414410032240c8001c0030b890a100603000003034040440c650500666038050b0642009100079494141180d560300d80064029061480102c0032501c5664290072007001004403440254203404010201400e20f13580c01104400b00316031140000340b00d401041900d00c10400d03c00002c0c1203684a40c41075895030b2040c00305036880f8035652404610705610202442c0964100d59000610100610001e070854600b031300154400d00d0002d1904040da40c00283c0700c2821141031030080440c610750715100c500c040707903600484070381e5007440708002c02454194081411920200d820403841003440341256100d54081c040984900c0444005129040c4840c1000c2502480391048940d400c1c1e48803005421031700c0d500301301c080c207035000140a02034042e103211000180c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 5419441 1250 5418191 5418221
    0x204031208011401030207021f08270309040c1e1206080601030b070e011106090309041a01090b090a08010213080d0915031805150405010501060f0507060e070302060c0102070204 78
    0x6504000322550883e10f0030709600d04060f0002800340854031100030b00c143d458410540780300286020ba002400786d00b000c47d0344e00c40000c81c494841c900b10014040300d80b24401da1002552034405074000b13002c043d004d0410070340c080c00340b02001c0f80000f11504000f00d0100c52580d594052043e800300c00032082d2505940105410b512500c018404954078086181d04890300b810301c155010514001038518142007503c3c08842c0c002c910801c00c4c904004401400b600004540422102100701c20941d44004060b056a00060140e00d0910245a005004008802009081d00c01a69a41c0346441c02da0384110200812040302c140104807400c820490920602110b00f0304070740541c00d02d41818440b5141c2c0039500704254442c03020080079101c801c880b401041d0003e080d81c80f0700903041d02c0042100070554085941d0b41c40d2600005025105a00e400000041a641c0794a4081692a294094485041019214011a200000103a64290043c90484102c01c00541c4071856030040100f11040328240c1105 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 5420691 1250 5419441 5419457
    0xa12080106030e03041203031104030b010302040b0d050c090702210d060801090312020711040c0201020702010806030d02070506070809040603050d080705040308040905090c06030a0603060e120403080c0307120302040312 96
    0x90383d0001c0155820307940e50441000d000c0e20541802c802625440d4400d0040030350004001c400c3c06450303007440307059900aa0707080c0b1418280d041408030300342c0c4e500c1010b0420b130024002c0c81d00c00c2c5414a42181c00402510403510220b2146009080071120040c0c9001200800562141a404c10f40a18002008043e00030404480980c0300602003003003185200081d40c2c1d0020340541004128100340c06034800150003040701409600d4068001d6003e04002d9020400d003c002600c9441c002a070304e9241c0c100d1394044d22a65281105016032500403900464042d98140400585500c0d944200d0004501034002000141d015420103010300360702a01d010100318041105001003008603088800f04e55070300800048541c3c40c01d50310b03400c05051040c07560b4444000020f02604098582001041d00e01468080140344012601e681d07036400034581d0016811b800b4001040480c0c9020042d002c0b961040050b6450310741d0302d13a01d011000950f5940c440100e94041010b1082c0505500801801c10300b0f4101152 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 5421941 1250 5420691 5420711
    0x506070903051c0e06070318030f1406010302010207050f0303040302041104060807050301060816050705060403120e01020403120c1b0602010f05160207090c020c060c0703060b010203130303080c04080a1208010603 93
    0x91000062441390140000003800010148a82500c50019000d18414000c094583c41c02c4e1803414480902541c610510490405c0c0d07000f004140e00741243e80c160020001185800280964403070940c4030b1030b40c0b50009000010243c1ca5a00401944503010350009644608207036014140d504041c007040704101d41400180500c1e03800040c9690030404002599000441d130002c01c4a083c89140710050413400342109000800d038100740f0090040010349018060302078084074142c00c0703000c0c030320000d4542c160b0440303d13000d010b0241c2da014141034099914030311140000c901d245075282c425071003140103039511000740500c8011403186580010b80106038000748440c101c4001e41d9101d5074043c49091996469503814503030b00070000c000d4103642c0070740402c0d210502e83c00116211086440b0580d0000e00385040c5101e1584003204035606021401c21203d1114116201103608820082040c4003042c000c0001144280b010040e81c14450711649606e040549110b40081c00c1c004180e0040c0149130038044030304 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 5423191 1250 5421941 5421947
    0xf0f0806010503131a07090801090f020d0203030c060403020a060c0c020622050d0501060e07020a0305071209030f0501050a0b03060105060f030c0403080a050705010b0105040f05100c0506070903051c 87
    0x5411040c24640070352261156011440304000e500e10003001c440300b44801000710044225118030640407507d611009599489145007a55480e4800500c0000d185000328010310304441451600c42c0050110b0f82040d500e0603601d89002c40c10340d001d070b01690010401d01d00300009801010759032949890b0009120106d41d0100d2118003841c1d4007507075402507048101c840980c2e01d0205000409d4001c011001107582400e0850082106005240c801a080c0c1d0025090500000d0401500d0754560341d0989400c050361524402d062021101c0030070801101d80c00004100105038080076a0301400c0001001c2c1080d02c0b580301114481403a060080d00b15200400043d69000140c66040c030044841c03990f640e403034071840c0080748902c0e00300801703003d00881e410b03000550007000f510740705114900802640d14260010754240c081d40c41040419400002c4c14041400d14091002580c0c3c0b117810150315001c1c3d42e41d50681410400c4506d000001d45a41d410000d102c0104654a9000e110241003102104614001 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 5424441 1250 5423191 5423207
    0xb09060301140310061403060a05070c080715020f0306030c0d0b0601030b03010902060d060608090307020a03030e03010f1406010906030e0303070c03020304080706020705120114010e060f0402030a06060f0f 90
    0x2840303078100c2c40000303000951800c1c00500130040ba0b81104101107515020761b000e1503401010094004e00c20000000c691038000d2240700d00400d04d1740c8030380c208041342c0c0d60746241d10b902044044600729007034581d80108c4002c0340050610000f43c50020b83e01ca24210050500c1c0c40c80102c00544201220800b00d40440e0708040d0894104000303280124181942c003010902400c15a20003e4215170002100649841658800310640340300703544030340094030341100c05942c90146100107540400355040420003e405001840204a409000811300ba042d00050108940c100429a14141c2618040200c5582d220005401500031420200103015564602030755074000103040a00340030980300502d09040c020000e403401080c0180c1110070143c4c56034402900c40629100d840d000390324202d03501c0c0030b1f15010302850441140d00c06a00b1016840d10710984038281024281e1a0400000c100400058075980000d61007414000800300d074080c6001c030010210300d5511405401c1200304108110402e50250b42 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 5425691 1250 5424441 5424449
    0x10203040209011818050303090601051002120307170a0603020f0301020f07060b0105070206030711150606030718080a080301050a090b030303010b18120a020102070b030c0a030f09020604030515010b09060301 91
    0x200c190340b4000402144020f2803442d52440c0413040301174004040250001c000e500c68035160301070790f80c5030b42d030f900c207015031002409010f1000d60441849200d1903d0080040c5500c420030b454101c82800520002c03140c13100c8181c0e6106202c40d01e8060901c25424426540641503030300342c00840c80d001c2d5a0004103040e0240c01070050030203880300c0f4a09180d031311038426180400d400410080e908d080040d000350207a000726410712428002c200700e0354100841300501074410031002d00721601c1e5640d1040101c90340f100c011410107041d45105400324030700c0ca041100c1e010180c851009950740e541003004001000d20b0940c4465452410280c5290003900c012040d40d04584009408c0360f1107c505442e084402c880802ca002e41140720110128001c0030005a0320740828000e070241d43c100c0d0b0b112901d0440510044550385c100d801c2c04c00c08402c1d03052003540461405682c8040001d0303410015070000d404d960141c0d1041e5815403050002541c81003502241e20300500002007464a81031200012440703030f00051007 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 5426941 1250 5425691 5425709
    0x1a1611070302060d020403020613030c05010e0f060a020a080a030903081005030705060703020703080304080d0c080402010207062102030103030305070906021504030804151d010c0804110f010c06050f070e010201020304020901 98
    0x343c0d1956131070160180c40245600510068803401000200015404031b0310094a04a0748582d0008042d4040c15481d4034010018013104060032505e428021030b6401980d0740421882020075080108401e0740103003064520303607500031443c0c20b03041c24028031502c1d019044544605e004d51041107940d40010b4920308a950650750940c542046040c02d80c203003c4954070281032070000200300f00c10011088020440844d440e442008402d00200381101c543d0340846000303000d640400400c1c403050340200d0070003140c0403050302c04095529914030a007007640c10070f80c42100480c1e10b850901080c075400c0000d0070b0241081740300030314940d0b181400018040d40092300c094240100304020800348003103c410208030b4407900d0824031004e4045031580c4820380b040c082d800642d501e801c8502c1c01941c0300744000c500468003c04004001000701003009510503140303030303880c0c144810400c0c00340000340b00b802a144150440d0300c03c00d000d454400d1001e01f10301c141407102070459204004110041e03589510036030558080007 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 5428191 1250 5426941 5426947
    0x4050c0301090c1106070903021806010c14030c0a060204030309060c03090e070527040506060412080a031b080411040504080a030b04020417010b040b030703121103071a161107030206 80
    0x4003501c05008482c0c2d513180c54010780040142c12034014441c3c80440e4401c0d5400c160354440006552070008041c4c41c151300180510100e00003184916202080d610901030949182c8562020104d2402c8503512003283c0042d0041400c0050541101c2040d00030820b90030540c141042c1940c0c01440b0394018003400c0d240b05203050101d60400d01ca00b080e1540c950301c90000e104803040540c0b507080103810944100303120b9400d000008101e824034070305840483d05001464090b403400b41d91900a260003001c2c8160416664580303000d0000c1d249800740301321445c50b440e800e520f400c1504040b02800080000c40380100d050100b801700042409046408101e002c1c580040c03c1b00100700020064820b941c481d00d5148090600e541400360107500180c8030380342c2140c1c104100c403003840a144d103030780c2d00c0d20015181e5140350450b03040300b80c0500108400c440056081d00c1c40c21840783c0d9810341e40d5a448075001c50b03280c840f00401c00c5041c1c11412418100006003060503807001c0c0300c0390442c3c0d1031000d13001c003d00442004c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 5429441 1250 5428191 5428211
    0x4050603031606090f0b180708010c17040f02091303020105010b0703080402270a0212060409080703050706020c030f040602010c020106030506070c02011205090c030d050403110103090203031303060e01060504050c030109 96
    0x440384485c001d0340d00211642860070b0410240303014a034411040740190190940c006080e6005104000c1c03881c5080d200c1c6008440a001e60b1100c05000900555509201e03541c1800184d94601051380b20b0003010208010181181c14002e084610580010714400010001031002c2070300300408039031050341225061564200c02002d9000c210b003010403090702403d0380b010f00c5451075003a00a04124030100000c1000c964400f8100400c0d80c00207100540f50300010010080403d11450040c44400e0240801502e002c00300c900583c0713568412443c400300702a01040502070b5a9080c01002c4100e0042e00c001d0240d00d0a54a4560f100c440c050700c581e00313002c20084e020301164000c0ba01e401c00c10608050800252500c02c10181e15a2003c521140c464000c24038140f2940740070b20f0640342500e070072240c14080017000c80c005500404011006a0b13041c80280a01c881c54400310080101540c0b0801c0042018462050080d0075116103805c0240f0a50412007005000c00901c001c0d00d0450700e40f400041211508 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 5430691 1250 5429441 5429453
    0x50d020313020904060605030c030c060318160306050703050106050702090106030209011403040b160f050307050901030605030a050109061d0c0402090a080d020705030709050105060316030b0406060e0405060303160609 95
    0x6401e03009400102000c208004c1c07149541c041c004488081c0c09440341006002c04054840c003c038414194411800c2c008519200c00c0e440403d4411001c0c2801c403102010499240d00c0041034a0f4400c507403480e00c030004c01100981c180105070051505041043c20516564005001d2180501541041540c003042007445a072007850000a030008102c0480c0c0d40781081c2c00d0008545030304403400703920080400e481c1a045c906c9a0728030710100009988040c1192181002220395034000200f1604050b110700300443c180da01032040d562001d125400000d00080c081c40c01109030350841c00141d41c001d4145040e074822a00101d24072041031000c94005984850380c1d40003a645012603000040a0b1081d0070034004040d40000d00030f070a07500b0480403200104c1d41c40d00000c060700d20902480c1e4100d003050010403c0a00389000c0304030102e04604010440c0e010600200381103450980c04100010248114041da500f071a220302d07500584107401852030030380e40800b04100383c40c030860020000c660714460034080c441 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 5431941 1250 5430691 5430721
    0x308160206040521060702060601020303010e040f12030f110906070305030c040308130e150f0f01030e0303070e040b10020c0909011b050703081e0105060705030405031006030b09010c050d0203 84
    0x2030020084c11a098460001510a10440300024494800c80000c502d0043c0000f07840c908c5200142e009504d036a0800e904a40801710181c0102c1d00405440c2601d000601001c450208400540e60300140810240b030704e40003910013000401e99480700400806410307480e10400c541041d505402d060f590b070780b21021405124030840e840501a580040345041500c00070202040846003440e2807405c0980311211110300c04c0760305078131880d44080c1c0000c80c4c0109003015150b10180c00014180011854941da41356415070748100c1c2c03d0300000d82c907514803000502c4e1500c0b805540307080075a090401c45c250154069075510000301c0240c481e18407480019000e440c2500305040100854140020741e00c580071024000d90010002200031868101c0020b0111407245560107403802035a0240005901e03290500080798880d04094405010401c030102c0c3e82c0c2c80030003066000c082d4202d80000c00c0d130b1440c1003a0002c2707100a40364042903410f114240382841e510a041d00c000213920000140e41ea110a0a020034400c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 5433191 1250 5431941 5431949
    0x108011401021c0503070909060503060610110105070e030f060c090d0807140601060909140402040c03060509010e0106091706060103021303060c0305190b06030a050402030a05120a0e040204030816020604 89
    0x962851009140a0b4802c010350f0103046c45e030b00c42d00145c1e078550102c44240c403164043c45d601a40070791f000415910300b440c2240301c1d222450401e00403084c0c403029640d095410071070340340700455040c0750b04203454202002a1000208a00c01074240c900f03002070092a1803041d848528410088208070784280101032080341e4100341c0c007050000000324000221621843c0174421800405d902003800501031030203008808002d168004408400d40d42c1da0b08020051030340c806480109541c0b0302c1d021a00d9122090428040e10146010740030741e40c503110004003040034a8100381500190380c4020420802c1c0011032682040003401c015881e4012280006130100c081e51024201d02e05101d85d890007646c0581c0018041c000c02d82c000100c12071400b2001055034151040d291700710400300700052000c0c9455100c240c1140c40203003070b242c1a04443e12090700e44904119040c84201c0e00244450340705400c0300e4424686a0140c406500f8a881e68583c0b20540c09480d01c14002150603204003402c641d54541200c000d0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 5434441 1250 5433191 5433223
    0xf1203010e1503030d061a04030302062707080c0f0103020903060106050d09060c030207020312040605070201180305070303050c0d02010903080406020a09050a0b0408100203100315020408061602150402010801140102 94
    0x7940091075403402800c1c140c4109600c0a212403080d410507d8040100c03000d0340d4054000748182d8883d4100e01d000081d0f0700d8424000c245034450302e01141a81070103001c1c01410320784000d00d4031500c41020001e02c078802e4043c0700e051501c10800240151804595503044555a00703255441c2e51140740b81401501c881140188803030310708440101ca00d078059001c3c0010500940444a2a089800002d00030f403081d0300404010076001e008000040d8814002014610b030f980c41c0f0310020680d41e548a514101154200318040b0b20041143c2c420030380108104c1c0c440300310300c1c4024081080d40380c901510b44030307024001078011a000180a520180204001d100408025007080401651000305002d5500f0500880c5424000c81e044205810103034000c2d80e0080208400c00f4034028a9070366045900300801482519039502030000203041c083c2408118811441e44024121611109100a01700a40a5036400d0954030f183c0c140400750368000f03521415124002c40b000b00700c0442c000103074508002e201d1041382e4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 5435691 1250 5434441 5434447
    0x160201020706050a090b06040603110d0507031205120f01050607030c0f02180702011d0d0c031202070305090906010206160f1103040906031a1b0a030b040504050f0f1203010e150303 79
    0x213404035400441d0741d600400c4a5003d41d00d03100d0812040e41c1042c0300107004140c07002403407402454000c800084a40c4a1022070b106240e0340d58500300100f560b8401000803806c040303504801c03900b101c1c0c00c6541c0b002160070400f03000d60619001419a0244a0000d010414a62883d100700036074052610365064008240080c0d2000400d20900c410b5011a400700041d400c203114170600c030304030050094492070960081c21014980141c119802010508240c040110910016100d40c03c01d1004185090080da80c250b41e402c00f0405205980e40c010700640d04650260313082000d200d041060181c004003076840c01000400310315038101c4811040540c000c0030380c00700040014101030f0303030380c003400413607100f01c211040c4006c0d00418480c1c00c01046410881701c446901c03204034030f1a070280080009400b1410700080e1070001e04c01050071160204e030102e606a00ca090f03041046681003001782c05034801c0100522000007030b8596585180810702c280249107100b100800c07807180c0e401408810f203140103012640c03 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 5436941 1250 5435691 5435701
    0x405090c01110109050601050d02010903080a0201050615070302030717040902120603070501031506050319050408070201020105010b0306060f0c0c0402070c0f061403070e031606030e060c0c0616020102070605 91
    0x3031140c00140030a80411184403491560b614107003d000310550304007000c0c3c0500da20b080b041c081c0c000b02005040381089102d00d004000a110b401c06411115140d0380001070910b80701b4244104010407840da1303000e00070140002d40000f80e00001710b808050b8003a048401710f41e03502501800b42e01550300b01d03051b100d0000c1410800012401901c0c3d2207524220200d40c4519502e400540c01c840d4020a4a070300c16490070b40900100340aa0019600280070421a51554102c0741020048503000e0741e04441c610b1000030403a080d580d0900a2030301402d40032a0491071420444001151031081d80d41c5035012a01c0803039030405624040c010103641060240080d50385441618000ca00c1c000d450050300160625440040b039020701c00d413140c1c00030306840b80d10300d803554a504806403800c1e0b03048004141d2600c59000b26074180e64055404100401450b05c02195a080712030300b07541044401003c022102c2414070507010a298000303001a0044542440c40f00740d45004003040380a4490640080e00c030b1410703c81482 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 5438191 1250 5436941 5436943
    0xf01020412020109090203010b0301030b1302030d090302090709060203041412060103080309100203061c020d020a030302030a12021303021c0602070b04020f030105090a06110403020901030501061e080a030309060605040509 97
    0x304200b4401d9039a403e0860322403103024124042800392811f0028107100500004151201d00354001c02c4900a074160301c400c03680040e2620160002030390009602d0401001181006ca0110f1b030031480504101d4111401c010000b50740307000300e204461029070003038a119800c0e00e60344241d110401d080801d44989684070300380300c00b003503100369240b035081e1090701503c0030170345501c1c420703a4000c850040c00c86107104800b00310440c40c17441e802016a40001040c14410050f990110f070308008510940140d034641c0b6032140c028082c05209820350340070381d004002007401d80020b65594810747c1c3d0704030380100c14040a0000c0c0da040c1202c520700203240e0703480060a1000d0028800f80179105030300c2101d4065200811100307040c280c503426981500554040d40300d0400040c11604200042c0e15200c0c4401d0405075207400141b0100002c0c2d1041c0c940342d540d035109010414210962500c100c41c0c4090702020140780071036159452029000180070159219882d0082140c42d4100d00e00920b4000c00502c15400c0a190f21 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 5439441 1250 5438191 5438219
    0x60f08010e07050901030b010504051009020a020a0302010c0309050c240703030e0d09212406050405060105070f030513030606060806090609011802070215040e100501020312011202030f010204 84
    0x81d040c00d2240300000501454204401d60513290f1021504403181d2030101800040c100141110050301703034407880814481002c1c03000d0001030401e6802084004194240a401c4030b200030b407038008044c2020b41c08808920001640807a6603010341d160b1410503012580511448902851190350f103c000a0308824954950030544243c0d82d2041030341e4501499810036100c0c0c40c958032446201138880d03808140110141c1c0b00b2019850700402c908901400c000b044404480d4401d580c00c118207a03140c0c414030080c1800c0c400e003a4890b401703081881c60403070143c07036058000385200030003010890000f0758625510b40801201000315803100003401b58549800c0090b19080c0100c0d02c20f801000e80350005421460440c070058101c403a40c241c800203510b850f0311600080d60140390280c1e00b180000d40b014150540c1e0b140104000c003080c40350140d0906180c0030b00c80000a059005c641154070038044040c0c200c0590300341c0340c1181d6211448620000e454400320303040031030b02d25503d01e09520100780000c08890003030031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 5440691 1250 5439441 5439461
    0x9050d060b03010e070317090108010611010e030d020417030a0503060603090109020a06030e0d030603030e04200304080a090b0702010503060d050f070807080c03010204030506070c080f040b0703030b03030c0a080a03060f0801 98
    0x21042d4018811f502d03401c507070207100320440c0069905c00041043c20702907151042051118000803c4400030a907100c2d18660180a81c0e40d000e80c0c3c002010818942c2407603480d81c100d4046c902031450050250f02c01851400b02400e502c0c0300d000b001000c0b500f401070035400751190540c040c3c40181d005a6824018000b0501c0c0001d5240d1805070b0040b00d1071442c03291040c141601d5050300c40746010040e01041c0002071012300ca2176003e46e0051180c807021007040f23101440c40ba91150007a144e8401003010f006002c1d0445500040c80c20009008800050b81c00805030383d4040c2c000e84001030414002e040c40361511803080d0007150b107402507841c0402c100c4000300d068015501c031602100c1038161401c080c18200e12451001400580054000c501d6840c400c0702e0b0713006524024000941044150905440c6640c4941e00c400420180080e0250405826000d680841c6004030091400c0c00c00c20a041e42d01d5001124000b0501040054000c000074000d038041000f5262140e2040b00c51a201e0740d2072402400c403041c0d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 5441941 1250 5440691 5440703
    0x40b09131107021c020d0303020307030213030507080f15040204050406020d090b090d0903030c0809030321060103050a061d06060f0d05010314010e03190201110a03140108010b0109050d060b03010e0703 88
    0x10109600b201300700c0b040790703030301c1d400341011040b0510364400b00c00940001d03290204260b02040f1404942c910280020090760154019025480c81c00000525140d4111140501a004203c072085107880e0b03004d0590340680c0555000c211507545182a030000d10802c00e03103060781e500d40f080130b0090186408105120321950b20842d400082071107010349440006100050010b017a65140c6000152584d000d0694100040c0031241850040020001082e15146200d5408000d0100300b240719039060142c103410108031001000100e040c0b004030703031042c20b03600f06114035440364102203402911001c040b6100e03103540c0a40c03203440720746016801001d0701c402e200503500c40461544030402c070b80041c414000d1803a041c1005600d42441c5508011800b02007405d190295541d030f5440c540384132220801400403601e40d0703500103601403202c4460450103206810081c82c0d603150071031611031a60403540c01415520100d13405580d100700c42c50400080c3c08181c042607095400c155456401c198001b40f04010350703200d04 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 5443191 1250 5441941 5441959
    0x5180610020601051003091a1f05040c050a08041115120f0c1b03040306020418051005010801090f02040b160b070e010806010507030203071205040f0e010506040b0913110702 76
    0xd501265107907403c0c06080d602c4401d05e455401e41038001c0d4000c05805110f07800e04400b804010b1001090410202d800f0002601001a0140c0c0341c041481c10320041c1004440070444400a19801400d6000b10034406081c00010310100f800d00208100c4002803001c002c000d5542010402000c80041d0401034811030408000da01059500308a060300610a81d914002d182c02c08481304074040300301110700c19107a401d0004000200102e1020700007040a8890441401325003403c1e24018000c4030350051144a07840403016060146a03840300109044880981d40481ca14424121100c005c2c8541c2c2d1055a02400c001480c03ca080c00780d10521141c41d0007a40c05640c16a44c0c054169500c041c412040340c001400900011a2503000b50b024165403070092045a00700305270350340c914494024807860400441c10100301084080c0c0c0302000f40024040c1c4410802c800e501d080042a02409240507840408501140610890700c40c120654040700480300c052140b20b0001d1542141640254820b90040c00c0403 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 5444441 1250 5443191 5443219
    0x9030c01090506030a0507050c010c02031306080708070503060a08011a210303040f0f05010507020c091e06090402011b03080103020f0d080a03050a1508060105030706020c031e010204051806 83
    0x5040201c212200501464910394880c80900014071000301544180301c0140081c0e80341d0701c000d1040c03d00920064008554a50351070f41801d80c8400c5a41c1b001d02045115002c100c030b02540514002d80090382c3d8180b960303d80c0c0300c0100141c8150211382140803030358a04045140481c9003550f640f450f054040d640441424045a03824140003c98100312420394000c0012400140418450754105401212070306160700d0b15944103820b4420640d0a2001030340112a010a10700e070452149170131480050040c000c4a5018011202548000b00b8061042e6041c0001806690050b00140040e06c180c0b0f20030410983c151030003130b01403c401c1c081640101c106c1c0290200c1c5041c40f1a002d02200d401503902c500380342c02810300b10042c042c000e00c03150615449040f2460b00c500c070310b40300001030074020000d869035604210905103003240540c00403045501c20090310503d51000b045981c4801c4020164440410700742d49001d000e44a03990046401c003043ca0a4411042e07542d40d00d0900039403007210401c48180d03107 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 5445691 1250 5444441 5444447
    0x7081201050a03020a0e0c0906120601110606030705040504050a06090b010915030309090209010c05011803020c030102070c0506130e07080702010c020109080a03020d0f0203011203080901060303080601030507050c07090209030c01 100
    0x80e020007174204d2510403050000610340480300358410428030301d4074541100100800d00c030b50000c50307000c0305860829003445910741c0c03c421105010f14215000b00f8040c500700c00003036501c1030244215801290344001240501c4800c0c03114140303154000d54180045041850259003401092040c0390020740703008400c024950000c850722003100e03019a00c0051280c00c000d1540d0081d40300c0d60026040c0001c0c000900c0c0000c00a000e06e44080004990803240b0b00c12500300603040ca6902c581491190740f041010340b002030546c0000909640013601d4142d10b0b20007141450700750540c00e80140c44210400303410840d50719030005c10300e40b082d0301987c001d205640d0114006e03401d0f1580c02400410700e41050114000031442039002e040801c48002000c80d5403100c8909100880c0d1080c2c1200c079041c15010400d60900d5001081550000040b03002040401d180d41c41c01040080040c02180c105a219030104412900c11400d40f400400e01c5026900c4155039075104900035403080164500901819011144a40c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 5446941 1250 5445691 5445709
    0x910020a0305030c0904180606050f090108030a050a11070e190504030905130b060d02040306050c12040201030902040212090a0c06170408071416030b01090902100c170708120105 78
    0x1e490340301d541c219140d40400511070f40015000b190080d9030307480c4d00301c064011803003462070080c01840000740c0c5504100c1407080c280301c003d4810340140c000000402c051b0000100310b440e140f500c0d107419622401c0d00401284c00f840c12071011081482100d00210b0300854940403240100d590f80b90010070703c1102c14007a000d82d5400c540140c00f10301010020080c6040c55800c500342072100d1900014201c1943e0006151600300310701d034013030240d07011500380104015481100d400c846201411410200e0503c0c0842100b100200000e0403d501c07100c45604545468041e210712043e07184400c1180d02d0018071866842da103002c070955904103401c1c0001041070003a1250702c80c0c21140500d41c0303440d17a41c58441d110107900014080300c560140311008503c0710420302400c569010366841042d03206285041c002c8001c481038000404240ca8502d43d00700590352003454620035005404c254200194906045001c0c80d0041500d81d064140060301d03008100d95030005010381ca1034041d160a050341c8072010700c14086 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 5448191 1250 5446941 5446943
    0xd05030c101a010f02030c010608010203010512010b03030706090609020a030303020d050703020301060c11180106020717030301120b040501060e01080d081806010b03040c050a090b03010b0301050f0610020102040306110910020a 99
    0x407005036041c403000e51080894130104550307030040300d14000710404901c1c00c40300e480d1702c105c54995010005003e1481d00500c0e0301c0142158030001d000c014500310001c0d4031303445010b0000780b495540c0c0c0454000c000c0544c20500100350003c00200c0503981d2810054041d42c0304002264100e803074140000c076410300903c29241a1603075551803c00c0e8030000d50b16901000104046254401140110014505154030250380a40f03110b6002d404403901c0e00d00300b22032444003441c03012865042480107001c6803200d40306400070700750080410340035500e0f1410b2150040809400240402c0c3c0c10341c0000c00c200600043d020f91028a9584111031075903003401d45802100400205001a0020001000f540311004003a5400600032101518810781d101d0005d8000c1c045031b0710141d0640e840381410340032464280300b08101804150024006840c000101200800009042512400091030111304080c402d5054401841d40200304200b40d000c0c010031903485800024940d071141017015001442c040c800304018400c1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 5449441 1250 5448191 5448221
    0x606090b011106060f0301090206040f0e010f0617041103010e030306190e07030b19030c0501030608160603020a0903020307030c05030115060e061b06040b01080105070c030203091309020d05030c10 86
    0x82d04d4450070440354840c490b9004c3d9056486046480150f44c40400800050001045111115282103001040d04405a00440a031060307100200300454000030b41c0b84009502c2007000140d0b585a140c15140040302005640d0150300e4042e400c40440b50000c01140180303400c4804c3d8408284042804245071441d009401411320340d00c010034043d90080d0040c40d141c22004000e41c10203000c020304400c6184181d801910b82d0002c04004004558244c420540501414070148c050090f00344040b04c0702e50007a118850800d80d0006001c075210344a801d10f100070b5075005054804140d52810728240e05c46880c003800d44a1751a2013801c2c3d032036a00c02c020388000c40728507484001c010008a81082040c1e081107500180458429a09800d071280902100f4801c9200d4400c0303103950350510f1141821140c00800c05030510541c09901c50110b90000700f070360780c1034908903040c4aa02c00c412a061014100020b40250482c041300c4082c0100305c004400707800d035045020212091521a071120000f5101078454803058 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 5450691 1250 5449441 5449453
    0x1050904020313020603091b010306050306040312021c0204030606080601030209040305090604030803010e0403020705010201050106090e040501110f07060b01030b06030408070609050d02070603110a17070311070606090b0111 98
    0x126003095009564003042d80343d9032600800310740d0046007036a031003203030080705a800500741d8003c100050481407459407002c1c81c0820800d42004040380d03031080f015002400b4064034440c00c60403d01190120380c20740f15012801700e080156000c00c0340282d0460700007240d1031803c110000c90805000240281282c1c2c004290200711740303031a00c0948040d4461814940c10040400022004c6009000114001c0c070f85140412214a05030a000b420010315070007140c110390404c0010455141d0155001041c3c0d061201c001080b80c6442c90418010700c4428201c01c0c03107902c0480d522420180001c0940380c00c40c050b4800b8000303800400011000c55a0f2045599408103062001c0340c04540c503000507110075403180030000340c104020b0301e40d240f92141d112064070060740010300920035281d060103141ea00d400304a071600e040010710003000d031011803107034074520700c900314500081c04a601c250444100d611548886580d00e640b00d01308007025019a005240100e420159040c9195100c1e0303244140c0b1407210405031017 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 5451941 1250 5450691 5450707
    0x20c180106050315090c071103010605030607030b03010207050f0c0901060e010516050a151e0506030a030302030402010207030b2d06010c08030709050a0e06010801050108040503071e0b04060e0c06090105 89
    0x240507080038207130b03c0c1e80d80c3c0c88558105480d11410780281c016102d40c5502c603182c1c41d042c03400e075281c0c3c0c5200c042d00b4044d904000c4200a0760314009040c68001d0154200800c3d44c0c00d03e200400c1c02805540406412403207084a81c02d9450303008900002c10220943c0c079100c2d1682c913944c041c2c599000c031104a134000382c02005038036060301c92080741d0100d5512500584080d808aa201ca04170310880341801d0310b4040c2d0790820f480700380c00d02c0c0c50181108040100c05104170326003000040d0310754194090103020f040e000000501168402d00940010b10340c0030308401c0660405007410112515104590030042c19184000d803030f04076a007071318a442040141d41d0f5180281099440f00105d41010f403240c0180241c2d000b01095560360b0000c040083d0846d8078801a0070300c5c00e0800103040703030410390055040c801100140004510302000f1500d04c1500032003849444241104c1c3d8107040d0020354400352084448000313010402440d0b421040030340380e01100326000313400c204082041038442c034046107000c103800b000922 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 5453191 1250 5451941 5451947
    0x602070e0c0c0f0105010501020705030a020a03150e0d0503040209060d050a0204110c0703060e06010f0e0a0c020a14160b042304021e1207030501030b0105120a050d0c0201020c180106 80
    0x40d40400c1d8003500508141c5001000c614000569000001c2e070794580c1c00500082d41d041180500800703003100180000c03031407600810f000c501540030140c82101e0040f2031014018442d04034000441c900d1003100d0701ca4651090041035500155001c0740b040071400007050452524107260f0302c07003641040183c00094299420000280069900100b41c00d00a0204115044042c03252800441c051380e4017040102c0b400035403605040050300f09082d543d4031624103211211095036002d038400c070207440000c0d9020307004005031b00e40b40b403908000b01040882c0000c10900100801c10021903209240b01c10b80352074641c003ea0782c2500803400ba41c80441940440c48050f800c411a030f80030a040e02800043c0f60058855008203501c0300a01d541c690804005203d800544101c002954080c0840c030b010400c1d541582e031250325089042c07017031900c0b03074600044092410b40e042c0281500a41c2c000304681c040400a9000380c03958130401002d80c05806481c6800c103550410080f4070030042e1111140340001e03801c090040d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 5454441 1250 5453191 5453219
    0x1009090203060409060c0f020708030415050a02031207120e0705090a0c0306050303030c030118050103020607020d0203010f14010807060e09060d0c03080d050105040f090f030302031503060c040e0c04060207 90
    0x20703e0b8095251100c620100d0341c9071082c012000410303541d41c82400c5140c031001c1c4c540103241d404041e040e80f0030007081160075040042e4072090100e40c6000c0d90703120032825040b45140510480c20703080000100900c201560040300310550701300f80e80018400f0320b1221500382d8913820544140e80d0080004030008a024246a001015a2805050014029485002107440c60300201c1e000d644c0105c0020040c04a0401100d03110459050b844d4288402d6055a020407d18011240700034005e010602002c003c40d6000e4105505102821904006d1626008404014280284101c0c144c60080803808242c5621400950650325009441c031141c0c0d80b45c1405201c1e880e001c0b003005481020720b00f407001c030010b0811001406982c0e01048080b0321541480e041000720740d01011003466417442e2445035400a6412075880ba511501400c00507120781e2503202000e40840781d10b0503158540200801c016072040c4000c027520503a18083c07040780c03940d51010694032080c0b089000b21800b41e403140008010920b00d1001c5 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 5455691 1250 5454441 5454451
    0x1908040f02012a06020307080603060702030702040906060509090a0201090504020f0301051504170a1208010302100f0203041a0c0c0904050a081806030108150a060f1403010e190308061009090203 85
    0x420a031103251421118580fa0703c907003195403d40000502100a40c85840b030360300700c10100c003d0400da0402c0c52020b5568070071aa4000d0180da10342e280d1105200242d4800c5000f4074002d050100c652030244c110b50b4598244902c100c0c0882c0302d40c00c010400c0d00301340c4241d2300740d004040034031440d41e400e00d02048a0030803504809102e1072030401c40410108a80441480d8904240004280c0b100340c0c1e107000d00c0c0c5454154620010001a2401080540e480760302100d00c4d079480d8142540581c148000480c194400c603009031206021044400c91075600c8000141803c094031003d95000d41c181d48200000c024080e075028015074070078030104000c62803150041541c1034801100840f007a8072030010598035042680040442d420102904103100d11078880385500c9030101d2400c0040f1800d103071410101000600541c0045145c04454008646096000c1000c41c000403088074099484180314041859032414100c00240c0351801007041424050b543c0348203540c20b43c443c46111030404100307100035003001301 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 5456941 1250 5455691 5455727
    0x307060e010f020703090305010b09070804030305040c05060301080a1e030905060307020a15020702010e01030903050406030902010516120f0203090a051003020d05040501060626010e04080f040603021908040f0201 93
    0xc82107070406442d20013401202e202e511895409031650405a0031a0f0b0344c5180a03004403545810025a02c0d4021440ca40c082e505060004280c2c0b41c909228107035107565004650408400030020a0000d000614080310520581000742d030b0780c904842220714131100321310050114100784410712282c81e0110180d1fa00100e0740c411150381100f192a850103141c1165500310600342c2c0001c00b0425564408500c5580001c282403d200c104500d941c000c08a108a10910b01015682e0342d40314216031188085800d501c10085a941240300a03003000b49000800208a0000c21000b04500305000c3c0040155008420300600c0807014038680801e11404503002c1d1002c40030940c0c20000c14080741142d1190710f01450040000003006404c1c240041c19800b220f42500d000745086440013000d00d00c41c0340f1058103550b84984d59490945071032520410342c1c0200c1d90b4142401703d010030b0104190754583d0103041710000088406040072000003080d540b403c802d03540504401b041126030000344d401420607440f01ca00d009 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 5458191 1250 5456941 5456951
    0x4050f01050109020d0f05060108010b09040f0212060117010609090203130f0c0503010506040204030807080a02030f07050d0f080108061303090801021614070518060607020d05060603011d0307060e01 87
    0x81096401c6a4090300f220700302c80d9010400035548415446890b0000007900010001400c0240002e007500701d051151100c491800544404503858079080440c81100d009401e54440c1c0c6290780745220320000311141400620407800c1d107058600d400040b036048500b10749580d0840e40c01c3c2551325001e58401070092401c1c1c01504110000a5000d10414030f40314001c185010905061404141c25a0005083d03648914014442880800c03803c42c00c80b01c0f107661103170400f5030350030704000d00340e081d80214403907003498900206040d0300b80080404c0132a81c14010340e549109900c0c0044003590028801c1c01150001da2282c00051914000e8601c4403035103900904001910b01c1d621908a426607229034800b03060aa5514414400c008480b8810707111b03441000003074201075041801043d00e40780614490a60000c491020490b035440d0b010484425030b802810f20000c142075410010307614401034405600135032800201801a1000b20600004000000081c52400c11552940d0026290303010068070725541c3d030 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 5459441 1250 5458191 5458213
    0x1080403051305100206160519082a04060206160807030515040501090b010e0307060e0108070c0606030b18160611010f020a0306030512030601020303010603050a0b0a030302030d060815010308030405 87
    0xc0214613800c010306900030302582c034001c141e5403c100b1982c440202440410b00040000b00000340503803000303100501e415003040c3d82d4071580118a108212840c4c1e621080742a0350f60041c4174840040040d585140c08842c86a00c852a540c5101e039080b594410001d9500e4000ca90200e20035003040350841c1440920188007001c54000400320755007030344128080d961329181b1711403d5030003c8510b540c84900300c1c00b5020b820301c0e24001900070000074440b04d0402c01d440c400200d01e18014900080341d40c1c0c100c2c200f000001c0d00c0380782045444206136208000c404041c00d540300f040c00c0000e200700580da4105034a41010340f8200003910140e05041141d0125522040e00366408883d901c00741011040d85e0740c0104000c1c2c9181000b130708009082404c226010404c2080041c980d80000c1203e0440e4000d240c0015150b41d4205100000c01d1a29401c2d5403101d07844100005066001014000c40c0303080820401c1400c1d0388020380c1eaa50407807180601d280c4e005c607200400c00301340d0240c007540d40180030f0b40564855401c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 5460691 1250 5459441 5459449
    0x109051005070203060f07090b0408030d020306030f010f02040303091e090522060902100c0305090f010309020301020d0603031101020a0207090504060204050312040806010e0105010c02040f020c01020d0b12060601080403051305 99
    0x11246c602d00501c8801c1005a0550312040400081c16110b0b20203291a0520074a60784130b100390b40c080100940c00201103070f15914200b04940d0321502000c000c008031690b441625003c0c0d4841d110030340000701c6000d40402d05201000420041c6c0d40e4494184003071078604101180500001000c041901c095202e0880042940c8520780c1c070100d00c9440000f07032100311441000750f003504c1c094120040020422600000070781100450304810342c03c0b507084641e14050030040b4081c2c05c00c4007000b50507500101d040c0600a4041e0010000d1b68800d44035401c000c41314003000b9080340211020b040050703000f810100710f801c040d0b0b4805a0404e00030040036280c1522280400e280c6120440d8040e6643c000003030030018500140406400362444001ca400c140d450000000c01e9110304283c089d110f2a075446005481001a0381120040303410007000703649820203045850001c01000c00b0650094280305001c056081b00455101d200d010142c55250380b80d1110b490498440d00400d603403a003050355110000c0364642e2 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 5461941 1250 5460691 5460703
    0x11107060605090a05040218060d0c0806060f10050403170c0a0c090c03050f0105011209050115030302010e07081e07080102040b030402130515040e0c0603010b040806010b03060109051005070203 85
    0x402884046107880c60721081c0043da460013000083c030345140c00c1c24000183d50307041c0d000807002d031240a10100b54540c04001081c079440b4090082204000711070001c0e40c0e0b100401c50601c01e880c00c449030401002c0e03243c24820000340d0408281c0004108202c2031002031035043c08001c0c1c40c200c18070540e00300140018110700c1c0820048003030326100e00101307007040251024007605100ba8001d1400b40041c3c1088a2040510001030241506000d40001a603117503203010340c0010341941c1c000c0028040000c1c040820120030362a804280c00550a11050503401034000079a841100e044000511600e451107400341e9481d003d010240229000385100000c290b04240040c0014140302903004d90b490070030744100100709214464441c0e03120704101c01c00c17545500d8180040201d8000741c8000c241040c020000b141002d402d40400790303101c080800086545984d54010b0015504000d00322507160740c9800f4260310b280001c403038460020340341440030322050401c0140035001801c0303800c00380e080a9141d400242428 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 5463191 1250 5461941 5461943
    0x100f140a0801050310060e0601080405010902040603060b010f02030310060c030504080a0305180f01020c06030603030909040c0501140c030304020103021e0703080f060f0105090d0203070807030602030a0b010806010c0f020102011107 101
    0x2071446001402203180a000d1021302028100040103c0b610f82616240c039541c0041c5120b0501c44008002000e000b03081d0040c8503c10350080c010005652245040001000c202644500180592400d000018000011680142c110301c00540c0d01ea41352071421a00407001c0001181003100a000006190300708220b003d00c001d110b501e03025104c00003000c07010100c401e2040c1183c803a003801b6201c07080c140d0b004104405c4100b0306840c01562503440202091461080401040d08400f41c0300400c014031494a84040503160241d85911455100328144039071409244c81c5500c982e041080030800547c000d5009010010709280140140721030310040e0b0040ba00b02d80025030200d080c040070404c100d001214859480901101e540351084880030000348140204424240a6803110903040159641006210000c007508000c43d0700581d180e1520700080e400541d00c124007035040074001c206642c02020300510400040c0d40d80d25600c1001c0d1030380e42c01f4454816003641035541e900e180c06551030b810300c0200191 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 5464441 1250 5463191 5463197
    0x604090e0105060f1305040309080f0a060c0201020304120c170a02010902010215220c08070314010c08040b040f03032403020a08031303020603040302010b180106081005100f140a 78
    0x4215012801402d5640060800c0d12403842d110080e500b583d104081003110000f42c1c94001101e40d5145401d03103183d00d480d00110018821540600420b4100141c000702d1030348140814840b003040351800380e090380019100103002c1c01e07011b00c0b600c14481c0304001c1d05540354041c0f1350f803040f60501c00080780000e5105490f00c00046c0d44030034400b0155601000400d00040d502480d205c0c03540360042c1c0045410240b59000c1c48000082303140301040c41110065100a04415026524042c4d40d910b0304540c05206000640c0082d401c1c030030701c049000d000b811400d2040d40c218001c05041d964941d2070300c994041c0e1103001c9041c0365030b40d0245aa40f402829010166803088400da05440d811401040301c0b02d01158002d00d41c51340304201a02d11440c104d000c032012039505945040d00c1e5111441c0c1640035081405103c2d03045002d4903d1400003c3c0740c2040303181261603d80b200c1e48a611150a68003d00c2003a01555411420510303120118600c03410744820303114403078508a9030a0380440d1106d280c0e0b9220007081000 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 5465691 1250 5464441 5464451
    0x40b0712180b160203030105040905010609020c03030708010806060f0105090102010905070303080703060905010b070f020114030a0501050a120b071d09010e1006020d0e0609060708030901050a0501090b010207030609050c060409 99
    0x204041c684580c0e801c140140f0314410460011a002540e0b1300c014050107000b192280c2c0c45030200503003500a40701400035a1403d5489000d004840390b660f070011203091002814034000040c82040202d00540142409006542c045c3d01820064070300b50b1000103494110740d618615000400d00500040300514400e0755207d10034288032400509460b8503800c034000c102e1400004018240407074044403c0b03945e10411098002116000682e041c0702902403a4001010000400414030542d51020341078400441c0c102201b60f840c0c4906001060300b130400100348000803408078051038042c2c101c0100c207662040a4030078991007100400d1b0014002c2c0d10408000702d08109204c03025400701034a80142186100408081c500404010003a82c20f11440c1800381000003a10459a215507084510168010312510354a003414913000c1e0003030404940c0e0040c2d0600c2d20001280e82c81c0140104070440c00d05030700a00310a819610389034001c1061030400c4805e032055a00c442030f561186030103030004261b1002e001039 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 5466941 1250 5465691 5465693
    0xf040b07060902041113050f18071110050103020612060303040506040e040605071809020c03090a06050d0507020309010c080309210c0f03040f060f0207031b031505010e040b071218 79
    0x1c02e0382d031030369410f003281031701403000202d42c1c1280b180c242c0c120b41c2c0845081b41030303540e20340c0070844051b4400a99241c27204148104580581c12907260901c4030342078400c41d48200f0520420404644082c00001e50205003000304903560210845140d0300100000c054915043d41c4800150f599805688407000c0b60140c01c0800061104500c14a54080003e0500b0210700c103600343e20a442d02110700901c004a0b6003c2009408001c0c10800d030341059a018000380004c98840c80050001c3d0050801c0020440c02c02d8001040703284040203a40c02400c06071585030108550b99a038606e10340008226040511400c0030410100d42d0000d03e0310707082c0b80b2030445140d6842c0700d241d10504001100004440d02e9104000410003007030b50f00e064008907000c0c7e00e4280e02d40c0541400881c1881104da0000c0e028590b0850491070007642c0140e02c0c0e04803449a001a800300d414012001d068030300034424032441500010010700486c40d0503c17031382d030b0044080c039060720800500d0214404980150651030b4044180e440100c0c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 5468191 1250 5466941 5466949
    0x10b040f06050105030705070510050c07051b060a030b040209040507090f080601030206030708070201140c0a120608070626040b040308010501050705100e0705061803061602120f040b07060902 84
    0x103264005250014409181030a0010b007940c48041e08500c04c02400142180a0140500481c6c006480c2d840086c051420440082041d981055105a500b4081c6840d0314011b42d50702c04a03411005809442e40f814907504030420303401400c011881d2504240c0800440d81c1507555171203503601c03d05039603c500e03050350f051040744503130036402e500041c00c1c5610901c010320250380d0340415260b0092017803600107090f941e00c0c00120301401c03d6001d640d581407022014060101904c80c003030a441c980c180e61340d4101901800c10402034418511075004a504602018410f0b184500500400100c160741d050010101003000c00745c0c147c404490913140c2c8100c0d030302031104141e80b2a00c551300418003460050700b0240030351289900c0c0d0303140c0500840a03503030740c050460548005101c08070041ca001003206132692070080c02540e01180c1c0031b081703d1181c0260b0300002c2c00c5c80e01c5800c1c01e070603000c05680188002c440c18003082640e0390022a60301d002d407405000000d142032a940c0180030281c4100401700e0b403110544188 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 5469441 1250 5468191 5468201
    0x301110c0607020c09040c12060207020907030504021c0b0a0c020c0a08010c02160308031503010b03011406090601050c060103080a0507020a15090605030c0f070f21020c0102030717030612010509010b04 88
    0x803038805c1e51510240000314071061030346010703500c941203002c405107018507041c0020711881c4402074000700c4460410500c0358140d131085200e58000e0341c9206610031080d01040c6403020602000340407130024400700f4011907843e0b12101020100b801154203030030070036000520601d0954801001a9190260080c409906010521100e14418051000b00c1e083d945c5601181c00001c00c11592000304044509469409400a01101c0c0c0040c0003006010140064141024001c4030014002c41100022501c1c0c1d512600480301c424011402401069086684409560388052441803c00100380500005a03481c0c0c08503400130581e0100321065200c5204000e049040558000c40c1440010310421076031400c0c2e242210612180740050541e02c00c00c52400901882480c08042e040481134146d48407180d455607582106140c00340c0032102c00003082001282d8070702c01d420303000f00429411120804281d4015010b5034100b10000e008490060240803514211034044540c03e0090391145041c04440c02e00d4452 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 5470691 1250 5469441 5469463
    0x5130501140112060209151305040b10020d080405010902150304031805010e100504030614090708190f050a050109030905011805030a0803040c03080a0504150e0315060301110c060702 80
    0x3840751540c9402e0841c2940100070101a03d02038000900401d140c0d03850050b0b0310224440c0c5007058030b50b8180d04002034824440d000d03041c01946802e01012151420221040c4d09070081e070300501022240c01002c490001001e001200c2d650340f41c00d56100180e6031146038842c2c2d2101d41c2c02181e00d9160030305000b459003d044038400a1441c0114050159990107401c007a80c3c50f01c2a9183c00355a00015030031500fa104650001e001c4a01e0b043d1302d40d0320000c50784d0034280118110310880d8041601c4110898070f881007010011a18800d03410007200080c1c82e11040b901d024000c01c10788901c00c10b962103c40c00d40740f08400450005030303015824400c0d9a0404921444500c50355a480f0440e4100008290341c1c0000000290100f40b02100180c2003008284407540616484043d55440e00d41c204005849904107024403508804000d05458a20703110300a841074041000b002000d01c60702c00c150381900400c01901c40307501552100003400e4a003908030003c010144481000301600d203030041000b410705244001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 5471941 1250 5470691 5470721
    0x30c020a1202010807050f040801020705070306060e0f010909030302091306060809030901022109030a030503060a05040b0f10020c0301020a1e080903030f0907030b070201050411100c0b0a06030605130501 89
    0x1c28000540d0303020703001650001003810301075500d9040551800300c50265134803c212640c00002c048082240100701c2c00200ca100b0301c01404429100c810a00011000300d9402102008040041003800c4a6410240040340242401480c000e000c2c00031446818501e0484c1c1010f680700c00040000d15072100311281d110040130f02850403c0c83d8280000d44a030002d81c41c4e45038001c2d0409607102d0b804890411110400b00040858050341590714000d0102c3d00100c41907441100f0101000a042c00c05d030148103408540208022141c1c4010000c00003000d120100401c02c5204142402d5001c1d1030920003002019008d490382c211603541c5615244c4003a03480003200d0f003040010740500a18400c0001a00e40240c030346031400200d66184c806039850004190700241000c00044240020f240d0113511040c0294043d07818645200040ca05000f181518224a003000070000071080e0046014000c14a810180303403480490100e0381d986801042e11410f40d0881a02d6001c1c09618040220074400c6084d00700d40302c5 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 5473191 1250 5471941 5471969
    0x10050609010212130b07030c051005010303090302040c02100e070807050f032107020301060902030108010c02120306010e010c020603040b090f0c0108060607081306030b030c01030207111903080304030c020a 90
    0xd40000d440d407807280e40d4a50000800b041e2502503800300010480070340302110005880d04030500700241043c0030324034155224014003100e117074203000600401d41070700d0701500c0b2400440d02e10780c24030004000c421a52421030003000205a4621254012100d00302800001810414288446141855070f20351100c0e01c10780700803040c00c45648012820003d19040c0b414041e0764081a64583d00d414032500030000c1d030651030010041000540c3da80a51f060742d400500070000c0b95100001665907094809184440c0ba5007400054015031040002020707080c0d062504c006100300a5021442cce82c1c0081c1d50884840182c841048210743d4200050781a841c011070042820404201c0080c01850300503003c1070007200d00095010078440f09500310361a80079000080c100c072642e507410040c02800d070202d00744e00c20701545010f908a50311034000d40fa40da540003035842c1c20316030000c0c0c00c002c00310f92248603441500d42c000c1d07000804a41c0b08005107204501030b448403900c480f02e0f4810081085601d03080455180f20b49 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 5474441 1250 5473191 5473207
    0x6061502030304020a09050705070b040b0103032a0b0603030c070b0a02120313030302091807090302010806041406040c0903050706020304090f020f0d0b03030405040e1509030405130f020702040f05100506 89
    0x1170303940021121000c200040d40d0312224400c41d0581f044e003e020301000f00c3c5c07a040c0410090710a218030b04030781c001c0c3e5840ca03c044042079240400e038a10912442d04112503510b220116145041f0240c00007001000c9a1900200b41c0743c1c14200f082591020709922004603d100c0e02ca41c052000700391001070b40802070f10703502e4042810081010301d0440035003019404542c0d6a01a1540300c13500741d0790605483d962030a0720345500c0050204d0164002240000c01c0e54000c100d0310304250041181100100a40001c0c2d540c4e14001d11004100c0014140100010128008085101401140003a04480e40695602c0d401c00804030705a5401583c0c000c1054410003039040100140b10640d06880d00400c00030411154920000e03265000d103402c816800b92a0010020841d08009441100da0b02c0340241c6c07004982c0c1d10f04015840707000310710030f141c0c200d04103214070040e0b5840c503441210340c01811a00182001034031b0300031500320303040580000d02c0b0558840c103004000c480100d160000700400c48541d486c040d60 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 5475691 1250 5474441 5474449
    0x108010602030a0309050321040309050301020a0c0f050c0a0b030708011202150a0c0203120703080901050115080a0609020d020d0e0f0304050d020a0b180a06080c0a05030c0c07030606150203030402 86
    0x240030f00001055512085841001414000c85001c484002e24010004501052818088506a40c04c5020420a04000800d42010300a40300c0482081d1282403d070170040d2110440302403500d10448032401a0307074603444165a4880e0320000381a10b4000d09071686041e81000c1d0140b90180c102d884240741e10910a0016541d000d03012460410742e103296a00d0f040003007400e603518001440d0081d8140241c0703d02142d011a60000742c807000b030003a583c220441c1c403944292800c03100c00b8000c03172050900907562001894060045150001403000340062215580c40001e0120f0300314803d802030080d00059107503011941400741030200301d9000060103914007242841c0e0750fa40704600c20140100603080c1c014040d940d4007400742c0e00a243d420079042d51550f0701450a180c11113014147d600c00c1900c00b42c045110340c410302545100d881d1130341c1000d00d8004229000e460030780004001103074a03401040420201d80042c02803400070352090300c0100307609040c454600c048040c600029401c44d4003d104000169513 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 5476941 1250 5475691 5475697
    0x3041e0b0403030b041506020303070201060611030d0b010507050f0d08070f080a0b03030405040504060f0510030305090d0206090d03021615050403080702040b0a0b030603060c1c0f06080d030911010801060203 91
    0x54582030011300d00c44001e001c240608001c1c501540070317a540080004516402000071803042507113500821407251503035429115960b48000000580d80144103440305010320b50b100b090003580504144d81130070b0740e6a0f00c25190104400c03070075660b81c001c80d5003088000c2d002034107680c204603141041d83d016100208000d000c132a00406502e940303620346c14200b40760b49090007110081c0c2006003081c066071800e03040803000380c4009244003000c6490f0a00080841480c0701388075003903c1d030598801b443c0008400030400c01c0004403401340e074009000c20004400d03503181441d0b64400741c0f00381c0280149d03056801404243c1040355000360207054030805048007241e0f002c001c550580b90301903000303501d03142c182c0041802042110340c416005800400c022031500f200d81d02862080c60105c040750300b143d807400c100a1290182c481c051907600d0328000d110002d5047e07034102103d409440c001c00244196611015440c2500c902240d9000c81c1e907031807682050140040c00c0b601d04a0007801d001d0069458245c2c001e43d07070300c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 5478191 1250 5476941 5476943
    0x80c0c10020706110d061d0906070806011b03110d02030906030f0402040b1e010f0801050a0302011101061a0711010e0913020d0c09020a0908060106080408030907080304060f020c0a0e010b0906070203011103041e0b04 94
    0x2f00305040040d480d6802410204030000702c80081415149091070090100100d41070b288500f4400c100c410207145200004a450a00000c0d00e05403c44d104d840744d01400c0c1d100075004990203600c840c98000f4a0720b8151007101d000c01080b40c02c99001071881c00151041094811500070810100f00500c256110310a00c9400c0742d60a1030441d03410099110b481c0e00400304c07500010080d07024a6505803200c007402d0050310500340a07060052022500e000151501903503046a2600070440c2000110034002d4070000c0342040c0d00245c08a4191070541e540c8040403d980d410000e0810b83c01700c0d0381801160701c07040a41c050701e959801400c1c1e550500c4406401c6100003003006043c900e001000800c00744092103600c00600145080380c1d1a240c54010107040a04040403041c0103108a03040c2038114680301c17505104030388400e005145c2c680d0a215000794070780c1c080603101760008401c210ba00011380302442003291b42c02d1111442038481c1820301c0c0c41800701d80141c5804100c0040850124042003418003819041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 5479441 1250 5478191 5478197
    0x804020a15030908041e090218010c0614010f0611010905120703091a0d0f02120106050f0403150603050d11030a030b0a05060307090303080c0c10020706110d061d090607 74
    0x2840c0c1d5100c02c40182a001500400c404404100090103003400000030107000000708085450503240ca60000c100c0c01450105072104003aa00214000d500403004807143e64040c910114401c1d048070f105140082c3d080e403103242c9144003560204401540400000303510080c1d80020700201803142c031120380d0703108400b0903540100000180310003050301442e840f80081c1942541040000740c20b4802030304031381041d45403070702e010306041d42094010030030310803030f2204500400c250144da403c04034211442d40160040b404400801c101c044041b4502440000d1000c07482640407907000d05618201d824001c1a4840ca07043c4065074014031403581001c01a20f139060760702c1c81c0c0041c001512000040071595181c0c002900081c00205102c0b07802e90184001c020b48c0d00a03180c800c0c1a4959502c07203103091191302c2a500b070035000000041c0d0100c00c90780081040a0003407501080c804454400407049900c2650900301341945c44108201d1802c5216840e119504001d20030070b00ea16003180b0342500c0e8000104a1420 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 5480691 1250 5479441 5479469
    0xe0604060b0a0807030305030105040c050702180405010f020c060603011b08070302090a09090303020c0f0705010e040207050c030102040b12060405010f0b070609080307020c04060e0705070311010e030711010305070804020a 97
    0xd640700d140b000c2c0000c0c0100002c4501e0680d40e4100a0456407082c09180d001d1401c201000392298020300840301c00c294060407031858003110400c06000102c001c0c000301c60325521034981c400d0042250000e4150340b00404090459800d00600301400c55101c0146d010900c082103194500075500103030303106d0b4020b20700e06001d83c0d1900e00704002409079400d41c100c02002450900b5078414583d141d80903000f02680c41c0c08680b402d8281e10401503450410744a07090000341c5425403501c03141444c3d000703012035900c1801100d810792110000203007603800a0700801d09500c2c0c04a02d0640c0c1c40c5800540a40002c1e056808025550421551400d1030700c2c5c9001d23014610000007980420014103a000b614051342043c0d60b40d44a0a00020081d210960044018415030030241c0200302e40315054207450180045498080c80c00d01603035010350b8414500e91448110b9581e0300c0058810b46d00071310040030800c1c86400a806408080000075007245c002400840800940d0408c200042c0c131030252000545007100c00c034106d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 5481941 1250 5480691 5480711
    0xa0f0b031803070804060e04050610050c03070c060c0201090603020c1902030c0409060f0b01030216020d0309180507080112120806030307080708070203010b03030703050702010e01090506070308060f01030e060406 93
    0x5480312000369148041c8000204003061010000c00b078011b86140d0341e036414041010104006c01d0718070507103580e40e02c0414160444034550248000381008500401544e080520540703500255921590180f0301080d0704421a00071036900400210241007503050441c20103409035031090780d814041d008403c07034000c0f038100c1c0825507508105280e021a401001401080e000380341c00e0018080c41e507030207548103003031036840c04040d8001e00a640b0f10340303100303083c412111404d0b800f044903c511080307058003840042c803c04195040410300408a00c2040c4201103040c0c1060312000b031502c40141d0284d0130f06420302444200088a00141d140001042c0c5012641a200d082c0000d0652046100003050304500250359800c004400e0f0103011110b0080340200589602101456128419440d0040c0001c17010402c190044d801000c502c202403206140c040c50f5940c80e0404034800d6440704609601161500040000320b140000341d10031308400c2131034184080f040c40700c5c81e160b0350341c806032000300066282c489143c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 5483191 1250 5481941 5481961
    0x40b0408090d050d1d0103060e0a02130515030403180303020d110111070f020f03030a051c090605040f0b0603030901020a060b040e0111030f06060708070609050c04050702070807050a0f0b03 83
    0x1000082e00041035a01c1c040c3e001c440038120500c80c0c40c01c17031402c1800030340d0440c10f58001d01c202405c441c041c0070501070590341c6420400c029408810b04201c101000c030070204413511401110151402a6000d00341e40341440d0a000e000c07030040d152040d400c14221003040c000641e0100c3c001000142a0611213104042c0244d482e015000040320109110404903213030302031202c40b0703014680700e90082e1405442222640c0a25441c0d200d421000000705d2070400c0882c2081048003045214000b0b20200010300c2d05480da40c082c10340c4d0060310280e41261289041e030040c017504081c0c4580021081700118a40350003000082e46030307600f10401600040d500c80302c074040703900c4a070051800980c260000f000030803440d20002d0103541040d5034032010b4100c42d80004c0c642d4106042102c12725a007040712070341000c0342d56540d01c020b4446d141040b5464091101d810415880d01c2c00b0b00c41c02080160040c104035814280d065107040c1441e0f02040c842c042110040002c5121015080b00f5902c0c40c009850760380c0da0301c40c046 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 5484441 1250 5483191 5483209
    0x8090f03010e030405040e03040b0301061b0f06020c0c0102011a060903010b0a0803030702070b040f09050a1d0106140301090b010303030902030a080406120506040c0806040507090302090f01090c0206040b040809 92
    0x680d059400c0640da810100000301c02031080c1e81044070100141203482403020358030701881c000d90190010400041c080710340200007060300203070300242d5030642e007400d036407544220011400c045480a4004c61102d802002c107220201c002002071008122a4610304032022a08443e84030f0316000c1d8030002200c0c1c40d292030a400401740c061014203000d1401c0e83e11a1003a44e26032040ba43ca000500a5080100b904411101102d0031500c02c4400441d01c06d003810968002420f0152070f01183c90781c3ca545988800c403551343c8402c9001142000003074880c0c5031541140d1000107011020384240d24006500c2c0c0003528055000d07054030380510340056240701c5480840d00d480c00030708014000d0003000c2400910b55034802403a4071000c01c82c0d42e090025441c0c40c02403109803440c0329100d42c04941e0f01000541e55007045e030301095221800b460071840d1682d0b01d8021130500351050704d2203840d0600400050110120703c0c00b0b0181400f600e0702c01891580360070f442c0c0800d0f078040070f800103280a0000800c2e0b441c968880e610 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 5485691 1250 5484441 5484469
    0x903030813061407020601060206010e0109021305030d02010b0103060501020c090a090303020c060a0507030b0105070302100509030d02270d020a0909030e0402190f020303100605160506040f0c120f0809 88
    0x1003109480303491203100103a808851413001131040f0030002c51010b2010902e0741c1241c0b02c0d615001006c2e403d140031003000c0e4100c80a40c440300030042d100001c0d29901003000d0072140c05141c0000903010564400101174442980003e81590f200040030b001ca034644001c895408040c0303232000103007101c4a1400b18040e2207246c4021865110307403428444008040d40c007d6016007419102041850011001514903015414015015800c0345140c0c5410401075000240d2054503e01078078580705400c2030706012a000855090142c0002c07801088645104015408585204403001140e801d641d50000300104c00c603000d010445903c81c03281004050090800380c060707e200501c159140c002070304000402c0340070504c48400244100c0504031206001008480c0550700c41d2007251801c3c1d0800c0d400366403c0e0702c0710307040800307181102524074003040052001601442c0329220324524654a82000c400c03072400ca402c01029030044222080c00228000c20f65410b050307000112584030403103040011301003002900 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 5486941 1250 5485691 5485703
    0x212030f0a08010906090501060804030f02070b0307030e01140c070213020d061202010e010e060901030e03040e0103050d1d01021c0302090411090112050105030c0f0a080f030a0e010503070903030813 87
    0x3000080603070014055816209a031400b088030350b40e0f51006c80f091711800e1240101044502001c100400e1203840114001051801110b000c036640710300812003503004483c20000284d680d00746101005080c020304040308141c0580032068200b00c509004103100d4404000c0c450b0000415100701d00c0050b4042d20445031031180c007005000d64032900e804000140382404c900003030459a80c1000e070b40c01001c80380092070b0040c0c01c2c5414000d11400540003840840400780132803205100000e28136100749409400395120340041c01896803044006014450409402c04880100384507842040c0d9000816000852160b00d00c210503105441c415402403003203074000ca0f002070a203080315104c8503019008000d01d800a81e10a264414224560b1003200c2080c0a81a41900b10369001d0406203042d101d00032441d90f000341502d54290751000344915050358001450010740020540d100110f802c080f242d410440203081040c918600110002c005641601000781400780540102c0c40d941281c3c0914440590302c81 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 5488191 1250 5486941 5486947
    0x160306020909010e040b0406020904020d1104060905010206090d030515040905011b0302040308040e0a1e060e0106050c03031603020c0a03020a0b130203030d180623070e030a0212030f 80
    0x205088000e940400344490042d11200c00005100b80d8082d0058031580c0c0002c0046e84d02c0e00e81d81d0340e000c042e511008001d1360058090014403d1440c2c548100740c00c40540c0803241c0d580320b20f4188041c0840c507481d480a410b42d0402401c0000d5418041584034112031980b40c001125a981c3c040160203201e00e1016980051500140008100e0154084805918404500b656070940403200f102688110701008011348000d00c41084105901144981c102c0c000410108103842d030085855200c3c1c1007211624003603a20b4450030402e801000c4270040c05000c1501d480e5141406461446540f44000392034644210550b41da0440d85074401c1d4152810042c5101c01d41d52400c101c0d0030000d60320780d00303050203a4200d466100415403101802c059510a2940503001d5414403241e48142002040d00150781085003d148440c6000110688a03034000b80e02d0304800c00b0540b08a80e0440c8400c1d6030018922000c2c4441c0ea000c40c0c40030b42c9d0000d1398104c00c9170304585042c040765140039481c5c150f004449103000050804 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 5489441 1250 5488191 5488193
    0x20c060313061d0f0106050316030b0606040302041103180102030c042c0a060603050105040606081902090303030412020c010206060a140103021903050105150301140f06090307030503030a06050d05070b0c1603 91
    0x208007032100e130b810b410090084940b07a03400c00d91141c03000700100c0040b401c44182003001950b0070002171760000004010500703066032070b0082000d9400b010401c03000e04070000204a100c11062083ca44400801c00085066143c020840d1105100c2c501949041601540311041c080c0e10b014880c295000c0d0900146401d820701e003071030fa405400e160192502081c1040008521030800b1700c221011580241d03200b60003616400d0151001c00da40c00924088150200703da0b0b00e150700d0030001035001c1c0e445044544143e01c2c26500003410180d2000005045401c00410b002441d80c40f1806181600c100c4070b07240d00d0390782850005038000d11071000c480c0e04000b81a0503448140e6051750040713041325811380f00d004a5482d1184401c5051109009a84012001241c1c40c03046041c007188450790702202400451a10004500103481c0c21101c2e0300486003a0300c004100186040d5602504005060070b9403070b0400c1901e1962501d0b100c100d203000e00d44250300d0100d04004880410070225560b1062008808012922 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 5490691 1250 5489441 5489443
    0x3060d0213020c0c01080903070b09070b21130209010303110f010501031a0601210507120e0703060e010605010203030610031404030c03030c1d010c0201030608160510020c060313061d 80
    0x1242c2c200c50340b4001c4414611326940540c0b5014442d400d000040e515100003580c0385400c0100181c095421440341420218a000f076000043c4265405800c8051389090400114415800010401d08140c40b03c040781c0c00040e181c1e1840c01d415a98181008007269140b030101070b242c4096004808602cad1300300030000040c040e0070742080e0881d50801603100000e03550f0b000190341d8200902900c0b10107500b0210f88882030340c42584280e8018805213444202c1e001002201c1c000e0b204400400c0400745c21541d01003040148030b00c14103400e01100703002480120300d0400040c1d10780c000100001d002d01800086001c188d0300c42e5028401d44650030841030460704044c2070040c5010b1500404402103403074003c859150b0f5010340c0101405081c03418400d03102d00f24481c01141d1800ca81c0b00d00700d0601d0307240c1d00046940303d4144428868548001a44c04c1c11074600070400c50041004911502550040300820590342c9802c070481e60b10a10080045883c0c03840781c0f5066008114504024500c19040328080c0c001c0d0744 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 5491941 1250 5490691 5490697
    0x30602030402100c0c06030b030a06020304050c0102071a0904090206090a03030804060509010213170a0b011205010f05010e0402011b0b010b0d0515130e030d0504050f060709030b01030803060d021302 87
    0x402510030780d181006024050b1340c020800c0c8409048514a00d800b0000d0501c650044420344c480903081d200c801501e03a0b5484d081e81c100342c504031103e80103501c07043ca195a041009100030401c40d803150759800f02603040d011440c0703c0d14010602854980503d5410354803850100d60540d80050013140350142d03a03090041201009a80031940e0301c1c00d28000c903910000500903610100a080b801100030381c03500d003001500c0302142484070014000c0d80c4212010130310440a1500804080d00c1e5065491142d01e05942164001e040310703480d0f186810014011501c84d01041c3c1e41c03141d1b0a007050f00d490300341310018104c101c8040c3c1d40103120214105c0045003820b00000903100e0303480812014800c2c0c1d01d03a001d41740a8081c004404940003400e0058070b024414864021410126502d01030741c1c602a00944400c094034400c80c1c054841c2d032701c06603816000310010001c0c1d550205480c605000c4050441c0d4a43c1e641180621000d041a04040082640341da01d4001901c405a80205440e48a20302142c01e030300650 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 5493191 1250 5491941 5491943
    0xb030403080106050c030409020c0a02040f0518070b0a030b1203030a0603020411030f0c0a0909060f030302060c0a0807031d030706050a1a01020322050a0902030405010c030603030e0409110a0306020304 88
    0x1c22250001038401d010340c040d030310084030070805075081ca41007941300e4009408c000104d90036445040400405030b00c8911030707000348041c07041c4080381d1854015400f481c0c0d00c0303000c2c0e41808107502100c020040c0b0401c2109036030700360002d407501042070031800380081c1d041d0140c0c556040407400000113010421180341e2050301164420340b001d116101c14007e042c00d043c00111155510078a10300700164510300d0140041120003c681080d500407615440120119080b07904000b42c03c0001c4070052091680400c03400750b00c12004080d061404603004001054844050607100506440b044070907195010f042480081c0200c09c0110b035150905420304101824080d6441c05000f071900200003600020b1550841c021030040c0c0096260aa841c01828080321001500708118041d81c503011540303507200280503000700305080e0003603100c0c10942801c6084078450b40083c01450328000080001980041c03000d2440c100031600090185014100a4501e03500d101e00b20394007000794400070041044545c0035501503 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 5494441 1250 5493191 5493197
    0x111030a02010b0f150307030b1302040303020303090c060901020703030f030603060e01020d0c020303010605090603040606080a030f02060a05040b0103121707120e0c0a050907020a0f0b06030607080610050a02030c070b030403 98
    0x41c09101e13050241c040707007002020030b40400030000180114040d400c11050a1809070000d030454160280308022a00030307400032001a0130000070310446910421441c5400202107a41c00d07d0000001c002035031300d8101e40303c01001d00c0051144540614040d5214900441d0030490902c038002d00298071a000b0f510004007551a640352010a420301840042500d05803003850b1183c2d460a1018003c220a50300000c00445a4944421b03000c24030840502c49400854400d80f100e041c0e071403070b00341c010342041c1000301018a21407030402008007060750003600d6411203400c40d480215240c000401151040d030014003445201d00301307200348034409902000303207004079071501303030400004461a01c410344520402c400e25074810701c400c9090049140080c0e20390f8000c0d1450044900492a50303942c0e00c0b061049900640e8403001c2e460801c400d500307092100c95031000b040c1c42c01294030300c1c0400c00501c80034807001c880c40070408080f0720760322554020001c03101509503000885100955825210b002c0d44d204907011000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 5495691 1250 5494441 5494459
    0x4080906040303030902010f09060207050d060e01020403060203060a080c010e10020a0f050c040608070b1801020304090c030f06080109030f030b1c08071704030503070201050f12090601090605030a030509040b0111030a02010b 98
    0x88c148035030f00102c16181540d0107000f555240c20100b0104a001d00c0c02a202c295071440040c040102c2440104015485064056240e03d06141040304000c8950301903401c0390088191400240c3e41312603400e0003864115200050040c2e445012032412440305c60003061109800c2e2001c060110000d4200c0d020f4604070380610600362201c0e001d684a44891181d88501c1e03a09001c8404411407000b52501018010710403a81010394406c1e140c415900c203001c180300441e40c0d9041100c410009401010060216480240134410341590003c0500c0301c6100144200341e41e9403400821a612018113000071202c13406104200c10031800c01c07040f07540c4482d000711203200c00d940030000c51090b42d03000ea03022203410001030742c00c0c21610780043d90b20364800180b4001e0401d0400c03000b0031100c02440003500070804000140f40320740c108403001c42240c00ca9000140703e03502000345440000d9102d070440d1a4427409842c0480c00c00c17641d00c0140c0c0d141001a94400c41400081030150709943c3c15800ba010b1206c048904400c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 5496941 1250 5495691 5495717
    0xa0b0603030702031b0111070b030115030911010c110406060305270604030804060b060d090201090605040b0d020c0a05011112100f0905090705030712021302210408090604030303090201 81
    0x9501d02c1000c034003c0d099003000c0400d100c0c110001c522406450b006044c1110b00c009140d8100f0308040841e0400311502c00c0100c010701440c143d4100600f4000c1044c1070410290840351681003101481c1d1078441d04110590130704030100121940100c01c030b0070001e001880540e844d46405005060121007441200222580700d105070328100c000300304c14040307220281074151100d031003c4500341c0c0020010b4400645511000070242c81d03030380040901c4000d00c8000074150100f81300052640481d640f004080180034002030003844842400c840c1558401c000c01070340c1d49109083d46080c08401600580075501c3c19200f0100d000040004041220b142c03100c912041d501c8940f1600d148509000340e04190030030f10418803c00c05590b200e141c10010a00407102e20550f500b0001c1c1c90b02c92241c120380350303600034650035000310704200d030702003103100305079841503040a1600254201c454410600d850081c2c00311408036013801189021102c8660f00941403e941d44c0c0c0f80e081c040c01804088074120300044500701080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 5498191 1250 5496941 5496943
    0x3060609021803070501080609070908120417070503070902090406030203010510030c0e040510050702010e0604210219020d0c030f1212050415050601050c0102030103150b060705030d051302040203090a0b0603 91
    0x2c2c2505c40c141c568512541300d0100344801540024074040a0100e02c1c0c0c8041080c200420052181c000f0040d0095941c03401c110380c00170b908c03510754140d0794150320500e000e11075a90040740078415110800700c0144c1398218000098041d1070590320194040d482c08007808200c80301d80900c00d040c0c078001d1189041e10360b601c02101d035038050120360240c034a0b00441c9006042c8031990b00881e401c080c1c0c520005c110b03840302035034441c1851400d44041743d03810740c1c0e0705a0600c0a00040c00c1d446081c0320600152000e00031044c502140414002c2000b8030500c810001d5000b080b288400382400b440e040008038200058920300308543c9100100104081003400d00c00400401050040c203200316440601c4426403e26a80200054400503040a060060074441c0c440c11550902c00b450085001c0c0010082100480ca100400c84000c2030750320f07019400c1042144042207000088640c07040503a48002107a5a5813903207000800d9944500a5115000006000c030a41c0c0c00500c0d1703003500c0e0040b900c44d02c070713502d80310201 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 5499441 1250 5498191 5498203
    0x13150c030e01030207080c030d0c020c0d0804030602030c0f0a02010b01020105060904020d0609080904020f1201050604060903080a090b160501050705041206020f12070206070206070201050114040504020a03060609021803 96
    0x40c002111256003029551080e0090b103d00c500c01c006040c14000f130384804a085030858107440000d1070784d0b41801d071251030307040040d144a0380041e600c000b048445030722411002d01c00c500000d0482d0360000041040401e004044805c09400205060748510310715400a02a056081c80c0c07074019800c0c2404035400d0f00d444203440c0e015540c01004100c42d0740d001e03515203014045103007054a114400744032054107512107000410381c5001500f0030a9441181401c80c202925040e0007003401900184000c1c170445400182d8034083e6a04080200c0d100c0450f180d0460340c10800c0d0b00040008100460f1503070b451010225481c01040c42480284410341d0fa0800855140c0900d126003140c10030030303030100d0012400c0d540c01001110810b88446203842104400380f40d03030580a840070001a03001e1410011400c0e07061103c0341c1c101c0b41c01c0c4001e119552400e04420030140c210620340d4412955100481c085644a200003001035a01030800c0c08500d9070b9071201c00c025000184c031000507810305945032103545408954 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 5500691 1250 5499441 5499443
    0x5070f1101020a0806010c030c08030c0c0708030c06040f0f0804031a0a0902010f030906090b09060919031706030c0301050406050105030c0103020c0303010b0f04090608030405040c02012a03090813150c 88
    0x244813090360f03411004540e03040d61100700b80e00f032140b000d0002001c10040401580308200580c0001d0b81d56510900c050b00e001026406006e00350024000b100c00c004010460640040d04a0403a10195109040620404d549924000c040c1d00e070000c1c00000308000d07040391a982004c450ba8040035561050020420f0b240e007400c0c0280000c0031510719084181c001c4d0302c0042c00c0340c040c0d81d00040c4000785503185001d0340300c20b0710b811145901802c100042900200042d038003001d10012240f11002c02681c1c0a0882036070b599050041019003000601d2a4604200d820391811004000303200e20f0401d07042c00401828280503850090240607040c4145502034021074001c004900000c41c41d503880c03e22600c519401030012501001d00030480011014090b01512000e031071184081d44e40d03a80785c40d007003100315081500000d043d0790409031038821107402c001002042e224959001e41003950381c000708500070013206000a004802c081116180c400103021701c0c80c262151030f00c0320780c8103c0b02c01409a0303000500d040 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 5501941 1250 5500691 5500697
    0x4050603060103061512080403060b01170103080307030e0313080705030a030207090e0309030a06050105040506040515090414010f0608070801060b040b09011407050307020a23041104050405070f1101020a 89
    0x4010000200a540074175003003801c8035594000e844e01c5051442d0104a040c10586020030049000e0043c014030740f1038160303980024200107080865100111881d82814400508261404000101000d000e0b400042c54080708c02d00341e0703a954890110305501e110007405940d41c0c92203403103408503030750a0008603e0f6100d6015001000d6513445c181c0040040c0c903244d9440491400700340a50440340c1c40400c1022a2184034800203c0c0941c140b034144002c569004001c0d1b03200724140400d010004038800901840c242050750845102d40d124181882c400e247c8011310000c641c238045c09014914859030010044d0b031400c406854941e940c4507022403e0f03545601900e0640402000200494112031000301034030b00044c145144d1b80420400c0313002c080d070172402c0d0039030f02c580001500c80c04601c0c1080e42403000c2c00c07465011500b00030584d419255280240503210b40160b50b1280440303407810452040d500200341c0248140168544024018284980c20f81900003160324180380029541044c020340700810f010395 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 5503191 1250 5501941 5501953
    0x60504060b070602160203070806070206060301051b03060a051302070201030f05091911090a060510110c01030c0e030601080106050111010204060c0213090c09060f06020303011a0903100608011a04050603 89
    0x51108002540b01c15154034041700300605420041e141400702d140101700c441f01800442ca09280007138100440103050b644a079160000308252828182035a00380c0c1140030030065220b50394440030650702c50640c0c03c40750780004211202a207036081382c0c00824002d07201303070f030180b03c5032036108aa038090301d10940c1c00c1c00341508040841204000d10818941c0140c0c040c07805100c1c0340d0046004202d01d105c0980d200c004040c1c54260034800c1e0708141c90b801000c030743c0525120400182c003041f22522007903841050341c10103494160f0748003124866056020b204000600b41d907510359550541c640241882e10440f030100e0900308d24050b050b403041c420b88048401c1d07500d880540300c3d03040c3c1c05c110740502101c14804259039600e419102113200701c00804007618100c00006030850415414070f40b281c205230f000004641c02000140000036031903014420707103001d81c0c2070940c40d100181c00280c02d00041124000100d480c010001480020541200c00400105200010708011100902080e14030440340c040d0598858 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 5504441 1250 5503191 5503193
    0x1b01021804050c0d050405010603060e0c100f03230a060506070b04080906120f0106090803040305030d020903070305060702011e02120610030209040c05040f06030b09010306090507050a0b0c01060504060b07 90
    0x42c1d04803d50211508031074518041250310713550200c4405640a03503040e9900c04080c402c10242d842101454450b00004003200c1500b00c00160324010000c00390801c1007003454261a4581c0240c00c14900400082c0d0141d80f42030342e107080e424220f101115468405402c01c0d42c000b07005e05000d8203d40c0c607940c10501c80b100e03543c0c3d162030b00d00065000709080e80c1c011100b04840c03d04688000c0c00540150812844a000f55141c0b40005200c0c0320b00b074000c451190401c00040000460020454194800402c03015858078800c400007401c00d03c035a8400380903400b0f42003c1102c0f40780c2c10b500811020024802c0550030320b06040c070340400ca0243c40d804040455101c004281d85103013007003140d807004010785005841c20b052040450309642d5004039034004030300d021805003c14040504200040d15841c40d04000c4540a01c2c005440c1550611000c0e1001f0355480b0480e0038018148445005004080c04100320f5030f940300e05145403030b4030512420700d09501c2c00ca0045041e141501844003140c00b0351380c103036041c9113407 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 5505691 1250 5504441 5504449
    0x10308040303050304050307060e060415020307270b07050303070305010602030a0801030201180803040902040608060306060a030b0408070b070e1e0306060f18010806090d0215010303052109031b010218 88
    0x80031740203688520050000300d00040c40ba008501302c13200118083e0030142002c0c0b4011410340c41480d44080854014010000c040f60310015007021a00386000110865075260003003462001280c0244a101600003800414000000f000b1401107440395410071450380c2e600b03000c9880340100d803070480005901d0001080590303c14080d210355000c0483c609046166503818061442d842507000543c0640c010808006142d00481583e88c420380a074054012480d103980019030507804c038000200040b1b9542c0118040c044140240c980310f642c080714680f903600b00040050714603043d214040c0d10820000000c0100107040d40036000c0101009802030041d03840e00c7c010011030440f98800d50303402800002401406020100e07580e80240440e401074941c5003000800d1904013000e000c00d000540d8007a21520362041550303001541140e8041c54040d441d0944050522085400d500c81c40801800390024000d01500220040c40580041002c8603508020684814282d0103841a00007034a40d9a904448103818 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 5506941 1250 5505691 5505697
    0x6020705130506010e120f0d03020f03011203050f03010e1009020705071701020d0203100501031103090a030e0103020c0114100f050901050d0204090b01060909060b0301050d020f0301061d04050601050901030804030305 95
    0x42e050408501d45170042c0081000c00a50000000d0f6650140f40728014000c0b044c00360a02c00c80c41c1e40750540c505501129281c940388010306c200f1414000c0e01a5500c18107200e40c0035a401c100b40c4020307140d640d50b5100600301020310180c84130264200c49400c0020700703007031501c201d440302584072015050440c82c08442500322007051403004504c0d50204800048441d4130f00c011031203044d8201c800f4400d01d0504000504803120140c052800c0700f810014860600c000140241ca85a8503140c4505a007270f020004802034000d41c801110300b9820031080d50b90030811301c6000780c4600c21040311000341035652045110030002c40c5c03040981159810006000310705203030ba41d401e4074500150010a603031009547d2040b589109920001c005840700c8070900c5040d456024120082420341302590231541080c0000d40314405511000703120755406040000651820341094000b81a0180310b4a116000000c00c540e6000b412101190dc0307000d5540045094a018040c003410380c0d422452450415045a83c1990158 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 5508191 1250 5506941 5506951
    0xb060d0c05030703080c010c0207060c0b04020a1a070516060e0108090106030803010f0f050105040b2502040608030d050105040c08040807050f030406030c030b0307050f040c050706020a0302040f060207051305 91
    0x461100c001145503201006850f0041d88181700d42a5039440300c0b0b18203030868441d55080c50464100c558201b04040c2c0c4100c48031003c42e000040400b982d152031000620300c030842d600000410191b0248403d00c208410060000f5038054010380d820341c0c02e840c9005a07114642c0c040c0780003140d0181e80e010840d5104800d011340c410b5a920001400d161aa190301c0e4494109900c04000040814800c2c444404c14003003c5000300401e0810f24186030500352155054090894882c480c55100d042c0c800d07010039002d088840701a0041d000b040700c56103034017965480780e01040e041512a810100000f030982041d120b001354403100341d44c603403501c0d882d41c0c0da6103421a44000c105854900c03941c108110300f424280000c000a0601d40c600240100310054013030180c03001d0000103413003900100c2c0c0c20406906c07090070346262684100e81c0010a04920301003941d441c05419400b40c0410b1010484080d10354040c0c0c000c0003650f02542d07002c0e0680e9a07030034040307130341302c100c3e000303031504001c24241d40d122000c00e90304856004 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 5509441 1250 5508191 5508203
    0x8063001090203030408070807090207030f05090f090c0d1406060301030305030603030d051302010801080d0807050a1202040902090306090a08091905030604050114070e22020702130b1005070b060d 86
    0x1c098150000781c07440c1c20a40241d0303210303000107400f0041c10f4004c001c0d1358002c00c2072550940c1011103613203000d040a082200300d8418400e0020343e03c0c1a41d51850130310202c2769001010019107041510111005410031700040020a26065840c0e01c03139464070440c40d00c0b84800402c200d02c1c503829954100c03207503040980410b03010f01c4107106007440200305004182c81449030117002000f10856000042503a08180d0005003c0d401c00300c0366001d100d900201c0c440d84504c0605000e60b96040f01442110246401c111150010340f0206000c00d030b882c4a5002044008070480803a80d554841c01c107043d49a644112000300361603c00c014202440c240040030440c408140d0784250a600e90380c00109082c110111403c807401d07550b035844c04c514407000014098004503d407901074203c1c1c0485c40032800040f645582049486484208100300d04800d40484d61007a60180180e2102164a02a80007404074550014030546017080c00342c403414403903c2501c075100d41062049542d40c03200f40c1400156441f541003500e031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 5510691 1250 5509441 5509451
    0x6010311040603150207020907050304050c010f090915080c030601080303010e041b060f0906020f0307020108040510020a05040609140a0b070507260705090f010b0f0706060f0608063001 81
    0xc1180c078490210035501300007016070384180303503c100a615540100300340103019041c014000032800c000b0f04504031280c20300f041040707451440340507a1802003690042c114a4285203818030514079040003803080390424400c59400c0300302c03502015140e6800340a43c14031503200b480100200368079080000d030458029000525010021150702d21498075640250000c1075580b107200301140e0740210307103000401c52480a0304c0200d030700e00b0680d80c40303220300b09019040009010206007480005e001c02c00d10b0b070005040031565400c02c8000a001038015103c3d000204a10040000d00401c0c80c2e010042c0715200200a910303031b181024095800c0d50042c400c1a95684078802001c1050301c044100501802c884140944003142d109038900d14080454215034001c484020901940c2c65050001078156560726007074079200d490007070b40c0540602401c200500018100300c000942149401c505005450f0503568054840d60f40300c00740000c400600c10307098006101038040b203403002d001c10f641d04442c14001c000829 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 5511941 1250 5510691 5510693
    0x3030209040203010b030f0a0902060301120501060504090f150e0601091109090106030f0e010e0d0f11030403030804060c020a1104020307021f050604060501080c03061504030b102606010311040603 86
    0x1c101e80090700719006031040002030004c8a80d04461a40d88038801400034403103808039501003005808184240c101a82c6503210031070030450f083d00410003810b4090001c000c203881c141040c0282c4d40c0f60721710650300582ca410400e580550300703011b44038100d054000140126440c1050110040140e0b0780c00003c40c81040c40324007640d64402c0c1d06280244960b6401144501501c4041030807940704811075486a07140006043c03001ca000700711402d80061030304220401a01044064407040c000408420650200040110426800246c61805a4041c0f403040081d24a0544241d98800b00c03590b0142814114004054903440c01d85c000350f40c0000d0b24410350342d0090148802d241081c0810040120040d19101000820700b420303c60380740241002d00e802801800c3c83c40204040d8800508481c1c0110600d0216081c80c2c940c80044a0046900950342011840e042c012124000b2940c051350f1446200081241d16a4010754191800c5e1482140940b41607461075540545c0e01288000c000d4100352160701c000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 5513191 1250 5511941 5511949
    0xc0201050c010518070b07020d110d0210050310051030090c0305010f020906040b0304020a05090c03180c060d0b040f02070b07121103011401021e0109021801031101050703030209 78
    0x240c015109007010204e204d00c418109410481700f6000302c4030149080c000315001d40e45030b02102d00c011b43c22481d0060210303400700c04100080c62515019403c89281840c4551a950050003103109100d40e1406503420354a501c1080022260600c0e0030002401c4100300503d2090012010751500103020741104000e404601d440e0241e4000103029203a0b8039446a00f0000c2c00820b010b580d41402d6201011440c100b5020000b03440e038011401040b007a07010210014085494115015001c2d140c02002d109140c90070f550000d0156104598424504070001c042e41449035000030001c0280030000c04186c10040812102001400e411048a40c07051701e610500541580520050140d24056600120780e071404150181c040d02d680c04241040c0703403070f094980c20568440d90560341540c00740d8901040361081c0b07030300403840c00782c1180918942c505200003a40e0440c80550008800714070a40740d100c003500e010042c070b2507602800d01c40580b0401c51420010140d620450088c43c88910a090050910034540041 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 5514441 1250 5513191 5513201
    0x306180209090f01050a0209030304030f060e0102030f01080f0705030d050702010c0f05030a110303060102030d0207050a0b1518041203050414060c0405090105030102072006091503060405090307050a030c0201050c01 94
    0x1080e400046800d000ea00085c06a40d03072050300030405500c2c0013402d1000c40d0703991050340300182c0f103803044140c0007003082844e400c00614440d10f00000d545904101500c05401803080c41091460300c00c2925480000308082445412214010050034455101800c280c3c1e442d17100260883c1080f8084110100060081c04401c4d00180550001c5480f03403005a40600200401108a003255100b4000c0020b40d80e07002044071006c00d00904003688400c070a14050340740001551000701098011810450740c0f8000014520826004590a0000100510010108035800d64010b040b1031341e0f900022843e980203070840d0fa002407061071014540440e0004207401d000003039070982022140050100b005150410b180e5015141c00c50086282001d00d0356246651280303104035510b03e02254200e04001c1d03880c6800e840040c100a0708200500702040c0c1820703c030364411521389100c1c034034040218030310110002c16143c5055024000300341da0503031502c064507481c204c0a0100d0401104000c8000c1800007802a = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 5515691 1250 5514441 5514451
    0x20403050109020901060801080705130e0616030501090b01140c070314010e0c010504050607060515030102040909020406090501030210030e0a06090f050d0809030a0c0206040b040305150a0203040c0306180209 91
    0x10302e00360900c1000070050040e0f2080c01088104c03c0140702d11003020401e01c0c121366048801c03c80b1005403800700006011b914200f0760140c0140d204110300b030740c10000340e13006115a40c3d404000d81c1c0c0c2c81d543c3c034030102c90003051102e001034031898404a081403901c008007500c0c161102242c07240350f640d646442c48070281505003040761351241c00c8a403285104000d4525218005d09180d0b04190500d004204940100c000c00360140741c50308040b42103140c480308005003c60000e8002d5540b10789444550002d8400c44500302d001780e01d442c1c4002201d00c100e00c00c0d03a05a03517004002484006042e0400c0303016140d9560b0849460041200110004659200d010180751094960500c00c07140341c100503060280d5054824140b00d035000400040312400300440760350411a00f0034814411072800402c246009039007007003202160004000c024004001440d08045144481a80c4113a0b82c10b02007000740d000946004003405014102880001c01c0d50300824003614030901981c00446481d00010807070401070752 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 5516941 1250 5515691 5515693
    0xf0a0309030b010503071a09041104120b060f060403030507080d060e07030c02010504120c3807030c08060f06090d08090f01020c09010e090703080309030a12090201020606011d030102040305 83
    0x22040081002c2072035a14010081200500411454183c130034004540030081d9220b072540006140c0b00f580e403194820341103241c1d1440e241e512680c94000c01c5603940130551041d036246a0303e500064242c50b00003220b45540c00050811420107141d03039025241a08002c2c0103e1301c102040c00040d1003604503200b054000c041544100c3c51500b010040941241c107802010b20859042c003081101150302c8504800c007c804500e041c0191008604007480c1450340e42c40600715840440350380042c010300c4c441e0f00701b00c081c4640360030500a860f65803040e000c503402c5011540c04942800d0005100345003140c40d89249d6000640714a1400300c2e0b650000d40e002203071f035004032210040400c03015203a040c650381d20540b101c0c0c00c0c001080300c42400b10003d1b01c141e1051254240c4034040c840010f1004106108c041d00075070b0300190307094482c1803084000340c0fa41c0000e0802c0c4001100364003031f101051414046e00c555250103801030200d035121003004550005420740d04252001901c044a0101c4d14248001d1005500580c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 5518191 1250 5516941 5516957
    0x20c07092306010804030801051c0b0a0507020106060206010e04030810030516060206010b0f07020603040203010213060f020d030606120c0201020405060d1a030102070b01060f090909030806030114010602030403140f0a03 96
    0x18201c4905400c0600355604121102003040f001036040381c3c1d6141034400480d60841d501c014004480b01c80c40205800a280382c100310184004200550000703030141040c1d4009100e000d0715041c0c104d03078a490034407a82615451400101c1c01190103000104d800c101c0c1e668100c003040f51a07403109440c0c006206803801003008544020490f0729410b00030310b805040ba920150f490701c650080e164203d4000c4080292103980008003060071075030258100c40e440f0310881071184419a0f43c10005c2e1604040321000740140c01221a40000288a072180d81700faa41192251814041d21100e114020059203c84105640d401c2202154a80e5840f015103200720343e0700e074041000035400c14007424403584050030074000d0780188003000006082d6140603055802c3c601d01445002c00a00e82100e00e06816070104140f00d152450344000e00d5485008544500000d4001b030102d00807040d440103a0000034070401d401030300140301c1032000811034103001c401000d80600301c4802c03120503a00c503800c4c061110000c4020034400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 5519441 1250 5518191 5518241
    0xf1215060c030914010c021309020a08070312050310030b040201110111091f080705071b0603050601410714031e07020102030a03020313050a050c01170613020c0709 72
    0x121010f10080c1020030390560001c0248000603282d144601c20007441448181c0e11502d00c01500c1e031103841e0494000303118010707450f603a942560300ca130750034001030b1409001000c45954aa02a604a03801400e00101c6844503a02d03589a0f006510000340040341003203070702c0352030540980f0300340500c8448052042c10980d6541d071480c1005000c01341d00c1101065603801e26079010035a07400c02c007011b611000c14107000741d84801c2c51410050841c141c4a031840f500c0180b0001180055156005500c20b60081c2c03941c4284000d6242107410300c030b560300c40c414405038035419008249520b00400d10007441c8964500c1d41410711303c0c3c1d1492040c4a866002d04401d620114081450b503450507520010615110f0205240c03043c00c2d00000c0d102e12803a0982018103030000f01092404180401c0c00700c2ca103401505441d59500c2c41e1410700c2d00c1c1c000d500304803400182d40821408480b020b090034540100c0c0e00404200b18a610b010040b406504a40b5102001d400303040800111040540106541901c5119000f03521a0302 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 5520691 1250 5519441 5519447
    0x60f0601020d020a020604030809060408010f06051005120a0c02011104030f030801050d150b060d0906090606050a060503061c0c03050303011e08030717090a03080903060105060a0f1215060c03 84
    0xb00c16004560100480c0400b60b2942421142940d802410280d81c1d996010049440c6214903807040c0c030b0720340c070b4074151644500e078941c0302c0c10680d030b022900105803842801e0112441c1c080c0303c021040d0b5a80a0300411210401d60b030100c505c601840c000403510750000c01c004441038100d50720998822800a80c4075081550180d07446000d4507048809220349c501c591980c0d0454811218103248031680c503ca014201e9a405d019a110114000c0e0300380f081050390300e0000c0107482c981008640175414100041240d02c0c2001c81101504e81982d5541e0640d6203100410040201c99a21111b14503104a078000204d10b00700c1c4030201460188008699035490041031143c9090205c020484030410355109018114002c411a120300d5080061003802c1148492020701501ca0b0849440e130114284000204120041c8050041401d0032400e0700c0c070f00c0e030740d4400b44121841060320801c0040c5d10140310b0840c2d01d000306103d9801a140240029282215002807400c003400764010201003400300e2402d40070598 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 5521941 1250 5520691 5520703
    0x9051206091212240603091b040606020c01030207060e03030108030301030516050d1211010e011a040204030b01030212010204091107020405060114031812070309030203060c07020a120201030b03060f060102 90
    0x1000c0842a01d404148504a100c0d01c1016020111642c402c0341d4112090103501401004803c3c000c20240d46ca007032078990f099496045403842d203c1c64982e001c03442503500d0644598011110141c0150610b94884d40044000354440b40044030b141e41c0c0e40d00111605502000651b018100380e200456503941541403592404a42c04200903000e10ba210b010300040c4c0f90003080c9000700e43d0080c814104035450301300503a00601c5610010300c5544c682682c0e032072880b105403c03182e01c0c44c641134030440305440903105210980c0700b40c2c00003400c09581100100014203000102c5500c40001c140014140340c0c50341131b103600380c425a041500d91000041164000d5182a00c2495080a000d0a001d4207150000d035031040140402444c51281501e02e564200c16254148400345040002c4030314103a4030546454040c0c420819404107038020702c940d00004480e082e090040355030554000305851b04043c903040d46200c4441c02074804a0405484040880c141d480421100c4d000d03506014440045241201c00286005 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 5523191 1250 5521941 5521963
    0x901020613080d0b06120f010f1a030705030601020a0605070203030105040b091b0f1e0318120414040e060703090212010204060804020405040609050708060702120306011704030905120609 82
    0x84020614580050510b10844074402c074501404500300000c0000112035000c0c052412a9580001d010071580c2c54081e4400c0b8142e5404140c0110095210007681550303405640100144200c1000481c042c14064400781d82e1190f0144126800000259255000c1e580103588850143c0c0c400f00040c05246001e0140d641d526406891807645460710940f06014405940300e9140b0110000501004601900c02203800c0061030100854019600b02d0310307940243e00481da00d50001d60302e4242c01080c032102141c903800d0044811000c504060070b0414143d821328040648035072281e030352070f05401d120101f4040349220300c40302e8030700081212840c014005500c600e81a0307002d059104200c00e01c45141c00100311600190140c0f40080c2c260b60701d1914000401c1d51000c094980c0c40b80f4400050740150018502e032150314240e0a48109116403421948280000d03103600d40072035140418102020307003069070a0384c054003e1030030a418035540c10104011500141c90304220790800340800c20340d00e10802800b1000 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 5524441 1250 5523191 5523211
    0x606030106170a020f0103020d090f02030105060609030d080601051b0102070201030605061e0c0c0306090d0909050103020d0b100f12030305010f0e01030209070507020301050c0a0e010c050601090e0a0c060509010206 94
    0x881944001d403229283c22000384500951139104005034481e605442d80e10107116010810f00130581041d41e10005c4441c8101c0c0310350700340f900040c8141080b109440b00c800c405030050044c21703e520300075241584d0081c0307070714100581071000710060550074a2440d10706400400050395003042c1d000040039200d890b00020300840c01002000320680d42c48540d100b1110b0507a0002c5e4581c41d81040403824665041002035040c03064405101289601252a200b108150744441c01000e940351600020345509100c0654080f55040b0b500380030440591000358480050160040074584410084d036005440390462504100380242c1c40f0f0070140c25101c0e2038050204213400d507680724605500d08a4400e8140402400b9000f02030115a105000d1425074201d01c0d4024000d208924212480744600c2d00310030100390018100c9650840554007a520740e040345034101000d0400c40c0c1c00c0900c4000070380244051174440703201d4030600c1c0d03011a02c50325081c4040d20440d03441c10b0b81c42000748002840c0010103450620030b = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 5525691 1250 5524441 5524469
    0x3091a0f0105040e0a0605100f09050601020307121b11011103040509060409050703060c03020315010305060306150d0807050706020105010b0c0a0609060209061801030515031018050a050606030106 86
    0x48248032680d1241120b0b0101c40119005400b1100c8034149025680010034003030502042c0505101045d001c8410b0b2403901c001030081a070b8840d481380c1034038400e1350002d002d44c10400240d03000c610010b5600e501140d850500c1c498001c0009401814a55441c1c41a81c0410140d04407008561f40303d0140c180490400300154141400e080003c1c54440d03024003401d100b240d8600e101e500301301082c00060002c603006017040001e211034000c0a0302961080b41c290b001607840f4424120998001d2003560b01552014000300b112750f0303401c1c0550b0040140700707064982c050f803071135001d9000a40102c014420648a42e01800d186443e007003000c0e0a40e1010b070840040d881d000e0016080003100010003500b1f0366044180414040680c1c1446002441865140c0c2c2c0c204800050340d510510782e012410036a4102a60104116030340c01d0400c021202e95282c01950503044030311112180c010b6034010416012406042c006200c09a82da09450604c0c3c82e00112601e810030f0f000c0086500d0f0a20600340144440150821 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 5526941 1250 5525691 5525701
    0x2010b010f080f0901060f080c100c1a06120a050307050f0109021503150904030c12050315040906060b0c07090c0203030402010504030311010b130e1218130b0303030703091a 76
    0x39911004190007103c100d5940014403503030003500003400418864081c80c0010b0b0b100c000c03007500c980b20309100900800f0f40c100000f8600340301b1103004140a07000429003030342118803204100d031044044c25445c2c1c40840104000308208090000140140c8a04021a503801c0b1905c0d00781c1c10548101c4241816924102c120409030f20707403a142c803c0d1002117031061035a0755142c000b4200601c407600f84683d04003500104200030550060040d0240a000c2c07141c00d5480b04428500304e403a4030040b6031810004116080710441c604140d0010300c0040e104d04000f24840f52104140b0495800410158040d540428820015041e16101c0c0c0340c1041403600c061840c40ca01600043e001c0e120b02d1000404014101c0d2282000d035100303500c6010350f10b40c010149036030340000301c000303d02030040642c0c00e001c2c90141c0302c046600c0c200102e0403a141c0e902c0c4c0e6052090003003d44003c100c03441130f840200303098058035400014516a030520040d40300e101191400110610282810440c0c51103d074408034480300910103100c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 5528191 1250 5526941 5526947
    0x406080a02130605030703141305010509060c04060302090402040302040c0804020a0e0714070618030207090605060301080c010819020403060203010e06040c0e1018030501020c0c0d080d0207020a051903020102010b010f 95
    0x900f6a4421306041e0ba1300c2d01c2da84411001041050a200400402941409101c000401c0040070443c082d60007805207449100801d0386418040d2050590a08104410403a8a0180e00580100f42c4000c0c0b00500f025640d802007019101c0c0720002a001401710010030003145031242d03102000e040b03014241041460840b00c00b0f000140010720032034503a4004540c40040100315040000745c2a1009008144000c65280296480d000e502402c03403680c4c100b0703e0208072810034100356412201858000c1041c2c040c0c0100640380c00c07101408da030f03602840340408058011854001030000714170403130700166298034040e12117054030380140c4510f101d50b051074001d000040c1d020380144542c200490b0b00d20500e0f00551401c2c4e40d040701d22a488a101800c05000206000c81903001e44000c0384400d041d01d0b1091400d44c204083c2c01031210700240590001c0c000d0303007015180c99002e840c1c50b46c40a0b05000c0501e44400000d284001504d0031040d40ba00044800c1c401c5503828090601c4081c001e08000214082c0a0009 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 5529441 1250 5528191 5528227
    0x60c05060c1e0a030b10021b1203040f120209010501080705070b060a120501020912060106051804020409020d020307030605090907030b1308070c0e09060c030601320406080a02 77
    0x2418100c0e10214800540e0070210840b0710490302c030b10502503603900c4081c0010f0090180c40c5081d0380b0a6031007010403031103e070000c101d81c03494409140c1c80c000c404a036101000240311600c500c0d9012480180404546920440b40640203885045c0008451513400c0c410040f40e4817050700a01c0c1000811030900410a4002003070310341d86030b8001e08140c16640d448020a80d211141d5100015002e0318081d00b9041c4803040d40101810401903a40389031031016841102e580d050b080c030560001800030056a61388502e02141c1041400300207001602e043c0d50307000c08500760381242501c000c0c143c0d400024401c966800d803140d60000c1400f41d415008078a814002d245e20b82000d032001804134461480006e4800101d00c58641c1070030f41c00703156152100f07081c5c00c1200c0c0003081e5001d02209201c0950201c0c410000025100e8400e646032000d00b417940d565072004403807103040c48111100000341d03c003840110803071703140d002c0c211042e400b42038a0312649860301c0204014005804640241d104201c984541911a102 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 5530691 1250 5529441 5529451
    0x7090f06150c0302151008010e010605010e01051305210606040b030d11010f050a06030b091209040905030d0f0b040b04060503030702010807090306020a0e130e0607080601030f050f06030106060c0506 87
    0x2d00951420240d0801c2503400c00352030700c1d80c411002c000c262610804010300303403070815000304401d02e9030919907401c0314100c0c003450380803851444060382598415030040591010100310032520640d200c003c0b45480e4a0484c281d015061180c07602440d8002c00c000403603010724120b0f810b00c00c20111102103500c540f849030089040000810406140110942101d841c5400380ca02c100060f2a00b42c50020003040e2600045941d41040008a0122a0700140f00905d2100e911403003450000b1090401c07009000c400001c681c0f0b808280010401c211140c03043d03090b194090007000c41c00348043c3c01080100e03108681c102340708a140c5201401152400801d44040990a08104400e0b40742d00c1025104400998001040680001039810003240d0200c400b01c50090196003140101c21400380c02d40c10307210000d12220036944520300050405204241080d0046418100015141c10300682101030315812216004c50340a203a0900081d800c007407140750004c00c0030f40b40c01031018a4070703500d041d120900030340 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 5531941 1250 5530691 5530697
    0x602070209062e11030706060f05060a1b020409080a0306030302010b03160905060105070507090221040203030d050a0e0a0b0612060108060106050901030b0901090b09090c13050c070204090507090f0615 88
    0x411443c0880c000c06954000ea8001d01c101d80c0c540b821480c0c544080c12450007100224100c03007000140d103013000300c107560040c0600c0c0c582084086a07140c815507440214282a640141c0b2024290003296410000f0728807004107940204001c0e04504020b070959450180c01d41c0250b00450035180031200310381d01e1909031402042d0200c2d403030311080012078643c003a40a002e405801a0080029468000c0d4024031510b641d030520400440d221051103d101042114040c1d0940c00c20071660b15071704516071219a02c42100314000448030300b0320700f81030320701b20148404480f039180d15000c0c440c20b49050a011802d1581182c0102220340c10f0611580d1151418450351042c030002082400560303000790000f0a0001010340140d800c0c0d030b501e07050017000d0320850b00300500a516002c003284a07000046650b6103083d0303028014030400084000c0840c0201302c0100501030301501070208800591311400780002d0580208018500141030030380b0741d021140c5142c500007480346000010060103188190240b02c0d407515003 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 5533191 1250 5531941 5532019
    0x61303050702030a0b131202070302010c1113020f18060304230309061201060809010902030d05070201031e0209010f020303060307060e03010e010e0105010f060215010504090f050604060207020906 86
    0x21003c0391800c0c5003400010400389602040000034500d6211540485000b181c40030214003628005030384540040c00040e0000b00ca4100b9100459004c2101c1080e030f680240a040c1d00541c40c2c08080120b070090b848484078010002178620060031400d0030512103440032a0080d145003041da40b400048010006c1540c0c0c01001440c4611014806209855460b0030180c06940d403100200010180704000340214004503c0e40710115420910510400e212180d018004054040259405032110382280f04e00728101341c0c403000d0024600500980c010204182c400340580c41d400c031000050b061103079100340b07001150700030310801c0b15650700001d82c001107410394100010000284030201e4050000c2d079444102940c00c0822104024030154881412990360368200e002058403507800f20b07202c03948421408174503094140184000d02c0d00781e1003c18080d10450340c442001000755585403d1460444040d24400d50103d208400d605050010130b41c000e4086400e42166041c50b500d1041111a4000222014001c1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 5534441 1250 5533191 5533193
    0x90f06040f031b080109030201090204050903030f0a050c091302040e07050f0403020411070f050604020109050414060609010c0f0b010f09050103050303070305040c080a0503040306110306060301090e01090c0303030e010606020613030507 103
    0x15a2103c1c001d000240e0003484003000d1410068007030100d528080b4011460103000030310030301c40481928003c602980480f007580d125160303142e000c0c0c0405019514000001c101004555803690403030100145101d9002d6240d501c0c101442680c81d50091032402440800c002040c1c00030007400844003901d50441d40020342c501c0740c80c3d50000e00e02480074010415148410401e00f400800100d8a00c564401d980d180c4220392542c003404191440407200c43c84800d15440452200c1ca0680050200120180751440c01c081c901d4076620940d0400002c2641c005e07042000602010404c040f00340c0213080b00b02000c1c807185d4035640c1c84994030300c07008282d002055941d202090400000c1c4034084000c01c41ca0003101c0345a40582443c903201d500a102c200c50851810741e21140003800c00c010340c0d00c5400b0003040c0d10308603031070800d11030081c140a100e540c605540c0c40038210001030680c1c080501860003640e0010300820038607000f42c01c43c0e6140d0080800c0d94840701c1000250790101c00071381c204942c5441c0094072400c0e1 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 5535691 1250 5534441 5534483
    0x30609050a0b040807020406050f06040905090c0303040303050d060501050f0f030a060803030108010b03010506090603060c03070203040308030703020714010605030c01030902030c06070305070506010f1a03090c0306070203090f06040f03 103
    0x181c04001c00a0140200344828007080034003414450380210b404003e2990348004202c1d2000b03481c140980c000c04d0601c0104040c0041c1d44c01290722071800b40680740d45590b4500001c2c110342c400c3e00304601184021912540c2d0711220b1081002070602803c00360301d08101341801c0d1406002c1d02901400010703000000030388050719070300540d00410200007100c0c1c40703584a0181c240078019082c8054041d40c43e0200040c1a4030300741543c54019100900581070381d0b1901043c0c080d156200500c200c0c00d40c801000000b00040002004601c00d03449030b038005841d11000d2600c841c001c0180104404284e0500314144001d41e00480d1100f84402c00b400c000400104900c0480e082c001c2c0c0418103907000e040410020700785508000240b20303540c440c0058130031300d13038941c003a082c40c141c414040c0f202009507240980c0061455480159040101001161105110a000a440e02804440c403c0051f0004501290309041140c0464490802140e0341030a06041c80344442c8200103904c0060078015040039040e4400c00 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 5536941 1250 5535691 5535703
    0x1082205010c02010204060311040b09121513020f06070507050609010306030501060801050417040303050306060703030605041802121b041104030c09090c0e0c0a0c0201021204060206190207020a03060905 89
    0x1500c2002400044801c0d600a4002d400c11b1058801090614040400c81d4680c5c03811034069030b60903100d880c1800c0350130b0148280d0020301040d0740c10903c2550301c41341d0041044c002692092410250400b12003050b03205005000900c0c0f01018000c3c0b100340403000002e8800709001c826503100381c5031161200d42020040300079001c1640050013a520700a00442c0711030040d08080e202d0f5010fa0b0380c500c04250004000136240c42940b0000d40040c3c0c091005c0f4596140200013410f01a00034600410802e8640001804070369081c2c0400c1100c15020041c40c0850911108040c8400c155030058060000720744440c080c0d01c140600300e544100d9540100d12500304c00c0c2c1080c1e0f005160404d600120040d100c07203034040240100c9100ba00c0500182d1400a84500d90441840c0318600d400111802c20602120560f519803100e44100d0550041000c0c100101e424100904002c5c01c49a00502c0c06081c01508840c00400c9013948000860041010341c025880b5070103000c04581d885980000c0051582c1420340c1450 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 5538191 1250 5536941 5536943
    0x4050c0406060306090b030307020a030602030a0f0c02030316020105010807050118030605090303090c1005040509040515090c0a050409030206040b0a02040801110a0f020106030b0a1505090a0504051902010822 91
    0x40c900007001c10242c0d8190b024000390781001c00d042245013255020183d403409020b6001b5484580c0060500004a45402a507000445000041410480320400f013050754000c582c10801030384048100700e544003400c03d00007840040790000f04415414aa880c50700ea08007030260f641840060b030b10280c15000140030100044ad041a010841810905040740c3c0b680e10a54504005214041c0504041c0c901106d00c0304e505401074039400d24081c40c0005200729100c0040041d20140943c014000b003862500210300d1140465202070a0403141500422680356410380210307014900e000540c80000b9000142c140d00580c01072101c2c1071640d0740a2812010780f245801c001724a5007044014000440350300040c18180c4101d0f20b504400310f00c4290128201d86061001900509240020481e14040c50744022105151140c14484450b00c400c081342c650070b801e0b2010050301c2d07039031802c000501905101c401ca441d480b4501e152a078140640000b2300750480586081851100c05007a0a03140f99901c010022603 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 5539441 1250 5538191 5538199
    0x601030908031b13060903030f020111091002030702090a0606031a031509030c070f15020606090403050901022d070b030702060402060307210501090509070b070b0a1e0501150806030a02010804050c 86
    0x10584401c0d00070030003000b510046000c50409c00f0091300c42030040c00f400c2c10ba00d00a094113402d050508040201c0345034510030340019030100308007000c0503071142c06410303124000031540401c44515100d80202203600391a1940c0550160b405008095a4080340e1501c0002030303007804202c50389510424504620034205076401c50b1046c000d0000720f4a08203180f26044980c9008518819038401d9000c0e80c40d0b81c4105d6101e0b511241c1400043c0010b0300610103040502c40c10320454104000383ea501d100821402001040f8074000580101a11081000841c000e004514540c0b0300f5810003440180d1707100c0001c0c000a00c00d601c048002110b4a01c00ea0540f221410b507170001161102130b56160b034000780b50a01461800d1818032001610681000501e5811a104501081d183c0031203511900390220019048858050b103070103c2c0c1500b1410007410005008403c24001019450f00d200c6c1405030004a500324244583c21040020710b40d00400e02d40192502801c7c4039403d9910b034a8101c2c20a15007502e03c07030340 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 5540691 1250 5539441 5539477
    0x7061103090c090f0403080415060b0409060503010f0903050a050d0b0603010308030402010815010210020d0204080703030f020c010807090b0304030201060305060709060801170d1b0501020d0f050601030908031b 92
    0x3500c000002d200d000c510041d25000c0858941c12998a8403100481e00036020481d001c01240000b0482900c40a07031107220728001940541300c3d06203003010741c40ba80c009012292141d5062141e8a400c0c803800d01c4044c14907000304030149455401404900894010030140320001c078105426403d2a0010801c040005000d00e95a40e100d20700986550000d60301a800607484e000007a1070701060301c50041e140c040c16002400d504020800c0000658019107011201d943c00740400550b000742004031001552181d110301131040039203c8024641141c1d00c1c0b01d281040144000d0184542d003161413101662071201100ea940d0f0f0f9a810240e0260407aa03000800c14401c6504104409a011200d80103a540795a540c00a40c1d0382d82c1d409a0481000314030408083c1c0228080140c01c03802a08200c54420003c80c009810343d6040d207541c0d003240c0060b850b45503010744500120031100c00610403190b000009080401c501c3e1015100c1d00703032a000040c24540d50300b1b28010350600c40003280c000d075441c6e4540c1703a0381a08 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 5541941 1250 5540691 5540701
    0x5010b030706081f06020615031c0801031514060103020a02031608090f0406030503030c0703020a120306061220130308031501140c0a1b03060f06050a050a06020601090207061103 78
    0x10f00708215041c00c107401d03a40d020514442c6041019004440c4254005c10080d101c00c1010403050811042c503aa15225194030302c1c1e6071000107600c1c0f1084004a844e000020b6155051120149100844920b00c0301d01d02140100c40114000803142c004000380b03401a16440f090318280d1a5204044d1300311207440e600780104003000280c40040c4606203042d10709402d1894804140806e64440b400300811607002400010103200342d0034060080f0328064412200c5801d03d548401b0103030711800040600103501c92809005090700315000404010003c0001c000d200610150b00400202c10800420300e28000900450420968006100503503007000406949080c118280d4580d400b404101d14046504424039942d103142010580e034100546901920007091b144e920314500007150459001c44c81060309020000c60402e100b44c01800003500303000104503090104024460f9110740c051403090f5090001031166560100d009411900000700243c0c40b20000c1c42d020000e00700440000720702c0c01c0b0210400c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 5543191 1250 5541941 5541947
    0x1803121206030b0a050a0b0307050603011205010902120d030b010e011b11040c02030c0c030102070c031403040b160209010803040b0a05090303040b0a080f06190506071704090606090f0812030405010b030706 90
    0x142c0105e0456104010707d84902c400e1613107481c414400e6943c00082840104001486417280404132441100001182645540014a084590048007890781e021f10300f90848503402d88110b5544040c00d08002c2c1c0700811840c0003c085800c8003980180c0361581940300c00800c5440180a03800c3d603c010424094084103480080d0b03030307070040f0200d900c0d6489180780001075410103100320341c1e80c1a040201c4000080c11610b0310303154940a0604510b42e44020000000e0f589450400b510303002841d40842c2034002007a0040004254040c0c000b02c07603030740041204021050000c41280c0c0400258100940c8030740c84040041d04501507913001c0008074030001615015603500c444142c1c850009140baa0019803100030a00c807281ca041d031000c03032010480540034070103440c248014106803841221150602d5049031a00e00c039540045d0b10140c03050340c6850060101907044284d00007d0400218000c080c185004d40340341e41c41c5409110111207500000200702844002c3d0030850010501030111112140c1d581d40c01 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 5544441 1250 5543191 5543201
    0x406080715080a0e06040201051b01110301080115080c010e03010b10080f0a0203040c050105070f14011a0409020a05040527030a030615020d08070e031204061803121206030b0a 77
    0x30307000628818001003000203a0b214070100c6051000040c4415034481d40191540c0e40605040c4546a92011800c24440d40034040c1103480c119204003140c8a500d0a90914203580204a4072007000010032810300c201c1c0e6001a0020305400c0901c3c0c8032a4107081c041c0030030b004041600c2c1d41ca41120080d5406100d40e070b0041c1501c1c0c01080d80e444031024954500075980202e000c00d840042c2810150b510401c402d6103d003000c0c003e00c50240000300004031f45641e0b6001e8040408101c0b00d0280d450b0300039042004039402c9800a5440151030a0046000759030001d48009014002c840c8503640d039a01162503003000c040c2012101d41c464444011611001c00c1065403904400f005000007400d055000c07800c001411001d5421001036001070521810000e01502c03210001044141041a03041c00007119942c104002c8080505450180c0d070b4680c01d241d001003507035285e0f00702e428480b5040745042000071944002100300c8251450060050f03601c442c5420f001c3e00d2941d0016048a4604051103030558095000c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 5545691 1250 5544441 5544479
    0x50412081003030509150c0609070303030b030304030b0402100509211603020d23030409020304020a0605031003030309020d061a130608070605071b03030203040306050603030f0901050904060807 85
    0x485485507200e441d07501c0301c0030141c04000c001842c18000d07a462402d01000484410b03200120842c105248440030302d1030204107c0e8000d0300f43d07014840c2003050580610500c011060f088d0040c601c2c080c19603c1d0120700b0200070b800240901662a103540c902031044055a440e60801001c107008a2081004444411a507552030140340c082c0d0142c10034085004200c2c2002c40350701a0280d024002292030b00d15070f040351000c0d040e007000d550002e07841484c41d0502c010000703850795800058480c1054018049002074030341017541444420010720521035a050650f5040713035414500881e210680b0f1000c544500c440080013000b481c01c04060440d441340019540c5da041ea01a29102400220841e00b207041e200740340b1800c0d0042d080360b9020701c0310a100c0c030000c00c602402001c10340c03c006041c21086014a5282d4402d0300160000b04060040144601039550021011402941024000c0c00915250b00c0b5518240341409400a440134198545030828001814120305613850180d441c50070740d03100501001 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 5546941 1250 5545691 5545697
    0xb030405060a0504030e010c0302160909060e010c0507080c010b060d09050c0904020a140a0302062a03070b0114040e061014030303010807060e01051b0a02040606030b03060f060f04050412 82
    0x902c0b00c002485a42c0c40340da01961500103040b06200150b4840380140026021800303600840c5403000c40c9904203100401510400052102c0c45090640c1141c2c8031900402a41e414403100c81d00702a44001510314094000e82525580c91100042030700400c0d0201449400c100041603a8440624a40c07020701c03428080c406881d4450900410080d005000303c0340290b000150640034000c85000c550889105040a4900c000054681d00010110381110310a002c000030469048509802c0c01a04031150400c090021030038a481540e48080c1c0a9050050f40d05907102c1440345021542d46400c031040c2ca51448003034075170505041c2000340520701d040c007520b450500c2040b030880c0c103810000100d0b8101c3d039580000e008624102001100c8114945c800c15040250034002001e41108203907800d85210125001880c01040c0c6206000980340a81d200409151410303e50110340c0d200440d03c075034440e515450031006640c0300000140019031b0300d017010380c001d0f24240c00c0004121000d4006400400315032 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 5548191 1250 5546941 5546953
    0xa030b0609010815060c0a0807031107030b04060507050706020a18050604080a020402031e0a060807060512061011010e03030a060f05010c08070303021209030901111623040203010b030405 82
    0x40103020251007501105400035414400090402074013600701c00720408002c048602c0d01664044c1c1501e031900c142d1050b2176250300000c1c2103080503017050100e0505501000034024181c0386481350070110900510140200e80c8030b1000542c140c1c8030741704607038103070740d100f04110340f1402c81c1400108400d0301c09020340351601180e00b001c600b91814030161030807910700380300404e44a5007503401c1c84040d42015101007620f001c1c330051040c0c1d0b172603a40c402910a0001c0400010420700d0013071300301c2c6820082c0d0711280c2400000c0201c4002c1c05121010709500c01020303034a5419004205108540e000c02c0107445803100d510b0f1041e800d00400010000b18040c003030114003032114a840714156050303011144541d40c042010884491700080059024040f00344c02400c7c0142400048000040c3daa03004483c940b11640000545100e51b41c0c010740d02d40081c0780144010150406e0300300c50f04102038503030f02a0800116081231004400c0c024085101c0420750f000e00199200d594950b05140385420070346044503540208 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 5549441 1250 5548191 5548211
    0x209042712050c0a060213120b090105010e04020a0314070503010507090503010e030901020703030807140d05010602010e01050402010801050d0c081005010f060201090507050108060d0c06020f011505090604050c1303080a03 97
    0x2d0041d1408680404082d028203011580c1790002540625040202410b20810001d801c00940d60100c1189014644140c03507850301903509400c444058102c0c0604c081c080c001d000168583c0000c200030388e1350007580f040814540d55045864001c55034002d550540c2004100303c03070300c0e90100c0088219035080d4000e101103421002c1c030310b450740500c03002c039401031703104810800c042440703500c02c2d640105c4c0c1808e021491103207401c0c0096003540481d4440000b9070b216001000920390900c104040e654544000700018102039000070080c800c18414517100b000201120010302860030002002800d0700c41c21030f030100b01c075007040c0e01c05004244601c200b1041010b00000b0041d0040c0502d0368002d07072003070180060904040042d038640a0280241360415610394110001400c40e2800c60f002c0c048a8005014004229021a0958440140a205807074003004204081d495150215400400407140803030680d075804048001d5010b4010040000300803071400000b4807003400010508407600340e0b0148101041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 5550691 1250 5549441 5549447
    0x13061d0c03070f0312200307030203030610030b030a0204020c010b13090308070f0e0607060204050402030702060414070f0504090812070906020106140d1101030b060d02090406050114030a0209042712 87
    0x14031000c0d1040091722252500b0700e00c034042c0804401c0c2031118110001019400c41899078101c845c044025900000c24444145007070350881e0300c802003030319013881900b104c0b030003090302c5070300d12a4028081e03500815202140282034000010425018019141c104020312030503000d000c0f10729081d8045101c11000c260998072034a1072564a5005803107220700410030205000d40744d40007003002d64070781c3d078288000b2406d65035500003180a030307910358000c0c000350a203400e0022004050310301a90890b80192402c0144400403070004003200c60444000035001e10500b040034062042103240d4078028107210402a51035080f124450035180e080c2c0c02040391548584a25002401e180140c2e03a210110300402000582550a0644607210624010400d030300c83e070300450302035049000e0300c001081e000320f4042d4584c24680f084000901c0c092800242603d240d5500c00d040348005070074449943c2d00000d03d100c075600c179500a1100c0701350161150030072820550110b02d06e1410740100720b5071181f20310340c42d20038188 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 5551941 1250 5550691 5550719
    0x30601050301140303070803010b03090d020c0a050f0d05030a0207031a010e060d02030a050316060b0901060c02130216030e0112050105060405060a11030309030a0906140313061d0c0307 81
    0x1a1a00e510310790800f00046015207103c800150b0600c0b0810403000000e45500c00340d030081440b01c500c540c80b410541042414002110b00c034100b107500820003990701e50707160760340d0004981051300d41c0b058804001000c43c1d04001e92000c094202d01c00011140610f51740021070008403802036081c08100781b01e14a03a0060813100b80b241c2c0340c0d4540c3d0100402c0305403a1004150034000d100804440441d5125642c550558004031070310a610301540050354280f010502a511888000b00c2d4000c0e1550305100c009444854102c6010340504030b060b400c900c1e0440140c0c11a007010910a218080002c0b861500518800d400301e134250015000c2d00200d00004418083d95068440062000b0300701400e00040c862035800905000d0108401017644414000302031000314011035059003d183d0f100001400600342d08025032203282007200302009845202800802d594000d0400c0c40392640c0342251307044c2040604506042546031810180d4100a400e0001803100600c19081d019078031003594400a080300c0b22 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 5553191 1250 5551941 5551951
    0x6070801050a03080307020a020306040c0f091407050306012102070c050603060310020c0115030b0609010806150f0402190e040f090b060409140f010501060305010909031205270303040209070503 85
    0x20791910b00a10000b20641c1c091a482000e40c4100c030b07051305080e000245046c0091360107840740303801024180000103000a009025210700c2e1024001401d024807010065800203244030200034002c0049032440e071140e00101580c412210300c002110310403c01c80b000a5000a0045850b07209466001a0a0401d1030039a441200002d020740728075025859000003951080c401c0034450356135201040601c0307226081040c041c41c000c4019042c03c0c9000420f0040d40381d0180c21011242c2d110b20100201e8901403281c24500d0201941e00f1020b005c0a900440c0190007003c8030120580703ea4054000b00540c00540748440c0c080442d000d01050502445410859041070000790440800600041640c01d00d504440c4649201c0c0b2402d40c010060b0301d49440c01d046600c0500f0722583d4443c001027022030713814003510340034201c408070400c508401e65070082e0408042c0b01c0320220f0162a48006581280d02c40b490003074001030543c89002103050110b610ba240e034001c40d412072041c050200420364140c82801500c0c450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 5554441 1250 5553191 5553199
    0x307050a050d060c050d020408010524090c07030207030605011205070605090d11060702150703030c020705010903020103091103030313060f050f040b0c040909030e040c080c0301140609030102040b0405030607080105 94
    0x902e00d070700c2d0390000d095035100030b0003030220400c0f4080e14a07850f0b100a2009200382c1c0000212410001e800305041c56400c2e0311420741e040100b000001a039105c00c2141e400500f0221501e0f640e091340c1c40c0aa0504840782d10281200c0d2904000041844403203601051161180c07056440494694901380c669000f1074413855003120a02c180b0800042070300001d40220000203010320305005440d03000800c40c00345102d4156040c807011030080100341d054091040c0481c018000b81c60b88134100302c0020030311003452201904041e1941d04010030300140066448032084050107807552850147d018180303510b0f0141044031054549000d40c58800034900c1014010486da8603258425143ea4440300350341341e805000402c23464004c0100041240302441180348103840703a20b8200c0380c159001700b00412602c060400609006240c001c0214890380394003100d0540700d10281ca280000390090215483e40103041d2101d405600c0000c000c0f81503008140544115202101200d2031641c400c40101e0b000d150a1285a0700 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 5555691 1250 5554441 5554459
    0xb010504020c0703020901090c14090105030f1e0709060908011b0f02070b030103030e10110c01050c010608150406060f0b09092206060521150403020a08070305090307050a05 76
    0x450314060300144104a0803008503203405031a60002520900207901943c0303026950140e52245da50464285030018550158180c1040d0003180080c1952200900d400200c08001c00000c01442c0e030b103854400840b0702025054018601402c01400b2178020340a048041001060000780518050040c80c505008040c00b101a0309625981580c510b030b01c601c0c03c0703000e50213054004141c03c0c0300030010318002d501070f98a40070321440c0201442501286481101c0806c003e51900c1c2c010203400041d0544407207802c0c6040ba03621508044030a00600c41038100d920b240c080c0700e803001c9440782e01c091054026400740c1801c2042c1903984c9980800f0308070900c1640e030a1203051241d40d1062070129496544880790701c02d0b20503540c030711009000740020b050208580c025540c2000b0b00450600c03852000d1110a0001c2c5c0c11000101880215500c0313801d45031050801ca132a1000404051090141000803903000d40816214002d0746405080c1d078100b04000ca0081c49003520000b075900e07004002d042110800740c1071f040 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 5556941 1250 5555691 5555699
    0x3180c0e0c0f0d0f0f0b0603040f0203120403050c1e010906030213050a06030207030809030f0405040b030c040908030108010b010c030807080601031b0c02031b100c0501090807030f0f0c0b01 83
    0x692030004106181e0070900340804070403444000014003164031224800500044554012070403078905803d1404018a4005003c0c0203440340030840ba08150415110491041180700117460046201d5100e45403401c04180001049000604051205800c44500d018240e070400d000c0890090700d04618001160f042007002814001d5000b4906081c0e0203c0120000717072a8400300d903402180e50b012000083e400107410050640c0071410307a8000d02c240c2c010790f14120088031540018025801101e1142d640c0e11211900356500300101002c20f040a0002e100d00c500e6410010320b02c0d002449804165400e00e22140869031140300c25202851341500d4610351034480b100100c800c58001003181c2c1c141580c0c1c40a0411448850030401c0c50841c05555070403100295105050074220001d804001c0002d5102c869501c9550700000400d030041c0d50715003d4400b00c4103017055030243c00803c00c0a44a0080000c0700024142c0c000001c01180b0a9a119115078440403401100e40d003040e5038002d8400e50740440144 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 5558191 1250 5556941 5556959
    0x7020306010509180a0305030703140907050402090a08010c0903050d020c01020d030c02010e1e010f0204031109040305070b010803040608010e04020a05040e0a02060f03070801081501030f080c0a0605040303180c 92
    0x15801a1a01d8030410505110f64884e62504c070f50100d083c1d0100c0c4000c0200021a90302d4007460a90360700707003440503441c0c1c104810600e944220364022148a2600468510360a031180d0b46110010071042d002404600c9183c00007038140d2113180005d0380c00c1d008091303845c0344003400029011210501039000706220501c00c0021001418035a600c00210354880c01000611072040000d680c0b40300c15841e1b500c005224101001e4211a6800420980d59005020400201c0e208401199116106440c42e82d80e42da16442e040f20141f103240d40040c501e1281c0d40001c02c07001d10010103001621060b45559240e644c0f00d200f4280c443d07800701c900a50000c42c0500c00e1015041581114540780f1618048441104040d40020080e07080510304e901d16480103c100159a5803241e0b02a0040c08401e001c1c280e101e03404128078660078014040035021010200a40c0100308981c000c403080311031020117551003803246c0e00c0e010000d05400e54007600000e05049a03030410a060b075803400e101c10303030040c0c4031101585030803000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 5559441 1250 5558191 5558209
    0x312040b0406090609050d0807030911040903090e180105070e24040b0a020303041b06020d1b06091202070501090b0a0c02040b03030307020a0c0b070309050105090a0302030f0d080c070203060105 85
    0x450740320703441c1e4040e900000c071303103016016169100d5806084800c109141c02031030340100901840405041107900c5000c503640101c8020b90300029a8041807001c0755090545488134242e1020409043c081c08100d5114000014841c04821100080c03129448800701203a21038140d40e02c10354000c008240c1c0c40a040c04c2e0410348492088160401c50a060396051030014641107a00c1090140e0000000c000422013281e070004a45041349421601d0b42e41040380007544e071990124102c090003014208920595040001c100061b54082d0050082f003526190408142d840700c004480940f05103007000c42e00f0b40c0a03c6200050740c59034400941410140d00c01110038407500c0300241e8000703940700002c03003903520240000d601c11452500280346600039031400b2803000c1e03581c0d400340b20b8000090059800007944510000101c400910308217480b14082ca000401101d19944000d40c1840340458400c6003d00201e40c4504030f91158032000455030b5103103404146445100402076250300010018030542ca800014 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 5560691 1250 5559441 5559443
    0x60d0309150c0b010504020f090d030c080706060e0702010506060d0b04020f0301080a0b01060f0203041202030309040606030b100504030809060f0408010203010e041101020c01020615030a060f0204080c030312040b04 94
    0x4140a000c0d41c0700c00d480301c15401c1c00c14050000340060b07007120074010a056001d0050606550845c684540d6005480d1130340a075a400d984030b120008121024544240c111001c01500034028540ea0fa1503841c2520042802d40303e00301e030150004001a0345240188502841131302c01400701461700517801801001805480003403035000b40d09100d4074920b410407001842c0030b004441c00401ca854002c3c00c0000742c594050f4012420020368000c80004a03902105031011103d10340350a11805a05100103401e44c0105543e81e41c0092805000103882e07079040e000785164450540c1c8848542c80100400c46481c8658000031705641020081c0085500b4a10028860303000c0d5001118100f648500545081e41d03c00e03881580105441c200784400d00849400769525460240018500188107a0000c0d448010050403240d5505540c1ca1a000540302401502c103840d41c4110200301c003400e00403c20000b0341041c0640c07003e6101f807801c1d900c1c841c00c000040314404032424060400a6407503a41d40d861a0b40010300c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 5561941 1250 5560691 5560697
    0x306020309030f0304050106050301060e01141e030604030e01080105010e010207150306030807080301060201060509040203060f04060b1215010501091809020a05060d0506240d0e0a0209011d0a05010509060d03 91
    0x3c00c041c401c0c900304000d14043d0f8400d200111300310345070204060075200203400c0121859448001004801505501c0000300d19041e6501c1c502e010811a458030150106078105825005800402c400c00d588400c039140c00c03441c01d80f1468a00e0740c8800046895403007076503149000d80e0040e0301c144181e86002040315901c02ca50314000c65400e44a64a8441a4001e50021035100c0d9022005111154081c01081c014100a0700c88062614040d00041e50b5004d014010520700c1070254042400e004054015600c0349401a201004ea030110010f042d6036007580c415485040013280c0b00100b00ea6120710f00800c1161103450f603841401026412501c01000b03440d000b280d0004014000203201d0305d410000e001492414080016a407078071800340706100485814a035405400c0040030400c0400070015160078110070301300014210451400e480c41c044d90302d82d000e0361200705980001640b4000110ba1509a035284440c00d0070b0b078480c0c04c002c0d02070743d01c00c2c000c0f10341c08044400001c100d406c0c40700383e950000303010745 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 5563191 1250 5561941 5561947
    0x1060f0f0804140a050d0306080102030606040905040c0915030b010801050411120c040614031e120d0902041107021005040503070b1c0606110d0206010b0403030e0607050102040b030406060618030602030903 90
    0x383c4080c030380b1340320079011078580c0c0080d80f041c40b015815200b020000d000303103002036185142210014032a44a240180b01e807180c1d0300c0011a080c42640307001040034042c180d90400c0121124102e00c02035000902c4126003154400001242e08181030207614040d90b40107080c009a8190a0b04000c0884046103000c201c9204000300181255918003079a002840c030001882e000c06400000d140c1000c110401d00c0c81401015400e0004081c2e0000b49280350f40c514100d59034881e0009800714015000101d400f039401810600d190006030b65820003018081d10807240e850360700a030744a06030b519004902c16070354560050b2204103c81040382c0c00a22100001180b240321440e110b0b140c0c0d100321401030704405c0c000b62030b0b409560305594040101049901d00341c002032140e507140c40071820303840c49140401010010341c50807117074180e100c040c1680c00c60340d03200c40255140e40d03d40801c160560411a016a110750914900141280c01928407503400c80424441c0c244190954641902075800608400d030640300030 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 5564441 1250 5563191 5563223
    0x60702060a0c21031107050d0e010306230108071d0609040207020d06140903042607050a0e04030e04050402010c020405040c08070321020607022a040203010303031401060f0f0804 78
    0x44025403c100b8003450290784091900c480040842d40844540e5240c814100b01c00300205e40d000500164503555890801c0c00c680c0d07080d00403000741109510240c40140040d0581007045c0044492143d0040203a88559030ba03900c90100315812030420751901614405a980c0c500c003801c0841c0100031042c030140000d0303d0500241c2c0405c0a81d02284400c0c0c84c199aa08030710440c008400451981094480c2d0085052909180c50591b035007a0b29220459400300344c8680a4030800c013800340d480100030081c8000e861603610010403010100c02c8400f100002c0381170115075400e25280c070403e8041c81e0107a490315107c400e00d50a000c0281805002581c000d104d0360b4001803c20f01c02c04c418030155100360304040c0c00c244400020200200011401010740d00000304008140380c0c0041d40a04003012207280498618202c40c40e11a40605030030007a8005000200110a154240d002006c00c2c03100c82c0381c0d0344013a070303a10042220450a90810400000c4601024802d5a841000c0d02c582080c0503c962902081807 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 5565691 1250 5564441 5564453
    0x20703080309030c010f021c1509050403091802070305120402040e070603020901081302030c06030a020705060708010302130c0f1404050901080a02090906070e0409031206030602040906080c060702060a0c 89
    0x100c031842c409900000348402c020b0070038091400c980c10603400640c18555031220408036041000810b4850790358441d84130382075070351120442c0020502010304100c40c0c1068200200490020301030200981003640c1d402c4e9001010340300300e80c00d20703401da91010b0805011003803d4082000280c0281e034041e803604c528a4910f41c4c01e02180c0001e10841e10300580d9100b400c0d0002d402007030001c0118220300714100890025071004501081403000882e0b400e6a25a82d44410400034001e02001801910400f4200b0002e5a0050010340c180c900840302942038640842c110800d036400f41c20604c001407e024103504603603001e05440b004403011080d845092075241d5010071446a026070260394140e00c800340318015402d103c5000c41e00090800081c110a103404c5c0000b0782002c40c4031000c1802683c1c0c0b00304d901c0a261080c1c00360b01070b48441c00402d001c907564a0a18070041e41141c000e02a1040c82c00c00300280266001520070514000035100d0350030310205800300310440d000340410500b403000708030306480000c1c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 5566941 1250 5565691 5565697
    0x13120201020919090b0d020312030702030d0203130308060301021306050d020403050109060501050414010807030201050a05070203011409010f15090e030702060301060302071707050303040221030a08090c010306120f0302070308 99
    0x3100d0043c4000c8516118120050751444170303040d8090445400b001e005a03c0c04140c00a046906180c91a540e44031803030128034500c11581e100f504130780b0110502c03c0c0d0040c925140b184c01c500940c0c0c1c0507016141c0c20101800c078880d09280d29801040070004002c407500510290403034450600b0010b08040c4c0d04c1c0c58140c2034900c80d041c00c03600580d88000601003860076104d03010742c102100010381140d40c1132042c5503a4880c00c6001c068140000401c41c02400742c4606c084561095010f0002d111314800d400940e80880e0098034401855405d003007000c3c81d40010340c815001840d402c60100e00590307280105000c000c1540c1c0102e510140010050b00015859140086000709115980160346508504001d03400c0d07400d141280d40030700c40412403200410700010541e6003068048038034580c2c03010800e20000040903658112070142c0070221f11544601e0704141e0007440f0b10420743c241c0301e81c26100001182203071403501641c0549030922540d000407404071001d245629200380111945c590710307900c800d20190 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 5568191 1250 5566941 5566969
    0x50a0803030109050108070506160f120c0515060d030c02040608010e0a03020f0105100306020d06050306010602010b01020708070b031b090d060b010f0c0803010510020a0b0a02040302010215131202010209 89
    0x40d0000004000e119681d1189900403c3c221000c0d1502d83d00b0100010714511030041000013408600c0c80c01018025036a0440b10f1303903507101c402c00100340c60240002d00000400b84080da000d020b12070041c107061110031211442760000034441006922a5581a41c00500300541660050360341d002c04170302242c09200301540f103840d020040c0800355503071900034079240b42c4608d003050607410710052005512840803034200b0f59074040c6000d41c485030325000c031800030170880d4440e941c180b198100004030681c065002c40340c60704081e802da4207c0c0391100960b13640c403c0c00b84180078141c02c2c10400a400001282e00f0240000d0102248a1420302e410000500c5c002c0440740984016598080707680380d568002902215940581c00c180003500300fa0f0702c81040f0741c0014841c0e58007500800b07020340e034014802e0043d10070790b030762003142c0103028200502c40e0070081d04140402ca002d8451500e28905038048992024801c4161501680412a00c1e80d15a1710034500700080d0030556409120205c00369881d140814524 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 5569441 1250 5568191 5568193
    0x3020708070b040b070201061a0903010209030106030c050406121505040203030408070e0105040c03050f071d0301020d020306030105180303060d030e03030c0d030b0609031203151203030405070b030c0a0806010207050a08 96
    0x641020b040400c400c0d440600300f80291b81c90b1032003c000d800940c200503050342c42580800c40d01cae03c0b1900302003400ba1055005240d41946444000300421805001c480207840e000d03903082150070746402c2481403e8400e020041c20140c0c5c24080210904495000b00fa0300c1403014055030b05155076447da0601d04002900150032071011400180a00d0519104000c12843d580c0f50510043c20101020b81d107904016041c1c0c010030400059280c580760020b545503907040302c00380c001c5668018601008000390003d8034114800c1d4240070210700d49941c040e0040040c0007860700514a0744d21242c0410407540c801300700840c18030004011910b180c1e5014000f81c00d415061201038500c0780c41c00103005088410942c0940c0c8500802d000141c0340391000604100c8000d00910306030354a0302c41800001035440e81c0b0f40103652041d0030340c08950341944080051801903100d04100c6840755140c22181035540000c5a19605010007030200c0c0d07174050700c41c910080d049601070054604903906e58001c5041401190465209 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 5570691 1250 5569441 5569463
    0x106030f0207120f110708010203011406030103030212030a09020904050606011205070512040c08030a020703030905010c03080c09121603170408060403081b0703080f060406030804150302070807 85
    0x1049405014064420501020451070300407243c0d119220b002c1c204114408010079944c48140e02070042501e921000540300480d50f115580d120414043d500c24000c44101c00c0840542d113103103003003103001e0344c0c1661f030b068000c1c192980003039000b41601d030030040c41d101c0f034140c9a402c0070015840d8140c0d26400385001d40040c15192400d42d0016080c01300a4691421680c540010400055030010980f1922440c0704060071094880e82008141d80d01d080d04103001074000040e144500940000380c010441344251910100c80b50754200540d6440e22603400034021480c520300040d000c9200341c00410302d80d84000c110002c00e5500490481c076045401400c801e885101d03400520520004060401c0c03200405125149402d0501d502c541d200c1001400090034800c4403004075141408224050340c84040030401161205403c1c20b00901c500d4044d00c0002c0820b41800200304241044e010310740503281c10040030b40c03401303107003400001d5007400c07081e090810513600b8000f40d00007a101100070403580c0d00030540024 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 5571941 1250 5570691 5570699
    0x6060804030806030703020112090c0e090c090c040602070506070822080f0102030103080a030b011b0302030714061302090c040e010306090308010602031201030f08090907020601090606030e03030a050406020906040303050301 98
    0x200b405405090726110f40c1c04002c041005070390068486103011602c0002080f94030031850445a03040f4a83c001d40300303000c0b0b0041040380210f03001a030154103081c00c803003e42064841e4031039602d10703204070300900006811101080c001e80c18000001d004551081100d00e10f0419a94842940b4807820715072201320b14028041002215010080020f40d090420003c604c4d551650780d800a1600c68042c283c0c090645a145000a44e801000b140d400381110b01e840e26003d030201d1030000c6d240e5001810484840d03148084c89000c03480d00080c07091140d41244031a0651501680070061203075002403801d00815010400030800c1e10707810032814000c51182c24045014000b034a4082e045410503048a000c640c02409104412500900207604517504070404000704c01d89801c00042e640720380743d10960022078141c2406250b560002d060350488811000070400b49442d100e084096414440e848030844d802440803950f10045a4400d0350828400c0790014a000c82c0e910200b100c41d086640190701080700400104 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 5573191 1250 5571941 5571947
    0x170a0305150a060903060e0703050d08070801060305010509070c1e030c0b01050409020604090207050c0405190501140105070305031005210709060308070f151a0a050301020406080106050a0507060606080403 90
    0x14070a90011141c0301102424200010040d1072075200c060829500c0d160019001002802014003030340e001010784182d10886c25000e4075a0b1801d8510b880002d07003100c00011410310910803641a00c900600520321900c5401d002c85915101410599640601030784120600c4483c040701040c1c180b1a031101004d07010076040003214140140d0200b07001e06d04103c1d03110300603a2440d0880d0141c80c1d20f0100141c0356242420b0030391604014280054000c1d1519042c02029040041a85441c01c0840d00500840c0c3c0c0f02c12020700c2403080c0105d0140807603414441c80740028011000745510612400110307040700e0351840001c03000680c95440c10f080d04100060070082800a101c0c41000c0c2a21510500500d440d65440e07100d103128044010304039040c00d02c82d000c100940d40026189141c4c0d03d040030320281c40c000c1c4054000e5008001c0c1d46104d8044454006210304060003614100d4090f6125103402d60710306802a11594055003400c400c020042200c00c000070214400d107030140a8543d07a941c1d40f4a014038001e = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 5574441 1250 5573191 5573221
    0x1030e1603021201021e0a020f01021b0c0a0b19030b090403050c150103020a0b0901052205030c040b06090108040f0602120a060506070506010b0a09080105180c0607030207030b04170a0305 82
    0x2c003c5034010440b0405446010280c00d00d103c0000031400e07038800d01c2001c12400c14084078540121035000086811101c0c0a1050714001e03901694252040c81200d071041007520a6144907403500403009100104031290041c450410001440c00d0104070911b1880004852020841701100030440200d815519400200803921107802d6203040d4000c1c030b504607000202120400e1151008210700051400b04076403040059a0a99043c004940700b210ba50007a9280551424001c10f40240700b19034421080380b51a01513004400c00c044c092504c1c0440702801154041001881690800c40701d101c2d40000481a1000700700c1d502c14814442c850381030643c0c3e0902583d4203944924400e0805100c00d00105002060150450301c51242c0705540d110803c03001e40b1201011fa10448603135180c0420009580040c0e6180303000d950b240c001b81c07114681c850f020480d0a0140035000f03001a400750f241070000a880d0203641c4d402c41e0140c1c02c0c40c14185500c8480c201207502170401400040e4650080c8003190507640b1071 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 5575547 1106 5574441 5574469
    0x406020405090405070302010f02120d0902010302090603151008010602031b01060b0d02030a0b0108040c06030b010309120f020d02061506070f0605010305031308062401030e160302 79
    0x300e8445076031b40701c142e020554580200e401148003046e0480c0e0070b4071801d4150b0900341039101c00360040c03c0c2030030100e0515900b0498100255520301c045d6109007212003041c0007040b000c0c4e0520a8050070f1001c064140140c280c01807001c260044251070841d81c40c2d240c1035103400b402c4400b00b4050041075000350009a000a6241c041000c1c50300150b11601c5820004d02c205218075004403903d0404a0300601250040842844043e1107a00111076600052501103400b01103511a1421a01c40143c0c02d000b1070b9004a5644800ba0140080800c844141c00503246600d030a940b402c0032a5500ea84803441040700088074002c02209294508135503410490401440d070712498640e5031303030740a5a10301d060300042d010001807203080080d24030300c100c0c8054807070000202c900c81503c554500007600c0c03c0c1810384400c60749584034800c10140740c04038100710b9404a000d1031401071001e110380c01c2d85 = true := by decide +kernel

theorem cover : BRFrame.Cov 5395691 5575547 := by
  have h0 := BRFrame.cov_init 5395691
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 5395691 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 5395691 ≤ n) (h2 : n < 5575547) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
