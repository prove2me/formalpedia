-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3494
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T09:49:29.222968+00:00
-- url     : https://prove2.me/submissions/32b5c384-b6f1-4d06-a42b-638ff2bc48ba

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 628237410 ≤ n < 628417266 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 628238660 1250 628237410 628237417
    0xe011d100509100305070801051f0e040830040b092e0204150503060f04050c161e14010609020408070326180301050f100509041103070e0f060102030906 67
    0x4040c1c0700868590fa801c81040c0403000c107070f00000e1882c010a04006203600301500103c0c024010300ca00040089a01d00079401240c09034803403403901480500c002804a20a4400b038198092003a06207a4107040601040e5011800d880d42c00b801d1400d010240301c148480d0303141540d80f2004c000014035030380f95036510881c2c0d0f0440c208540700b902274298a40e002034401c1601070310010b01080801320b41c0100d00e80401703081504111403081c061060358001c69154034042c018a4010100222110b242c011040f0f03242c040821351010039075407070544001e4000d441c9030609140429501a440341c510b4a00000703d90b03800e507002c0340d103e0b55045005101c1401030307100100f1903604903680210303105012103424154810300182192031045c1844003082c03850004030b0f50f6224240d42c28003100204882d66407412809001c000541d400d46903200d04480910442c1000380443e504280a500c0b18050b020007036002a10300b451540100042d56880001e000f54000144107081e04038170240043c5040c406401c020442030300 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 628239910 1250 628238660 628238669
    0x10c110c13060f0b0d0c02030f03010e1e3301090e0a060905070e01030b01090f0911160606062d200115080c09060a06080408130e011d10 60
    0x315001c818244220300c40c1c0c00300c001044403010194540b95542c0c0404907a030003501010b802d150a0804c010422803020044030f520602e0061614196400c1c10312000c01c0001c0105026080315074020240b000400340140039101e07112080f045600104440140011034012446c007118103410b00740900d900303a030000103c0d02a40c414811945181d89c0d00704000c40900707810740c41002c90500c0e040c01d00440f582d02040314000d00100707880510405c207800f8011548400c03684561118403040324401e00107003000360000491107007d00007003410260507552800f40005c0004048400c203658283c204440c5402000b00310640005924050181c01c001d2180308070105101c0055080000000654464120080401064400e8100208099a05800c4070310100c00b07507014036191303031040040b000400d2401c450128440c0c2c4001d850a000f8520f02801500c04d140d01410881e00762206108001100d006045480000c1645005081003940340c9101080280482001c0c0010100e0045c10004c403078103810032020413607 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 628241160 1250 628239910 628239919
    0x20f09010c03200c150a1e1101111b0601060509090a0912180503030a020a080306060f13090f0225021201020406110f2811040e0f010c110c 61
    0x1407007440d04640000400003e00c00c1905050100d58203007400240018559000340d922080c1c02219000d4400280500510f40c1c0c0010132800e480c144d80316500c0c0040c00156071500340580c5094151440a080d259840040e10000f40081003c0c40c0e070322913150121100b1884074001d041e4550405000404c03510400008038081c844000201c0c2d03034001342d0703441007050076000f4080058494075150b0040c0911442c16001c0080a543c10020031507103008021110007201035001000d4a404e982e0305c00172150030081642d64400c40c00d2000b0308074601d2100040000071a007003914100c090078800c0443c02c841014510298483c810700020440884100d02580b01990f800b40d9000d1856162000450301510340301412055400414001406900300d1344d525080c003a0321003515503103640d21811030f40e10b845088110f1201c00401142d103081b06002605810410301681c4001c612000880c0810b05a51800008040d154001107400107060790038482e0000c180418680000010210a051503075400c01500544c4207 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 628242410 1250 628241160 628241177
    0x40f0603051003020a12050d0305010602031b1c0507030f02070e0c130b0c0115150c0b07050d020a0f121b0e03010b03070611060c040f060c030201020c010905010506040f020f0901 78
    0x920480c0d00d0070380c003d603402000c00905035156640314284030f24880084400c2c4c4103100480c0b41481c0280100750584246500071420802c05e558ad1100340b82100e40600468010819011095181c01d0742d140c00c00501610b0b41036139404c00c0d2030014400d541c084104070454001090620900300d00f15003094101c0503020403962140301860851003011495440300070701c50070009920818400640104202802c000500d0800940e034542c07810851407080f0764a000201c00e100c0d5080020030781c003c002d400c0405450810700340741c40e0101c1c080403a80300c2460500448c0b5420f00c0382100e6030384215091020b242c02c070000e0054184820b0200c0483c205085d1590038010001001e03182d9803001d40c00315098000043c00c90703a0b07480d40d54102400f42c080d0403540c40300500401d070010b01c0790303100d003011501142d9074158400e0040f03241060885099800041c200c1c115502000090400e032000d00801230124040c100018490529804000454086c038030030406050050044034021518802501c4d802d10083c00c0410a = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 628243660 1250 628242410 628242421
    0x6090201021f1a01020127030c050a150b01020c010f0831021804050a0204090807060903030c0905040902130504030302091203191106060d0318080102031b040f060305 73
    0x4000e4007040422010300182c05402020000da008808091039400348501d04110850049082e80c00c0d07030407140b02e0002c4004486e40c00c400ca4006048a09010340340c0034a8a140c0e55072202e04100c800d99041c2c507962441c40e0400d03210410b52040c00c60340d003002d00007004070f01d07246000039261040e5011060140075494000031001c034080c0300c2441040140c2c410744401a02d0551300140c00707961082003640241d44410b0840f0514030b241c1103060040b0340050061003d160741d5420040688020340040340d14002c00d00c01000001d1a038055841200e00c42d860225000420880003812504540d01403031245080200000140e201c0301980b81402c81503c0010409694a06043d400b0341f0440000f42d4020210155015a091010026002c0b61480c80c14184456140c881e0403107031400882d0070140e681c2c01540100b8010b00d03105500b8848070340700c0d08180c805100f800b03005644402c6141d01c4070500f42d40000811444410210810003042c804150140c201810110030344040b0304580205024580d8130404185d = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 628244910 1250 628243660 628243663
    0x20a140d020d0c09021c050a02090603011e1a030717011a0306040b0d0b0a0606091a0c0f0318011106151005041e031a09421902090d0609020102 63
    0xf0207000c0d1444255035414450070721040c0e50400d8429180c0040ca800085544400c050085400e111300040140d4110303400d0074451161880c02c80115010501caa200c00a034002c02501d80c0d0301e5985000310142d40341e107441400a0000030701b24101c120b01201c110014041c040501c010210140c802c0481035440e03a903a400414020074a00342c281d68032200403100c290421002c4401e0368801c00d07003290107004d4656102019070b0040698003441d01003000101d00702580f00e9250016011601c201d0045444509035001c042d800c55020000344c0d41406148244005103507005608066041e078040028215481c116039101c0340801b03030021360391041d40601080808640302c0d00a55020f080c20001841c1c06124841c80c510320102144000c440c02c84501803500c0001c000f00418600c540030300d0000e0820f18182042095203d80c03130400410180c01c000601310844504c6801d55104900e004202241e5410320803119a2000d1100b014907017103a004104001c425100c82c044009515402030004c200320f141880180d = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 628246160 1250 628244910 628244933
    0x2010201090804080304062312091e1b190302010f1101150504051e01031b1706090f0d020d0807210501051311121003020319020a140d020d 61
    0x5810000c0100c1c01144c1000040002c02c11219261107c0f00296020a5002e035900c103102314800c6002028404951a10105c00540d9442a00c0b001520031485001c0780940c0d08040d01c905c6a1165070000b030f282c156800f841e0181c41c0132000121603d441914240c00d42c0c1c21110482e000003070404c002114240d0020f4060b080011800c0e00d428024410150001c180450b500c442d03110303082c0f0403400c1a01040846480e400101404c60100300706c43c00300d0b801e6841c0c0045200e5040340810381e4140410001031404a881002010700800d1070180020341041c201107480c141a20304001180d4000c5280c80c48400e4000540e404035450b1802c0403420740d92132110990701072130080b10035070070780319007080700c0710704200390703400141a6101102e03031004059101d107400045401c105819024010100700045801c00810282580b01500c10800700d070882c0c495000c00d082044000701140e034a4101c2c3c1c507003021031a140d1075950241044928400461b2616400640000d80c40c801c044d00070400c14035030005009aa0550 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 628247410 1250 628246160 628246163
    0x109020a03022a19030507121101020d060f050a08031204230a0c0603111204140a0308040605010806040201140304031e051b0f0a120905030601090902030d080417070201020109 77
    0x48000c0141e901082c0141d0310841d090505550040c215031100b042210b0150300c260303d0b0140d460078285a9140d230f80f0401401500741030020310101810780703039190100340020000d444e110813001c24100e01c0c01c2c80c03c1c00e208103980c1141e403080300071070024401a10000140d40c0034442c400e101e01d1031a00c90b420a10501d03c180d90958041074041d6101d880c0707403171002460341d2020780320307101c0002003559072042103040b1180c4040400241204000c2c501c8800c01c805210754105025501c005c05054100c446540b40c500e000008401040003041004140200c9214282c01001e020014040a14265000070038007441200041c603040c0021000c01c0501d8442c6a504603103408e048004440090900806044c54000722141d102407600d0700c0b820782509002041c601c6003800380c03000601003417200b41c0d0b0308420300781580525410012000c10000d400e80d003c102c2c1c00c0c001d000211340000e092a4500500d030610009611440500c45100f060000003002c3d58010340c00c8070380150780c3c11307101d90301c078030040b400f5021a520 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 628248660 1250 628247410 628247437
    0x1903030b0612010806060f010e0d02060c030a0807021b06040605220602011d03070b01052202040b1305010507020f01080a0228021e06040308040c051f0908150109020a0302 75
    0xa10000458030080450b040c0c2d0b1340c80084030044d035654000c1000c00b0b9084082c05000540c0b649501842c0d08151022848043c40288602e0402020f50b00d4980355030000c0301090002041d0406006120f501807001030760041811190406081421022401604c1503108a404100000601c007941ca56212000044108840350f04494550385d01c03002400b1303100300661084041310110144a8031140041140c010f240c0c0b207444005640e180c03008201c0f40c40182d021800d41a1030f111540a04002c003840200b01501c4d003030101a4a4040580c880032004c96142c2125042c00070401000002d44d440e94691400070070309282c010720b995a030007800006402840803101d0061036981d1440c040e6120300e110b4080c820360542c201c6001843c500601519240402c0007070810b50440d1000ca40401d11032541d45600c071380036000020245c1e5a5130041074001c9140001c200c030b80e4290321140300c8816408065003009101c01c4004001a42001c41c20307980042042c41500013859001070300e4058140240c05031005810002d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 628249910 1250 628248660 628248667
    0xb0c0f0706060302090123091e0a05090c0a140906131107060b1005070609020a0e010303050714030301080316050c0402030c0c061e0f07090e07050403031b02031903030b06 75
    0x5820030151400740400c0780f20b208071800115030400031030303614464884010400403283d80b087c01440b1880c40b026000d840c00c0b07032a43c2060007809610f4400c640c0140a0350f4000265803410800043c00d11900c500d1040c4503882c10310003001401c2d1640c881c2040500200c0700c3e0040b540f1002e00040502c0300001c091541d450412520b018042d01040142c40d07594000d044c2442000100070070001e083d251030b4410000302c2c50600540000c990141d120400c8684080c1141c0c1c0040c0d2142100c100d0302e40240c0c8101e001480000d0060100308003080ca4845140c85600154159414515215100d0140341006005450f603403100c1303024403104004050450b44003800840d581d0070074071807480882d030044407180c2052150303d000ca8440c40038003841c0740d161401903c81c00e0031920740c0c103404401c014018044004000036041c010611440b07a0805500071749640e1a0380d03035100d145140283c92144030b805048082450002c1040258402103040d400c01e107502802d01000d1030507803409130f005090308a0200d03001b02011 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 628251160 1250 628249910 628249913
    0x60e0f0708150105180106120603080409091506030b01060f030f02161b18050901090c06030b040f110417070e07030b01120c0c060c0c0204051f05100504030b0c0f07 72
    0x10a12180c28080781800e600e080c0e0300e400510031002060b821a03c170000c3c000004010152203002c040b100c210b21441d020405650f41d4036800e4094002d17400c4000c0c0c1e56550520541040411b51554003544070210041c00b071645192280c0003100414401c04052152402107181510300c03a078400412440d09400454440d213515512001c0510482d404075150381d50100d040c604100c0b01103103442202e100c1c00b030300c03d07001d842000c41c1000340a01130404e10407592a0348440000890f281800800342140781d0300000e869510408003c241c81d00440e0701c07581d05160800151001c3d8100007240e0a5034100c0e1703081903203100181120b500e4581d041e4407a5440407c100c0600c0400395140d0040066440c00343c0e00c1890004085070440200c44143da92003001c01d00a1410000040c2c6582091490125508000c0c0d0550107507004101038030021500e42d690200001e910030300c00550354040303402808007036801c000b280400b024041e00a1046003c040c2c000c40c81c01001500180c407410440e90603525460003944c0b01c40e441d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 628252410 1250 628251160 628251163
    0x20c0a06060f06021501080319120903030b0906040207080f0f12040308011505030601080402101206090203060301050f060102060408030a0b0d060e011109030c011404090e0a060e0118060e0f0708 85
    0x441c01650f005004010310741c89a0302000744101d05817424a03025600e02060b40c2840b241c0c200e46c1130000024030060021041c48240680300d80440e06000361004a456054001000110200105070381d2086d0320502c403280c04507041c681030302e800c040c443d5500c980e60103c107000d5845600500070380100c50188502008209544010120b0403141002e41c5001444c0d0350390400e0704c1c2c1e80002c5031501d00144071072002074090314005e07203100d074610003a0034001025642c03e201481903840d160000241e80c2d8001003440010305003481a9580200415100d202504210000035180c1002030300280145e68007101080700810143c0c4900c1e1390325401405c2603100380e00da190200203030501620a0681e5403a007010303021001d001c1320494140c0c02e8001c0107011890030b218010b5403001d01900008510030014031001c02ca003510b40c4140486000c400c001032000010300e103454401c1c0c070718249503505540d061070300194010306d50917090420550711620204540d0343c6081c00350311304003420285000c06c0c8034801c000a481c000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 628253660 1250 628252410 628252439
    0xa1407052a010f0e0d14070f0303110a030e01120e06040f02030f061009021b0d030b1c0305090405060d051c0311070209041b0b070501050a0c1b06020c0a0606 69
    0x204041d84280400014005403428000300c40c128000c1130782c1d204503a10914002248420742c0d44110b039104484c05064000c20300c0e10072160000a0313a029880c00c14800d050f00800381d07020b00840d080080042c41c801341e03001041401c107419041e050008680041790780558541140149480780c3d401c54031a450308d420241580316105034282c0c064080c0b0320040504683c0841c180d413040030140303024000d035481c0c0000c401c000c0d0310011340d07070030310142650100c01002024009651561101e55001c5010002501000b0503001600c0350400189511465000001d1b0024107031070b2940c90480e0b0004150b910070000c954040e00c0e2070002422402610245504200701240e0845031203440d03a81013142c0f0b0030b060000308052054031030103540460341e640000e0025083c0260b6003c0c005007070002c511031a517600c80006503504425001c48050b5140d01c1008071031031300e42c802c0c613614103e685040c9101c1c180b207519420100c1c0840300c01030701c1d0640001c0c1d0b40860420400100d40e41e2a4042402c00100b035448070046440c04 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 628254910 1250 628253660 628253713
    0x30e0f0a0f06112803020c060408070303051015052110030611250c0b0c060702060f061008090c060f0403060b040c08161407051501050103020f0a140705 67
    0xd18041c040d035a407020f0b51081d15030003c002d42c454500d2036a03080f2060707140c41e0030013000810141c0030405d62410307000c2880300d0340c041d6210340c860a4880c801ca140250070348500820400441c0c10a00c0c1c20030400718488448441140d9030f007040d981d00c600c0d003d0380201d0300100000c11030844400c0810322600694907040b00701100e0040d001009076035000e4481c8152481010141c0c00e0452982c3c2451221400d14001084668428007516040541d0368060030180e4128203071424543d003128041142c1c042d010300500e64450800340c41000d00d46003080c001288000032100c15800c004a0350005103462000300120640355a004043d5910340002100c144140d502034041200c0f2581000c0701c5144a0400e801845981070300c0782c5541c020380e520040342070368014080c0c0240e0100b10748000070f0030403000c03500020f0201901072006003405148190f600b000014040c1d100c1410548100607007000c858444007500c40501403484e002030020304407100007055005e03a8002600b01d01403d540c0000654440e0090446803 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 628256160 1250 628254910 628254923
    0x7090b0f0f180f0a1211060c01060b0c0d021c050307090b3601090b13090f0b120c03031c1d0a1703010b12040609150509070506130501030e0f0a0f 64
    0x60b21410034409803021a12130440172104429025000551500030107001100151069080658984109082d1403003584000c0d61608001480100200c0c00c1c8000d090512040c0014402d85519190700c000007081c01e080b0780c2c2005000300200700c2e06403103441c520009010011580ea01c0e00f0214802c1020f09081005201d400700e0b03d007203410304050b00005640c04541058585000c682d15203120704006500c00146490301300125080401c0c4c68401b4030a0302e00f401c41c0300750300040a000c10410b0100011804c81c9080156100341e081070703d0f40d40c002080741d00740b0b403020f10b4902c4500e00b69040310001e420407102c07440701c0c0221042c2c3e43d600c60300001550041c017400b030381d1061440c41d03105040b81902d01c420302818018140c1046408002141400150342161080000103130050841c0c44001420210480d20114151a0790901070724483c10454500504012a040d52404608a1020320000010722406050584860041450030420302966820320070003801c0e510141c15910300001c41c0714115800f101c0e107 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 628257410 1250 628256160 628256179
    0x71a09010c0e0a090e120d09020406060509030c0609040b1804060507050316030903200c010e0f01050d050403180602010c081003030c0f020f040911090702030307090b0f0f18 76
    0x81c24803840c000c000700040540000200740c20040001e000d8191050020800d201c1c42c3c2c3c820742250040b1000f410300200ca2800020310800510400c0b00b6644d00ea07200c14200070301480308102d0380d030780400c680005910450f00780e9a1234413458042030290080c5402958008464080b09a03401180346d01c4602c101d109a00803c0541e072008026119800181c0d52010340c582c002880020381c600a03803000b00340b240a4245104000c1d41e0703440c0071a070010225480000394100a003c040156006003400d0030000d000c0314400503100020780003c0040c01500c0d0400800364860021505050003010b000175201c81942448208035210140a40a049114900b0000070100340000b04c004001d004e031074040d298107503134440090000c3e48910b4864240c0034020f0f0303401035000c1c0e25a035856a0320310580502510440c10004103005d000c08000142c14000c1520007507400030410040c4003036002c403003c002c3d920061351702d0380c0344d04862081e0352031401366401d101f0032180c0002d85c025030b00819103c012140e240440300c0101 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 628258660 1250 628257410 628257431
    0xb0312030a0e060c0f030c131409090613060f0f0e25030201050711030115090905060f0405070e0a020d0f0506190b1902010e07030606180605010906080903071a0901 72
    0x70fa940c403c9602e4444201c09014030702d66480da03400150f403c0b180c03840d1464203000e070244040c0303140380d100d500c4400c03c3c07a8880015952400c298120b660300041d8000900090b00c1e0000401c0c00c5003554960040c02e00b03981c2c96071307021025100c0c1c0c0004507084c00303024104400040603a009a0322a00c804411100302400b0007004011411621a0310076654181d407541d003400c0c0e003036a0b806c0d054080420031540c155241c901d0004007585c00ba414030000c050050b00841c800d0344500f01542407040c05400f0074500c00c0c44004200110b0342c0041c4038411a070b1140c0042410340d42c0c01014100901a007803400504030308001c1c40318602e001540000d40610320494100c524031090384000501d450a40c866203980d8001442009079144180e91206622904c90001150000e6407400c442c3c10018150402c403607141e034940c000d10981c000c3c00b680c0c01760f03c0e52044040000f0350410717002908011141c800c007000c012200c4005034100009005441d1400d91100301201c14110480c041d202c40c440440d8a8412903290906424 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 628259910 1250 628258660 628258663
    0x8012f03060d060b1804060c1d0f01050309150f01241d060408151f060503061e03010903021e0c011b021f030b04061a030f0a0b0312030a0e 61
    0x1e0051000030710000080641e50b440401826050306400c0d80000351081044611803c60001d80c441c0e44200c2c0c3c00102c28041d10b802030002d914026004401203182c6035081c46580704d5018003209501d00742095916561780e00207152410302e44003855280d2445c03060074031246c0c07401421290b050780d00b0700c1c00300c81101414104452840c1d45130300103400041d01103000c02e042202403101d2600d10f801d003c0d1039545882d440321100c0c2c1c940010343c80110800c84c0b4000401034650000400c0340b80c0310a407556102501d610313003c4024024000901124810710007000300e0300c9000c1c202d818903002850094000e000d0b030983e50070041d4031a8460304134640180d042d0604d4100b04070010a84000740c04050b1240140c004a0900140c02c4110b0650100d0700f01103440c8010b010501001c40b51400380c1a16600403d81e001140107000658007541c2c0000300d1038411095150307542c0350341001d0700d500825902400c605540d80344854409040c551211581500400086a0b0020840c40c021481360b0840c100910020781080b030001e = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 628261160 1250 628259910 628259917
    0x1410150b0304150e0f0a0c05060a17042d0b01060804080f0c0321040507050103060f0e0c0d0920100e0d0f02060f040905010506030103030807050c030d060b09090a050f06010509010908012f 82
    0x61001074003030be000c5086407012040c169041401040c048040340005403d130000c284500b0705104590040b621170104102e2000202d40c00340c4101d2a121500e810982d0b151130180c010110441d546110119042034034610401c00c0e5404c40d64004113032110704080c000802300c0d188081d02e040c1c519005114021407035501070300403101200c42c0200c0c0c0c15004c524040342c0d4000700c0405042c1c14500c2808100c0348000303003224000c483c034043c090a40e8241c1040007a40101d80444078460150164400e1514017528036080040c117101d01030142c3e48104001c1083c9414203800714008002035100801183d038196075030f20032010f00103403011030304108103a9072503204015030750000744001070006520f800003c64240c40f64014190201a0808403810000d001011106461241d00f148181c3c440224400603985825400302d500003c081c041003009007411300c801d04060710006c1a0300c0c14032030300180d1441c0e0b030b074880c412590080a0042c002c01c8003030403003007c5000d0025102088410014103c10000b1030942140c01c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 628262410 1250 628261160 628261177
    0x70b150d050c040c0c062414030309220c020303060a23010f2003071a060d0201110a050f06160f05030406181410150b0304150e0f0a0c0506 61
    0x280142c101200410010f848610760b01c02c10840321a050500150690103691983c0001300f4120002c0031a0304401d441850380c0384d00c020543d05032107484d04440e445c0841142c407280f105542c9a0304076000071403014481003100c5080001280307083c500d0209681d000c00038500031041101c0000840780d0316682401e1014885014200703c0c2e081210a440c1c40d07001d048407020803149428070001c203000a042148400e40306d00100103280e00001124001c021292a0003421211701d40c0004119003407280108031644603000009042c800c6000150318207480400c448400b003540b00c0129045071300344228031600e0b52001c0c0e403500c407102c0490461015070b42c00307003c0d501c0c07107038505d5511030f0b04603070b03a548400e0040c0c08410140180e600007441d0500c0801c902c1c0160001442e02c2c000184103c441840c00b040c200c4030315429200c2000d40401d820b02031307c60100100da401ca03170400148102020070000c06002040c03c540d0800c0b9500c60007280c084002030101d03201480a01410f400e00c038040d6108288881032003446038 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 628263660 1250 628262410 628262413
    0xb040501080706091421030702040b04060b0912011b030e07060929041d060909061608041a0403170121030c0f05061f091b05030a0b06070b150d05 64
    0x40c20701038105c840c0101c00d00e07880c0080003525480424942e501c0190090203544000f40c0000941d1403d40c203150080900745c1e03509482c00c10035645001c1c000e0700755001e10541a441034001c809070200c20307442500311070a044102c01284115012541000d8010b0610314a00d604a018400d400a0070600840b040421a0403682000850507030300b20340041b2503242c4a0414600c070409000104113002c19040c5450490356500a8003064105001000100e4000034100740b819880002008030120080d1540c0720141e505080078aa1034440349047d541084400d000400380511301410081410ba205803004074544e41039010000a9032502d06240c4121100d00040c080c40b420310080c000028130680c03508201c1c0d80902c0781c15410200c255a00e60500e40e003600c40c003040d0141d11301c1c03401ca9581003c10306c400800714044100000c01c60360380c1e41802060b03640c1492050220100004040b543d09421450300584000c0500d6900da80c20300c0c2c01212040207070348a80c0051005000002141800210412074940000 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 628264910 1250 628263660 628263677
    0x50904020d02091801050411040b040e070b1b1605100c0f030e060d0c05040f08010b100e030312010803070606170c130b0901030f060e0a0b370b040501080706 69
    0x1000d000e0344070300141c40d13540c00301c40035451200d0651082c80389034043d038420308000304c0c0308c42028108825100000d03203d80c40303907262028843d090580080d000044070f0f2400f070755135200c0402803825040e051300507844a110b400703081e641c1789149089586040680e441126110303154098400300308c43d001c1305440300504c840e0313007809a4804603004d00f00102091000a10a83c0b50098240b0000c0683c1c80c0c401084002c1400842c0034070030419119000c0c2c2c09002d00200810912128000040421510450501c11b200911800a903280c4041c400c03030300c00d45103602c030341d540070b50b500e00415a0f03d44c841c0c01c0950b81c0d14649540810404c941e80514800d41c5610801001c16810910400110314602c40000c43c00d15581d04000d110358482c03450080c0298019501d040340c2d04030324100041525110910940703160444a00b110024907516580c58114001d100118100b401100e0b102c0e0f5141d50a078101244c07120b40710300c0c0c2d100041130307070700442810001a42d00380041d980c0c64150b9641d0380d000380103c5020480b6030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 628266160 1250 628264910 628264913
    0x30f041d01150e040b060c010b010e010f210e0303010f212a0f0305060a150515130b04090516020c01020d03180206040b030403030c05130e04031715010207050904020d 73
    0x49245820f80c1d2001440012088186000240164000d00502065945421180d1550340c0c1021042c24252000e007002d16500980746801030002000190010380c6029031801d88603000200c0d03100d201e80c0c07001e10084039501d58492070000024040d92180c101490035255003800d0041010382140401c66020352028243e001008201d0001002ca074031419100c130142d0000550420020507480086010700083c241c01e09044c01100c00382c9165108154140185100400c641d0700c0390803041104403000603006464143e49400c0d080c1d01121503100b0819100d011401140c150440d07401103020f002e05a08081d03807840c41400c00e07a1100e0050681e41d0158010700c80954455000f50404c0a0120120b0b00c41120007100d940002c11640054004c10701c250008410882010303014482c84220350781354248075050a11040343e25400d000c1c94000c1d000c0c8100600d011404150080d01080031110f103000300d180d50b5140080004c6205005030240d9401403144030000100c40c00c01079051030149802500c01d000b0003609 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 628267410 1250 628266160 628266167
    0x41e0e06090a09151a040501031a0903042301020c030610360b01020f0a0b0103061d06040321060b0409020703050c0a0b0411061c0c03020c030f041d0115 67
    0x6041da000c00e0b4603001004001030f1400104075010141440c0000d17102d1001042c0c148195442c58218069032a060060001c2890302c08581104c880828a4030000d1b5200000d150031405541d004a0800d811884440742040d02c00400a0f560300003070342155081144901050369a5100382e074501c862064200083c420b078411060340c00001c00090403078404454440248584482d16101401e1007281e84040707a12440d81e041c000b60340c118064000418121000b0f4a500b24003070030600c0700508440d91081c1d950041d40442c120b4141c881c07009070a641c078a00d040d060107003d038848401d00c1b44003040290000300d039003510340c030481094a401d003140b5410300d81461035090095001810a5041c813500f0700886003020707010802d00340503900c546a0110300341810b141400c8140410b890039446110f0601010412a00e11444c500749251482004189007821a8050300203101d0384000341c44500002500d00f10304da41010003001101c0c80000016008030501c170111104420a0003007100070000000c018410038413 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 628268660 1250 628267410 628267429
    0x1050c0708151e06040b030307050327120607030b0a051c350a0c0803100317030708040201120e03072609030709090204060504050109050a141509041103060408041e0e06 74
    0x1b02900720791400c0080d0b11a40e145030426801c4089104101213084070b00c110030310b01c87c51910002e440c156040184902c0168850000902203400c0555489080c10070f40e442c0140e90000b0030000d8050b50041138200d0b17a050303c075003407154180d440e1007441150300110643c7d00880b101d102e5070000d50903803500300318410001650103c05c5810030815450112004100490021030260080e003441e409080d140d49480f07001e104800742900c8001030284204808160450b500c81c0e4800e43c2440c080004101401c42e103001040706243e010780300d1101141d241c003001000407800c0600011060320311741202e4400811a240c0c411225507680503009460200701000194010308090761004001041b01c0b0f0f101d4003c00c040b074809038002d045181d01c910138000d1001c5584920120b030300e0344403035540c81f500d030040303019103d41d0300031848038019101000020706101745541c60b4140d0710350080c1551014205810121041d4102c0d0140103215151645c400503483c2c01140e6090850351319149038600d6990b4001003045841 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 628269910 1250 628268660 628268681
    0x90e04080706020f0c1b060711120105070f02011d0316031202310506041208040e0711070608010e0403080a0f0e0709060f0e06060901050c0708151e0604 67
    0x241844028000b6074540050701070014007002003515640380c44050340c0fa0040c4e5807070900002e0702d10400480d507a16070000321074034150007004400604030310a001c2a01c0c2010441c00512a51070a424000601da1002c0c0d40d81e017011142e40203121960b0805102e0f81d1040070700100a0071035004000d052442d050417081e40c8217040c0030f4206850300031500d0f00000e0503684041c2006a64070208410050358070b0400720790441c403010b0410540e0056003800017107060303441140240441030b0a00401d5800300050b4000720b8001e00812880401035007004d01000d00b039a441c0c1050b010043c001c903580851100c0c17140341402e04850301e110b135441054580d510b00340c418000c09040c4c041031644910303040c401e405541c00754240c40c0c0c3e100402407407407a240c0f412842c200c1d040354100190417072499504204010000b0601c2d60062011a00d02e9070303030362407040141c1e03151040061001c51030044000004030080c1c08150070a001400140140782650383c0c0c0744101105e07003a40740c0034542640f0840440c2d850305007a8840c14206 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 628271160 1250 628269910 628269923
    0x7170f0f180604080405121c120b03071403010506060c280b07090312020a0c0504022101030501020408120c0307170c01150f15050a05030403030f090503030402041b090e04 75
    0x10750088001c0d0900308226415a04058006404c1150341030580550441c10741c14005042c51412a030944c41d0b0140c42c600c0c01c20100110380c2c1c840109a9410b43c002c0d440740310010201c900d403594813007a4900c000d052811441c865441e04000494034281a81118400c2008901a0504000203101c1e00384400711014203c04e0808a94003d00c0010b041440701d6010351650340f01c00d25014554a44560f00d0164282c512086401c8100240001118601d01c8811b58100725030146c2c84039520940e411440d200c00d01e40030388409501d030000090000641c005d00580d100d132030a90f0380c0003480c0141f501d2640f2491240710581d40c030401060011480007042003041c0003000420914103890304a0617401d594540d0001401a841003100b0042000151440002805c0030502d103101c0c0301a84002900a02a5100300c4050150000010f001c0500c030740d104000c01a0b404000304410181c3e424090399035081260100c1c055031624502020305189128400e880102580d120a038250920304d00b0f6150b200090000c8465 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 628272410 1250 628271160 628271191
    0x207050a060e01090b010e0901060602010e1005190c0504170109020d0f05100c0e0a1509031203091a0910150504020901030209091e070f090603050c2107170f0f 70
    0x24140d1100318000c0014413011f001c541002d03c07803a030869105030b12420a680c900500850062400300f17044000d40e00f010f4001420b0368800714000403503044040505096841e1910150282c2d8100000d0002d486c02c0306d901200c00f00380128418229080311801940c4070888440e14400140b80340d00003600300d40300f0000d9a0500a0b404c040409540c8001c098102180c145501e94a1909010a8160090040c200c0402c100e0090070b0000d40141d8541c08007a040e0600c0c0c060721000e2502a80041c00866440307820060742c41482c00c15003541000c1540c1e01d0742940100c0c079103071135154854000ca1469050350841e084006140c41c08020003940a003040a05054003488203d03c15900c010031944190704095102d500311540c000804018203009100c0703010312581220607249241c4c0401c4032010b450040c24001920340307503201840064001c1050700a0541030b80e20415002680030f99809010310820380f90040c0c10310400300c20300d5000100b02c0e810100010310b900000d001500000c4450380016090810209 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 628273660 1250 628272410 628272413
    0x8060712020c010b190518131b120303050132010516140109121b120e041a100e1f0512010305030703020610380c0601180207050a060e0109 61
    0x441c140d035089417115110280b48200045d0510342640a000000c1312200301c2c03a0b1900128031214691350101c0a000280000c60700e14009150740c108502a1007203180c01c40c082552460005c01030007090094851401049200c0d0520704080a1503c0d85411007c492244400000004440540280e0b000f1116005070414000c0498102c15003410340500c02e13030020440d00c6041c106255411440c6100d40d04111142201c450404140305810401c00c0e44590103880341c410341d00088500300b82074010035902629240c150040802143d00708490343c0019a403050416a011713805a40708141d04100c1a0010320344042d00880302552139014919401c0d900740103050072008501c0300030000e0240c2044806a20018404040c144c040003c079a04c0380d40c000b80c42c4612810640517070020b10b0b10792211b480c0418402c5e010b00003404903264040c044d00150f64450b4440e0f07000010165504402c1c411030b00380748500c2284500d61201c1d07008540010350020010071500d89240c0c0e4250080c00508003900c81c1c0d5598049210 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 628274910 1250 628273660 628273669
    0x809130614010c060f11070b0907031e02150307020610050f060f13031b0e220605090f010c03060e100b0915040306020307080a18031d0604090603080c0708060712020c010b 75
    0x101034a1403040087d01d41643d480c24044841001e00085495031140c002040001c110041071015100702c1d1340c0510000f00c891000c42c1ca154170381e1040038074803803003c010091803590000e5214410020403066403000ca5880c0c2c00d00c440d5090300700e102c60704001c00300404013548403050002d1070181c400f8400c00c0e0181e40d4035200c203c003075075034650074640c1103a114000b00020350944003019000044044966424441d103403601c0c42c401d4501b000100100e4590002401e100b005014410a00c40c40b02c0c0203000146a0100080082a003401403c2480f0090004500d0021002210340c041c4c80c00c08001f82c1c600203610f01001031030112510750b5900003c00b04401300c00281c890001c1c500070059600d80008c1030030409540815aa14004c032200c0d280151000140403a0344241d19000c000c100030b4a141d0050340200104034107116542110711007504260000080164400c010b00e505c082c01030581e0301035610f4009079612260240d03080000994050415508070890350f0040100c2003a1800010300d0414600104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 628276160 1250 628274910 628274921
    0xc0503060903030f15010c0f050c04051006030e120901080408040801020a1223220501020318120c06070f0306030b0f04050c0414041401180809130614010c060f 70
    0x8001e0741c1000c002c1c0710f40070414603905034002c44400e119142544221000900c81c2c40042406451a4540500b200078804140510075803842d01070800c0c03001e4585040100481407091007104002842c01d43d08450859001c2441c4200b0303015114118a0440288011510680c0260046d00c0700a030800000440540910051800381869155514007402ca2074020003210003902c0c0c0c251800343c0d14100000720040d01a1000d9001d20301c258000030405440000c0b03c800351082c030004110b984008103010100441e1100b0034a521020390846000000d81c8041c42c15900070281d045205502c0358011410450050400350103a46292500282155880d104e010b0034082c02d445c0d0b0304490000c44107000500006021ba00780241c0240c0b800e20208502a422010b071590050003d40072170012140d1f81d200e58000c0d00500040701080800780b03035905d56818010481e40c0300b01d0215100d1406ca1418a40c401510301030381080314942d000d6072144011003c0103450845280104a900c00d81c0d41c07940380c100c4072551250 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 628277410 1250 628276160 628276171
    0x412031e0c0224041b0801020c0703050d110601060c0f29070503010815040c0b12100509010f12020f03010c120e010b10050f1e0d050a060501080a02070c050306 70
    0x401c11180c5404081d0034140d045840d0140348082a441480700024424296002948501d010100d2840d0140007950b512650300800e16550000501403485000000c280043d43e004105545141c014040e083d900d4002d00083c1d817100d504240c00422a00d4094510194001c2c000d2480031200013895468500448002041c0c01240340030584548088491040d0203906c40c1d040d050940c0385504113010141d682420003080750780c85440d070001500b0000c0f1450a00028941800f2554541e0034020f00c0c0101d203c0c081315000126000000006004c4c927180007407904031131414195520702d42c00d260f0454103040c00c2580582e00800152000c0172a901c2c24480c69005404e10769030042c3c0f060706d031410b0809032010704001d40708680c10100d01122582d144600304490f6400c40c20825981e05070f09060714040d000d6100d0f54044501d040e550340300080b01240041810361100c0d041013010303944080c2c188048801d0b40c05924001401c0e0340c0041c2000038240d00a1003200d0243d03d908034100d07a00c400091030131804440 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 628278660 1250 628277410 628277471
    0x1a07110d06201908040302250b030f0105010f02191e0c06020106092910210204140103020307090b031503190b2a1e03250504030209041203 61
    0x49581c1031601c000f10980310014149800e850500307213914000d5035003141c03074000003024121802a1000c01040001103000780f0140b405562280703011003007170009107000d108580c086520101c90950451000c100d081ca00030f081844030036510680d89850300d03480800e903a811103124801c8209030102e1260600f9000400c0c603680007144160916040c038040c1e49040c0c08500b400600003404514540b060300080703001c0c003401c0c4c603a481500b05d41a000c40b200d4400c0000d80b0780c407100e4138600f040e01c005250014010b03241ca8000f44041c5116120044040348001c440344000a10701140900626508034000c5801c58030119200040300c0c1c802d000203042154892514000d103104d00740f4203080000c10b814003544121440716000ba980101d00c1201a1010300c2c01c00e448507130b24001010083d402190503a40c0122454600050b1039141007a035100d0310000710798500791072501482c0c140044510400440d030690764050055402601d0310b984249010303841418120900d6160010404c0d070101c544c0e0068581c410004 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 628279910 1250 628278660 628278667
    0x50408160503190b06100c0b0114090f04050303061302041a030f011517060418031709061308070611031e01092009040902191a07110d0620 61
    0x3020586810314400b0f00d070207040111440d40001c21803040c13101d0350060702628008002456100c00716035845200b1001007001c840b403800410542e14824050400071020b45500000e6203540d580c01c40402d5007220300510355401000001d106e41084800c4040300c1282040c0581031544131801106501c1802c030840ea84a035002c0104010100b495030000e00600c40010802121034111a00401080001074000d90180508002c240707540c8030f81d0f100c11505a0031210704555044540b400070a004021241000d07011581400300f4500c0c140031442c180034401070411200e40480710399490041b0b4101141c1134035656a41d1815150848c100b0006600c141510100040e041d10801403000c140941030308407280d0641b800d01c04510040f010071400c0717001d491b02511541c460150b14001005005080343c02900200c04800c034100204800c000001503d12048660780b017504e07100b050740314034010f0071360141600100c0c9200039028240084030f0407400b4050380c40031508100d4000300f10b20754080340e410f80349000c8000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 628281160 1250 628279910 628279919
    0xa09170a030e0c12030304030f0c05060a0507080610081602100e0c15120c1b0106030b10140d02091008010218090105041503060b060d1503031b0c090c05040816 70
    0x1405038207103040f0102c400f50408807100c21529540d0000610042c24064441c00284c40540204007a43c40c035039000003241c21515141e154040a80702c01d94151003c2207030b64000c100300e441c0c400b1100e0910a50340e13481007031a6032510b0901c24000d401030100d1041d4050250a07400504c1c241c010b00c5041c1e60000011700203207002c5000e000d00030207881e080d8400c5110030300901030446404000250000b804c0b40c4110313190710b80c1c8144005040c1c01401104441e61030058004204020048002e1159040b900045461a036031404a07a41100c01000144d02c043d007403d003400180f610006054000c102c41640280d11621844a642203034811103441c45001c1c103890b17603945103180595a841c003401c0c0c1603c0c14003400580a0b000241038a6070f02000f00303c161201c100c549252145410303920b00946c10b176000d1040c4802d002c1d8085c1d480c504c5020a4001590702e6910341130b14103000003246c4070554008407440741789103000450401403c5180804e02009401c107c001362020341049203151076060a041e001b01e640c0703031 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 628282410 1250 628281160 628281163
    0x3c04050105010302010e0102150115140a030b0118120803040302070e040b16050c0d0f0e0d060203060a080601260a0c030605180105092503020409120f05030f0a09170a030e 75
    0x441000d2411540800824081b0000128405044a61188be10320390042c0b80601512558090001201c54030030105401c800946d01d40c0001821903000e0721000e81c218443c4c01901c418a1580c0201d0f90340303070002011000011419001158041d001e4410f84250b0754643c0454002407100f550280c9040c00702c001030010401620001c80006011401c02c00c0c503041107181001e488640340b442c03010521141c041c641c441240545040003110100034948480042c40e45030180003904103944150081c1c8020368007042078000060a181070300c041080c54401c2c0b40a01240f110f0034a40780403000850b004030b0310b29800051400030704801543c442c07400482d40c0e1800c003070611901982102060866810701c002d00038000340100b41c8030038a414094900c0100c0c01c0c0c1c41d0b81c02c110130a65500c02908507140c0514a81403202e00345d0000900e194940c0d031150041400182160f0500041e02c41d0803501414402049080400b80e0240e20260b100708000f01000d9000d244045c0c654001000d400c02194a440d03a14614810 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 628283660 1250 628282410 628282427
    0xf13021b10090308060d0f0507180e032a0f060f0601080709060e011202091513080106030c140d06290105030c120c0d020406020a02183c0405010501030201 68
    0x3031212007000044840c3e10300501d140c030702802141c014680444207506011912540c3c0c41015005400c80b01e54564440300c0e01c042d220040a809081440c03d09040d4903511301104580b01e000c0404640b690303141c0c01c014181700c4c100e01d0b02c402800d02d206010070140a4001409a148201488009030b4014501907001520244000700755004000b0300100a001041d041034407450410002c0c41c00201d0f44d0a00c0b070307040d0004e110f02e0300810b5212801142030703403a0001c080000c00120b4401d034400b0500c19603a0320800d003614454000204040080c0b1018030190a0743c034012600d068006000c40d20100e01521080101c404a160000325040c1765110882100a611040c0461440a20b4000e1440c50440e0034580030740500302c0290030084078040426042c000550036a00090031040c400c6503115503900000e5070361140306a08130301403019032020075101d124104404d4400d1340b0200c0302e0036045200b4007680c0c0d00150b0750103108500c010751208032008030a5005c03030140300d244101c000186030750450001404803003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 628284910 1250 628283660 628283683
    0xa05060708040b06060901080103150207060e030403141b19030602070b0603070609030f08030a06080709050f0609130b060a0b0f03100b0304031e0210050906270c0f13021b 75
    0x45c02c201c003000991b800015141126040098500c1c201900541000a0300ca9020050402030420400103144a4044010710031070f8401c1910b01c003041e840c01e4100c3d0f01d980703c0901c02c0706450205542c0010b075007446490750121100c4454012030082d01d9903148400c0340c2200e0415907001c81204e0402c0343d00c3c24200400b102030305c0981003110409255035039007001c250300624000c3c50740c40040040390f0780502c550070941c050881d1606070ba01c1117880c0e07515007004000889620b181e021990b00403812a003060200180103100505c0f035400d03142801c0d1a0282c0308240509850f030889141d24001400468050142c100d8100500c1c01075034074140a0a0350141c030900d6000f042d46d200007002070000080c0c1244100300020604104015000f41140c02682011f8960044c4214035040004011882c00f001c00c1c120700c42c0780302c50509030045000d1110400c7c11181540d00c609280e0003030101c0e00c1c092034801d256546902004140d020301068030702088050342c0103449100078490900c40b9804000000740801c10118 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 628286160 1250 628284910 628284919
    0x60b04060509181315020909010303020d0801060813120908030d150b030126010b03100501060810230303090307030303050915060603011203030f1b09090204080d050307020a05060708040b06 83
    0x141841d0b440d00400580c0c4044c02400811440c1c1750f010b001110b90151a000040186080b259607520b05002c0e49442d0b0981c0702c440021103401c00824184e014030f101500410031003480012101c0f00740c2e60006035103400c2e2010024484c00c0c040c0011014002c00041c00340010b50640892641440020440384804030b81045060000c140014040c25200e501e1000704000d03e014068a0401c030300f03590340d0041c101c07a10380d581c260242da202c054525103140c0140f41220010b0382c0d00d00b100da441b5410542d020f2a14003801200c00c070207000b81d441c0c0c40120b40348601c8100c4014240c91030110300d43c0000340341004590046001c02d880710100010410240300192040300407603d01c1c001031511400050141c403050280100f203010903074001e024107120354003000110300141020042d400e815428010252140107000707000644804d0081a400018000e0f0307400c84c3c0310b04004100450aa030310956058200801d403070214850501814040340c801c00c22940075400c141c4490328203082c0f5081407100c8150050466025 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 628287410 1250 628286160 628286209
    0x414010c05280504090c051c1b0818190506101a070f080c01060905070302070305070f02060c100f06090209010c1b12050303010806100e0c070204060b04060509 70
    0x4510000c40c600c01e41c0321010000c0b80940e070241c1c040e00c16002d40d03000000003625110700095460f80000c0101031803e40b490342031041180581c6568141c03030b105d480141d96400507620000450340a24101904541c43d000c614050601f60740c0d0307462074021104a4200010a01c490520902c40d0921085401ca0303000d42045200f0f45c141100707070755114550721240c440d41c40001101014400d401c5a40700d525588142030a44e41c4040015880c0038040901032a49000d14142c04900500d00074802c0300d1015901d80c40e1503003805820b0312411004d0300718030000c0c0d820504c10400710108601c10300c00340c2c44003c821100000d038040a419243d0031240160000f86119204001c40020360381c05c108041203060340080200e81c9500b00c006640341d80700341948404460854241070300d08020000c000340d416144003104442159848a01800007000c15108507a00480040c0105804090000c01042c0c4c2c140050000709505a6902460300d60364030075400100005c2e03000c03502c40c0107450080441c900c1c0070385001c0030400 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 628288660 1250 628287410 628287427
    0xf070f0c0f030b1305210901030b041e020304020d1a010f08031309020901090305070b12060406030b04080d1e0912080705041514040602010b01080f040f020d0f0b0414010c05 76
    0x140818041c11501c14516244e044000b008402c0201d000400b00070b600710300c0c10902d09046442640c0003500218042820603040902506080c868000b43c0d00e0003004618001126800450095001500036600240d141c5800c20104105440042645040610190700d640c54200020003800f150f40200c052354004106103444040602c1d1210f0990b901e01c2801a43c5000714401a41d52062650004286025044002515450100290122800041040140d03503210740c20081140c1d40760000030700030044003000c180815940c030050b1021000b0310710f0025805413601c1118600940c2190404c3d1843c0d124041c2e02c2c108045080e529006882c18181108182003a040281640c0114041e4440d481900704003014800d00c1160690411007080302a01d940e141c40307004c02401382c40360030013050200308500040b424003c3c80400091141c0e8001c0120f800007640c0fa4200b00765608484400c0d00c484060740b8074000400d044c44601b601441c8203001018491b000003d0143c02e50303003a04004002d011b0144031111 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 628289910 1250 628288660 628288673
    0x70614010f0602030f121810020c070605032e030c030f17070506060118030204060b0a0f020f0c0925080109150f0b0904140708040510050103150e030f070f0c0f03 71
    0x100030744010303036480480d95180130541f582001032103420030107803040908082c0001e101d5401813603c2a00300007595219038591070b080e0341900c4141c4101c650402c4121020502d40394100c9103510844610005080c12030307072521000c4184500b03402c1552200b103600011020854aa160f00800c44900348130079040c003e96440d41c1d910741000615103814400141a111400510b690500b07001c1c5a00070700030841652140e00c50642908451078090106502103410104540006480740c200d44408004009685400cc24050002c0300a080d5200d089001d440c261042030f4000d03003241d50410f003651259903a41c581051002a5142c54488907800c0c0007000b0b007400f242d990507002e5016100a40c0645aa42c0e02910200d40204041c5888026010f41c1d1404d00600b6a4001c1072680183e003d802101e400980400c3d0040407680280300090000b4440d1a00c001301a0071500170300c00300885481902c0c24030803148001a41948124030448070040c0d0300b910b032401c2040300311310080170381004440c402465095658070b5 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 628291160 1250 628289910 628289917
    0x20f07080c010810270612030203030f0c0403052a0a0320010509030705012703030c110402180405040501060f0807030c0902040b07241d06152103070614010f0602030f 73
    0x3603e90000e03172110f00040c07441d0700240300501240008141d088030310b040084d02e0340c205450f8940c212106a01280c48404054107880580e41c014020b00142100d80c000c9040742401d03040742c0000244051220b5080740e5503c0300200045028403211001520000303035410300d841074005841d0500c00103108401c1c0e1600c0019504060300c0007070803c0b0701000c2c276801c0009866020710142c000d03e034000040c0801015403208169980d1486041001c09451112003040240d008200c0000c80d4205001500c8009251035041a0340240c002c0d40001012515210003101400c0c86401c020b41960084004104200003030800b880181461803045082ca400c03c1c001900b10310448002405011400b002455564030781550b8000060042c5000c0210000060071920101c2c2d4050401c151800f481000891001a19140c0c80382540000c200d056030010704c00f050100e1108a41e001c1901744428001031000032040d00c00c0c1c24101d01c090000305440d41c54808491716040442e04484215081401100c1d04c01942c20180d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 628292410 1250 628291160 628291199
    0x260408010e16091806090c1d13060b0609130b19140103150b030106030902040e1605061c0509010506240a120e1525021c020f07080c010810 61
    0x100f070313003510407410710f035a0300ba01400034110510f04140b0804214118040c081143c2280c04041d540326490b908090248d07030b0481e0900b102030072020f41c000c000f54441e407103150004d070001c052509001024004c200501d0070030f0440005183c1e104d401c800d1524292418581048002c035003000d480341014502c201091046110f00c0c14540c4071560602c05018000c0204081d1402007000e44e00d82d81e4819004000d400c640f1400e900540c80c0240c0c002c3c1c4403101042e00780c40d0a401c80900642c144c82c00b028003a0030380c005c6444441c2130801c07074002e5110318550b014041c000c5000c1000400c45040c803f0802045080c2121810202c0e02c8880e0320700e042c0303807140c010303240c2514690030003440460380ca00382c0a010707220305010908030307015100000c100f1407030161609000d0004030300070301149a20780749486200070701c04c0c0041000d640422801d0800310175511a038050801e0030320503100360b03040c0170501303e00e41078581d009103280da04080b0a0707030300550303002d00c51039841500500800001c2e0303e0301c21845080f81d4000322 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 628293660 1250 628292410 628292429
    0x60702010530090703051e0309061204110402070503030609150d03020a0516061202070c03081c0b040c020a08090d020306040b04150501050105070303090c0f060c02030c030c010e060304260408010e16 87
    0x703600000e44014401d850400340d02520ac0c3d42d64103c03003224401491403c4904841900c03007001610800d09151094951296020005515603140d0404020704e00b200200318000013a5045188130082d00c03200c1e40c0e411520b10a8004143c0d504162401c0e9052510007141d215003220320840400400d9800584400c1890624070010303a5101e0600300007c1d0030b6505c5e00060a0030b200040e94600311003008585241200302d540e002c0128001c3c10f4200020b8507510380940c801070b40803d1620000c0740206009044d042c400034100143d4200d00d5000c01c8c03d02d40212000c0c4d030505440403c1106001030141000b1940c7c58101d020407a56041030006010f034040c2c0c0130040c0425a40355020b42c00c0083d880e000c4070150040c0d420703242d4241d80c2c5010041001d016184201e0082c010404801680e04000504140c0300c0416110342003107510b018180102600300520035103d031020b480e210b01c40d800a0703090011129803c084207070b0741c541c1080500c1d804c3d40e259405001d00c40d800009072028044000c0c42e48e0050341c84204 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 628294910 1250 628293660 628293703
    0x17070b090d1e020a03030504080d09051f18080307140601030c03080a170114010e060c060a18080a05180306041101050c3903060f0606070201053009070305 68
    0x2680110403450800075001089104d003c03043c1a008030151046074407401c2165200d2880f04001c03a044a003511600307400c610041c3d04814240d41080055460300514035140700b001071fa4a881c055102072030342c040c13884d40c0c00025485040c0840030a0950089a600004002030b500d140e981005600b0684005041001d020840f0894244681c03191581840c1c551400d0145503152000742201c404003081036800706500d80e52401050800c40141c4440c81040030203400240d861070035600c058941946134201003c020680c3e040090341c048081c00f80941300c1d5a609031101c40d080d21141d82c0a00502c000707442540803108110001e0210504940300103000c1c608580c4a00010741c1e804d1900c185800b00070520100c403000c0420644185190301000c0b102c07400d81c809a10382900038036440d0a0190b0383c04618054000001e80c25003052401440e80c00d1041c0740191411110319221700d5910003d40802070343c8a010044d52030f1004643d06100e40008100c0081d00c0d000703182d6602c042c0c2e170b0441c828801c252441c1c03a0 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 628296160 1250 628294910 628294943
    0x103060b010c060509010c1211090f01030b030a0506041104092613080c03011505090106030b0f0402030a050a0e03180423010e160f0e0108040c0504020417070b090d 72
    0x321070b1208416403250301441a8188a06000d019001d401c081c200016444c24010391500032034041c0c16588400c5000d074078940541c503000d02482101d40a2651305154607404c1c0d600180d01c0401042c903503179000303502a02c01e03402c00b85480c1c0440c0000100f01841581401840404034950240b1b640d0b1600c8480e03401c13540032903c0b1030140c816024200c001e4200e0b05020308000b46000c0d02042602e9603501c124003c010030120303a00b180340305995a00030f00f900804000c0c01401441d010703a02031483d1072030060503901c3d4050107000040580c0c0c802c40f05140519250710078442040f08a01805070107230f01c0b0802039401c1201a0101c80c026801c0819100d200d00d440c2c0000c7e4446900c2c0740c00880d1000340c0316001d0041036071101e00c4411070100503104203c6440c50f880c6030314030140c89001c4041d440142d0f591030300384110840c00115000c11024100b81c031500d80c2004006420750300e6100800c01480f203101202c4514003103541c880c0c01d160043d0710010400008100c050015a01d480a0b0000030743c0c0044c502c000e58010 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 628297410 1250 628296160 628296167
    0x1050402180a0b0d0b09091905120f180f0f0f040b040903050c060114060a120e0d0e01030f050621030c0a030822050d0e120a1202070b0301030b0103060b01 68
    0x201c100003508090040c1c0c0c00300c0c0312420400207040c490f00c15041440b124040c8018017640443c1250513200c180c020759803018200310481d0800d01d4690040d01114000300310301440c1c2480d5400300b02004800c00d00041c401c3c1098450780c1d0b404010400031558102c0f5265280041400c1120103019180705e020700b0480314071160b0300c551050824180250040002c881c0311301e0060407603408a602d4030f03080c0c8a18400020b0361848024a0060b01401800e41810710b01800011344412451401c100601610f0300c240b4000d09008002c2c100804c0f120380d07184a8500440c00014045519140350203e121b81001c4c100b2401e03444003010480010103080c1c80c2c0400d0080d813031495096000c0c0c04015001030003109021010306901041c000d0040c0090380249000c0d8940c44000081c401c1100d100500039080600d421200a0040b04480c0c0940409406030190100310303900c0d01d0602000c0341e8112108041303600a0502168104014006046002d42c0301d40b842d41583c85a24040d401403100074481e07a19a0b03003d0540364417 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 628298660 1250 628297410 628297447
    0x100507050c030706060521030403030516020d030905040c030e03090d02010c051005060a05180f060a0b0406031505010c1a0406110c0a02030c010203390a050714030a080301050402 78
    0x5910140c2c0e40300c0600d4507200c005000140f040521508005e505900c680d82020350074040c0b413031860010342c035052541d038081e00d40350030011000c1c01c0744140898060143e111201c61204051180d5600c10722281000308002c01c443c03100240000b050310344003086081503400002c07101c10441c01c4038565a400d62510049603164010700c80242140100028610301c0070f4541c0005001da1400c4840c0c1c20529114400c0c040d2003400800d03412440f0080001041003261000401e07500142c010740350b80e15140d160280d01c0050340c041e603c1000000e603198507040061494a2084000d40001d20300a51310303000548529924111740205110040c06c40c5010a0030002c2e50350000d051651483c0c082c5845044841c05c0680320342c90008168040c1c00307940f148041d5980301008645942401000340740714072421b40c4138601c071030110364800f201c040040305180d001c44100300004103025104400034061142080c241d6148070305003107107140c0a43d1110480e440001c40b64802d50b1705440040d20300585403c203610038400000f4 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 628299910 1250 628298660 628298677
    0x1d1c060f0e0703030306050f0a05090a0b060a0e0109120b01030b0702101802103f050906044d0a140f0f03030a0318050d0315060804030210050705 64
    0x749020003454034a03002141441c1140d0007524100485640e4400f071003040e21580c015158090340c510010b019501e03011600c1500108a010000341020500d00031501c99484000148007180044420b14111b6070700c1782c0c140001d00081d5209070308004e42540c80303000c9400306003c0209200c1d00b000c009862603200300002c03503002013022030502401618400300d40e00c10b61381c0c030400c1e406407040b0442014640c7c0110054048007254000c2140368108010030000c500c2107414041c10400352a00110741543c40740c0c064140070301b8080000c1c1496040c00e1800303003920918007151031502000001b031f01c00c404005414100119145403d1002c1c41420109500c40c0080c2e0000c0c05640148074610203e00012180701c81ca0382c81d03000340c514078211002102040201c2007a05140c990640c002c116900c0703181d210b81c12000600202400303850442045540340c9041050540450001030350301c0030444905035940d101c1e88020011400c00e002d0504103614000d44440e1181d40010bd02600c070400300f1000c9100720120360144 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 628301160 1250 628299910 628299941
    0x318010e030f160f0b090108160c231c020a111f09140f030a020d0f170901030b040225050304080a0605090606190e0c0405100309031d1c06 61
    0x2801d50301000c0c07401c0802030103416413090140c00c1c04607007044003108580750020143c4600f015550345440394080da0100c000c400041000060f021000284040e04050350b5695120700c92a00c14005c1e107503e4603040000c0310781500c15280e500001c2c481d58020a10202d026001241aa5007948040228102c040d003414907214a540521452251651000c592005e0b00d14500f82c0c0d0a0030031070f480c02c121f8020010f032100c1c2c1d41a00840001c400600e41442110010341c800d007614140b0160303e8135000b0301e03298045040c0e01030340b00000d00400c656a1611480881d5401180d0450030700e0604103d1340c0b64192125915000e2a07000e89a0780d0034450108181c800504000307040f11700c0308a984c50160050030090350500101d10814011079510714058080c44420302d400b00041405a20f800707128641428086c000500d00c1004003c085180c0d15440c4130041d130403030325440c0440c4035403842c41d0040140c1103000702b070500380d00f05d00d484004607a00c8903c41034504080c150403038000d01442c14040002c0407900600540b0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 628302410 1250 628301160 628301173
    0x417040b0a02060405060901111b070e0916061b06050703060504020a03020d05090a030c0305032503050906061509040f0b1f11030309061b090a0308030a0e0318010e030f 74
    0x441c0d40021440c1c41948204291b0340703d80c490985c000d003651100000c80c4242042032000c2d050480e4800c0802c050b019134402141e0415607600c80b5440060340c10394042d501031300088180e01d40074052401da60002c007045d00e007044021200300d03840b202110a1280017890241c4890204100d203110b508290050000108210f544001044001d402035014070119201d00742040c0c000342c040400801c0464020384c040e16080200c2810356011550b5a0000b8450680000c049440010803440b414500e4040c0d401910001414203040c00440d24010005280e18403908000140d02c3ca403071091170540740d922500740c4000c10901c000301c03104009000c1c00310500d90040c10084802c00c803103d41d141102c29900c0c103500c2e04202c00d440d09450036120b2204442e0070040d0741c000008583d040060100c0c030001d24281c0562941012500d41c0040c1103412941c0c4183c9001a0101c103200c1148c11900c600d0b00c990170304200541ca070000c071607241c290010580c50001c0c180210501e24100503241480b00c500711129400c142c900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 628303660 1250 628302410 628302427
    0x4090f02030d0513080604020d060b010219050601030c0b09030c090a090204050f100e070e0d020a03061415060403051b2407120e1c02040f1104090c03020a080417040b 73
    0x180c1004012000c00201e00030700151700080859018003841d0094084400483c80303441f1131000d0040b01c0c00c261304521030260700ca20800c9520440c01c007001e110782c010b0900b95145040410b200c451581002c2075650007008100d03619036002603045003140f0152000d8480342c0e01d00d2680e40c0207001e070300f0010b03401500741003c104130100304081c80c51089840b841c14818150321001d80d0744d0342c55402c9451030085100303010580b20780e20300311480c1c3c561188000d0070102e02c1070700d0b607480d403081c0c80840b92810205848038090103040420707560001113041080d10f58604262554450580e1549110030b1045042800130390b0110319100ca95400740c1680192800b01c0044202c00b01d10740346544000c4040d54400c00040b14200035500c140c0c4803584d0044000e250300080f070510724101183c4031380010100d07407080d0340e41120305020310303240030741000d800b440d10301c0d15201c0349044e131001c0079581e44194840406204114038603820307800c12905504a0341024900070080a040822802c622503274000302d183c5207000c1403604 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 628304910 1250 628303660 628303667
    0xf112505150910080103030503040602030408070f1b0602031c0b03070302032e1505011b021306050f120d05030c04050306012601060605031b0909010e10150e04090f02030d 75
    0x810300558100c0d803c0f00f0181c0d01125205400c1c000180018000c00c0840c000c2101030b006950400c5c05022010f140a54641e0343c1c0e840b451341024101c5020104030300d42c4052000411000f0010b015a0000c0c5141c003080c0c8501501c90310b40d4556404480344e948012419540302000107001859002d02115000c4100c0080049084410903900894821010b81e0303201100a50064070398a14002050b07945460511340151140f2500443c040007041e0700d00e1280b00903070b94210442601d0b00c914440015a1800c100c148115400607074011070103011240b105408100b07000880e600c0b030752454a8410b0312601c0d20f894800c034502c40d5a00c40b40e03042c030802c800440d181001022881054041c0e00c12910300100444c56142078078801d1250780702292050000520030032480509040d2030460b550340300d144c6448000080c50000d001e0300407402000d516070030400800200c50f4808080d0449d1603100304000c41d8001c00500d000c02c60b00543d4002c5494940220401c044642040c3e00035a000f030595840c03044846005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 628306160 1250 628304910 628304917
    0x1b0a0206030c1c0c0c02060f07060603060e0c04051509060d06020403110406121110030b0301021809090304080606130905150403030b0d080909130c0b07030f11250515 73
    0x3070300300c3c600d5001e9008028094071404040520365240c0c030004002540030030960b0b0f040300d4410f03c41540d00b000900c0000f0030a01c140780185201d504001010405010454901031112641c035000e94a85018070036900388826544405100c200d40401040e5640d2012410121070070100800c00e07800880c3c0031040050300001010000c105a03002c0000681d02e80d941403911082031400b512544d81400c002c00b035400d2036520340c1c0b101c10711341c00c0114880c05001d000c60308a920440c407080d114088949c212503a0300e0700020254119a0000041d800e003424034079040c2d102c14000d09814840c40b130302c03581d4140b01d0209070030000071320340c0100903a040c0121030140702c0d004c06021501180003d10340130b8001000d1500074041e0f1403490b0400140c904000310181800040b42d0040c100300007140c10081000c00140310100840d0180082c4407080b41c0b504100d16010f8001150b92820000340302c0b003600d17110345030b00d400a110761000c8003100349250300301d820b0b4480040d0840715810194010740c802c03401c0128814003030003c = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 628307410 1250 628306160 628306177
    0x30c02190e06060f030a0b030718051b03041e1e05010b030d0203041412030c0604030f120501120201081312091802120103031107080a030305010e0601080405031b0a0206030c 76
    0x4050082c2c0d141d40802000340710389460018540303818000b080e80240d9507407050b180040060111081c2c2a1195100c12a21007004031490030325448108210250078902e4082d071049615450142c01c0d410107586122030502c6c000320765501311000c1d0140034240080d0802d00076006804003101d00e401000c6040c07090203409200d040710f000e446407080700a02e0b03500c004210b88c00c4034403461110a16a11308000c01032190707001c0c40344145621050004918400040c811a40030318440d44800210174504130016058140400a8000f22440d000041000c4007508154856083c1d091900c075a807039907070900440b045054020013812121003140400081c581200c00790080d241d035410b841c84d81801042c1e8480c1030b03115003083d2151007401c0b07d004100083c040d52036131444200360400e6503a0185c645440303034a400f04801c420740009407200b0040041541c89940c40390400000c0c68001c00624180d140d50703a60344682030998001e8040304170340c1d0034580b00c00c0c00002002c6900400c0c01d41c0d45e0418a032084e0194000e030301d9 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 628308660 1250 628307410 628307429
    0x602031003020f090702340b0a121806020a120f05061201060515070203030c030a0306090b040e0a140304051e040c0809060a020d060b031006141201030f030c0219 71
    0x301501c41e10380500168800e90a6600404d1030002c00055880501208926121084020358400d1f1031021030707048642c05452442c14550f210a10318400800425000c0b5400800610307080c051f00b03444070b10a4034000d4036a04101e0150395145c1c0000c0c01c460000010442580040c9801d20400034243c458124a0103003c1c11a05200b62040c100601400ca480c0c0e84125540007140009411074210b5400107807403898002005ea1381860f10004c49a421507000c5409880001c1e581e00342804052464030510394a040c043c1c40400100100880c015a40d240300740000d0010401c200c01e80c0c4081c003040003120007500d0041d00d94a4074241d200c004001c4250701c00c240d248584e0400c3e0300300d2042031207198918800c8051000a0001e6112218800020340c005e103a84c481480d12082c1c04980c0d40344a0008500906080d041010304503c3d0a03402800802c41b040300000e008010070103103403013a411174503031415607800010010184419180540d20316800c040025042200f01038500c80495001c16072004039905483e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 628309910 1250 628308660 628308679
    0x3020d03030f0c03060806130f0c0e090706050c0c01030e030d02040303090e18070e0402030309090711152a0d06170d1b080a031d011a0d021f0507060203100302 70
    0x100f00b90301752000742c01080035541c0300c01c000a48001c001aa0082200d020391241007807010262695a8040c103290000c3c0ca00d04103250520007c0201000003500400303062074410704081c1d641e05d00f02d8a54a1180c4c9076810161141038130700400b20f040c411103505000e5248119610f03540c0345009000340405206036a45821410000b03451400f5003801c00a01c031268401401c0414200002410342c2c1034054016038041c40f0038420011213894942d8950300601131134a803038010103c2004201e142011005803250403102c564180326030303209008071800300a498032000c076825a2601445c500c15004998142107018100b100001e6800c000c45440020105944180c0e10460551501600e401c400340b10b031000c0c9107081c4400704010524800c040c00c0d81e00214034000c1903003809080f00509060001c20700300240d0b555508100e03e5802d00145000c110300040e2001402e09100343c002846c0d000c0f00055034159204d0b442d854100b00c500c10703003c480c0825070200045449041002c45100804003902049010b240c951 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 628311160 1250 628309910 628309931
    0x5090a0b130209010804030c030e0316150e031e01020705031306110d020a030c060b0d060c030c02210a110601030501140105041e0c09031a040b0f04260403020d03030f 73
    0xc0c002c880710490103031154003898507a5601280d23200d4940500303804102c541d103903200a42d50306000c00c45d0070041c130303c40c01c2070b0440c14480c0c0d0f004116000300018040c481c0c1310400542ca1744020982400d600c11400d1902d0034000c81c0c60b07003140a032041e02d500130a01d001c006061082c00c002c82280b6415501c0540c2c0d1841c40e1038000c0c8415503514030040c1c0702c03005079200d86030140c00240308001c407241c414882e050202e1032006035030200c1d40000c0d401104490094540c0d00e0700700c0380c40e41842000c0070707406184000c2113101c1c3c8034012042801d5102084c0c2c1662400020554141d40c092014200411a1402210165a0340341041c900a01f02c8502180e00c2200200000640b03241c540145104103160881e1440060b00c0964031200401081030003000f400400d10000021403440c000d0803103001000f5074001420b02d42480c144008400c003e1881110140c00c8081c400031501085480d090030340451030401c1001080d079a06001c6000702d5000940c440c40b081c01d9841003681c10b40000d4040d1812420602040249 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 628312410 1250 628311160 628311199
    0x10c09060908071a0706052806030b0a1109030604030905041506050313022b1406161d061605060a0b0607060f02040506030408120c09060d0b030705090a0b 68
    0x6104440311640302d1141481036102030881c003140d00e010b0ba1003217450107a50f41d54810a9403012214000c1c1c1c00348403055032141c4041c18a14144004440004011035420350b91446007000014040a102d107139921060f4446110000c2182c0d81784600030110340c11442e0920f4010f201c80d0b46402628091030624001141030182c0e1442d0300103840642d00c03400c0c10765a401e0507245080c43d404070203a0f40610582c1c1070b2411044640320f1081c4001301c16a2600c00a0420b0900c140c01d452248203000b43d0307a120804010058a41e8580d00480c181d40e4076000205040024041003038040305079406a00010005031048101046005071f11104c0c40f43d4103403946651404035142c225603e40480c2030700302c1010403007034000440640c065506098a01c070010300f00307920303400844d02c40e0708119021651482d00046880e11000403800142d84004a259010b242141c2c00001c50342c6070080b4103400e9a03068680c56051010b0341c040c0b08403005400080c05120740f03440c0c1601007101411052514a008181414400d03403076044 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 628313660 1250 628312410 628312427
    0xf0f1a04030309050f030717070518010303020d05070c0902030109050403081f051512092a06090f0f1203093c15042705040c15020f030705010c0906 65
    0x101901e601c00075610305001c3c0145441c8110300203a0501802501198030302c10380d0301c008c2c5050720000c014202c030307802c00052054103081c400312000b41c02000d000400020354001421586e00d622883c08584505141c80c00c04090651a04410400b900110010440c0c0c25a40d00c554419406551286a252502c9840c010800c1d50b48440d80e05d00340d0300c04000e22450070440020400c40d90202ea64900d0f142c00d02c481001d40f041c069403250850740102264035190000017404500c8000400680140042084005900341c0324842c86d0b207000c0d90304a5420051551880407141a40b4406851120350920b6182c50701c3e00da50110154521545840d080800303c52a018440191712911400802d5602c3c0114003030040e0a011001c05039101d042e0400c041c003003c0710031028000808400e4000d084010f11021441040d2001503080ba104510b400204804210080522021564000d00017550000d580304103d0a10b04c80b80c1d180bc641e44000610310f0108481580010b460a4956451640e007030340340c201c05c031441071 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 628314910 1250 628313660 628313663
    0x305010c0201140618180a0c03050c0301060602070b0d09030c0803070e100302070206030f0430082d0709050415030507050d02032a0d081c150b030604060f0f1a0403 72
    0x41208000340b07002c10a25040031602400201f21030401d049a03a5011180400d90070494464101c40c001403840e0809001d250003502c0c1c4c500252140390300305440070f12140109803c4410103502d03105980f05050003000000411900003103496074915020001810001e1010745050244083c020441c12040c800d01c2601c2005600030179082c0345480b08943c580c07541d44068000d4820003140d008036048110501892250f0f4504501c03075070759904002070b000e4600342e40101001c1c03418420030208e92180101030312140c3e800410820064a80c0c503083c00444e003482d000c1d0409500b10f0726001c0e071303400c1d9110160752640450b4490412503500540315818040d01c509005002501a40417902401007010100b5940c0b1581043c13981d00c00d4890151000a550203204020580f0400d00c00200040f8150142c0d0041710f01003140031080c04410702100540b034240740b40384034030036020101101040300380c0d5445d00104c0082c807421a07040310141e1542400c2d42110101c0c4903000344d400020711f50207000d100090a480869 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 628316160 1250 628314910 628314949
    0x1a07420203010f0608041505070f0905180109021806030106050403051903080105131b0801090e0d080a0e07050a3203060a0209010c2112020f041a040305010c02011406 73
    0x1807504c00151118035002d00b04444c41040e002d48841d00d40210312500344589020340d1401c2c000010442c001c1c20302d1a407070b00500d01414811005640e4418200c4404d030455084040c0144d036045151304070f02d10b044003184143d074000d60001c00015829440000760050324000c07001d503807000302d0301525a40fa480000400401080d0803c00400061904030705464540181c03803030100c0c12001405d400c14a114610031402d0219180e1401440640030364441c01030b036075602c40d004144206500740301820203800101501c0c4035540710500d00c2d0081c01c0c1404803600900026002d1810309880d071400e1038022143d804e1400200c003280202104540c0c104940000a04028003d055a515040380200c040d41c0412900c81c140404045500001000d8040016050720002c1a81e00d0680303a181300240340e0340702c402c0c04508960050040310700e030200c4c0d02d04607402c0741c04114030308048000c0360b40207901328004d581c8040c14a501e40000403000d95010340081035000780c40301501303031203035514030400403124024020701019 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 628317410 1250 628316160 628316189
    0x114151204020402090a0b040b0d05220206030907180c030e120706090c030b090f01050601030c080f090f030403111c0317190603060608161a0742020301 67
    0x5803c0c40e6005091100c00038200d00211521251003e046030300c16030103500b051000060041c80050f20380f1400303030001c0010100c14182404840300790310f9004049006403285000201050b41c4c0c0c4400c008030f000078010340385100c0d2400110658200203040c54034410011904003013800d200ccc5000410f040b0200c0c40c100711041c0c01d01d121521103c1c0286103d0001721007008280e174021011561030b40031584909000e00003000340c12074640c140d90948801405041c185401d01d07a120130020740101106034082c039903c0384030318140d4490300850300e440f240c0d1010070194000001d011040c031440081d040d001c510140e43e1050394202071030340700b10141401d150103000207a11818280702203020204103034104c14071440d0704450650000c1100101ca140d64400c40f031143e6030310002c004a45040c00510701d02c802d616a40c0e00e40030301c2c1410240c5c03110100071034029582170020301481004485540b182000ca00005000a0350864a94891032403190303982d960300100da0410b0f5080440002d00803207040ea0802ea041c01c80 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 628318660 1250 628317410 628317413
    0x109080307080a0b0d2108060a05090c0f0f0d0608060c0406120b100905030c041109011103070f0b010512011109060c07051215090c10080a02120114151204 68
    0x440c0c2d100544040f4034039440d44080030181e42c801544040c1a4001c0e1003108146105402c08203840c4c0c0050840c106101503401002260f0752114501021034806480da0903150780c641d00d45407018400d42c40f480311120310201e011601403c1c80d0020b0600301044060070016030b5228402e15940d104212082140044100400e011180c811030240e242d200c08908081002d10741000010105004142210006a01c03007034100403500c0d041014501d18038040d42c0401c40281c540b480d0741650302c680c5100340d06204644001c024501c5003002221602500f0201c0c0c090111864034003100c03150403c0c80340340c0c80b880740c40844014024041c801c0e0701f0b0a140c14a60a450083ca01042c00443c1d04010750a040301d0150f841c0000709600c0d0384500318a0580081d0281c07c0460000301c901c0c103c80b1002d000a5095441041c0d400a40d4861051400c8070409a0404422640c0c0304a000006881002d92245c4850b009400000d85802d125145041d8100101e444042c040c5070380344980320700e0081040840c5403da200d0007150 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 628319910 1250 628318660 628318667
    0x604080901110d110106060c050a02090402130204030f060f0213031101360b040f05041a10171303170703140c03100e010305030a1206080f0f0f0109080307 68
    0x540d40041c1000340b003188a0070822820495a00c00507004180f12502200e041d40d42032162002800c001c3c2070600c4c841d0025140d46544040c40c0c54001e018002c030802241c1036546400c0c100c69035046041003950340d40d403a032511400c05405180100c0b1054201020711710762a03078600994242c42011615000c00300c0c5103403240c401c4541400c3c01103041c800c1ea0311880500800081c56100341d007205803403a5030440c0b0091a4000410202d41c000b01c2856020301041c0654407080c0444400c8550445020403000c0048400342582883c0140c0c00741d03c50340300310f03c0100503600310108503420502107100075040d9903800c00718010a2600040180000c14480714541c00c1510f1507000d80c0c01480034500020300c400700000e600000c0009460190080310040100030f83e0307c3d00b0300d00c500c1c080c1012403036002c080d514503500c6c00e40d00d02803161004148040c54480e20000300c560b42c000e100500034401211604c42c400005a80c596010148001041c00307146500c04060005005100103254000000f51561b6120345044 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 628321160 1250 628319910 628319917
    0x120801061b020f12010c020703170a05030a15050402070b0709051f1b0f0c0e06040c050d021606112802060127090b06010f0f0210090c12030801030b0a05040203060408 73
    0x298001381e010b4066030603503000d10900f111504140c00038030f000c90460408200070380c1ca000384407a032641c0410160121550220540ba0410020381002c43e201201d00b441c034000078401e4100c1c540092002c41d07030105025010184a00030106900c03161407032600c40341441990361030f03001040c4d00808a44420201c0f14818140c000c54400704009507550369505c0d5880400c2114141e50598041c4551441448560a0201030315000107003103e0801c00100c14140103410340c094102004c40b4981e01203501140b600e03001ca000e0591304d44c07000c0304001080071a520b270384194003c45c6410b40480c10311085d100c41e0440d8819460009130460f001002240e10f451030310780f6003041403030021000c50006180e030503543c00540a04d525039440f422004050303207401c0c0c0005240201a84071402040b40d600c0c1c2c000c2059401240c803021041c030410300414a401582400b482100e4070380d0001e40000803035110303c0c003419400f1a100d4140c0c0e1040c105043c46440d285c421500781c0e2001d950180d4507802c848003080000d21300e0f0009 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 628322410 1250 628321160 628321189
    0xe0702210c2b080f10060806030a0b10151d06030615030106050a2607050a0207030b25020604030906030f0603050d0e012a060903090b07120801061b02 66
    0x21551180d11600c103115401d000d2140848200c00c0c1c07994040603140d080f501642d0700030030000801e100c600e08044045003007211446148140840c40d0f000c18000c0c0c60038894110080e030049201c0b40035081200c003403040c0c0403291250040c0c81c1840902d1020f41880f03141c1c504003000d001280c00020070f280808000042d800940766640c000c44220940c01405000e401440c001e2586413141a15001c2c001c8000e842d48003043c47c048040c000864000d680c5001188030b154000c072862500544862501c10700340d15100d40d5070000350800e4071003004c00c8901c9200141004000b002e5000b83c0b15660102001030b40e8852059a00401281001c2030a0011502c241e02c40e164580c00030801044807552a1620360424102d070045200180d0200130108107546c02541340104901c010510b050f40c6280040c2e0503c8940304000001e202c02e4540c03500405141c46250450041e0200c040e007035a54070198602006040e20088606012488072030001400c3da00825030b1002220b081c5441c1d030b030015400d43c01c220410403c002c4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 628323660 1250 628322410 628322413
    0xe0307090b0402093f0a03030c02030c010e0715090608070822080702010908030a0e040b041b02031903021201063b090c07030e010c050f030d05010e0702210c 69
    0xb440c000b560f81c0c0740003140c0c00001480e401c403609481110100c149042d581707072444004a41e8102d01c441120000e05901030359010b1400180d1862030000403429845031208000c850340c02c01e802044d4440c000300300c1100b00e82100c11040b01d1240082d0003941d0343c0010303202e42408145140002221070b8018506140d02200384d80008921401800c1c2a40c1d140340c034040c09403007503031002c10a1811560040d416801810207000150b040c01400c0900805c2c40b01a00038040c003503600e40e0720641c069140c81d006500d003840c0d020f41ca5189041130f23800081d901e400c00703444d050501250f10351071080135000c3d01c01c440319a0610010008160308210040d02c005001804056600110600c100200c0d0010002c0e60045d0141489010b01e50308110308010480d030340500b01081e0040108018400603420480e0100c0c0b20100782007001184140c2d080160a20315041d1a04686d808001000300d000c2c04294000c506a86422150b1503040d100d03068201e0740c40c100c5617a0082c040e2201e1700025160903001d000b806403000d40c4d20 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 628324910 1250 628323660 628323667
    0x3061509030308150d06020909130c09091406010b0c1501050a030803090a061b18180506060403060501030b0609070305040201080c031f0312020c1509062503020a020906010e0307090b0402 82
    0x105e031480c000044c0a1343d58a03800704122549140c210a0705801455900800170641000d032200301c80c10205114240601d59641c40500821110312044540f072440d10090f500d00d0360b5981180c41180d44004014103490150940d0700303003804ca145100d1410b07507402620400300f040c1107541e510060741c40940924160700c07448486200103402805108005218071204826060b44c0766405003402040c950070004d0010406401d2100003002c881c04032250801d55804540340d220306003c2806403040b5000981024141000070042c40803407900d99001ea1410344815a440c2c0c2e41c0601201141c0c020380340240041c003c4c0021480c061300002c081c40d040039107a581164a10b10703c03c8804009100c0d584110b40c91400c0e81d40204009806001a100418003501e0328581e4001c2014000307a07078400c03003140b284280001300e85071103580d00440c001c030b0200381c0300d03100030350200000e0402a5407002c4046040b031040b014440020040d5211341014408600007600070881d060510301ca0802401c41011080d4001d9801d0 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 628326160 1250 628324910 628324951
    0x170309010c080d020d091104270f0212012304030806010f050c0f0c031005090d120204030c0929031506040e25120206070201031a0a1503061509030308 66
    0x4d10080000c1c041c1814009040d140317601e8039005a00905c0b407201d100d6441d000c03440c0b03260310001c0b0349020241980c1e00ca1010030300c0146007080307010202001c0a0341108450607503000d0102d0560103a00510b09203001a81d0f45009545140c03810501110000c00154401e404150554000c0721f0791451060503080003400c0c502c120280e10301d0800843e5858466500004140c0414213042c8088805220030400c2440a0b03d814007509030b641c1d244541007020080800009000d400b4254160307000346034007400718004169544000b034050701190032840d882007080c078141405104101c02000d44401c0c0500985403061800c501200a6000106a00d0308561940c0081e4134241c418001c0070500b91f03802c00c1c1d00c2100c00e0899030b04901296103400c600d82c112668038809016944283c240c501c41682480d02040102e20301c03411155419000100b60b80061103d01e01240d0810018481e8110080d1568100850355595002100300e098a00091010864510b07050012030722841a265100b9900340d51802d050211 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 628327410 1250 628326160 628326187
    0xf150e09180f0106030311150106080c190815091504090503040902040b03070207090b010c0f05152e0506090f01170c130602060f1f0803040816170309010c08 69
    0x1810340030180b40e59100307401d00c1050f4201c0c3c82ea84a0a214034001e107448069904804011070040c0900b000303000d80c000018900c2c1e00800129185803400074018001007491150143c40030b1400d403480901603054541c0000356003040601c4901c6040e164400415001d0b491040c080140400f4074181c41c85d0100304404507190301640000c0000709282e912050f40c900d00305500031304120f0290042428541029082540350380d206501011140d0445d410096140f440c1c50075502e001c0604001d0000b5071071020402c040200c9004240c10015840043d008424985c000000415030080c01707000e6000c030003408002000d0420b0841e0303180818040c1481c01403e0210300b21681261011034040d240b800000840d0b0189074510204000208100e000821050a00118100e9004401050700041c000070442c00000c00040200e050002c0148101b92640c540d110008a030b100e514503030103003201300d00185000a0000d242c00142154080c000007031403d0815000046a0340c420041099910200a01040c0401e01d00e = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 628328660 1250 628327410 628327423
    0x1051c0e0709090c210c0b0f1615050106050901200a05030d06030204110702010503150f0a0305030706060806160309080405090a09050f01050702070303030b0a030c0f0f150e0918 78
    0x260403040b1425191242c0d0030f00702c580200440040162886000b17000501c1e1090302c000381c900707840800d921080700244581460003900043c4120f80511000c040c140102c0d50196007034041800014042d0b82e032517480503681441030120700c6000810040000703c14407503865500c8100ca002c00207454036840d07240c42e40c1d07295400c0340a00c40f1503256940c42c100118645881148110100550030608110050300003915074080148060040901c002e082205c1e661035980c40f003000080284860a166140d0504a60700e070805241262807501d04100030808d14400540c15200d000c8490500701c5a405102e02200500000701c0211805141400007103150303074822503501d11072109807400003a14841400d01510b00540c0c03003000c80680e450401841907403540802d100040d030340c243c140414a0245980442d003400342562015002e0300044101283d0414a100c0300402c8858034208a05056240e600036614036180c42011400b1892034100300b0b401b402c2850850364051502007294001d00100c040701400c206 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 628329910 1250 628328660 628328663
    0x10503190e1e010c05121f0909020f030f0a0210021204060c110d080409150801090c0e01140a140301021306020d0f1e0804050a05032701051c0e070909 66
    0x204407030036042150b1002c5800c441c204041600a020035658000060118070580044003140c0301d542000174000c10326003c030074120f014000741420a295459580c04020314035070b28200d114001c0d07071482c900c55140001d030b60b14114405c0c3c40501034012280c2e0810810751300241d00f000650041c45980c00404006070050401009551a154281051303403420b10306440b0014101031041c04602841c00c086104002035034141c61800c0c07000940c18514880000c0e0b80c050903404200d1303945c2048010010044008481d008072415150307041c0c0d290340c03074440b103070890300080f024640c128080400c1006140207400c1c20300070146010b000146829034544940c680e400490300480c1c0942e02080d402c400c0c05034040303213a402d0320955240c003d24a8000d03403000d100c14010443c3c00000c000c009000b090a006050100340c071306d184d01c0320444c1c0d6115400301c040e400d08000c0c9803407920644981407280c00954000c2c01250055450301c4000031100c41a10590001005460111403040c072030203e0100f17803481907101d20707241107 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 628331160 1250 628329910 628329913
    0x509040f140a02040501091e0231050a080d02060c03040609080705071e031e060b28120803070f0e0d140c040603050601030b04060912080a0b0108090c010503190e 71
    0xb241401030006449042c3c0c400320743c0601e40044800000d55040c08205200b50580d80940d446503120010241e4100101006036036400480030410303200f0782c50342c80104a0f101034070301100c03031a40e0301a83c0761200c00d80242107000d60840230000382142605d000440d8040c1c0b04280000d011380300c94850300401c0e007141404495990160001740005a0441d1200c0000110340043c070015904603901c40c4000c031518010119880c085080e220b0401145c0c0e042001d000101400d841103619030801e141e198412082c1c0802100e0203c581d0101c0d00201c1e100d11580c0c904d8016103001d00e15214010704071401c2582d41c04582c1088003460307030b400b001d40d80c0c0780642c031200e402100c50002d114110304209051007508002c161207070303150820030000a2000b00d4000d04598100348407103155941c9052000c0a08220140145078240144840c003104d43c0100011340140419603040100720856001991103620640c2c0e0103d06500c41c9400d0480c0c1c0d1310070310003168400d0503607034100f06004881095400b960044071101c0880d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 628332410 1250 628331160 628331173
    0xb04080d0e040e1e100c050703080c09012708011b0810030507061103130308030a231b0702180f0a0c0e090618010305070512070b040509040f14 63
    0x1a03a8422000100280102da0030001d400b0740140c0c02d036a40c0b038410f40110684003100d40703512082c40f09000001120f40e80342c3e02403200900074240106950701003a8201d01180410000c281141d410300140c40070004182c560303030040610403409082600c20700560a420750350150f004214040b0a020314502c0b02c502a0b212111094105c0340a003004000404880307013514519400c1002c030794001401800ca401c98101106802c0f010444c030b50840c070a504034081a001e010100104102080f00114420f441c0030350100a20344c42d244c0040c0240c0341034107036503204000a40c0402c00644500b1315500c404a15550510b24008440d40840c030b08000b15410729003810501d9003000401c040c01c805a0382e00c000c83c420108040c204030203020742400b1075500c15a029800720400181d41c0c1d00d0300618100c02204800c4540c4c290360303407850142d54030606170140ca401202c072480c41003e2000001403041c251400890858181800c1c0b2051001c41d80740104103840c0b0b440d5072140c4d080801c081c1e03410b040c11685043c018061 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 628333660 1250 628332410 628332433
    0x708090415051302030c0f0a0212070507030b070e011202091305010e04140a030206042306180c0f0112050a1103040b01030506240108091e030403020411131a040b0408 73
    0x2c4000140420783c6140c01001081205d51802c0112140040c00100b0243c603403060203412864000e5050068040c1c03800040c0410500800003a010100c0707204100540c41681d0f036180840b5496590385030680411001d070900b059640c182d8000e44120308001c0d02110301421603100c40c1050b140d00b81e102506d2010114280024484500180407004c0f40680041c0720b4801d8590f0001e555000050029011007400031802008a41040080e0440e510042c102d8085041880c202e4078a034078680301c510b501b40325022456006080060300b2600c00c01050711903056443d001c40050002c0d02e8020302c203000240d074820052084095203000342d8002c50054070b0150700ca40c110b144c80c92170020003400400f24205800200c0c008294061004241c24a0038a000709032a10b84000e11440c1581c44900842803840d981019a01624000f0140c01103138000c4a00b402010000340803032000340704012103c00f010408040c103020300c101544111200c90541781d4090320b000d0ba0345050180d107400941011400b0740081018030b5 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 628334910 1250 628333660 628333669
    0x105010f150c080915190306030f0f081b0f060105010f02031c0e0d0c0308100b030414120c0a0c0e01030c0501080429192d1506080910050106090b070809041505 70
    0x11804503031f4201001401c1c115214480d180c46158802840c800004403d5820410140180c45401c4420300120100d0002d1000c055150035240c442100c962080600014047d031207840c0204e1425201d401035458402c40e6a040034185213507214003c2195100c5182e82da001c2c0007000510f041251603910f4110440b20352400428641d0003400b40340c0041c1d100c0a05102c01840c110440e82c000c0c1d440741c519040751900180780d03414a0b00201e2410811031000c00d0500c044000030907140740b200d103d95210084191580b04000c040d40d400c1c040a0000c0080c0c240510165018410071500917015000c03070008580d41e004e09071031106c500c3c414402c1c03004901040c44007182d20303080ba0106000080340107118140c03844010703641d01c2e4a000408016102d01c0826241c41c1d40c0154072946002c403c00b20710740d41d06a19507074050b1400c4010b5a00080f0b40c851302603001c2c49540d01d442014140d0700e203580e8601e402440c2029045041e0858241592408010403010b15959030720b10510001941c060101c0010758900420803 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 628336160 1250 628334910 628334947
    0x90a0b130515010306060609061e050c15160201110c030d0b0307090c05090109171005060418050601081e0c06091203120103022d060c0307170c0105010f150c080915 72
    0x40c0c18482041103501180d00f0300009201c0d0ad5040e4581aa01d8180c8860380d01e1502d0704001c0070768209a5007605014105c1c1d006041e4204040840d0000d00010043d000183e006120740c0c86500040d400902a44102c2c144c550844155100000c00702c6846a403601d005200300d41107001000c000c180006400c1e41b0759600055614014104c90382e0002c2e01081e2000e4150b00c940c0031110860740d913940e450004410b03a640303034840761482c415840c02da80d01d100c072890300c42c0ea612400c0c040d8481398401c14014641072044510083c01e944071840203480030501050522202e500b281d01070583c0085034041003140c0c3c49007000034040c6400c5801c0200410b514500501490140b0408816107010300c090045000341e030030500c08201c410065032001d0381c0d00f01000c01c06046001e940b00040c5500b2000b110800321440041c00307050050b0b075900080002e81da132a60036014200b00745c840d058030708810921328680207005070700d640051030061618030318052449000460f180301c40d594006060002191100c1c00c0148910315 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 628337410 1250 628336160 628336169
    0x150a030e060f010b37080103060b0f030d0807050d0e0c12010e031602030f01021201060e040b01080103030302091f12060f08030318190c0509090a0b130515010306060609 74
    0x1c2e060950610340410164424048030021500315800055104101400d1024440800d0800200009140f50303008004840a21058443c1814554040308624001810500d0000010020310900c0104141520000070040070081403090500401e450300c10540a2888008003510260841048140800000c1c1c01c95408110841c2c0c90000c080c00030160000440340d003090080c0040c4144021880040c0c540780060322950219400441c1d010b28025001d204203042e00c1040d1100000d941d5003800b0701048800340312800d40000d4843d80100086802940140341f0000054400b15506221401c0040c514200d01c1c210000030340100100208c0c0d05643c41400007038807603404004047c030b140222403980c074000a090009500c00e03180b011120039000300b0240e0f03440700a03801100e020381c2e65800c0c0450590094811107018094400c0040c81090020441806075940100b40040a8a0707110311504039030359403d01190688140703140d161305684c6c80c0310154000c40c4981c0000c211542414001000c50100360312 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 628338660 1250 628337410 628337431
    0x4051e10031116020f120303270a06020706241511060103030e18010b210601020d120603062a0f0f050a030f0e010f050c0403020f0f150a030e06 63
    0x15260307154a10b4904603459401030b00f0100030302c10316500000e5944581400e1840d4001c1304403d40074640c440c040091407203031440108400c070034002c02071240480d000240315421584c1044440d00006030755540600740c540c1c010940002d4107440d010700b141c1c100c54030007801003680c122000c040112402c0d02e520080c0100341c500d040720500075282c1c00c4035528a41804000c044c401382240d00c025540b240b410031180052009c0220b1500d5949c1c140c00741d0243d206641e41142c0da040086000c8602030300460007070080c80b040c0d00601d40300142e264200c80101000841d88191340c1c0f242d0380000464824090907281941d501c0850201074002c500001090450014405c24800c030341d6502099141c00c200d803084511140e0910650352541c006003180104140344502c046245020f05089040380154042c10000400003800c021a44900407014080d0141d444020f505c84d40d41000c0d00c8031420481c3d154075030203502911401590001100114181e0000082c0f50002075a4015032141034604020540c0c00503508007 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 628339910 1250 628338660 628338671
    0xc12020a030b0f1e060702191202030d050a1d12030c0105010e0109090804030308151c020a090626010209040c111c0e10111905162904051e1003 63
    0x190079428031300002004d8820000440d50130195120800084680d4480048041d00307591141079007004064880c509a01910451610000d624018001c075442d006a94a0792140498030030080da0096101c41c02142d0000302c0ca850070395080c6800c00280001003142d800214456040c003815200000e416800485801c0c20510720801003040c04040383c041e680c061401688540e02d0849104041008900454218240d80600000498a1080d08400c20b00c00c89004c0486c568401d00b05043e03500a010f640010701c41d40d07a401c16031114280a042e210380b05100054140302c600400074007150051a02000801d4100c0d5200d40701481c00e0103503840504031036030340311800011500000e018085070052240103c5c083c01c071594001d8010780c6111200010348086488074551030500e005001c0301c1001c01c85040c4109460b55284400a051060a944445040c40d13000e844142e0f01010485400841c00d10300e6204120118103034885581800c900096440e40c03101c400ca280c4248020255200f208604052400 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 628341160 1250 628339910 628339939
    0x20f01050106091e0e040b280e15240a09050702060405191e260a0e0114030f1b070c05090105040213170709050f0106020715090303030c12020a030b0f 66
    0x14001c45d9000390300038a03125006e41c0c4500d052140320b461300001c01c240c10105400d48039100c044e42c0140200325154016600c0103140c50003415a14007060314584040c07500a100c0e4260038000346820074120b180244921441940d4989000c1241d07010340300380c4011b8201c17400304001e012f003c110302100d90a54140840440703e040d1148410100c5407440000d80c0d2980d403010750240040c0300b0301401c0700c00050001105070403c0040b85980f0b9840f02600102040c91450407401641c000d58042c4600801d806140d82340d65291000a5409100142500c46441c0b84980102154144402404850744103c1c13980202a00305400c01a03035400503031050b841140100822203400f0f00c001c011004030744504003011390400c84040701c80c0c24203038103030400100c45141104000701810700c0030015040700c3c800d0f0283c0700a40c1d10b480803c0070f82d03050041e040021514001c0d081000a100368000f40c0484018903140c1e181a1014851000760780c414180d120000303440d040007400300e1510300000d0140780000c032440586640403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 628342410 1250 628341160 628341179
    0x311100912060204150903030e032b170c0304060f11070f021f180609033908061512072c01030f12080705090d03020f01050106091e 58
    0x3503019030030800340e04107949010000ca54041d2000340811803004220030200c0c10001b481300490380b1090380050301d15410802107080c0499201c180340c4414201d10742c82d211080f030f50003090000050b0703c01005202200400a89030f900d600e14040d240e160034599603401d00782001c2050b6850050040c091600e03010302d0162a03000c0f0011500a1a8025440443c2030124000240003c840e0003805883c403052a024000346580000421200301c180341c19030303541548480044522031600d00000b040322130304100d03482d078491103110702000c40c00510f4840d101c031415040e1021101d041e26801001e0986c40207044c0000d0300a1180e00c41001c01059400c440075104448009603940c0c1103115000c6d05910150a0150001c0142280c0d2030001e0350740040591075a4030300d001040740210072001d484500a02d4004108203120701c000c1806840180e0310349080000c40001c1200740744000340c044003944515411000e5446080c001c603802080c0340e84070f52a62501e04510020385c00e10310382c202c510785900100d09101038204d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 628343660 1250 628342410 628342427
    0x1050315090402014505031f0b2d1012020a030b270c092d0d11010f020c060d0203280615050c150613060906031110 51
    0x10116020381d001d485a000694420030207084280100100b0381040c0c3c001080302c19000e03040600c9003500e0050401c40c9035100b01d50342c018090541d060f00580f030034105640e005850303403543c0c980d503541c006070312281000015200b00d0348155400320701c80e154041969507180b0f1261001203d000759505032401e140003000820543c1d030a10342480c902e901282c0c4a6040d442588810540c20000e0103c0c0b03401040310564102c029441c03098030060504031b4001510035901013007607801c04400600407080c0383c0c0680c902680f2241e44614884d081404056481c005a641c0c081805640c038001d615580c10802c40c140010000a186650b03141558084070716682a42c5481e0100c2c0e805178542040140c4036102e501d00712030341e2020101d0b0300e60400c94000161100c00c1c41036020348129041d448084108048280042d1130900601c80c602e0380540202900d2840d00c801c0f070001c16413158000f4441007aa601a03d2410f04071030060b04064040c50f581c0c0811b004000900c2604840c5c858211400b6070307440f40c2ca440050000340c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 628344910 1250 628343660 628343701
    0x311040b01170712140108210921011d0105010b0a0806090703060f092c150403021002040e01030b06060909070e011202030f0a0609020f0702040911060316030b010503 73
    0x591840058500c0d4450803403292071405040c0c0500481750716080e481d0701400280a00520f82c000c4c0080290561806000310f06803400021109007031080385401c00c0061407200012480201c405100b803600814203104000e11305811000425005141984041c216801600301c2403101404000c0900d103550030690181c1e108400b106c10607204d070307507041003100503203056032144005440a070004241c0c5080c64000d882816440704402c1c84402d080350f24600300d50310078100b0300c1d05a0040300950b900c1504040c07116a0182c003d004850704403c02c041181300300d82c8075a02400b04051a40c0040c000c0000d041040c50304003108603140d81c1010015800541090005805c0c03c1c2802a002c04080050340941d11045000841c607000310349900e420030f940c4000c02001c690859580c0d18085000c52042e8180c401c1e901107413400440d117806c207085603003444000c01059006484600702500602e0f2035070355401c002c43c4980c1c0400c10102c00041d12090150a5441c42c1d01c0340d5040c00300a03c03c00000f00b06914580d100340 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 628346160 1250 628344910 628344947
    0xc0c0b07031e180e22080702120307050c0301090308130c05060408070e010e0f060909070915030b0f01060f050903010906020705070e0a060b0a081e0103061517030307031e020c070311040b01 83
    0x100d02c91400c141e947c131404c0c400035001002016a11840302003c00074007070750707802401a41c88100614040608881070716100401140d01540865404044611009100d512500c403628082d51214005a8980c0143e4011081e551040d00c1c184041c00003030311064018581d01005071030a042240c41ca2019240007001d90f401440035800150500804000375001444460810002d15075425103030b8244c0c0780c00780416131b40c0d03550031030105803200a26801d0701e0488606543d1011285a2031408952070750090740850b43c1036480c0c8400e900880c00c90b200401021b8480c000a01060f0724140d0321840301c0c58010003084c001441c0000403c100701000d421281102e040d4030f0950025501c1c00301c0380c0080f00c1ca03003c0d4074440303004110010007084001c0e400106103243c1490000015680c0d4131035281180c03d0203242d4011500f090011554036030107504050207107104c503262000b8009180c01c009003240c1010b484116a540401d0041082c001d03e020f00486100c1c0561b0f0501c40300003420000390044c404d0140c01002c4 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 628347410 1250 628346160 628346221
    0x405012601050f03071d0124080f0907030209160e0a0b0d050a0204030b04050a03090503012309031207090e1303083103090e06010c0c0b07031e180e 65
    0x30351303410310080b40500100364044000140e26001d14409503001d005900300502c2d00502d52850541180b01500c507520f0540c1d680c811a0f8488542c202ca001c00600014001d104401c4003000683d241e503062885034041542d82120910600402440048010049401509003c10038072500c4500030032900044110000450181c5490a00700000d22640c2e20240ca502c0c4540140700030010085040c0d800a0301039961103d095850341d08140c202c0fa00000c04001040ca1645c1000d240400c504886a000c0c3c403c0c020380781400441d41f69403044079002c6a10340d0010b211b080d000e20042400140450b0003442c01d04c0c010000800a40c1c001e0030000d0082c0041e5041b04507070100389004110381002e119500070700b51078030128060506d07000d054031019001d41140f0300004000102c65500c40c0982c0440250405981e1551502c1d20200c00e1190340004000c2d0b00b0404180741000d41070050350412642001103070395050b02c1510854039200d00c54400e8000b152110300390b100748113440c3c3c03002010980442d45859048407 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 628348660 1250 628347410 628347439
    0x5030a090302070b1c050708010506090d0609080f030f0924090705030d0e210303010e0c09030303040b2203050901050c0f0106060905150702010f0e0117010b040501260105 75
    0x203810b00c3e5910450080e180081d01071011071700c124140c8a5022088802e0142e510341d1602502c80c41e509000d500c0c2c0102c02440760013130600c1c0c07882c0500c015a02803030380040c0c00003094482001c1e56218031303c440b0359840000244010100f401101c0c0740d01040304c43c09800428414803039108401d0b801d4110309080983c1101281d10440144443e00060000604403841c40c076038400c024000b9061064030611500706c410313100301100300c140200c1242181a401862542c0c7c00d10402d600d80303001c050000d03038084106001c4500c2d5031f1410401140507038080e607103100c01842e00d01d440322104100c0c01d040054000203094642c0000c0d400c081030710862042400c0190706c40144030991417a00a441d00c40384134a601f088000240d45400c10440e4040d2081070b10310700c2c1c0074084044281c5951103180d00090018400d06040d025280c4914030b400c0e800601454030410310ba03440d00c070703070040b00d0b4081e004800c001800080403c11907170012204948448045004101c43c00c2d040c030f02d804503200c140308140c003e01c2802ca400d41d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 628349910 1250 628348660 628348663
    0x30a0c061b0306170a120503090a0803040528020a230d06051b040308040303200a151508150a060f090209041104121518080c0c04090305030a090302 65
    0x40a280081d00408034040e0440801809880c140c86810000002c81c1c0d6046010480483e00c9000940c005d4950b0b0942c0c080c85208590940c8001e0111815005100c040030026002c2801580114040d0008114192590403031f4000304074803150901c1d142e080b0325040320058560701c21081c2190003060501030404614041d441c030180d0051007103a03000d40c844611800304042c1c0d0344090300811b91000c0d441002a00c00d40a440144030307900018001d07010520040001038071410381102c170352001d440024085000490b070f45107810301e0840222a005a00824031203141954890751500384405079022489038648000c0365114a000401c03400c0f0000c848000442c509803540100c401000700c20b400001059551049000079085410f910303118a050800d0301d00d01024407000e0b501612440000c05001000507902c00c40208800791641e26003988540d9070200101c60341342030040d0b05000d000c24603511207280c0c607100c0c00c1050000889200f58030703040700702000c2070740203056039888150b041000a0f001407509007030307 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 628351160 1250 628349910 628349921
    0xb0f04140109050a1e0c031218151403010b0702040914161502010501030b0f0711010f0b0a0b1312060b0307120201030507020c1c0614070806030618030a0c06 69
    0x1491590308082c07220080000020340000c40314014201003c1e070200c86030120140c0702a0b144043e0402101203002e0000c510440703107010301507409040c0040322aa12080803585008a540114242810401c0c0196242d401c0100d4a540140e001d19041c075543c1840041703600b0b4014500d0103801295035141c21000c103c0c03801100012880d8210845400e42c84154200c403003140c4502403a044c82c9114180c25024a00502405040e264000380d004201d9403824000d00320b42d00001c011404101080b03068810b07a040a20800102004182000c14030070111810b0210a0110390b21060380a942000103000f0200f40403030003803c0d1032141c504002e40d40d0140c10410007404901c04038a0707060261000014415024250f003a0400b4800e8809000030340d03070f0395001da8984400411094000c0c800f00c03081245920f8050700a614144a8140055007020441c0781104c60a41240c1c0a00464000021b00081c0e1404200c0194003265240b09100c2d540e100e80c82071600d80c01240070720014004108820010000185c224 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 628352410 1250 628351160 628351193
    0x20618030f0d1d0309210703020d020303222d1e080f03031b092809290d17031504021c0c09080c0d061d0c090705070b0f04 54
    0xa0300b041c0901c005455440380d0121001e640320f06e0001c150158040c21081480d462224202c0162815520b560240481c3c9500c01000703c2c0c1c035010400480041c2c6018a00d0341e4040c0404818074000f2904100c1c500007404206480c5030048590440c07241c500e40c0e0340c0c4a280054651683d50317022600c4200c18003190001c1145c208010900a10b0064441c203440000070b03601c98130352130300d0002c201400c0c13615916072031082242c0990468000c0c480f1a1000a070480c071401004012403801000680d1101c3c0182214103483d1003540c5c89090000c130400a44541c1914040c40700304860300145040b0715038a2074640b6884d101c07142020440800014021180c501c9581040800540290343c4d682c4040301c12010700d60f0311b0450090641c030308100078803010b104001110998103d44000d01001c2480010003202004400044481e5a02c42e01039001d9011408100b0850a01a0b002000c010a50000b0030950301c4000340b4079400c010302880000c0119064800711900310f0360540381e100d07094850342481d51040816425 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 628353660 1250 628352410 628352441
    0x31103160b130b280305091e162c0106020d030c020a020d0501020a0809061e060a1e0f060f2a1e06050a02030402210118080703020618030f0d 62
    0x1060310300803aa0b03059418130801228881a035010107810706600303c071400c1c0c81000c400d90101c00c0030700c0440b400442c840a480b5250049901c0c50f040c40b200d044029145400000943c2e03030040c0101c054200301c4c03c00d4412424041007071880382d0b0400c14025981e0f4147d5000c42c04250312a1b00f9411002c0c020322590005c0764000d080c446c0c418545050081c040e40c40a4034181c0012200000213960300350104803540540a20702040e204038242850720451128003034021603212600a0b0000b8480b6840807055850540c41000e50300c406182c644082c1a0806a40c401414080c070b101c0c01500040e402006c08461002010b03403100320b61100724284a4000e40c074480107040c0d44108441212040400e059a240144a070b0703018001c80c0e5410350768070240c1c001507500030342182d0f0b46c844c40d01c41c03d488280c800044001c0c803000000c00b04104043d2017400d000b190420b480b419400601c0b4014140e0602c02d1f6a4071800f4000d03507012540d08491441c1da640b04840c040e02800001103400320f44055190800b4101e40300010 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 628354910 1250 628353660 628353667
    0x909040305040b0a0e0f010e01080604022113120c0f02010c0812011e060504030b04020d24020702010806030105160f02030c06090c010915080a02031003081201031103160b130b 77
    0x15025090100c2d10700f20074440e101c01d0300341b80305640c800c6901500c118410394800f520760300c441d028000a034100c2c015620004a8090389039180010050040740f02c3c1c1904503004281002c01c0c10000e003544180b13030b48501004081200340e00880c2503a040390999550a01e884c82490040d81003000300703801822200004040e40c1000094208803040c4440d41022051110007504d50340d03004256403910a80c840100710f0711101c400075026140c0140b117200f00c42d000d5800d034112194a1455030326400084440c901c4041d501285603810355900c00015540b224042d40200700608220b00800e005488001c10441081203290b03200d43e45030310900c00d454450141e00f084070142d013041c010154450707440c80301d02400680d104000042550000035000e40103080c1d0348500040c0e480d03410b81800a036200403c0058420820100040081d00c414010000300c1c11402e048000c40d4110300c0c001503080304100402e48607038006559070b402e40e00380a050004580076690f40c155a08038003040c403200c044055010782140c1d040030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 628356160 1250 628354910 628354927
    0x5040e0705090f1e0909031216090305061303090e010e130302011d0f010c36120b06030708011a0607020d02060412050610270902152d0909040305040b 66
    0x1340940043c0c040115492219a036030216100d03942c0c011081080c81c060500008601076103130b40301407160a104c2070b1500c00c501940743d40714a840c084082e560092020841c0841c9014150b03c030700c0300b102030440c071224807035203500d010311801038503070090141d00110602c0c01410007054000d5000685080320b804c02c080d981c400030840e0301d0b121a4058041040e075400c0c10f40e00f0000c68030030100c030104401490b6040c0e00c0f11110011000c00c5000108100340b105100140115810b2107007608003680c030b80b20340c403807000d42d01d020824581014216030044000317030704040821400f102c5450001c03000c02c8003601c1e40340c1c8038541c03400010300851064001a4120000007404690703400011580d80f040741c01682264a2500c440c2e01c26460070000f4440d62190700000458130040070816a0100c04412944070b01180381d1200d42c0000342052040c0c082c0c1a0201d00000d00d0803010070b964115010703244c40d1421100300130b9889202c480c001e07100d000c404038801c0a580001070f0801d8051800e1300d010300300c41d1b140162215881c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 628357410 1250 628356160 628356199
    0x302709070c0b0a090302071511070902030414060403050a21060b070515010e010b030405011b0203040f1a0d050c0c0a11090c0c0a12090306110405010f05040e0705090f 73
    0x74050b903004500000140355002c03a80075002060ba419402012518601030a030071080d07109148080030003903c0031807140e44400410400c006801c141d907005a413414580f5145030307600b41d04803100e05d85401100801005c2034010058030440c4125041502c6801c00d08843c60308801180c10980328045e140200c0400c61805c0031025000da10700c20300840c0c601c1242d0380513260171038070f003485074484036002000103104044c4a40d01443c1c0242c4164004603454040c40010035924903410f200d40300603413010500700200d08080c1c82802c01440a10b01d8210038000f4040d0000e554450301c030200351000c0d25000405d08284841040321042c0c036110040c1c484440c91494030b06005100350405a1107400341401081029042c0e0048410070242c0300000c102c12409681c0301d000ba6450f030030030703107050188101000010174954091720101d1030460b070180e60ba0302d05000c00506010b07002a0448200310b0117100c1481111400b4504981240607070400d036840d000004002a00a044030b03808580000c1142440140c0b0317003d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 628358660 1250 628357410 628357427
    0xf0b030604110a0b030c0a0c031704121e0804140c0307120c050105191101061e030c06080405030a0305040501020d02120f1b07030e060d02030930270907 67
    0x6048443d09603155840103c402c04d404243c0345400b07003803010000120500d02402d074044115101341481105451140c0c821480f05200301c609441154007000441e9400e07034406a00d4089019007060000c6100c001031f00280342140c001d000030801000c559981c07400350010800c04c403070094001c0441ea0313075035102e480f8583d8809039a00300b00d5590078900700208080d0700070f03000d8520f000c0116946041c66020310a04550700e000c6c0e00e6807400c81c1c0d5070340c0c0c6002c6218201c54900709000d000e41110a036641d450361800340c2e000b0700d15521040400ca03c0c90140000680c001c01110410101c1740b902041a44a50605a0080c4180020020400e10001c0c00d81200403150182c00c0c030924050280f503025940343c250aa600d0708420741c0140c401c0d0410085203000038020001c2180008003c0e110714200504140d0310000c981c0113031451051640401101581e0340107221030402d0b00041400b006000c03041d001040d45440c0614000c0141c0341c81801d46200180ca1490f616103c00a0020001a180d080c98103001c0c000c0c86 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 628359910 1250 628358660 628358693
    0x270f03060f0203070c030c02151b07173004121401140c07060b040515100e010210020c011e0e0d09030803010b0309120c0c09070809100f0b030604 64
    0x341001e1000d1820071441c426a4441d2180340c880c4c1020344c14a5600300d416203840e000490744042c59140d41505003040c4005803c03104401036098241c1420018680c3c030f050180ea0200f1609003034200008211a00440c100a280c10700380c800380c009078000ca12107034010204000101000e500414002003201a614050141500898007112410700d202481401d95034903081c0b0301c10505912000c40c2484030104c000b840010f0141c1000502c0314051000030341070320800e66507038848032080c881e1108503107031080b06280c1a070700034103022003400400e1340044c5d1203124005840c6038107507000c20b02c80280e0000f0740020f9040301001e442c501300310a020750024010304074004000319900c40c01483c0c0201030702401012003070702d802001050035a80b80500c40241da620007400c484007801780c95a40c0c42d60481d044090324002000381d01600b0441000b00500c00030200c0101020104064081805101880072803c4003a94003101c2000c05d1400000152030082d06010026907054818202084103000e28000e421a000 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 628361160 1250 628359910 628359923
    0x705071203120e060709061d0603190e0609100f110d1a0109050d0b100f12050118020d0f0809060c010209120a0213051504060303050c0d03061203270f03 67
    0x1003c20020319541c50104403520004036034111000d10910b8003030f26080f50340c0b101485103003c000040c075021501a41050b0381c41069060380103101503440c1c0303d07030080e51640340e4840001e01c0140b0301524100d90355039031041210700f01641c170802018903440580010101140b61840d040c0d076940a810400002d10010508074030161222040414941c80b034055941143c00003410a8910b08464965020743c490107400d4400c00c9440300300000d0618910030b0550002e00e020381e02c000310641c050a0042c03d45150042888202d00503900b184010f94600480070744081c3c0220015034900d09030301e44201c50744100907107149c0c020300103c0d00d030a8a19054008114603101a680100d85200c91000a0b540351580d41c8025400480c0d80320702440745081d40e202ca41d1015820b070f044941e0781e125001040444000d40c20940002d10000b039480100f00040003002865038007490100545e505d440315070030b09070482d0b0800508100d04185034030008d8a0030300510801c0743d91030504001c0c0aa58000c81c0411442a110440b081e = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 628362410 1250 628361160 628361171
    0x4030c050a0b090a110109141512041b08010501260f011a0328031d0d0c0501170108060105010509010302070510090c080102032422051e0c0f070507120312 68
    0x240d442034140200b1a580031b40c4041c1d03400f08001c10400700040490b03000910080610403c0000f0441642e152f005030301416a82c2c64000a480082a001420b40c0100d491613040000422501c0c3c20b030002c02d024800203c21a10901c10082d504a0074166040e0b01c5a0556080c400080e584c40c1c1180e401002d2080c04501725800202d62034051502010300d04da98941c400d47d4240b03e1004a40207990310724080d29001c840b10003a902680000c1c00c4841c00c020207031505c50050724280050750300040081030080c3c10070741d805007940c9403408217030b541c5505001311410002c01041c4140c05074005d40540e00c00320f9114060b0f440d1444004030030401007400a01c1075400341d44910001a0b01407041c42124040c001c142d60b2a00f10800c4020311484a0179030056090b0030101d640b4030368496180b0946007111108043c0c1001c100f0381099041c4050b5407284810b0003440d80ca0040078000095840d0007140d550704810b64200340c40b1000d6060013414045954072500038144103164240805d6441740b40d400b00909170034020000d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 628363660 1250 628362410 628362443
    0xf060b0c240c031305060910050f040f1704090906020310050d151112041202250509041b030c030b1e040308060310060b0408010c0f02030304030c050a0b090a 69
    0x114460914000122980c070000031541041d03003000110790009510008450020542d940e040c078001085070075000300d40003a03081007410801da0042c140c01c615503907666400b505081c0c45205600404010052a0850074254492040324130001da44c01401c01c940b0411448102c5e080231000f070740c000c1b64039450704080008085014640384080b0310425401c52921a5040b043c000410b00601c2c0caa141b41d4140c01c01400704132100042ea0101e1880749128442242008a4041e0084d1904c600741d1800c450b041780d002d1100121742c0300d44c0d03290301c104c030001ca130480515116800c00f00e4501e0300f4506010000c912101d4003000b840510320300c3d0030803684920000e45003960380c212501c2000000301000d615034000a00440c000c40e10610304990016401420344940e8900c0100100481c1c2c0d8a13480b000d10080085010080c240083c451604801c0c400c0c05d200c5c0d07a086010300025202d01c0f00900c000d0900141800f00018058204011941a640300c0174421450801c1084c0d02d90310b00800070101d903018159200103e = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 628364910 1250 628363660 628363693
    0xa080303010b030a02130b1602150306031518030a02060907090216060c111e07050904050705060703120603030522050a090902010c020409030c0c150c06020a02010f060b0c 75
    0x80c12284042e90752821610741c8101c00000e54880b1751a51410414244081440c072008401010040d038143c2d12080c0191843c8184004d0a0070340307010202d0100d05000f08031040e280401d40704610150003c49400c40d0741e070341e038002c05207030456500d0b6907540c40046002042c0d1a00010209d0081011344116210903554260201c1030b0b110344840320003a803014504900006400750005442c003d10360901e1300d03a18500f80002d038500040508151a2102c100801c0711010b00103100c0c2f03c01412091311594075034682526099070718040c91040c42c1c06501c0010342c4606040c42907501580c60030300700701c1c2401455a2401d0042458000701140e074180c892111400302070b052007415400868202801c07192860b894003003520020841d502041e41405148011540180e46d0b61140204091190b2600700c0f11401b1820010b00c0381200760841703480e108401d07181e00300391074000005101641c0d04c080096a111601c01040380509483d58201e079280781440c0010900400080285c141d07000108100c0c2d007000b9440001c031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 628366160 1250 628364910 628364917
    0x30403020f0108040f14010c0e030606030c1909051005132f040803070f0b0709080c13060902030a0506010e0607030903080702060903030c150f040201022a0303180a0803 74
    0xa620000c0c400740403109501a01c2e41e00e40c014017500d0803030026165510344410200f080f034409100c0742d40d100307a19001250000c111a51031013060300140510302e401d2002c240c0d1211110105441900f8a03681520030030303010014000074102c26281849035081c0001c1e03000d41900c450082a100b20780c10520400005468481c580424181440840c000380411b48502184500c0d10b2411225003010440424082e608000421004e4401c0131680d00040160800c1e6080d498041c00c1002000200601000035090010740c42203103060840304040044240b500030780061009611a80d1842d0010080055006540c0c0c41644280000e888902c5060140c3c81040394a1040010003004190b0440c030910110326003030050035481d4030107080c46207040c48182c0001c0c9590000038158020340c1c41980b04100e100358030800f2542004851311061110305103540040c0d112005200c2040b00c168a00d14940403031000724040603025036010b010b0741d41e11005d8a01d01c01c00050012074080c0604a110030000e400c10303002045 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 628367410 1250 628366160 628366163
    0x703080c0f0a030507050f1809180303181c0c030e09070909050c040915031511041701060e070e01090806091e0c03060705030a0506011e0507140a03020d11030403 71
    0x41c40c0b8006000e00141c0040402030b21001c1000000d0041e1f0000d283e40400520f2110200e20303001d400307420900100418541c000385030000e9980301d007203400215075001090b80e03082091148118104080c28001918180b140000070100003407020b80319001d907030001691900303d4029503030300107940d0303810701405103010050340c4003800610200010445800b0551041d900190300715042c5190a6441c10341c030060b240e410302c40c280c0f0a80580c004100b040f28a02000031b4071503040e00c0c144814140e0201122960296208a0727108028081400c400d14000f07500180103001441c1030103034030741030442c00100070300c80d191031403408189074031030200d1003050010f2294031071300810000300b80c2844401a013003c0030b0004a81d4113030303038405c100c00c1c0f0089507000d00c0082e00c01c41c015511513803203203013103c009020794401400807410b110310010305078051048082d80490301011402c0c0503540b00c0c500d140101c000d5503484200502405040020780c2016404607680300c0c540740d07a503192040b84c5c400180c1c013900e81c81580320 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 628368660 1250 628367410 628367437
    0x12190f0f0e191203090f080f0c040b040216050705040e0601230102070803041e05040e0604200301050109090318140d0305160f0201021c09030f0f02150703080c 70
    0x1a40400e82c80e28004080340e00100700c50300000960741d00f41d80c0c22070302c0c0010f8044001c24540007040c00410203031a00c08004041d504010409445000403654403100000001402180c03501104105912140c0444048030110201d40284880c682130454940350300b4022103103d1410488400a4004005480790589402c070b810840e1a030149480d41c03181015101c1e0031070640c02940c90024002030144045d00081c44100c42c2c0020201c00c00300c8018840001d504982d10036880c0c104008070080001a405900c00e40c1714181840e445950000115900c88045805034036600701000860400056080400b11621030f48035446080002c0912443d0720f0782d14080d00400c50013402900301c0a180101c900c500c618080e090072842c120242044000780c010724101541e074404c1d00d1002ca003c650b070400500f01003038580b8422503819030004900a05a08040c84045c00ca03445107018001841010f0111010340755006200044200c01c820104402d03401902080c2c2c080b0340183e0004414908080c1125410b94002c076 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 628369910 1250 628368660 628368677
    0xf05100513020c160905060907081e06040e0a030c0605060906061c02040302121c0f0909021c470405070e03030c011505100e100212190f0f 61
    0x1120000250068802c00c0414403901c9913441055103000720600240c81a40380105441c600001070015004025140310f007041070b12000c000c0c080241c0040010107000040160005407640000600a00036400c0b4450070342c015407441108251700101d40005282c4600003d029503038070701040061400c01120141d822001c10040c5407041445c0c410702c0c42c0600f1041000500b4036880f5004031301c4800c1007a03009400c40d0300001c04003054421305100b000c20407107945010340200180e400010404005032045a86058000c1080082545008400c2c0841e80351300c0d10811030a25001d10701c868030000c104100c04010140800120307070854098103960b2030034a054400d01145404c2080c403008200040c403100030400300360300030082542c0c00c2c03005040c109000000484d98a440d1564615590041d901c140e111343c403004030681c0c40c190002c0c0140030800040380c10701c0c02c0803170401041c0d05140344010158200712001480b481429080d81d05600440c0441d910300c1032051503c4800d850211024007604003041581e1b = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 628371160 1250 628369910 628369939
    0x30c011d19140d0c1103010501050a170a050111190801030c0506071b06050d14060a030204110d02040305070303030f2c0a050a080a0e01090e040303020f1c0f051005 72
    0x21400074101c0c0e0721485240c101400a0075406080c200d14420a40014004068000920070184052400f08008030006c00aa500d4800010341610181c452015200141800f05005d001c0034085000000c5d0020001d02012485280c08007150307101c1411124440e0783c403001015071034815040d460690340d200e00314074809801d2404005041d086010115a40c820129a0300202c4a0084405004141d80d331900e688984030380c0031000175143c80520503510002c1074810442e49503104000c03003080fa6016140001d03038801107207003500d07a84181240d1003000c50000400200700400020040c046902980d005c018041914205500b07a13000e282141419040d04080c102c6031854040d08032078100315003400c40305280099541c55040030100601900c0404012a600182c01d4003c803030340c04c5101c003d20703220a000e07003860705030f4030b1040300500060200341d400b05080250003030680480311180c0303003281084003494444400601402c2074503400d606841c1424049101d110303039103140c41c0c19604028410006e40030130 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 628372410 1250 628371160 628371193
    0x903070b06061b1014150a050d050102040806070519080105030a1101021006030c09050c031b220e0702010c230708071704061b08120709050301020c030c011d 69
    0x10303400d0b0082445610311814031028081050b207241560381c0c40041843c28017803082d2495500c00401100b195102c0f610b82510f01c0d0740d4010203c0c240c074021100c1d0030145c1070134207069009001d41d030800385d4544a00c0e0184403690760060060f01c034001e000c0c600b61400700310719542218080c1080c07148035003552050140400003808582d000c61080c80c184100d0f0075094048020b1400d42e4541d034416130308030801c0318050000c402d66008080d803141c111b00c5d5540c03860800500002c1641c0800b0b446010130300c80818a04e02c10245a4410002d240303042113946509602d070f004000e041c0400340c400c04003540c60844074103482401140d0112000d1407414550f03504005001100600d80c0c40140100d601c0e1303404106143c00159034014524012164080c4162140d00b0311401400c002040c04500070001c0252140384005812441103490100e070a80c28400f40c0d03164504181d4034000a5007140354554008107002d4503100c03001001c0e0428803c000b000b40044074840d09040c269141600b48846680c00c42c204207640c0302c50 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 628373660 1250 628372410 628372417
    0x303010321210908030a06030c12030f052101060f080f01060912030e100309050d09050d15090f050d0e090f010b13030f050a06060b090d02012f060f0903070b0606 71
    0xb08180041110800c903566896184d01c100c62100581ea82d0300014000d10540814a4000e0069a0f80303854040042e61009849840042421020410006820003104503d41d99990041c01c44601320704180d61180d2003c0d00222682c03003010001b80c0307200d0000d1850030b600c064450484810b0b4030350240349030074020103048400001800350b0038014440c90700041a01d0300440a004141b0560380018003076690314203681801001c0381e20004020f01e000301448659030304410383c4140c1c3e0384944810040710744c96413810081c003410f500241646000452400a114000c42d4080c4032a02555844010509220800c410820150b882c020361070f000300c00501000710507074001c080c00380302c28011264180d1707242c1d2860301400c55800c0403140ca80000c1c0e266410002a4003501c40078011114041d4244000d00c004108a070702c00420107410407002200e40d81d550402e000314100c0c01c400e0384001a0603008a80205070340c0e102b0a807614424020b5640c000381544801000351480c1d25803018511140341c40c0c410801c0120b40 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 628374910 1250 628373660 628373717
    0xd051804092604082d030a020606130905161a0f03040b0601020f03130e070f0f030c0527030c0609030d0806150307030c0e011e2706020303010321 64
    0x14010800030071130440801074000e04069074481740c6019011007480070701801911503804a00d6205008003101150042285030344030000b034400c031203110304e088407001c013402c0d404502401a0040c600b104240e00203480c2c1e0b0384203803281d40700100400043c2421228a07480b90402d500078508061021800089c01030007210340102051045a2410001400090031a80005291110303c150810204004020104059802061030403e0803840d04002c4003d858000c040340c0d8002019a01c0003c0030805001d80207660802d0314146204802c1d21120103544040d00d03070690007510074400d00390000500c2c50408200c42c01340c000603004d040c007400880e1041c1c612420142c00030f5800455034444000325140400510f201c0d811342c0e60003003506403514002400d1540c80302c040714100504410240c4a1950a40d50101c0300400c2d4506154040390255082840070300724030b00810183c0c098440001c9440d8000095810380e0700600c2d215002d03515508071107400c1864201a40007003805012201c0e030520280c89000c0004 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 628376160 1250 628374910 628374983
    0x227060406020a140309041b0e0a05060a051b07080a0312020a1e020f0a080301050f090f010612060302061605060f060d0f03110a0533130c080d05180409 67
    0x302d8940001000e03540c1c41071080c807011120701c44814003268002701c4218004400d44011031b0090030b18012400d54861803a660080c0403001410f015503c29107204082d41d03010520550305200c0d11802801d032100000d1500b07500003281e0030000b4944809074030880306441d0032511841106241c1182d6099003611004440d0258083c0c0303c03502c1480703c81840b141142901ca100e200e0703030345e41c100000c01c82c40b042281c181d640079180810400124420340c21390030341903500909011500c4000d588016000d0420398000942050010850003618011014001c241c9031041e001c1d10b0302a82c44281d2a2a5000225110b6501c00c1c2034a820340042031032000040c5005000e03103440784159000c1013480d0304d00701c0e00c940c0c103d82652001504100784903100400c1e200c0b02d6084010709500c5040340c481c070f00c02007201a2070740ca0040f854a95440800041c1c00d2000e0007401d0400c1a1088000c8840300500180c121070000c10402070b6603600f0714503518140c0301c0d01d504e00c0d84c00380a0100c80c2c03c030386401c00502d280c5c100e46503030790 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 628377410 1250 628376160 628376167
    0x207080a03091805090c060310170703061103150d022107081b0f10021c03050702100902090a1d0106032303030403021c120227060406020a1403 63
    0x10800034403030442014000e40318038a140f40350109480c501c030721900500b000c0c3d51500e0706119540c0c034082074588180c00125a041c0e00d03078070380e02c10100702151716901410b00d0702a041c0e00c0508101021424104481c0503510401171041800c003071440c01c0c40100d60b04c0c04440743d800010041860501030414600e4005000c154800414040100410300d604070b101d0344541c05400d040142000800064505100144c2d006074040c0d058008070b241d0061090303525101d02442400c0c00c040178802c000380e4007030b071600c41c4491503140c0190f10060300800d07068500c080140101aa03e01c448101d0340546500b10b030307015241c5800e50780c4d02407500d4020700c08120601504502da2001c1c4815a03000d002e00800303540281d1420211a01608002c080da4031403181c080d60582041c020040801e40100f101c00d01c5880e20b405d412065004840219000d9008000d080c4915102003446808a003541503951001503080801c02032218400e82000441d008a00c81c810059100d5001c0c4030006901d101100311500d48013003180e04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 628378660 1250 628377410 628377419
    0x3020d0204090c0e090a020436020703170c0a0819110d141b070f050a050d030504020306062d0d0609030e09180a14030d050903030115110a060c0207 65
    0xe07510400f00c49400114000d80344481480d0581c0500d03040840c90380b0841c60240340040c0040c0c0032482c3c1c0c941100746900000340c1c000391901449a20340d1a0700c042011907545c002841d000c0d00781003070341e00030a0903001c4480002d110404010110b601c2d080c000d480303c110744c2e81c1d170081854456a85800c00b44400342c0f10f055841403a91554041d041d0452960f00108040c0c600f03841300488004000d000a848405c100c211001007500c050450703452942003004c44440d2412828024944601c1140041c07403803060440000500380c0c5648018016071084049d2443e9440d41c0d0704000758440844c440911014508080c40d0317190407a40b401010042015115555600150320307000102e656a00050300072a6404880f69610702d480c01005a125003031081c00710995068903007150ba141600c4000030f09424254800c0c018080042050300c121030032088040c4407070710f4220840d81e113a8100b03100b10b510800300c60500d6441c40b40100c1034803076a4480034008000d002c80d56142d075400b030402600f60300158083c1540214 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 628379910 1250 628378660 628378679
    0x80c0711030607050406031406100521010e01060318050607030b151329040e0c040803030a1d030405030c0d020406030c080109050c09010b0304030c110607050c1201050405060703020d0204 82
    0x40c4203e03080c0d115030307450f40d20b042806001e5405541c00c150455080000300446560b44055480c092a481d150450721b4000200c0c01e0840d0700a102042c00d0040100b80c000140d280c2504510350580381c0b240e40a100440041c04d083c0045041413000624a070050000100c0c0b052007580500c9448070001d0005c4041d4100b03586c62145035001e008003a000b81c5e40071005011912410700c00e10b008800341c101015003112070f1003c40207c1c0c0964020031554414400c04118512440c1c003c0c0d5000c0e0a441095940c1d80c108203c11a00502000d41250401c02c5242e0f2011840c1d000803040d60211103005e0080d0075091008010040c80d80b040b40002c90b80a5614040407001c01d00c404400c40180c101900002089a4103040c401e14141c096105180705540003001441030340b51000030389400683c10f00f0001c0ca44903140c54042d8407440100d84654100c0b0000ca6040b003401800150381b59030342000c7da00c2c2c0030b01c0326402ca80b140c2a541c0485024040b6400700003c540458480c0d8000c011108402e03800500345921651041c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 628381160 1250 628379910 628379923
    0x2130e0705041805160305030403140304031e03090f0503030a0c050f010e06040c050a14010507021f02030d05010f0b030c16051b040f0e0718020f1b0708010606080c071103 75
    0x4000d850748081a403c000c070400c51580240c0c0204d691508252840c7d903a5a80ca100300e0200900642901d00001d0600108205480c061680310050701d000d020900075605000c240483c0070b400141d9080d07400100c01011607118025258050013440c5403400110b41500d2203c0c12075400c03122840340d150101d6240702c0030b1040c580c0140c4a00c2c090829400d082c00e1030800900141c20140c03103040d800380e040000c40001e01200810040a0800d903458444071700018141d41000c6980d0310746018890080c0d00c006901000030849a1011001001240d80300c058021105001d8050880c000000308003260300880c1610203000b903192208050200da6003295030702400e2401c014104003010143c10902ca034140b809005000c18160a01d408008400900c413049070303030f0381c014441c100c0100c030382105040c035110080c1c046925580072105003d5031641d14091050f01c8152304a4504054005d665000c1078010042c01204111005a5100140350325658407580303180d8000d00c400c40d07192050313405440290f102403161 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 628382410 1250 628381160 628381181
    0xe0a080601050907030507050301150e190807090908040303051b030d0209010807020a02100f140c03030106030b0901120b06040e15040b0109110d0507050c0f071e0302130e070504 78
    0xa00500c0d49003805200b61444044c007208141402c02c400c00007515488025030741160b1042044114040e0210703400d485282100d40c0007600007108402101140303007655006e8040b22283c000b265541541c44a0b82001c5034505440100040400c01081012038402c4020b031403070300e070640d8481001c401ca03407501514580c8049541103100b60040341050301c0350f812010312a40800765001070042c11446500080c202d084d40c800075000d0155046c554080c481c0301c0c03443d003958041e0075a02d841e69601d885400d10760300e030824400c10000a0902c100c2c00c9943c203181105504030381c28060a442c0c201d1440e41e4000300060f00514a0380c21690b5001c03a60607096082119082013440420300c0e0030a0b060500b4130b640003400503005155094100100780903217110320400c84440c0e031901c1d0800507a940721007004907501d01c58120200132504c00c0e60080d1490080100319541140d42100340fa80a2140020401c2048036451201030b50021800c0c014403d1920113070131925050b8686000d8510071340d211000941201c2106d5013 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 628383660 1250 628382410 628382413
    0x3080a091e0501171509070e030a050616020703031704020d0f0b0406110a0905040213050405090609060f10090f1e1d06040807140c1c110103060f090902010e0a08 71
    0x41c20030a55801407400903030a40c1600c0b03018154548903c00c002d050802e60141da00a11950b00081c071600c0c40b50355448410b40c0c0080640b280e4428501300141d4801c1d00350781c00e803001c00c1d46c00407050383e032070001507080100d90349510380703041d1100c846070f00c50301c8a54020000c0e81c110040010701c80010f1000d50701e21100c00d00c10b000300845030038a81004002c4911100030358100c80020455104100d0f0841e030141c0448030112030140c1e5a03032641c8214000d80e155540443e8001d8240700500011100100345140b06802007002c80307010b0f643c0e80403410b280100665418100e05000d28041c000e02c241d0744c101e02c2040001003c04102078501c500415640c1043c20b60901d0300c17540d1114194a0f5040000100c01264400c0004003080c1c00d0944039821544118000203146441201c0d21401c4001c050200b2032404074010b1485840c038445070042568101da903801215409400c0b00308121541c041d22800d015240d0742d04641c89002d0920784d104004140064090b814819100405505941c40842c03d00107414041c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 628384910 1250 628383660 628383719
    0xc05031504151206090b040b0613060f051507052d070311060325021606170705031b210106020303071d011209050a050606060a020703080a09 62
    0x240540c490104212a0038459070410384925104100741d0801000e8903400c0e0b5030183c0b00300103031130840001c0c82c1200c40288031040403402c200601c00041000380c8102d2051381c0c8600c07048260004101110407600402c5804103005606000e14100040b00c10324034901c08612500c0c0c208940c40d02e07454580e0b444540515406401c90300b501510001419001403075500e8000e08072142107507140070725107000410f00c9007c0c1c0f50203c0000d44148004418101301c0c0070b543c0ca2000076021401d0000e45031000080500341640100600040052094030391962802a00345420810340303482408441691000d1300301c4450340c441c1c20400b01174010810080886610356204413620b250312a00603082d8202c16032080043d50400d00810400d141c00c800c000c007000009841d28004480d0f80da005070351030004181046d058924000c4460100070303000990800290054080382c40d141d903103c013088290300c5200404d00041e0400e10003080020400e0b40548030200c9a0304000060030388640651000d419000d00d004030031107100 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 628386160 1250 628384910 628384921
    0xe1803070f0c0b0408061308070b15090612030a080411040c0908071e1203090b070303050f0105091509090f030703120f0b06070206090409081b0c03030309060f090c040c0503 76
    0xb04007420080c401a5406428240381c50030a13034071039800919000c12242d03811024003c011b102c20031108000c6e0b1012130803907282000c80240200c2200030210900840d82c00b400b04150b0702d444021026141003c0340214030b01011030000311081c1c0d501410031100c0141c280cad0342450350307911406590701c485040c0d80d942400c14074107a076551070200c8680c810f4429039044030b83c0c1001100f88040d003000303170740e903205030f0310389101103860100c410303903510b0b402540e1030078010034040d0400d60315800c80c2c0c1c0a40500c002d124441e90700c07481007114a13602031f940403544190305c030541d2084e401e059092680c03004942c01583c060b40700d00006203080d58440d407011400242c08000c80700c40481c5034800c44800c28801c0e030041194885000202c2d18500c01c1d0f0310f01074403c50001c60880005da0b90340c0c100b141d501d03034020349594641180c03080841c00030b60112042c84441c0903920400505040003c1030707034440c00709080180840d0302c800c442c011003020302804150503800b8964400a46880328043c120320ba00300c85d920340d83e40385801d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 628387410 1250 628386160 628386173
    0xd020d0606050915011b030206042418060f11160f0618330504050c1207061b0803010b070507030506070504090e1501231302040e1305070e1803070f 65
    0x18507000203445801a402c6c4004ca580016030f40c0e8003075403045401c00c588081840c0c0308110311405005161907420320355000b24502521104404041c070502c82404006000f402c00300903110041350442c0644000c1c81001709111f034164030803103440d0086544211414250722640b00380c50600d000c2c546c11101c1100c11800704505c0070340b145070b00e00005841100d948070600100c1c41d11003010181348c0c1d01075111000b0a05101c01403003408070f00d4500600d600d42c1030a40040c440e85408041c4078501c04220b0902c452174410000a08541d1030561114480385981e007030848510060f040f00f58180d0f0309201e58400800054020031186d800f0310752684400e615a45045581b109452050285400c2d40c1c000c030419142c05040302d2074903415107064501c400d00101504072110711076204400802d41c031400c406921045035101d91b0040090f9501c01e50a00b000d9518110303100740914411400502d00e9200c0c031020424000e00c207908940102c001c80c50401d00d1124548030502d1038120031030030b407480006110000e080208 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 628388660 1250 628387410 628387427
    0xe18220218070e0909060c030c040801090b091c0206130c051513090c02060610021906020403050c01030c0f05130b040902030609010e090c011805030d0807090902090d020d060605091501 81
    0xf411180080e00d89088040070b6100c0c04040c02191003c8004808140103030701d001c0503503011b0135000d002000400b0150419444035202540c91b44454001e900d03c031601c1594401c100c11408501d030f001880760743c4507103221000d10b040b80242507840f0074403a00701190076503e00201384000881d103000705444601340f03965002c0c500c400750720042c80545000340003555290003054071039000c1001c07a620710000307e21403416828480d403a40000c0100454407098010841243c2c060801d8a00030012200e804c1d071507100641c1200ca032040504007282c06035400c0803845100318001c1964030415038440c0101a9209898081078106811542c10b59402104110243c244035552500414251421a079035040045940340c0b2181480900c904012002220560021003102c0703640040c100942107450007540048028441c00040e0f0b140350004542c80e00019901049000f981c600010040152404200c26400c10000a076000e508a60341600da00001800f5552000d00d2845038195140b8040500103180c0014609003 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 628389910 1250 628388660 628388687
    0x50307120501120809032d0c0405090a080a180603060504140421020a0206031303110d0906080a0b03010608010f0b090906010b0f070507060c02010e1822021807 70
    0x14500307001041080581800610300d01d401c034140caa43c1d8410880443c1c00e10020416000b4020f800751515042e01d1207000b8400840c40c0300c0420b0703c1c0c01d50701c01000c002c01d0716002e43d06060268000442280480d0088008165095071428500040014003036112081034481d406040881d50380c040810090030540554603805048140b8040030f4a4030b951100c0701064841d801110071400c02146c0c9500c1802004413a1540e50018540c64803441e040050480c10350302600220001014404444204413000807052a00b203c2038680055a90610104842821000b41107948075500c929180310b007901c080c4120005840e85c440045112413414403d002a20011810b85e03020f60004d40070420210004109107040d202090705190ba07030f103901030203a40940035a400107001070003141000200d00e5044070a001e01c0610070f032500d1034002c407a2020800110b44804500892081e5076000480340c0d0074001072041788840003c03480c580900203402151000401449040341d402000e0284a80650400e200c5a60032 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 628391160 1250 628389910 628389947
    0x81c0212040b130c0e16111b03070e01030609141506301e03130506030a060e01120b1b07060507140c0120040503120a051e0d14060f0f0619050307 64
    0xa4101d4070407e41e513480c969900070700901d59450ba0190a0f5000d21980c8000d010303161008851317507140d05106000b8101d0901c00c8031018080d03034a400840030003240001120014409000496645101b88000884030081c10030580030386405110040034031900c5200c00c1070741280100248081c2460580c003169101046a03503984c424805078508801326000c203015150b054820300d840ba00c0e240c82103800740010303030018170684900c10004104480340c00e80c40c1d007815002e0112081540c0b82e013011101500400d840503545450204038030004140c05030095a000b10051610f034440319240034100080350880d0f042c1032102e9444014517032062440303106200180d2049858036241c01e107014002a65140d0351604556440d402080380030700e69002d00d0640e4541040403040b4440c441008010350703440d92209a2086095141c0010703038410010101443e8070800026100154000e0b50a08000800182030300955010000f0000039038101c181c0c03101468124141e0b00c445890f070031318650207800c07044800100b0400 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 628392410 1250 628391160 628391177
    0x14010b0c0c040b0d0f061d030a031103040c0506070201021f0e06090313032d0807020108130c090f0f1a0102060a05090c010e040e0a081c0212040b130c0e16 68
    0x76640e40d9210300051a4003171a1543d102d081e80c90504042d1400003114075903801c14401d003139980d440200082c03103c078190303640801040740803c40c415805d02040c1e40c060300e1009038240c10303c8141420b1000b13000700742c0140102d0300303030103000c8928010701c00c402407101c000300fa04c03410a003034000c004000040e00146008080d500301598040d000000390014400a807040760f000d641000c2c0041c2104031102d1040a5000005c034225103030410f030a031031380301c0c0b1800c0340010948000168101c10881d00855201d0f881500603040c64544004500581041500d484001d6920009000e242c09a803148040010194200c90708500440d400a81404402030040c141503003800d0400031080c0c1c000c510310480c0002424110100100800402c0061000c01402d0003d44520f8050906118074003015001c1d515042910030014407900740c1110581c05a14801001c2d10520408180011042140b0a5219169003418000d42055072110000e6a20340d902c00340c24080d08900344052075102826515101c0c5030340c00c0c460034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 628393660 1250 628392410 628392431
    0x1d0d0201060b0a08130b0901021201060804120e010e0405010f060e1801121110020106091a01082202030709060816060f0e03010f0c03021809070813050114010b0c0c04 73
    0x5210b075054400070421352400045210000c5403000324040d07042404000c051814a4195000354400302088260230088000011403038402c0c00c05500c1640e125201d03441400c00a04141c07041141e2400141c103014201d55a400a52074034400d4a00800d00402041c40e203a203045005401301140001e9a80929a4140c0200710003d8440b000c81c1101d00b080300312407928071903041460a2620104d00301d50303c00004160400745940c15040b80e000d1b292a0201040410f1130454407001d40006015054049240000002c402c405c0d001a190603072004c01c2c01895810b0070590000e4140880750b04487d4606582e40000e012070134080051070100c0f030760801c0d045551400c180300036000d9405040708000300f0845030480440d6071000e411845003802c9801050141d0200400b0140181d04151541070348003405042268444c0360000405005c5c024035266201c040c0c4880340f0b0079001401540081c0e40c1176482c0c407402c05c1b84081088000740201901c42134580c80e8540004000d0901242011040c401c50500b0749080d07 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 628394910 1250 628393660 628393679
    0x3070503040807030905060309030a020714030d0810080d0203120a0b06120402040b090702010911030102190f03090219090f06030506060f040f051501090608010e070c0302101d0d020106 81
    0x250020303000b024541d254a0b951808880158994000740c1c2c002c403022043c8400c0020000152090910035000c0e10b6485480b956456520064441030683c9035000312000c0400e240689125078010340c90710203c901e03031515420b0312840c01c18281001700040e0300c00513070b08000d070609019407a041030741d4400c140980c0a0040014085d8024a4414002060900042401c555841d882081507000c0030302401d02c1440d0901d00030b8000d06c02c1e460140d0313913420100a0000146018030844510059100c0c504940003c68001240c82042c10340d003034424556284803240160359a81401c0b0440c07441050b035082203904064418017a5850402e5022016040031010320001d140400c07030941c00030055895008d01482000040e000e400d041e0942030503280b4000c1401a08040f041c1c03da05108400c0c3c1320303403503601c0d5075441c200c0d8505000d00c1340c19070020115001c600c5e0705226020714a14a8002e1048039040c00c036505203002194403092401601c41d9030a00c41085c016028000101d0524190008010680c54080c628 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 628396160 1250 628394910 628394917
    0x30304030207030b060d15020c070e0633040f090b10020a060c05130f060305060913084b040b0306151b0f1915110c100f0605010302030705 61
    0x4100d0a00f10000400c5506e41d080d003211215044a0a03c4160307840f2580030009502c04401500903016440d0040303201000b51031490b002d40b00240280c2500308120060300040d5030395110891194002042c0810f5560341ca40c0074001810b801c1042196103442c0105880840300106886805072444a08402140d5008550000b8840c0c00803008030740088058411100c9209055415007184081a0042940710f00390007400c05031004e03504e04201da5100c7c00208035200703a0440d1946000c550a40c621b100240449001d04084070300c1c80900740a2480c240c100141d00206c40c01c0354909520012620030402c0d0484402d84000f101d05840540f4140c10002019581d100003010726000304103c80e12941d922000c10202c5540604981d1301c01d00110805009a4030342c41c418480c100c0300c1c412982031001c004541c3c0082e501082c0d00482d0007c0200d164400840a80702005007425880010300141400602c01c5c07141166a9810540000300c03552003041040031259140c00c02c604051062040114050300001103 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 628397410 1250 628396160 628396163
    0x80c030414121b030f010c110c0402190c020607020907020f300304050f0d0518190311012d230304020d050102130b03011502010506010203090609030c06040e0108060903030403020703 80
    0x4220943c0c9140d010074030b001e082c02d0b07040c08690b10b802016848aa401020440c41e00d001e002600d0340c9102d6030341000264022a05400000d14841843c00c2d210313805a10103420042c400b4020384d0601c00950009859120100d50745409608a50050821100c06020700031000030300000da80d65030801e08ac51800d01c41e000c40b81204808000102007401c0c04000c00c02d03003c1841d0160200c540440c00884020216009200710300c880041d0203010517038078a429000d88400c1000300c0c448142c0e892554861a6920143c6c100050601207120926440180a40e014000c00f062091000d1112510b415000340203805000e0480403071803c0d603904d214010003030300860303810a80465070b00c829040d02e8240580244901c000c01d56124003100c0000030000e002030051812a000410400340490b412101a400e84000300d030864011307003081007620414903060001e403c41160180440c1c6804241c0ea0103c2d06c00d9000741c0025030908942c4004020321041084015440071054010b182941042d0340c01a6940c80d05000 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 628398660 1250 628397410 628397443
    0xf070206241509030601090c120515040501091b2d200604020a120c050415050301020d0506041d192a080105100317090d080c03041412 59
    0x1881c0c0d510080d500501080c003038028190701c0a116081c40880b0642c0c040c002140c000d01401000064403440791083c40c0982d6025110b0300381301d181480c110380060100800704415820046c440840c1d6444030b07c603c038043d045e184000214500c0c4281d0020551000c0022901000307a06401c50340a0012424030f4402103090f107519240100558a00f9103040200c02c1c864140320907001c008080c200d20000e00203000303d00a440c403110a9444002c0c68100034042ca402801000030907404200c1c0d810103900400440d01e140d45800c8520f070701c40d00041c1c26a400b048140c800380c0d4942090217a1440c01784034450219040c1c2d07220700780340c80c103160307c4a4039401020a110800f042d034003207000a00482c1862160000c0503c03803920301d400c0340d001a00141240600801801c0d40c83c013000102c0c13405c92070440d18246c03030b0000c040e9040264490b4440701c0c258003460b0b00381e4001c881d82d1807180024544801428804c042c1102079a2900c1c10004007250004090254a00c2040e8116080c2a142404202503820405048 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 628399910 1250 628398660 628398691
    0x20106091806051b0a08010e0105101e0302091e0a080120091306030302060f0a110405040905030702030a0b0114151206030705150c010501051005091002010603060906060e0f070206 79
    0x2e6040050321139202c116400e0031000a8400b480f5076016a080d0b05039200d9050440319a40c0310414441c1454800c0e4031800480c01451103031501c00712220011880042c9481c0151400c0101d80100d544050320403c25000503a03a81c81210342403a00341c0c2003074041c1c08080000c001003a002c3c80b030710319154505002c0301c0f540400040c07401c03140d0700c4107528032810b04102242840441e40e030740750080d6a0780c0116102440524200081031140000d801000c90880c00c810380c241c18541030000304002451045000c640d03a110402c0000e0050f1024480b00318414050b02450109600d00050b03070642c00b806400c0700d0712a981003401c04030b176040e03600d00b56403408081e104038000d1a038402340031a240c8882034018a520840345014110485100f00040810b062003400900c0580da0300e20601551310007900c520004100b007400608010304044100c050401c00910000c17450039501e0f1610422202c461100383c80c40d0352200303002c0c03110060003401c0035040049251030756110705d46640001d40f21080609500300701102403 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 628401160 1250 628399910 628399921
    0x2120c0d0507080c06040c03061d0606010509010909140103150608152d07090e040210080702030409090f060605030c1518180105121c05030714070b0702010609180605 73
    0x40056038694103443c3c00700c510600b01b03800c0c02c40300e010162204641d08e07030402c447c283d0281181c090100500c00301d44003d107041e80f1442d00550301030700401d40d51810400240c00024244042d4007801e01417aa010000f880c50f54118104001001c9011300d8080310b02d030415004201c14480041c21903e00400000d5403c070341e0700c03101c044d0b55120f1401e610140059118543d0415030b280100d500d54083c400316152916010b5031482c500c035038000100c401941c00241d1140103500703280107006c01c0d6442003070303441541d247c0344e01d480f020022a01104401d8410081c565140f0b010411988181f0f00540011801401005090300004078040134000e62400c0d02e0702c0204200200700300c032007403041602e5030041c0204502c100390446000010424490303244078980c01010745480d66404240c4c80b8403c40c2d528a112030820400e0800d5542c0e40c400ba0001c0c0801205010030444a030b03606001c0c183c0d1a100b90101e02c480d0a000d04000e007510169003007000c03024580000481180f07003054145034410740c010404a1550380c0c0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 628402410 1250 628401160 628401173
    0x9050d110615060c24010f0303020a0204020a09030506040b010320100f140a0e19150c020a0b0408010c410403020d0b0a060b090f041d160602120c0d0507 67
    0x400c00c40e49513074440c00e06090302d100c1c6000c200506643c402c01520700c00360798980f42143d6001e824400600980c000038481405420980c005050b1440c0d1030070a192035950740ea4801e45003070000c5506441c0d0079403110040c000c001031004c00c2c1c04c080c000802c554076201118800110617860b080c17000d60900550940c8500e496001c1e0a005560369003490145840d41e01c0094040c1c801c11460700c03050300c41c08100c05039038000c501f0307541c280050307503400c0409c0c40c0f01581341d8501780c503408000342d8103a0b4002481c4100040182e2040024000341c01803100206040c1c01210010f03103121680250280d401c2e08080300002030414502000401d00048961001403110035040c51040e031096030006074020041680d0031040c00401400180900d2084104111407603403141c5004480c000c0310003442d801080c02c2004501850a13400c440e20440030755960205840440e40c46500c3c1106651402c56511119074040000325014001c0c14071480c0d44104580c44c0c030074402180c94951401e61070017824031102066640038043c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 628403660 1250 628402410 628402417
    0x1030f0c0306050f060a1b151d01050702070501020606101206030f0302120403081227010b12071a03090a05010c0305190213050f0310060909050d11061506 68
    0x605080420040084650007006004503000f164042e0f0245808001c0034208074040328800c0706039507183c07096041d64088802450340c00d508103880700104d600d48000d840c00d0b0b40c851054036512070a01d010348095038a50013400c0d501e0090525040d900300a800700708690b004140c090340070b0300440b0341b4903200050400070f450305420414100221842c104001c070801c01c844280122680c069000c031003e800724402a40b8062040c0d001c02002d07680e05101044000d072440da1095000040351403802500102150300c11500e100342444107041c1c1c0e4454242c0d1a8274205610002c0180d564040030b0f00e021400c001d058141204000081d2000d10000000145030000900548011552080003070007440243c103402070140009444100c10510554045034483e00e09100b100c2c21011055520030520b8a05020001d44094a248090701800b62540b00c10403036400e44908805004800b000045031011401c10503c0c040f151144c8030107000090703a01304400c00d00062800d81c0b0a9150102c03503014a94000494203a00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 628404910 1250 628403660 628403681
    0x4020f01110a1a0907170d03020d0f050f04021c050303130218010807080606010503070e0f0f041508150907120206120c0a021002040f030f020f030d0221070b0112020103 74
    0x1031044400000440c26242043e0003612213000f01e03548940c48a0036049031644c00042041c4507840348046522075070090f00506289100e036a00010101030011248098607012511445904100c1080104500c0c1c00901c0082102c00128400c01008442e80c0756556880050084441080c40e0102c0350304642da00b19003415466541c0f4035980d01965940341c1d599689115004182c1c190040c0c60015800703500c1201178034410307106d9565080d074407003e541c14808500d00003480705030440c88400300760703109813103c2c01108400038408440c014818a480d404a081460303a5641d2074124a07124140720b0200d00024001080d01d107001c3d00032070f1041c254400103420b0700c5031450701103ca401c0d040c1001101d90003140603005c1c6002e41d40aa03035810a48200d600200d100d503000d40d203a0407085000900204180c41031558105101404050110702c01d800081e180c10b42c1c1c1010400181d00c04c1042c070b004402c0c1820a0031900e0b9038424094103061440d640c421011205000c0d10492000401e441800c0da88203800540101 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 628406160 1250 628404910 628404923
    0x106180e1207030c0c05010c11040c020f0105070504080714060717090409080403061d030a11011d010b1008010b1b0c130b01020c09040503040506090112061e080604020f01110a 77
    0x240c0390b41c07074064018543c1c032a0988070006008000a06075010b21700354044680e104007135000350b003805010840140560346c00001103207c0c0005150440000344190707030140703055440e0b00c0e0f195441d10784601d141c421070f5000382c0a6a010038601c4060741d1100030581c1c50003036000011007007400701e11100c9810b0340107491030740b0340c410309018440081c014004001d00a81c0d02440091042c1a6042c11441d1012060280a202030340304000c0e030441d59100c0c10f880920701302e1550000c12560100365000e510303040491481d4000381d5540360340c015a480c1c400348240d100d214038240302405600d41044180c1d030340070341c178101400d0390355071100b8101c2741105011495200c4402040440ca4451407a10000186110013074980988030700400ca035003d14002c80140c0c0318690040c003c500d018204010300c48941c01c04200c03141880076054040c49440950300664010b85030115010300b09000943d01ca02011a81d0740c01141035820038400d000250b140c41d005134803243c03028200700719000f2942d4082440c0030075480016018 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 628407410 1250 628406160 628406167
    0x4030620070c0315020309060a02131d01330f0e130905071e170f060103080a1214060415080703061a040507090e09030d0e060610020106180e12 63
    0x104020038000b241602e001e464064004021440d1407001c030310003640c0010260f84008001556100c0c3e64000f0410840f00ca001c00c1951a618806c001c58401403c56418004641d40014460404102030913440c11010402100c3c00c8100740b0405142a041118058104424000d8640720580140c283c0624500c002c2c0000300d50b0354000c3c280100030040482c0498540c0103049002468030090740404070001c03a654040c0040c0e43c500440c1000c440c5044da0519100c0c0603441e41c010300d00c003051140c3d0f40254040c0641c00d65516262000030b160030078128a0300541071602405040f00d00c040c0d4003291344402d003035800007000d821280104640b2046580b241d030316803151001c0441000800d810250000901c45054001d0a00030410081580c00840300c21001595181c010071008281e044050f13003010020082d246000001e402e01c000b52140c0c4645046c4035442001030101c50300b04041c50543c4040c0c907200812115042880602c515075240e41c2c00e5005a0f180d40300140048400d100003002c81c0550031181c0d07070303 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 628408660 1250 628407410 628407413
    0x605011b210e03010b01080106090905040c27050f0103150c11030d020405090f0105150f0d0203010e0906310809060a030b1804050607030f18032c03030403062007 71
    0x4180740300000c4500039402e01714039003a01c0d4050645036050b501540c458400460a01003074000510004000340e4991640c00e1001030590b550041201141d4446031240c0900c8500c203c800c0c0c00d8500151100074510801d2004001041c0710390702c1015014043c000204800184082c119115100c11203060000e00000a45090f40642a0300170400c560b000e4801c00da8681d208188008111000d100d0590042c5014810310524960301e002402e400340185120360425443c603102c44108d030402d8010004070460383c000e1100043d010418140e02c12200110039000e00321007445518030f510034100c000d01c090140c0b040f81d0304002c545016650b080c04040c0c1844c1c1c4454224038018040c00d45400c04900400c502c600c0e0302d20840d01480400d00c917a030404020622615400c0c811001421202401c0072502e507649000c000804610717034040d00c0940681e81e4086401008140c0039514041c441c5401d18003000024202d0703151b18040181d4084981003040050000546040340742c019050385250113120030300281c100c0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 628409910 1250 628408660 628408667
    0xc0510020c010e0c060d0213030f0b0612030a0f08070c0822050a0b0a05160b070908010b0a0503071a13060207240203070b0604150602061501030605011b21 68
    0x104440001d02000c65480e0f80280c4504086099503002001040360b214941e00756001031081e0a00d041c00501559640c0c2c96044903540400d104175400c03a0307a60140400c2d460060851a007807031004001e1440e0010241010b80000c40c1c4041e0b0b4424058040001111180142030880440f50042c03c0540d648611140c06403541c03465508a12480814071004241b5007851303581c44082e1001300b49010700d81510900b0588042e00100c1102c04850488284540016600112140108009d45410030038504221803182500c1207001c0c4540100c4100e14100446e544c001180f0084440003d4a040001e10b08030741400b40780b00350711140d50508004200041c1183c2c3c00117038202210401846040035444540c400c1c01580d21428140e00164018072901d0301251603c0c1c0e280350040c2000b00f001071111640000c2001030380b890f61141015130031607004c00043c00c42e4080c108003074000910f401c100403130400300064040c071080a0603686458814401c4403c02004d6484202c14403100421810840b46480303008 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 628411160 1250 628409910 628409917
    0xf0409060e011d0106060e030706050d29040b1c06050c12011203020706081b0c0c03060a0b0111061003200301110a1722030309020a0914010f18020306010c051002 71
    0x107881e139840c0250015040340700f02c160000c47e0b207005000c0c04003180791400844440d00a15200c5500c607a036a10503030341001c08110703001088000c50310013040c80e4030f411040104688224a049d03000784059000341c4580600041c589280aa104d0000609912480912a400c1c050041281e010240c103900106482401d44a5140c84500c240d0071a9001922990200ca140d082510345500e20801e01807501405040d8401404405420408680240900c00002480c0403c00d44408801f103a540d039040328203590010103810349002140013401c1c00c0c00d10800074840c00b0143c2c440904090800718182960180291f024410071784020000d11089199968880c0b840c1d11020440c0c2c0802c014990440101c402c048440d44207000c2421540100002c1c807007445204401c0c0b0b1421010075503100350781401683c59010b11409842c80c07000010708a5016010100c2c8400103030040c07a8003c041110401155000880718400d006a01c0c02c003585a456542c01603800304035507607000305203014000c441185561035034081e = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 628412410 1250 628411160 628411211
    0x6180b160e150c161e090e0a0f02190303080a1503150507090308120f06010e090c0a050708040b0304020111031204150209040e0d23121012060e060c090f0409060e01 72
    0x407445c41c2556078018904452204507440c440740c03c10030400c070205006028420302c030b0b4005000810299610840da40600031240c000f02e01180014042c0441041c003482071b800480013544014a1480c20b47c2c403440015036504002c0c100081d10303680020310161081c0e0042d40107641c440c2545458204040b8202c100800488003e4000d0b140d06000809540c8149469440014041c050b4907807070f19840c00c00b40c4a03038096050601400b8040105400140d0042c00038002001411070380d94403401c0c1403000502c44480e1506442c940e81c01802320300010300d0421201a009076014803d00307104a0080c001034041d0007101c0013150300c6442c0c114058408400414216214116507036a40c0070130307002d900c2e4488620303901c659842e1511014010607000c3d000448406810031201d442c10300c2100d60711a070295604901c1d06045510b20745a41600d40ca044040100c6608080082e01403030a051629001c20309501d44a10410300c910f455180400c01d00c082030703100500311800013000b440f00d50366000d044003042414501 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 628413660 1250 628412410 628412459
    0x303050a0c0c08070b04140d0e03060c0f0a120603120c0308060418062403050a0309060f0804020f0d201302030f0f0406180b160e150c16 60
    0x301440399100c0c106080d0110340c03001207030b81013241c00d840354150448000d00890703030304041102c0100c0652007040800003441055562007041410201031500f0301c2c801808603a11840180402c40f000b00c42e120564014604030701c4c2010700742c0030f10406800030f40341d1a40040c00005410801c42116a40050b018141e84c1c003d0710f80e040503403180d000303101c110346400507407100b50320004210500040e419000f013040d40241118030781494114102c102038000d65640b044a440d488484610f0825070412440002403a441c06c01340c22814a664018107c2e5400800091040144407038452503651004034014482e031704a41d446c05030028010310400c00c82120010203100c2c0202810100f9200d1040c000c892055a84c202e0040306170720b03100c54041d030300764000d0401c40c0c1e00ca44422200a400b40d0071001115614043c40d9a01d840d03080640002e00706034040e016600801070240c014000c261a0032042101000c1c0c01c01e104da50342e400450885040c600c80c0d602c1200c054460100000d50030300411111a07079200c0841 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 628414910 1250 628413660 628413671
    0x718150e0405130b07050a031e20040e01030f051f0605010318020604053a0201030501060305060a0501080a0b09090705010f1814010509120601090501080d05030a020c07030f0303050a 80
    0x19601c82e4070204003c00030480c52082000131440da108401411015041e1700300400c400c41048510b00780200d49800b4000740c2030b66100071030013012101a1848a26060464051a0500b801071282e1165014007002d80001e0240e55448100304040203844441910b602e00d40740000c120305c0b03c0c0c8003e001184607450000c0d00384998070840a03100c641402c0c1e41c0384d005006903d005d02d410184602d03104101180d00d204035052105401c0c90340c007264144000e50402d030f4000d81082582c40003408644041e00090100351801040028680b154440c41082e58000d00745801c45603243d0910f24060000700b840300ba000350b646000e110404200194440075500c1c242c0f1780812205054030102c9101280c080c0190b03016002d40c00400c441c0c40d80c2c0c42925109041858058944042c0d8808510710700c0d6a4007070a1190f9014200421040803544289805081d070b210103800c1c01c90200340018070500015002c1ea480a0380010f0303c1d0b41c942c108100b113000071a40a11092100051070a0203401060200c90556040e030410 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 628416160 1250 628414910 628414921
    0x4260910020c361b07030f0801090506010219140a1b090b0907030c091508160e0102120d0603020a030b100f030c03030c031403130507050f0102060718150e0405 70
    0x10001e0008035019081c8556a480d810003035450b81d02c3e0003400d014000250030384407840703040400e001442e0300342c042d8681d1010320f520008024146203050f48441350385840c19003404070b60380c1d0107d019454080e403040c1082c58607586007007100f107904140490040f00e00c02c030f1040d1130420680c24803042e00209075041e58044140d032440d001c0141c0f0200c0f10915400440f60001441480c001c1c2d02c06e00c3c2c0c0009a103089030b0881d46401c91030003402d9440740340c10042400340d0104440c440b4941c8402000c210740303250840045610303200203980d80d00d20f203103804402d800100d007540b0180c0d4154080c200458004150401c80c6980f0305029005090549060b84081b03060100803030715610000408049991003068151103901c0c5071030440300b82c2e041c40011010007040c2c070080c1440d01a070102030b501582c9580d001c60030106107460060310303101e980e40c4046c1c0203170400108003000c0c0c0e07004540c280e03020481d424504042c15101404d5207450b42035800803484030f42000b128075000c80e07210144240020050318208125143c0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 628417266 1106 628416160 628416199
    0xa0f050c1002120115090b04060c0515010603020c06090708030306040e0312100501090812090f0d080d291f05040812180904260910020c 60
    0x3000f005101489064600ca00d0305016400c0000c0000d15040014099000301d100e081e06001c0000e04a00900a06100e031a017000e20109801c02c03a0740c2c4400028009411200c01c02c1030505c10a40050f9441500045180540b2050b60040d4290380c1c0f40c1d020080030f8117181110501500091041c4810b00f090a41c07440c0c0a461446450540c0504040005194462940c841e1a080e402621405a200301010443e01010401d450b410b04000c5440c01160403004e00440003401c41030002007800d6440903990000c81c0107290283d04c603c60b0350f40b02016808070104000340c0780d848410364070120b800c2460100e006c40b5a000d02e05080c0e0400d81e40300c60032424500318a41d180781c04400083c071800800100f11041540400031518000f80382400e85074240d0810088150761420311b1084141248043d00100380c800040c00280082c0c219084444025100e00f0311203c0a13000e084005504040b4490 = true := by decide +kernel

theorem cover : BRFrame.Cov 628237410 628417266 := by
  have h0 := BRFrame.cov_init 628237410
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 628237410 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 628237410 ≤ n) (h2 : n < 628417266) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
