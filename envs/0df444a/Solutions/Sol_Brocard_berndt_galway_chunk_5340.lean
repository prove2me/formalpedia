-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5340
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:32:44.809771+00:00
-- url     : https://prove2.me/submissions/28566a2e-d780-4b72-8a14-4a4d731d31b3

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 960251798 ≤ n < 960431654 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 960253048 1250 960251798 960251819
    0x7050904030318110a120f060921020303040b090309030c04020a0c0807110306060d0b04080307090b1201080705030111070f110d0804030b06150a0c020a1a03270601 72
    0x1900403024107440f01c0307100c5040040072200400701d6004544500c0503481400c140124041590021114000c00044400110700c4541c40b003120254000740004603c012030900c2138803d0881c0b1240d410400c81100d248100320b6001024500450084080d104503496003110251360b0f1080d01e04894240d04038002c6084c40780b506901411400701f96041c000034554075640c4081d141d50240608880082c05240103040900b000c014280c0d1042099940c2d1a5082058840c241007010080c0010a082c80000c0020f600780c1c807400c0c2d510000d00711020381310784412140c900d00700b010307000f40503560700da109030700d00064036180500590070300240c0c03600c8451400006403140000228108000d441c6500c01404030343c40351f1100c942628405014002c07080d16079003580342c8811814000307801c02d4418010a442031040d5510700c400c03510209003d041003104900a44080350000c462035100700c14030802655440740203e090f200551113200321260410340d001e10b140c0c50b880100c0401c80c01d00d03540e921080051040c880785 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 960254298 1250 960253048 960253051
    0x403020d0e01032307050d141e1306020906070b0906070f091a0706020c06070c060f020301140405060a17010603050c090f01030b13020a03030c0b07210c05090307080a120201050702070509 82
    0x14070303103145010712070003500c015101c64217068100060700d8020803c2456000c09046009c040c5000451583d00f428039188d0134599040da400361240d5400540f91900b036403040101c031981a031003603c2c80c040d80f0b4559095922104111540d101003815800c210202d50310900840301510071501c080c102c3d4010f4800c00001540108000700c030504da003000f0756118900108030049c03180c0703015a075080d4010038516080c000d640c0ea4801c80c11030940180010301c601510400042843c4000b960000380c660b850000044070041c0917440b81050341540010329800380010340052054030b000e6001c540450080317000384407540d0401c039840003801e04010018030025200b0b418081e0000c02d09803161000c540c0540018030390494a910403004181d0b40c400d40c1c1c040001c2d8440c400e44c00600ca0a01070074490a103490040314088010500d030241e81e6030818118081d000310181c0305100006000c071000151584250340c1d40d00300e2900141e501e004590100310220b407050103010311074180f59019000355072500b01030000702c010 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 960255548 1250 960254298 960254311
    0xa0e0307090e0d020f03040605030a0c030f060902030907060c08030a0902150a030510290c2104050301061505161509030f030606050901090b210403020d0e010323 71
    0x303104000241008540500240000810058800041843c43c040e103001e600390480c4071070b40c009100030048683c0200035613621600301c5c00007042e00202000120000d081c020056040180b4000d408a400750141e8090751003820f031681101c0e14a911404241d484034461013008140c03030030030800103464404580082c000c0a2028000161055412590f01e030749410076940100029074440404c0481c82c40c801d1a80d009015502d2000b81d0845046c6142d001d000c04110150b030307914400610042e040500b00700d4120300003840c1c030003030b03280482403e442c00056100e07115181c440e60a200d00400c48810716000b01450f031186890381460060000345586080c2031070642039070544070034405418000218041d03202d5141c400c0c3d8a4460881122801a00b1648641c10400030050140100c40c80783c1d820800d40380945040c02c4c125a250625001d080c00f45104050311044410891400d1004240d000922552161a0354a484080425a600440440300c108a88035042a40c5d290b2000038803d0b0400091780209 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 960256798 1250 960255548 960255553
    0x40b09130503041212020106050103050606070b1f091505040203060127090212040b011401200a06152c0106030e0c060408070513050c030f0c1905031e04080a0e03 71
    0x3507a9068180b40b0f00300c0c00c82c0541d441011681c00c5e81c4e0381642807250501a00d000d00f0100020300700b40000c00d00394001c0700401800c0130110804146c803840380510306c01c0d090f20000000146541c40c0e07103030100031342114ac00c0562a02c0140d007001c1601c0c5024000c2c0e034407840341a510607048a0340242c0e01410122010f461540b0044024400b00700c2d034409000612010f4203c240c0c0c190b242c281480c2003907038900140d01020350000591040f0505170782c03103801d1411140e501c140c400514402068001c3c02c090444400610f0b00d0314040b40702d28820809010701e011251035040d091018880407985200604076864a800300c041c002c3d0040c80183e01a9004840c1c018804c01282e00c081c5218001c00d00645c0076411080142d0f01601c402c00480c0b503c460b20203829401502c042c049800c24070502c80b000c1c00082d0a041600401c1000502044415400d540541034070f548282d40c0030602c400041e00e42c0c3c1c011789026040c0f03130412611001e1486070b03446050095030b215010502c0c01424544c21180300c1100c10405502d130 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 960258048 1250 960256798 960256807
    0x901330b07060b1c0305092701030f14010218062203110f0102011406240a1e020c0102060a0b0406080114150a0f1e21020f040b09130503 60
    0x121003010703081c242c0c8150400190a0441010800051110103051980000ca80c101c80000790740203080d01e5144509403124059200800d514044228800308140c030610803d0b4000014801c41800d1800180c0c0600d80303903c0c140d650f51108900303030710442c1c1ca000040c2d074640450041c2420030000800861401d207030030b00700c0504802c04404262995920980d00d10310a4801e040607440c0a210750305907000240004c00a42d0840e01d024005c0c55402880e4034030510140c25252109140401503001010340806015924103003000081c0075620043c04000900d82e0342941030791f030709000146140325044141c0090900d50307100126500030381419150b030b6030040d49481c000144d00209000b02c00b284450705100b80740c0c40c40c2040040002c0c0130503500e400d00c9619131400c10040d60083c3d956a4059600c98580010910054601100071032f200d580031008a441000790094100040e804050001d8400c031890000d825884017040700362034000d00025808085000880d1503406507880c840103251040b0250307400c1 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 960259298 1250 960258048 960258059
    0x18120c12081e07170a06260a0212060714041214031e180103090b070c020d0c0905150618130e06040302160902040e01030209190c0e010305090133 64
    0x11038815200030000c500900c10a81c1c411010680d113a512241c400c8041103814070300050500c40c40407122070702c400c10351800c3c0e03e80b04c100024071141c1d28483c0c01400f00f414101c00b0800b03203036450008888072000140aa85851110f6a9100c202c0c0c04580401048840306082c5407900d2600420410b641e0250b4802004402003c3c003c3c2c4440701c42a01400c82d10b20f850740d40c800c0030013182c0902118098101440c040b500400101c20b40c4807543c1010359441c040700300364014408640c10301c818040161044490000000714015107401c010310034620f5080580ca42001c3c03100b8410180588000051008501d64120a881c107040c8461020694510700c08924070018400c00c030704001c4107030350a900580004540760417002c00803809600a0404a40451a29180c00102c0e4144101808000e20a013030150104d18090040c00c0c25499210081004100154144201924621410140714040707820030b000104080410312070400c50070074458a0390050810170515442501030750003400040b06c503980c2d0100c0c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 960260548 1250 960259298 960259351
    0x3020d0219030213020d27150204050d060e011b1d030a08040b0406091a0414060c0d0815180f060111010204121e020f01080a060918120c1208 62
    0x4e80ea4107000016610016856800305845844022aa02058290044071901c40480da410100340d0021654100c1c00620b1000c40080c1c800c0d5030056520440f10340c0c2c54004e10010381d11030450303504144003c011020b14860010341146428141c5030200308018801c000070118501605510600101550400543c0d9510300c4425005a002a520200d01060500c041c07600880e0000207031100e69001740c0c820109901d5400c0c940310754002c0001c41200c8c419010050384682d41620f490810280c00da4034004000c0394001c003500d1088a80200144210080000c0790074800724500c00c0800a850810190740d6050201c0365a0001400c01410041421241411584284003a0005d840c9007000340c0800c5481341420f0381c4c04203c3c43c911034000028078845c0d01c01079413468042c500c00c107020b00308030784035503070b280300340d400500c06a484203031382a080045103510619060b0000c0e001500c550300d4a40b944000314000c990450b10744000511210104070400c4125000328031803035000090701c00c0e42032070300f483c4001003a = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 960261798 1250 960260548 960260569
    0x80109050312010e011a09010e030a0f120518040e0c090403081506041d0c13030606030c15210b040c02060a1103060f130f02071b0501080103020d02190302 68
    0x40d1960004a929032140750380040c02801131075005201c5845505041c800403d40382c840102801113500044d2a0116034006c20f1501c503404e0004003501c2070303a505405e1260100789602004c40340000c0604810b00341c0c0f40210203440121201c40303075950410750f150003444000c024814a402d018881d041d00c65002d5651207002c40d100390b11030f944103003c50074501d82000c3e101d54414031192040c0001c1c041400720720b618080502c44040601000c1c02c0e40d455407400003003284104484114224101040401800456000f58044a10400c2030298441e60760f01c0c80d60740e07190400310b40400107101180d0000c0320701c132101180050410001000844030001000141180c40c500401805604030341e0800c400084140b0603095508100603a140c40d52806c43d0009804503c610f01051003011302c200c02c00042c8030a50301c16500084d42d80001c55594001c1e0034411560903a19140c4d4100f1107070a07202058551061482a048a502400042d0264603a40c00c0000e00020404e000c541101801d41c00400360303031010480da = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 960263048 1250 960261798 960261803
    0x30a0606080a0308161215080d030c1103043206040306090210020a05120a020f1005060a080703050703202d040504020d062003010b0d050106030c090b0310080109 71
    0x1460345071203d10b800b600e039000041c01242d007900b8852568000ca83c10450300400b0700001c4034001501c0461019440103c600f603006410300f03100e40c02009920039050381c07041040091640f110203e4892400f60300d59240f15070301030400a8a08105011040d0f00040c0c07a003003061034400c08040c80176040d4804644c058009510517941d69840b041c200e000d509014180116000f110b00c041c044402060726050390310010b40d060b81441207c001801d6043c81c0c401d0003182d03201d9582400751480300e00c056080401030001590614031410354280001440e84000034070800b20303948039019042092564980c450200c4040302a002c56490000b0320b41c00b140e80e03840365403e0303292003064005003c059008480c8a1a8490042107010b10710b084144005680d84548135180d1a50001380411088800d00b030344000504c501c00c41542c9c50401000101d9244800c41c080c2c601644a00701c01c000903030342e44a080303080d14126000100410039280c8240700712002e100c011540581c0000c801c42c02903554600b9a03085a980781d106 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 960264298 1250 960263048 960263053
    0x15010f1e33030209090a0e07030b090c04021b0705090f15040204170d200303010302090a0216030909050c04060f030c09081b2e030902030a3518040209030a060608 71
    0xb50700b00703285c05003d603600070422000400503100c00072101c5586018600014158889100000b480c00c401040641420f0700007034020b6413180c03089801d00f4151368070548031100900664030041030758180704a60b14450100f192800d9040e0300d43c003040c0c07101c1e20b0f500301000350041d40800000c100d414004120100410108004188500500e54000d003013000100c0304240c14140c06860010f04200001036070305481d0102c0300e952880e01d800c1480802071040381400301c0500610340c48181410b41202e05502154881e000078040b81d42e4003c101030441c86036014010101d0020355120f800144a9804444440c181d8200b045045483d44642c0d071034480151a030b42030501e0182d0ba03c40b03150410312082d000c180400c10356111812440804c92464203034080c0d006003016030303c40034002075550401281501ca07420401040d02180107030b90f07241030705165128010000321401700d20000146030b50100c030340881551100c101c0d14500c00040101035480301c44003179414811b8010300300105070742e4402c040003040031100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 960265548 1250 960264298 960264307
    0x307020c030f0106050f131407050304120810140409150c02100209010203040b0c0c1f0206070801051c0c080102030c070215120c07080c15010f1e330302 67
    0x101481c2c034a03040c2401407030382d041035020082629110314003000c84904960500d080c4001000f4800208403684042c1c103c1c0e4005800d10100c61307002001035005034001c040d42e4992a580c00400e070707255507040d030306042d001c14110003c10408664110020403200010804192140306031a902402d4007403030701b000249950703020a0591142c0402203444090942c3c4410360a20b1040c1d00084d44038011481140600e80e00040c202020310000d0092502e0800020301b9914880791142582181c0c0003000c00c04400341c818400865005401010342c0ca04035880140181258a20520030180020740d680d8225150122024003050655080c0060351113040000c00440e11440c0a004211180c0e46100601080e0300d4100b113010040007414101c03640c01200e8032a104c0e540c5d4032524020b0014072403c110042280601c1d035810007400d030f038510308034100e0304000403507100d00d0340700c0c51622404079251642d55142c1a5201c41000911100c0d211b002501640b4075000e03215082c0030000c8800c4104411504001070760004 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 960266798 1250 960265548 960265573
    0x230d0602070b1824060103050705070510050105010806030312011a04120503070521180a182f1b0106030f080c070f03081227010509060609160e0d0206030702 69
    0x5400b4206104d94000140103048402102100c000600b4541c1010f03103510005c1c800500810858a555900c50201c079926070780c0a0f40d0f007004000c02e004580c00918130b9008500305140c00402d559121140e002203032444d0b46050202c5052601c4030f56154180a424040000c41c1034201e503201140500a0014568586203407401078141000b8002180b0544524408800f44810f090180e4081c0013050600c140440300841c0003c050610720b0340401001c0070703c4070100d645001d458002c0c3c0702d003010707083c1c1c101c00210007240e003d483c0d0340301a00e000740408010b101c0400d507207082108440c2c0020100c00005515030300c0c1e4035000114507a00d4015030340c0c160000743c2e010001c40300b0861180102001181610034900356070f41c4030754500c90500300b0b1658400420100d0003020b00003110703017101d00015519480c2241d6106004d40a0b0074211180800c600030000005da45003000e2003020f100d0000304103002113850511b0816140380b0307030440c90690080070280d50035005868160003035000780b01c650002c003403103c10759 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 960268048 1250 960266798 960266803
    0xa093203131719030c0305120a0213061e120905070b070b1b1902070b0c2109151309090303090204201b0313060504030c230d0602070b18 60
    0x10342242d41d81c1d02c010ba03030100540c41c1c0224102d000358540382c40c081103185030500300c90030702a80c090964001400350500c040d242c01a40180741c008564800c3c00b012130380c1e8050a9900750a1002180c5210410341e2010707801902c21034200f200c146203100001440140398654520384282908250680000080c0b10420f0100d440482584000801d2107403101400205004684d40070b501c3d4002c00082c03130a000d12020900134051000545114054940c41d07001900029a480301001c00341003009048105d00e80701c0035208000c82d01044c8000e440480020601606a00c0c070358011180352140300881c0d03101045501345c034040e1020050080d500899105841c1c01000120760009014068400030810b6001d6079118150507102c03102c0400d00b0030001a800b2200c03250651281c44e03058648441c0685c0e002c50801c5e0480090016a40201070805403141c0302c15004600548581e514243d610710211001c826150010005160300c0c8103020140c00d0148a641d2034500300810b907030210822642d1040340540c1c4008 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 960269298 1250 960268048 960268079
    0xa11070801140c0405030a0605090109020907081608010b03130c0306050420100215100803132105032502040e0c010807020102070312051f0308030f0a09320313 70
    0x40c03c1e22840d00345131000190355980c003941c00030030650319007000880b800003e40c011003c09030050300d900e91501c1d042000400e1a6401c030383c0c0b0701084920070341030742c0182e1140240c0b6040c1c410b124560381c516202c02c0209040c11403010011207100c10080004000a42076000b0b1742d00840c409c10000d40e00c0e22500801350b000c0755040c1c428034010040201d5002e0300c207078000b030061856207110281000c90344440925170160005600034200c54440000c41390b1180c010303402400f00316a06518040c0c00071140d90020600060f840300007400a90060000c2843d01036020350901d030f0600b22800b2128004100e5001c1800d039100c21400103c60781217840500740355608040c14941c0220705200031071420302560303005020a5070355407d01600d9507441c0001250420843c8080381d018802d0801d20070307a240d6030314010300320380d06c200c40b540042e0301580702054880c900c40c001d40f116180c2c4080c01d075410407941560410300140c80905000d0313566411034010785041c0240004c0c1202040c5502c105032141c280315450401024 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 960270548 1250 960269298 960269311
    0x309061704060504140304030506091b150a20010207050d09230a120503030a15150e0f0a06020304030b0606040506040509090a0605070f0e18010b0a1107080114 70
    0x911034940da4840d2209105648507500031000503031900c450800d800e00740039100044135203201c006000700601c80001180b0b80b2038104841100c0d48002d1901120f0080d002540c5042d0300240d040c511004c1c10011a0080c12601d41640f50452038400105030003400100000d082c0c2c01140d43c0090303e0010302c40d0600c041240e100290030b01c2148030349030411138911244601036072440303070468644403600c580d034403158400144840d2400704404901c03410055240d40c002d8500080261500c0200488140044800b00c21901c0f0040144c1483e14041029500c8141c40d00130194003041c00c5550028a6640c0340c0c0a40c080c10303607980255100d500f18502403001100140910384591800e0008110b00c0c0d481c0d00c04c540645205841ca520207880700441c5a1800003a450014001800d0108000040d6840091070300e1400d003596030010121118024004030210103204040b054081070700500c00b0607403000091078040c150746080300c60342140314020b50525105801204069444102c1105405d00380001c490b040340707 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 960271798 1250 960270548 960270557
    0x115080a0528060902040e0f130807020418140102040810020f0f0f27010807180e06030316210f02030304020d0206040302030105250203070f1515080a030906 69
    0x1d1a8048510071248104502c8807040c075100307400074941071030f04150020200000290f468a071142540d050110040f1a450301213150340000550104000030400d4405400c841010b292801640900014240100b8219070f09000040b0344400660207284035441d440c1c8035000147c8035818005058100342410410320103550060000ea00d5402024003112070464500c41515600c60704006218402d009591000141800d03d00d41e400580300d103e540c0d610011f109a0303403000e003541c3c0e14030300f40c652441c81c02d09404418000340c2e0600c00d44544001032a040320004084a0824508516100c05880b12150071120080410650b0b840301c0d0007104a800140341c0b6040060305c41022a00c0256030b4040204042d2040c0807100c07241e41035450340300071140078580140081c840c41c90f001a0040d10403d04103900d8454070001290b10300390b10710100076107580c00e41c404034240d010380b03454030755048481c400444404501d544104522202071241101002420700c0400340c108011181401303020b02c54136a00000500c07 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 960273048 1250 960271798 960271801
    0x40615360e0a0b2106130f02040b011b081b060105011d0f0a090e0705060412060f0b030a030f0e01080c030106110f250902040e2d0115080a05 62
    0x44100e00c0311681501c00c4038086000eaa80c415101402415403404400d42001d10788290a0001c4141104024481918001c51300c080e160066555480494110301404c03020900c201c502c014501608416070710503052400c0c655414902284c0c02c000d0440d02c001710741014000031400488039081142100c80003c85000d406030f98502800a480e003c5076494a015988160100580503502c9801c40c102c541e5020f00039122031074441009000038080c1030b0030200180315000c070002da50b00c1c107001140c054400540251514013010355885001d840360800302c400050b100c0c601000ca946003002000c0d001d07802561178a02c20580740c04050a40c0c1d0380075440904004c1090700300006240c414080f02e0440301c0358544060a44034004c03190342803101c220000400340c044c0c0160300c043c00c0c0c4080c0010501052040e4658a400d0355111520201d1045101b81c00d0600080000a4254130b02003608491007520f14a24910154001c5440800c0707800036001600e15a00c00545100031582c00095554000038101e004c000d00e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 960274298 1250 960273048 960273137
    0x905190317072111060c12090d020d1101020d05090706091a07030f0507061d07050102030c070501031e050a0606030b0603071409041508030316051602040b040615 71
    0x802840c403007080303501500c40e01c0c00d03030505105244801003142107500ba45d110703050503810500d20360b1218031000d41d04c1c411039000ca404424040f030813911a6069030018401c00d0302c540010399105c10441e94550240d50b0900068082c0055030140c94894010b407405018450304042c0302610212494000600407000003c074041021a10070441d0719050b01410011485420a08202d070380d03200e0b600d40242035034103008003040d0180c182c00407080c0c8041d0007005d540c0e0701900c0d20012a80d0f0300403208494116400350800b007040c2d500a0b0320002604044034108002842204041016a0710079518020010740c0e0306010007110380d25108103120307903404407a41451820030510080c00180301c419044691400042e080509a8441e8440000c8458807543d500038199201c03d8641c40740c00450b1000c005d0384081e071f0102800c520450840b0440c0c52982110310b50328419409010080c40b40140d001d0b00140d440c41c02064180074881d4492040c0360341d41d240c1000c82e10b60030256a40b0760b040d410b00a142c0396000e160549 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 960275548 1250 960274298 960274313
    0xc050307120b040b120706090602161401020304081c02060609040b0a0c02010e25050d081e12040609020a0e060607030804020303160f0b09030a0c060c090519031707 72
    0x40a00880c0442c0100000700020020048951650791060b0640c2e1085070f08500860b03000c003102c0c042d40300c81d05070590f9040143d845050b544405c00d00010400c1042c880f444000c0c9500d425507030188110b0742400d86a00342c040c945500300303158100d00c4a4030b8035500c6030954104134081d405401668000c80320305196403007892100010b4410303d0015110740c0000032a91003517005000c034160706400c075455640b4410020011400c0c4494404110785c00450100b03581c00c2070302c012600c0a80c801169031404901e080307841c074060060394085e107420310f00704401100d146035854210300450055100050f001c41034810030a0749a010750004980c1e44031b01041005940ea44400d81d80b889815042031462982c592001a00b140b080b01c80300c0030305100c00c015000510041c507500d10700d03d6124501c0e052040d00e42c0c140c035a55034084c94034244001411901c00d2400180380750401c4030426000e040c40c642c0152908002034060687d0300d240c0184019540c402c10500c0ba0480302801040010044540b034900103481d48007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 960276798 1250 960275548 960275567
    0x70f0f0c030c05311104170615010203030f0403050705070f0e06010309030f1b120e030610052b0c06020102031504020f0d021c0c030f0c020d08011511060411040c050307 74
    0x5080704131400c81144600c0d1690021074040099000040c0d40390b880743c607c102c0003010200c03000c3c070620621000800c000756002c881f42031010141c0040d400d40d40c1c6c02840c0034002c0c1c0b00601c04c07410040300303101030720004d0000c00044020384030740010f440116040108107514013600401c1e86040600f08103100740070a4018080840a00c658070780300c5202c65152940c413144220f216401000c3c6000500c130414a185d01182401d4400000c509603080d070f4441c1c9141c2c1c0c0003414507000b000d40c000e003c040d96281d014a605035108003c0303c400e5100414614545075010312081540c0b10074050703500007082107002c2c60703034445051514030308607402c6080100a040f8590980204441400107682c00202007046000c10030440c00b01302801e907010300c99550405001006480200a4808128180280d520b4258008195030792844419a540311481e0318180c0013032420074010b5055070078080516109292801d05020b41c520441c0240daa1450305800c040a210032644011898000c0050134018408129880040030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 960278048 1250 960276798 960276859
    0x80d030914150a0e0c06070b0106090b130e07030f05070306080601050a08100f090c080d0e06070201052703070b2d041512050a0914030c0a0602070f0f0c030c05 70
    0x40c101d0b8855600920340322a405e091540561701107250010846102c1056050340e009507036620407940d80e00841c0009004442d0405c6150b01a01400d210400800d030340e0940c0040d4514001c00e030318260344010800c0741c60603107040c0000390700c441702440003900400605005101c1540c9482010340361000c0e0949404903045010941754507100d0000810b0855000413550075007080107950410755505c86690b03240310000c2e126006c6001e16444424514200050300e20603074068658901e0810398039440807c1082c10b11803600302c184109411600340c0c43c00c0040d84094480c2915a5580381c1d40c41d09043d50006080481741c06130807104000c400b4025111094078215098180701045907501c488082d6031000001002041c094580f00800200260700d8001c0e0702e0003030148030b0001880401c00034a90701c070b01c00c0400e00e6034264816954140011826801001454014051003040d2442c07580c4a14440c0341c0000203444018201c0000d0050000d003410420081104540d4140c1181c950000c0d05c90344030090012 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 960279298 1250 960278048 960278051
    0x90f0a0b19050904050708120c01050a060308070303051b030c090f03060601020a020d060603050d0c03030c0f050412020609060c0c01090806010509010e0705090a060f142104020307080d030914150a 86
    0x100b41000420040d0700c003d032852100b03994161239810806011500710014400c43e075802e00c0c021952031405882042e05980d001101e40e0b10f40f101070703207041e0043c0c0b50280205c840c02c1180008520038601420142d030240c50f03030300d6400b0b6441501c9030400845041101586210390403000501400380e80000c0c00e00703201079069400d00746100103420004000c184550002d803043c06484030100d41c042c0d100c109104410320035182003001c4400c60000b11810030041e1a00c5000c40d03800c0105019541c0750703c0c030140c0d40703a1008060510346000b180c04240c10b81c006220440c0d443d03006040248082d0b0b0002e00403005881c00500405403580b40c4000500700c0306060ac943c082060750310000c80c0341c00d88113408440c0e6003100545009034450303a030440285130083c501f9101c00000c9800071000580780061003241d00b07110170b403000d010603514009086880210007a0049034548500031300080c02070f40500546c044000c0545000400140c00d003040e9515000c41d406032101a00700420911082c1050781140382c110410030310 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 960280548 1250 960279298 960279301
    0x3050601090f05010807142206060909020712140c1212091603030305041e0507050a090c021209120d03200a0c0f0201180e04050f1216020f090f0a0b190509 68
    0x80f03010b0400c80002084000c0c4415188c1c203a2200c0f982000c0200c44032569a440d8143e0f403031140c203080b030040c22002482c08195110810b0680d114081c400306281103041140d162103045248949043c0101d8010380000c100411070011001c2202100b540c818011400342142010041d05045800c0b240d000003424180d4070008102804042284c0c1880d56007140c0a071030120351182001c4e0759980f95407103400e101d5603901001041d000c00d20700a10a044080c0d0300244200749203c890b954454014040c0680c01004090038411007881c01c10611a201801d518009001c0e2020b18418042c0d108075a204105a44104200c3c00307459404505140f65030303000500000c80e4035180c401214488c03071200000151412050001c101046400c0115014034070440480d501d104a2000c1d55840b00344501201c1400c81051218224000c0c41c04061489a84018211300b401140b040c006403c10405a48000100c00302d5010400c00c185e05102d00701e1107403011640d1160b42260300728505503801d02400f030709009007050300 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 960281798 1250 960280548 960280589
    0x3100617061b031f05060c060a05060103022a1c080108102c01151706100f0512030c03072306060a050f0a080a060b01081b0706020c1603050601090f05010807 69
    0x21425000c5d000080c4595900c203c00108565103036400e07910508850300d441c000c62815802032086030900f8030135003102038031018400d4008200c0403a00c540030906001d024001140003180c1d010030b281c116900d48501420303506100040c5d10f040c0041c010845128941942105c0d200a06a5441d4007515000b0611091b460130000f1180580944c03501a07140781c1000c0c1021038060458003150030500c18600c104d82080e80c80c81140020381245200362030144030118018041d5080c00d0341c6414507000c81c001140d00c3d07c0c0d015131700d841c995400082d055074401d44641d003400074291000c503c3c400142500d0300620341c2e0304151001400c1e20f12103101d40c0b8403408030b0840c41c0c8020784074002c546d0000e10a60040c1c81c115595802c012020700700d04261140012240400503920180400c03060120507608239405040c000280d481c4002540014001c4003207201d61011504000041482c80014600c0703035014041f01d5150068030030a40fa0000d8070340c6501810680180501d42001450000320340300701c0040301100300d621 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 960283048 1250 960281798 960281851
    0xe070c06050103030f11070506091512070509010906050307021c0c020307140f0607240e0313090606110a0b04020f090c0909011202060306040b03100617061b03 70
    0x25400412490a00c030000003030580000d10070080c025a40c9450700310a0030b100318140c8602d964014294001401d00c0305043d0340c2400c04040341d00d0b617940a2080c0c90320250b00121a0701250849440000490004e0600b00d41d5a100140030000d10361400d10508504140030040d48a141e114104009400064659801c4c1449080807003c03a98020f81940c03032a645518900c0c1000c044d4050841c040d01c0c0d8004550b00b83c0c10198129a15150022503c40340640f034035140400174030b0b00319800d0020544404048103240301c01d00082200c00280001c2d10803641c80c281c13112090b60600c1c0d00c801c1c144600303803420b54000700b408914491a5a485a40382c2c58661300c920000e0204900421096089a00c503420011801c0e400780041440420464414034580e0341d800e94000c904c0c030200002900110103001048007414650801d600300d00e4000d040c1d0b201c0c80e0003640060212400c65210750060003858244010019052024540200d82d00b2064000c81c00740c00b08c0341d5100d22001d89641404280703805400400e81d6003 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 960284298 1250 960283048 960283067
    0x9030f030c05031c02071a091203040503040906080a020a140102070b0f040b190207121502030a06051e041a030d0503071101020706020901080a0603021507030c0b010608040c09020406090e07 83
    0x240050f01031244c001a0b40080d0001c213000c880342c0c80da5030250300f0071740002d070341d018400c2d4801002030260141110041d240c542001d0012200d52200f80404034125015000340800b80215900900008000303004024005540f40c0c01103181d6121606c450f401640d000c2a801c0540d0320000c0b10316503d0300784c6082d9050502ca03543c0400900180070440c154140f40741c2c0c1a000384540281d007107130825604c0d0005801c0302d000966006245994100490918040c0b54010316801600d4000c00945503070b642c400719070b4941480190714411007103a8400c011600d828400c04a00101c81c1a191b04070141c0000803944d100c103064014401d000d4040700095030036128002d90140501107400a64660400b0b02c0c2c548040d4000050303244c0869103d10000d1061441c034403941c0e040740e400402485207100000307030200c01075000c0318058042000450a242c0810300d804a500d009115550f601c0030113180504200c0344039581c503006280128010041005030035400346100c03040c2e82c0c0208056086888030402034940404 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 960285548 1250 960284298 960284317
    0x30a030c06050f0421050c0601080f10050115110313090608010c1d040504051c03021b0c0d11040b040e060103030246051e0705040209240f070b1609030f030c0503 71
    0x55440042288030700840e0032903c80004000f01c0d50020342400d00e20083d50024010080415034440ba0182c07a90f20430300b003101c0d1038940241580c1c900303101c440c0003c200c0502504640e401588840040106141c00d1049071400c0080389010031070004400074190701e0040b11940a40b20300d8450000c00d017401010b01011030205161000640001940da10141c0a504080850540d86d01100c201000800340450004a203020090010300040c0032035070f4400c001c6655101542d0001e5541103281c545403100e120741040c01c1c0e0064014242903145240092601e144110030002500c00c0600815004411801e224289815002d081c412011801c4c0046840c1d0800e14025066214600c01d0324054034551040039000300e60300b015035604580790001c0c402a886807500c055002004072941d001403103a500d441281380511602c3d06072520a1340c1d860401140c00842e402d841c1140501c3c2800100c03990700c2c40d80e600c980a43d040191550340b0319102e8400b0031907012001f80c14000c0d403c3c0302604000d014001c4401307401 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 960286798 1250 960285548 960285553
    0x1202090d0b250f020c180a05150a0f03021212030a0e1212040b010e060d0b09012307030b0d0f0303020a0c021306030c0e0f1303020c030a030c06050f0421050c 69
    0x34000b8034010b09100c0100150b50141c0540c00062019080000391100004c101103c4110140c4a100a4178000c0000810060803880403010b075001c40d9840122003030041590100f080d1446046004000c6040100045460140c1c41380308440320000e4550140d03580800d80d030400003803256500c41c0f001e08000c000000300340314a100040c5107000c1d2201c841110302483c040e600c04181c507078075603d802d03c4030381041c0c5a061b800318040380c0440010f020100c51551007000b030000130803480c001520102001c400c1c1040703203d4074801c61b8108200103034540315401c1425002c803803107500a0155242d04248910789503000e820190000b60300d42100780682c0c2c01105265001e005240500e160f0400300c002801540021124100510f00000d4010203202c000c0c2e005200321003606a01b600d1307550b4072103030110200e4000c4007540614200c1c103c080c0d030280b2480c6000c5010340c413400d541003441e14100088440c000d002c0c280c0c010340c010500001c40d44081c14810307542d00d038a100864050703005038151014015500d2040310f51 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 960288048 1250 960286798 960286861
    0x30c08130b030109050609040305030a3201060f0e2d18180102070203060a150905090d120c0806010513030f06090618110f060d020d05071202090d0b 65
    0x70400380005504030788007101c00304981d0702c442c001c120341d092003964080d00081052011607418010740d840140200340d1a0846068482002003a02c0840c80f030300303202c0301d80513518401045140e03040010103800c0600c514180c1250b25400001494030302d8400c7d03030600c400754000e82c0c0307901003803480c4019030720210014030540401c00300107000c03507210030100c400044002d01c00c1c0309143c01c980140240c51225074010040c0840b0740c0d907155070000510ba1089c50303032003444490b01c000a02c40404e10945004024060140004601100000d440310503620580c2c80000c0c40c007030080c40c1c0740d980710280a8102c0d409281661b030342c2c02d541010405070ba115800c007801c0755020082d40010014181d20001c403c0c2d105d040103000740d00b04009402464904807202520001d01c01c0c1c0e45464030f20f481205000905c07001002036013080e2201c41580102d0304104903c12500c2d603034500b80884190488028080c02032600015880c03c620100821191a1424030050072085e500020032403041001300030048280500707003100c2e801c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 960289298 1250 960288048 960288059
    0x100308030a0c0504211214040e0402371d0f0720060406141905071205040f021f14070501060b190e0a031a06030c03121b01020a0903030c0813 62
    0x101210610300b110f9a121904406c81554080c0b14504c0620114401950400d46004480100180003d00c00ca07801009241030340300c03040c1035142626074090320901c2c040f400600c0280c140ca040c115030704407003070242018010000110031040369a030b010484000200b00c648648405854040030314100d011403e01044c4006003d240000c1c103680304e5030241100340804040442403401c110010f8449810304c03110324900d0034041829820040c0c0100b46807501c9410000780b00c40a03000ca590507102260795008650350103055241008a0200c0713040194209200c410718107002174402d280f401501034540d1008607909042c04029880040145130400c0d03265034424452800544101010040c00045451205040b0060602200344025694028481c00d05c2c2d801a1109006a82000f440ca9905201300d2411074080c1c0c5007404480ac1d115009203225071140e10918041c10750221000d0341440c1c5078070520595910950200d0144101c1e0303010f040c181010380311414401d40e07900c151031039441d02000d4400300181 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 960290548 1250 960289298 960289349
    0xb190905030a0f03060b07030504030206070512030a0911030c0f040b0a0503010f1d01090816061503030518040515060a090305031201170303070c02061c060e0f100308030a0c0504 78
    0x1100350f20f0f51304106880e200c200c0341506019a50010303000035414003041c401818403000500001d0b00440480310381d1003401c10864041d5004682c4140070b9903c072185102007007101c0c0318000d000710084020708040c09560300401c9519403000075051007151180081030450b29010148400b81c80050001d0091207c40c2a503030018007203003420080c00610681800d011440e040c401c201c803c0b40d00403030741d92511300103030594007d43c40c0180c0160f50140d500c2201c0f1110384030744030b135040c0158482c6e222251284800003001e0000044c1c100101e0246050204105da8282103101c0b040003c0801c0714041e80f103029400c401c60f0002c9139a000102a403000040e002601302d00000745604990400d010389501612080100b91a40000d44116000c00c520b43c41910051412101904a00500304405101e908078985030310141d038516030054422640410a0107a0b034010070176510380c00701d0010700b11041149595500b0103c0d1100508605c0c106a0b01c0c425800903620400844004110320b0383c15500d0903050214400 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 960291798 1250 960290548 960290567
    0xf0f11040602071e1e0801141b120c220e150114030a0509190305120109090f03050d0609050c090118080a081e040303091a03040b190905030a 62
    0x1016119800740012601d0115801500003107140000c1a6010301e800c0380b4141c40c1d80b0340c3c928083e01c1e0140e084041b030309000034460080100e040c104200c0762030900f40c01d0f60000800100355584842001c1052015418001218503000410f0303100c00c03540d501c20719480c108450758058511007250b00d03040c0300003000d80a40e40c600b80181c1d846e640000008041000549040134450030260440000740005064200c1c80cae444a0f504c07501240640300d9140d480d640c10070f084020002c040380412408111590341e80c004810b21809403182c2d180c20406021192101e200c00030301d0400050802c40700044601c3c040440741c008800400400340c05001600f0402081400c80c2c200c2d01d102e80c0001e51004a07601c080f001001810205c0d40094060610b0420315120118640c0c00280044240b0701c0da18004008011000d008100440c041da5582c000e0a007006055010703c0032580304035204030341c01c1c800d01004c105100c0c26144c2007000f90501c4100b16285507018000f401c4036074006012030002041e11405950000a4031 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 960293048 1250 960291798 960291809
    0x2030a0e04090c080d11031207210e0312010b04050603010e04080d0c0509100810140307080322060c030813050c04050c0a11010509030403030309080f0f18031f0f0f1104 74
    0x30400f81d284503003d69070b2030194201c823012101414020822441c0942200301c4004d0b14410390082d030a00400d8400150303142c010008000354400610801d07480f613140c17205405802c1e030307000080c94146070100052441c0410300551819122800101b01049020002c8034100d03000c02c44180000140303100e01502c42d81011440502030840e0442e0110131307074071411b2164440d05200c0c40144041d400c1900c140c003c0a05150b410f90140304040e808180000d082014240d820b9503043e08142d18100000340715584000b5070700c150140084103e5901c00680c01c003584035485000040741d0600c1407410308100749840c0141c40e1071500701c2d14140900c40301c1035181c4000c2a10101c0e60301e8040042200102a608840b000c940481c1942c105100620002c3e01c01d030450b940050082a407642071010b00b005155095210702000d105060000490384e09000600c0400390b0040c000300d001d4078900300441081c08a811411522011582d5503141c03070901e41c12140d108440c14450b0f030401300509244c05402c0ca54660160050 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 960294298 1250 960293048 960293057
    0x60507030b0315090312270d0e0618040504030807080105060a02030304020d020d0209070c020a060e300d080f0a0b1503060d0f060f0605030c0102030a0e04090c080d 72
    0xa0042402030060750440303080900208080030000d088200b003440042e040e590b09000c04c0002c120306400080449000b00208002548641b413003542491a908450419442a4001291f4401e100381c002d16480084042030740d515035104c2184100455070708c1c14010b0f00358094600400e000900d684541620301c035000940f00c03c209642c9540801106004400c101c1006074000c0000900508040e40d08ae05c01501c043c1c283c210360302060b030000d4200303807046032004009415a0024025450281c030300314018441410b040702e590180c90080f403948154464480500060310420901000c000741d0405070b0b0f200c001d801d44244a1003248010703c4000c0a4840480a40204020594054251040003904880103000c490614030920700144a038100800990b8041240f600d060040707a404070400e80800e12402000420040303480454080710400c1e04418000e80c04a610010b032360760000200c030710120a47c01c107410f05400c2003000501a2601400003041d000d030448000811b0407000070f1584520f15643c88 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 960295548 1250 960294298 960294301
    0x91b08010e16081f090c031a0a0207171b190309050a0e131a0f061003140c0c03090d050d08090102070f150207060908030709120804091104120506040605 67
    0x80750341000b0030602503408160030000710441051301c0c604145600c621a1400801d00c000b594954038a2507101d6481640c00e040000820f680045091420b542c2c0801c441c1c400f1070800030642c880109013a08a4070b6514203030b0001608070964000b916450141a100000b01d80c0c805170098054106201d01c410110082040d113400821903180c003600b0bc0050f44c1052040000954600082160f0300054400036510751001400d08400741c0d8540ca907052003150056844842c0d03081134030074010f159502c4011041090b240014030500c42d0742402c0e40c01d406c040f0070100c4a455201c0181c0e0b050640c171071681550791001034800700004222012070140c501d480c00e0346418240395180d4104500f41d20501d000100441120b070551000502d000c41c034011409000540103083c0401d580e200003c81e107036841c0c283c2e4402ea001c000c201c400c80c4d000c0c580d100605181c100c0b2203961880c0b0340d030f84000c9000324056000f4040e141c0009030b4041d0380035000d640040213141051589010350b81400380c1c50710310680d0160341301c50a010 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 960296798 1250 960295548 960295573
    0x301051006120e10020a09030b010b0a0e040b0307030209060f120c03070b120c1b3c15130b100807050409020303071202032a0705040b030a0303091b08010e 68
    0x210301800e14400401820004c01201c03000380096100249200a0010103000171000c10192091107000c0c0814511352640c80001117005842c1039807107407050344640c2c00c04d0282c1c541c075240840e08204503581654a080603442d202c0006030310f00010490a9040304003844410128000001d40c91910035080d405d480e560340d1510000070700392042c41c4c103c005040d40e200105115000540050507045d07010040070245841c0c80701d2503410003494000304005102460000c400070494a07504441c80c6030103410a0200b10501c00166440300348401c15200300d001080c0015400301208410416000e511400080c030f1450300c050410b00001c0c0034000e406e043e1003400d9010505091611071500c030705400074001c40c1045150b81c1c600054001720a14002140018030180c1404040f11003ca90340441c020211450700d841c69201c280f0701307201c660045204038204601140944c1340450b072807240700d8040c0b0b004100d8600d6814103101c440000c80780603517080a0440005a03484040d4000c0f060710740440141d500c0c5d6156017 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 960298048 1250 960296798 960296801
    0xc010e010b120c031b010306030b070201050405070b030106020703080714060405060f010614041806080d020a0203010e06060a0e181603030f1806030e1009080a12020f1611030105100612 81
    0x2c0b1582c155000c5d1941c0600c410015100301e903651014907011441d0303a00c079541e110300e50740240c4419016030345071028441084014800c04010303107141c28400d4299807400d940203544000910003d021510009440014440100d204039030701905030080350501c0c20545802c1d075807040102c1d600c81c11401030702c0010411503c21000c0d0b6000113101d000307030b41c2407a0030118680010484000d03400d003110350318400001c081d030090107e22100c1c0c540f0303005000034228a0061500751044a83c40c90540c2e0803c2041007043da564880200a6400d8241002e4080c2e80d183c1269500c900300202070900e0f40310302e18031340c884c1c0c2c0b031000c8901065034440d076991601540d221070b095038001601c0690b42c444030f052034802c0c010076100c0e903c04480d400c1014121a112851071545100b210359680f0152201e000000380320314000c0e00a58a500c540a190301e0440c0307040e80c901d8085801d80200754419014483d2a40c50f841480b050020440a0400c010000c00241c1407661008090a4251040b0300c042803a00010010b9000345 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 960299298 1250 960298048 960298063
    0x252030906050a02030c01111308060f13020315010e15030a0f020906032803090503060705090d0f1b2303060a151d060a090e1b060c010e010b12 63
    0x154440ea12154100350040c0c0307042d00038044480840c4001e02200b03507080d0b424010a000d92554440465640d82c01c1c80340c5ca084168a03401400c1603912100501014120304501554003001d03803251400341c6012880044d0800750245c0c10303110381030b0142e000411901a074000c00ca02900a40032445000f1103044107040e07c508040380c011f40342c862411072000150030207401030b941c001e0b8000c1c08c0c1c8400780d55408200b500b8540101011a066505010301810590003195020181004034002d18052500850081441c826007022034060411420b10504001d00414180b10960f4400800e0034a11f6204600d13030020003052040700218503502d501c1c1d100b0300c0e19080511441da40d001e03010b82002d42d07c0d1000c42e400350006404030107035010000400120b0b4070010111900662041203c41c4045c01c10800700080614103410480300c151412040a48030703d00041c41c190320501c080440e500d2110384000191046c004c1c43c42204955003030040007030007a003041d403002501c03030011292003404a03414098540d580f43c0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 960300548 1250 960299298 960299303
    0x603060909031b020613031b091803050d0b0406060f030c05040b1e120405030309060108120a0e01020c03010c030606171006080c1312020907030908030106030252 71
    0x41d29114003400f9120040e11018006080a441c03c51740c1c10807240314a60942c815512181d851500ba48013589140015000b00b8000c801441011103200325100c488064180c0101403007800a4034000428083c2c0183c00c4886000340200a440d503158005414085020160310002c0e1421310b00d07600081c001e40a48080e1440b00104604250000c901b000c50079101d8907505810140074890f403079800c502c92000b0b43c03069101d00040c64036400e00d010b0440c070700401a00118082c3d0481c01d010903080380b420040d911446a103180c03d88281c045500141d003801c0d003030000e06815508040c4d00101c440c0d0550466401c4070720030ba440508144002c01a5001100e090300c1d4034090404001c1c0030450315100d40b04007900324030a00c2c40540703000c007541c03031400040c451644a003008041112682c800d41c0392007400c041e840810340c10280300080e00c0b9a540c01c0350b072205000329024940d011401d4011440c03d0804020f44503603003000c95810800c10500d6820403240501070348030480c56007441002c0055940d0030b4000b0207030b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 960301798 1250 960300548 960300557
    0x9060905060d020f040909140a0f020405180a0323040503030405090709180c08090f0c1c0501050405011d1b220213240e0607030225060306090903 64
    0x5042808010321940300c00010b0202607000c1c00f50f602269940801030004048680002550010920305088050b83c09440a616078005101d4400070508181502c10601d9045800184640c2d030642d400c0c0c50002004108111031040035958001c06410618209512001805e658222031381f1011190b440d1155004064041d0800e100410041c10617015241e00a001030030722021154484400340c00100d080d040821406894101c2401c1c03240c1c000c0226074000040901414160303103100711084e43c0f11a402c0300c25010346424800319100c0c02000361803082a079403101c003d000b1801d0a0a040c0e01030215982c4000440c103514a64a4507000b001072080401d1004c01260548010203c1c10003081c4241003e501010385002c101900b801e2000744010445062900e0408507086e003001d1814903005000129680c00f104440e01654140340c00a242685c03d440486186035512290b2904074207206010400c000001c031005074a140f4003901001c114280d0301143d804102c03403a600e40341e81081d6048840b002e00401d = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 960303048 1250 960301798 960301817
    0x30a020f0907110a060b0f090402061b011b030209040b060909010603110f0f0711041505150f04030507031a010b0a111516030b03070506030601050c0a0204050c03160906 74
    0x28201481001ea001030702c0e00f810510300641c902c4960611001030011203956076101c001400c00e250a12401001c00800c1c1c605910744d1a080e03001c1841446614a0b0304520054010009030000003500242d1040c021b4030b40e01041c04008040140194001441040c4210b080c4841075805040100a03190102c400403d4251264a0720500740c004010031850b0940208042044004055065004103041b528005041e56a4200c40c00c08031380c4102c032005500d11990600c0407083d9201d08101c40c0304284d0b0811030f22403504c10744071a8039039003500c18008070700324000c03011400000740100424514112070159054140c402c4080c1d01d0119145000d004601c1c8038641440a00007084c07040910707807056810301c0202c40443c6d01100405501c90401c0780d02500011a0b0703001d400005506024212088a09130300070001e09042c00005001804000c19090400c0b501241d00143c0c14400c0080326140d640140040006040c0b00030201b08075801103038030a01c1000d49142c881005842601d0182c1211503036912101d11 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 960304298 1250 960303048 960303079
    0x4050a0b12070c060b0d030507141c050a02150903030f0c0c100c0224150303070525170105070f0e090103021002010905031305010e030d0f080a090b04051b030a02 71
    0x41c01020900b602c6141c0c5c0c030980d1120300e0711840500c41817030b0f004ea21a2a2030f0b01c2603203032064407105c1e6018182000c0d04050003070b02e007052307110058004a20300c604001c6e8458000182c00c9140c04250704403000f24907090720074000c0409021000754000e10101c9120615580c0308060754030240300ea19100e80b8a6404034501c0e680400041d4000c2d01c480c440c0f403040d02d1844400c107a000758454440b40d01c440c04d0410b0f001c2403000c58610140c928002c400c098020f9418104580c60f2284c030790825111107400c0c01035020f4100c822540e5260518003914140c001d0003d08880414628000c290440300701d40410072000c662004a0700541c400c0c060082d00503c1100c55a0944c0c0c01d010140081480798000c3d50b480700303440360014500380060030380c8000c40810119610b240500040034000b4000800e8001e410151a90000c50361064030b0742134200503401e00b40456240d00d400c0034018156000003030b00b0b00c502402071104020300800c425038600340d05035559442d0f64000c010140c81e4101d403d00250f01844814a13201d1 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 960305548 1250 960304298 960304307
    0x60403240b0405071106090703020117060a0b0406050712090e070f0e0a08010b03070e091b24091e1008060a0317030a0e03130308181504050a0b1207 65
    0x50095024404580c41c00200003160aa501c10340d405404a907020110902d40701c8100f0a16500204ea0350050a040749035800203002000320486200d41111100c00050058845a4500c0014915222001d039515030707601d40109103420014042301c800031141890682c980c030a03000303482620724035544444141c072440d000703845034070311481200c0c01e21031102a10b002550b5025840381c010044a4004603080040d0020076003000c5460708400c111581500520520010001700003407003240034500e052000015000250000010004d0729181c040d200725200d081070070700f201a15035681c2c00e980b800707405181b446805d60038442c104490340e0002c130341d0003000d401039201e120701d2508404090900490301d030b201e8842c20442000104c4812840c1000000d11040c00c0c80791041c40e128440c1c20010b541051081d500300311381c0c03401d0780c4000391410001040d015403102403030130b50800828004041c142c01d101322807140f4015402a103d15132048081c4000010113074108012102181343c1034a45c04001e6681c03210548 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 960306798 1250 960305548 960305603
    0x50a0b100506122815120819020c15040e07021c2003030403050a111506011202130e090c040b0f010c080409090317183313060506060403 60
    0x1112022102c00c0321030b81e054030300700c030001c0d0380d007161300200c0c070b8a08044120310001629030080402c0d8980f03404110201719038200341e602040000e03188485100f00328100701e01e84007000c02e08030b9001317600c0e03800aa107100c1440010f104481010302086000c0d07a4a10f42a070721904160b5919200d01884220b101c1c12500c00ca500681c08031151019a0100281000ca2443c0d50011602140803450000d40d0b0207000313030070100741285505110020128204003101c0c00c0d0b400d25014041c00e050041c47c030440218000d8075010f941c0045140b1000002032582c07142002050322099031240a203005041030800d0906007806951500d4801030726a0944060031001150f001d01100300980d880c4605100108026540303014510105020341d03299000d905152440c40c3e4800d00140401140c0741300080032021089011882028601030014a2650f80359014194070702c2150185520280303540031400c100b2581c08000c20f000416004000030030030b50343e80406022180c1b02c3d80c04050280107582801ea060124102c4810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 960308048 1250 960306798 960306811
    0xc0516080f070c09060501032f1b0f0a030f020f19111314010b030106020d031a0a0f080d050a021902180a02030405010c051c0b040b0a03050a0b10050612 67
    0x4514142050300e4201040f440354101a1049131180010041983e26009640d0002030206c03513404044007042852411a01e4204000c5078484041003400502e074074509104424002d03501030b9014448a4981d05403158aa21021404039190301005188a4800107940108001440080c00c0c11107881c9401a003841805034100c480240780c14540711640c4408410b090160f0b40c220700440d4001018500062808050300042805081400104030003079001450410b1b1761172509001469188651420846402d07805610707400118010001961442c4c0c0343c030220031244c03400152429105400d808a0341032041390714590040c0e11880c2c80540ea070019584000484d172000303100c2408c06000e0540c00c1c01002c0110b880340c4061390f02100b04011300c0400c1c0182e5215001e0751800c0c600c1c0048441c810010900305880d480c0040d5038401c00c940080d20360307511038221a80014081090542c2da032038020751322032280ba821603141c600c4a0100e0840c040506141c01035481c01800c0f182000d044030030722941410000e104 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 960309298 1250 960308048 960308077
    0x515010309140114091c0504050402090a0515090114090a03140106030b07090602101104061b081b0709111e13060e0a080304030b0c21190c051608 64
    0x20203001007441030311301d000031580090b6902d180c001801410b15000e004207100880c021a14a401250701130110790540e0302c02c6a0040c0c6901c01d1401160000c40c10350001500b014108410062000e083e40140c02c070318009a03641c0c1c0d80b1050215440390540100e0034002d4008550540a01c001601401c03184440310300302000107441680ca480740b4048203070607690000810700c002c40c10300920798140702c4400142a0303000140601d400000580d0020302c40c0b407082c83c0402c149540f560505249860070f003080107400c03400701034940550031160aa8041e851a03000e500d84070351440001c1000d203070b000f10900f01034108041810429642c0701510030401010800c01019000c02040c810400d0301080c08002e44004d542c1d801c880c41d07105090150305a19504100e4180e8414801000007a0005501c13030707881000e034403600342c0320b0000a01e0001180311b2400c800e804c0110384001c110301d019000e81a10740344010b040c0280b0230041e184406984902c54100314840c40c403442080c0901081e0000700914000c1880d801 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 960310548 1250 960309298 960309323
    0x2a100c020d0f03140d0b09070807120203100b0414011704080702040f09051606081b07110402040f12060b011d103501080309100e01210912030515010309 67
    0x4900030303540c03103001701401171a0f031050240d80034203202d1010b030707440302d0b29092849884c1001ea101502904901c2e200801303c940001c006146181d80d01203400040c96076182e04c603121916510203121803519118a50300056032413100c14424030303040701c000d80900d804c091141e103001026000d110150241c100742d07000d140c2d200c0003208002417041200c2400101c0304400180ca181c100b00b40249001000b0381030030368402c08400b0b80c03000d0810724011035200d558020044c040c10158140410b019002d903a00c4081d14401c110720003c0c81914000420350380070b114442c204054000580151240c8850b4651700c124a0054500b002040c03c2c1200010072030b1145003804010f9440c8544080d0540c03490903032484d01007216460b1144091401000c03140500440f5025500b00058a4081480e4400310016402088017804d05108035074058100001c1c60102188903603860300343d420603000a082c01903011199840c01343ca140c4a924840e22920b800ac0c4e081d20070070a21984013000450241650280640e59801ea054 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 960311798 1250 960310548 960310577
    0x21020d0f110d03020303040201030b040b010905130f021306020f06070807110a140c010206060a0b03060d1406012d0f23100f02060c0403020d03112a100c020d0f03 71
    0x1d98118404c1c0d004541c5c0307140620005080e9841102e0060180b401d111249d40c180c0c0e0055044021f031201900c0300307140e071800ca20840c0c002d4000340c0d000d0079209100082c030a030050200152002070f40d400703400b10b40c9040d5100448a80d9004107c4d13a07080010410004a1080c51080e4801c04040a100044481400c100d84030f4141800150892a0141d40004c2c1c1c03038505541c051007601d0b8020350883e07003107103001e24201d04203585100c0141094440c03045035085c170003004070796082850103a11850441e040f0350b8455400b021108104030814210080e112495402d0054541d1050150741d500ca15425041d80307002e0400100c240d10200d414203200d4010303c010447e0300e511b100280301c002c01d0b99a2007190481d401c006410050040c00082807004c0811003031001da110000d100e0251581490207258200b034020100707060003074071311088100441c01d0b28074214450110010040325903040303030041c2c0595001a8191040c001c22003000350088811050417000c504000d40d405035143c06824030790200794902 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 960313048 1250 960311798 960311809
    0x306040c0c020a15030b041505010e1c08030402011710030227041a100602030913090503120f010501110c0d030c082214032a03010f0621020d0f11 64
    0x40d04001031040c21604a1313803070f190b454041c0c480410800d0302d0800c07850101445018480295000f506e061010000d45507069444482155103105410041d0034500e107401d152051030361340700740e070160b001603503001d0352a2600d9850b081150107810800c6000c0c900910b140d0a2103540035150058a40d510003200100b00144041c402d403e205512450441014420445452134900300250074202c64064400d4140000d580010454072003890480b0800b502e0b030014a0080058209008018014040841c90650010b45017548c580580c2c0b40015628030b82c0c2e00c1e0401101d1150700782d03100001e03691000c000c80603a800c00b0714802443d40d001c0d2800c0c44441f805a101e011031030b03101c04648298420180e42180c81c5200300d1155801500000104c48003220403000040e40d50314800da07416271390b0007043c80d038800d1030034099126400a0038090003d001c0151964414002480301c1d1050242c003049100d40e240a4146540c0200d1074a91b004028044084136030701c482004d80c1e2000001c44240c9000b84c40181c4c5659003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 960314298 1250 960313048 960313069
    0x9060f101e03091a012909040c0203090901060e03250b1b010b0d0b01030b07022109090112051c02030904061212090e010b0708070803040308090f070b0306040c0c02 72
    0x9600d003c034444200d4500500240c501c58075a801c4044010018402c85081444907245846000ca00140900c00c68035106406d05c2403680003a440b501c1c20705e03c901c2003034011020f030090400031200319003070f0b0780d81c3c90082d00c0084d00050345a41c140c21100d410b58481070a140b11440d4071440001d01c00456440300d043c90021790044000301a41807148001091106090241c1c030001c02c4107488800c00d09180d079845495086045c00b005089849002c00200e04900c07c0000f840842c000f150144071949403800c83c500d00764020721600f4000c5c0d00342030011402d814845440300707101e82c0c404020300d800c1202291500030301c1e00302e8441400314001000402282d50f1640100405001d0020f05e485404c3c816103008040009800308402c244004070303200304600301c68040c0090450710780d000a25039800382454411003520032400000c1a601010040c80145503200f49072510428030030046911800c162001541e031030109210311000e0341410400240036050903000030100c1099030030504503410f01c070350004080d8200d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 960315548 1250 960314298 960314357
    0x60303020f1b060301061214011e0f1a2503080709151224030506220803060409020f0607061e060b0301031112030a03051509060f10 58
    0x4010203081200c201400840500d80282d005032600300b00990114002e800148100c03400d011801140c3c0340b0940180d00444c046480c0d0902420140d82c607510340384600340d1062070702d00300305070111004540f2042c813003c0001990000d0943e80004d10041035088600c1d44214020f41e103140600c0c01865403840d246104010643c842d49811516140c6504024030b49049a400b01080c031912003031110380300742c1080f40010024030b03412001c034442c2926075441408294113610215100403144c5d001040c0203004c80c0031800350316440d4500310009840078440345004140200507141000406c0825114903084d0700003116507201a050400030b00c0c54030005070103078000c00c2003a40c010351101d910b85880380c0e50300c06800402404201c200b2150b4103041c4020114001400700400110301d42e182541c49a8445030142d8400c1c0b09103007103030341c0c803206960b004004d490207803038800c1074249984038132042d4988103440074030601c0050f00c1c05101100f091f0811100c03a246070307402c00030302c00081e0940c0f182409410072000c0981 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 960316798 1250 960315548 960315553
    0xd080c010b121f05010315050406061509090f05010614030709050d11011e020a11030c06160c0506270d0b0709080709052715010f092a1b050106030302 66
    0x740e200000112840600e01c9107190794076160046c40095903440c02682110340f422000075a540d0307607162510041020b41c10030702c2640c240300c04a400d4a0b5100000c4419202c211005000203000c0ea08200260b410278010003011030192006180d1030300c190000345503c41071500d410a015a5a08c010481c0818100d9050382e44200594000360385581000303105240c40805005042c500c4202040251660480c000003007181c14104120041d560f000c00078200a12001007201d991040c01190b000c40144020700200d940b0440542d00048500d00b03130050743d81c000e107200d40810381606c03400741030800115400281c07680487d80b0051500400c5500c0a90b81c882c40707458956021450a20358003a1510015903c54601c0700d04010801072070f00c910f0002c00c0120742c200b101003003040341000c80e0343d410b05007444114008a09000000250046850120b40c100c82482d40100001000b00080e6030000002e203640040d0f01d00461031682183c2d10403080406e030030404000791881d00915584460030b41b01d240d0300940069 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 960318048 1250 960316798 960316813
    0x5040513050a0b09071b0c0302060f03040308180d050d1503140705030115060305060d120801170f060c09010e0402070f1101050304050c150d0f0504030212090d080c010b12 75
    0x6000714800c03400c0c0860211003410042c903161000030000d802c90340d1504030306486d500502081008070040c2c007010310703401041c217500c4a840d00910708043c0c104031030541c002800d070004203403004004031800148039070321303000380100c0c80c0d4042043c1d0f4103601412611003049e0781c3c0c035521020500d40340a0000598803800a03203c04803c0c02c1d011501d468101c1d0080c0f031003a494600c082441c6154a01547c00301e44403820302003855503480e80014203150b282c51016010072503e18400c000c099102c00b0090503106528041c662151041e9070455403000113030008101c0342d1200c400301d40d65901e2800603040c04d100515151141c40c3c1030401240981e0000c13602100d6001c05403400d10100080c4c0c50210032620000c1c81c1c01401c42c601030700d44903a108420310340701d801030409189040c03510104104540c030000d0307203500c00d2014000784890705006100c100c2c1d054005005481c4180002c82d1010f046804144000340305600200d91a203030442c55600c540c1c0000180d668821400341180c60341c81c02003004129000241440 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 960319298 1250 960318048 960318061
    0x1810060e07090605180d15020c060f06010f20030d09050c090402030304180b1e0a09053309090d18150503130209012606160c030504051305 61
    0x1000e40035140701d00b404000c0406106040d03200c01520103079500020f003101a2000c10011800d03000b500030f0090441d003107140c4042180c002a40003040380184107002c0350900c0c0d6070200b4a10100b041610050b0000701e0f1900f440702c0c40c3d0b02c10a2802001024015104010b504140c0302da8919070210324401700443d00c4502c024184402030084000ca02c4081c1e0b0040d8240c030305a40040e84a00c190302500290001c0c4800681c1d10b0a150780c44843c3d800e0001c1c1048541100241c12101b03858050004580325118280300481d80710300c00d008240c0601444240c41c1200700e44058400f0080b5502d001c080b03000d2060202e82d003195615801d90314021180c090190401d042107140040a02200b0003903088950781d511020840111160007009400046150440e20b070345900000341480d601c2c605010b58401a240c0000c41c071269000c01c44807808200d581800102c0030702d500c540d602d4490403202d203804000c00c0f0800c0c8110034000c260184103107100b4030b05103141584504c0000c1c0003020036404034011541d5201003012 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 960320548 1250 960319298 960319319
    0x80708060c07050703020904060216060e10270f0c1d09030a020703061112010e071214070507080d060e04030e0303091e06071712010f0e01050603181006 67
    0x3003004000300924542141c54540564032135081c4802400b40c14120000b500303000030341e41030f01c90400f214002855250090300707240c4050080300c80700c82090700a001e05882290811700c19030710945100300c008c0c2d108039060380d529042006000c60a5aa10034000904000a0750310b010103c054010b07400ca44212945080d1000c074407035401010000b880e8401c0000e2103c560300080c980084070717800f1001041014060001c20513900404002d015041400d60022900e2004502050710031003160707484615415107400c4441c1030310240d013102c60f504889440442d640500c1540103116643c080c14500746000f0301e20680000702c0d011688081250756695040c4030805038001079503803540c00111700960074203150740009038180b0580d1f400c0e01c0c0302e03410312a4041c4c00d80c0c403400301340c600240c0c20440c50003407801c8980c040c24145d0f1104040b449005e4070340b0000300341d80c1d50144603502556a5255086001d07801c100c04e11980f82d001400c80a80a01c2400203000d940c8420001e020707000e501c0303140206045280155006 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 960321798 1250 960320548 960320551
    0xc030501080703030915300b04090f1103010e16030201020607080c090d02010e0d050a0b0606040b070f052a12061501050d0b041103160f171803030108070806 69
    0x80d841d00b2404003000421341c016805001c0c2c807280705049010025170b0605444c100002c8506140c0e141c0f041284079940c0700b60041c100c0c0209035651041c4840d0800c0da003003104545920000801e9200144d2481c40440e14036054481e0303a0340c2c042c00000d40320701d480e01c465141c101c4108034184281500341040c000c55074140042a003010480c200070f08141403800031080903006075141540100c80c0f400c94001560700c03a07541604401030240003006510a6070038090386031313410038100b603c4241c0c45002041301800c3c001c0440703048a1020038010f050004030f0756285485000c40c031094855204880c1c2d15491402c0d44040f6840d81e031004c3c41d00b90740c8105c01e18103001900070801051084c40d00020b003004010742c8030180d5285c0043c800d280c80b40d6120f4031915404001d040c05505103030403529082180100c4d001c02c0c0015802800145604051124842c10442d8180d07501030f54000010840a444210f1105c008015138100392000019802008000c0c0d0715495034009074498112588a403008000080d1309000c0315 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 960323048 1250 960321798 960321809
    0x303070f0311180a030b0108071e0b030c0d020405030607030b01080901050601020706110a050102160c0e0603030405040f09140105060a050114040605030c04090608100e060f0a1a130c030501 83
    0x10700280c401c02ea144249030040d40407245881a640071031242d5680d40d044080051503021080d0001c5586842042d81d44002030301890010070700902008240c42104002c0004841024001618581d9640300280300e9812240005840729024000400c582d50180803107441502c0c079640010780360711414001001101c01428121090340740c442401342c0c0d81d0780420043c00b607880c0c500706400c4492200841c5803506540c1d0001802c15480425241d400b08004002e04071a54003c94424810719102e03001e1214016040e0380306030389030b407081208220740c0c101600090042e6600300740010f40d00029072111242e5591480004040e82d5645c01003010034031304104070a000d4842881c01c1d0190640d000312025183c4940d001d01c105012002c00041d514410040c111b070701811100f40c05000b101c0c0d072500c0040d0b83d07001f541000f04200e030501c06603a055440005090b485465100400c0d4a0703a2102c40d07001c002025418010b0040c020403480c005c4003a240c801000740340e00302e4001c0014950599243c0102140d1040e00305 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 960324298 1250 960323048 960323051
    0x60f01180b1e0d090201080906160e060909070207180b0108060f0f1f03060b0a2c030109030804050111031314150420030d02070618170303070f03 64
    0x10032010309040c00c0c50405541c007240c1140d0340c1c1e01100c5940703401054140860100c0c40000694540c070703404a9004011040c0c0300783c031000ba858445040a50700c60008551079100740e21041c0d504540f01d84a40203201c08180040e0801d031400d0600ca001c2241800c0c200c6201d405a8401c94040103a144a502c0c411050f405414080203c110308400080c021346d03025080d50710030100d0700380c1411580d542c0d02e01c2155108000b400103260035504006160718108980100300442e142901c0003c980191200310f504407002030355110440c203800740031103403c9402c00d02e1131000c078486c0000407001624240303d900c6c0302c00e019854a4400d4546843d00600795140034500891090b014818000d00c0081001c65420540e48815584500349048806a1800c0414111041c00720625002d20082c0310145c05d6003910300d46900c2c0c4172900540c840b410305656611032002d29005a03c03d4800700583d40c82410387c0405402d0b218440703078040b6070310800544010020026020746410010501c0601908440e100b4009005402c0 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 960325548 1250 960324298 960324317
    0x181902040b0922020304050a110a0f05060a0c12021018020109180f05190b0102060c0d0e0705090907061205070c0803090f0a0506180a0203060c0c07030c0b03060f01 72
    0x3015200760080740c251074060703031400003403012019101200784031410305000210348a10b400d082850759050b80c81e8007683c00400004080c00141404210801961146218000c9a0f8644014880b09602000c000406c0000c00c01c2e040c1d000078900c079a04030b03101c00340d98010703e198541d44200e1021500e036140e031a02456482031490f00180d0308071014204942d81c4d07503259045042101e13150380152840021541d0480d1406c820400d50f201c034601c0050480894050401c580360312a00161390312101a14034044405060102c1010040950010082c07000064203444d8855903507000f0462080741610740c1845900310540c14041e0a510440035024040110300c00c1c040c41c1030140300501f03a80904000036120a00020009008000030081801d2607040001140d581021906050780c4809040e00d0b10758405201e91103c0c00c03500000103a8a2450741c0040140803d40c40c1d00e903880d40d0690110a01d041580640c100000100c4c10b6180082c0080003001d50169491400c1420418100142e44403141031011313980 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 960326798 1250 960325548 960325559
    0x221712161103120601081008070330080402121e102004051908160e0a0204050603130c0f0803070b130f020d0c0f140a0e04030813030e18190204 63
    0x15454100e1310a00b40601d45458201010400e200b940e00101c0300c900c0f03800400400c110170b800583d0340b007410030591900c0f0291620310f944104000524104005184a0041340243c034100500390080f8401004a84191005101d1124801911000030006800c15403086545241c2c501032009598582aa190304070b50a92010680d58010780c05a03900a1580c1d07d00c003282c41c501190290050803425045590070030041c40c0c800b05205c9207002e18600c50b0400408144907903a14025501560401002e85066a450b2414280c1840d80c494007070f0786c942d5881c0b10000d240c54420f181c200c081c1103030380d0245507079111a0502d803c0030240035103900c5421520040b450040f0f4010740c030800303007203604440d402090051070503d0282c5d99541d811080035050203510000c1c1403080c161241c41804000c6c2e9004210580d83c07801c800189104580140110720800000f480e00d5880e00b41000149110741460100040c1980200741182d05200c054840c42d06442c05100ca41504c180c0c0d5880304883e1218154502810302 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 960328048 1250 960326798 960326827
    0x60b03010f200306060d02030c0d20070f060b04090302030d05090a0b04020d150507030f1107020616060905100c0816050f0a0207050d030314221712161103 68
    0x452901d04000800401d1311070307864100325040320421100542d01c0e8200b02d130503d9050303030212074111900f07480e00b800d603440b41c0c4002a80d070799150403551110703041480f10380ba03854580202e9041141c0855607080980c6c0c59964500c940c03031a0600036801191218404407840003140c5001e090400903031b01c15001017000880e00580c1da60710a82c181c40301d01188189180c07046102890032a492080c0d400c22041001c400d52650000f01011504142400404031020146030544114040a034004004004c03103643d00f100a030424070304500c00e04000031074000c15200c0c103050030604030360070300d001e61960752a5050540c081401030b0014080c54007004031544422002e0220311801c072150325204001700342007071014000d04c440401007001414404100303034a80b400400400d0154900a03005003820042140c030401c4030010340044001c0d01020700402020b880e0a0031039080e4145541c41031504010008140e0031040702d4602039802d019800c0102040d101000d0403120760344801d052039505c00c0c000503803101b038070 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 960329298 1250 960328048 960328091
    0xb21030901120f06081c0e060f0903150c03011805060907181a0c010501060804030203180d0f0f05010b01030212130f080406050903120405030d141303060b03010f 71
    0x9080c0702802e03030701004280d00541418001c40214502e0705000040d9080b011075141c8086034100c540e0214203412240c25a10074001c9003400390041020301101c840c0c9a040c1c0000d11a07040000c2c11140001c1e40c0c1c04884850312000c461600c01c801c0c02100402035203000c0a914400a04070708401e104c1842d011001c01c0400310000c1c000e40801940b1a01c1071000418a10703101c019103503194040d100384100c0707170008820741d1054003e0007041d80392100000e552072040b40124021941580998903040408022410350500408481d6210b0f000e02006e00000396a8910560ba40780300d038501c500903400302d0814500311510034002c0c0d41030600400543c481c01402c0c91156502220310b51031040c545040e402c01000c08061540020310014001901040d200d8100001c0c0400c200f04508691246c0c00c0e01000e981c0e50b00652107265010341c400302d4000341d141e003d010021180465400c402d800c100302600b040440b40c405600a4691a0369075040100a003800e004001030442c42c84410310415001004800701c2061 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 960330548 1250 960329298 960329317
    0xf010f0204060215040204020f07390303030c170406091104150306020f0f160c050f01080f0a0b043303050a020108130c0e1509040302120a030207080d0b2103 69
    0x1400b400117005c643d03844d8141ca014150042029072079543d6890072a000d07104000b54030f1f082c103c0d0f55078041a0003150342c0c5034016445503c00608034072891507400750007500e0b1030300100081c0088045003242012407080040d202700c1c0a2500801e601086041a4400041010555004605200b52940b091050138601800caa900040060756441500c1e140840d501032031001015050000901d98019510002c030f0034851406600092a07807541c900c104100c044040c42281c0c007240701440000c00321006809100c0d800003115802150346041000020300311601c01d14240000528480825075580b19046058180200807881da00e00e81e003035403141607884d000c0400082c1004035010024403903841182064401c282c0c41180701c0d0f101c5031035510450072001c00721561503a401c84019010341074501039170f130f00d0b02468040c6c024150228001e99082039036403000c0c9021050580800103280040c0030100180101d01d00d100b000900803800c5010031070304040c41c4140d00c00645c0c0e03d841101c421580070003200c4d900032 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 960331798 1250 960330548 960330583
    0x112b031401060f0e0a2610050601081512100e0f06010b09040506180c0a0807020a020109060809032107021c0e01030506150d05060f01180b0c1606020f010f02040602 72
    0x31081e00001795128000c1d005048142070b00080e4100c00c9010b200d08814692040080d01d440d000c81d60000422070b181116140e00003007041c0c020035100c0701072080c04840340780081e003212511900c0f144c04a00d4490401d4204003155a030f1203420a051006001e8858042034000140032294075149928610380601c9080c244070340eaa410105640d60340c4d0a03210200380284000c0320741e481c602542c6848064201030b9400c0049401d500c0000d000720f2021507002507855058480f821010700345841112480001003044106200070005006c00541e10720f640c110401c02010f454486190150000382800002002115440c20200c580c0c60025000076001c41007070000c3c80c000640765070313a40001e41c80c030340030080c00700031034000007101081d85040703070060f501c1810141c07022070a51103040011a8007a0b00821015081e0040310803d000c0c01c000d0b94010f14001e040380c4103c4500b808600f14004072240b90303a201802503400490400f1403468203003e8141c10710181c0d001142040d18041c406501d50041041469851 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 960333048 1250 960331798 960331817
    0xf020c1002070504230403030c0207090b0108130c0504090507050411070302030a0e13061806050a180e010b1011070807030c15090801180201110a080703112b031401060f 74
    0x302c030640e6030b4000b10141500c12065800c6c0703802c001c0c3c01810000c91660041c0030380c0401107840c01260003140050081079440008039a0345510072100c100700601d04480b180030b201000501c85ea12400751005c014051310240c83c0c2603140c4001c000c116000c400000d410010240014004240c0100c01c3c5d031884061030074540c0132500303c40700151041e154506c103604613514002001c42c41100c0180e0f400300d6a82e040340c00300401c41c0c4803010021000d225100340141d0701c4c00e06540020701c1d0380a410174202d092001c0300100f0304080f60300010f01c064044e03000450000706586042c84104804000d224021f20302103001e001c1090854031003d40003606d5001c3c000b469150340e584d0f16012849042d0b00c1f802844c1030343c020000600c800c15200440c04020b00180d0004035101c0ca442074041001c9070800c20164403034282440d00ca002e5a085d1079202d00c0b240c8a040c2402000700001014400b2611010208941100c0c40d62070804080003400310b942d1082015840c56207070f0014030000b43c01c002425114a0682000e0011 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 960334298 1250 960333048 960333071
    0x403031d03180405160c0f111512093702090109090b0a090201050304030f200c240a0e1f091a0a09030b0a020f0c06060111030a1407140303070f020c1002070504 70
    0x1640301000c6032382d0b0008148520f000d4010303659400303030150382441c0000782429155020060ba4443c00c0b2410b134840501c2c1030304d00d401001a000c0c0f40c882907498044103203841b024150000740d00604240d00c003407801034465020108004401c40015800741c0700000c04c0005545940000304140001070001b8244500d0303101c0f0781091401503a01d10202000009a8200d1340280c80015440d1604820054060844191241d55040002c0c2200203441101e03d4101d0405000f07050031102100c03c0140c083d00500c210702c290f82020400d4900c404922031329114451802d10b4481400c82800e92154070041c040400d00006030003a6004550b00101c80c0c202e40d8003c6075890f0305001c40300030b206e1091507006c18140025014003e50340840d01d1032103242c090300da114840c0910381c2d4554aa1159984110000b000307000130311608082c803005040014021140034017401882d0807120b28541c019584200401c4814181c7c2c0c5550354100903c915005050301c0c400307140c0c243c402020755180f440d4081d00744141e03120243c2515 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 960335548 1250 960334298 960334313
    0x11506170a1109030615030111040503100f11040905090d030212070f18030b0412031104090905030918060a150c0611070f0804080601090606080403031d03180405160c0f 74
    0x4a443c028166035560500c98802c3d8072260301803140900035403c1042d04118219240292821520060301411000f040000440002d04458404c020510341d00d044a91403032940601030006070514800005a03401c18809462501d241807032040c0c10980104070030585252080006604901d07a8181040000200c07d4143e031842d24140724616118500c00000041c00105011076001e0382c0203002c5420f4980c583c41c0e0444c20b5070282100105001410030007005140c902d03503c00005140100706a0313040c400b0040008861b10740301c0b00b041c01d0042c40070080c0322113860107400c80700040240c8a040e64841034038000180c40b003008002d0103800030b69100000c419032083c501c03c880507154030400a0f424046945041a600d8001c1d0090000d9481490004260140c4502c02c01040e01e43d05c1d11000c1e4a0307662540e040340a048005e0120444600070900c1c01e8980c44200003514105142e601e0310000d07840100c0c107010031a1801403c0140c400301c1c50400e008101d80110215178207541001600381000400e040908 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 960336798 1250 960335548 960335557
    0x10c0609021507150b0a120c0306020f042105120a0302090301021b0d020d0c020906030f07230603010f2603030108060f060f010e04150b0309011506170a11 68
    0xd400402c500384860065001c200200410392040140022440443d800b00040360014280150000c1200d03074107118106030f0341c10800c2a00c1c45464101151920380e07460070103076040300c00c1c2c42d66507000105081c4507142c0103050441403407010050a03000400c0e50346500d0b55921342c2d0044034406800020701c5040e0300f40309030101ca2092002070003d641e9884051815034102071a401961003a024500e04280d44c5132000c50300c002000c12941d00c40340000d10036000c000c08844054440c0b6450b104402140d0051b0406000750383c01080c1038000c480074000191581441c41c441203802a202e100b00304010b1003c222204001010760305009400b04041422900a400b00d81614a2a49280c4004800090600702c005907080c41004c404141c01401e072240d0091181c03011440c5500c9011600d0141c1d003025609096008100d2401e004058107521507a81256420700d03841990158056515040c000c1d0082d441020300300002d21a07450300d001e0b9a60b1808005000180103400f400e48180c0307034800d00501010101c1501c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 960338048 1250 960336798 960336803
    0x30809030c15040606120b0a0203190c0e010e0a0602031c06030b040c1e0b180307120308011508060319030519030905070e060105070201050915032d010f0302010c0609 73
    0x395821903103409041d1800702d045404551007800e014000c04c08000f2106280005039100030540c60684400c481c18004e034000a21200300315041640d00142d10102e4010410341c0c502079121040385211900004001c41d0f029030105024600d03030842007150a1f800000c4408a0040d9030840100c64020f0740c229001e00300907800541198994018001440116442501269814006203a51071401440e00d01e00305c116100b0001000784c148a042074040540c02c0b4400c20a6009040c2c60b40b0a84421300c1148000603000b0550000710504014465070090740c28142148a03541044100ca08d0290002946c904100e56082c2500e070040c541401058082c5058030b900d4807a07043e0303041d01d80a4240004000b40007070403059170544288070001175041c1d16100a54000ea0040e52010b00e001c0203a00107641907480311340001e1b008510186020050800b040c051405180d42403800c044103c0d00d03400b11048660001c9a41d0030102e04100104000c60030194040c04895082c2481185150300d410080001c0000e890701 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 960339298 1250 960338048 960338053
    0x19120c092318070306082e06090f020d1a150a1107060f3b030c04230703050903040e0403050c0f100c0806090604200a021011070b04030809030c 63
    0x1528060110700d807400f03200b071040d540d081107400e9071800c8072a51440c11506483c4e0346160a280d0b81084403260b0741e2050091070018020918940e1913080d9003c0f070361540c035450324059010903820031501140c01029001c100064003080c100000c1030014039500083d04400e02445400900003035000c5c0100400456000e500043d20145a81c03a20301410900501c0e0100b000140c0c3d4184104c0c20074540789170035408000c9031864003180c0040d082d0050078500c0040c0e1031903040c8a11200240c4075642d41c000d42ca07a16141d01400755000d003410f145881c0c90300b070190104040c9400c000400000c410008162012030304640c00c05000750700c4904040d916480703414a550041e01500420610b01a800200c0003000310b0a15400c00295111032001c032a046001c0d61141d40c0185440081185407030f250700081030400030301c52121004080058080000c2d406210340c10096080200d44401442c0a8810140c10613101d0080f28a40070060350b4079608072200400c0281030040303050109203080010402c0c0c2e54030080c032004 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 960340548 1250 960339298 960339319
    0x14010305070216030b0f07022a0102101a210a06090204020d14090d050c06131103060114030106090605091f12080d05060d0f030e060f19120c0923 64
    0x10174840c03c030710441d400b8107200c2e2a00301152040e44000385048400540c02d910452400380c01e20b80440c9005c107010358a0440c803604d1464441c3d00242d10800042c05545060341e9030503103400c0309201400d610074964050012b0083c1110910404c01b0440190a50380400c0014100115100090090082112000d02300d0300c1d01c03c4003401d11221144942c00307031065800315000403000540884144c420420045159041400403407240f203441d070002d007040c0784a800e062542100c04d1020034907020090f48410b000403e541284151820280300300341c0605004002408001e0600740464841c08001d1700c11340c2d1394441f807113600304440d6100c80e2040103403021054a20b500700042c1480701e46508405105070041e0b280c82d012400c00d00e0041b200300711290788003c0c1c07851a0702840d2803c2c1c443c17461f40b10116800c07200400c940720510704d150001709288010203008803840c62007070200034080c04d0300b0701519140344d1816821010868100303080c03031b00301c910401c070f60004903c40141c0755131041c003504155900942c0c0b800 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 960341798 1250 960340548 960340553
    0x2107050a122a090b0f09070c0807020a150804060c02010603030e0f0a0f06020a0b060406050d020909030d0908070303230a020d1409010507180e0f0a1b050d0c03061401030507021603 79
    0x10848140303034074202c0d0120400031044c1c5c1007081104045e6424008101100505e10000d42d0700d002034501c0b58001000301d21203541c0d03001001e1000f2030443c10ad0b8000303100402004200b1265120f502c001401e548001c04c81070313085640181ca55685500018400c80c061583d1035120740d10f0a0260003e400d984040c0b105040c0d94280c082d550307525040044900d82019400580d40d801e05e031180408643c40100205840111602400b0703126501804e0180540400c21008012040f903000b08085140304611403a9920020b080090441d2268038403a0207801c1850a00d02c04030001030580c1d500422100c80040c3c0d00d00040b070307240000b081e80c6400e4100750043c50041014030b11301075100c24858441503c60f1150340641d807141e540b9140d014081c01d04424401008203091a4032141e400303612160500c400581d40414404207160301446099035000100300140c440d1946201d401181c02c139000ca4103050200307500b008541124101160a11410141e89030f001605891003001506c1f4900300700301c01281c10544a0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 960343048 1250 960341798 960341801
    0x7061b030519020909060d021804030e090c0c060105040b0a080a0804080105010506030f070c06140a050a0f1802090406060e0c0406020606010c0f1407052107050a122a09 74
    0x200d44900c8200b1200044a001141600884982c40c0c40145141c8940e40c03403d04021004400d002d0076a0880781d900401948145d03820340042c01240681c4902c42c51115a0ac1085007030711005002035608002804070600802c000221603042d9074040b00c01042012803400440c0c4007001941c4000898400ca070649000d01c46004000c4c03043d03d08074030082c00b90ba0f80300c2007402102e21007a02c0741100d40c000380001031459445104400c0031244950000b0030840c4014409000e21001510005030803644c52042c4a82c0d80b41c0d51040340c0c2c000300c014406210700d081e807030096586032202d00c00103401080f580002030100003580c1d008401030800080341000c01d042002192070581c0040c069803006d4803c0b40c0200d030f1346600031182620340c5940400000d1f0403810b90358544004e51690b0401818611940e107000c24660f0f1140490141c2240f2402001c000742e03a2412105d1404049500642c0618000401406010469120424155003001d060624503000035000d2103100c51080030503400d001e60540100303800078503 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 960344298 1250 960343048 960343051
    0x60102031e0316090305060c0706140403030b13060506160c0b031f0b03060d260d0f1109031213030f0b0702210a0c030215010807030c1707050607061b0305 68
    0x3103030704a222203590800030351301c908181c0009800e9600040014245a20b032038020180180b058501052030b00c0c07031020b140c800703800540b0120042900c42d41d20300340d1820003400101e00148884414448589010081703201441203c00d81d0000e2445010b00f0001c1c80b54a518105c000c0000201c05992440c2072000503001861940e46140019070700e11000600000703000c1900c0c000c6100600240309402e180c0e075400e000307005200c03040a5151404070451810761054015080c80c1c02403a1001c9600b40d80013113004215485841c400c0004d280a00030b54080703840000d900018a054405c1c7c1c15a03401c5088203200c0c0c0049143d0000f0081210300b00c1040822076540341c120f0044416408986400ca8402d010198848911900f502c01020a11003590541e11070607000802d80d001c0d005030f8240034450a038051550400b40c001c540c1580c441801001000941c40c6040b004140c1420f005591000000da0b55440d12024410f0900c1000085540001e03c0460350001080102004a10706144003205016024100 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 960345548 1250 960344298 960344311
    0x61a0d060e010e0f01081c030e0a0b04142103070806011e030c09121203020a09050d061b02061023090a060f060e0a0b0d02040b0406050304050606010c0209040b060102031e03 76
    0x801c000040c50316400180021f035114002c0d640018030301084c1c030450040c140c8040550340c0744070703810802010400c03524405020f41d000e18044588010540c014601d00b810036404100081181070148800140c0b0704240d83d00b0101c81d260030102a280d100040310315040c5e00d0445260800d11002240c20f042c0c042d0302c0031300c88c22255103540c0841e6607283d10a201c20b80605201030000381c480506508858425030081045000301d08041d202c0341d07190f202150485c180818100d8400c5e98481100511b4524944004154807c0344010070940c60190451507003000d141c0300b00c4261001c02c3c0c8040281c1c9004044003051a040902946107a20308480300da030241c24135100e1812440000b80d00402c00764030030310040040c020081c1c4440c0361a4503181108056901c80180301c504c0d00e17400d100106000f580302009000400c12503a41540743d0803d1f00384503003040400303002e0505104404010030010f03100c04555950054004003001d85e1540c1d03a40060341544582c11340303050a80d141031540503021040c240990b00800 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 960346798 1250 960345548 960345571
    0x9160b070b150607033002042133020c0303061008011a030c09030304060c1b050a090b0d02060a02010c1b05060612030d0501060305060f04061a0d060e010e 68
    0x122810036020514007658034843e0008070030014180428020b0402907492402200d08481440300ca84c0894001d00f00202d5007a6207d400080410924680e0300080c0c140c141040900c041311045035688804694010200707036400c00407105d01c1440400c4c00080d1469040030f0140a40d520609030004076107941c0100c403518071980a20344c180c0c03007562040312194180d8a00301040501510700e0025a80740360801024076503528001c100340c0ca5075032024806040202a00d03111400030007001d2400395015052072013401111200082d04014556030106c0010850700c1104000417810300c450080f49034840083c074040c0d000240003030408070955055006d00403105055840d55607100c2c01105c4a07a880000c040054410fa1107000851801c0c900120a1140102c1c44c100306c034940120212a002070790001d07881000480d50315010031126003000c4584c2d0308100c000321010032415080480a001421000a000d04e03c59000b14020394010b20941c0250050800308140b42d10640c1e40d0507082c00020000c446054110 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 960348048 1250 960346798 960346801
    0x22090c080d030c12270803041e1509060b1503090f0a052503050a031701060201150b03060a0305070f030314070b161e0c050c01050a0e060309160b070b 66
    0x298428443c00c20150f4042e5918074005040e00d00706400380029003e200c10036120120799010b900020070621540031321441c82e03103031203103480c0c10300010070400798207914009c8800d02503035000140508900345a00c6103580c1c00141c0c16200d818880010001c6016480c0c0008580007807000c2d542c6090302552081911904075075141658500d000d480d2000c1040081941e8005c000d1590000c0c40b2858000030140c0329088055596502d4441c545404080c0900f50041a144800100004030000c101070240100e07000a000b41e912480019494074058410800c01c0540403010489694803110035800454100045032621501c452380351030a06454402100415074081a800c201e1300100d003503900356030700320660705a50b540b004001c44a031030701c001c80c0204100c0c500021640c10b0021440100d0082c03515958aa0b00ca1158039040d8a4014400a1a410304c901440900c503c1540130341440500d50054500d02e4803915001d48007490900d00c040302400c040080040461106120400341480502410000078103 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 960349298 1250 960348048 960348073
    0x3070e030d141605010b03031306140a02060708090102190801080709050c12091207050c010e040213121506081f02040302090a02070f12121505090622090c08 69
    0x449a03461a0045140b0041c00006107056680c114103180314050800412018110b1002a056038000008070711503001c00c101c2406850f80c414a21140e0f002189001445c0c2901880702a42d2410002c2c00d03001001282c0c0e00040f903611003034060360b030138442c0c281c512810440c0c00380380079003c90301c00d028441d9540b099850008100e0998001c480c05645010f5150741b800708058400040c1e140010949070b1a40b08900500004c004004000c0c99801e0040c0003401e40c0d00400c3c40010180b20901e5030a030300c5540184101170403880c1c180c0c211000c9501e020031f0468902450b2074415038528a0021000c45d4a160000010b046c2c40b000c118020019400041c100020031911a8032080f0300581c08041d4101112000191780422194014a0341d0350040d200d180f40c650f419502e12186d60794156040e80000c04810320140700f10554041c8044c40c0741038a40c40c00007941070070701145d50100001d2095108101004c0e4034000250811009142146100010b00c400c441904000765189518842c40c246841080e604014 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 960350548 1250 960349298 960349307
    0x90314030906091509090a0903030e0d09090e07030b0127090c0603052a04150e090c071502030106090f0504050f0103110f0d065c03070e030d 62
    0x250710000030601403c00f080318040c0060381804101c0c8190050007000b41d042103540e0b102a20b440fa140c490b1012441c1c0c0f980e458001e05a441d00c0142c0d80741e540c082d01484400c160851040e1041d140f10b90800103508194071602c602d00300c1303035070320150850203844d0010400c1d1910510070b040488140c01013440c203021081080f400c598032080b0160442c0c1e43d200c801c2c46218480d8009a030054238030b248982c0e000d840e05030160300c000b490031118003101400003400c011102500c400d9401100e030604000034405840c801040d030085c0010304049035000000740180800c4220f981d1945241121030086440750386415001d403002e0546d000d0b860f49100481000a1107281600500c0e00c11180710f070104c030150b4a559603800030290210311083d88100d95645c15959515a080500c007028060040469000d0111540022040c00c100a00a41c803400c212030181c0954031003c0e03c020b00381980c815a92610350112a607000390100400b40e03c03241000400c0c00021a48a400d0015204003102940c441201c8480c0c00d40c2c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 960351798 1250 960350548 960350557
    0xe06030d0203030c09012109021c021804021206010801050603070f06020c0112021b0705040f02070308070c03021006030f03030c02010506153114030615040216050d09031403 76
    0x10b030300030070001c0c1d00d4480c00d8019101c0c1c4841814018000039404003c040703100d205408030b82015907207403a458194980000c002e00c4a0803030201c1030f4100c1c50b40703030041050b038040d0600510314001c1d0440418115200c00c079440d9010442a01582d98550312004a10f01800c002e6415512a108030640402c0b041c4401400360102c690035001070034200500700c01910324010542e1441d40e151b90034450311f001d01c0b4400e1005840105c80c84c02401076241004204012914910750180c501ca10500950780041e030007502c4160000010b00f041007054003185422031600e40302c00d1128142a04005000017000901071650751070901c00d8509002c0d5406100017203088440848031550b00005280c8911320096240000b0413105c10141e4845a00903958850540802c503d40e0200c00390080248041110252030070441c494443d04401030034403030400d070056425408001d4503441c49a6800502c0380081c2c13000c181801c020581c0701c4140c0e544840240340187c070099261009031070001e00c202603c580e40c480401202c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 960353048 1250 960351798 960351823
    0x12040c060f1403130c0306150f0b0a05090d060605190302040c080708010b0c1c020c03120f040306020f0c15090c040608070e0c0c060a02040311040b0901090b2205010e0603 75
    0x80b4299611820440d484c0490540c0035070340003481900100c0401c030240113010074840c00c11035040c0c52a213004900c5c603403903030280d00080d950541800441402c0350f0080c203ea80030b100c00c035564610b0860504050340200344c0d55000540c0460b080700c1407401141c40860040859000702c40c02c005664407507205a47d1440e00b02c03014800100400014040400158007030f140603080e0204850b21003c030005848101c80c020020400564060f0810001b00d15042008a92821201e01c16604084828600d400301d80618003000786110b4022601034018004c0805940c120002c00040394800c280307044000b408150306582c0c54100d8040c400c241c64050a06004840480318100010001e151902070300e011909401f5200e49240b000401c86000c12120030484a40245030400700180c0d95803641c0381180807440303400d8540d4066814140000040d9840310250390450340003180c0070a40481c100c001640d95100384400da240c4a2900d4010410601240d1045050b11907142c0c0200c40360b180d02040540d41e040c0403489 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 960354298 1250 960353048 960353087
    0x12041a1603051f12050c030a08030a020a0e19060306080a05030f090402040e1609060f0c020d051009031d06091f0207030c09091b0b0f0f12040c060f 65
    0x506031190303100583c04400c0c0404201e0000803c50010b03800461030b8441c103c240254441c140900600b481048100c0100300c2c000c0c00c090311030750707910010b90000600700c0d070102d5408a5203640f286d00910203442071780c0d0028480c0180c07c0540c08850401207642c060400000d10b040c0000c80e20080c000b810170302260300719000350b0504010101c00401540310780a1a90032035000e01000a440140d880f00d28001c10b034205820309041ea00040c001d01040c02341d400704081044212012000382d810840c1c642100fa010741d0007803c40d070210b0400354640041c47e140110312514140b001c1e030074154820548a9810380d0a1002c90225054404014207401510f120b55071204840c90a070810120114080d1000d02c0e09006503905159030351202c4a004a903648000031143d100c0d50100c3c100f24010032200389404003506910021400c2001c090074500034070260071414080054509294803424060396454143c0a04442080c50146411583c110f014424540450002c00c0d030001202e0255841441c8444094003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 960355548 1250 960354298 960354331
    0x807021b010c020d0c050901060c03110a0c050105130e0c040501091e05062811100501140103020f0f030103031812240b03120c0f0304050a0e1b12041a 66
    0x3003005404c200304044408100c0c8000029441d00c07501d04507402480640c503205501c101700e08002e09513000b00c605060b501e802869031074000030303018080034040d205c1c01e103411503c4200b031415000c11301859422011025040408201314581e0f814000c1c000d565003030741ca8030450f030f90b21070660b16242c82442c9071a2104403904414006d40c14518003611106424102d00c212900214480130050142003400c0c2c00041d035101c091806000c400c1220200340c07003025030304010540c50140001d10701094022407504150b00018000d00c10442002603908207150342940e10341da07503501d00d406000290703034004050001c1c9204400042a0010703084141c2e060781c22081c080c1705011852802060000200415200143c0d110511140c07030f141003209020702c400c001055661800ca42030131a280104510510050703500401c8144155140e0072041c108071500581d07a044d10343c5451480c0d0601c03103000c4421040a00c4041b81181d02d65440c10b0032a40594000d000602c01c01c01c1e200241e00070601300b11540f1144100041 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 960356798 1250 960355548 960355553
    0x8070e0903041712220b07051b0103091a04050708070f120c08030a030b03010506120a06020a1110050103030311071a09030f0705070503100e0601140303190807021b010c 74
    0x183d0075402656100152240b4004144600140e03410061151404214848130084600044d00d03c10b0040d00d4941322441c10410103036035899940102d8500441c40591182426601d82d01a42020781510f5001003250041d07a000a4035003d2110100d60a583e00d102d6203000041401c408511030045d140e940d030b44120ba41c0d0911a0307030503242590b0002124070790362500d40040c81c02001c0c006001006895607001c1a20200a010503080d250003030030081c03003403100000d14450140300181b181c141c103038082d13005a00d030402100d0a580e840c5c503c06882c1b030207004002040041c0b401a0788014181c900c282c6003044603104004951109001e1a58020040c00320011440800300f465544e8036403241c4601c04603842c0564100e44c1c7c0c41c10f50811017007150542c1c002d000501952034140408a03040050000802400408401503980c404061140400440e01d0040920030703510180200d403105181403a84440380c0341d0f1204024840b00040700c0b01c800501891f12144003441c10b4035585c01128005a540300480e0344540c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 960358048 1250 960356798 960356819
    0xd03060524070b1503010b041a1302090a2601110307120b06210a020906071211030a0f0f0207030305041401020703062a090302061801210608070e090304 67
    0x900900701d064400d101141c0011050f8003030340c0c443d01c0c0da0700c4581e10121a18003458207495400300a036211301c0c18080498508a104594407901d40c004a4050103a00765900c5104000d03c1120074803034100c0e8090201240345400081441c01002c00240004020384c0400d801508941c1c03040703403602c62840d040002c00e1009104003407809554003030180005a0380000000079007240d0000c0c1090b00d0b000104841d814803108540c7c0c08a030710400b100400d6140421140c00608a88520314004003078400c2411a12a158810180628402e8205c01100e81d100d0b04094050218a251035030700c2c00080100b88000b03c42407001c281c0504603581500c410341810704095400c000600d60a00040c114070403548008003040b018028100c2c0880001c1000450500307040b906200320340a8084103003401002c0c401000140c0343c0004403101150724400c040b00d92081000102d6074164003400c10540f41440812441c22280d0980c0302e002240c1d803d81c115001c80e0350711004001002005c940440a5030001e03c130803c00a400e2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 960359298 1250 960358048 960358099
    0x8280f1403160b06031006080d03111c02030a060503011a010f1404030c0312080412140d15080706030e0604020906060903100f0c110613030e1002030c0d030605 70
    0x403141039034141110a40c03602c041180c410b40c2654a000004103020883c14188045000d101c115001440b009040842c515602c010002098082580d40c1d54191480c0c018502030320303031f000340e80825803020840d058140d0000e500191a1080c50750b00c1d1072000222454140710768166484103001c143d040081410040d03580d42d0120907000d0070700405450721700e480341c103101c01071000e18420481c4800f00d90850a103030248202d120301c03401c00e10031100d041c0310100750b1040d100250784400d407902c440102211840c41046000d00d4607201d0342c45041074a80343e000c15280c0800f605880400040b1610a07540b80400c40a4464241303401c401c0d03800800108001d400c00d0103000d984410040c20045c0340098030000710340341c03486401e50000219568240b50003600100e0054548180051400d045041c2d20041c206032101c0001e03020f202440019204541054059074400802000061050794140c00001c006900c0c2d070301803030320481c0d00e000c4c1807130f6088902d0080c4101e90030744202600e903880310a0000c080b00d015100 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 960360548 1250 960359298 960359333
    0x109050c2d03120703120615020718060b04090f05060913060b030102122a190305150a060e3f01020f0304120210050c16060207080408280f 61
    0x1107001c41074000924200400c440c91199907010441c0e8442c181b01800ca0780c003130300b20308602d05040b04501c10039a800503c590a8a0b80306c088140c1c0400019091801012203a024007015040800c0c0006d105a0713647c030107100c5c402d00309030502c51562240d00700451110125080c60a404500410780302040751070344404904500640011300c0d0440384412100c410348101d03000b0f031281101084811040d1340c4003040b00c001c00017214005041582040011120306400d015000802d40c0d1080000c8020b00e44803400303900c000018100f07001c11910740c1c00051142d92a600458000c6007803000c9004001e20004010341c6045000c00c00361580c151120602601034245000d4104941d0240f010390082550a4001c5000d144210b60300325141030310045c040d0030480f01e0b25800b40c0091a08080000c0200344d00c084801c0900c44c0c0c000c03120610110300c2c00384001e0180b400040c01c0c020002c50701007a620400604c4802407480c28440409507250034210fa40051240c000041901812034860b80002d0001481149800c8 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 960361798 1250 960360548 960360553
    0xa0507050111030c07170703020c060d090c17071a040b031023090a020306100e270a0612080d0c0e120106180c0914010c05030a020109050c2d03 63
    0x305000100c0e081561030131201180040c0410030400403013422403032000f0b500352650600c07040e51406500c424035010220700074940064000401110f55124800c616844030029060a8545c020680203038059a00303079200d8810603501003040f030300440307801c05490704e14820540740906201c00303903405400c040e0000019020b0780002241131902500c0020f41110380c2c80c0c2c09121440a00c0400080c42c0000d01003141d80e03031040040c4561034440107000c0c4201121400c0514452200d0340c0802d84521261160380e0750342c20700e142810340c80748600650034020382e0442c0d01402403c0d00d50644042400024200500303000d801c0002c51000256900b100307070615214100a0402855000841c103400b403802c040c0f080c2c0d65500d01051041039400c020316400c0103a583d40410041100001c060820b07400c80c007840380703441c0352032a4103034a9070720402c1031402807580041580e0300d5014106010340a03001030cc004407410702507030501603010704101100c4513100c011581c4015040c0103411b40040c196041c01c101c1c60f010b0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 960363048 1250 960361798 960361811
    0xf01080a0b310303021206090408090d03020712030c11030304050d03110a1e06050a020903030414061b0a14011e021602060f090405060a0302030604140109240c020609030a05070501 79
    0x42d452145951000b500070385000d1390f20003010700b0508184600a042e0f0b031049404d0f0b0107000100d00f8840681d1404101615201441c05050409903d071200a40c05078001d075115041050816910844804c0050720803190070030002825010117450b8011030255076045800c3c1081d00c80424030540005022070035032000d86506d0000d90700d4120001c0040e0440c90094595840180c080040902c40d0700e03400f0900042c114206034820000030b80302d204a20400d460034800381d401c404680e03911012a00794080d410b203c4404032071007180190329014510400c0c0c940383d0320003d100e12104418001d00100c43e81c5001404841c46041c11103400a40024601d01c00e11800d02c0c100c080162185001860300103a46800305490f481c26100700b20558030010012801540035003000c00042c0c600080164005600c4803a51744c0c04984480114010b103c20807000e4550082203645c02c803c00403480380442940c3c118102440102c0d00b81005030f81d505c500340c6400701950310030020504140d22401c003401002d4412400859078 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 960364298 1250 960363048 960363121
    0xc07051804120e10030e06090c03100222030f02100e09161106070e0f0d021f11010501030305040510020c030a08090103021b03090301061508010e28050f01080a0b 71
    0x4500010840008031b60340c0c621102c401ca10421105500104040c01000a10381c491b012984400d0b400e08120b8003c1e8010400e422850442008040d5004d40000f4080c1215501e080442e1500b002900c01e034099030b50381041101c5240316503007040210101070f00c5400c1e181c0300c0305008500105100c2c070301c00402a42c2c803000c030700d0070f0300070b0240b82d0044441e513403404220b40d81d280412141440600031103110b41d00d1a00c1100058482030000346000c4041c80718015024a41101914641000c1002c42895464403001004140c0c00034042c00c103039041550040c07105c4059000c280e07614201d403070715903130700d644002183c0001030004001064190300615015003001240056215a002c411503241501d800115001314107040074420300d401031203000320720040e10141c0d00000c0c1c0802c2d010301605420600303000004000e12940001c5030b00340c480300242140d0f0090019803010060005542800030711441c0000010f40e4100000c520b14000e400140c00e840c44c0c2c43d82031a2140b007a840320251075940b100c01d09400113 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 960365548 1250 960364298 960364309
    0xf040c0305030d0e0f2407091511010f021810050c030a02010e0c011809020d060f0b090120030a0309020d2a0902042301090b0f0c07051804120e 63
    0x28a0300100302c041090002c80c40c0c840c0c10110180c80c00d11340c41c6d00914440301b0005200c140024034804c008152041501e0320141105c036485035401c040d220895425075a108281d100031440c0b08080a41c008011039401000f40200364403915070300c00c0342ca5000c100c0300340007807034155112204480581005460a0214400c07541140c01140c1e003140941d6494083d0320b0301010501c0483e22079042440e201c401c15020b0346107900c001c455070003401801ea074003090524504c0241d510100217071540030f8120455236a1014082016801403092034006070b420443c60b0002c103031196000c485040e445002d1420a0004030044008001101060384d0160310180b142010a607010042c243d25400007806100341620a41c5e400701c400510760040002520400080145040206c8990820040303010508199011000100c2d004401504407005605001808000001c1c1c207800409c0c102280c034050742c5285070744604101c03040c0703a0307403120719440091140000e0016081c1c0d41c803410403809a041040203504142c1c080740303 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 960366798 1250 960365548 960365557
    0x11090a0504021813020a14071e170711031006030b0601031113080303011e08070e09011e02040603150e0703021b030c0a02011218061517070f06170f040c030503 70
    0x700c159000503000c0f0402d47c80070098080f1044941c0301c40c0341800d00c1e03655001d0411132040708200134100c41000010402c01501c8050181d503814500383e01d808007400c14160352010004500c0c400d111301c402105c40c0c0311342d0b40034150480c0c3c3c10018510380c80c1c4c0d0f01030042d4040c1a04890f9042c1c410000c005008100c075002400001404a000c019902d0350304040700c0c4052202401074903140c0000c81581008081c00c009140816038501c480304c1121901e031001c0c0907002d80440c5200b0b15020f282011229807502d00c6a0141040741e0450b9410f210000c1d04849802d1140c6c118015a44001d50b0358001640c0c6e00e0080d0001c15680545800d071900c004482108030303046822400241e600703500040403980c250b6900061130b2224a803c884200b140b80b185a40ca84000c16916400409031520703400345e154188032400c4900300414a980c0000d001620040301d103901c4001340d0140c5554484203400200d98544900010b00d0030000c96a5840e080303440d511501200030400030002c8924103480781020000074003d0000e070 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 960368048 1250 960366798 960366829
    0x2040b0f040305011103010e0a09150504030c1104060308180a05060a09060320120411030d0810080c06160204020d110c01052404050a0b0a0b0a0311090a05040218 71
    0x154480d4150f2819a003520780c45081a1881d4400b440188205825500381d25008643c0200c0001c081038146010b082c1c02d048000114071452402c0c0030481450b03000110503100500c60740100b40020f940740c0802c0220380ca10300000d4404034040c4041c02c225282d4581a03010304900814400d242c40e900d1000030040c0d44000c0c544c1d00000c200000c208200390f0540520720018803241d10003c114840b44400c034170180203054480390b070400100e0105060101c24080c095281d4006415900022103500019001150644108000c20401d042c0000c0c03400740480c0d036512041d001442c96151a000b14a040f019071810f20b03080c0d030f100740c1c20482da4070302c00080c1c49107118034001204226110280c2126250845030300411041a080155804103030201d00d29240705604001164005150f407144131111004022045400d43c000e0203848002c904502804050201744005580c1840b14041f14962906180249002203420000186081c081482e09070003401152000300200300c0500c0f84040040da0701d101ca114072 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 960369298 1250 960368048 960368077
    0x406081b030717150d030513050907050c06090712020d0c0b03130203010b030f0316060905010908030613110f1b0601030c150c17160f12030b010e031b030102040b 71
    0x260f0105100c4541c800f580404540d80c8400207500c2c4c00040340c0304551070700c0010208180080e18654aa15240b948400b500c4050150744c0e003880c0042028000341e00040c1e1a1001e0310512001410f00c110001d801d0051303a1881c003010510541e2503090000680400c0c40445420058141c045109044000a10300c604c02c484401141c0c01190300506086034100c24801d40660486c415500003204000110b4403012258001401020b10030300308000140901034008080c0d50800c00410240b080c194061405130300e0454905034001d40c0d04e0045800c5130108100f0007807050040c0450b86d55460035401414041c0b810340074201c41910f03c03599840c14071074240c00c00c5900400a0206200d44ad40fa8107894041d08540c1c00c2401002c0c0382611650902d1101e1003402c0c00c0d03248002074440c9041500c5111165072a48034011b0981901e4619080045014030030400c030003c0d00d000d880c200c0303542c4110120007004102a001c0c0083e20b40401c034003071010307020703014940c0c140d0340030880020745001d00c400402a48010450 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 960370548 1250 960369298 960369317
    0x31b0f0f0f0f13150c030e1203070204020301080c0a050a0609060503070e101206300309030506070c02090604050f0f0a061d190c090b03071209050a0c060809030406081b0307 76
    0x10541100c1c0d508801c440c040101245007980002d4101f1225800c8034402c0f190f00c0d501c05405030000b8558480e018009411a0002c000091070300c1c000a81140d800b04110340c0002456110070034040742c0e200c0c0788115030010310b41c0c0c1010080d00d40194002c6401c1000c0d8503106206141c8131001c5004184c0c0c50f0741400024030314a070140c030502c00502c200e00c00741103c43c1202900c0c007007400c100804122810114019024070340001820940180081c10046501c00207541c9589045075000e401d0303032420720b81680200c0c0ca48001400324a030032b10405118424126440c1e05980351b1085881040d88000d151591042d9500e0000c600382208030301501d014920103503001201d00e481c0b6883d004400d940681c6034020380c10210350035155a00549820160f0b0005e805158a036074903280100c07100200c200d0020099850f0038070304418000085034010348640540300031407c40c0d41d61101164800710844802089801c14007007404580d20444a5a800a0034403801d41090311501c4496511503109440c0b05000c203030840d0 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 960371798 1250 960370548 960370559
    0xe06090a03050307030806043b0f071502190b04140111070203011d0c3106060206361507020d08011e030b090a17031b0f0f0f0f13 57
    0x114540c4d10540560382480027290f019860301c0140c044240505c141403940800110044200c0600c0c200c2c8080c00c070442d803151680034026520384003140035404200c03440705440e4100303600005040c80c2c80c2c560143c6803013010700641c55188100d80d0140040300c11011191003100c007002c0074003c0d085011a003151080da1110a48101402c442400052402c01300070a210b030200c1c40e5011419050100080c1d80340c2c0ba03c4403422401c5224001e03140d281556070061300b844201040341030b03840070b400d5400c203800710361355611510b400644142520784011410060399140e00c2215001c52854014403c0c850222440c03904084c0340d003103910004441003801603101740058210b05901402d070710b00418880c00700300e5a07030040c526840c10390724850101400e088400008124690301c02c000d003011403504011328100d9220620496029580140c2d20101c0e868410400d1042040d180e0382101c81c010086081c3e0703807402c04c0c00070812402e500020b1080034164424003d00144008180c000c00e525007100c0f20900c9201c1c24039 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 960373048 1250 960371798 960371807
    0x901110d0f0e031b1012090f15021e0a0c06091a0f01120308071b140105090c010207030b060a03020d1104141909080903031c200a0e06090a0305030703 66
    0x1507001d41c4a80d1065149144c1c02c4000f1001a0b010001541c0d40840035002c05000d0b500500c4200c14404024544030140d41808082078028400500c1392060b02d8103019094600702c103074000e400d204c4400c95422041c604060084400900820310702d07081c403e000300c00c2c5859100880d296403606071400011050950f5491039540c070704982c40f0400fa1504443c65050003100c5c1d40201c203940700182406414404176480398010619207080074805a0036000e40c241e203241640500d400550032480703942c240310125013800804240300c0d0388800180d000348100c52440c1c0359010802d40150180d60401818003005c40581c84003814100464011509411140d424000b03100c00c0b0ba003294135091404000005010505080b80010503d01c004544041009603050a201751544568910710b54903220005042941704204952851f04403840d840802808000f610480e28a180112540004503c1042141d014a018920311550b40340081c1529040204660104030054404d1308291119403011618104045e4130 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 960374298 1250 960373048 960373067
    0x1506030f033004050a17040e0403020a0606060905030a06230c0406080a050408160221012721180b1c0905032b06030c030b0705040b03010b0901110d0f 66
    0x1002d410300745003d031602920350501d00d00081c210008401c05943d000e1840c02610b025000044440d00c0324105498045d5540f00c142104071400e500b0600f0000d160f0340078404810884801070060540310241d980c0342001000f003a624003005a501c1014451405003407500b0030702c200c11000441e41c1d25070070010007418200000300501203840c00d060400000941042c1500c01003081c0c001c0494202c070480c400110380d120140b0705042180c1c0c1000c040d04580c07105400406001300e000c140c0008802d41d1060450803c44581c4000d0300b040030302094068180e115400014210180e45080d0b00b101c00354803100324913580030303074402c50070040d021690003024880b8500100c001e4440500070007119803030f07030740740d54590081c1c4a5604001e4109202441040c020350001440142094070410046403a403078422169800c5003c01d8607054112800110b031a0302450440d401e0315819007459085a01e0190b500880d80d1145a0b1203040084600c800001c1d404100410110000030303071170f0124600c04c0c0280041c021001c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 960375548 1250 960374298 960374377
    0x3070603020c01180c0810180f0311060a06050a0e01210f0804090207060605010e0a0608150d140606011b020d030c0f03020d0809010209060d0b18010303020d02100903021506030f03 79
    0x203007050703551819808e0070711240d54603403000600c001e0380c40608050b6030034500d940e03030f075420360040504100e05e101450b40304d40d0540c0d508070f50024019448548040010b0002d000c1c03684c05441152181d0491020142502c5a061040c0c0c003c034500f280995a002198105078014000c00d50045800c2c02003020302d019100146c40280b800c414900124000642940410300c291800e02c090f250100d282624905050340003040701401d20340240c071140c13030010b02d00104501018594005c0d4400705030151f116242c076400512031000c03600d403000d00f6a0204807a1564094040b8244a4100c010100003094103030001b00701c038040e8000e040001c201c600d000d006040d0013864001903900c10044404107540e40420381740e51002030b00d00080c0d00724100b004074950403000d81125003e0b1b280b4400010806074001182283c45245d0b030b09485112070400381c060141c840000000f009a007042c45502c4038880a03246a69000f0303002021194a095400d500e6410b541c040c001c8a1714207580c0300800c12245181c0101941c2d60f64 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 960376798 1250 960375548 960375551
    0x40f120507090c020c040e010f1d0c0108240310090f0506010509060102030714010902150c0114040b01030206071b09090302120309070b07210e130b03070603020c01180c0810 76
    0x4103c0d10000c0d103c644a0010360322403980c1d0611841205000d6214410000c1d0070b901c1004586a5001c0c86c0c1c1e19055062500343c03442c4519074440196500c20b895480c0180240742d0400345840362311f03c101100c80f44610701990148030303800b901f1515150a00500e03c955000f81d00ca8246600300341021401d00d1030507042103021344400c1e000e0010f030f81da000044900d041d0b0001340c4034004100384210746014018a00740a94007102c99018400744000f044000c00160340240700801a4a00b5111b03a8035010340c0448000c0c1c40514014010809402c00d9001002e07005d01c80c01d032000000301c0407150100c00c0c0c0c8280d0040c050b0159115507900400d070301002002c0154401d518440c3c11441c00da45410b50340c0449004245008001007009010018580d156061005040d440d403401d0344020103008103840c0c2e05031000c0d40304941c1c5440034800c0d4241c1d481514520318024024003415070900e4070560203035105165002d8999611039412091329002c144003080c56208a0248486a00d0301204529000107070050200c100d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 960378048 1250 960376798 960376811
    0x9140a050408090f0f06030106030e0f1c0e01030f0e0d09061b030c03050c0d031a041806020307051b1c0206090604320f010e1908030c040f12050709 65
    0x10b0300c0303106480c0c50200031203501d42c81005180200b81c140f032603000120b402400200c001b03d0f000780c15030445400d0b00300b44400c40e9030040d402ca40d000e9944880050501640340d0401c2e04e14041485280c10080d50304060401040050726044c40e842101c8003500800d0321a00b02c451900c880d1984420300e4001040545020702d50b01840c0341403211110b0700c8200040c01d21509024900815000380d09588400c1e0b6800f05407900442000c401801501906200070780c011045085d0088529161049104503011080c030311b060700416640349002984060507507814868203005015503a42d02c250310b00c1425a9001c003a100b60040784010001c00385600031448155000503041114034000020090307030003600034990b81c000c95100d0b00c4c0302c081010b200d8111404603407000d181802065002920410b814001c50003040345a403886001c9031101c3d0465002c24030700100041c2040402c0c0060041c54110014842203441c10342e9a00444404a040751f016402c40f1140e00101001c0c402c09200000c000c0c20811030a01c030f90b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 960379298 1250 960378048 960378053
    0x80f011d0304050f090a09020909060a1107051e010b0a0b130b270d0b092b021e01180302070905060604120b071701060c15020f0a0f020c060409140a0504 67
    0x1d013900c1001e42070160410000089a0382442d412403151789030040d01040f10350a180c0c0f94151a61002c0b80c0180300203062801c030460742d5007000c0480344100e41000280401044d010910301008000005031620396480d880d0244207555641d0215008210340100c096454a00c0c8402e44c90801e4241d0050205c90310900c46002c0d1138460540d0912800000070042c2515040d00c400148060045d07100940350b00c2050b000c1000183d00041c09012807080300c84640f22401000f032154109100840c1c0b8600140c20022109050003402a280ca00b003101c1000003040880d140c6a96041d60009481c06400580c0462400c01c000406031154540100c2c003075a101e40303070a040140703e4124410020004002c02c07a00000114400d100343d0092480d254403e840b012556560300e0000d14400c0c1900c0705540c2d014120241c81420400b5100b200c0e050302d038055004e07081c44a005010380d1481410400e440c00c1d80165800400390381c0c1d682c4003d0014005812000810070660701158141c21070003003914803c113281c070060002 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 960380548 1250 960379298 960379309
    0x8161415090909070f030f060f0b3a03020c01080a1a0913050604150c111c110102040e07111603320c012709020f04080f011d030405 58
    0x44150060b140d0440755121038001514002465100c40314201d501000881040060441007100340c0c010481440103208005015003242c88450015a001845018181543c0010117035240070300300c00d0a21241034103020100226a02996400310016081514403103c0340d1303040110581c10071030003e010015410030b50500110340c49408400e9100301d8083d4001800f61a0f0b42400c984040d41c4031040d20040d0406107828241000d940d80400b1010781010440e01b00702e8469102400c0c0c55000c80d005180021800c030754180f5000b02008003030104440400c00c1d00703840303074240000e00091541c000c01c4219481c01c070b0742c0103081c140c1580c00541c564028400c4001c007046049060815079030403e14001114005103040c05491082801c0e0000d00b50041c60b030188090170118401d03a0306a001c0e241c1d010030601803c0c8181c0200152084582d80700e01003101442184d2140c1c0c0600714071144103c0980c5032980700c000b600c3c80e00412001603180c507074503110002141ea0300d081610130500c1100004605180c1060300142 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 960381798 1250 960380548 960380557
    0x15060206241f11070902070506011202010507050303151f1d010e04060906030b06030f06010e072303180601180b03070f030818010207060c06021308161415 68
    0x40c0000c0120032161250b0ba00d01c0c01030160004030340c00b00c00c0c0d0103000d0030700030707000d29802403c001081c0500180054081250700850300010f9005000e07010f03581c03c1c446080340c105150300080e8100101441084005602040190b01542101c01d052060440790707410400d401c044200303422070820020344161244c0381c00848445580c0c1100d5a0040b1041015004a41540c001c001c100d42c800c0c24480d0005c0c0780d401070303031010b82940d000d01c01074503082d0345040505507071309144d00941032540c0c0300e1401003085440b03403620386401c00491b151800582424091502030442803044445545400000713000000e40c0c0180d10540e8041040042c1281c1c0d0315005000c2c1c0a03c2460b40760f071041c2c580710a105030700da5074144120000f4251034020300c9401070b281d04101d507240d005071000c030202803003c1145030095070002444000b2140d0541d500951001d003541e03060042d400070184000c1c1c42155000218070300006100040d8244101c40c030aa0445180144000d680040b2890300c0d4056801c071580609100c0c2880b04a4 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 960383048 1250 960381798 960381841
    0xa1205010c0c02010806040504020d1203150801020f04060518030105100e0604050115050c1614100504030507090f14070203031603060f0501140f07060b0f0301050f041104020903030c0115060206 85
    0x150527070b9140041026621101401031043c0b081c0d100c1007800f82e030181e10440b6421101041980c4e02c0c2e46800c1050300b02d20561150115500c414032017040040d2107440103201e011540c0345161441c803120400b003400e40320b05444100710400041d40c00e0003042e045a0704a5070014040381c06200c5940341c5503603a403612a81c0854403003001000590b100084004100100244920b004110b40b90750340d030340c200c00341c00045d801030300d10072111041d100745e103d07101d14290f80580b90000003a00c200c601d8100e60b80000c0001c0701c4034108041d291040c00300c021210212491050030180c01031a5a031030310100c3c0700200d1110311002c502713251400c0824001744040c012004103464003030801c4092001942c0710080700d4025180506030780c0d4070000c0d20804200680d007200810000580c1c030340003005007100800d4240c0e8800c803840310a40f89180f00160208400c4a403005000c00701810052a21060340042411503100c0038066005039154002d00340c2c1d1105070005c03d4000d000f5440540018104030003801d0800c900050314 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 960384298 1250 960383048 960383051
    0xe09060d0b06060921060106020c1f0804170304030314011e0e0603030c1c02060f06130c1103040605090f0d0b040b0411130f060608011a031003020a1205010c0c0201080604 75
    0xc1c0c42d205e4403402c004a5807201002140c0c01d00744821404565554802d001d24401801240312a00c03c500301a0a0f194004403c020358440c02d0190040c200e60286005000343c0310001c0200e0805a00c1c04c0a10007980074034080c3e9001710b16040c0c00c1000080514043c0c0c003044601d003818440003090076051003054103889140c0115000c03500d8950000703141d4040d82107450658002e00c181d04903d40f4400004d0314515950340c080c0c991a41c0d442c00d0030104040d08460064010703032000507489000b503071a808001440b005041c4400900d4401c0b1b0000d2a542058101320085640016803c210389091034a061400f00e044421100c501d40361b82d43e802c41c20074090f00080c014040c1e1000301c2c00300898003100c07010401c400b40442c0800000311400b040609049808003240c185070400100d0204e10406081d41603d1001801405941040c0c40d143c903640d000911904000490140201c01039540208050040860610300e00f0700c0e2907941081400c42d0303540000001801103200c0001c0050341c01501c00d80d4010402c0b00d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 960385548 1250 960384298 960384307
    0x3060609290f030108030711011e0806040603080406020f0c030607140f041a0d0e07150c06060803032a13170a150204090b0603190213090c0e09060d0b0606 68
    0x3466008a00540040c030b00d0100020030050b00010103080300500071801060b9400c014070040d0790880f0312004a401c0304038221f14412150740107002458024001500c0081e00507925141d4000e503800c2604414010303040758420f058000d04c1048419240001100540618249480081e02181502d4007544540d01d0110b61207410310b8100064500409851070020341007810601700481d2a48606200300e43e181c0f90250000900c8030004da81c01c180c5602c500010741000501400762220280304808450244d100c0c00e010421160038000345003d030b500c2080d00c0300d0f0354010001c44160301c0650018032402c0003041c01a003881c00000800c1108559054840b80102c102c030b4004142406041d05000e89000c51202d51000780e800e956000b4811284000c0c010410a280c0c0000c0101c50b11054500e6058210003588898032000349030300078090040819094880c1c182e4812480c1c06039540b1102003404a607026060000908114100d00d41c000e80484640c48285180d0b596000d052402a2141e03024070000324 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 960386798 1250 960385548 960385619
    0x801060f0509040f0b0c0a120c0c08031801060b21190c0507050a110406060201181e0209101404050c0a11010f0e010e0f0109081b030f03041203060609 66
    0x3680011103900100390660720f01d440c0b241101141c0c0708424242c00a4041234401d1850180d52190b13011400203540c8070b10b1500031740c4c2c0350300b4495003000e02a18420049208280306100092040c1c2000303102581c1619181d44010500300d80c3c00d503105610240c040b0580741045510000310840b442400c144120018140780040d0f8120340c640511038004245209452204082c060800e502c0440700e48100c805000180c2c440c03100324240c881803e0520b21320010341e044000041e03c04150880c0d02225601a14820007003500019444801660303015a02013a650041c00805020300c802c2c1d180c1002a0350030b100c5800c00180300c2c902481031681940402000c80d098042c061400c1d080040d10041107601800301d000e0a1990314000c0054980000052060901c2c0c03000025041c000c100219801100c41410502c60100722403101505034240400c138042080b030186800d06d044041c2d03000781d02480044944d0110b00c40f01600300d40c40d40d08443c00340001c543d010042101284000705045216404019980d071030710 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 960388048 1250 960386798 960386813
    0x6040b10081602121b07080d0c031103090409030f02010e2e0b04020307020c040501080d08011e12030309120806030d050a1130092103310801060f050904 67
    0x800644400c68000a0808000030441360941e14000c83e1070940310b12079071fa484615501e400d82c21030000860344460a00c2e0109001d84490796902e40300310f003a02c0c40c241c0c4100000c1e04544801c03208034081520030354200700c4c06074240714540380180044005c0020b002c0b00040403c0c000911540806800d81802d01e01500349a280c0103182600701c040c00c00c0d500d90412203c0a5210488148214001da02e807600002e42c80100181c480170042c4640c03580d080507400e03d0600d600300e1000c0c1c00c140d56440b4030350030000307080c40a0420800b40f00340a41e600040c54011403030710060601920107100e040100182c24050917903404074441c40d004040303041144e03984400c14801c0e18002c81c41c807001c117214040d92000348191285074114032080e000f100441d00700500c003416191224010341008c9034204021389000d441d400000050604032441a41c02c69041c807145201443d02110744072141007240c2045800080610ba030f601041000d4507900c4002d101d001d080004a02400040e4414540f02c0e90419004c40d080c40a0f8 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 960389298 1250 960388048 960388063
    0x5060d05011401091406090402060702061309090b090607020d0320030f010303030608060c0403023106080c0f010512041a010b03070206060a21080d0e0606040b10081602 74
    0xa020050a401000c0d19050091260060136820840c03090120403500d17072080c0c4183c2c2d004000d001d160302e8a40074090207800c00c03403080740c202208222502c00121001501c00090a00e0300b004940201c0c98680500c0e4120084d018448650000e418441041e4002c51841ca1401240ca400158074941c1c00b0b074503640d4411008404450413001060060110342e1400c01e5060740d01a8034140501c1760307102a00c40d07075a103040314010f440510a100500c0107282040c0818640c10705854005000500380785a6103007445112090461070340ea8102c20086003606010409500c402104d5240d003201c5580f0001c0c05500c00d00200c1131342401103400040400415507030480f00c2d004075800401066849440c0b040180d44203a40c01400341c46001d0014005282440c07446007629100440750306044400c141c0d2041d050042d040840f4400001d2041400c044414420014064008002000c030790074103106002c1181c01107000d042c090410096030b041e2140c0c019200e50382000c2030007916456032a0081c130482c00d000c1d2 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 960390548 1250 960389298 960389303
    0xe0f150103051611030405041a031501030b0f190e1c05090612040c03050613030212030c0f1b0f0d08011d07050304050102090402031302010e030604050c0d020d0215031e0c040905060d 80
    0x1428252a0f002e0b0301200555002712003c0e4119424207100c070030f1001212409100080c0075800d80c0340001c0045800c0903000386c00082910001d03e000b071000542ea800e071603031216035032165400225061030584c40d0302006003100407075081c07032890b100059010445500ca091004c07540000b907071000c50308105580e038411006681207000d46034a81003450000c400d0b8104440250018406c240100614901507000c482c096805404842c2c640718080d041c00801ba000b081480424103080c88100c05400c100b8040e11800c62203080143c80025032921010301300e004113800003102844000000320040c1c10004030241c0000c0c0300d0501940701c1d6a580b5046000e0b100b0a60301c20341050010040c00a80018000707800c180034400d880302403483c0c3c0f00106066580500729030103030890744400394a81ca5418402554140b0900141c00080301568130b03004154511212020100b81107400000c10800036050044c0c2c5008070701c05c2e1282109400d080c01044514000c9004100b021541c51020072059500d181d1000106039 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 960391798 1250 960390548 960390551
    0x6150d02030303070c0b0c04140d060e0a12020f0a050d141312142d03070c0e0a0605061305101b301b0602040e0f15010305161103040504 60
    0x44c1903413000b00712003800c100c215006403018003c940c0d285801030640c1c2c2548c20940034080a001080108540307441a0041030724030316902c0140018035041489100c199a0003580751b100d00c4000480000d14106d80001215010f8200910351400180c001c5911050011580b030010450545151030344000d1180312105e000483c084000055205008002e01d2002405007102603041ea0034546c05c0c1d9100c443c083e4003408086040c10003001103180c0c1110b1410100d54000440b030502120b99189121032020340c01c615142d4980a04008800c0719074010710000c5d20007650490300340072080040f04e0a412450052601c200f00240101e4240c9201d4100c851074401a0100f11000c0c442c64205007010b00b01c458841c0a0b401c118500031603140034031140d10b0403d02040d41e03950090507400c0d00040041c00d802031017103502580030000090f2885247c0d00c220700850804444d030702c41d420140000140000c0f89800f0074140342c144400c120f0a11b10720412104c0b10348042c00c0081003044807400080c1148904e402480d4410b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 960393048 1250 960391798 960391801
    0xc020309060c10060b090105070605090309061612093015090507210b04170406020714030615060901020a080d06050f0928140c0d1d06150d02030303 65
    0x18000003c032150310302c0c04103c00300f1074240c484080170310b02d1242441c1c441c0800c00c20002c4800040065118651018030181900e08040c15080000c0c00d0382d0080e81504002101c042d42e038000c1c8004641c0c00e21140320f00e41000d41ca000d24200d2001155007122104001c020700320f041c4841012001c04008400310307804041c212403c0c505c90a1880206520b4409690910074503d004c9254a49440c030384054045e040483c02c034944c80d558403202d0080c0000c04c100c0b400d88140c9c030841c1030490141301900c0038080e141c0103480b05c0c4c1d0410017030110030180e000e00d00d84250700080c00c0c058020903100011200c1d00c010b0365015035401c02e800060f842d100c0309540c014405c100024400d9845c2095034444400d65004640441c1038507004020410741480544140c0c04c1841e20152000704420360426012010f01d407020082520155602202481d0070201d81c01d0104c1c600c00200e010110a0f18864605004006440242a440d80110007a501c1200401840720406031001e008806c0c3d580441d21280258001e00f2a03130b0380d = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 960394298 1250 960393048 960393067
    0x3091203140a090201270509090102030906070e09060126090f0106060c1a06010c120f0f05030405210d020f1806070f0b0a0908070f1b030302030d0c02030906 69
    0x61680040d001c0854a0520204404030554000c0c8190f40340c0596910344100c41c22680303c1250880c00068400c9403440110016454a070440300034420002c0c04001a1a440c1141d060317820130034020a1038082080d9070740c41704000d40d12000d030385070002c1e02860450122494180d280702240c040d151a01c10540f01d08040044400001441d80da1800d2040e0003031100d107589100941e02d800f02a00014062004549080b5100d0680284164072600c1454107800303e41c42a100d41d17a180d280c0c1c1000c00e001403c1115004c840d0754104040c1580c618061504a1451406446947d2074910600006242801185521010311103500c1030700c4d90310110b02021543c8002c034881d0440294411603944a045160220409403441c04400340c60680740c01c108041016503260b55010085c407070041075000c0081d43c8030082c401061800010300483e0344a440c0400490210f0b05003040690f0b040000307683d404081860a0000940c003005494058a00d6000850911060b6000b40c2c00c500505400540081001c0f40c01800c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 960395548 1250 960394298 960394301
    0x70f0f083004182c100203070c0c0f1e0b1e1b0606090108120a050a02031309050403030509032b0f0c0f091d04080c07092408010b011e03091203 63
    0x28003004e60848480002400002150184410008000c5a401c0100d07000360300d81960700259842032141ca02420f0100c030594031100d0301e40d07441d000400c0c0040c3c00c0005110034000c1e2510840e400c44025180c5294515121080704030703209801070030300c84002000e8001c00c06102c010940b8050700034000461146030000c029260355610499402d403061120703070f0000804003004920001d4070401c505d05e251610301c0080c000e1f949075200f8000441180f0003042140b40c1007404c5200800034041030030010030103062a04000b8191000a480361106420402988108034441c0700c001ca0384030104000004400c1801d03030007800415100101d055501d00f0660304070303c6542d201c58404010700960700e44681d0b9946070810815014006c03189207840f00040000300c0c0200d0140c501401140d802d44040b158a40e4403801400d003600c0c41ca0748140b400104541e1114240300c5c640300c50901405881c0001c11000102e80700013444052015211610414440b58464802d4440d820422086400020803004e03070403507100040 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 960396798 1250 960395548 960395561
    0xf0d0b040b04110726040303180801110d050a0c0e0f12010203160f0206010f0515130902190305060d0f020303160f02040f05100e0c0408070f0f08300418 67
    0x31084110300000088181405c5102e40e11140a0203000d4102811940c040d50003080c11141c400079003c08500001e80782d1000d000e10206002e508969030b884100b203092541c1a508003610314003a040c00c004035111340701c1d031000400250035005c568000b100d0180c180841c0c00c04800007d140b0065000000b041080074006807441c12010007941c400100f0000702e031040380c07a88030a0041e950940b004000412072031400c805180c1030305500ad0451440e014100800c0040b141c09544501003036600485d242c6035014038071100d60220845410184090710786170000031040045540001c0c20071030203035894820b6480c10000d8501b450320f241d40d03804031131100e414403d0900211381400c91280307007441e61518440b1614000c041c02014a400c400317101e58100003040d0403042c801801c5072000101800000341d00380003041104020309188940b0040d0303034100541f1321041007440d00300f000d9a6004515003a9114400d507050040d038103006824800c28622414a01c007d849103a0011187c8613078940308641c00300080d030209 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 960398048 1250 960396798 960396803
    0x12181a0907050109080307080d020c102a0206180109080a05040e0a02041508040501181401050903090607060c0e2d041e05090a0b0705030a110f0d0b040b041107 70
    0x1140c1d4950303150011030701c1c00c0d0b1900840c21103400500c01c1000203500c05002d4083e12103420710240c24084624441783c5800748000c4000c43d901d40380c4a100d07810100036626042800c520342c1d420603100500da81c000c0c2d0780c1c14010342500f140c0b00442e103030104920005e502902c01180d2000240f56908001d5000401c6034200380166045009000301189a000e030070310841d011038440d040b140c00340e1100094103448498006000b600c1c15501c46060700d03107100b4480c6650600521924034508019a560038290841c3e4000300851507990040000f1603079642e070602542c450540c88800850590301500080725a205820203042d08442054441c1c041e40d41d0710301d510b002c0c002204003030881c1c3d40080c50030001030780e1000d801a103100710000000d40b03242e40fa5400c22a480b008040490359200320698803140e071803104a4142000540200c18040c01c0c42443c000e2000c803016004c984c600301844000484818030840d020002d456550f1004620b258036a80c20020301c0e0900100208504019006d00c1e03450baa201d05d008 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 960399298 1250 960398048 960398053
    0x8040f030b010f080c011d040f020415031802090c070f170a0e0414011a0418020c0f01050714210405010b0f0402040b120c12160e1012181a09 62
    0x8a500c2d403000170141e40001059450313900c011042882400c41c1d4451014868200d625501e0088a00503d40001e10040c03900b0f02e016001e82c244e4440050444054014000001d00f1640019025a4560440726007007903881010540e2031702e05c0c0c07a1100c00003d440e00001d02030080400001c010300c1d03101303003e0311701c9005070340f94219220340c8001000b046454160601c4050040e401c01800400301c05056804030001c440c1101c2c1c41c16488201040820080e0940c0e8064141c00244281d040303541413160038134101201d0001d20003803c103110050240901948000a000c0d0f001c14810410000055424181620301a200e521401c041c10a1780c00f90500e00c0c0401c2c0181054001074403542024400c907800c0b6064075601c0d900f0002409030300d01840e10f01401d0018078440c1800031841c0700d480184800e01801d4850951851070107007a00c054664800403030654880c0c0400e004094100d900315203612201e407040b0304002821000d494410420b002c050901030007018030f220f00034004c400710302d5210340906041d40c00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 960400548 1250 960399298 960399329
    0xb030303062b0f0b0a02120703180618020f0a06050706020702010507023c010801140114031008010f180308072f060f060a0b0c01060b0705100e06060f0d08040f030b01 73
    0x20172801d070322036801c588142040000001c1d000300d2003640040d07804080080d2414030000581c9510090300c591001c00c8801150078010301d011481c0c1641c0415641c034007034480042d103520f842d902410b00e00031a04003801b80798001650004582c441c208507290140d0080150040e20800c490060007800500120390400314410405800c82602c00c02400a07940140d6500090303078241020b4106041840c5040c41c14401c5800b08000c804038440c0186124410001055201d58030b80483c15003036460b8450310002c01d9140c150542041e41100c403880309480d81500b042030b03040e2501501150749545920700004108005054200305280c040104000424410308a8155480e1125494500c40c400d644459111403242d004100070800d400180402c4048407000140507552154078408503070100004441036008007090513113801c1365100b9080342c0200300005140c28501000481e0607080c002c4591481040903521010400911508480c060000c450341503030030907942c0c40d004100303079401c0c003800018144000 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 960401798 1250 960400548 960400561
    0x3040302060a0e2104030816050d0c030507030806030f010e010207050120040512070e0a0e0607081b070203010902150c071a04031211010c021b040b030303062b0f0b 72
    0x2485601152041c0580340072040800c880402081000d07600c0700281040c40000046847c920162007400110070030200150628600941420050a404418420b05100c40c1c0b011035800003e860041d0f40c9030030200c141e0f840c2c0f0340020349085954aca841c4665030904054482d144010b401414041e44170b28003d0080701d002c2c502603840389591070507990007840180420417662401a0402c000031501409603014aa00c603020041100fa003202d4450003903071280c00003003c04804100c2c0940c404290314141b002410706011415070015425541e0091003c0482d84d50203656080d07019400e600d82c0181405c012a40894032140e282d008120b5520345030040e600c000482d1016107900038035100b05148458038181c1949e0b96000ea0300074016000080080301141c1d0713400ca000c00d100c0d0710340f210b01e240c0060541b4400014004034804085101900540c10900c0016298500009803900176000711f075030fa401ea41405295400558032141b41d000300c210340181d500248808100072642850007907801255590340d28 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 960403048 1250 960401798 960401801
    0x3040201110610091a1003020a050403050a081308011503060209040b0a0905061f02060f04060905030a021608030f1b010908041418040b0402300f0d0c080301062f0303040302060a 78
    0x2164003d8001945100c12540305100c0d500400009480d414012f0a0070784079141d181c0b4000140c8001c9030385030700008150400301c5000300098020105100203010700200b0301101d141095a91000810064000c2840c0b0f039582d589410072000103030090400100950f0ba82d00b6070002d00030036582c66008400c8800c810025a04100d884244500c458004000c10340310303406840070104006000381c541580e542e030b540001034024001031201400540c01015820b060b810940d20300c0c05031354062800c6610400c5103d1140e50b0340c00950b100344000307090003d182e00c0302c1032486004d400184002005040c001030081400c20f00c006500c685040c06880b2039401c00100d81c05025a140b040c1c502400d19450300000500502c0c00760a200c04210034170301c0c0b00e08000c404004445030120440c5168826420000c405030f02907804003c11903e9800c03510300010404283e031900d10540c407040c003c60b13040264600a0308094480c44502d0360464a1511003211580c3c0706c0601907890750415a801c80041c094100851051102ca = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 960404298 1250 960403048 960403091
    0x1704171602040c0903052a0a06020303190b030c011107050a0b04030b0708070c110d0b0a2403080a1808030a050901080f0411060a030b030f0c1003050712020304020111061009 76
    0x1b0001e040c1052561041980f401c1c044000003400300c2070364030380466601d4614440d401040e55800454803804d101c1c1c030800c100009105400c41131890001d0303407801541d0005074403010381404e00f002420013642c5008582080015006290060192240000c264004000074011640070341000c0e0541e840c0c6010488080009464042c0080e855103002c9011078503440c1c5c200307010070000b0994886030303a141e9680030641d0703401c8a1800b5901ea0740e161003c5000c603410624405c0c4c00f0207154a9501c0c5045a9400c1464021041004100300342c410148045c0a01a200800542010800c481e15a400448028074031341c003240d0114006840040401c2c4211030102c5001d028562000142d004441ca040038451941c0100d5014403c0649640c0c6252450f1003d001926641e62a00080c100702c200308028040195400c0d00c40e402010b1a0104001c4000d600c40d420352400306038047d000d0707500c3e19240012a40031019861000c0740740550414080c180e40b0840401d01101c42504050000a004581d402d000250 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 960405548 1250 960404298 960404303
    0x30a0f0c080d11120c101e0c0903050d030c021524100f0f0c0c08010e12030403050306010c0c080303070806040e070e0402061e0d020904051005011704171602040c0903 73
    0x84541e4501c440722404c1e014041c09400f80085810000030251a80e050314524400c03198104c84001c0031305121081c601070f14003030900c28280404418511380d00c040c0c1c3d03001c1e0072a070f00d4101503075186545032091090214401109185061190604000c1c00100c1440359005045584a0041a0001180c1858a15020403038090748030001c00c2e00381040191900c02018500c601000b4030154690001800342241d80003502c410800028268104141c4c0d0740f80c00c407000c640d031101c50f509104010002e540102140d074408030a00c1e01d80550001d074544180c03020469000b01015000200c00c01040030360080500303106501c122001d02004004484241e01c8650a000b9820b80d20140d50001e00941081401000344009801140e02c003551003009428081d0021002e0107851500001d0f02405480c1030301500c2d400c4142c02031000c03e81c3d0710340300c0084d00c078400348c4241100c196013aa001a0074004d1454115400ca800140420f50b1089807480314007403029000e030104e2246140c010b5100c0824803d5415000303503076 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 960406798 1250 960405548 960405553
    0xf1407090b100f030b0a0617010803071e080d05150a0e09101a0402070309150815132705190c0b0c01090203010c08041e03140702030a0f0c080d11 64
    0x100c0c50312088648851000020303040c19150055a0680d480365104040180010303a01c0714800d40c4023a007481ca1220301030b444540a94024064200801c05200d05001c601126606c103000d44040da01c2d11146500415448030003c40c41c18040180400d00141e655030b0b29030781110782c00341c0c8a413107901619550318251060000750744559800907110005502c40007901c4c400e044000d0807030134140d00080036030340441d600b200050104001041050b01a80c5440d1124041c0d0400041034900b001d60780c4200d241c843c0302c00d445603a10032030748920300085038446c5c2038124881c030901040751070102c405c130309006e45424211010700c5590801c250200081c201d00114030f92243d8910a55031910030000141d0f0082c01806c051556503158050041e0b0b02482210b25040454803000e44038a010300700305200011295100d011405080c03100b00000e540504084201c01031040f540b0345171481400481d2600030030380f000420300c011350f54900c01031241c0500518105c4103030f01c04a40d80698065821650390141c04503d12096 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 960408048 1250 960406798 960406819
    0x10e0c040b180106110d03060305120f1b03090312030402030606010e0a0e01030b01090b03030c07050112020d0509010f0c0f09050d2d02010e01030207051902030a0f1407090b 76
    0x386016040014629001040c000e20810540b01200c1115003c0c2d01c010081013541c03104045000d401d00c507410042071342e4201088a140b80da200e407a1070b600e229000340511000000c0300c0d80001c28900654502e00341c0780013920804e2044024050b41d942c802c1001c0c0e4480d00c1154038a0031a04c070302d02300300c0e4031a6601502521071515070200550749040600780300341e801180020041002d000e240446802140106c0741294154580010f100071a110401050b001c0d420800840f00c14100002d030791400c4030400e1030314840140814640350003d0103015880c1c0c90351400c00d01802002d0005420406000900d0101049200c0c0180c0c8161200340c45d00e4580c101007140841c0c01c00042c40e08070303400d4a009004200b1400b840d80b044411a441000610940000d16504014202556400314450109903400c0c20110b2078030f045904d4003543c8081c22680c1d05041c040ca8041c2e442151030034044120980d6011105400f282c00b6481c02d442400600d41a01081703220310b01000401070300502400981d00c20180078090310 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 960409298 1250 960408048 960408073
    0xb100c020f0d0b07080106030c0e01021e0705060c0304030605011d0a050a1b021b030106080c0d0213020a0518090112020d0309032306011a190c0f0602030f0702010e 72
    0x784002184036601c0800350400b90301289041200a200e030b5107a68a080c0298140b86001d0129030301d0325414070400c402a040c4003c0740c0d0b00000d00220070500741d5503191f4080c0241c1d1010b4035141c0190011500b114000c1044c1f41401400000307001602d1062310184403a80e02e58002c0400d050b50710780440c2c1c0140d0761a005c102c40d40b24581c46903421044100001ca050309500a282d5105200d0076032010060b0303c40175040c0f030b4081e1195142d142ca0720048009001e031924100010b55105402900e4a100d40e0460001c80119511000307000200b64030740009641b149881749000e0840e0300050400b8000c20030032803034040d003032402e89003043c165035441d00c544542400540070f21010f5096080b0480601841d03440210102c1d03207400801d203440a04010104840f03002042140c00d045040e481f80c40700040804101d411460000140c482c43c0c00d02070584940700740180f101326052141220007410841400b641d06052001580085128180404400c0e000d40c40b6000c080b4200e803810136841403150480c41c0c1c0100d8 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 960410548 1250 960409298 960409309
    0x50d0207331101061e031a091b0102030c0a06060f06170f1513050610021903050c070e09010f0c020a021005180604080d0215070804080f040b0a11010b100c02 69
    0x780e008400b800000c3c41d41c2c44402c0103105a20002e0072040105034210308008004511008261100000030010001d003042003100742e07249006445682004040d014054450b442003041e200d03503200110071907403940100c0c24001d000382514010f00d0b82000400c07a02040b0680100c1c118008001f034181c4d00301c141c0d40c0340c1e80c142441c074101078103030840301c8010f40450b8100c0da610340403070520010380140020242812820852440c458000c05030a6410a0000004000c0304480019020780c05007416a174a030140b484450074807035a80c00140c1203808080521511200540c40101c120302a070100300312109149a0030303a540d040c4108000c1d03100d03840b41035106609228901814030060902c3d0b10424243c5c105000941c41d4001e40c02c158441d40c0480702c0382a80d15810444d02410800740403558649003080700e0010000c46000304090304400300050400c00c0b02c01910105d9005100040c0c0f402c3d11182c0748040203001a44440f86505291b00700030101100d443c1540f81c1e4044510142c0701d240d00750005900340300 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 960411798 1250 960410548 960410567
    0x220b0d06050a0533010c060e01050601020610030f080a03020909160e011d040c1416020411160303051302040608100f1517030c1e161d090a050d020733 66
    0x14100701c41c1290a00000b87c0d10301484002135081c0f000452107103440c0c1d00092600c1c0c40107050002040c40c214042000c60110018400069040300c1c2d002d9954050070429130191055201087e0131104a4040145042c8907840008045c04242e030780000148040c001107510303008000302400b20302d030a54802c0e040380c6066405410746d0343d101d0525858140707080440803015080308603a0500108a080072004602e0144502002510b1200076142801c2a11411401c2176034818001418907640c0c42c0420150010340c08103e40156008000740301032515450700036150484102c0000e840c03401c041610702002154052801762203144d0740c441c1c0340a807071b01d0340040130030910968020142c0010401c4006400e0107010102d015101503050242c00c0700c0c901e9039035181110164100740c09400504081c00140e01e00c864500301641960070140407500e40c03808040c00c0414100c0001d02d00d12440c00d0388442260080340c10021194005082e03040c0042d004c6401c00700712100b04507440e1580713034a059119100d000d0074100e07 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 960413048 1250 960411798 960411901
    0x31b032a07150507110d030f06170a0803180709020703020c1f23161b0e0a0f0f05011517061807110313150509220b0d06050a05 56
    0x17040240394090550030310119080036400651165442c02007820240600002021208082c90008072421030050301e603803225100078000303100040450b207881d07550310010503003118190940d4006680c5141d004000c2d8001d4070304070301601440e91464000e18186095848501c5560240c00700c4420b001c40c12103110035000b21032058500000c0b004a807041ca103802038502d0f14404c04c07200442d2001d07410700540c00ca08a9100e0010040a01d00234818285c01e10601d80c0c020214174400300d5400503212500c0d01810f0f8044082c103840d0f00c0c007000050540325018105840c184103480d12980c01030310703510290044100701d800a4001c5001e4124080c4c0f81c41c135000990b07003d00d0034038043c000507108660f01170566000e40e81821300400f00400510001e800d0740603502c4104505d09000385046c02c00d0340410130460101095500542c0c04822445054080381c211308a00c0a00906820058056151290003490241c584188151074800058802d08500c2c00e264500072030080f01ca518841d00074448a2101c2e07d00341e00 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 960414298 1250 960413048 960413057
    0x90b01060e03010e06150913211413090b0a081902010203040510090807330216030803040606080a031b05120a110c0105190302031b032a07150507 64
    0x3101320782c00078030145010311040c0c2c0760801162104810051a894060b209410304064442284001140c4914402d030307030140400e0400c00001d13044c2c02600c8050f04481e0070410000002015040c00551980201c01e54402c82400c00c03107092441c0611400321141c0c061504190310951458100c82d800c0110f241d8138901c144112494207032504c0205412143c003560341c00c042000c00c1c206002c0030a0a1202c2e002500c01d101d51070381d0002d030703170703807526000c1861082d0308080b00799002c400441440c400e000f604400424003042e080c80541d00c0c0303006d040d1030b40122410307a1010704d4504c01203100714000ca030300781c000b9070159036011210808041c030382c08410700094210303039500c6041401840c024080b00680180d150341e80f0307003500d0f02d21101321581c00c0007901601c003070411a040100d61000c03261040785d81e040907100c0c503005889640e003e441d081a09110074034982d9034100801084094075091307502d85980e48000c0c480301940040b0420080050041c06001403002200e48510020159141d02c601ea111640c0e160 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 960415548 1250 960414298 960414311
    0x60b18040f06091d010507080f0c0918070525111323091e07260a140d0203030708130303020d051f0b030f0406200a051903090b01060e0301 61
    0xe045416070608184c001d003034000409000300c020300c151a0322810710704001506280c030185403034280038000d10300e210f603a4020507840c0e0151136a082041030108030203401c14550800260140044c0c204801c000c2051000e07810b81c04840700e401c07010840305079014664005404d5100100084100305c00c05403050550344580c40c4584900c22101103c4000500803c0020b504007840c041e828030902c05c506207928484c40f014106146000240d100843d1001c151034030304290025401c0360b03500c1032081d10200c1440b400c0320010a0050942110207841c20000440d0790b512500708060741c50340011902070001c25108030001e01301c0b5140460700b0044522a00c0d0051a10340c240c21640200c07001510b02c6983c1d0001c404c0c143c030f82d01c03050341142d0001e0400c00f501c440c1185000da040c40c080d401c0060004103202d4562958040b520403440350a9820761410303a4168483d0f50701c0c0c5005009401c5150702c1076103255001a41c81141d40a403040070041390300040b10144503802e1000558801035041c1c0b400d40c0540d0782d201c = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 960416798 1250 960415548 960415559
    0x1703040f0b190615170601030603170d050f0709050d0201050c0105130b1003050a060902151c06090b0d170f040e06090a0b0109140105040312050904060b18040f06 71
    0x30310740d129003041c0b084206141c44501c5000100c62140e0803000700c80b80504011281640c110b100844400c080040f07042642d039401c0e004030041d0542e130b800244403481080c03180d4000c05040d8003030101ca083d5a0b404000560398002000c0302e884040c1c80c1d480109000c0c21051250342000402801d83c1030041c1880380c50711071055001d03070841d103040700d0b00c800d100d1b072441400c0e08101c2c0071907040c0e812030418131303005c1d00da40e003192a000d032140c83e62000103019603a541601001c40d00c1d084030b44c5180031030001c100e5440c0c1d0724158505131003420102d00031086616003c004540c0b4200c03441012003455024281d40303030b0f0b030402c3d549507401400d100c0d4041c0c4400009020800071110051b004201030720031b402c4460b07010b00741841445440c0001401c602e510500701b03102036440f42d03444100d5004542010003824804800040180c03540d214a41010f4130b000c0c500d082e140d2109800070000d0048000a032000c1041a5503800c1400c054015502c10b015820b174003152352070751446c2981103108001e4505400188150741e91 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 960418048 1250 960416798 960416813
    0x3070f110a0b0f0415060b090d021503190f180201120b040e0c010e03150c16020d0308090c032a060d0609060e1f1505090d0b011a071703040f 62
    0x885071022021040f000300000c20080c3d00c00c0c0e40207220100300a001580c1081d03c80c6603c0c0c0240c0c82d025000b1403403202c0f01000d41d40d4410803040d0b102942a03440e036890411400e6081051040b0125212407401c1c0b4002d80f00007500340c03082460242070300460303450320612503004580c1c0e011160247c01e0501c0d1904c102450559aa105405440402d040240500756009002400c02e2601c401d05130300c00d070041102415603c0c000f4800903884030b01c0d501d006a684403000000704c242d84800a000c3d41048040c9102000c25401000041c00340403884100c40e01d00f081d1400701903a4810b410309900740c11980780041031100600c029091880c0d0002413440341003400401c07101c070842c2c0d00c07036011801591700d0f450108901440d450149402504800304200c010b082448a52104207030341c4250303948c1b14401000140300d14424400d42c1d60305c210040815068030554204002c1b400c00a0240e8054403154141e44000140581c088600913940404942044030035803141a010750002007050fa02d1400b440503000003d0000f = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 960419298 1250 960418048 960418051
    0x503070509041a1302090906372103020c1917030d0606050304031416060e0105060112020c060a0504050c0303040b040602010c030c0e1005090301090804090b01030203070f110a0b 78
    0x143c0480201c40c1c02c41c0030070014042046804d1400b1a40304000c014595124054402e50207901501c4c0d06a03000369a04d410200d5410090680704c8040402040d140c40d00315140b2401b0032208a01c0000007090071080140c0c0c1b20b0389003103c006025a0060500c01d103e410320185064900540d5500129501d41c0ca241044076150605288502da03000020000070342005403103520060030325407822509600e003d0350050409c1010040700059100c02180d51074000c4915501044c40c5940020300380401ca00c1401103a0103420207440c118041440c0344e58449001810340300762191010010002c00240d29901d009200a03c0089c0061312240607100502e00f258a040008000034081106441d540308d09e4000000d0031110700b00c06c2401010b042180494205a01100f4030081c0300044489003c114042241602c00e0311034a00155090350170603c28109101d030003400340044501c80344040c01201c5200b0011012884200c40800202d08554400032000340702d40111880324a1407411120395030b2040c0c40fa000c80d0f200 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 960420548 1250 960419298 960419321
    0x50c030a1211070f0b01060806090a0e0102160f020406090b0a0311060f0c030406020606031501031e050d0c0203010b0402030405060f041b030b070e0307030803070e041e060f081606050307050904 85
    0x30050b03d1340c0400203644501c0f40142106d00c0c0c5180c079814010000307200e11034094401100e2035112031544400600a50442c4c901040e050142c4410810925001800c0c0e04180c000340d1141d4a02000040d03014107d000762404000700400640405080d80d03614080c18007110021a041682401000785011406005180c5040071200440d183c81c98200000c0c0780c07840090030680a074001d048080d60410110341a1410340b507018001d107000540e02d075024404030440601c050964030844210414460b0030003081152203000380e000388044044501848140c0c1b209540c020115400200080e003c840e03080151134202c0e114204c0c017100c0f44403106075403000c0400d94005a0782c0880903c1404800c0d038228104251525058000d4840180303103490b4141d25000c014424410702280031108001070703490342c2c0228460303242c0d4843d040b10045041e4142008040902440c00c444c0c14422000c07801c04000189880c5102c180081d4211880c2007500445150b00003901401c2404404c0c020405240d0321030064108958 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 960421798 1250 960420548 960420563
    0x3031603090602160b01120b0c0702031f0c17130f15020708272107050306090726100f0b060a020f0616200f10050402040b01050c030a121107 62
    0xc0885c18121645201070384440540305200004000054045c001c840c0d1204202800ea515404030703001286c00c0001804000c0344c107003030190508800316035942c084c9083c1d500950358070443d11462480348401c034100741c0f0280c007000e2142c9242e00002d000b55000c4039240d03225804102559002c0c0e04990140c1e005003000700c03080b0b240444c07481d071200a110000b00340c0b0460500201d1105007840040f49030940c5440c80f041d00380301000d041300b141c1350040192500802018040740d0302450074a08264840b00640651080a000390741c0208245005e643c4510725503032002c001d85100d00c9042d201c000189001402285060340f124001c00b450b60340c40c40608240140707500a0040d40100c2039080d414100002c02100c64560307a41e40d03400040303921803122170b0a003c0001e012a80200c40c80e20b05403078402d071070140c50064415041408145c9070150000c0b0f000d80c0c170954080c07003501d110100544081c080d1000c2002c0d86d6000b4001d203950f41c0d20503010445118400c24000901c200d400b5100001da920108058aa82 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 960423048 1250 960421798 960421837
    0x3031205220f1e0809040b042d06061e08091c030b01022104030206090d12020a0506010e0c0d05150a0b04031b050117040c0518010603050901060803031603090602 71
    0x70244040c03844600c18005014103000c401c80c1e0310750f4118003581705858000c9540b810740c2c415603121036109003108a9400d500301c642280038240c1f000794101c0100d00100b01070605000240650003043c4403041c4000f03482440d031340000c0000003140d080f040104000000c4c4104070205110441280424014286a40d0003103241010b15001924103e044e0703200d20300041c00c0742e480c0201403142e04140c40c02d5036412681250f80e103000b0b000054108040076030180010550000111810381c0009200010a1003003065500980e42c0301041600501c0854011410f658204428407014041c0e601c281e0788121440c03200080310a58402060704407965412850320705400180a01c14842031041c41c03035940c5e4145135440c3d182030824000070001d5409c5400542a50b01c4907005c10308020700e429402024002c0580b100030000305580c204409007c0a00c00d40000c01e01e4440414566441030107054281ea13230240c01186151940072085842e081c00a425104141ea40c146900000c3d41c00d000408015000c3c29038042c20 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 960424298 1250 960423048 960423053
    0xe040305041e0609120c09020c07050901170a1113110c0f12120403050c030d090308090102030405060c0903070819021c030e0607020a030b09010903031503031205220f 73
    0x1c1e680100038a840c0050221810012113502042d00307005c0e071700c2d11452181000b0340c40ca8000c404281310b400c8004503030f00103e00900031590000703240007100c004507050380305031b6a282c04407401340d441030061110300e800085414010030410b02c18010100740c054100030388040070207403240840340d10724203021020600150100110784100403401000392a00082c3c405100c2d910f0800c40d0303522500350682503500c82c00c40090306140c00380b001e5926004007441038955504c2c034035221800408614100714041056900030552048051090364031a583c041d00500d120703124000f003500540c005111150f07251056100101d12100140820003800320b401482c1c25500e4a07c0c0f04201082003404041c90102110400080100e0350140510587e1318081c1c40940ea1074400e8000318104c1c41d0f081d0000380c4000c0854090003c00710301580030042d01d90003503a0401c040000700424203450f01842c4000b40c0001e900350000303d800b01d40d40c2e20058109083e2001c66414041c071700c040845501c5041415100045403251003c01e = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 960425548 1250 960424298 960424319
    0x12090506040b0c04060519020102040b0d050a0c0e030a0311010b1207030b09010212070e061b0a1a0606040303140c0105010303020f0709050720011e060f05040902090c130e04030504 79
    0x10002c4410035003d04103401c10200600030701600f040787c07200d0200c12149a80d02c41c000c0d41100c0c043c1442024466459440502400c05400240c81c0313444d1103890801e141002605c40c03542ca0740843d8000f800340081a0f042e80b8204c0d00c0044150800455542e2001c080034a03650310380441004240d664050141e907880c50810301d9024900408440e016401040680c0c1c18041035880650304c801036040070900c1042c02804100319000c0c01e81014a00e1402008001e41003c00241d40440b280c1f01e41240c00b0500301148148441100c1540c250342c100b40280400d200107030203501c3cfc200c803900e5241407150405020200407420348200323034019000350f0840c0320529000c01c81808918050855070750140454202a8001000d0070010500f202044004100c1c07094200720a40002218116882c44203044c0590b044000f0004c201a01c40c4800c0110030070400100c0703082c039004011425030024982d00c003076a540c4055139042d41c050b100b0300324224500ca41c0852a100352074001400b4500a035642a1640e090240411 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 960426798 1250 960425548 960425551
    0x1e0b0f06090d02010f0504030501020307031a01020706050307030b040f0f060305150601230d060f091a0f0d0f0512070c120f02041d0f01020711010f1e12090506040b 72
    0x2401500c0c104102140c1ea101c441c00a071501d9428603154005003621001241d40d03001d079420040c2594000410700c10000d61540145000b21521010503040461040042ea070301e084501c0b0f0b240204405200181070381d8000d5010043c41d01d0050b001280d0b0920420a103011100b0301c15020700116682c0505105100d41041190030558400c0c0d40412141030940000c1c18400800032101c078980071442084045003461400e8411042203103109200c010f85540c10380c000179482d4007841c603503245858410f5442568804295020700c201900810300580d001c07051003240c2c0c0c00c0000568002481740e412038009242000a180d5402101d201039460700e44034940b10a08005580c410081c03200f1b01558640400c00e9039809411300e0364125400640c10b06201c1c0251940501440844030b00e00900c5c0c004201020107400805e00d0a00c00c4094081050100d001960f410071181550310001e0084401d1646103400003042c0d100703210b09401d00c0e0b101e0411485020096815814040b105a08440e007403204020244200c2c5 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 960428048 1250 960426798 960426829
    0x212070e0619090b041410030201080901020703051603090b030a02090a0f051c021906050d1b08040f0f150e100204080a020105161e0311010603110d02041e0b 69
    0x2c0ea034a075075100b052070942c000c0d4007441e11403640d20351884000d5519a0f001c081c1406a03040c40e10030070b240807200444038180700d00c82030b0302158200c40004c080400600c01c9450703056164555a05200e1024075601d40b07184007400031000d000981c80301040c900c0002d000717548105140d0001581e02d40300c000501c55440c0c180d0f480740d0001178450406000c243d981c003112510f8a40d0801c07651440b10b1060000a100f200138605205044050300030205060754000000d0681d00c400e0003092000480000d59005000c80f41c100060015000d200800c00181002e8410340206004501500243c4c2d03003515002da0007070410014a0f403003640c5003240000060140080d00030848108021410309152608064403503010f003c0003070400030002079561000e50f0146009000c5038002d101550344840d2980050340c0c480510000790301040d0800c2440060040c14000c1c001a6548072940c551800004810b004403020300480480c3d106031181800d4031144c0d4288108107904ca0201800300300640c421081c80320404608807176 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 960429298 1250 960428048 960428059
    0x801060906030314371e0c0b190615030e060f0121080a0f1707020d0815040e1b09060a0e04020607050a120905060307020a08030c04030212070e06 64
    0x7003011940003a0000ca0101555014594030385003c003284400102001c0405001c03000c1450309607811035280c04180c1000040d03210020303c10030b140c11030f00078071260001e0b0400240d14541c022001441c08d0100c0c81d085a08038840300c100c0d01d14185a181910110741000c104205000801e0207816414040c0080c604101c5d000344c08142801c2c3c43c1ca944012050003158503001040440183c1014051244803103141c03c00111500c520110000030448a203a00d00c44000130280f05d0307915a0051080b07130307890180045d50000c2406444010041c1e03078014008000092524842038109a03d40381c6008281d44401e0680260800c00484403001c1d015000010281d400b40d0302c240d04100054a42103010800e9402c0d80d174002c1419511480040c25610920b10b00400c00d0240da110354042007448030702640e0b0b4100a031100c2d00c03210348420038003210303000403181c2c10300580c0622560004184001f00554010001d060003521b01381d101c0d00800d03200c19210565020a500c0348400b00501500000c00c00d1704028200d50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 960430548 1250 960429298 960429311
    0xe1507030516051305060c0c0618044505060702071502010b030a0215090a09020d0c21050403090f08070801060602010507020d0806010315030605040b0c0a0504030b0c040305011508010609 82
    0x44c00d034141001030003581c1c00ba210020f52680a01c00c10082e0002132640109225a00d85c180418885915070114026000d181041c550075504540042580840c000c68aa800e085410314101118112150030314000040c007500702620200d4418050144a41c2e0705800034140030b440c000760481d04050206050046901d0304007000380039038012440c0e0102c10b804030340c580181c5001091f00125442181503440c1c0c0125216000202c0f84020b4000c0d0008000c800c1d801c1040d0104000c00362480003015a81c00d03000b1885c10180c80c0a684203038001030700310303020713251006105171a01c04d03115604901390040c0c0ba1581c0692010000c090f001d000385c10142c92207100a10503070404d0040a5a51101c1403900d070b0030322940c2300006100740d00c694868448040c1c0842954540703036990070b0810090000f40c40a6420074403010015040102d114202e030003140a0b95a41864a403450f21400c41a26000d0003d100c10a4104800004954240100c6640d00307090556484124648a0042d084461642c030102609083c0341 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 960431654 1106 960430548 960430567
    0x120702280801060e0c070303021b07060e130b030a030c17030109020c010c0f080109021606050a06051903170a0309020312030a14040b0a0e150703051605 67
    0x1c020404580c60b07414040c40342c1011111907014403030030400540002d00c00d034003d00b4140030b079a01d203907032800004224034181042c40d030215000440c1d0b45402c0300c451a040c046201201c001e9070040018400341000b0a07211616084040c0600004c00c42c40c40034081d841c0d40c840f02c650404880380e46e036507031510388610094101c541641402c0d03280001c0c803405140a0340100c0e204401548411034941e10f0305080d60081e6100c1c050200900b5203000f82134000888500a4902070b41310118003290b40c07801c01d002d014007041d41305842040640d041c81d080010840301e02501150110b6190200d550b91000b070000d030701a21103604000c0d0184142c408034070304810010050b60090010403030a12925080400c0b6010074142605d0142481d1540008142d214210f54440300d04881390005a6550f00740e40c81003a41c0c50709044540300c01198aa00401081c18469031400386088040d040160900d40c009 = true := by decide +kernel

theorem cover : BRFrame.Cov 960251798 960431654 := by
  have h0 := BRFrame.cov_init 960251798
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 960251798 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 960251798 ≤ n) (h2 : n < 960431654) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
