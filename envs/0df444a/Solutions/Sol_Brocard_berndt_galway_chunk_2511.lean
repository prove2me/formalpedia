-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2511
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:55:31.215797+00:00
-- url     : https://prove2.me/submissions/5a2d0838-8f23-401d-9a08-138a4ac0ef06

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 451438848 ≤ n < 451618705 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 451440098 1250 451438848 451438877
    0xc030b0108062404080f060703020414090a0204080703060203010e180a030e030721050d050418180f0f0c08010501240e0310020403060e0303060603010b070303091b080607 75
    0x300e0000d001d1031040ba101011200486443d00c41e440201e40b0f00e01001d6640c0d5100d00513a86e944290040100841c484c0b0400101c11501c07900c01c2e2070603240003942a038501e018100401c80850000780c00440200d90801c40095280402c120380d10040d4070940d80075032a0340c91301120000040004006428002e00c0070a141c004c0000841e0310050315030f05003442184601003d010038584481b0b42c108c0c025603030f0080304006c50000e603104a141894464001c951000a401038111094001c5200d0240203261440400880c030110740c01c503a802d40c0c0d052803111300c500c141e5211300320104843c0200703455146010345450207010044c800300002d41642c8000f8040d075403415a180320342648805907950b0500300d20040607040c030301c01c161a1038032900050807141c004040c0304519000354440c0c80101c0f601031400740c590700d5804010064901c2501c0c010042e40c1503a1074440c0700e03505a840842c0840c20580d403050500300003801c03541414020310b1703442c0c1001e0140b030070414038510703020380600000148035856041180c03 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 451441348 1250 451440098 451440107
    0x11701030203030729040c1707030503030c09030102070614061c03020715030b040c0e19050303041406040305030d0f05070215070f14030f070314091005040309090f0504060c030b01 79
    0x2d0307903034020000513a4000000200d40d01c000883c0c0f961240324461010300007400308004413101611a07001e40703032350840030321558640d44e041c50748401041c0f0341081c000540780d1101030000c0c3c404c80502800141c680840380e90b5800841c0d00054802490007040030030b10003d81000181500501c032040300706404022a914081e40d40c9640384a02c5240d0b8aa010341c45582d144070b90045207140c40040e00034031407000e050b5400340c0503005852440340100410300800700c440707002d209804c1c01c0380c0c0060055031038982041448012001035140040d08110200030010004000300b0090681021100000a8100d01d01c0e44c00c105551016000008650000c08160030f403500c0206d4254020245007065a295643c81100f960418410f000c208007040001c000c101803c144125064031440d400e0380e0170080c3c540601c1c5a050464010b0324140140c1d88900f40c00110b1070515400b07182c219000e8105042104c0c1d64143c03010650b808445a02e031001d450b8824007003040003d004070100c013211810140003166803640000c0 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 451442598 1250 451441348 451441357
    0xf03041502031309050606040302091501080703150506030402060f03280203060105090d170c0309030105071b0303050a1d0a020a05030c42180d080a08070e0a09090201170103020303 79
    0x144d01555075400300f0a140d41c0c40303048500856020b80345003003500e00107030030f048080101e01c65180407801140000c0c64291003881840c5003280d00040d48002a030818060100f980c000a1040f41c00820070884885e071503010002440c420186994964141e40210000e0f62607901601c40e045200c41c01401032102d5a038001c0103803400414151035a801c06026030810743d820250b400f10200c6181c0340001c181208160100092100320f60907002841a0b0b102c00e01c0449040c90041c040e070300c0ba807051f4a45c040000380301c2e41003da003160507900041611288035038980c500141c1c8840c8055168030110465045050104140008140480190000d800c8a41c0800d2001c10300d522038540e603d0325410258403007080c50b4803031003612001c843c80d605510251040e2181607803084107518014003002507084210329005201c40e008513071101d07881c0c0c101506008141c85100024101c0c401b404010085036616032a01c044020090042c180b020030034007454000580140321400101c0341e010030213401440542c40020464 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 451443848 1250 451442598 451442609
    0x105180709050f0c0703140406090f05030c0f010f03060f1502100507081503190f0b0c04030201121d2509091a1e1006080109021216020f0f030415020313 67
    0x40760717100c18500c0c003100d80c1d10565461040c0c1d441c002c6000f003103165000d5500020f54035900c50040005445038201030b0350301a040003456002d480140d045125511890b40720039545090f00300400c041b41c89103030700c1a410101e40c10401c000780c080551501526810010107841c0c400852041140741071548004000b038100a00780c906e9110b0100780701006490401001021400000b0402c2c4540003501d8880403c140d40c482c1911041025004a0050036020b02210112a41611442d41c0c1c80d4602038138002909624030340c540007542428119813045420300030704040d541c0908041c2e00039112940c08840707440543d08007070440c6c0e242283c2000010740754607094100c04c0500d1006c10031035440081d48200300f00c01040c6030184080c8002401111520f00c1301801c140d0b0820f4035041c803035a8807202140b0890003078080311b0510050707100102d844005005c448021181c110b1040e1000e51b481103242d2803524441e4200c0481c10b5000040820404d8030580d804d02d0301d42c1d4644065450701e0070307012140c41030090710b001d40c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 451445098 1250 451443848 451443871
    0x1c082107080c03090a0b010902090f01140711040209040c0f020f0714090c0c0a030215070804080910021903020a020a0b030903030406020315040903080a1d0714030a050105180709050f 80
    0x224800b9907040140c6030005e640b0001c0c40f9107960b154802d01d8080e40054940c1c1d030141800b0303000f1170712540c0a00760301c0d0380d50200c0188080c2012025200d000301024500d0049410640c00c100003c0d182d00d4500400c182200b0607102c03200c0611455600134a846409903201d06540c1001d281400702407490081120011001c42e5030002c0d60301c8000c65081c83d441441900b81841c41610864801c05801213101c420766807110f060040c0d10350b5251003d460f110720846005044a00803c107425a038900171801705148812881190b0300d01c0030041c6c80445501c1065070542c00340e40000000011480e1031102c1c0700103004070035803250560500418983e940d00001e0001460030707801000040c9100207510f02511171100080c028001c0822a080103800c503001a0760170341d8800d0400a1800340c010340e07004011089000301000b0b00d440ca150035030007002c0c04441c508840d07243c041d548900d000b05209000300c50043e52442140451420000340c124600400c940c4a82d04c110f04240c108454200b802c051b1651003000360700d0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 451446348 1250 451445098 451445101
    0x6050a12080909100f060201020901090611010603080a030b09150603190e03040312030e0106030c090c05120f0907081902150918070e04090b13021c082107080c03 71
    0x1c01580600582d0141c40c1c11080340410400d25216102800e41150b0343c41c2c2030807810649400c400c070f00340c0c4501f21005002c540001070404c11035220700c00324094180d00c000002840c0745c99a42e4800aa400580850000f030344440c0c0c5801c1d84d24259a84a4004402403c110728060030034010079600d00000740f00720750340001030741040e95018440d00032001c60f408417000d50741d035241c981c507008008220140064000a2030078120343c0e4022414803130481600c0d042100e246019180000d0710b0040d01401101d8070410038180508400240440c40e06400f99a0041d03140419143c40110689841003d5004280f6035025100125609202500c00d400094059501c420321002800c4080c1c080d2003103a11260704082403911148418655402d001c0c0503425640d00e40480d20603003420001511141100039102c40010404210225042c55007081100c1c4050001e4108060000410210840c10041543d0008001035149a40079031025001e20b224918021550942400080100401002000c001c3d02020000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 451447598 1250 451446348 451446353
    0x804050c0603043e030a03020709020f09060705100b090c040506070c1e0305061614130f030506060103060b040e160203130f0f08011e05070509090403030203180106050a12 75
    0x10a00c405000d503ca006111184688208000d00132000041c401c0712000e4648095880d0119464551582560003006c00a00300051030000b980000382203d0a21300400012007079032500d5001e40380681c042c1c2c001c2c101c0501c1c200300800c02e8130480c036002c0e48102ca0726420410015034110569050710401d0702c980d0349a40d61440c0440394034080c2d400007880942c1c07099006c01100e80001c00003060300e00c5607003980c1003074562007101c1054504804445000c581d210040e5050320452002401507542550b8124520940d01c039020003444459810a54003078100008000c02d5507058020744001b00b81010f2403a240524180c031214866002400b00101c544000c00042c100c1c520800c150790600d990086900001c1ea40c40498411080c4240324081c0d40010460002032000b106104410082100c1c413001240070900e650520010000286000e05020b420300c151003080d181d5107031a0748110721a0300c005079607007807420701c00e50450410f6501281c16818410288410b42715800c4e50b808454502140707201841c0d0f5407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 451448848 1250 451447598 451447613
    0x711010e0304030c0e071e090333020316111e03210112150b19030c1406070201180b0f03010e0619050105090d0b0c091c0c03141c020f010c0804050c060304 68
    0x651024101460708000100c40d0307045030040c402c54140c490301c1cac00c60003e1100070304000d03800b048071104d03d0012900701c0700b941140603031160f6050000c0c850994500000c00580554101d50142424000d80e1000c103a11941001151050002d40c10b81050f100496140031004802030248101c000c22501881d1801c0d24000384070703004072012000040c07c0d00e040c0e236414110817040d16040d200954021383d03038200020301290340d030308169042a0060513032480c14159070010359040446d00e120000701c0c4050b844c0007940041100103000c01d0241901036035070380c1d45032410403c640c6070040e10040c411418500c0c0e00c03c05c40042d4510070116142806c0060700c480b00b40000074000c2580601c0946000d80b00c008100050f5403080040030300f001d0032240803000c0840300c02a02c0726600340c0e00d0001d06981e40c014080c40451a82c4000561408040d811030344203003803d03071400841c404030f400c0e0003001d81c2c4000380705c501c640820700810600142c607140c01d4150745016110b0990719048081c0c454010040000810b0500142 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 451450098 1250 451448848 451448867
    0xf01031a03010c02330a0c110102030705070309080d020a200d0f020a0e09030d0207020d06020d050405300a1803050a020103051303170711010e0304030c0e071e 70
    0x20000c22400f861243d010b5255402c81104815503500b176501c5880b001e410418010049042a9554410f0b943e05a0044010241c419042d820311800040880b05d50800740002c40c0b2400007a40d9494855120f850058800325031500403c80c3c40e0407200d07031440305541c0042c0d0400f000707810456000901c0c078100c409203001651412210340054007100c1031400d0020340c0e098140d0740c0344203039802d20101d40d55480600340e40800703172000400350300308116141609101d50003a0010f9400149089015110b9a0f03802c012644207041480d0101d40328800c0009000060040c90031401480044000d10294032144d10003c5403070310205420640041142d80703a0f188145c02c2c00340c601401811200c0440d44908100e0f59449480c80100d00180c1400c0020310203020403075040899980c540c483d40c444800c0c18400d0422100700610010400209a899079040030003401580c041e12220f0b006950f5807400c5040a14101d000d6400c40103541f0003007c00d000c1d1b0694400e15403804000c004418018101100340100c43d000d20 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 451451348 1250 451450098 451450151
    0x30f030a0e010b090f070f2618030301030201090b0c100204120b010519030b1b03011818081215030102030c0a1e021930031b0906030e01110307030509060906060f0103 73
    0x30003107810076101390075104160042032740843d0308880f0808041002c0d502c4c80240402030000f44030b00e00420845010b82c0180030401c40000c01d85850320312607800300301240c00543c015268020341080950a00c110b06121a02409065030a000c00c030050811070342c20000180300c004c0c40001c0c8440001c4102c4045880d40c000c0000915102d50b50303580d218000c14000343e092060f002030380d180511000e20b01403260341e0381110b00e03840302c0c045083c01e0360382001100c0941c004207590b800f6806c01c80208419a020310040d8841e1200890254641e070030030364002d2000140b400e03198541040c440c0008100c60300000e2070303600c0c00007050400c2d21400807450310744d005c062918030490340d620101d0082e80b01075610024140450380d2941e42007181c80c1245820040c1080200c800202040c2101c0091080c54440e03004010712460550001c504030103010302c0c941c1c03a540202c40403000207541e00c081c0704820100b88076041e007000c140d100520311414000000303014a203404054505255841c1e282000f58420410010008003 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 451452598 1250 451451348 451451387
    0x8151201020a0224010614030a1503030306060909021639060e1e04151703030714040e01270e0d1107080703080c030f030a0e010b090f070f 61
    0x61807090041d660328004142001d4880e820403002039440311406000d812110550347c1c1031101c40c502d0540802c6944007410201c0146d07110800c80d00c40441d030540410045120f42e030001282c0b403419500605400703640d000000c1d0280104044201400d84850940f08190403042d1020b1030100c0204600502034958100b12001c000146030100011405d125002115404c1d1540c0790034070300420400c02c44a090707015141e42481031584c1900b0505142d4040055461003050500901e03495101c520904144103981c4c414550000040180e4651303c5200f0b110750b030130186400d506080c244116180792110501924000610314515650b0003109403080c61408094602c1c200314402e541400280c8500403690040041130340441402d652040c0003440c40c00b1145010050611740c0d08645d034a50841d80030200542c0c1030f1006000d120300c0c1c0e980e1100254090340c51202f00007035502d19404443c1c20342c1c2101c40c809204a9401d401c1120380000c42540e140c0c09469441c1088444a0410041d544034030110402000c04 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 451453848 1250 451452598 451452607
    0x51506041503150e100501050721091a031b04051507020f04020d0b091005030a08030c120f1608100e0a0608030a0c02040e010603021513080d0905040c0f0815120102 72
    0x102c0a44c01c07071501400c0c41e20200300200d51941d006440d188101c80c4001c0000e50041040625128088540600242c207443c0c9807909960310b2400100404820440c049022000003d0041426103011101c1c0c00100c0410760904003441d21000403181c0f04090503130307051300600044000855403840030140480750010011503c43e504140c1003001007101880603802102e00c480429005040b51042604031140140180000c4030325607144442504040d0220311f100e50300380200c1c0f6201c528010303414420781407041c0c65540c5107000070001c00d4558a0640f04d0080c48242c509019201c1c110202c40c4050310a030440e101e000d03841707260010700140710036130080e8041c0c0804651021010350101003a90058000ca90034011490948a180d00720741c07852000a50040994050304000009070014046040b03802420890300e960300c0c40014104502e0603174041c00990744900c11301180c0750038800c60034810468900364101c04d0380c9a0f00038028035000f8100c401038460b04081d1103155903d48050815012540009540350f = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 451455098 1250 451453848 451453859
    0x20d020a050c150907050f010507050106061e090f15110615010908161203051e030403110c01271a03040c0803070506040204150308070c0905150604150315 68
    0x6500000d20349511030094114030441c88000c840f202d07020b6105070b00603120191800c0d08005203020601190b5042c090140224408244284034010051a050712024481401c000c1c107400d20030784180703c8005020041034184030310842c11905400b580c0611f0052810507810380000d441d49406480405141c0c4545010080082842e00341d01031440020380300d120690382ca030380c1115200d4243c05a2000b0400b0a9102084048038001c00d0070000783c06410600e2410706583da80e9003440d50800c5c101324040800000b44400c040d40116441e40d0403450001804c403006400000038540c02c42c18003082c03d8084000d42c0200b4010b0841c0802c00202a0f10040f030a54068180516055400c1110700703071070030000740400007010b21000c011a00002d5100016052541d281d508220003440c0640c9003605001903040080300081320000100700d1503001e01810700c14186410002c0b01070b900000c103003d20042140c172056109032105010b5600b135a0030009070280d48452144220020642c40702480d0b00c1c103030655030000c0e8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 451456348 1250 451455098 451455107
    0x1020a02010c090605280e10020102250b06010c05010e03040608010f090c022e09050f100b0d0201050325050d060b090d0b090703080a0509120c0919020d020a 69
    0x1031100907181c0980c5544d550a0070358640c06030b200408011000103c8854a54000c02841400b0011034280480b84207100c001155514045800d00030142c5e50020300329411050101012200312108014080402c42c1c596604541001c058000e030b05200070100c08800f002402c2d001300003808a44001c880c1c5503076903000e00400c1c0314828401d00040b0078000340c010135130403254010040d40704119001800004214011900c8801e40000c04030000c1e840003500e820309982d00e0060580351805400100b08480b500d640e4282040c14038122896424a000e07410009512024003400c4050780900b466516540c40340b4140c14180c0c41e2044100d14050540c199241554000010300f003042c03c041020480c0301d0b11003019100c94401c0c01c44480c8d00100241d100400554640b50840d4020301d200c0607550010f66960341c0cc16203802400c3c0d001d010030000702e408516424001d0044218206090003023031100910408910140409005000780883c612401c08540503a50100c40301c4000312142159560500b500092 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 451457598 1250 451456348 451456361
    0xf0203061314010905190f020306070309061a130c0c120f08010603050c0910020f0601180b060910050c1204030f11100210050703150f0911070309031b0801020a0201 72
    0x1030342d22030709500700d00540d18148202c44205500200400c00b84416100074181440044411517a00c210510b03031000685007800070310302030011038a020944040d0b600c0c001058a240740c02c40d465110303c0c0c1c94000c40c035660302040d1012000460f040094052a119422107602402307800c05008408a00e85021580f944000e518607800c03010f0351000302c01d98a44000320309480c0141c0d1016104c030014010307841d85103003249190880b006a401101c00c01580d1203441c5003494401d920070f40e0119a4000150b030495014010b05011107001c488440ca414244030008543c0c0304002d41c02d204001001c0b5202503441c0d020820013000140080b42d41381c030f40d13940b8904412000c0e110641124038841c40703090309465084c600c64403002c28010341c01070310211900d20001401130900600b044205502c42c0b2002ca100e190380400000a0315089079038106850401441d20140d03000700d00307040e160306010404400440c0c1d02081c1e003010307264004180c0207d034115011940d8a05095005554194800260581c20710740540c0000e = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 451458848 1250 451457598 451457603
    0x309030309160311010e060723160302061c0608060a0b03100b100c0302070f03061410050904061503080d0c0f0807021f1104120b010f140d0f02030613 66
    0x11107880c0403040b00d620300000300d80310040104110300c2d444500c07980a00b444a4420b00054a00b506000194541c100c4005441c0c031510042481c1c8500f03075107504410721980c4503400041101410451555005c914ac0c0e03c00c4240007808082d07417050070360741c5140781c1d00700c08018040d94003255042d0070658199002403441c20a2244288190070314004c4d6551940101e50708024010b10f06000b070380d64900705888030b50110b64203c085000391140031810807540b060000255025a01c005825a0804645010480003518905460030b0b40003080200f956060a40342e40591312a50118065030b5090501d01402c015030002032890320040b900c62a0946694030482e2079a085585810140d885030809454201d0252401030058000c00001e40919008584039444548501f01c000f5000071404e42c1ca804503000b0750400c20540712140140406c1c810074021950144c04080e5840010a10300420981079015403c00d00c1e010f405581580000e100115042c2c4d0119500902070394101d00d006c2e45403130031140504008 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 451460098 1250 451458848 451458853
    0x3050612030a270b090906190b040504050c0c0a08160510020903100b0913050a020a0308040e010803040f060f020a140607021e03031b0d020c0706030b0613090507140309030309 77
    0x710700074125403040d40c0440f625007000c5440c0c40c9840041c405014002000c594003c202500c50000c40c4110a10b23400003017484d644050386807414101000242e41d000344c0f808859410030310003135180b84004290720721800c1c0d0045000b503444c00032644c640c007003894024016150703000390600c0c14603c1c00590010404200c0443c00d813102e010107a817882d0f0071a807241d9a000d410800c1d80c00065010036801404200f0030b80110121040201d45a0019140c20304c0d40e00300300c500d4900440d04019038020031000a01400701140914206810610104100c480074031403101008200380d151003020340240040a45a6044420b00345285c1c21040b03075a0340c640040c4d03140c20040c03143c0001c1c0f1000c4203a400d01c08880d2403100d0080d510f10b44840d1940d04200b5200e808003082c0c2d000c200000d241204103840101a02d040d0b460151883d00e1034690090b0446645080040c022581004001d40c0c0c007802d00c1d08181614808a40020107844110007210307101403101c9110075101c4c00100303000e9800c0000005c1d500c1225501d04 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 451461348 1250 451460098 451460147
    0x712060501080702060402040e0309091617011203121103240d0f0212011d06010515030103050a0b0910020f0409230c2808160201020a02030a03050612030a 68
    0x11201400201c0b043c00058100001180040c41c240e0044510340380450b040305d00b410081c034002a840442520702c070940500083c046e00541d904a14483d40e004514540c04031250300d094003000d07520002010003001c1001c9100c030b0740802c2c030441c0d00c214400300c4400345003912464401c07e42141241d46000d54009000400c0e0600e45074500038625400e1940d200100300c45002c1e440e820700c0134084000304440c46d95501c03540d04039540940a14081ca911003890010066945031905006000a01d0b02901c2c0340c800f4100014400315400141d0b030070150f0b90100e43c0e41d0f01942d90550607030402d01f41402c500c041f40c0c00000c202c000d44503500c0c040c0060300c1e45010204040c0c500b101c044500610705440c4110300703c2c44074002070101140c40f009400c144d52151480a2003800030034030041050192039418010512840c10b21035800855030048008000b1800214903203040c1600107996406075119000c10107490340d0019580392250080c88403a030310350608907070701c40d210240d01800315076041d5440701780c4807650301 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 451462598 1250 451461348 451461359
    0x30a09090c02071404020c19120c02100c140d020313090207260d02070804091404050705240711011202040501050f03070c05060103150e0705092805071206 68
    0x1055400e00070705500140300682c90000c0d04641c500284070151783c801d60a101c1d2041d842c5044c49820b2040c010742060740039010311850311482c004004007040c420002c1e01b4000c800142c5412469010030480c1c1c4c102240040f0041c44c111244420302d602d0544107000b010580340f031668000004d803140004204094032026140ca40840882c09400d1001c0e040f03001c1ca0000e030041c1000c051020801180f01c15803a441c1c80240901c03c4181d910044080301c241d58001f80801003010b062007826a40d25500d8a9030420341080d485071541d8454030302540344507260030501d4002007862840d02c5107180c50302012140d141e05090808210400c8a007420901007202004420700628942c401c59095802c141c42d014140a06001080b4a6801c000d05501c1480b0750340d01142c0100d40c0401c100d6000303501c1030300080c05460b240c400043c1510800f101d00ca0305940292400d0049580f10848954490b40b0498466405a54900c1c000400014006030b0100140750200b40498680d1009034100032248a45c1e083c85896500c1 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 451463848 1250 451462598 451462601
    0x7120f0210090b0406090302030408120a0f0e010e090601020f0a080301050423010e220c0609090b090606220906060f0519031508161e03050d080901140108030a0909 72
    0x801c2c009046200c2240041d000900ca94003d01031a40280704480c20f01da02c50740064980801d46041240c002c00201e070006906a011400741410403c034505030b21031a92101c0081c0c090b840f03a510309803140c98181d0015075141d100304100c11120210108550808500b0305007407400e0f90080c001d082c00707542841c1c175204e0115001050029100b102d40003420041e0f107805020040000c0142c2803c51160038811080000c0c3c000030f11584546000b1781c0200c2c00c0e03515040001d08105070720303440002d2030340c180608020300340e40740704000c0c1c1d20800c15240c1c0340d42d848000c540100c0c0307503042a40da42809003400c4000700d078050003548250301b968520f031240c585100e0035400503102800785400010003803208642d80d600e980d100b038006030f0014000c4492403255544030b420b400d05100781d41350f04109603c0744d032100f0482c0b5105e40b913107900034000c440008544070f400d43d2a9951035013200b0003e981401f000300085154000c007540b0462261000c001d038000c00d941c48003821502c1e540900080e50018008103404119802207 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 451465098 1250 451463848 451463861
    0x3010605030a0b07050703031518060501020606030a0206090d02040504051b040b0a090b03100c030f1b020607140d050f06010e18071b050f010603050709060b03010b070807120f0210 79
    0x1c1c1c0c0c03d440d1503480660864896011078400c800300768446141000030a052036420002d0890480c9400214454142040c03c071500303540301c2811035009000380000c0d9200803c854440e00c0d01541d10656034248000455800d0007101c038000e400c5490507041005200010a101400002c0d00c032204102807140d000308130648010103c8958480010a81000140501d80c0b003151a0700d0060306940c0c10b807410354044801c65255410748804a511881046c90703401c130300d12503030841045180400e460f091103100001d55600f0020a15018803440420303001d10390343c07940c050f1000401e41c4641030016151040500314001c8055414030301040d0380d0021441c841c5003500401c2505003c4d100001030030342e5241c000b00c070b4403078200d480f9030101281104424080342c028441d1881e0300d8050f10022034030600d0361415070324104990b404035030444c3c948501400300d110714204984c115021512010b032991010708000e456440b07694402010f0b03040e402201c0020326040340c071490b0004016000c1c0c0e11048088420001603521 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 451466348 1250 451465098 451465103
    0x519090308040b0304060b12012c060a02091909021818040b070c050102030901150b04081f0b030307050c0108090f121303050f1606090e041709040908070203010605030a 74
    0x18001807100c0b01c11400615403003400b0b1000450f035818401c010866862886480040e02c2e5120000a1001143d642710800301010400110440ac140071201a0702c03014090078400143da000212051242c0d2003544041c40600340b0a090f00c0c10729a200b2000000b9071089050810707181e80c42c04d0701d0000c0d141c0820b201803c031840344801c0d00306131b40360b03600d40c5503c11000f0005428010f581c891800416000d1001c0d49c403405002c40002503142c00710000d48400b48242d4041c40b40c400c0c007004140301404d00441c51020030004118034041e907580110011014102048070103405100209000d0280080003e014091003021788411126844e10044941c86902c011410b403115840b49442d44000880e03040180380c00e28100411840310b98995840764103100d0760302071203082c41d40030f002a02010070b46c4186a00c000e06141c2840050035240101031890003030010b00180c0007031054500c140c0e0800c110411200410350040c003c014140081c90003055981200341c080c1e00961801001055a04000451645aa4 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 451467598 1250 451466348 451466363
    0x302031f1413062004030b01080f0d02030d1509020d0f051b16140d020d110c0f01050313080c070801200f0c0c0409080901020606042f1905190903 64
    0x1019881d03043c050080d4002d210701c502119591307400d0441420020300042c510446040c1a40d500d005a0a0f1400500311000c4d1540d42128420800042d00007080702d80b0380155100c04103017580b4800c601c840ba0081e0b9407007924114000221070107c40312a6000440c4100314400400c8141c40354100c6480614031071045141c0304c80e0801a40ca09981801c1c520822188141c85030450008101901801c08100f04540e42c0940c0c0324140142045030040d211092071b8406000500e02c5080940020704207040c0d85469a041c03010000103d0341804c401d641c40003010307030440c60484c0d03185c2e0780d8049a46d440000d0720840c0c510b5403800e103100001e01512014030420342c01c28618107050030518114255241c1c040034003136a044c881c0c40ca2890307150315240201503ca41c001ca0055489040301000a0f0500c0310003050301e8800c07480c1444040510010080603075100c3c1c9003402d60801078000c4600701d0880d102c0d042400c80b40a090094100e030255020008044201d460340b5402a81e00440001f603030f5015080c0030040054 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 451468848 1250 451467598 451467631
    0xb03060f2404060b07060516110d1101020d0e0f0f0a0b0a05060621010f0801021219060e18070605120403030b011403040b0a0501050f060d0c02070302031f14 69
    0x801a24103500c28a070300040000600c10780c2e130000c000305035008080842e0f0858031303541040490211040c2a401044040c00d008000d040c0b00703480d458440310084070b0401442041c0e80040000582541078481c070000050007004000302d400d004580d16824840300d0308007841444151030303a4090108000d82d140e41d21004402d81d5459080308400541001810160005414442d840b04200c0140b0344503803003da910307082c601c19410100d01c1010032034942c00c2f10513140c0c01000401a0040d0340c41003180d0040f8008800d041c8240701490780f030f0141400d940700c00404c0b803108082c04003190340c21071949100c800c41d07404c4a00c0156260415503282c018a558000c03499003402c0080c010a00030b4020081c080d00525000120b0100e00300c1058540d00f05070380c29a40407100108004591056108560141004650000791440c5520004015224090600c08219210140210003500801c079240245034018183c4000c0c1a01c10207822062100004080301e0a080c40f502420a10000c0c4010340681c4224131089440d = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 451470098 1250 451468848 451468891
    0xc05070b04050309090411040b1f0804060b040c05031807242c030d020115090e01060b0a05030a0605090105010e0d0302120c03120f0c0403330b03060f 66
    0xc403500180291081d0100300b1103444150380392880340d071280e8403402d00701039400d0644c418041114810707000c09004001c0d441c0c0903090000600790428511a1528004a80740d035180740c00c101403c00c048420360081e0401345d451034101c2d04800914860082282011141010000500d0f50b841a80c401c1c06070402c0120940310b0308a4040d10340424080d1503040114001c02c901a5640d8110944030048100c40c619400300003641c41c1c240b00354002115540f0080c042c403c1401380e1980e02454921402d40555a01c0c070b201235086d0000c1d0000c2d402056501c2805880391a00d00000c4c104d6032003200d161804a16000c40890710b46008000507059800c181c1d41c081004400034244645a400c14100358158842d1300e103003007003040403e402481000d00a40240d51250000303800c404044001420007410000d41108100c2c05047c204182e80841b1303000302206280c00040c0c00c0c04025882c0d44401c00d8551060300e00564810001a0010301000743c0c15002c550346680c0f140c180c0741002a003602d8000501d284003414102 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 451471348 1250 451470098 451470113
    0x402040308031b12040f0308060411041806050a0e22030903150f05040c050a0f12030302220f0e07022103070318060c02010b06041a0706020405060d0b09060102010c0507 74
    0x21548103d0100510b0082c080300c02e20300c1e10000b01c400f01c40e50011074402e1000c01d07910480c1e0340d41003201a142804251b00100c40340c002400385008900504040c0f03003150b400340c2c6044d0032400060a0282005a407141c58100d02524042d084502c082c8900341001003550054a1100308405981c01d540d4090b00c0508582e07031003200034181464021070b9a101c1041e45605041c520610303000d1807240165140d024a003200340002c2d040544e118000400035500200150070203130107007040080c0e240c41d005940c1d0b51440c0e803620401d0008e140803030004850000102d461601003607010152070749424000c410750364102c4200d94030b038800359804050400d00a00060500c81c040043c6401c42514200070561340241c0f1050000780289075025602103840d141c05201058084c42100c420030340a41d012031800b800d20110611000020519081072503000a03100144502a4140c401505004000326a90700384458a00d028207450143c85114000e040007164843d801441400480562501d52a01b00b2102d42c844c541c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 451472598 1250 451471348 451471381
    0x510030b0718051011010506030a0b060d020d0506070302090312040605090918010c05181005031803250606140a0918050d200c0117060d170c010b040204030803 70
    0x100c02c40000c1501050300e5450340d880c8152141c00380d4420038032a44012106003074507006003c1600170b400801e020004100407119450b4001004c3d2042a8131107058408120f541401100252482c000d0b141031142441e45a00181480d0f0001c1f03007258030407660300c0a403902c98808c901c105030204004019400c29818a1403a896000f174041d8401a4ac25216502c40360941b20380d088088000384000541d40000c3c60b51928507a0090000d0300d80b0074500c2c400c590060050b1001610807003c064100380c12a504003020000c070340302c4005403c0595104e165800c0b102c00420501c10003182c55505010b00450840090702680418440040c9041c3d0464900f00480009084400c040c11103c0451151180842c0040000c203003200140c0d40c03445c0e0f403070413503d851b00a102c501ca2144141500179651201036030f03030300c01c00c6600c0001120b5011800d80c2c0398000003803851400d210000b0042d880154004818100c14800341400c0c1488000a010411244040108901c034130b000061180c02c0600101d16008450801c41 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 451473848 1250 451472598 451472627
    0x5030a0c0311040603060e0a050f06090903220314011407050c0106150806030615010e100c14010c0f0201110f160605041b090207020f0108090726010510030b07 70
    0xb020040d5004040d4640d0040d0030610200740c0b205010080c006030022040d41c03150075070404101d00d00300840c040144a00141c24248100740c802c0200328a030f0014000c965503003000020b24140001880c205240050851005940c4d101da1034100840705641070003462095507000340c0c18103082e918900305884c950045e0016498035941c401000c115031240142ca41c1c0d881e0700c03c3c2c6600d1601e2030580c080510700780d401040c0490580c40040130725440e0b40c01c40c0012042031811105100b40003043d010464030100c0c070080140425024010003607400c0340c1036014906403805541da1021581d400a41a802c0c2c1e440096003106441041007480080423045003d844510841001081d1020f42501c0d9a41a12400e89040c0c0d050104041030407038242500481d030005126510301582020549d40020f42d1400050240038180000703080090842903051100310060020024a1035481d120791080c250020503e081c103034250b43c42c3c4004904c80c020300c0a10300048a60010780e061207940c0b06003003202c0c01c00901441 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 451475098 1250 451473848 451473851
    0xe090402010c12090b031005030f0a11090a090206030a0903090609080a082a150109111801051e09030c01140a030b010e0d1b1e0302012006130b0a0203010605030a0c03 73
    0x445c0c806600c60080d03015028541d8413011407410f042c209401d01c60340c441c0089a07680301018400024860390031004440d5411078281c00d081e0381e0307036500d4070140441c5072000b0351000000040040c4100140d00c4804424041d42e030300d036441510398205469000391406804c00c10380c0204281c3c00002c1d2101c00030b08510066600c0160440c2600d1700722001c843c40c45050b04050307048548165a04d507030602040d4010620860280002d5003074610500442c4500c9032003d60f1070343c82c2d0514000d181d001d6400ca0712008441458036440c0b0300c60b02c0c0160b00a07086080918449c0c040c020100b4034541c41007207040c0916642c40c0c0c4803850300801d40c0061b4024482c11b13201c54148000001d202c82d940c1e5841c03656950f0035000b0309480d49005220711040301000300a03001180b1070000d422054401c0c0403403001410960381d0a0800d80d40c4c0b0f5840190010191500e0741e81c40000740b243e00104140c02c8001d01103801c0c1c1a210700c03040320003525100301c0141680824050400000d85c01e0002038800750f000c2d0031011424844c1d040 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 451476348 1250 451475098 451475117
    0xc01060306141801020a0e0f030c1005090411040303020606210a0309140301061404020a02121b0706020a03020a170d05040b01050f0a05030d0e0a08030d0603030e090402010c12 77
    0x301c00003034451144881d020700c00e441040068424084542d0109110004001c514090888030040d100c3c1600d960304a000b00e048081983c1e460b1002c00c8450144203001780044a0441746c000000c0c1581e10008585002d5400d003c45000c8ea81c015600307036030560707a26170054039441c6e90390414002151012a070180090501d01d0a55034030b0070003403042c01e200320b000780e80e1440c03400c1c00d004c0503008110308085494020380c58243c0c01c0081c1148144584034a0808440c0580d48505c0211300701c0c50441c46a1810941010004000c031280c40c01d40c005000710360b280f2080c1c620903955600240e8031007010302409000342e046403426038001040c1030896008440002c03290750810014000034403c43e0803c543c11111144400014001440d100031a41d079088004c03943c481031030f400c10020a44800d0410314407000e01c900b13080050611b1b0740e8070f04014050140c400850344c8a00c000b031491005411984403c0c1c0115020442131020b5003880450b0300d21468040c0c444469800a5035260300d2416108400d9904000034101c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 451477598 1250 451476348 451476353
    0x302030c1e03040c0e040209070311090411120610080f04030c060c0806010e2d0f06180a0f08030703210905010504020f0406080d0507060207020406060c110a05150c010603 75
    0x580190400040000749a2646000e103440c480c00c08068010300642c4421700d0400c00140e4031032149913440002d91034045103034010b081d83c1e40244c0c02071400c015071250819903003031221300c501c01c0030f001500c142107901c0080e038803401c00344034001d2446001c580000b02180300144400c0c8034101c4031074105119280500b081e0314640c942e1812140401d682c080015003090502c0300540e48528400e0300100126002c01d022403180c8095110111041e0000e0aa20071884105e0a107a60702c0c030362196149005807045946800c9012501c0307010b584483c2079440391059030b4021600c400341030314120640e1041001146400b03500c0c1c4050b10003043d51000169041e044024507811501e00e4040d5960b024824000407070b65060503c1044036800e1002c2e407885c0103525240c0f04102c041c200284000c444a410700f030203541c904450820801901c03541002941084c2040e10010307209610290300070365580540548550102e26008008441c29079102c1c82d076020000c285180000c4c0c1d0041e0052018112440000564503601d5 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 451478848 1250 451477598 451477627
    0x9011706070e0f04060e091c02032a160603110f04050904050106170109030e03060f041209030203070f0510020a030f180e070309050609062502030c0f0d0912050c010302030c 76
    0x1600911440502d2205211405108208104901c140c409080000014500c0000e5503801003c52090311401070030b02c0140c482c40c00c1154be40302540c203a408d031101000500c110401c070301c45030f10170301000a2500c904812000d40f07040c151252003250b02071103841d041c80c1100b00306801002400580341c0795030741c0100041000020710029080001c180010540303e800e130a01902400c200350101b80641c1201f01000216015603208641c00f590181c400c1c0c05002e4445030403a070448940d04001e4251103040c2c00425001c400322440403c49030304480e800c5c0303001aa80300480e1220009000103000c20300c012005a00e60380600724440800100200340d00d0200e036603010030703000c0000540d81c0c3d45c0865a81d18601003400410b002981c1d100ca0074500801341d6007440100701004403a41123810001c2680c0500320342a071442402110400f8007080211840c0c0d080701c520540c0c60b0600031000e000402c1c031000c0e00241c0ca038403000d014194250020050700ba90610400154040e6200030042402441c00f000b02e240713000d060 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 451480098 1250 451478848 451478861
    0xd050304020a060825111609060509010f120305040b070b100b070209160c15020904050c0304151109090f01150306030530120f010b03040206091302091e09011706070e0f04 75
    0xb644e061f80840d51400803020300719002070300034500407800c12005000f84e04607083e0220440b502d49945221045050074120303400c0c040c1d40c00c0400401000194131040c0729540d5091350107100c0034590490b4050703480042280c0c501c5240d00084d00314040e003000580d5140041e640c0c100c80310707090410011190241d038940d07035035460354081c0b02c0d60241d010a2060203800c1900c40e00c0c1d40489124481032441c03c05849494030005000074429070551035644e80519941c020060324005075002d4405002c0f801c022001d039094200034011660503403071003080c21001600ca0300410003100d030000054215140840006c0c005d14450251036500c1001d0004003403032035809140240500c2c20485800059400c0c051502e1400c4e00d0103a1014140420034014040540d607681e048038240c4800316607144030304001d07400040190140d40300d6164810340800b03842d8905940c0441840400b901210310880681e00e0f8002e5650040c104a4004072661003040041c4180d4024a18140c60b40320041404c10702c0160b680c0082e054648 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 451481348 1250 451480098 451480123
    0xe0d030501030501050702060108150405121b0606041a010c080705030c1b0a151b0213140c13052202040f21021e120d050304020a06082511 61
    0x240c4100400c2402804e03c034440e00030f100c42c4042d1110354589540382c9da90347e00c1844c9207030804400742c000c07070b082010410001c48078103000300d540b41c3c0b40d80710780b00c842400081000360300c0c00c00d0007400f00241c150328083c89110602c1c02c80740f4008411048050044895035640d002c2150360500420480000c608100701821282071070300018051850561880f04100c1c00e0060024007170013560206008400303450a03801803501c0309107003004c00f185807001d120340034415500c0701030341083e602110030340400780a42121101d01c0c64080142059100c1283d0f600d00b6100e0580007460000e800e40c001d104501d400c40b54111a07041542c1c500c01c5c03091074140c8540480c1d00540c0031448003148031808110030b80d0703003150030070008501e235501c1c40b45544180c0101f0200340381100740f0346030114a004950000c0c0d07907100e11000e884846104543c00946449000342ca10707070081d10180d22640c200000000e05c244034001c440e100d07040480d11441740003640e005903280c1c0c07000c00b1031507018030903000140101010104100960000c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 451482598 1250 451481348 451481351
    0x13020d08031f1e060f0203190f03180b0703050603150703050411041509020306130203010f030303060f080d08070507050a031205070e150d02040803071103010630060e0d03 75
    0x44541c0301c8100c8940e11540b009040403c9800758007148881038814000703e0f1282d0400810203803008200300e003544602d81400d04c0c00c1a920030341c1c0e1025544500340c14200806601d00304134403c1c100e0381c0c0f00d0342c01c0e5003840001c0c555261500003450b414860b8016682045010341100e0711301303440380742c0c0b6140307441c084440d040060b41e2103003008103100c450700307024072598420741d0b0402a161521440d501c00c12114018a0102c94002000c90490f8945c45403822000312201400c644a5031507a0150b050042548016800a4100000840e03c8201c5184060888080c140180315a100d2500191080440205010b00307002c4140421004600140444200c80e4840d54070f0b11200f503680010001101c1000c0c14400030419030300180704854490f51300d0340d81040380300001c1c2e54990300181c41b658064400d03900214031500001c1022020000841c10205039900200c0081c05000e40395079020785c004c1841c588884000c030381d4441c0f805102c0e840385844103c940c099000441c40e0304036503044520f44015042000c0009 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 451483848 1250 451482598 451482631
    0x10201090c080c0906101e110703060501050901060905220f1103060315070f0503040c091b0909020307050711040b031b0a05030109030203030c130909140f06010b0313020d0803 77
    0x185060603e00741e000d217040782e80141c0c103055203038000c100f8403c510140a130025a40c2e41d2615280c01545c2e071203d10b43c4d00c02c04480d1501e8a914048003e08001e101e0300d40260801000460020f011300d4070070041d6000546a84000820150b980410740240700b0880c0f069542c03840d0644200f1014060011000101e040050390307418508145480d0107036190135a132228680c0b1051007800c5501c4484030452018078640a6120b840f00d0505d03105280b0300e85d119040940ca040700705d03d45046c0300d01e000802c8032035036203801c1521039483e00008241d110880300701000403410442680014000240c55003501809032000414100038000700b0324000b04100100e001010b424180701d140e103442ea44240140c03001b03030021b1010710044d540c040e59130300005c0c0c020550341c0c0011502520b40150700c6030060040c014580c0600c0407264500b021210b511070480011200d0240e41d507100c1d802d05001640c01d0481e400d11103210700d503680d9a400404008620b4400300e82c094040d01d492404942803401441c002c50a80c0103a1a48 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 451485098 1250 451483848 451483873
    0x30426130303022515030b04050108060103050601080304141e0d0303061712090103020702010c0606032618060901170109020318060702100f2c06060627010201090c08 73
    0x82441d841251002460206540c100c1e161311104044202c0b400000580301c204004501903015100b00e03208260028a008000a103500b80081c186040381d00a5007590740e243d885003940c9850344118001d100340710710040e000c020b082c00c0c14240040c90010300341021900062a01c00601502c0541106500117625010244007507024080c00550403c030980c010140d80a800d0b0100c2e01e18041d0800907418582e02003018019640a05911078001ea400a01081400e46900c0c049102c00c150b0803081c0d021034600c520900088004000704c40461000300014015020b40d0420800d299101d201c9150411040c0300312400b0581d1025a03003030180c440340d100035840b850300c0380381f40796081025007a042d21580181c2c280001d0980104000c90708555900001c0f4021200e000c0c07800140500303070f0345190200b44804404c1d40c8a60010340c0d01d80c5800c400c500781c03881c03a1500000c0001c2c2d8050034509060b07041240392503840110740580c03401080481800003089116240d00e4070000505160321400340ca410082901c1c0702c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 451486348 1250 451485098 451485103
    0x70206060a05010e0f0d0c0b070b0a020a08040f0507090228020304030f060e0309060c0318090606120405010b0a0605071401270302121b0712020603042613030302 71
    0x18000c8056480c400001d1900740000d16142e500800103004212219400419444444100008035000a10108a90f560b0380c4003100c1c039840038905844c4410030301c0c081201d9900e02e00880c0d91140c4d550b510580f06888030b07190010f0107600400129200d2041103000148614240007800c00000d80c023221020041c036000008500240c406120303001c54004200900014403c20103460040c0c1e00901300003807140206070010710f944a119000c07944001c000c5a82490007000100078607040124142c0c03140c5902e00c10051040d510740a0360040da02c030205000d47e190304210f0b01c4804d980503000b030001103034403040000841d208000c103030003100c0090400100340041c4000705541201c40301707010008005040c0100c0031003180b94000da00c0460f09401218140c1c040c141f0801071940030040141c0300641e101034084a00316500e0501c941381e800b9000707001d0005119895201060003482e005445549142d8641d540c08124007050000c4681061510000c4055620040090b210121034045445952411410040e2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 451487598 1250 451486348 451486351
    0xd091b0806010b1e0307031104030f1406010302060a03092105040f14010e01050a050c06071e02011a011b240501080a020a0b0d06030204090c2402030a0f0903050114070206 75
    0xb0202e20f00300280032481c2c4102c64001085400006915284d4031081c01c12005080724150012140c03c0224001c024080880c2d824002c051154040346042c064803441617803214801d110203540f02d0003d0000c8160039010b504007880300c500c60b210421401c11202c00da17950414811100b01d001840204003440307890400c800720f00c0580512584152a41c16410000f40b4034840704000381e042010200328291301a01640940364040380c103000342c50f150303d0722120007030046001c02440d02038516882e5141d40840d00600c102402c1000c80d1044e00c044000940064500410a2003800c070b80c00316040c202c0010844000c08003410301110084040f1503041d80789007000355141a00903510640210407400c00507680e520406013103401e000461070300c84c501c5079645c500404182e030019410a00740340601d0104800e81035028140d41c0764044104000c0400c4500098100903d0049409a4010009800518001c2c01c80391840719880c50298240381e22665964251351400d04001d480e2210301040c400300075014400c45 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 451488848 1250 451487598 451487609
    0xe15040b060c070311010552061505130f0c09080a020d080c0d23090d060b030109061107050606120d030209121207030806061305060d091b080601 64
    0xa0304004680b49200c1c0c0300c003054403000344580154184280541d0091041e646400001a1203071014024250424211f11114103014a16030011548848900700c4081d01401040c00704841c14074500181c3c0c03940020094008541d00c04600e5043c005031994441002c20030044800d000400c07a462600114030681d11101684014007449080034840d01a0000301140e540d07030110f66060111074603040c09412881034103000ea049010f680c401469081d00500102c0c40b8803a0100c442e5900b00e00da0b460540580501d20740c40d40c0c0801c5041003040400c20a07085050707981c0005000140d04a5955136400403140d00300401d100c4904003054800a0003410f00941d82d028600380d038000c100c5c0514031501c50315206500002018140d01242011140d10f414440359a814292003c0f50340068451914a1803600071a008400050510000800600300241030316020211100100d1040d030503c020060507400103014244941d80e107080c0040450501e064003940504d9540c2e01c1c0c4402410244c40b07500309901600700c07 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 451490098 1250 451488848 451488859
    0x504200c1b1f030203041b06090611120a110c0d0b0105103905060108151b1207050915040617060d020108100e190b180118060e15040b 59
    0x10398034007905601e082c0001c040c0d0701e40165603940700e1400e4030100d00102d11a11141421b40c1c0c0105001303400100c080150b869545868500c0b80045054540d945014800041a42c00c184000c40e403113030041c0003510407054014251511620b084000c507004410362070054598078078103c0100441e00b4212a0400c4d060380c50b14007404440c3c02482c8082c50000c0c83c0c0c00d854038110304880032466028459034002c15a030b510205a43c904c1d40d6a04080c0c0d6240c090340903995444070710030081007c09c0d030100101c0240e4900040d00501f030189000d40320182610042c04101480020050000e03e0f41e01c0c0385a000c003a00c612840240c441d418190000d181c1c04050444004001c450010700c41140d070340600c1c00314216424a86029107540708410b030403c0304c1e90b651180e40e4000a1106100041410350103c600403c000031003003088510410800c0303000042c1c10b02198525000c18014400340f031125240c1075000701d00c4000400d80940d0340c04c158501e000200c0e171010001e410714a18002e540b03458003601c1d4403070904a45 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 451491348 1250 451490098 451490119
    0x2a0203031e06030307060603080a031803090b1c0513030e1e040b04090f030302210402011e02010b1206100605040f0b09030a120c05070f0f0504200c1b 66
    0x40840c19001c049944482084124001401680c040044030000c5901030000e01007969245090642d94010400b4030f00403c1c1021800b8080802003000658490342590320a42c1039854034592014950104001030b054020469115040c81820b0140900400302d20000f0324911915040c000c101c04440c81c0418880c02d482c08032000041e00b004071309068190100c3c0c0002c1d2903600000010000c194000c001013142e800300c0001d009064040d0302415600141f2812071410f80c0641c0d1344e00210000c1206c0c001d002c80e8124000b10b06c03403031000c41403401044050000103004800880043d1080c200710103200c40550240c410801c1c41061004854020140e6050160030076050114402d1114054061183d6007c7d0124078000d440c0d50410020944607040480b401142c11546401003100002c0a0b00342d0701445000700010f00e00c1402000f040c03c807481c4210251000d030402c0e003004042c010750722030300c1f8010403001c86008130350b038a00c0c00800c01e2905881c01818190b455070f0b450240343c0d2003400f080d40b040c40d1444 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 451492598 1250 451491348 451491361
    0x1020a090303030e0c1008010e0105030a031403151903030905060a050f070606050916020c01080402091512010608030909011d06061b010c020705011b120c0201050d2a020303 76
    0x580e0105880e458200801c0080048050528051079005c3d0790350700003485501101c0b00754104142030b0582d075104404002c1c584c2c0352400d0640c1c0b00080706000f000600801401b244400702c03079002d55045419010381e24040c40025001800038150504200c4030000542010410150000e200100410080c1e0706c2c581023040c440000b42c2a070041c8802c040c000713080091400c00b000550390140001c1d01d402003101c14a4100380741c15400c03021006000e00d0262144002c809a1507000301d0403c2d202d290b0007000000c0c13a40e6100d24078070f00319101e022903980085158280b04951070f02805110041c001071130086440d0325070072017040508107040c0d00032040d070507045000c5900350209014165000c02c0a44050382d0b00e4410220240c1c0d107042c0c0d00d6203100c41b9480e0003128910181d001c21107200711113090b1785000e10303482c0200c208002403203000b81c028840a4802d0400100600851440f0540d5005040041c01c01406050f81c800350351604ca03402c040f9a620544410404c0c001c1d0180d40c280d02e0003880154198500380 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 451493848 1250 451492598 451492607
    0x11040c1416031106090106060306081f0c0e0303121501050309150c070212010b0a230f0d02100201061508091e0718050612061b030a060f2601020a 64
    0x444411007824911024041458040c04004482e02c840354100c1c1c0706454503001c6940241140e001d007000003801c0c9800001c030307180c000540b031045800741c25441a2884031000403070f0081c049407040703c003844541081a05699010310150814000e0501c4091040c41c2440240e10703001c103000b84e03050511009200703003c9888000110b034110314650b180c045105072615158100c140c01841c6000707500140320704461a6005040d0801d083c025801d465040081e62102844a5184c540c01c12080c0d09d07070f00000361a00c0740e2074620384140c417840d4040c040307418001c0319801040304022000c0c40800941c0d1580c80800c401c00d0505240d0961900510b415811403c1c050115600c80645034a550f131403000c1442181102d04003401004001c00352011040a29100700c0b801c01c2c09003008560040c031030000021031b035404800205075180b141c4d010010742e10184004011000841d080980a071207a241d4854001c60b28900080240c1c01070105580f454664042c4090700c200d0f030f01e180e2b5030341440716401030101c410f0701c0e5000b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 451495098 1250 451493848 451493857
    0x7060902240a110c10030e0606060315010e0d06050108030a02071a04050420040906060e0d0c0b07030302091017071e051c06090501080d090e042d11040c14 68
    0x40c0340c103403c1c0c0e400700503046203400903000c0b01541c00110343c2004c003443d40e011740c41020308080715810746813160b4809040150b61b0000310717209100e60104192401381580305985000007560028a40040c41d003541d01da040482e0000d0f00041100d03400040e1070b4080c42d0f01081410018648003c00d40c842944080c00c42100e80642c2c1305040c040d13a124488003001001c0f031941100720302104950030391213a666056034070240856110b010b002c01c03846040003210b800c0100041c02081c0c1c00c0302501c00c800e4900420b818071548543c0042c2c0400d64240904151541c400380c1d40040003030b1554039004210290031280c0322084000e816138091080d07940b40000400b9403101a400348146a080441d20342c1d0116000d428900f04409054042d0307450408046071030316090b0b002d0f90607643c1e20022103c0176031f010402036501d01d03194003a0810368005080040c000801c50054044250f807449146c00707401018601e00e562401c8020411600740300c2d4400032010340d040c140310300100c41d903441c40c14030f0700c4004004540b21741e8450b = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 451496348 1250 451495098 451495117
    0x80d02210301030f23010c0915091d07020f0307061401050609090109050903070606032d080d020703030e010c020606010305060a060917010216030906120b1e0a08030706090224 77
    0x204582590741000d003840d00000840c03030090000e1070781325100034810007040c01148242e22070b2621014101c1d10a8007104151803104a00d11403424000b000e01100c2c42f8010200301c110b2082c20b0101e40da8110a00203040010721626010031600c0b42c141115900d948142c01c940e004041c140a61a600e649901c011411a200d440b000140745c2c1350b4802143c218801c4803c0034000508040c80003040010030700700654896a481c1c24213920485d0030003654805001c01d00d0261401c081880180002005a0700502e8030911038100003d0454441c5410707429140e41c48103400c09070f000304082100e1540c040c003840313138000c10444622901900745800a820505540200441c900c260a43c400d45158254115000050402c80c540210a010703d401170100d086806440c3c00138203840039a501d0000c0d01d0241042d0f41c0f8000301b019194903107429604060058240700c082d4409450a00090320000520007046514000c60700441e91135030354014031a84d606890050110600d41100c40d4000403040e20550b4140034 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 451497598 1250 451496348 451496363
    0xb0a051209280507060c021e0f0901090e07090b01050f0f0409020c060a0c0306061b05010609020c0a110306040210180b030118051503071a04080d02210301030f 70
    0x86945689a1810420350b100b01e0014656150980c50580040607a200c0e552181c03040304c114913180c0708101c5098110260003504000e072400c1a14068142401d90140000041c00300880e5105800014404400a07480440031176903408102110f60f6003440054041c0c8040081406a5175200c030008009100b8030150300c0320200040307a140541d00c0114101c1c3c0080815000c01d5485604000301d554070760b00b003564800881403401c0d12150900340240101c504581d850303100d0045106010055526680d404602100c0e955a200404500f0002c584003803c210150080100b80b00f40c140c0c03800c1800001c100010510a5005004210040c0c2d5a884005021141481c00c3c00c010b80d505000d0310600800c1d500207500c5e1680200002c6428801540d6503501e00c1c0c0405014806500c4624400e2124181c41d060a0b405400030501070181500456074843c880d041003943c0380c5066075680b040d81c1400c204107001001604009071102d2605041c201103083c01e90000b001d189103500d580e03100701030814814001003411 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 451498848 1250 451497598 451497601
    0xf01230f04030f050d02040801020f031918060b031f05070f05120a0e100903020a0209010b07020a030209060307080f03121806071206030602030415050a06080c0405150d03030c090b0a0512 82
    0x110b45d501a10005d040841c000e54507041d0302546680144c10440e0784c25500307000c9841001d40c0000c80d0240103a545c0c4040f4084c0490020b5468110141c070380d5003003164040c03150b400c21252001900c42841482c04010703c00042c11b050280c0010642d244010b043c8040000910503400d035094905243ca4110102941c001500447c001c044c80c18a0000d12803170304610300d41159107050540101d40d024001d4401c40e40680240c3e01c9450640c030700e0082541c040d40107110b001e01400103060950090b0b030084c80040403208140d80c1c0e0803045103001040008149260808110304807612805000075400c1a114465a17910380c07481c4601507a101801820301c4c00300406880c410315441340550004002d90f4005205650301d19103030407c01060140d480000c10342c00c4c903100c00540161400d10841c01618454005400007104c114100400b40c40040c00c010100101c00243e450b60b80c4c1c1d0f4611600080c2d10070344020940f00000800038182f003a059000b456140c404004200441da800b0301103c52850b081400c16105 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 451500098 1250 451498848 451498867
    0x20c01050415020a1b0501020c06180907091703040e220807020105070c060f0e032802040216030f0305070f0c06020c0c120c0f030304050f0607050f01230f04030f05 72
    0x10a20070204c081c05512001c4015580303042c07904160825683e003a0229080f24515506001340c0b403081c0c0c0c42801441c1c1c0c003004034200ca031404244441d00305c80c4614001e0490740d00c620440180120b0280341c95055480050704020585100d00c0c074507807116015400490300c42c00101c11001070403040100a155607400600750045a01031401c1c1c07074449400c2510400c40c56150074014100ca40034407408400b1442c0c83c40c0385a240d03c1d002800d50b000344102d4900c8100c064201c03080c40100100e17982c040340d00c1074023440562083d4440000111440c0e00036034410440d1911003a001d400c582000c0e000e00208007d40d03007061505e90f0031015548800791721610041c4e6655040c0c40d020b00f0480a404400da1101d210850500c40b03800c00555030300e02120803100789050751004c0080640e40c2c030482c89919044010251048000d1910780081c2001c52f0258050740e68054a07101c2e11403c49200c0c07250341130b20003007039107079514200c8107185002d500042c285032403442c3d0304081d1805480000480c8a0500304000012407112 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 451501348 1250 451500098 451500103
    0x90504020f092d06030f01050919030c0b04050a0c0905040b040803060105070b040308010810330305010207150e0105040b0a0c18150e0118050f01170a0c0906020c0105041502 76
    0x5070700003040840410800f040145241040701511403078400d100d0361410218020040c0305150040c03800d280101004a484c4501000034440c0d0300c030980c18007880c5c03103072a4041010518564819440b03036014025489480c985003000c0101d5800c161140d501d45800c010001d24504205900290014210398495446e0750049070f482c41000c0e03008224180c020140800c0503000418203058400c42d601f0744040030300c01c00084049950004002d04412150400300c9503106101080441ca8010301250100c2036842c1c0e03d9442c2039a0000d10100c496500c40f55070510007100c2ca2142c05d8000f070030040240310030304080c0c1b5054907440010381010030440e07495080120441c0511100c20100854024032116241c2d9010404e003900e645040b50000301c0d8003a4012180366200303045481020042032020342c80350f400d210038025000c44800400381030000d0080364008c2c201c000700c10548a15183c0c07a0100e9a4020a18000c041d05070030380c05203084d03502000402500e40c0c2c100040d08e00750fa0700e00c0020642030342c0c1e5081c104d2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 451502598 1250 451501348 451501381
    0x10513090203031317012304050102072319331a0306070e010903030c0c090e0307030f05180f0418030c03080f04151a0a080304050307090504020f09 65
    0x25410310000804000340f03c400082c0000b117440798807121550799401d8540500f600c042e5124a5a01c1c00c0a140c02030b200c0121464060304103000308001402d0035410b40d680c45281490302d100001c0940c06820000042900f0840e8a4241000786100450303440159075800c048074a040303230501080b00b002c001c8561042180c1d0030160980310003600f4461404c1d403844040003468a40185130003030058000040010b0b00505042180302010f0f561840041c2c99a2070482d1418a1a0b000b200e403084103a4000510f01014016140180c035203501550340e0380c610303140180c42203800032224428082c0c10b10403e220405810f10081c82e40307a0582e904070003001c03044002001003035401701680041c60401219803d06034004481081d051194030355003026215030a41094604003190024a082501c10384444880c14a0300f150410218449140c8010380b101341c002503100d50f080d00104029440814100184e19041200c240100b40b0480c007041a03041a801040444094070341a0740904000004906100752900311030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 451503848 1250 451502598 451502603
    0x50a050d020a171303030b090f010e0907031a0601080a05100909080f1803060106050f030705070201170a0c02070e06061815040f05010f1b230304090212180601051309 73
    0x3c2c80b46045110b8a08810b0b4003e0242c00180c540113007460241850002d0b00e01030081c50745528050303803034030951056070a4010902c441d5401035801c0040015070a0440714400c40b00c81107103003217519209000400c8220700070082614141007006024020103d400d4070350a450034124089080078060903c0c140502c00e2103141d8011400025111000d40e41009002c0200d6800301d0540e00b450740c4c0c0c1e05040741d550141100c5010482d9040021410b0320380200000c10050784103040c00100c420a04200344882c070b0301203400300c04080d1591aa6000c5503070511464024101043c1a0070060030703d400407807190300900c02640d850807840020034559549042c1c1161010300c401c00d095654580313070410f0444099a40c8030b1035000c605082201507032140070f8040c5c00110f40c500046440c0c0440c054903a074548401c048410541e400d034545009090b0f50050006002803e4504d402580e20120040020904c034001000b8081c10b00600d00990052800452054115038080761070100039071000000c4401407001301c000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 451505098 1250 451503848 451503887
    0x9060403080d0515061908100902070308160c03050433030c02120307080a0906060909051b09091c0e060a0f0e0f0f09093a050a050d020a 60
    0x8156100b0500c1d0810b0f4440c00c1603035501c03048566040144100e60003255050203074030180c0c2940c880c40f144500b00c000e50101003888407020a6a481c5211000c99100710000d40001d04c011041108402c40c5a840604506152510341d061001e1130318010080d01a40c017400228072044550030072002103091400741507613051b51a004c80c084100e140075000703041e000285c00150103080e0f0b1a48013001c03140c096a01c6916140c464448070b030b440c00444401010f0b4100f003128010380e500d201054203c0a480740b210704a200c0c10060084031070b11214005224848451503224689a008200700900c0c00304110146040c100350b420303140700b4681015078010900180c01900a0070104030b5500c450b9210902260600c9962640c2c082c004500702401900d504030780e03402c3d0700000c109102005030708203290030940c8070400100b031360240c00d920f05251031940c01101201c0015281882d11000844144459044440c46c5003001c0b4030b400020702024046000b0f22003401034055020990381c10503801101c55800900070280c9 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 451506348 1250 451505098 451505107
    0x30c0c0d110d0207060e04020c1005100302150403082d0a0c0311072619060b090a0b010c0b0411121605030109020f04051e09060105100309020d02060906040308 70
    0x40082000c070340c6540c2508030344600c1c0382e50700116001181c0b441c00c1d2012030340e468000112240621010790f200c49002400c1d03218074503000401c4092489000d005080e04c0307010780391051031030040098000e1800b03014070013403070704020400010b202d0104848602241b4006c2650113480f03640f62441114a2490200f540303080000c0c40c4135800d80c001c03000c1205a00ca51258080315800800c010740e10001c41c06002d520790700081d5440302585000840d0705034500100101d44802e14460300c0c5071110303031000c2d00c1240c003e40c941b01c0f03816452400c00b4000e80e0080f15a0020401ea096850008255094890000d8103841d04240810184084113660000000e80944000307800e0030210142076461801c54141986049502804103603890706004a91035030350010f008502015000e410040104009446801c00d1032000c1542e0907900e5102c240d691080a10341c0c05410b417585400203004100a034100404e04140c07514016200580d41c500c12401d104e40c0503110543ca8000d41004240144660303040600034190106 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 451507598 1250 451506348 451506373
    0x150405091522020d0c0c030c031101020903030d0c020705060f0d0b06160302070e01080c03211911010c05030c0a0309080903070f080d052503020a0209042a051005030c0c 74
    0x80080c0700d00078901d14108112820000c0481b014044040b00400252296a420004c680b1400c099108201c901d00011b1030400c429000a20303540c0b00491222049480d141e50740710041e014003002c00181025100d4524200349600780c1e41e5944603007007500e04900c0da902001c031081d403100b2061390542404090240114a4a801d02955074601c2d03218480040750b10030004a0701c43c6001c52806810140680180b0f0001340303417240d203016000e03140d0b4000b032815804c1c403181d414030400302c00b603040c5410f01d51540803e0180840d04c890070340b080d100010042c802d0030070078014070031501c2080320781d8408640380c001201c0407035151040040c840d0f0721034140e252150900114400440500c403804652420b400c40361003e40c118000d44060007034440c8008a0f00040c140413032034207010015040220321900c10f98501460315400921152000e44056803080018410118045c1c15090041259048440e0311702c8001d1400c80001d040c8915403030035000b00032000c4086128080c1c3e04081d01d180e0390701581510761a00042 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 451508848 1250 451507598 451507601
    0xb0a17041109070f050f03060d121d060a120b030c061902060f0f040b180102030106050d0c091a090a050301140610110d0c0f050706050306150405091522 67
    0x42920032403540b408540350f03d00400380344503e03000755110141040d000440c0c100b1030b500024251604020711500c0c1000040070a8900b076041c2441780c071885031803c10b803419955206092890b0754000c8604000340c0d0009508207404140b150120500403441021389800f190405909110803500a0340204052603e10f408198006219505508480c0590b0f03810340b100c90214020340b0100c40404c1d8420100b00429440b01c18254400c00311402e00e040010500810350890b8426406800080c0c2c0102c1c000000714851300070000c1c0a546864190500c0d030404041c1c043c00304c1c18100b550100c03980010241115250914580018000140208000381c0000b401c419403620032242c040c450f0314111a00c00210f8098103880c101115560700030915102e584500303481c200d500d184140c0304240c0d998210000034a082060401400003580c41a442e0300b0201d06000f640310701c0b07903131008041e031040c003003401a903d400b5402c40d4441072800102c0012000b840204920502c030300c440c242002c01420140280b1501c0c0d = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 451510098 1250 451508848 451508873
    0x1012060f080c040b18060604080a0507090b0f0916020a05100203101d0a050a020702030f1c02030f1608090306010603050103150501061709010b0d0b0405010608070b03010b0a1704 78
    0xa605403601c4000c0881000101d40c0071a081c541d00c141c444641207500c55544d1865070b804500903007842c0c80d04d2740700d1711224940040c0034011103541d4440b2809102c00105c40c02004280f40042d00e1080b141070705071300042c401d030100030a4101e040003001800c14816100300300110410350403034180d61420007055039101c082d6104031340e9400004510040003401982da4102200050610304042250b621345502c418007800015107110460f94007403000b40003507601445001070800c0b20600410580c0a840d000c2d0107001300c4002d0000a41d0024401e105940714002c0844805880c0c011445404c5d40245c501445280035100255070544114000840c086415034841c6059074010310598a1051550120a094a009001e400e00203240c0c40e074011011240c2810580d040080c0e10000300e40c0d1030f010000f243d4007000c05801990980001001e00040c040e0038440c05000c2d00360030002c0c000143c100080c041c903034481032144c08419000002c046454034030459072031015100701e845642c82c504042c1010400b1005 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 451511348 1250 451510098 451510109
    0x524040c08030a12050405030d060b0304140d0219020303040b0301060f0e0d080d0c1103030a060603050906090a0201050c01060e010b07060c030608064326061012060f 73
    0x40300c48040360001d03002042d00d45058142e42c54043d114048210038015020160040303c0a2009100d002240c2d03106000c0e01d00a4503e0b218526143d150500b01800310851100540d900c5030440302416040d594045071418807843d2a44403685030048900c0030905d184166404501058008000420003a03401039000140882980e10324078452034610400101e9050340c0002410310304200f000300080c4906411180800c921400e103c02102c0700c103a0303410f0441d44200e4948c980203644210601241e50184107058020381c3c140700815181c50245191503491030b0f0444003905100d4082800000071600b500041c002d00301380381100c10355595136a425a4241c000010480c0c00608180240720428070034402d01c0229034900c80142000c2c0c881c01d2598034481c1003d0b0548940c000400c1c0c100001c550809140c114698181290925440d03510740c000f40650000c0311000741c01540c8949942580803409030847c2c0040c03081fa25400115042076003030b201010485080102203061000000725004406820000c031003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 451512598 1250 451511348 451511363
    0x31c0e01180b040e0a091208092404030e060c07030b0618070e040f0905030f09012312070903050105150310020f0717130308040f050406030506070309052404 69
    0x6030400592500c0c100750307000b007154509081c04204081202d8131030301c44c0c000c1c0910100150100c0c09032203100130021910303120030100d0300c1e00c0140143d049042140500203400280703568141690031b80c00c0400464007500c040d0410103800e4081c070b255034a040840d8641d15070781e0200e0b119075070b40e480d0403004c3c088102c800c280709191000d4001e041c2d0110260591091a403503a03000c085013400d40811004001b9505c607201115510010600010300402c01004480c590803842601c45085034001002c0350584c41100d840d0301c00740d800415260803110151280551188420506950b03406c504031120015503101800a40c03d11043c0b0001501d00703455400750341d40a80949092001c54030b11078003a0b00c161031481c020300e001046600045452182c2d00b100c98101c2e00c001510b85401c0c0001200106081d130000e03901150001030030804d203064101c60340c00912003030300c0a011092440d110b05459030002480716062645a1032250b003042401d210b04041e41e100c60001d140d150a103401584101c01003110219103c0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 451513848 1250 451512598 451512617
    0x1b0c0b04080a1505040b040f2112060f0b0703050a1407080a030b0109150c02030307060203090d02010e0a1101080a0f0e0a0218100302010f020309090406020705100920031c0e01 77
    0x8016019039407085030840302046d081d4855a03911099510305c01416030740d43c400c0c00c00014015100004000d030b00c02880d51102da920303a408220740304132071803a440364100180c001170070801d00d8110019a001a0b0309803d269071940c0c040c44099854080c2070040721001c3c0c8000a900c010000c179440584038206c4c0c141d80030008603128000540c2c418400380542010302c3c80c2e608034924804d00c5407140f0507942d0320140c1501d052041c10703601c10081e40c1007030303034511519006100c4039451107909105401c40d80d810103005001030b0b40d807601d805007206000310b100c504102500c4e0000e10240c050340c0143d0401c04485404010b8000b5050040b51201a542800c910480e80300d100c403050a280701090502403039034800003109481c9164019a0010403d450401c2503000030300c0401d110743d95a43d40a489140216000743c1d07550030300e117800707400e10700381c41c0c0a103015600d890401d0020480341c800200c1c0106600074448900003d00300060b1500b0f0f8808a91420382061700a58a000ca510816040045a0a0301c801c590b0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 451515098 1250 451513848 451513883
    0x1061e09090f0203071d0a180b030604030905032a0603070e09040b01050a0803031017160b030103031214150607050a0807060506010801030b0601030902040e0f1c020d1b0c0b04080a 79
    0x801954145954456078100c5c080c0126a1000d800c8c0b51500c0c100040081e6018521012a0070140c040b00c06401144002c03900300440e06050050083d40740c10140944400d1209100d030300c0e84c8490500f04039014040100c00125528050404680d070240f00800c1d100d1549094605680c48020900031507010b9204c0300b40002e40e07051700005480c002c0d48000c1d00588140c1c00d060440c01c41c1d000c108009103045c0729400c00e003601403041410450203001c001d0b607110358941c15802c010345403074034164038a20200d251030595001540c2411070340c0e400507101d0b2080c201c91030303400e00040c0d00c034054504094018040c0b282408108001c25000f803100a1007442d00344983d540c1d0500651340344400744406007000395010300290240d8413982c00240c0da1840140000346803d501130105180c84040e403200180ca901c926810801003000302c14100308003440f0b100800a4440c0e284005007054011203c0049800b142c40f0164200310700b01c2101e0011b4100c480300e8540316640c44920795134a61001c9010707602c142006522404 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 451516348 1250 451515098 451515137
    0x106150f09051507020a0e01083d060b0a02010501051003110711032a0306011509030803040c05042f09092406190806060301061e09090f020307 63
    0x4030001038031200182442c04050065541c03021030b900100e0381080107028010b03a20000c2d0304010704803280d120b00c02507050459051a00380f8201c2c2603000b141001c0506100c410740c14602d0852600074440c0c08002c00d50ba4a0340320040c1070075800c282d00c01900410b2984005030705600040c100d6000b2a880c0c103030540d803140c05908440182d02c0d18540f109c2c0c1082401c01290211052038641c9201a0403210741d154410300d07032114a507404410064440c066410b04002e45001c2140901404600f409915109002d82c4064400031892200812503500030000074244021003043d50014507000d001406051041c0c078044140c0111000054500e03114002410031416105090700c80149002c1c2800700d60380c640d0041000c1020340382c440046441000b15081d011600c0780c8014154141c1007441081605070541c1c406001e03030b180109a1400f8041c14001004440c0e880f1980c8001d5400030f05142c01b2608484404440c140d0158100c000711070f0400a03080c2d40c1e495291700840c45010250360344009002c11042500 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 451517598 1250 451516348 451516367
    0x20a021306260703021917012c030c010c051315020c0f03010f0c0809010b0102030c0a11011404120c1401090b0f072004051303020604060504020d0f05010615 69
    0x502156001120105402c0d03064892104511401c0c12546401e83d01e600069800c818000d0305004100c10702020050040a2115496610038071b9000344501c601410000e08202c0c0803480020020b8030a80c011518403005100301c602c0d11099900034001c80b955007a010381142c0c0b040741443d0904420300400580920b29022030116500c0943c090b0400079403040130882c40c650070115507a0300d55a200060583d01186201e504c0354080f03d074403104030900d892412107003140d84151402e03055400c10003911000040114008080c0769100412051801e440c2004903038120b00e400d4000c0d0000030003e000710390224003001e007403c890b208000594109445030342225044520740080c501203080340c40144200342801d00504085642ea054a41c10203500d174031003ca2800d143c0c02c12102c000b1070650b099030320f03003414000c0c41d43c03010030a1000c0d441c80d0f04540e4001d5a800000340040c19080e56031002c2021542c50440c94030b80389410007406121240741e424928000c100c0d03440f484503803a05006165001c07501903028030 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 451518848 1250 451517598 451517609
    0x1090f0b1f031704080d0809010c030b010503130503090303030c090f010c05060f070509131508010203040201080c0a1e050c0d020601230402071b0320060702010c0201020a0c06020a021306 82
    0x2060348502d1580c2c0c20300a0642e0b00b282d460fa100c402c0c400454904070800007000341440995803840c031414036240c02c0d0b08540c2009a000d08041c10a41507084590300041103c0d080482c008100a0b0310340c40f810304a0560251086440e80740c000082401303600b029072006407078491421110b200713180000c00c0c019a000007480000030b0043d0032140008402d070060000b0540d02042c04e0902d075140c25112000601000c420b01500132055a552010040900c501034010000c0c01c92030000314a5030030030f50000b03002c00c81c001f401c400702640d00140311007289110324456101c059050079110004c9605400181076500300340c104000c0e80c07042d4004120000e100040690480342d2034641860308403007001d02c1c6451030040c00a82e82c2c00075002c0100d03e00103000e11007440d0710f081d0030310287c80718581185080030865a00340f000401c0d10b0007940c0340081c0b03a0f950350111801f0030b0307090034170310440285840141d08244040b4005444001d031103c0010340107070086420360211748211003080ca5075134483c803108100da2503070251 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 451520098 1250 451518848 451518901
    0x100b030303100b09010905090915180316080d05012301020c0f041d0a141504051c12090b190e061302030a0b150109120506190e01090f0b 60
    0x810400346503c0003000d440760706242041e00151a00040788402d5800d84210034554001c52198402c622007a5203d030300203943d040b20513511503021807066603a005110f1158107046185907403100b0480d092044841440c90108144650f6a650041c2c1001d0304d0300c12402c0d0049900e080d076507070b215031001c10030b00c1c0c1605000f8521841421038030180001000164400310075920440c52011000204000540c0894884d50000c047d08002c410420b0406d040303014010042501c060a20000aa010400030000c1000b429080540d00b034860301200c000c3c18940b41d03951281d10b0183c8030301c1030010740c210b0684121074099800907401e80d0081d0301c00c2140c0d600d80d205c1d041e681151011400800c0704070110b0787c001c1d000904850382900b03e41c4821640400985101d0449020101c0700e85083d60003040c0c0380000c112110405901c000301d81c0f105030315580000e0010810071005040c42c522038030b495110a46651185001300320083c401d05d0b0030380d410340c1000c000f911240854000660043c464814900c80d24006107107 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 451521348 1250 451520098 451520131
    0x3030f0509100509010e0708010b0102070e0118021312030207030303051b090f01020307080f0d1512030e0a0b04140418051203041505040f11060a050405010c0501091202100b030303 79
    0x3460b0000703110140010045540f2549012142241000300001501055000080c01c040a2002a2502c4256070000303003041075002c01044400b070002a1007183710382195001d03903074140a003550b9044050f6a0080c1c522201c0300c10500051550015040007500d200752010002c0c2d84850a0903550240c2020200311030543c108400d20642c04d291940810003403042c0101c0703041c03800380e50301c1c3c0025030099040030028490102e000740d0b5011f00b43c061108004203c4501506150030541e05083d4140201800703400e1101120a40f1031702d8441e401e565008051000705a9240c949a0295628403000b10020b5441a428040c902e030101507044020070342c8030303404002080064a402410020b51300002e200383c0f0381c6000300c500308035840c80b5400f070240300d94031500d911080c0d140145440c00f90100c0109009010384005d012074444160000c0c1201c0a48009080103901c40107245002409849005001040d80401d0030407554141c0d0002012260503040700024440d9440d44401e1540e0fa00044032420310b07030b611054 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 451522598 1250 451521348 451521373
    0x60e0108070612180b090106140915120706020f07050a1d0901090204021204031205160e030a021f260103020f01170f160503090706200f010903030f0509 67
    0x16002c00c0072041d0f0100400d1000106083c00d40001c0540029150b0308240340810440c01401e00c1346001a01031000c03088041000540422251b0800a1181009480d5100b6aa4082c0c0d03400310185144280c0b0340403500f2594640c0e10003901c40500540400300d0307100381c18020813586482c1440b0019580070f01514501e05445480740d40c4240750103405101d041d50b86054100140e10749000400004a501e0511181414103190040500c0c0301e10b00e005407180c2c54281440012a23aa80948501f11034919090900392220f20010782460424031000303511404844000174429400111301444509680300e20121140f01c1740c00c04c8804c4400301d801007101040b2001031005144c40410889070b55018901004100c4880304454164041650090548080c407410020319a500140c50341a4804a1900c40c0c00e604000e41c0b09640c81d410b6018010074405035100c1e00c840c101148094074034031402032003290b02c5d04840311545070081035200020b40009003021185024000e16010f02405010707140001d120541424 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 451523848 1250 451522598 451522607
    0xd0206090925050a09060206130212070810050106030c0203041a13121a0601090506040905070c080d050f0a0921030b030102041d010509102102040e03030604060e01080706 75
    0x30b18584002100000d14038107880a01e94407240405103031107a50380c42101207005460050305500039011944244100000f240c03190400714610341d070540e1100b9248a45041c098108a20f1f034000408a21a10080d5002c810303842d08064100d4295840c00c22821104000403070301ca1043e405000041850101180b0640303240400030000b80c1426414010003548030550003004540d50303d401d0310944a00d400103008846455200c40d0413010900340b0340400c61524004c02d6440c000c40c4034043e002c41d91600019025805034500c130b002c2642c003569441e507031202c0705007400003403000741d4100c0090808040003680e04110341c0b280a889940106486000b05503501403030840c400303900c04a001b05501c8150185a6840034000b5102900c8496840055030910700d080501c01c00b0142c0c4a20720500400040c481400c450a5010302500e0600c0700064514400001000303541030410320094200340303050b112112541011024600580f0126020700c0490fa46400000c3c01082c03e008862003504501c0c02008542d028 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 451525098 1250 451523848 451523851
    0x309081b15040303020d05070305090d11030403140a0606080c130525030b01020c060a080408160c09020301080f070807180609110405030708061014040902041b0e0d02060909 76
    0x90003101c9803022071440c0c9900c11a070644044000c01d40101ea00e0700e040105014490f400707107031803400b00f00e10310785141440d90b01e000502040f0207000004198052003003060080790301039a0040350007805403d000800c6650780514180a840040c50a030300460b0044000c650502e60020007003075001140c54070f180440083c24050090540d003803010609030a40c080006c0140c20402e815100000e1400e005000a03007000e002e180c3c1d0620926003000641e1989400940d0250040e4210700c0305500c0b503203041c03021103c81c82d580303170040c00a01c82580005072840141c0c00a505954a80c02583e16902590140d555030301030314011400240c000d00001e0041c84110b840b5020708000f9042d020800075502c8039288101d44014071001c260400000e0107104078281003000320020f1484070001c0034180b0344241e20400001d92402402c840c1a81d2008201d003036a11500031001250b001402080700180341109400015030b070341441000300b40301011041c3c0c02d203001e43c050b48076250080e200a103444c503100e0802030074200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 451526348 1250 451525098 451525147
    0x60c0f27030609010c0201151d130c0312170906040618020402070501060f06021506041a060a0906030b0d0503070f030c0f050703030305011703070f0512160b07030908 73
    0x202aa8460036a942044224000c200020001030060703d02c51000b402c2d92040050404400040842040a2640405030045150004c0402140c0d0b8846035a62602c9002e1410060280d00c0d2a25011041c8107501d00645042441610361242c40140715440c1d40e00030f80d0444048001d030700214000340205941d0b810000c103031644c0035803820b22088030381c0c0018101e03045624140c1d143d82d0f544000344100c0e05d102012101030f007014002802ca10310907085982c0040402007800d8051900c412104031546400103081c022a04014000b5403242100c60b00105142101d01c9500d0009003231012420311811304c90810008030b50841c0c09907103080c500381c80301d180042c2034050880802c20fa110001000c900c00004c241d40301071140c40a0101e25156041c001d090304c5044c0c018180c401b008011a80c664000001104d10300c80c1c2c044607024010031035082c0390b82001c00e03d24080b8018500003030301440c0c1800200d84240c4c000d126400885107920744c0b50049080704d4040c1001054130a04004404000b0310490070020a5070 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 451527598 1250 451526348 451526407
    0x6070c0f0b0c130e091018030e03100207030e03120c0a0803060a030605011724010302010e03100612020a1502120f070606090b09070e030606010309170318060c0f 71
    0x28041803076480608040d40114140c1c24084107000030400e00307002c202d001c40440c0005101c142d00441c41c0c40c7c580710740d006004051107031000d00c001594405004030400349256500031901d41659042c0504121505e55050384070703028403907040100c1d010010a442003541081d0050800002c0ca60b070320355866001410503580103201040001c0002e03450300a0754080d102204440240010b800f144610f0000da190000b20f0111140e121240601c0c50032218038110781c0c09180a14450b11041c000c00d007800364090304001a2818140007148054841c0441080b45200391003101480380c1e1044000300e904115182500103030028ce14070120038448402030010030340c0003203041e8a00102d940d5048111a9281d12840c8030301d4583c100b46d41a85032007064154440f0380340c1404000c0c08400c0000030745900d0001c28103414590b4a0110b0340c240090500c9444130b01844032126030781e0742400c08020005d2400030740c89803174a01c10100001d141140f9401528041040e29058600b01200c4414018815849000302611003 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 451528848 1250 451527598 451527607
    0xf0206070f0e0402220906051f030902040f050117030f120603150a140c0309060c0a0c02180402100512040f111306051c03050f0307090f0b040806070c0f0b0c 69
    0x90383d49200402511540210400c680d2451201300c0d40032540540c0320207240362034941c0c02c00207919259600d43c0d500305042c0da811144c1d0f40300041500285148900a500649060440e840285a5621040c140c854903503640d100c3c0c2442c1341c2d4283d038034490380d900c15005072b42c14012160700c24583c4031501d070884402003d80703441074000034250581c00c500f102c2d80c1c050301d520b401c480c44074140701c800019044680390651924600d007c2112565030743c8041c12140b440c0300000f0301a40c0350b9100d4440c10141d070354010711000051341480c60314030032480140d0b41130344102100b00c18040100d01820460b604803040320a149500ea4550300e50340c1ea07a8083c0070b4251050180600f41d42d4887d07641e1050807854089040001070b803941014103202900c1c1101c80316441800c400ca2642001c0b0342c0140940342c2c100284e0b00429070300d50741c903107040f103141c0300f25400b80c5e41000c00240081038400050010744150b07031020085591940d95240d08507000b900201c4060041c4841c0e010700307030100300d100440d41e500540d4442140d251 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 451530098 1250 451528848 451528877
    0xb07350601021c02011410230f060a02031209010504020d110d1401051503030a0210050a0b0607080a0215040b070305040507080f030408010b0315061309020d060b010e010f0206070f 79
    0x210341c0542d190b2005075980e203a01b031003030403901610301d4102019030f0541e00c460307041070f1340d040078450800e15405104498841c1c1e0300c12035031a0040c0b8101310102400440d201c0d00c00010203981ea40100da40f03609041105000518440b070b05100300b074071840e001480700103420303125140c981c4c01195403511103030441445596030022428111152203c0d100365000061035140c4007020500403103280403224840c2e0401c00100d1061540000d901d40c40c48004140040d1540390064450000c3c07006440344c0d0b03003140000c500802845a04406860356001540949020f2001c40314041d16484045500800150480c0003260b00540721f9800720f54000e00c00e1044845c56600c0b061031628100e1440c9941c400b44e80300207005d00c05284c2c28003c06084c0a0300794010a0040e2071000500f10002c401040d1601540fa0311501c9810324000d908085122900a415800e500f400d1b0300340180600600c01e501800300311501c138050540d51240c5080391a0440f180c1c064441ea48450078112180846405000100017001000400 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 451531348 1250 451530098 451530133
    0x4090507170c06180f0117011703090a060305010501170115052203080a031d03030402040c090f030c260c0603100506210c07080d050712090b0735060102 67
    0x802c1c07105031100c0c001020f158081005001039065540e0400c000f07070082d07d007100096030040b4107483c00300c0c980c40600d0142405040c51406446002030340b03c0e102400c00104240c15500442c16554203030703101c482e02c02c032103881002500028420031021403c0401600c180904c21405081350380b00030340481010058111400c042c0480303542066034a81c00005035614103d8241c421550b8070b0651051040805140d00c20240e164040100040e0260f5165503d80c5a00e601c10048070001d030040c0748201c40200e0304d904120003401030307500460f00300321a4829440100300c0b56210032420340400d41d0042c5400182e8a05100c269000030b000040005403890010400d80e0307039080a810781c0c0c40d00084c0141203140002c4184595240a46400881041000180046140c02044a0503121080c40c0490540c03a0b00310110b0703142160380c450305055440c1120a000700a03402e0300030343c028182940d40c0c010701c00110202c2003041c0c20010804040300c40107103820048600303205049a110340140107491383c61118041206 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 451532598 1250 451531348 451531357
    0x60d02040504060c030f0c091401170108030a0314060607060f021908310602030403020c06030411030106060e0a1202060c150403030c0507020108011e0b1902010b04090507170c06 78
    0x120a50b80b58044c4190a44c1d240c072600d0b203880d2088009000080340854003924a06060165410300c003108100c02005034040c24a8004001c1c124a40e420950303996140b142d229000001c0c0b140c00a41043c80e104035a401151a02e4020200180411b00e0020315a468500074030704d255036901c0d01c031f40a2010785070780d182d0404e24484090b81c0352290041231030506d0b81c458204800f00c0381c452416a90790107114103028003418a114641d0b10217401a40c94480e4281685001d2498000c254421800020401046a08220150b24510039802402010b803079840030b8070189a01a605a02304040b10340c100000d08400424115890000e420b4910b403c8203120380c00d0400e05070034007103001002c0d0b000034001015810301c1561000d40c900d1400c2420702c03c1c181d000802444d0b040c400d403501600701259034080b103018843c0100041410b4041140d440800c44a96494078900c07a00100155190650658040c181405080302c8940c1c89000343c1601070030704803031441c0c40c814200010b005100f5a000c40c2e65a8440c1c2c0c0090 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 451533848 1250 451532598 451532603
    0x30a0804080106030b01090e0601122109090f050c0a030f060503030a08010515030f071115240d02060702280b03040213020a171e1806071b030305060d02040504 70
    0x104025086040c0170403003c0d410790110015900d401004c0500c4d000100d9a41d042d50031007410003d2459041c10700d01d00d0f011846070920305c088405d41d01c007410303070b50231491442c12500c1010003403000c105000c100100b1184d0803601504051820040801d00601c00d07844100040c81c1003800242c03558941000c40d00c0d64201c0c8001d00c021031600d174018001071030140d03450882188010601c0b840d40ca48011004400f04010f4070700030522140320f041c41c4020340280802c51001000803040d2500340b500c00e00141c030a4056107640402c01d6a50f6250b1082418003150100425401400162815030745500381700c40310b4150701c07000514000040700007441409044c6488010300b00d902185803a4105801080200c0c1c010280907030603244100a4008001d42081c0d50086050004611203a280c6da40a0015851303501d448402d054440b003130040082020040d80d80514281800d02111126503501c032041c0d40301000345242c0c0c03c0046464603260000b80c403c0d0802e651001c00076011b080d100c84503a0104041c0c81050703804 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 451535098 1250 451533848 451533851
    0x17040906121106030412050d02160308060109120308310f030801090b010804021525050f0f1b03071208070b0a02030c1e070b04030207060207050604030c0b09030a08040801 75
    0x1600309000c0e1001c01200b82150485605185040695445600c00c106141001c2070041c04907074200685590b80c181c424400030816024048100703840c005040d44c0088920901080f6200c40109200c404c4040c5440344d540d160700d82c10103544500708441203200480c3c094200c100002e04400c0d2144001c1001134002921607495182094400e00c0d01400c408016004103407120b1514203c040d40742c0c2c4c4000c0765500a60140c8035929070602450071b1040ca031255014070160f50f141d05030001c60040b01080780100441c01071003030b25000200c800341c2c5e81c1c44043c4469280a9079000f105240042910f01514012041c001000c980350151748802d0704812404c045020f9501c100701080703c0c0c0602450b200a42c1d400790806200314550718080340507115a00410314401e60200b406170410f5280810f40302268440c076001080108149810b1500035650a150b00940c00180a075000000700b60130550f050750182c030740c0511140300701420a80c20043d180c0106056607130612501c0200c0f0042400c000041c00a000d41ca0300 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 451536348 1250 451535098 451535129
    0x5250f0305010b09100c14031602131803110106051005030114040b0a060f200604020112050937110f0303091503040c08060106030b12030c070317040906 67
    0x8000d02203840c140c1c0700c40d15502080142c0449035403181c42e84600d007000f50400c098841010b0901aa84134000101c8144500c4000342e0b6142c40c7d5652800896490304c2242d496114007a4040200700340d070002580c11111001c0c0d81d0140d4006070207035500015841c0180300004005030741c0e1000030a03000d05a194200815400001482000613885d498100e61800340d405001407101c01e004500e0700e4809106420400000f0326003002e8583c421004240c13914102c2c5a07820314440000c1c551034507840c00b80d400301c0c0402d01c08460403084d0300450003034a00c40d00300b1902401e43c8254503c11400103800a03145400e081050041c00e8000c81011125000d01e94002c6d003000c907900c078456082c81103c1d00c4804d101c80c4a07a200340070b541450381c0e400e0503c00c04110320500c45501c1e5156032401c1606000160001842c5010f00030003c9034013079246d0b0010422410440d1820300501411a586480741b01c0c1001d41c1d01650400607050012a8181250000c0c00010b203003c1b82c902076841451404880c02034220803520070b407000303 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 451537598 1250 451536348 451536377
    0x150703170603010b1807021f0605010221090d0f02060a030e061305030d0209060f0a0201020c0709060b070308190f050907050105032a0706140717010f090525 69
    0xa00281d0280301a0001c111001c65140000c01d8840508411030600c2e082000103000d146c400d2144141d100d4400408000e050701c0042c0f948050505c40c01058014411099203c01211010318041000d50b20806403510b440410320500100da110104140e5a14000d00b0740c68006031a01c400a22f42d001a5980c005100c028840d480350a005026003054048020805003002048001c403c0322840d0410110050b0f80d102d8110215084d4000e4134004583e4090204500082580640042c00030900d1039041c2e03600c180e25098843d080341d20600482504160902040c0c0010f400b409030250442c5051034108035003135009000b00280d6481d031240181440d250301c280460080c0401100300a40000d00303160f0b09514150b0310384a00c00800900100f002c9500081c440c00c1404960704861405421040511810200201d030303c11425068410b0700000b181108080c40c7c80c03402d80c400740d069482441007441020f150801f8013029010141040003000e0079680041502c0300300040074400d6401d0368441c540c0c9898100d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 451538848 1250 451537598 451537637
    0x102040e0124020c03030f07020f09040305071a150103020901020709150512030c0d0804081608030f060d0b0c090a0518010602150108122a03040510020a0b0403030b150703 75
    0x2d0840040d5808200c038084280d5011090f01d030302c0610305100715180c0c1da070b40c000107103144500c0c0003058020518138140000c1c107600c100108455400740d00a6507900043c1000f40c4103009044903a11614415140b64a000f50322079001400344510520489083d030f900c4015100440d1480880b207001c1d64044401003240c6d0602d618514807014a0348060b600b00b891039004203460341001090001001850030004040241001c1501d500c0710020507001d8040c01a45003d400a40c0f040e1607051145c41c699000401c0e81c82d029001d202c0c4d00364011768440141d114541d8164507a0416030850354000c8412001290b10707102d40340380f20b8006028030314070101c0c0e5241c0000030341043c5141941004004518005000070302001403d0519241d0060721103590300c1c10a000301d540c201e078151229900c0c9004662b016060a000170141c82603d0703086401c681641f85c2c1d801e09a0381d50a0380107004040c80a00e20010b00801c3c005e03404074055187c00781818000003007580240300c2c1070b030000c0800c60108004100c0701814a000c03 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 451540098 1250 451538848 451538909
    0x2090109050105120a022109030706060b160305090a1e05090f0405030910031d0607090519170a0203030706050a05010f0b0712020c04230907180e0102040e01 69
    0xa0901d6440c1000c4d07502090031300c140041c81c04445a80001e10710340c2880c45c1610440344d0f015106039151a6050410040780c80b030b03002c03090940e5013a00b060303c04620001a5001c44e14011100d018078200260b02d03640554064000e18046540454071010029500c0560b4681154a0111101c1c04021302d080804000c00700b41c01420640660105000b0000040c40002c100c40a4a40850b2102003035620464214040d00c1030001259500c6c500501082c002400060130f1402030318144c03956240583c450007881188450b034104403a40c50f034214403c105502046600c42c050400e0001601c450b5820354020078a10781c003110084039025074540802c89140114490280500280f01c40985c0c0c0914100c640b100c14002c1c00c0001e440300540d1701650304813070b000b008403a1a81f840500144520802c01485100c0d06041d1103140905442c1680040c22008001c1000825505004580161845080041f00040550301503a0449650070000424100c5034002c0040c001c009015150049070310450106504009 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 451541348 1250 451540098 451540109
    0x601080d0201150b090a0518190b010e0f060409020a0503160306060903120306080106060234031b0e0f0106021903140711060f130f08060a09150e0102090109 69
    0x500048000f1581d012aa03540481d140c07454019103d610b6800003d001c82c82a90209502c05508001c0e019440e05850715284990031007044030792040f021149600544411003a0940001caa507040b000507490f10105201c0c400c68054905d42c20280c860b031303004041b6806070403070748003141000c01001500000414880a400c0081c5000d10520b4540240076101c004203000c010580c10411b590000c800e80b096000400800d10a002405a5a980c2d20065281c0d05035500c544030304440500c80d0708050400b40f408481d9480c0780800800180e10b5901ca1a02c804c0c152014404002e8400b81c0010301000e045154038080c1d14601c03c5981e0725407414a001e4a8200203400903001c0249401092000c6a04059200c4100ca9284592030761010f50780382c049205000111326035801640400c03542170290000014001e4511030700e00c84042242c54030907044100313145200f25400c0e0340c0200c0008440c001107403c1a109144116014440b00e5400c1d902c84054034202d5180c228980c0d40400c01c070007a980d000701c03208014131 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 451542598 1250 451541348 451541351
    0xc050316051b06030a0e012913110307030504021c03080609090d17060102010e01090b012c040f0f0209131b05210f030a03090c0b0a0e042703020601080d0201 69
    0x6182c00c0104203d80070060012104503550011b404501c5020741050900307100d45151400d5021b1b02c0b03084041041d00c00d018050003900e4030a40800e2090070f80c0304540c1041800520281199a464070440c00b07000003e10481e00501e460820a10300560008803009107482511181510b01e4900300307201009000401c0c62005920410341c00d076210341c00011400591101b60111111a520394005034003500303a002c0c001c401c039131030003490000380b000c62619141a11202d00e40030800d90f09210200751200e40f6145020809010702c2d01081c00201c400d4a4007103814829014090728207503c0d0006040440102c410103900c05008014200300722840e059408215072503203014200b103041002041e0030600045081150709941c00003503096600400c4070304041c0d800441269940c2500040050190103000c40440c1c0d684c601d20000304500c83c00c20f0035112203c0b03055503440c00c181c001c0300420010300501110012840c4180d9814520b031801c184240b00d50030300070740060880303524042c0d0251030b26141d94207900859 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 451543848 1250 451542598 451542643
    0x170a0f0b0411070f1b0314010e010606171302040e060703110315011101020c01061203030c0e0603040f0f05010f020a02160501021f06050306040f05150f010504020a0c05031605 77
    0x512441094406003034003c3d0030801300c003803903103000c02e0140c0403c152201200b519050010411907420202500760403400001d000000c01c0c1c518450036140345020b00c401103140c10110380484001d0000c5903500000c0d4410440d1150603580215040b03803000c20441116402040800090503058080c134000b04c0500c200d81850351815401031552201050b000c0c9041010240500003003080940641e03030540c1783c20001b00411a543c03200301100482a141c101e01107810030300c2c810100c0d4014186141001c00240600d407a5070340d46c0d03540d211030035001380046480104614809001c14003d00c074030300080c3c26030000103a9403102d1100103440c25000300160b1480003011141400303180d0f07010460031214810350100e201022045040d90015261941000783c142c401c40e420441809602c901150409024a080e6603070703000503459104001d482100e5113405100403400400c03c81c10030790b00610b100062413500b18403a840d940da51506660241c0007550b82e007030184400380b003801b82c18400740302035011420848456 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 451545098 1250 451543848 451543871
    0x702130923060c0a0c150e0d030501030b01060c06021b010b190312050f1207081e25050c0303180606090103030807080411181b0a1e170a0f0b04 63
    0x11034000800e02d001031071003c03800c803803124043c044040105e0352141c41e55411030b1440103214014079600d4003401c0380784618a800300750b02d4020320403541a81c0e000544007003a41c0c01d0240a03140144203079001c6480030707800c1003038074902009a52480b0000c0703040030002c107820f120780082280c49074603e1a00c0201c5500c0e0041040080c81c640380a00c0ba00c80e0300d041503a01c959418040762040c0c00b07603a150001e4150003804010603164001013251240d510211640d154240b89040d40b051007508991440c0351b0029000507040100c0a500700c28008a458644603103003160032250036095401c1903d0341c00e600c450082984801d00d0080c0700003540728070207540c1035060750700d192002013802da80500880305004508020806110503504004000a00034148584419100c901c8181c41c8008481600749108441e80e81d50501640000f102c940c1c240c1541d0f004008801c9035848100e604c00c00c011241440b0710b480e80280a9981000c7c070610030b8003140d50009a000b4200601015500410310070b501c141d1804103058070 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 451546348 1250 451545098 451545103
    0x30f060a0b011803030309021e1804060e0f070f17150903040f060c02040f060b070308091c021005060a18020c0a020303031614030c1c020702130923 65
    0x91000035550049861151940180c1e03402c021000f0514544030644404424150540c204140c22407080e01c1d507140b0100301861408014020351a40e580c00b40c03901d40c6038140d540703000300741d180c029000746c00000d130860290b0542e44c5020418581503007180c0040f90200301d845100041c03100200781d2110b440c82e0392400c40030311070f4848900c4405c5070310b1000c1d0140131407807166041042d10051320f0095420b00942d07442c0d031000380c59003031300c22400c0748a42d0800905040c0c0c2c0110303010300310813104214005401c200c0c40740d8080d1009400104419214070414483c014006140d1040c44102400d07500580b0484601c4103914060324001400c950040354101d0081191250015402d0b9002c4000c990050f101c0b0322103280c1c90b00389500c00c14060b61510010042c0810350042c40b0b0a081c100900b40c80354600440c1d01c00c10040d01c0d000c111664170a072802809999410300000346140342c40c1d0110040145400030550004032142514114001c6a41d82c503808001045441c140460b1029a400050001120b548401a6 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 451547598 1250 451546348 451546351
    0x1080c0306180c120106150512060d030e15090409080903100606080c0c031204030504090609090f030507020a080723060304052503060f1b0f0f0e06040905090606040b030f06 76
    0x74020054020122038004c420340c003900251140c030841040000206000400a0300700350380c0350001c464240c01142c82c5151114000306490752540703a150178a01048204003045021010644241e40d0400c9a01c04660b02d6128013007400d41b0850099444520b00c1050501c1c08000360300600310b0516015083c0682d64100020580c4028030855150b038a50540c0da00703504501030f041c010b02a1310340d081c040c8020941c00401070415101e150204200c5107680d0866001900c2c0c11240280180c2c50001481021070b210b0001024944d00181c40081410350f501700d064608450303a808043d0b074000600880103180d0304284601d444960468005056040544900e9240c0b191104000115006403180c40440d15200010f14000c50300301d44d0400800111150400103070421a240c40c48182070220403804060142050032210616641c0d0000d21a000140c10798854010302106903104409001c0081c030381c4414000e441c421407903003000e031016007840018401514604c1840314840d40050075048140e00c400607409 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 451548848 1250 451547598 451547623
    0x3040f030f02010908100f0c0329120d0201051f14130605100203071419061517010c0207050906150d0b060705030301030b010f050f210601080c030618 66
    0x21007a0801c2e1005a8640d0703540d601042d070a00030352091383d600c0807182c5d00c6007002141a0764141b1110300604400c8044510442c511444080340b880558001c1861800c0c0c0300242001510f0130500011a03540b40380b03009543c87c00040141c1d1164208024a04010303944140d030203914030018102420b0641010307101c060042044d000d011603032201c626500b00ca4114a00400c4060841c0f004500c00f660001e4503584692816241440701a11030443c3c44000540a002c001000008a040421070f58480b0058012580c020003060020800800c101c105000b0644880c40310000010381c82940d16400382c00c0524035404203100b10314660401c10a0340b11400491000d511003a0310340da0365104210400001e0035410016504048041581420443d0020095050340c4c010f90310baa80d5613030b803001808585c1140340170702e40c1c002e00c03c54009010323410081107540c0c80c140c1078040340c0900c4901082c124501a02684500c04580c440321240b803d6007802d0000302e410543e04650021611070a210040e900c82c050400c4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 451550098 1250 451548848 451548863
    0x6060f040c020109120c17040b0702120a021c02040b0f061902011407030606170912030a0902091609050105071a060a0801060602010c081302010f080c0d02071202010e03040f03 77
    0x1491030502c01c1d8084001c080c1e024021864100183e80c00038880300760080200e0b21582c445641c088071900c1ea006950444100d9401289000259801d20803410041c40201c04148100f100500041c0d460303c48042a0200084401c84004400d004000584c0c10352400640600014407250405841d1a801c4403415031110224018502c942001203006152214103200c03108140000c0c00582640754001c03900f00da05581d1125002e040b03001690740301140540d40b85001e50700280e080318502c40315201640d8400010714000030805a0394001c10081501102e80104d40709c848500078141d2a0803110f483c0150900303180807420003c01d40d940c84160600114021011882c1400194680d5204401c1d0b07c060004034000344100c598428001c4c0c00f0302078540c80c40303000c1402c50001a0414910340056440542c059403060203841041d801502c41103030240010350341080420203c1d20f0204180010700c0014030075103540c2d10a5040410007401c40b10b98003694001e40c0c2041104000302d00244111400ba0f1780c20210 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 451551348 1250 451550098 451550111
    0x110c0d030b0a1d0f091203130c051e010909020a050d021e0705010b0a0e090d1d12060a1d0d080a090606090b090115050d02090a0e16090806060f04 64
    0x42d95120594001e050a20078010070b6440c6009040300303c0e0081d4a03500c000c0301603031030341c942c42c43d1507110181046485135400e0000800d4244100d840400c182d006080c01046245c81d180032036a03c011581c0c20100740740d04014002001c0d42d00000b403500030651400114201201002c0051040c4140304145c90302035008031313001c0100785d01e011a002c012006e0f100c90540e203d1380c0c1c1c98400e000c1c0c5000740301079209480340140022a60000c44400d4860030f800d0000d4a8407999604007901c40040f4402d0504c003072090308681c5c0507961280464103c01d04480710042216140c0401540c040c2d901142c481890003040d110300303d00c08540051107d10101590401c00502d035038020040005102005024100c03508109000a1210180c3d0102c0c504400540310122183e0f294003040300d07500109554540015010484a40958010707409806401c2c4020180388800b955058401c002880c16030b5681c1c21407102c518008141908658850014401c07a070150410b4030b4140c0c001707842e81e0055a4080c0c0140d85800 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 451552598 1250 451551348 451551371
    0x140d0b0301061701140f1f0b0a09030c0821030705070609231606030b0f0603040309080709110906090d060603120e0f030a081605010e10110c0d03 64
    0x1005050154806002081859034480301d40100420010306050385500c3c002c4080000c0900c2c0400038030600c20504121030310b07107074280c00c03060911990b414a2240304200710085208030809008000d021415079400d00c0450440c101407869140031750040389560b00c03444166a142c400b100050154011200c40540c90780c0c1c0320300703041d11b161055841c01801c840c540399140d4200100a041041c0d010340061b41d62040c1c03005003501c2544c0c5c90543c000072030482e010f440c08200701442034102ca03c0034900901b49442c44085280419900d0b0400e440c100c02040100905015003042006800c004059004007031001d0420492a540c83e4850344002501078140040c840030146c840c1c00c0c0e180d402d00e41c0448100b1002e9544d0030011402c0c1c100c943c40310006801e010b002d00300c516003a00704031300050004010700310f02aa00d03900c401a0361301c040124910180310290b0000416002c0c451a0b441e085008007405c1164040f9a038441240d4500c1d041600c3e1180900c00d410307002000042d00a00d645490600140c1910040d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 451553848 1250 451552598 451552601
    0x106180803030c04030605010915170307150902010327030f030605030f010f05060402041802090111030c0a030e0d03050306040c02011104030c0306060803030127020d0c080603060106020d140d 84
    0x250401080d520002040c001035800180c003c01c01c803801a1010802a40c0306c80c600310940f8081c1c0c1c4541584805241d00340305440000044808402c1e41c401100d1424400c2d0740c4035903400d403090380c11540c1c103951104182c041d540c042c010300401c01e03a0111000404d064003900c05850502c4440d000d002c220038200c00d5407a50703011350311010242c80c00a0846002101043c1454060400001498015810600460340078100780c02a40d05807503141d000406019a1426040002d401006a0b6810400c0f0221000034504003400240502d507814409880e080696040290104800100c202d0281e4403003101341000c268400280c03604600100c4000c22801c1c40707444101d0140143c000c42c660803000008000040003400f038107040c2160b00c20101400302d103030759601558503404244290200401d0340d00c80c0c500900c00345425851807814aa4006040c0740c0404174000803101c41b9010800410f804000340f18142c03408011245c018240792000704245c904030500248501131040c290041842c01080004c02c4d02c4030b9 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 451555098 1250 451553848 451553897
    0x3106020705010807050a26270a020d051501031b060f0921050f010b01080c0406052b060f03050c0a08121c050f220b0c0c0a0f1b080705090106 62
    0x500803032243c141c0c2d4541e0701540c41f9409a4800c100078441403240c0b604040c42d4548a450881050f015005442c86a001e000002c01100c0086aa0340150015404000c0501e00941c0c0a50300034100c142c048207103103100d881c08115542001c0184110701c100320000e10390018400c0c0503158136103142200c60f01c00c0500c200c040c44111800070907a00850040d0030031442d05600800000710260307905000b40d181c0e00c0d034028151046018540000d81c080113000c0b21020a45060211021034141404110b0003401a000444040e030b0842c1c0c840c01c200d85800c000b40103003000a850490005c4a07568520b13450604079540d0307241054418582454085006860280c0440d80190a08520441404140303003120490048090442e013856000311000030b985072a4403480200c6072075561200b41c402c41522038a1050546030801c054005103480b4811008001803100070003540c80781e1181800da041c0a80b513040401c0307403c81e03507004000c40b0381c0300881c01c01c075598618003a541183c0c0c090074440e1500700b0b1100e05d10b244201 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 451556348 1250 451555098 451555127
    0x10201021603050307020c010e0a0b03190e06060a090218040507020f03070501090c06080f060d151b0e03030f1b071509060210020412020f03033106020705010807050a 73
    0x55001c1c0505140d0440d004501c40d10469094840e003500c113400554280201601240e00001c0d0004148a40c0a60700d00039a0041078400b1504980521580b000080d12031400215015801c05420b00c1841e007441c003008005040426015400d000c000020028240012840c00d445140c070b40c800708076041e0003442200c1c0c0806100d020b0700d90341c88a60070154040d150701082203911440b8060000b0ba510311546d42c050096000b41083c0b038558981ca01045042040c0017025942040c03868100c00660300c1c103204043e80018490216401401d111002404c10b10381100d405000382c0080191440025000c0210b460f104011072450f5589180d0950051522100c0d8100004e80f01200c1e955280c25900445544110340d1594203d48540c000314080308260301461261a103150b03016030b095801890b0500d0a04800000502201c0c100001704401a0611030406260244003c40c01c4008002c0e0004080c075070701401e0640000c0c0b0800c1e10b010002098400000c040d00c04011000c02c03524282c61088598840380c80 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 451557598 1250 451556348 451556377
    0x5030319140d050f010608091c0504181e150501030f09051e0c0f150a0c06050703060305120c03040618180e010b01141909090c0c150203130f0201020102 67
    0x111450303202d00c020b00d01034403000d02c240f4100c2c0000511512440503503118100b01406071a000ba0903260034460401800021810301c10180070129541c00035444040802c44482000f0981030f00a14030301c1480c130048070004d0502818681110055081d0707580001c00c80c1d0003881e0002d001c0c82400400e03401800710a600030164000e130140b81c461036600811003014600402e0036600c8250440c3c00b0020041c074454101c3d60041045da6094241035096405440540341500341489898819521f039011038404440030740102c1d56130300d000d100f403000c1000540f54684610500900d48190b6020466486c0200c0c071480d0708020b100900845180f2440305500018078000c4030030b0103410300e030078075400161420112100c41580b072b100720740e151580320b1404000b18483e0703020600c1c03803e0307070aa0b86440c84030741d0b002c2c0c1002804039190700040e04600c40e10501d11544041da0301c02412035103501d40441000512509601014014401e00c9000860b005480302004d600c1807503586030f4099803006074064002c55006a000c103 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 451558848 1250 451557598 451557607
    0x1110703080301030c1202030c0105090607050d03051e042102031c06051c021807110a050303040b010608010b0f0706060801050f090c030a080f070c0f0303020a03180503031914 77
    0x2000d580914180d905c18110310070040c1d11565621016104c401000c0e6040e804201c0c41c0300b0035400707040140089840078050b1460f01085449091500741942038860019548000b0840c16061a0f0081000d044151000d182141041d4545203114805a00407042c40303040c11001c0d6400d54001c000b1038104016070f140c0b14030145210801c640042166110f4540100841c8603038541c14100c1142010a0f02d41c001c26106001c69050102c01004400500400c01c3c80700281ca00707580b00c0801c003c106405c502c07a800540d680e192618250111b280182c0c084000e001903e00103110960386001680c0505603541080c0d0745855150811030003603d0241d02024080d4600390030300c2016040c0d000940c0c4110f0401d011911144e90b8042803503681c803000e00025040c55424000ca1585038038a90060105e00d000700601c0c1a15519203840382d0664849230300440144c0c0c80420301404240d0002020310156086003005604d846c0780102090b103d01c070b003004a0719050442030030341d0805405400004d81c0f640600c41b0081c0c03107 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 451560098 1250 451558848 451558853
    0x13020a0308220b160c09020d0207020f01091d040807060e0a2d020409020d14030a09090606080f0916060c0611090109230907050d051305061501110703 66
    0x40d4000b000140c0d0350000c841445003026520294403040f10a08501e2516103000c3c0b1001118000403114201c40c1c0c41c003040300004541c69540094049841c81361801a5501e000c0d10401c1240c0c1600c030802d43c140800078a00308019124140c25400e408100d02d002c2c481c560b15440c1c112064414a0f5005185030301d0815203040d02000003a038403054620414101c5d408400444c0410242244418010703403001510300c50800604090300180030307032403000c1c01403d810726040d41c555074041441c1803400c04d15400464822020341d482140f440060086200c1080b070740d401c2c07007801401003200800156101c4d86c0748010a24445003007103405201c0c070a4454440196844050062604003008020340d807642c20b0510301c24005007658126804484141c541c030840510346040f6110014a000c0d40c1c080d1079950b080820b44a4030b0b0307a08418400c907655520740e40d41c0d0b903039445020200d0314044d005501d52150f141d00a03000420020b8065008003141400c44071008001e030040310f81d03018400c0200708600a20100004 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 451561348 1250 451560098 451560113
    0x3010608090609010e100c030609020f0304021e060307050906070c060f11070b07140a050d080402040f02031311040b0d0606171204030803040c1d0103051903080103060513020a03 78
    0x540500c03030540310543c50b003031012400e0f81c20b90b0301480700a401c082080707803290240307500c00280c1d0b144ea4100421940e40d41c0c101d05003240c2100701000cae80c3c141c00000b000b08501e000b03100103020701c1c0c5038070094517021000000300e201400300038000e9090003400117841a0036640c001c03e549800b9404448181019190003006121b035603900015400b180c20074200e602460404240740c07040e00c0c20080c44905040341515a441c1c0314240700c80302e0b001801740403498404100188000d0312071003000c0e00c4601e06805c2510503c400c031142d818981030441d2050040c400151a101208044203030084042c0c2000e29404001900500d030070a40164000c4440034108204045500f0600c1161000c0c03211590b6849591003040d00c0d038a040443d00c10180c81000140001658200555000350048004003070181c3ca0740d4510000222501169884221004c01082000307010030a40503420300410421503040d48690b00a859200d06002c02808591200005180c043e44440403030551034004088403001a502d08203040c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 451562598 1250 451561348 451561351
    0x21905120a02040e0309033003160912030503060d020301061527050a03030f030b0607111e0d020f13020a050a1d09010e07031d07050a241209020603010608 68
    0x28010f80c10b10500c9100c2c0100401a0381c6240805405489a20001c021071100c25110b04041d01200c142100f50740e202118043c041c0d446014560700d03107210400035160140c0074501d950b001c201c0440a02c40c061000a90150644e0380018060b40c01c2000240036200082c094122a000240318921480c0316103051548180003511852802051420f14107040364403c8083d0790500be03498020300071000800001e48140d685c030540400500d0000740e50200781c00014003640c4541340503101c040004c0340c1c2e1451454590200340d540319072200c5a5a821100d11301090f0101d811a001901c20110301d122040c1907107594200e5000c1510042c001c5544500300100a00310342c0040030201d0011302d5081e155601c4003415501d41566103070082c10301065a10300300d01000c08210003170050003095286c8055107181034410441c091500039140c0540500c07800c05041c4a5541030903441104041c3c00d80320707450b9982d80f40100154146a5520708112060b950440340c00240001e000001c1d0031a800200000d001c036809003806 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 451563848 1250 451562598 451562603
    0x3050f0a02090f04030906080403031b12051006020c0609061909150f080402090901140c0301090e0102040f15210903030b031c030c020709140a0b010c0c03021905120a 73
    0xb01e9621401c0e0405002c403401c80700140031034105035051001c18001d2141e2944030303101e8070303003c5500800841030340c132010a1aa0fa00c1c021402800c280c1100ca02c4030302806500c0314100d580a5840e625000000f55561100c8540030300404002600c890680c4590007110645100c541c00c01c0c0c0005c04010703000f05419490b10a0a0002400b40800c480301845044101503050306541c2e902020745550b000c01c02c0c0520b001d86112040d40d0782d24090700100e030103150414400c40d403001d100d648940c03600b900d14090301d12080303a08142d40d00c1080140b0400c0c1c2180d51900954001c0034440b5024151441c040d01c0c41140c01c6c191880074200310003101809011a0803600c440da200355010700c088400750007851740e188455081c80001d003010b0311141181c00d21a503c8440582d40c03a104a540f02071392924100300321952204039180081d4080d04000c2600014020300070820004e182c200c4040c9007648401c0742411560100a200b411003420342c00002202500c45c0b4040c020041564203036405000c4195610f510040c404c = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 451565098 1250 451563848 451563859
    0x602010b0102061b030c0904090b22050619020903030412060c030603080d0c05040504020d0e0c0307120b06010302070828111002030c0c0d020d110d0f05031003050f0a02 74
    0x2192000e501c04984070b400313814250148030100c003100c8081182134000500000202509000866090b5194000c0c04ea800303003d40d0400105043c400b003411980b40340a41e000f40341c420408189130004100282c1642d02c400002260006480c00340140c2c00640304491960350300d40310219010621034240b070000d07180306220300810095136441031001e9064a459100c080d000c4401030080158020158000c020307509900d140445c501902d90000030121380040c0740c80c0807190b03904c210064640f40200710b424918101200108000d518041245ca4001c203083c000074009180c0f9004940720743d000e601900d14559000d00d0054440e80c02840002c820354246030704100108500c3c1c01c10b2a864003c000950a0701c004c8005080500949081c41e0701940c0041c00c980c64400f4100030710040e0030b1041c003030004411010fa0240040b0014201c1c010072005681c21540301a402081c1c542011540007107030b13880c440d099400d04546a03641c049078080030705055480905540101c0140d40b9180001040411007030b4800c03a030303 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 451566348 1250 451565098 451565111
    0x2041d101a010e0f0a09090c0b070809120f030a0503070806010309110103090206120a090b160207060c080d05010e070f020a02030c240a05031626060103020d15060201 73
    0x2190000d549180106000510544030903002070b501c142100c06101802a020107441941600801c0c100b001075440031142e65654205030302041180010a4000c040a043c03513070a00c0d84548441d001885851300441c4689009441c15076480820f2050fa038682e520f080c296a01e5000410014002d5841143d5044c0040c0e2420000303006980284540640a07401201244c0c1c41c64494005500406460900344c4e4468014000c02078408207001480384501c402100200383c4004600c0c1c50010407101501c2c034070315030850f40c03108203d50343d00103840c50440300c191070181c62039040e40c1400c0c0c01a100382c120043c0320a0070100003107070900011741d010340502d12907554100c0c0441c15203c1282c8404001d20000d506030440c091040e401c2ca07181201d40000000e0320940c00d080303800842c0c400b015510180894010030000310402542c0640700c0300c0103001100e14141840c0040c10561010780b085040c00e02d00e0114113070f0b00046103490340300354190341201111000412102030b00c159a640703a103100d4400e1800642c20001e = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 451567598 1250 451566348 451566373
    0x403050a0b092b031104080c011b2f1f1b020604172404020301110405090a0906020f0a0207050906030321060f0402041503050f070516080702041d 64
    0x40c09609059030150030019100110761200c2c81c0720f508201450070540c07140d111080c10a4114000e00c0201200401007030280040c100144c203a0398010036042407284006019008640d0b0703400e8010b116104441406050547c41902d0541c145140c0e00e500d80120307071101c0b10701c08512000403010b88481390340c5601408640e09040c28500e4641d200e0700a403c00e005000030000e42150307400e807154695030381094440c102100721020404100480e10383c408520400140000d5080030b21500704000d410038489482c1c142000c001c51803a0b1400307418040903541c2c4e40c1c42c980a01c81581e0541d6a0070704400313000c0f9902d4038500d074000e59030800c1c2d00500c2c1c440d1000801080041c58000100c4280d00e81d8956080307480e42d81107078034a0b91048001c2c02290020300009032114903a50300e10040016200345400c00a8800d16104010f04884004060040c012540014440540d0304481030301e40805040824034655602442c0c0400d550040c000020340041c24a0003034121540258803207084224500d044442400304003 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 451568848 1250 451567598 451567603
    0x303050c100c0203070b0a060503060705030a0e030307050a050d0b04050114040e06061c050f0313091d0309191823010e070e24030106030b060405060a0804050708030403050a0b09 78
    0x407509140540d1040051000050b0090301b0303141d002c10400f0380090300554440110342420001c4607010002807000041000e2155075120b80200880554002e505514015030007400c80d21486a103074040c0314012601c8005892240c02400041501900c107001c996541c0000303111452100c0031491049082000040401740c000651503c00c40e40241084589802013a082c50b030b45000100a5500e80181da040740d50781c4c0c20820040080810107444142e04901c0c2c00d00f0035049403141104242c0c800c0c5001640818002c002007558142a4200e0b40310b00000b840c41014000c29069038044c074038540c1c0021100901c16141d0b40140d220110300303c0c8101c01074081c548000322282090103040e110510110214074040c1c800d6810302800c0c14050a6610307441100300c01c194100192162600c1200f000000610146a05020b07045d0b80500585403c0d0a1a06010000e4002d0054081500c10000010002010721104000b40801051201c040c0c1e0741e11034407814096282e513580d41042d60b05c901c1c074601140003460b00 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 451570098 1250 451568848 451568861
    0x50d09090203040c0b030702030d0e0a120203160305090d06091203050c04030c14131811150d09050c090a020d060b0405060d0b1f0e10030605060711010314010303050c10 74
    0x3400c1360a0340750902c4100e425681004d440401188800d001415400820b072203550f5000481000415924120f0318000c41c041c03041107069011500180014502d9003c0500c81030411750341030901a0701c9081d40b40c0840c08864503088040d21460400030b130901841400762079614054a941d1b03080c0036507030781c41c560540107109a02c0024040c02c40100108000c0c1e403e040f03070b1a039809006119241e0034003403100748010745010404980b240d4105401c104100208202c801403802c0007614075036111909403629a1841c0958481010825140c03482c80b41004401c1c0310016040b030009208006030b007000c4606900a40084003886422460010081022882d013816503049901c01001d280c03501e0109820100504000310500f5007103285480e00a15010341ca02c03480441000941d2170816040c3c1d0f00040100840024480100745841d00d4001e0140780c8500c1d040380c0840782c00c04500420340c903002004030001d20f440443c02c125070305004004010960b010b0010141b40e1800c00440b0100e85400c0d4506045801 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 451571348 1250 451570098 451570103
    0x1a030a0c0e070813060f110403060c0e0909070915030b0403120506030312060d062027030c10050c0114011e0609050d050f06010b1b0d050405040225050d0909020304 72
    0x39215055400101c494001b8111500202c0d00425540f5401110724002e030440e030001c0f22000d84596030980503540c042d0041168000c11549042503082840d10561070b41114001d0004040e15008202c907040d10801035600207590024201d1614901814001c041070f0700c10107040051401d0501143c094900082503880700022000d65400d107446000810010380f01010b0100c801a88446013030741d03e5078803550003c1c070600054140c3c940d5485000340d1a1140016141ea241c1886400001e4004c162800241c01135941c0040c0c44200c60034140001c1590140038040340100300350700741420303069003000c0101214101e44068284040c50525220744500b0420300b40903210002d0040001000f191074500f041400c0c40e40214141d070300c1100313000421800c240c0b09803c0044950000034862104412801d484023410941401415070f02064420007841880389101d4140f107260003203040601158100d665610000000c19812000703600307854219110f0000e16405c03008106402c0b0700003444001070080303d10969 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 451572598 1250 451571348 451571371
    0x150402150306030a02130b03010c030608150403050f03040c03290613060e13020a1703030a090201030f05280e0c2103040b03010801050c0c060a1a030a0c0e0708 70
    0x10800505036a40760402807115074140f0070400c3c04805070300c0f542c240c0d10301e80d5070040000c140210001c003410b09481e1448845010075240000800061001060440303081e141007540c160b1544485c1070482da98040c02c8443d002c0150f000061004008092075000c085920510002c0400301c1d048242c08400f18602420445026540c0c00043d09403a003200100f400724423400c0c2c0001c0d400d46602c071855940b502103d00682c4942c0d00580c56080d8a4800010320013810b02914069150b0701850045449000145c221100a901c50b070072b0030210fa020383c01801d00c0580c0b1400811491512121049549880c0c40c05030300220080c100d00310500030a40905110f07032138001d000740f07091860001404110700d42401006e2091900560310052904280000d1009111483e0f41070b0b22135040c100050300b1100d000c1d181e4500d402003040348000118021605a60000b4001000a01841c000c0b810500f074140c01c0540b242d0601845045030200070b03100211105849844c009a10b0700c1d5101001651221010b0341c4200c9000c = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 451573848 1250 451572598 451572619
    0x20414090621070b0a020c1504030f0f0f0204090f14010c0e090a11040b070314070b040602090a030501050c0a0e1804082101090b030d090f170703080a030e150402 71
    0x11420b0300111038100b00040111003585540c4c01d0100031640018243c440107800c640d148038440c0c0360004d0b44807240c051105007540340a20b10742d076040e000c581a400c020050500306080c4000d0003410000a8541a0090401d0003244007500d40200c0ca80740f0208201da1905c0e907180001511541486800b207811100d4136801d03281e41c0071004000f820140205914409030316400101c0c5038640810140006003d804a00c41e2105031b03030b145c05820a00c5000364040c607081c060140c803010580c0c1002e42030300141c01c440e0040c0d540d0301460214809070b0b00c5400c0540190b0801040c0420805404000e11780440e07035a68004289058008000003c00550408140003400b9004200802c0328200100075002c1c2490081c074140c441202e109408000036801494010b035901d02941450505010910a500c46e03464800000c0d800d000c140c0105110303d00940c2c8003156108a03421040300c00300303d846d0146802050f41c2d5110314164034024040d100c04c100520311406810315084540c6070000c03c60340156402407250084 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 451575098 1250 451573848 451573879
    0x5090c011e030b0604090219140d0902030309041b1b15110c0604080d060816060806010908060108071a090904030530060316080c013e0f07062c130204140906 69
    0x20305032f1031030280e03407500042013000c40c1c036500c40c45151070325402085109203c82c0802e0000c0d01405c076600d640c1c014003000b03108000004480356028141c0181c0c0c600e002403402c2407075031710418901400c070110225106071001e02c0705001e00702000d4001c010f000c82040c0001038031207603030a8803040351510000500342c5180e02482854000d2405039030048062409040440d41d44054030b103061800e0380105a1908094018484005001d10880c0c3c030f84600c80360746103001c01c001e000c00c2c2005e000420150400001054087c2211050145440d054210401c400e061200390400310781600340c290f1320103110707100761a140c0004c50501c0060004841d0008054140c000001c0d00650b100d004000c444410507203240b998a00c074031088250420720001040403104804e14621410345410b0030707502d10410783e50140e00200200d9a010070304007441010b120b81100c0c0e09805400c0380ca20205150000d50f8840805170190a10328203c0e80580100c421a03004e8041c1c0a0000c0180044409d00343c80c8250082005401180d1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 451576348 1250 451575098 451575101
    0xf0a060e0a0b040e070303050a0f09030308060f01020f0f031c06050312031302061b012904020c03190c060513080313050703060e010f05090c011e030b0604090219140d 73
    0x30b1000001c1c00c041641c1550380d6005080c0051500100c01045001c103440060b142d000c103608030b1401c00340c284841c03012705644000c0c109100003040c1902c1100e540c00301d10001d074030a000c0707851130005203401c880158400d030800b02c3c0c0702c3e0441207034507010340c82d14040c400c550341c62401141d0403a88081c0161108080d1004030700e0311680020400783c4800a00c01180006842d614010040301c0c0015082c0704501da0420704880c2544c01c903014040c64940d4000c25035a03072004040100303604100480c2c0040c1ea070180b10010a0840c041c4d141c0c003191050444180d40c03c2036070804c0854500e24401c900401c030641d074003203650b01c00d00d00c0c40c82c01403c100014000a83d07035218404000d0f4240c1c1c06082159224be17a00c0d43c44405503444160700c40b40700d94542040e010a00791901035241c105e210030019246e031450342d00008060108241504480607034a4040070503050103a800b80e1207160015003e10396944d2941c1c5010060b5105010b0942d016080f0107000d409503210701120241462045d00310b40ca002000e018040 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 451577598 1250 451576348 451576361
    0xd030905010c030536040c0e010302070c051c05060a02030c03070e030f010c0509100207080a290103052119270306090506161e110102120f0a060e0a 65
    0x80500108111240210100400b410842175810182030040d0701c1c242180b40405a203403071900d0040b0f0410001250090700710050789001c400078600180c84808604207240a1803050388859004400c01060030282c1c0c41039605d034452203015800320b503081c5e02c61030611401c9100c221444d1014400c18000700e05681d105103d00324000d0001401c40c2c01148020009500311440d8480700300200e50005182000790800c81560035041000780083d00f00c5501d0503884544599442c1d0340104503c0c0c0309543c031040b90200b4a209a00001c001c942070034a980c41e858450760380c910108a41107850866644100a40e5100b8103c580c5440d10110340c0002042c81441030394003810110000f4944402803d6848030301c00040c2c0c10358021400390b4004240030310141403050400d900580b00070070440d4428084840f4a4100c5034251851803440c0814022461100d41100d15500308030600d41e4035400003480328000512a84198051900403600b041c10f83c40354010320f0125032851040021a240c000d0000d210401e0030360059 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 451578848 1250 451577598 451577603
    0x18060c02130e150a0c1103040905040614090a030813080d0c020c030a061406010f05040e0406090f0f050c01021c050903010902270f0c040504020c011407031a0d030905010c 75
    0x20580381c010554490070111210060480011120100a02c2c0081c1340501d05904c5e19034100302c0b15100c80705e400c090301c82c416806505211074503100424100241644000b2168100070b0f08100c0c2400c1c05803070103407900010401a0700007420707000440c000410740c01c0a2908981c0c007414203403401d4030964028011f010509910b8040d80601401d80d0b0280d1001c2c007ca6800601c40e1100203445001c901d00044410400307051581084401d50300d08c241260043c08407029500100c100c50f010341d0b40d03403401c60042c00c03640d600182700c1c0511201150410942c27540c1c80340f410b44100d0507111a01b0030304004a90380c41103d0907070aa0180381d800729181141c0038800400c4000340140021a00030301741d0700810314000c070841002d64440115004140c0c844107108402e6048541c0c000e01902c507007001344101c0e07290700031402614456540000e2001c5030b0082584200c0d884007058403c00c1c01ea21313000401500500074501002c1d00507400c80041025854100c204925080d40754407201c1030981403900440716400c424108 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 451580098 1250 451578848 451578851
    0x90c0609190e0c091e0a032d030305012903070c050a08040806070807090302010e0f0607020a0305060105040c08040c060809071220120a080f1b0a0318060c0213 70
    0x4034a801c0b40a1485104001c400700365541c5140000500070316000c10b0030b00011003911492241c603242d6403601c2c1c403c100c030b800c000544010f428078076488412120143e031402c014124008800c00701b51301038001504951a500340c4104a02051401220481c484115000e40d20707010800102031a0240c401d00c0c14650184040350324940d440d40e6860b4640e4001e422049031584050104800d03954058600d6a002810340f90240c5814510350010b494981c03500966481983d007406c003032506445c0c0b0b1003a41c1c1241d4004100d400300740c0e0340c3e007071054407140c00b802814020350074024180ca221380101c4a0a01a0f94019001c804d194913080c0100c5074014060b080020034040c2400000c4c0a800340030580400c180584520010f542e60005021880e0301c155005d01e000e91218041c892405002080c901c00c5141c01a00f0300350f8466001d88000c996115104142c10070005001610382480e80000f18409182c0c443d03110b11191050096903100c5907805072082d200010500120700c8018200842c034484254640d100 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 451581348 1250 451580098 451580149
    0x10120c0306020f090d0f060b0a030c030201030903050c010c0c03030e15060d061107080433081503070308090415080a170d020304030206070e0a0f06050c070308040e010608090c0609 79
    0x1803a4405d0400c016140c407800425454240655440344182c2c614040715604103591a42d591601c1800c00742c407000c0e0605641c1d400c50020f0600810440c2c420054681c003c00c4159124000900720b00f90b822000c0e40002c0c03921101a00d00c510001e56494000003400ca030440d01d40c2c83c5810061590008107040f00c8850f124610109036281c07040140291910481c04151200c7c10300200580c5a0781a000c000f509c100303015286806404e40000c00002c4081030724001c040e0380c1c0d842c446050740781145440f4680501c1501e900005002c46080500300705582120244000000d07001b007403c10707010500a0746da068021030080c1000030101c40a400440c00c03050281d50074200140c4c5000c080360011503047c2d0241e008103041085c000d074828820101400101e5407500d0690800d80c10036004142c0340a900241709001480030046a8100b14080086510022060b901c0f6141c20201007540700170310640c0003007000c010200d01c1220000c44e80014022002c0c0041d42095580c60800822000d11003004100d003500b0070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 451582598 1250 451581348 451581367
    0x7020a050a030f1e020906010f020c06030a0204030606080705060a210908030403081b04092307050a0f0f05070609060905060a0b120f2d01020d0510120c0306020f 71
    0x600305000394080e080b0f0b060491107a06100d10b8500600c1d0380003c0010443c0a0100140c0d11001c4143c5c1191b028a4002d13105200400305074030b8020342003510ba61000303000c01000f14100441c1c0041060f01d1240209000e403580d00c04805a0b100d610340502d9500036018000ea00c08a84120f851907090140e09409008203100f5210003c1100c01c480001c2d145118000100800c2c10340080006030020245c04072003070221120501846039000d01e0080c010301584502940c00501005403030801c54560641a072000c5007817034940913040d0760280145d5000718406603c40d48400d4020028444010001d0319a03e1a00e8140d5882e2002030080d00c0c01294030903601c10b01c0c00c02042e401c0000c0f45c8207007060000001c03404540f40030888103070305c4441c140c6403580c0200007036003c000004c40d0b540c2341182680c00707910b5500012070501101040502290203203602c0030807445102d9001d42c00550180e03003281d0720080c030242c850380c01c18120b004101c400340007004025000c100080c035590045c0101005081d500f8102540c11 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 451583848 1250 451582598 451582609
    0x40506131733040605060301060306050907051c0302060c1c0213090f0207050a0803090f0a21090303170c09040e031e04030c150e090f0f010b09060f07020a05 69
    0x1a60031525680c0030002e100b100e0041400303600c0354144140c0c4440e0361620311020030410000000c0c0010060368862001c030300240c030709400103006940d0001c018407032490b003c03503000d0b41c076240e034482c0c40d06c560080080c004489002008050708141c06030301070203a0342c0c0c0d207c4540104d60700440000d405030200c1a0400f803100030a1015104901080e456561403624041842055a0f40006180b008910410403440040c000240082a03513501800715912584d8414100303040c030240b4180c0f031415003d90441c503010420101c80300a041000b0010740c075407440510b00210341804203404001d003c0380c00b100c00340086004005510764030040c01c0460b14030300000b0b90042070070744110042030803041d40301040d84458813028107100b001400d1150b64941c1040c0c5592120400100c00b40305a0001d18180418004400d114001c14248000003810003221800c120108000541084880801035600d0000225160320b00c2d808681070020700a00e1681000306600005840307a10402d400c03640411410b00000740d60700c0d00c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 451585098 1250 451583848 451583879
    0x31617040b070605010918060504060b0402040b03010306180f03110c06041d0108010c05070215041203090303030f0606081b1b0105160807050a08090307062d1104050613 74
    0x205200586a800c1c528203d0103492040e04007101850604030300c41c0c2628128101c04d441c041d0898004251030302c0703a0515000909846c0300070b94000b40000b0380401c001501c82e00450481c1c1c030401c81000607030318215018841d5141c0701d400400704400500c00f40c000ca40300e51502c185001c081010355074407082e03540000e8100d44c015400b01c0c1d40c00030844d10110301007907103103090ba00429010740240050700d10144014850310801a0003442000300c071200e103042c0e50796182518041c000d5241508510029824003800c1c03110a88811400607041c05801c0d0444081c50181c00c3c00c8410b41c3e00c424003280c4502081d03602d0302540c2114526000001d02074494459000401c0340c00388481e20340000f0740da05040382003041002001c85043c0501c000c00003441142c960103801c4840070701b0185442091911244030b104d04511a08102030f2001e814140990000d004100c02c802e51103010320400c41c072036124692100283c40e420041d44501d80320034002080181002c0008145a10068000c1c0c44000e444a038040c022114 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 451586348 1250 451585098 451585109
    0xc050c06090705040c050705031e04030f1a07230a020c0406121407081f0e030a2c0609040e0115030305040e0a0b06030a151206090614060303161704 65
    0xa61410452400c003171045081440051801074a03110254481c503030b03a44121200c0701420905a1981d6038481961815603014640c0803e14140310b04490506040c1d4140891000082d00740d1500410841e0b4081e015138480c20488400d41c1001401c00c1011200c150404103800c42075001e15012103c3c7e0b40d44038890640649484910700e0310321001d5044c03104446074803039201031581e840040d06010198001680e424980c2c8840005c4c000c0782c82103e61038001d004002038500340c038400492030b84038140d0450a0319508032124414400c50b500280b018240842c0d841a034190000401c01001c0005e0500750084150441ca0000100c0c258080b00d0351420070000c664815400201c01003000e0004916032001e940d00302815070300074003018042e000010000d100250903c41c0382c0d81d88044107040da0003c032032514020a040001d050125041c0d00b000380c05007072114000c44909240500c80aa42c00c82040040e004403009002182419100c0d160300302080401c810a40d0081d1340408000c821a9520340100041e10 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 451587598 1250 451586348 451586353
    0x1103040b0f18010302090105030a0506061e0909091c0518030a03090830030601090306020a02070611010e06010620030403031d0d0510020a0306080604050106050a09110d0c050c0609 79
    0x190705898000b64820042c0700c64100340c01008010a960b80c00700659402040c3c040d0002469243c0b24001042846a00f800c2c1c2840b500b15a600407144100401a0552003000d40b1082a1036403a1240c5541b00c0d40c440b010220100d84012801c80c0891181c00a040c045404200401060080f90006071070004480000c8002541c0e00301d050100f83c0c0b0078010140801020342181c03285800c45a06000014540084055607685c040002940c0da0701c0344400c0001103030480b404541d601842c220080d20381c00c20340910000320b8007d003d0341040e20014807500014002c5030014240990900f9012140c6005001c02070416001e01c0078200d41c4d00c1d074140000d100652082c3c55034503800050008008141c0101e00c1c60318401c41c411181c0c807010900114100d0107400c00d10400507680c0c40c032440f0550007842c1ca900101c0c114400c00d0100420050154000415624104d0b14800099640c20349241513800c43d0400c210380030000d0000648d0441d075500a900d80c01c40d5401d1842c24a6080b05a00e0300d040d40403908048150b = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 451588848 1250 451587598 451587607
    0xa0b04090c15092108210f01051011071a040f080a03030e1c050f0c15040302011103130609020d06021303020f1e060304030c0b04030903060516020a031103040b0f 71
    0x1039030003d42000c001e1680081000d030f001010000251405004a0003a28a201c00201c0e00c1c05121a56545d5410840003408420103040130040303200d40c20009d01501303018030310403880c00f041103004e0701e00c003070805c803010000300710550510001c0d982568004591180c1c2600901011070402d541c000d046004d049000020300328102c2c1801c00400b5a50300d800c2c0e0b00315030380042581c40d02d84c83c500440708103118140e051080d69a03082e13541a6055120b4124026018010030002d40001845e80100900903802a402031011060821075000240302c150798400807991070442c058005243d58102001940c0002c0c0035954020503a103892080e68425020a60214075800041c411441c2c040d5103070b03806982c01c1e41c40e00000100111200c00020341d494155100e0702000c0001001c251080c001c04c05c240d540702d0074144007400c081ca03015103507038101c0c001100d80500b0000047c408000f1070341e00e08400c0d101680104110040d5032000d80322003145840f242d8013400100030205403001c2c00b81c01001d00c04081d0110a1ba034 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 451590098 1250 451588848 451588889
    0x102109230309010e10050901140d02120103170307080f06150309100c030605031905010f0e03130503010b060a081b0a051c0203010b03180102250b0f06090a0b04090c 72
    0x6a2440d1120240b25141c0502c1250f2095070220584800710f100b8203102c14035a007e1202e1001c07074018ad0f0842440325000184a90206846a80d450704991003044890302e0901000d10012007408207c414030001403110b8001541c034104036914030741041000c2c00c1d0210b45012901c2190040e0700489006456078800100f640001c1d80620500c0c51020b42403400708525400c2c080000c0d00e44400035128145d41d03500700d80d4001448002e50110501c851241d104100d4100d4281c281c0f51a90042c0c030311002c120000400001d040d09041c082c1c3c860b8008010407562030140b9100c0d0039600c124019050f00501c0034240303490080303071035004028440c060700c1c1d071201c03620780380014210303034100d001c030490340314094010300040211806000941c1c0d0007900c00390100504d08451000e6030300900400191074403410010410034100340311a0460302d4910300030807503c0043d40e039840940b01202c1c01608c07030a0b0402c2d8004006001c0601d51303403120842c2030380140701048048007030300c8010b069034241e00410024a10386450912 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 451591348 1250 451590098 451590107
    0xc070b04121e15050f060409240f050f071808100518011103092811220501090c080402011205130503071a0f0c04030807290610210923030901 62
    0x1480b400c107d0301800071a009170380d08614241c000c00c0c00006078215001000700e0240682200400140c2204100039600d4100701d642c4648609503140300128100000e480b0600c08810203580a80c0c2460000700082500c03904854001e14004152203a900c58100003503240781400e0050b0705e01d64005242c0280c603400d04c00040d03410485196000450000c410900c80c0b030005501c4d901d00c88680d0030441c601c800178103030408961810419440040b8105004040520000c041c1e4031060507180c05c8907013048105100c810580e02404151006808649900001d00e80e4180c04c0d00070941c08800d4107070500003100207a8a951850b0003d010403a13202d400025000340304020400d1441e0720208507a000081030034140d410980e107118502000e0501c64000800c9801d01442603445ca5910422000400c1082600303e9504400d1005680081c4100c0004055012180c0f24181c6015541184035003881c490708001f5514000b003d000008460b10b000e08464446038825031038032810500f1084010719074551070301c3c00050 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 451592598 1250 451591348 451591351
    0x7051e0c010f0c1101140309010606030c0807021b041104030f110904151a06040b070303140106140714060f040c050a0e041104090602040b0c070b04121e15050f 70
    0x5041001944001e01c0d2594011480300c3e0403031308459100c0e20219002c004030340300800b0003079600e9015000002d100c5415815448081101c0c40c03a80c04003d009003d00f01100c1448080e906000181c1c0400308140000707194100c120201c002c02000094a00b041710300042940e000b031350040d40c6003e03aa00e4031805101c0842c10011102c3c1c0115884401490316668001d0000c503612410b88046548007680c5810202c0060803a0521000800071610341c0d0b41c038040c1d41c2581e031020404500090504030701c0b2220442c060300a6050714015102d00c41c0c0c0c0d0f000d00b050b00f0026041130f0000d650b169649003000180300810300c10700c3e024601c801d10000c040d00d41030400d8100040c0a0b80050701600c0c950a080094031107031401c49030455403107d0f200c4140c001035000180604444900075192510005002414482e50710040c80d2400300ea10640c1c20b1a940d070410361441d40520300c10690103098480c00180028041c40000e42101d19420300d2101e141102c1e25161814071355194000c200554071b07030a01034842980455036 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 451593848 1250 451592598 451592623
    0xf0e120c0916021911041a0102010e0d0921080a0905120703021503131403040f0905150103110d0f0603060f051e0601140c030405120f06070e040207051e 67
    0x700c0250708100302c025035a01c2d0064583d060700e01c071800c180e02046074410004240d07090081051041c058143c076100c68026480e21614095841d16030070482120020445d04600c0e5960389520011900d080250f41034164006080c0c1102480c3e0b2881d40001400c10000c1c0c000181550386029010341000244540c800120b01030801c160301c0031604100580d500e00c2c036403010b010040c440307517203030b840310300d2404586040d04000522381c1005002c00d10941d1800405001200c90720540501c0040e40c90700314408032041903c00e04500303590507030706240ea94040c1e0003c0742c442c442014410702e8603503608181c80c211261003d14020781b0f40c46801c104188076260041080e50f22408408100c0790502d01014030014120a0f0341c0a003007565032000510b168080c54075260011000701841d42d581e4041880d8030b072290b0280c0a03c034400e20400f14404a40c3c5030004090400e0200c95000300f0040d118000c00742c0d40028400000ba5002e03401308030400000d20b05014018002640c5200d00802c1800d441101c0d0071b01c100340107034 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 451595098 1250 451593848 451593871
    0xb06070804090b12060702010b1c0305070807050c0604090903030f020a12051b0f0702190b12130c0e101e091a182d070f0e120c09 57
    0x680041512181180c04490030b49000090f00e00004000c02d400400d407628001141c041c072410032601940640221000000844d124000d43c1da1004811040f000c1984000e000100140407400000701e80b4801444800d0241c400c490707443c446000052990741c0941c104c048001e4640e0307554810141c260240e04c0010280d03140641c2000102030303004110302c50380b43c4050540790b2281d010a511410401418001903500d031102c5a55031a141059030b4190b115030310490003054100c160000000100455805440048203040d00d40000e83c0485070803944040c00076050398081000da140090b60084c443e4009000c501d001080900d001800007070300d200d031540302030004080d403000c40380340306100f0b42c826060300d00690000604004070410701c1c0008104804668001101c2c034182040700c80150305280c810000380310035549580400b900c411000500c917451a021509a0011500d21070007003c0c2130a4444803407524100000780300380025030b005034500c4108966042828040340074200b6601181c1c0c0960220030 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 451596348 1250 451595098 451595107
    0x5160206070503060f06130803040902130b0309060705070c050d0c080c040c090603020703120203040803010f0909021e0102030c07030b22020906060f1306050a0e0904021e0301020d06090504020102010b06 89
    0x4100d400035200142845481c6c002600800c1e0009040d10078080c01800045907107803070301c501164000b58048070643c0c0b08800c10000010300e4100070000c072441801c01e540581090f89983c2029035494101010880f0302e600d20720b1000c5001d40384c00d103c03640001e0140118403507c901e0456542c1c00c100040e031015001d641410605880380341c0200c0104c013161850b140040ea20841814221440070880421032212800003051005000fa00c070091170681e1110a04c81c01d9407a95000344008460090a000b0b400842c3c00014422111900301c01600c01881801603a00e0714868009040c14040290022503049003018144110041101542d00d501c401742650950000125000140090b0009000c0c9202e41c400180c05105810b8040a0340d016005070f400101310640c6981003c1c00325001f150104d00055002d40c0300001a24010840e60b000b01d40140407503044842400b114440c00e00f0a901c40740e010364003006004082002c51160b5002010b8068000406042034070009080d81e03207174004184166014070 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 451597598 1250 451596348 451596361
    0x5120901090b042301060b07120c0309050904060204031208040611120c130f080a0219051c05011d010b130510060e180109021206090c0d0e070905160206070503 70
    0x314007070700250024800100c50042130007420494201c04150707080e81d400d20400060000341200600300346841900d004c0da42518640f0211801b80d007510002c0c0028140d41020030103401c144e103109030801e01406016283c2078403a1580c0d90700c0390602e9a480d000a02c0d20741000b080c02420301c510351007960308030707005403809140b90b407182c1d003840014280a02c1042d0001d5004140a003d500d0a00100342c85142c01d074140e95070f0181151100f840f2841a80949201c962a44d0080000d0981ca01075660090412040c0c107075825405402c02c003072603002c8038150350750700120021481c00201130040c0301c003000001c5811031030001400481c101100044c0a0701d41041c0a000585a107484035609a922914042d200a0000e000007011a004c078800c50b040704044074004204000ca40c2c004003182c1000c00c20802e101d49920081c0442c3c41c1088642c100d201c90280000081b0f4802038000c468556074031800c940e1203980320444182201d10603a22920703580c00049800981c00e070144042a40983e240c01e2041c110b15019 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 451598848 1250 451597598 451597613
    0x90d1709090105031f1a210c10050d050403200706030e0321040c0b040b041e030213020d060305010c0c0b07020c0f120a05070605181504060c15020a0512090109 70
    0x641c490040e0549404604841b00c111140ca04486400104001c4d10354004460645200c018010701c00d02038000c005183e60141803c4c0300d40c01e410101541d072903250081c40001840240b40c045d10450800c0500c10104003807181103146001c9207040320019141c03a91074000c024003120394400c4140704540090000051a12034079050071031200355007600c8517050b03503145000c074506480c0e40c00001ca26480801c0208a0301c41503009082510b072426009200e042807030081030802d40591000941c09010038113082d42800054018140480e81d00d1804600035841e980c5070f41c02d440001e2540307000a20317201100d80c18028a40d9050390000c0180c00505496024400813030240301402403902d0150150180000c2ca03ca01005031190709600300c1c00b500c8466880b110020a00da004118a01c01000e021650000c42e1508100f02d04030b032031520075280e00d8a4a0008185c921540002066885d0400b200c0140300c4025140000c080742c0801d40d5502d030380c84400c88142001d040c0017070640c076002c2c4e26050b6034000140b8031 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 451600098 1250 451598848 451598893
    0x30628090e0f280503040314010506120f1b01091701090201080c0c0a120c05060403090510181509080d0f03060f030515150301180606140d08090d170909010503 70
    0x1d0707458100c9405144c10b1443c40c6210307950006040b10701040703041600c1401940f04034002c140468031011038030071080b0405d948041d405200030791a08104180000b0320140140c0102d61070b8181869120b06a0311140d40b810500f40b01c444901c80c3e51500050402c540c1e201e5112035100c1c01d400c0025041040d5404e07100d2703a40509140041144c02d000c0650a08103000c2c2c01c903880d805a206044490a25152400900d500040d21519015808842208510a00410901600c0001120451052454100910039864280e0b40742c01c14031034042e00119070f1171824000e448034600503882ea039940925041c002170031281c19600007082d610b000740013070002540101d10042c3c40790000c1880c0c0c40c0c545850702140f0196107204102c507815860024903440c00030302040d001030264020582044200d9480d0303038680c3c00c1ca40c810381c03413548800e10060f0203000408400207401000e2026105080c082d24564440c0c1d030174040000900140f6034007150030082d0703240c04410180941000e4002e02000c55201403150410440b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 451601348 1250 451600098 451600153
    0x20307030f0903151d0118110f0402030c120105031902040c090902041502010e1507110709111c0905030a11010b030307060903170606030628090e0f 65
    0x40610200c24114412150710010710b030401c004030203c042180078040101400301801701c1550500c0c0260082c02e406100d4030050319450b0001c103c01041d00c1d03990060610503200745076840400c82d940c0c441c60344c540c3e2000d9840380d0007440500c0e548003400a500c0000c410140c1c0410700c41e92101030814001030781580e00c0c00384158103403000715140c484ea15064480703d40a03001060b40c14408030300010201142a0442442d8146030020028000302c4003100c0d84074105030030070101c3c480c0503002060410344580719425254460b6419607032555100c01110742074418100c80418500340109001c80e00c100e41c6144500d031220300110401c8000810381c0c130103480740240d03041501440410580b01d104101b007900600100b90740141070300c5d0344220510301540145400181a400550305c9201c01c002d404011010502030640103100d0340c00c65680310204883c07450040c50030b140e11409144607034020621840110094082c02601049141d280e509040c03410074050144400ea9000303007143e40b50880a8940c4034884030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 451602598 1250 451601348 451601357
    0x9030602090d1a060118031106091c0b0105090a0207030f0e0f0315040611030f0a02070c0518040b0c0f0708130e0103140c0103050606030a0e011506020604060c0f02030703 75
    0x14200e2000030200700907800003402072403502ca04008003042c2c00c0c440501c251340c2602c8401a43c1035915031148507051500006001503441160302805d0310380000039000f0407000600d01c601102100b6140b54212164190403640b4068900040c48103140c03031611035030720001d0030304c007182031120a440042c49496003041400c20f0100981c6a03003115202c00075641a80c220240c1126139001c2c500c0a06810501c0c11201610b28926100c02c580e0414501804c4074011104034860606548444a0404c0254040c0c40c1c121018030340013100080d161941c10b0356071038507180100c0e40b005500d00346c101107850b200c00419070012044104a01200d041d00002511521504016800d03241c824103142140000c60a0300100616a05180000100712800354400c401c101c3e0b40c002e680302420b0010064090f00c3c0240c0350b083e8405e50500005002d00c8595011b000001c04240000c09c440303805c03d2441d074404482d5044100141c1240d4208000e1002600408000741c40394981511306000c01d540c020b440b405207180060402 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 451603848 1250 451602598 451602607
    0x30411010905030f1605060c030a0318060504120206060f180c07140318030601050a0e040c0e181c020706080702120409090510062601020c0d030b01110d09030602 71
    0x5074072500d07400001d4003026049400041400c214999280c54049104411640c220380c00304445c10b1100546d0100c2e4006001181407604050040c0e000d400c400c806103295440100c0e10780c01040c00f81c0074240c0031314010000384241130300c07540d0000c0c24401d00030141c0303000b0781441e14a440785440341c600d1051107103281c4010002d15160034805944c24802e400002d0f04503482d0792101e0004000110050420f0040a07280c82007050281092645840d800d201c1d13a0750003c00a40100005081c0341900c56019204d2240380c3e40490301c4412056026500356600700e41c891001d0700140204030100282943d075040c01c8a501598000c1510003952a00769020b000d0410004d00c0100750594000c1215244800f202c94804c0d0300c0380c1c1c5031042d4200400d0020b105a51920403460b0700c40c2c502c400c40c070400098070fa9540808551140718a0601d240d0000d007640242c00359420440001f0a42c420301541280b00441e82c0d000c6640700c0f40301d00040c42011100000c3c929034002e0314180503002e81058000c2e007281d0340028007503140d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 451605098 1250 451603848 451603883
    0x4060c02060d050702011b03050c030604020a021f06050a09060b030c0a170f040b010b0a0c1209090213031b150804032d141c020f0417030720060304 65
    0x50301a0708000d040c003e0800d8180440103406400c500d9800030946940485400c40c0d5200310140e030003d50f00b54072100410008103880e41400d07001003441440c40e004441040405900c041101920040c1281d41c2c04e40c5c1d510240014500302e0125401040d04000621003503040140d03100d1284006010f441c800c080004032482054000d0389209065140460075013030501d0401c00d0108046000c55088031239440500000c0380c07210300c1e20300381d40707000401e691003041808080d83c45000d10b00c0b40103403410074080d060500140100303890005140c0310f0302d40400115181e1461a0040c14044228101041c0303100e00780e8280b2101d40310758114840c400720b0f8070f08a030003600c40341006d50740121103e034080d6109020800c01c4a1002a240080820b00b07916a10721035070b010700f9240b0b0891030140b0380100f00c03601c140c11400f080503c2c442c4c01400030b2042004416140c2a5562048000146441001030b05a0000302d404c81c20300c260f1110302c24041c06601d4007000151100030014009210042c0010b050740da210385507510 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 451606348 1250 451605098 451605109
    0x20a02010e0420040e0103060c0906020d20010c05070611120a092f0307050108150111030c0601240507030801050d0f020910030606080705060a050331150504020604060c02 75
    0x51100746103104a5036130b621780b1403100804009010681c1c2d0142040b100c0400c079032007881c0003000c484c400e9001c1c000040385807500b254504556418500741d55400c1e440c4070700041c07081c4039243c0c544800c0d484060342c0c4c0c0e030145046001c1c1e07036985019142d034010030300080c026680d03129000340d07000d0b51007a00000c2013010742c50700f68000090002c3c44441c2031590301d490a58000303102c43c1110901802c030221a0001d40d201d00454103000e003221800074282510a03032581650050700d02e030981ca02000c003603a0510810032001071400c10241e11005030461070740c000c010602141c4858440156945c6000382c500a21500c0c098146001881894054032404412000b0700180140c050700c0c40340c1c01800e5800504002c44840320b4190503010541c3da42d890000001417903080054410304880d8082c2c0b07564213001c0840d20968442c0c100a280031444552070400c0ca040c60305503540e006000095000c0c0e020061414144426203220440703030f40512030f1030724091001590b140000d03a41101c2091420180050491011a0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 451607598 1250 451606348 451606391
    0x2316051f110a050105240906011407050c040e06180d0c11040209040c09170c0d060207030908030301080706120b0102070306020a2d08060d0305090d08161a07020a02010e04 75
    0x34100c0d4600b03024007039514440c01601c2e0001b0080154a80b035901c11008109404e84155020b0717021602010081000c0c001440c00345c0400c07030050b41910b928480c6000071070150b40da10104150950040000c11441211794105204800000d00007010ec14600410281c85003100d6076014003030500700358241515940c2e41d0100c4d40c3d0004060010321100044000180503261079000700a00806030018146c60014002400e060400004214481d03525464031071600a5020143c1075003041100d00010179054401c100841c0208115002840214a0310500403c841902c0b06040b2055091104082e40c5a90008012040e25008400165607001c2c100007074440418901400b00540f041c0c03402c52940a020006000032440b040d1190308296a4810030001200900c00380240410320030302409040e410142c01200c0c2d8280f00c0c00746940b815204480b250003014400d403084614900900c0c010100c41c0c0700e0034120340c1050507030005291130246a8000b07490f800c00014254040e90b074550380f83c0d03c0c0010ba054181c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 451608848 1250 451607598 451607603
    0x5070c051513140c0f180c07020a030c06210e100c0207050301060303030b120312160207120807030e060c15060a12120311030f0604092316051f110a 65
    0x40c4009900c032002c0e03a4030343d0b900c0340746a4420b10080c4c1c100300c4141803010902840e06d00301000419140d076020010700c116040a913080e600004e01ca140880043c0300c030402c4802610051f100c0c00301a00c1c2074507807401c0c0010804030201c2d646050450b0560320103000a2651a0440000c001050b4032a00e0701040303150181c664001c1d541036007012350001c1490f17016403100640f02000d9032400c5548808024403a80c034443d100042c4803003d480e1001484401b200038250300c0c000b0551054416440c3d4071203426402140c00301d000d545046000a00c5001c040d04000741c00706003a402e6030722604100d41d04040c84d4032030959083c9684400c02c0341e00003511030b81e600c040c1040504010110341c030500065041030b0079003003504117003000883c0c58004d03030341601880720741038a00c1008858002d010568481040c030001e841d1424085030240301c85070651240c8450003036100d404480070001840141c20352008051202ea4070f40c801d50003942090040a4258403040321464510f8581c108000034804540e402443d005800300302 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 451610098 1250 451608848 451608863
    0x1c0b030f1902040f11090d0303110a0e09060a051507210908070f050a03020d08070c08010b0103060b0f09010c0c0806010305150603010b1e0d080c0303090105070c051513 74
    0x210310301d40002610441e4260003503504210a003403104203038040f00d511400403443d4030824040001d282c54402e0540032014400d1601040c80e003c4c80320b050125401102c44500030403a001c2045619040050140381d100d030044610700c99943c604004036003083d801e44074001481200089135014015181520384140055a01c0e04450103c2081c00070306e064990300926100340140800000c562010054010030348070020000c1c0700031440c1d5801c002d414110801d086078042d20501180703010680320903070240102261000420b164070020001000c0b65103940064100440c03e1009600018607e070599514840a013481140f20b5402d060200704d0000c140d010740103511800001004002e000703c0c40e10042d04200e504040c0c0c503200c801c105820f03078501f444241d03008000c7c0d6130010149524032a4110b070b00e02020f0528007101d00329480300c902a03070100c0e2070720456900000038080e030040c0902c201580045036107844113034091319036107580d01c2d442c03c1000543d900602c0400f040b03514540200807020b103640034a4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 451611348 1250 451610098 451610113
    0x105060a0b03103f030f03150e040c1401030204030803130206070203030a05040801060f06020d030b04020c010f0608070b0906120a0b090108010b030601060305270a050708060117031c0b030f 83
    0x2c503104111010400c0f0f013040f40024900c81d40c201c0420116185207907058031800c003610b42e41241140105080b0090304000e580300400042c0210100c900d46000340d001380c0c10840080e0402120b1954040303410354a60415104100810120b4020000e4035013042c0300305000201c8408a00000c0d00c940a544006135050100245030b01c0d000350040001c004894181000340103283d669954908101c119104250141e04014080c448851083c2d0140700c60f08401800142003e4410340d903d400c640c00b030006100b0b110f0750341d03005101c85030b0204401c030014240c2c00e4841d403406c818640401c01c94050f032031440e4104148140444c4c9074071101d80100d501c480c006003800c00ca03980c0d1004d0790340c064008003a02c03078001d000c1c1900201d0b44078400d0140b148192084107030300c22a0500540c0000c42c031000310070880e805000c4c0502500000b00203000860040080c60002d05040d4100075408940401050040d80b169000300942180da0158000e80e101852991070b001a60b524001d02003418422401481c503d107000f64031 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 451612598 1250 451611348 451611389
    0x19020409080a0c052e020901030e0601080d0e090103050a0b09070b0f0403110d120e010e09070e010210021e0a0c0609051b0117060d080d1b030e0105060a0b0310 70
    0x1d542c0014a0090044440c0750303511940b003000680c041d844003518a8640d007817070f410968054008110703c080614000034000f81603241141000e03020f0f085041550440034011a800350303c180d184400d078400710b65024545d495591081e648aa00080023042c07005400700203030349a4400c0c0310410080c0001c0d8505a81c4401c4031720180c009900c9804119103004090360317408010705000c0c0442c1440b41e80300d16291110b40005000391005001c2c2c510050410610744021202910b400c41110b005100503111540e5000405002908015500f2701114235a4418803590087d910030121803d200c00e2402c0a8640d101100c6008544240c814000900f4142c02e158150b420442d0004c0c42040f04190181542800c54000c40116900704500082d104605c1d00180820b10300d24100c4001401036100b820481d00c1c3c043c15070980070543e000d100c110f0f500e8010501004405542600036181d104183d40c00800541ca80800041c50105890044c0c401d9520080000b07403d00c0525148480038003000311080c2100340100 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 451613848 1250 451612598 451612607
    0x120f08040b0a022404020a030b06040612140d050f0717090402120106030606050408071503020c06090f150c03131b08280503032d04050f0607050c19020409080a 70
    0x2001c01e4000c1d070308410781a45009500c138441a014541c0245800e40503491901c5911030444050812076015540f00300006001281c940c1042c64280302d4004052645103000150b82041060803441090100801002007150f07400400c444406510140140c0d04000e00c240042c00c50060200113030b0080c3c40020b104400c074552500f44c50480d88140e074180b00403030f2a18000c5606005a00c40d4025a9122020900c4203110128500000000c1032400600780b042084605103880c805480441d01e9400c800c620b100d8030901841084515610030303002c8591401c1c14280082c0600c00240a144080492002c280401108003203484c2ca1094000402c0c811b00d4a6103440754861200310411485012803520f090381d00c0e10312202c0100403135040b41c0074608580e11380714104c845c1181139220007100303625518403445a44450107200c0c0564080d800510030015030b103a44514050340a0419400d108090080162b1404005440c10400b0310402040c82e0b0403280b031010602070100c0030750040050102080900c002c5030700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 451615098 1250 451613848 451613863
    0x705031c1e031a030111040e0c13030b010e0c0307080a0b03150c120604090201021f0204031e0506070e0a060e1503090307030f05130626070f020c040501120f08040b0a02 74
    0x10030151000c00383c0b2a9081500300c404c1840510610742080c0420040c12060141481c0d02c0070034000081c0c500641181c49002c500820782048444001302c0c0010700903000c1e070702ca641e2350190088071101d1960034000005044050005c0007540f5098a88128000d0b07514188450b0140c0403502220021905090b16030f120560005d4030074041c0802d1600000304140b4160140b80051a01030b00540031082c807011010b0b2030940b400081058060702040300000045010102c2c4512005141401d00510134520301142003080c00b600490801c13102c170320110703803070740d035015a4a08840c0e403401c25450f520609004101d458044487c103140c2e140e070200400118400100c01061158800d90340d00e140e101001c10256854040c00030680404855403a051202900903420343e600d1800b48450180307410400c80301c080b680a01202d41c1c00008104c40e0341402c4454040158a41030001141d007404150b0505280c43c49100c2d8003140502080d4010f07008030305000180c0304550192a000d9815599191100c2c03001e03503107403403 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 451616348 1250 451615098 451615121
    0x20907020a1b1a030f0a0b1c0510050112150c0c150605032506030504032a1b080c040b0406031a0610050a1b0201021002040303031d0705031c1e03 64
    0x49034020b031804400003401c60303100d643c044451550035115185030800400303450711f1450b002441481c646a4101450341002c031858450802020f282d139041030b070300d02550010391000c00603260960f040720018031045096001005e800358000b032302c020f500004407101e41e041c41020b0030b09115030500711074000080c0c0054040d100103800321014000c203261194074201560001e06408861500305001c2a03101c0d4200540143c000d20704405050750b4003442c180c0a8101c815042c00359000170300c2c940c1c1084008420507070031001c51100300e210303d031600c3d804c00e0b2a42408201d0700c2c4030b1036840f105403502c0e0ba02c95020034055a000024000224141e070302c0305021f0003069956501c034403c00e10002d02014490030842c2c1c2d54500c0c0355500001c4a460f8800b824440b50070000407419802488028014840740b44081c0000f94000e40c9c02054440080085c2110f0420302c0428013482e401201042c0320340e403000034001001080c1000036080d03803401c2103012105406015103038004105d10010700b542003036041e0000c910000c0f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 451617598 1250 451616348 451616369
    0x2180409082a121309051308030f060a05031f020d110304080414040b0d030f02120d0c18260c06070b0f131e05010b190f080a0f020907020a1b 62
    0x6540000b0302680c025004007071003240c1084d0007030000304003540120380c104403aa960340a52032003940d1000403e4108072803420390042c030003003004103a2a044034010014041540901404580098083c04040c41c0074016038139160009054100c02c0f0040d40480034960001c2c002940b039013000d1070560042ea0241c8900003642c000e112000905240174425480780d0940140003180525413581c1c25104281800d1520056010340c02c000315840c0c254600400d890480c0910008100040c0780000d8031001072900584440310328090144503c6441000901781e402d54001d141e450320880e03c0000303181c01154088284c1000d40410600c0403c01d00004c841c0c018007262952820b5a40c81c0703d4642c4440c1091080941a1800300c05583c084640061003028058040c00021820301d1008001c60381c00030325201900003044140c0d000700700f03440000400d90f010b050040c02a24007910540c445103c0c00301c580d10040e100c0c155060116001034001c01c00740f20bc49a200075013a203560a1500ca03015110220700c10211283c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 451618705 1107 451617598 451617613
    0x3150f0105130b12072c0601081009060608011a0c0a0b0901290405091f020f040302040f0e01050105040b090a09031110060f060302180409082a 63
    0x204881500030505a41350186286c807501c0142801e00b50310411444c00c10b54840310f48041070300001c3c2482d25002c1a1526125000c1103c0142c2c07001607044d00d4840c1c0085c410740c001c00354031304030b82c01000035510030305101c41c10010901c03c11100000e150004005a000102c800b080e1542020380d5000001d021801181d20031142c1c1d40301080415801c0403a03508151510f040c7c0142039119445401414a00d070b6200361060802400e5a440d0700340580200c0d804280301c1c04c803016640290f8005105110f10b4880040c004005d014100003450b01e9424040040380c00c2c249802288048540602900410340c2c1d007440110081015080c121b0810011045002c5205400c01a0101c001c80d802800180703940f80c000d00003c0285607900c1941414018400d0300708082081e40c0c01d4054a205075000700e40b48400f4948100148901e0104039416110300360518144500450700700300240c0a0fa0445886 = true := by decide +kernel

theorem cover : BRFrame.Cov 451438848 451618705 := by
  have h0 := BRFrame.cov_init 451438848
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 451438848 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 451438848 ≤ n) (h2 : n < 451618705) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
