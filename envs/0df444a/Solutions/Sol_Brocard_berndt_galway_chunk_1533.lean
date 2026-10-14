-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1533
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T03:26:35.325948+00:00
-- url     : https://prove2.me/submissions/ffd38e0b-82a8-4c8a-8cf7-48fc478584e6

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 275539568 ≤ n < 275719424 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 275540818 1250 275539568 275539573
    0x6031e1014040b0f18010207200a060e04050606090a0e0105030c10081810020408060a060807030c0b0c010f060b0702180601020a03120b0901081c050a0e0405180f 71
    0x3080c0e40c05452281840182403154103080c01c2c0381c1a920f10703c1d0080010901c24040002d035000c070f40751014241e944500089500001c650780c525038100400d0b01003c040c1020403890362054007813400d04005503210102c0d455a1240c855203c046030811020381030003400c0b66007110f000e00040c0800d541c0d4843c584c00520340c02c10399001c1c0c0c0d4100030074107013043d440303d0f91a4061425484130603a2598003402c6140e00200700d0070440c1901030840f008030f003400000c1d2500e000643c00858081614400801c0c22030045000b07800810400d07540e100f101d6104c20541c80007130036000c2c0019080180d90403200040224854010001650032000144201229400c0e0403119a5030300c0828a10110300b020140307008990f500640502882c60303e840000e50f1803400420041c104001c14426400b4040680c000d00100304c002041d4581568480c251156a0300c00500481c500340700d8108030b80d064a00400495010707488640d240c03040034100c1000d2201074480070f49081c0d00020011403140c141382090110341c4410b03105001 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 275542068 1250 275540818 275540833
    0xc06050a0305010f2411101e09050309010f0504030203061003020f2d0109030b0403080f07080c07081803060a0204090b0306270f0307030f0f0f1706031e 67
    0x1009040b1241600a80d08943c00850241312014171044c10074640002c0509514035402d09010440d0f0400000703c80c0501c5101e80c0001003415041d43e00001150200304403818000c5900c141e400090b221403980280180d0420001000c0030752162004078400c00d031506215141680d82d5005c40d281c030340111030300c24580c1c999603000e0045140120030220f403260225029400c4494141c101e20f01040d2240301054a0a080703c01c0043d6a401000780c640159000201441c0368070f828100627044039403c03a407000c6c04c0c1c4003581c0044e0a0600440099015000410440d8140110b0b43d90ba403ca9501451424040858240070400c0300d07601003103403074402c00941c030016858501e4058014140e40359099050721076009241044017118240c00400b2040c20102e030046448064000c41030308000c1007841910301808006a80c0b428190041040c0c292401d640d5581d004440b041901214520b20369412100000c000b00724945403003001c0c00701ca50308410010150341a2680c002840240d405c038005200d40182c01144 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 275543318 1250 275542068 275542087
    0x11509080d1706042009010917010c0807080103050d050d0e010203070e0109060203122a03070305150f030d0f02070b0c100b0102070b030f0c0702060f13082a06070c0605 74
    0x80c042500030206031070910005d90a6000340c07085481284542c0181c0b11701040c0180c07541e03c503125100003404059444441801d10708112070291030921030440c003052003600840c0d903040c42803480a048030740001c040d0060260b1450b08031a40c1e84540c041710700b0703251a02100c05482c203082c40110300071341c4562101d01200602000140034415a03070300a806541060001c44040f030444030030301e6801040840c00b41c07960140070707500001c1c1080d0f80f5084030910501100700202641c06a103c0d9000d442e401c0c802e21260081c0c8020004c204041c04c2d00642c01d50005050100f2310ba0007081c8000d5032084a0040e20100780d100c1d000d100c4140c01034800c04d003503075110100010017a621803141c000c0c040c030280301808407241070050382046d604c8058441d908010568000a4015811a081c1d440499006110581e80c541301010a80c2c0c580188a4100041050320f03000500d02d02e002800c2d20a40c1c1076803481403a1000700c0c1c1e18002591052480c05d0350440d20802c0504001100b01007003501030540341d10b0f51a11805600d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 275544568 1250 275543318 275543357
    0x10506030706081506090d0503030f0403080f0103020d060216122f06070c030e040c09081c1209060b06030403230f0702060a0512040606050f01020c0603011509080d 72
    0x142c1c4000e05020107001072010003d01009841c1c5403000030b603042c940c1c0f0f065601c0410343e45003552801404a0001000b0b00c40181c0d9001d07049070040e03009507030f00030071a110b050034202c4a000c207210080d84030110303401c4080007030190b401a000c540000303c00c00a03041c079951a140552681804a04002501018081103c081c01da50100e20301e146032404142141240300075603036441014102c041807080205c41d40c400c040c0308034084600003d001d0414000902d104001801c10146402248103c0c0112149540000e0680300800a44502c65a07000340d10702081c114a4000c02002c20166006601d030328040141e500d49100450007a4403d1f9a0119540344074291141d201c514100c1e1403829030020401d8042406070303d801d03100d460390110765250380e40c400310509840c035100d42c00b001c04103010000c04000c01c2c000542d100e03a08443c0e0030f80751411450841303001280c4600b032030b030303065503001c1810b02c01808041c11400e210440b400450924000d4581c4810b601e92a2154203600e100010f03041000d9180c01c80a007 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 275545818 1250 275544568 275544583
    0x1b0b01090f0539040620030c0a0312060317030a0c08040f060c030e100c020706050f0301140109080307050604050111030405150a110414040605010c0f111504060201050603 75
    0x544000c0005040c160000b1440d1881007080f4141c03100d60041100004414a11048036004098040b50341e45079280c10181101150310b0001e00c0b01c501d02070303540b00410004021200883d01d40b20103031400550599042e1640c900c89544007100981d5994003000140e00c421155490860800419840385030940071032040c0c0e01c202030070008000d4000140700000d566030148000083c3d0001c000314410720303148001c80c01010000c550070318a100390300312800d0f412072a03408048550700d40d50984980c55200c503015102403099031a52403100004100411212646070000c2402d03050500d4000b00ca00d40c2d402c03260749180c204410076209034000c0401e000400809100318640501c5801d4100c2c11480d10780c55080e25061107000b0040302d10141000030b105ea08041d444a06c450343c0c48580c468a46485a80c0c1d8512900300a0312140500d10b80000401c036980a600b100521940c448401880c1303410942d107820203000c103100702030f411030481542086000401d00151000d08082e03800010b040c50700404140c81d1198 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 275547068 1250 275545818 275545841
    0x7150201050f09070b030c0711330a0905151201061205070314061c050601081b09060f10090f0909030e0103090506070c0c03061a0307230904031b0b0109 67
    0x5401d04010204400317042da54480620070600d40c0780d10007400c0032582c201d00f080752580d21540c208980d040101c5189a21071032425103402900da981040c1d01241000d1144000c0c03100480e66aa03020080381ca0b003401c103903d4115007016440d0510000c2002d06d55101001c1c1c11180100c0e54058002c56800e101c4d100341035204800746418042c1c5407900c00e00b070701f18000141400d80180c12018090603400030040342c40f50480d611004564007582d441d0005a202ea00c2c1c10354045101c000d900c0c04500c9072928036442406a42d0080020076000c040c4000c00040c0504510100300340000e00000042000503a6505001044c400303102051520311031600620075403075411924145482d004000000c103000084080d40401c442c02c0c0140c00c2c03001403d001c2100e401c2035000402881c1482941041e101c82d010f0b10074034405040d421074440a4490320b495000300c04859032691070414900c80c1810070300d400380341036420034043d0620116401c40041620318031003c44030242d40d401d5414004015090240c82800c0c04003c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 275548318 1250 275547068 275547073
    0xc240a1e081608042120070807171006030c030209010909110402030c160f02010201050705030403081513090b040312110f071a040b1909081b07150201050f09 69
    0x41c20a0380ca2110898041c07002d0200034000c000102040b68a0006200503a181e200c26013400c46480c2c002408407240d00c1c000b51514500814900702c607600041c01c00152a081805401402e0810b61405640108032000072040e10802241e010300c00701c54030a01d00030b90301540ea405042825801071001002040c3c2c41320b08018580030b081c0000c100042401030000c4011500540d50b03403110004041c3c02c0c05515504516000b0100c3e02c01c1c2000584440f80035007034802e800a200ca562200b40c10744040c00200c6000d80402c2d8001d000900ca1480c0d03100380031504a00070080341c0e0021424a001d801c84040d00000c940e00c8074640c090005040d0407031040c0183c410b40500c1440b101c04103080340e480c00c4c010b244881150340000710b0007008000c1c05441403404804c0440719101d003032070141070984140c0000e0340c9100c444020409841b2905030240110040c054004512900e01008040640343c0c3d9811681d02c600c440c007078510040395400c14008003401900182d030002c1903506040c0c3e603c002c00c0201521001070340d03 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 275549568 1250 275548318 275548321
    0xd030801080105160c02102303100e0c03070c2603100b04050307030f02040f02031003030e09130b090a050d020d02070503030a170703060f030b010e0601020a050c240a1e08 75
    0x4680c8541481700e1268140c2d004c8440d03000c0702c10255861101d5200100392040000d05444a404841c0007842c800c82e2404400d90503c0d0381c62200b24201081a520460f00c00d10810015034060b0183d070455081c00d100740e020007901007222890210400103022102c0c010300000080c0500d103c941c91001c03029003da046c01501d41854180000d0b5600398070b102c010080c042d40380da11000d56540b41d1000100c0d06031100203540c4d070310f030042445840b4a0a404200c0c0410b81d02056582e030740c141068501c1c4600711512070161503100300d445045020400400d01d01c1240304100048000031010312814240c2e0a594005101c4464519000303410580d5540125000f47e0083c0710142c605a8442e0b00e0007080550f01080070001d844801d806c0700904030640021401801c4102c0020400068404044c102c404400c9500c0c841c1c2c40b40001262200c0e4032400c090305950048428010502d809a50200240f95422012441114400b190022500191101401303ea891210045142c1180b0603200200286150135101c6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 275550818 1250 275549568 275549611
    0x5011d030307300209121504020d111504050a05060f030403050f0403060c090f090e060f060d0204062621030411031f0f060602071e050d030801080105 66
    0x1240401807018040150314a000c11103d40300c0d1283c416103507989040d02809514003600e080281d0301440c442030052403040e1080c8a10000450300c0d10461003070b11608907040e11a81c00b04030310341c104484143c91010f592510040b080e40e908200b403081c0100c0c0c69045131600c0ca09002c0004803100c0380e0142d80110820824000585141d9007120b90169140c10001e031202c4010b0071306400350060384c1004001c1c51400d900d110060b9086441d1030211560b4048224103a915402104261a003001080360990301030b1000c1101842c41000c150b6116802900c00145a00260000340c155042070f0b111058010100002e00d0200308180b4440c030900444100800e49115031514018204001c5421603c400e040070010a0400140c01c817004203202004088800d030340e103110000c104100003418040700b020b10b48070a18032407074098003800d012100d050300070340103103498501a40e8040118100800c01441d4100008c40c039035031405480704a207806695041c0041d81800303d503600316003015103250600607800c1d85141d01e = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 275552068 1250 275550818 275550823
    0x80f010504092a0503060103031e0e0d0201080a0b130204030204050c03190b0321030f0108011b0804060608010e0a050d020601030c030326090a030210020301050603070518060a0c05011d 81
    0x140300710582c440c2c0c94041c03003c0c0c2041000401e20340100783e16005e184000030505911001c2803000321043e5941c60041e28484009440040502c15415000110b29070107401660262070044d07071150f00248049080030419002840c1c2e28100f01d01e0441191b030104c1e0520550605e4403403144c0c03140303185100e24078608105941c2143e20360489424040144c8603075800420f034400b4800550001010900c0e0404000a081d1480c0075401c21034081b25070200d0350000040c4450140154035580c1580803600400d100242c20848007680010403e81e40c0e075898500c0007030004400d114015045259201078110f03c11146015424048041075107030031544010010700101d4101c081c904200c0707916050030103003000510081c8020199580d16041c2a003004820049802004034081102900c83e07800e075072603006500040e01c1280001c0c018103410100500c00100d8030350184005080f580714800072801c00c410342d0800100307250310145205001402240c0c940041100c24018010010b15030403183c00c8508400c041942d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 275553318 1250 275552068 275552093
    0x605060a050c0111030103022206030206070c170c0603071d060d02040e100302090c2101261501050d0311030705010f0501080f0a030509060903060c130807080709020f040b0a080f01050409 82
    0x41d0720040e602040c518270805544041c0c0110750280066413103001d01d00b0486074151030b0b0302c680e031108c0d800007101c200007001c085104031085400078041401c40e290b448081302c106050201c007201c81240200710480381daa5030f13009032456000001016035118182038a0110410001e0480c01801d40140c800344010390301c0c203501c2039110b1003010515440d20040d00d25020211107802c04614484803280012130010320003030140427441c1003074210917040c40002c48003507921410505040c401c4500302c0014005032a104000d051030902929000c00304400840d1590705542c006401164140c0d0b45003040d2a40308558081e85005090b981d002e0f000c4245c1403a1a01d4403005001402004c12a001a841d045a581e20050f201001800340444841d80741142e101c640d40c0e44500661910031a400c0000208030800050100503910ba40740501019450125a800030750000003c1c00240d510a00012031341c1c1d043c1c000030304140700e003030f65440c94682803c010103503000b94107030400c90107603003881100000302d23402d5401c0c0c6 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 275554568 1250 275553318 275553349
    0xc0c0c031506031a0708090a08040e2a12100e040611040b04030302010b090a18080705070b1815130b1b01020c061602010c0905040f0605060a050c011103010302 70
    0x11032000c8035108040c0c1c000c10950300000c004d04019510b83c07070f00e000a0f0301c025120b220b454484032496254420403560786c3c140090024000441000184101959440b520f0313080b407a0543c2811030380515507229201c035000c212a2052540010504801ea00d0090f503107190030803816680204a00e0030000e83e16400140140090b1007181c44401c6084140080000c4800410ba182e5130141c495882c0d10f4001d02901c20361055501c90752402c400b1583c507094070b100396108007a89260000c0000050b075a174000580000360242e54500980d400001c0300c40c4a00e00030508800001222111400143d04001555448088418401070b0500014103240aa480d240060b20000c051079a21010142c1d01c0c2ca001c2c02c00200408490b5001103021890a000082c046000c0e100c0030040002032095803000328221080c0c0e0411900180c00d03190100081e051036884010408030041020642d42e40f2400415500d07070141207142d0010344001172a0702840b00c20702c150070000100400d01451540341da000145c10315000b1400c0c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 275555818 1250 275554568 275554583
    0x3110f07060209120d0c020a0b030c070f1109130b1006050a21060303020c0109080312040204050c07020d0503090a080601050604050130060e0105010302340b01180c0c0c03 75
    0x21000035511103030130080d44414942210884000208001e103c800300d100c040307010b04031011002c60070219420550703120311440d400c0c0c1820240c2c4e540311244d1020714032401b034031000700b6940190825143d070200180314070103859808103518490316104854800090241e801043c21000600041d40d2081c1201c201d0404d40ca000380458181c0039404402c1d07002c04080d800d02500c2c14000004064010a203458000c00980342c554540b5516107000e43c8078403c1140c50030f07440500c0400200145060741c0260b8100e900400340500700242d0740e010800d170042e8601c00b0b40b0607500102e000704691611203c604003800b41c03d00940815403500000c210307980030728040c07241444002c00615008540d0007a81d50340c0d2108125a406c0c401c85260360441c020001405886030200412001181550003402110802081c21442100101d074480ca40c0e034100309805645424000c100600d0404141d40e0703224035010746460003c0300100110111b504003102c04085518062050554520020510840231081120307000340c030 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 275557068 1250 275555818 275555827
    0x2103072705090405010f0b10080106030f06170604060e1506060c01230618070206040f02030f03210f01030305030112050309040507030207050c06040b07020d081b0d03110f070602 78
    0x1648040300035004150000403a0b42000300307010054000c840001c5030b102d01040aa00c0100c00d00815082c00030464000c02c0c10031004001052290b4040104a505448000344980d2135481c5082d42d01c282d083c44d42945e074410b500703220030b100d118401c444548006a0080480101e49102900b104d1001800f0034422030002c1042c8440000070341203e1200002c240b0364829013000c422001c022900151211070145013900c10200301c1c10707144145c6c0c1c0d00892158009241d156a2981d0f60f0320800c0c2e031800101c0c0c1601a00d110011144001c10141191034000b60700d45408110b204c0e42e48940c250003c00c500a191020401040441e4100c401ca038151404029000c19101c51070a10525601c00c8001207a0014030b04000c119220344d045d400341001912480135580e01500720010070589018901450b110300c10108000310042c0352000403910490310070310806042600000480407161080ca19100c1103800c0326600d00c076610341c1803245104041280d19640c0c02c0038929541c00710b1078042c031800140450350015 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 275558318 1250 275557068 275557127
    0x8070807060e0703030e01080106080a050a0618020a030e07060512090a0b010f15021f0e0a12080f0a05130201113c1c08040309030f05210307 62
    0x859100a801201c24000d400705031000079036521040c84180c0000313542c01e903c00019032003886c1080c100d8802c1d030b8400c03240303448111001005001c090560341c1d48560700c50000075000120b00c0100c2143e20800c074010303290408480d0190070b403010411360360040d801c00801072000c25040415121055000380d40b184040d80d038180180d20380300101101818628011000061118a1071400e405680d505180710140040441d42a603460030880d030307080340c0c400d40b40d150355030b1610880d8424603d030b26040040718030000c01500d407060400840388581000924000400011040c20407003c0d070040e049020030802c0c2e241420b000191801301d0720303000b810050080341c07014403007100b04604120b805e00d4540c01107542080c410440042c03030400c1001c03241c42c0c240d000000c4a001012480300030008940e9070640301e0b40c3d0821800c4a0700c1100800c00c40602c609180e0120200d221443d0420080344a200180f240c2541d160585400301840408106030007000c2042001490788980d0050f0f150300350301003040d2101750a0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 275559568 1250 275558318 275558333
    0x307090305120702040c0509031c0504031505090106060c0f020411040b0a0f08060102071802070501110a0914090402180403051909090b03060c0406141908040201030b120a0807 77
    0xd62018200b4400c07000e90b0640b21052000030680d8500c2110104402e454404060341c46028281401c4d074560006071000004044022041030101c80ca0b140c070901d080c0d02ca5070b406410b1200f102c0c07203402080c0e03650704000707107000c00744a02006805241001d400b40c0761641d44100360904402002806070387c0360702075007915062001c00d0310054029074180f603486800846006004214101c0800006149500810003550010a1380c4055030a1540610344812123450128040c2d0f004820484d10b0359a070f000c00182030106000034021400b49695040708a40c5802d00440100018181a81c41401c00b0024880166180364140300e540c28201c034005895030395401c080e00c55001b40c802c450901035035102e492007802d03440081282a6880080304102003c030304801d141c0c0e40c1c0812982ca4401ca1010003003404900c0c0940030148215074210642441e100e401c1306006c40780b110255401002c115a0001d2008668242c083c00c0c0d035008080e039140c1540d0311a85070103070b5642500702d80903009482c0025958280540d5 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 275560818 1250 275559568 275559587
    0x6010603050c160312020a0509040f0204050609040216020a0305070801060602070e2404020307050702190e0708040c030c0e0f13050d050903210712020a080301050f0127050102010e070f03080307 85
    0x5c40301c0c210f44070317840040082c010754055005148a24604091504001003510944056400240115040010040520009600088440e210500d500c99030710010383e200d0b810a00950700c140050b20704289007805660940c2c150703400050a41d00000030600c114005e106000b0b600011101420202044080001e0254800081080e80181c00003003003002c940c1d00a001048880c2c401c0d640143c411840541c0d0100448042c01040007248255003c11900d52080c0300c5c5a8000f40200101800345030342b6a101c2042218940c032070200340d5a40c10070408151001c0303040b50740c401d01c10300d500704c0c3c8401503589a50b10b443c0d01d201e044090003804a5904000c1e1020442c2858003094008610700e0031050801420040e0084c003001c44040c99101c503624180c0703201140301c480040d40074202d50304590034003042042d01180c010000b81013144a41c404242030304102c401104200381031003100649030030500020300b56440f0a0503004107500c036000c10400082401020800c81e0f401041d183e440e52110130048a40592 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 275562068 1250 275560818 275560847
    0x8030406021308071706010b0a140412030201090b07020c010e15130f050405090a03050315010302071b21030507060507091505180f090a09050c0301090605060306010603050c1603 78
    0x2001d041c0403806510002d60041511085d00e030162852085032041643c1d0102400b402010420900034004288d01528140402404c0e020581c0d0506d0b40f12803200412450351031084c0c1c0141c0d11a0030740414000960038640e002005440a80b000b201c1ba04000303000300c56010807607409210400746d00f4510b8200c56003620f044040c0241029204c07642e40c00a01000010b90003001d01c124a8500441d07400c100019180180c298142c80b01411581e5642e102074607110100d200505068082003004001000203020228403114086444c402c030b8107100c0749104101c402c1c0705840002c648074060001103900f09003611102c0764060004103140d95454011610030540340d00c22081d650301ca03014031074016000009410828142c0302001c007882015000c00006103d41c004040c0c201c0079100102c0d100b10fa1a40044441c2c030b00072821120180000300100f0300315030107010140c400c50b0381c90083c0005440d082c80242d0040c13241e441c0502050901e2000e400040c45900004001a5640765103e070400d8002e19040c0715844 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 275563318 1250 275562068 275562097
    0x70614121f05031b0901240c05030f1b0c011b080c0a020a0f0e0a05070c14010902060d020702041107020303300109050105030c031612020409080a0203070201170103020d0803040602 79
    0xd240400010307022480304c90390b4401d101140c000310b584001c82140c0e590030303c0811041007520103512000d903070800c1000c0058525000402030b041148140c04024511040d6510441406419800815003420304036400c0720304000078880940c034000b042040135042c0c9070304140481e5984014110143ca8540d058074001d4210840c14400204610760324110710465686148540c039030b03598401d02904842044940c440410004a031080200e400c82040049016840000155100b266000194590002e09101000640008070350045090500400c020440031040c2c0038141600c5c1d41c0066245d00501201c1e4104c805e0400d0141c0d01d6100480e040e01444078001341081c0196115583d01001d072900f400340d14044c0c41112803136042e5040015141f070442e410110241c0c1900e080060a500000c4072a40c181c0e8400d0300d80d110320001c0760960300180100301058005507581c403802e01c00541001410340b940c0344504060001007001d42c4580d401d41e2080e6034030a8a42e50f0f2a80c0e01d2601e480240601d605c0f10300000f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 275564568 1250 275563318 275563333
    0xd09020d0b0603060708010609060c05010e0715020d08041703040c1701020307030e1f020a050912030301141e0103090303020d181e05100c0e03030c070614121f0503 72
    0x1100c0c078001c0d014400c264190b410300d03035403910165441d02c0e083c0b02d000d0028850070401c2040b6485480403510440c400c10011403400f92411803907103400c0e02600200426071443e07102044040d01005440c2d128825800e1401440c034154071130000c0100c00d100c20a04208000001504001c00610b4002c0a81020741d40040d102881c02183c0e4001d410031181440400c0c90301101e807510403000120f40d600d4035174040c03c0080e005480c500d81b001a4100254802c2440424041c008580d90748485204180210b00003d40d202e48c903281004050101505006000d9503065030410a10042c2d0010195525001c1c2000305400700a407508a00030300ca10042c210b0f4507444e1849540090361111244442240911007480c00d030b14506100220540980b00c000744681d000c0d5600e401444010307000b0071541e140d00d0501c0c00d0300c88403410200341107070302c802e0151595403c02a414800160010341010304552601d840c40d050086003d41c00101c5a00948041108100c1d1580381085c603aa4142d034802901c4081c060300c1d641c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 275565818 1250 275564568 275564573
    0xa141c030203090c0406050d110a080a0302060a0c0c0f06091b1d090d12150b0418111204150e0313140f03120c0102040806070503010513050403080109020d09020d 71
    0x39041510f04840c98010298044228545401010280c901c0201811440b141603694507441c41d103a00c68154110048540000b400341042c0100d1011a01980140c09a03140101003d401c5031086040e00051202001050010414800061240683c860b1b030008200b04e41c1d05001410381640c400601d46e050745c580340172070b401c00e4811a118130526040b118448a45a05200680b150004440100040d0440c201e1101c0d608031908401004500c03804109000d0f52110b0070584654095004002641005049508041a18030400100d03442660040f03080c04190302240000b050082c10241221540043c484901420769201842480e1a00200c981d90f0041014441906078240301da00c40365030702024011141d0608602254070396000801400c00700c006480076098541000061b40b4840d9400c0c44007040341c0000b0030140380500001d44405460798500400c2105030701c0400590000181042c0a01c800a900b103083c203815504010005a00c400f500c9810354024048104041d61200312041000c06 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 275567068 1250 275565818 275565821
    0xb030a06080f0105220213051617060303030412052b06060503060612040512040e060f010c0b01090c120203010902120603060403020c01142b1b020a141c03 68
    0x21070350150180c0c0c0480c1c1800498a00701c0702c0c122650f0880c150b0030309040540c26503094119600510060140c03070000c880101315801c0b1030081b20391143c0c41c20310701c111031328603a04002030301d6084042c07001c0038500d0300d001008243c5901000d0702c014034110600c04902c11043c0500c0c2501e5505001480030550742e40004401601d080c810403607941e80b81e04d4803002040441c821000c0b240b10b0b01024010514020a0040c4c0030b11000000704291401c0c0280310301644807141c035070020b10013801c1e00c581890050814404210b40e0714100b0064905004141584600143c2c16516841c1160f000003030006142c00401c0007a0b51916041696225451000001050003032469006c0c201100600356094101c0d0750f0304041c1503481c00291070140150b8001400300300c51390701c617000d00d9079916241c600c45400c103104244080c40c42030840800e040041c801ca1541c0300c542105109192010038101c60a207081551000c019440c1d482c1ca0101802000304504203541c0d11100300a01c0c107054108862100240541880040 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 275568318 1250 275567068 275567081
    0x6011503151517130f120e090103050c01020601090509340e09010c020c150307030204030b01081e011b080c2a010c020109020f04020304020f040f021b070303050708130b030a 76
    0x5104007455004100307140c0018500d02d03e003c0d03101600c017162804685407000a8414034842e00200118101540350a880d1814111300071032003680240800313403142c00064101a03058120314030f243d1034a000c2115072400004e52144d00c403161200034900400109926003000d1818140a07070100c0403107030001c0c83e00c1000340040e2249100000070410300c41c1d00300080f0380700c00e105104280d20280d04c01001c1c9003500310300300640e0014628100145440ea407903a903100744000903401101c16410500ea0001c4020341d8007074800d50405080d00070091180401c120130200c900c410095410041104001040050030100f00c0d0245a00c004d6400340003005054041d844108003400307070b4555420700c8170fa92481c43c014081d501d44160b000341505610301d00d032414032000b034000810580e4000d405540b402c0c10f84e2142d20034084402901c190260b0345884a403558460310806140e6030415034840340040010940c071600343c1c0c1d4900d5100d00e04965410108400b08800d107c2900880034140c400024051240b1b615400b40 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 275569568 1250 275568318 275568347
    0xc0203060c07030804350309150f0703091113051008072322060614040b0409020705160b0d053403110f03011403060115031515 56
    0x11051a03a03001ea80003224080c1100003000310391404c001c02d0008100d01056503407200c50000d44007000c06550314180401c060107007002201c003c000103020504505110b00a501c2c1c4201048070550b0034205140b11102d01d00624410402d80d46102c50b10800803074a500c0c0c052104002d1010b00362882640703c8000502d4260746030b111002c4d20000c001403440d00840d1900440391030760205c00304c079204821100c8051700d0342c0d100700364807046200b00820114034a003402d4000c49101c0740009059424080702400050740c2d0306042c401650284020400303200028125025103103551005a1100c285241c845d01e0540e01d40c941c0600f000071b400380400c220740880c0242c4040c10380840284599112030007000c2041c4a410001c50182760710071101030b0313a4408a4002000c4015038500080c40b0200e00d2000c0c0180c2d0045c81d400e0303415a500100412a803204590744040c07848044002d4600355240255007010a05030010407018140c4900341400440c07240091003000f07045150b90000c1c0640c8045000b81248851f0140 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 275570818 1250 275569568 275569573
    0xa0f0603050702060c0301062303070f0f0201060e0610050c0604050322030b040f0c0b0c0102040f081f0b0406180902010201050a050705070201271205010501080111120702010b0603070c0203 83
    0x108101c0c8000303130460244030701601403861a42007500071130b0000080782c5400300c1c100515040d0444040484000e520444050742e41c403200f4410702d60018607010003031102504580c100001070050802000400e45c00035402c4030740c5001c0c5440110265218099003281000d91f0052204100502401100410952841c01030311000f8800000e0464520480c07400050481960f2030b00041c009030b080005034016a00070403400d94825903e08040d4241e6001c07180780903c40c0d401181c01c1080c0000700b10348801403c40030000d09482042d4400d80043c07070001c2c034005907080b92600c800140c0d98589030310880182c040307004100320400691007c00090032041c4800ca00542c84c3c000040d80b02d00651080398021027481e40c51600e00a007940044662004011144a00044c0c680032100c078407884030512401410b4404000315075416a050007400c440d4140e00415aa03410841d000744803680c680102c071024205c0a03469940b0b61903c0000324010400d0745c000c00d80108000080c0b03d01b19070410802c0c241540708604 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 275572068 1250 275570818 275570821
    0x3030605060c0d11071505121003150902040e010509010605031507020606060307030204030210091806030503090609010e1c051c02030906070602090a1e12080901051b03120f010509090c0603060f0a0f060305 90
    0x1400500c2c00c00c242b102400307074401c01c089a0440d0545800007940d03640000c1000c11038035900082142100c005580e842c0c002ea54441c5c040250b0305041c0103048000e13080c3c40307201140e4a0400006034480714020103030303489204000000b5142601a6042e1005103401402207150301a4824001e408580e950080507404120071b8a00c2800002c81e00071780003965800f00296003099030346401c1c00002c0e000030300c9280c10700400a0400b03000741c84640400070640341c0d444108510000d282003107401e0118008258a00d07000d01c0c070760007607403540010480c0d0301401c080c0c508a945031000d0a15030028064080000c0e0300850703e0400086080785070481070f5180c40303010340d0400816a568a5618000400350000300802d0b014050192030350701940c05000302081e80c942801d000c0341d591b502103046074004511032614203400403c0c800c8002c000700c00c00303015000c00e682c0408941403181125940700074250030b203441454000001402915020700503c075a00018010442c843c0d110f10720101c034141d1a000321000640b8050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 275573318 1250 275572068 275572081
    0x20a030b060a020703020411040503011503110102030406021903030f0f0606020c04140a0504050a050a031205070c110405070504080a11040f090201200a0f060903030605060c0d1107150512 82
    0x704480703680c140d0b07400400b13043d440e66080c04003070100c603181011148000d0000007400c1d1002e003c0e521030000c28800b1581c015040d480c28080220402a900c3c4c11580b00b40401d010311900003491075000c01c1c09136051244200c407460120068400d817040c170b40c5068240803080c8495009600180c061311800c0e026039004158031818041150110390141c3d200326078003400710792041182d0703100d035400500a00a07100500d03800d03114285002c8101034101d00040e0305206d17200d45d0f00c005105030381d04001c4c0b0307241c8000717419182d484034140039081c05510351147d69140e02050700350f4050801c440c02400300000743c40e40300c40320f42824608922a6668036001e281001c480b0300c0700a4452007100503c0e82c1c141c5400d00410000704900c01c1d800961041407450b440340340501d001140c01e00310302d0303403020b07104440108201d440307490000c003668601d50096000c0d81052080b40c2c0240c20204256082ea21145841d501c0050352050603481d26446600c01401850b40000700c9c1354181d4040c0c0280382c040b140e064640c40325141c64 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 275574568 1250 275573318 275573329
    0x90206210a0e0c0613030b0907030c0803031005010e13180c080c09070f030902090a020306040c03060819020d0b010306060806100b2514010506040e010b0618030708060a020a030b 78
    0x460b00000b94010201100d02d0745014000b5194007841c00141e28182500c940e524044048190f03015119030340540c50070000c110364a0b0781203000c3c100c040051800c0d405c080022116000c2a03015441c10300021505481da41d45640400600c16006410180410800c3c4802c0070005100481d0689062440b84000729940300001000b40000502a000b00a5a610780300121454401e0a24000c04c16448004602c0582e0f24100b100e0f004001e0702c40d00503030340d08180d000c103c102c4106020803c00d01d4100709007000619030205915180070102d4407000e070748007080d00c001501c1050184004000785844800403060112a51010042c1c8880390308480540d1103c041070050b0b10b0b03c620440301058000c11900e0442d032403649a841c1c034000000d102d8030361010035542c1c442a0480407001e0140680d1340c1c000708686840c00f0f0144120300741c0044000c001000b6030324041307001803060540800000d60712441c601016103042100d0001026a242912103508104182c10040d500500c01c1e900000e0421143c9615890702 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 275575818 1250 275574568 275574581
    0x50a0e0103020702030703170705030a021e0c091503030c060408030f0106090305030f071e03170c0406050403110102070302030d08160e010815042408010c0c24090206210a 75
    0x100140081c40c51f6603549284582c2c0c8408a0721988014008000001d2003003014150400240c0c0140580500c090322111040441c210719000340e501801d45042207448050109400a00c034076058003684c0603c00100e8074500c00d10343d03403100300e124280c10082070003d0000070b9801009101d031020402e903650502180c00075001d000150107a0010440c00f02c00a580c000107000740c070700c0b440c4004034015816810300c0d003026003444180c0c049100d007060521a80001180c880e8002d208503002800d050a002000b080740c0200e01004280c84812203841c0d205a00800681009542c01012581c41e90700c60746004008580c00d480c5450700030703203603030150b944907004500f5540e001106079107100040d0b0780c80911210520000a1860704165181d2010b150314015880d50312540c01e400202c075114a04d840e07940c600f144c1680d0071860400400000000c0010107050759040c0d0306003260088151754050040d50741c010a00940000d40c022000140480020b01140d0400507032203c031901351a040d40c0b00410300043d19103 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 275577068 1250 275575818 275575823
    0x1050414150106050c1c050a03050106081603020c0111040303090f0501081e13050d050a08060f100c06270b0610050d0e0c0d03050408060a0e12091c03050a0e01030207 73
    0x601da00140007a510500c0a08084144e080440c1e122510080146043e20b0450b00c440000940c0054500c4026170507002d018010304852030810b17414a00112a104800c078442d02c40c40400d6000607003440008000d4000030f0072100708c96007d40c1d0399552032801400c2c440e01c0b480749890070380e80c02d0800075542d801407044a2141803210041c4119903256844aa01584001c00d07200d0a49442c6500c040458020031012102c04841e44680f550349904902c05000004020302e040d2194000714048a02501c034001d8210080129062440200790546800340142002403066007802c900002100c0e002042d0641480b2050301641400415072500014000d01c107000003119000300703204210700c0c015401c00e9400290400c807880705880643c01440001a18010446010303000110003040600c80c08200780013240c5c01503851601080301c1f2420409a45d101d111030081c550605401148020349500d4406480d4101615629103110300700c1c15141c0a089034011a21300c4000aa0f20200070348154040c0c800c0303601054 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 275578318 1250 275577068 275577103
    0x10b040509040f06050c0318060603030d0510180204050103110a200f1e0111070507030314090d0b0a0b15040506030604090b130b0c030f0703111b01050414 68
    0x14140014400e1418020b44122031510309914180041080380c440d0a004040d0100c2080d520300f803032890081c0780701d8082c120201da070304490144542943c0001c1150f0004002d150003003245e5075022844021054142e102c40c0f00001c10740d005e02070f550881e600034010707208243c81c100000180300e50140a280100d8813403101148524880040215065035660300e141c0b0000211035103200000c6602d0b051066580981030b60303601021031203070f0014080c05990f40311829030701c50600340030064444907030321980da10002c0c05200460100142c000c0304082101e40012000d002c440c0c00b00d190b0303d8101b00820382180c50462441c9070100b100020714002c050050802007160800d1709183c140b00420955038400750031554402d58030044030000568210b55580f150021100c3c4d0181092103051001242c500140750001d000810000c004525052099494000b01540740014180f4207040300d2a440b40302e0700e5800f4036243d0a0b803900f150320141c15080f0b50b118900ca4121600030710184405580d84007620188120500c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 275579568 1250 275578318 275578327
    0x806010c020303040b0f0319020703080a024503060c040302060d15080f07090209131a06030c09120307030f0c060b0418020910060e2112040f0905010b 66
    0x258420106240d60500040a40c0d150564a2030030341031561000f03c02905401000c42003001c45001c0c4001d4580d07107108500203514003541a0b800130b00310703a4000c151013851640814201e4920805451402c2c003850341075503601000300d10101145400c81c5060351584101c12054040d40c0b6030401041c01c1c1e01902100d481300b402c0c203045508020303079500041c009081044d500d0650034100380383c40c00c00800900046002c0c00024416202150400903c0e402005050780100490492604c0b40303c0e00785d5200590344800606900c0301d0501051002004002c10f900c000d0104c244000d003d0014001c10300380e4012126a40400c45958140c1d440303000743c07103026000c00d1203003100d550158000c55405140c01d2040d080003030f01039030400000b01218070403420394144107a500b51150031402e1880350250441224490182100d2501400900c1048240c5110740611300b0034942515440f600b0010180140d105019540314142031030380100c0581242c414080f4a40b400d8400080c1c44803148280b41c1690b504048440c9070 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 275580818 1250 275579568 275579581
    0x2041d0d050a03181a01081203060405090f0d090504060509130305030612011503020103230a0c05070204180b0f1009110405030a0b0a050108031c1802190603051608 72
    0x590b0400520601419251000d11854480c2c6500a410961080b40441d00c1002c804039948640b01d0140c00111059003c04803044954415074140c0307910a03070858002c603860f5a100034041c10100341c00090006486995544003030381c0d411038800e0003581c409a50400107103945004005011005030b03400001c000c8a107404502107442080151340c000e50150803074101e00b4180d0740840c21035809000380ba82d100749200c0c0500456a140c001c10828032141641e1304001408400c80524031300c1c014001d09042551610100041802002035405d0b041d00103100300088107150604191000c2207000450302010708000040005070200d44190080040c245c7d4009124208241c11008016039880940e540c14288070004555404001e0b010206124454032038160802c03030b44203800c1da41c060308030651790340050010041000b0002d980464801340c1401c0815103000b09943d0703042c42e040420002e50070203a1390000c01120f125110f4140101e650b03039a000c202681c5c1b00d0805007654042c501600d00002e804501040c40d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 275582068 1250 275580818 275580827
    0x2070303050334030c02010c0309110d0615030b04020a0b0a0c030f050f0705010b1905010c15060e01080f0d02030a0f0804061118040e011802061312060902041d0d 71
    0x2110304403043d01900003804401d21605407040100c81c1e4000380d02d42c0a44d00130681c1c203008035070360842e6905080c000704007240e50303002c08042e0840005020303804280c040da003031003800d40003802d441c0b4040b13549010441d240d0078890503d504c04c613010ba000c0e0601100005201111300c6c03c4485282c2a9a18041c1205003070381d0480310baa413401d070a002000414062070340411000c0e401004c09910442c00016288c01d4401804030b0a1a00c3c0801d02c80030003248410801c030b98001c0100e51034941c3c0091061101d0440d130715030000a00131070300041c518401000003c148004000f5602000e0501030080b1210f84d003000c10200e03079074807403080360b400020303451101c0007852402181400d8025110301c41c082450043d580720914a900007003083c645201119000320a00e05192080c1c99400c59210001e100540001881d015603485000c0028020400002c074150030789482d050300c01c05418015201c080e140402d090440207803230409402c3e44a18901041010300320b080300060f42d03001c04c1c4400903007401d0003066400e94 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 275583318 1250 275582068 275582101
    0x1b070e0f0c07060c0807021b01120b0a0f030807170c031c1d01151e05012312040b01120209040204022a030c0708031813090203060711010b01020703030503 68
    0x44624024440c2d01e00255040c01844900394a690340d9802501e0049070092410301685038010190342800701803861642e00095200440254031004640740524202084101d9850b920000490024500c0441044080070080000601404245d0010058040c004800c1d100f5202d04010952040240903040071318503620340d102d080400e0380001c1c0310403c000b101064000c954104c161036590760030400103040004004401601e40b2003c14100c0744147c845042103a40c0070300845040c045020101c50406101c140c0c8410b01c0035042c40029198405022407076584041502c040722103114140000c150b900320b48020102180d0003c184c40519101c80d001e01000b9844540603104014651080c0204115020580c00e40303040c00c207004658880060403c0c60518425811000503a00304110000000221240102c0b02c1c03e401c0300c000b034800036129119001003900510094050181004001c07505800107814040c43c01080020b00680007610012a01c9004c2c502005011850a201242c0b03070948000340d58 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 275584568 1250 275583318 275583331
    0xa11190311060f0d06091b02070e060a180b0310020c03030a0914030f0705060c0316050903100e0a060e030c0a0308060d020303070b090f0601030f030507031809021b070e0f 75
    0x42c0e24102e2081d9011071103034085420000c5240d02d038042000030103141e1061442041a003802e1254003106081c0003500d8031b0152050180411000c0d005c41c03902e40d01d0003428002400340c08160b60b800d900020120740a080000d0405201e4042d41e9000c00c9072080d94003c5400035007404015526550f03c22241d94001c02284200340d54580071a40b0441c80500100020402c1007038944040340c5500c5989050b80c50070382c001749108800340702401840448070b50301d030754411004081d04080d6201e80180c0c4c04030b40b5112a40300d4610a50b03040044420a08101040b031506260044106000c015440b400e000d44d24801e81d03594441c154031070400040801d10803141190450001401d0b11400036903074000915542184406894880c1d9200c00c1c000360041c204002d00a40101402030a0150b01d0358441443c4884200006820f2090000703000080521411303d111004481c0803000300305d591100c09050080d0005003c107822012142c80c81ea00e11000003452900b240c41709104601d95030fa4200c1d40c8a00d0300d034041c054 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 275585818 1250 275584568 275584579
    0x30316050307120e160b070809100c1a0403020d0207080705040207051203010305061e130b0606090405010e06100504080726120310060c110907110303090a11190311 72
    0x14603c0700c1e0840c001c045031031081000800d00340061010b80c0c8803000e9158003071590340b0306c1000000001040f02041c1c907a504012152000d85181c010003d40e4044a030403030084c240303158110403190700d2081c0d20149000da40240d080f03442c00c80100f14243d9440640e4020124235511099080042c0d1403d17030010a5441e104409031a0703c00144400c02e44c140d0000c0e0801c44550b0000001c004500c0c90a03804203662801101c007114550501a15040c019028130b0405883e8950034000100181c90741030413180440e001901c104060341e0351744621280d910b0243e44845c496454241d010307078490b00c95010794050702c0100703003d842541e01d000c401e0300c00038000c01d110f661082450380c8000f039486024059003108900c842c003005d549151400d42070340c00000a0304a00144889400c203100401c0208584540210083e1a0240c1c240c54000044e11007801c6001d000039144000410000402004138820340c845218510002c440240b01e803c0050f484041340f002c2c00070794a941c03402c002040c0d00220b80045504050003 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 275587068 1250 275585818 275585837
    0x2010c2006040902092b0209040807240b030708070e06030115140109061706150c0703030c0b0f0105090406050a020d0c02011b08070c08130506070b0a0e030316050307 73
    0x4074220742c200f030f40070b161081c1d4007050040490a007907024039501d1407000c40c4020031701c100b50008103d0010360711020b406003041c07000150800010400300c6420a411052416446100d008003078000c41a000102401d10308022032031809090004640c0c0c1a0340c083c0000d02181402c004401069440040c41140c2c150f403a03130600042007010303c031b280340a40b01c2c00022a080e40d10800c009000203901e035002c001003218546000d002c107900d00c02c03015040b06040310b40da00000c03454803408005021b2845005150301940c40004100340d0041c2200c00060320400c0b07000801e54414041000da81802d210742e82c0c001282030000786c00106c055120f83c0d800700c114007006050803034084041c002c49032040b0104002d80e64825041c0070304811508000142d5070a40f8199010749040e2070000c02e07900f14048014075101c804120290943c400d02600e0020302409460562102142d0900803000c003019244400850714003580c3d07050700e481c04400c9038400c0c003103045450480708021100721246e520082c600d000b040034056 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 275588318 1250 275587068 275587133
    0x504051506031003030224070e01020a060c03020403110406080330040f0510050c04090f020708030a1512020d03052203200102160b090d0c030f15020702010c 69
    0x41c0a18050b0140041502c0c201c1c4c00c1d840d02a19141e0318484101c2d40724641d58450000707c4407060300316440013542c0392004144a5810040c2c0c07400381c502310300801c41d0f810001132080b2280d1660203441128020f90040400705580c10900c4110380d80b500480400e50001c11081803000e10b40882100c5290101614011520007408140626030342910100c0c0d001c80001034070024003c08003e507048400d2700501c02c0156003040305215006200c1d1703104400007103072210904282e0039082d605032201660420f813401c0d40c0e490301014040c0200062807034010110820f120105e038843c50a42455401d0343d01402e6402c0520700c42c2c40a0320240c10050110204207070481c3ca102ca00400c00d001c5000030342c403031503002c0140420720b40c041010f000305021190443d807010b1100c00c14610a00303000811500800c0011b03030394070500000f145c2c02804c2507102400300c20208070000100881030650900d8180181c0c010842040e0b001565000d9116042000c2d000800350f030f1241e004110109a0f82c81c0c0b084020b16440304903543ea0 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 275589568 1250 275588318 275588329
    0x216050a0620030721060807150215041505190c03050603100b090604020d0b03031305091e04140120090907080108061b040504020c030307090e090705040515 69
    0x103101215030945618420800b110820403000b840c2c000b1040203070035860442001418840c0c0003261100b041c201c50404899241c00354401d0002d0954a000d9641c01c1d9243e190822500e6147c030060b40041c03091600702c000030503607194158000c0d540031202c0c000c44007200026070003620000c2d20164507402d00f56800c401d422454469075044d60400d44010549203410801c150400181194903110a8202080d141850380ca40d054103074448411200140c462100424883c0201241d00c031964052000141c01c9038652140120b580440f041280c0341902680c0340002d00c08001303800141d240c0c1806c200d10115000036020f120503014840c50b07000000c2c00307081d81102d804844003400c0d00d10106100003c2d00a1090400c048010345c407070710506200c0b58951400b44d0080ea103c0008040b8200070212414200c00e99031000d007150024540140b095480307c45a942282e140c0d4002d031298008108040d8001071100c02c424030662041e044400900202442c203811700c40500001484a68050003a0800064603540c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 275590818 1250 275589568 275589583
    0x9070e062214090c0a03060905210d06150c031d09130b0c0306150d0908030c0c0f07180b0105040902040906080d1803021c06050901020306030714060d021605 69
    0x212001c99500140080c1002c2520064007100c1c15401000181d8240e440e030450a204580d48034200040010030341c01c065040c4844001c060310202020000d141072400074101401d900c024400c1d040000c01d0f605c0c2000e410078840f8440ca000403030410318400d00464010141c06c050250044500e08039410070800260000c3e10444040180c0300039031400d80705001200000c0b035482030301010720740c0c85c5040000000707083c2c1e0960520803414200000e0050141c8100c3c0d00041080da601021113522801c0c102a00c6005401c05891000e00b4451522280000000001c416048400f41e42403402d000c0c91010703d6001811040f49280d06101d0104000100803149100a100400200b2030004800e07080405480c200b1180440031030400402d40e40c90724200500b4003544007181e03411245960f0301189003100003491203c11a0141101d0b00e01030801c41408410340046105074030031000c4d60440c546078184281e005091602c000c1d0400024480300d60b04524036801481c2c1c0c540700148103450f020003a41c07001e03d003e05 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 275592068 1250 275590818 275590879
    0x1b0c031207150f06060e0303040302060d0b030f060a02030a05061c02011202040e040c09200f030703140a050a05070f02070b0307230c0114011508041704090603050c01020609070e06 79
    0x26203100030017065502013000e0360841310883c09141340c00e1442d0000f0302a405030080401c030080d9a0400350320155010001c2d4900304d40e142003170710120318060a0a80c001d4100303e6400c14281e09000004050745400c0742c20001c800200c4507610805095500111050700061803040714181e4200004140d119030001c01e584a075100e0701424450504000480b001d4031443c958100c03200f404d886108c41085541001c1c2c801070511240700a4403a5a840c40c2103014203221204c40840c2c03080e28060040d54819500070340c3c400c03074868400703005507120070f802155042003ca0945006030001d00c3c0070320660000c0c400a44c0c00006618020000c4000c0030019200d89002100b1b101054400003048801d03200207005241072034803628485451076262913400002c3c15018200c1e0400c00c4843d0300060104101d103594010f15580c003083c45038540d5216500c00004200754002610144205400e00e80300d90310000d11580300c0c43c0180c003d0210700345030911030011400d01414917503000c82c81c92805118240800c580300c0700c01c3c9 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 275593318 1250 275592068 275592071
    0x506012007031214190207090207060510061b1506051503041104020403150203060109030b10080f0a11100c05010c0509190515070c030203010906021b0c031207150f 72
    0x2d1561070007a000540140385502070094074828403c0c0c16003d842a5500104c401505041c458851305040b41055100e4000c201c04505c089544400c1c00420360102d48110f003019031a800c00b0742c4442050b0382c80d902c0403101303070400030003825858005014031680358507180c1401030110f038141c0c8800c0003030310034805001364030310500d804020001446456080780000d40c9055030301b1403a103801c2d61501100c00d412607001000107500040460803031303441114450010364011900340094140800181a008100c2c441c84810340b2071800d203004451070211b509100c050340300c40340c2d802526582041c014020540d6010800340040803070b10740c0c0031410a01600d0854882e69903a140da40410310304100b2800b5209070b911143c043c0d04003003482580c603500007810040480500c519202c040300e01c0c001d081d03403540d60802501542401c4100c0100443c41c2c0280020394006000c22403038040403107c5c10b03640c01c03c90500591582c070030050548020b40f00d074000c0c10303a50b003d0004a40401031811400f82540d011280110046 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 275594568 1250 275593318 275593333
    0x708010903090e13060203150a060509040609180609050307060f0603020103061d0a1e090602030603190c05090a0902120c10140904111333021005060120 67
    0x198080320708000f50103d04030040240c10850103c0030303482d0340c18000414071a4000007240c440d8071484440c0840040041540702426103e030002031091700721601c910301403428882d01142c034003050302030f04144100d2500c1d0140d0719101d64442c80090940180199914003040013201d0200f0998003554610780032126001c5561851440010b0464003680d0125008691182c12190741403000951190005003003500840c0c00d40404110800310505124210b00951901403414200406500554442c12040f01074074440320741c0e1190740408014001c0028102860301c0030a01c82c6103050b41d502038000c980300c5400200c06005501280c1c40c0703a000303100f2400640c000c24960406140c900600351154401e498900703580300d10b101b200d400d00d018200c25076200e981c969604403aa583c0e40400e83e860325060702030800d42e0681e202070b000200c00c00c20001170104446403411000074030280e900440d1000c4250f005007e6140108034400c0240400703408241000b141408441c4e9404843c540d08a004a8a80180012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 275595818 1250 275594568 275594573
    0x30e0a0f0218060303160c180617010e0a140c060705060402030c1516020f0301050c0a020f031306030b12030301060207060210140609042a090f060b090d02030c0307080109 75
    0x30000010342c1000e0004248100a11520084141c81c1d8030440800c5c04d021840140c500900703901c3c0b45812007040b640042c04d4002c4140103030381212048656010085044140303002240342a9049040440c080d64081c1c1240e900081005502038045190042542c003000e1140000074000c3c1d016000654041e40008207010543c0303010321098458401c12101c80384c0341109900c21040e640141c1401c0c0840d43c000b09510000e41d15088000222000024004c211900d40499007074010703000501c3d108010301c118016800742c04c1c1e00000311100100001c04038180c4516100d01140a40440300706160004621020940d5025041014501802854014285490034081c1c02890f2400d032440070302015041c0480312250301d005407411500001c1c01e403920303c0705035541d040021100098000440c1030201e002001c200c2c003070314600703444207940030710744203001001400c00140192145401200001581000010802d14092441051070303403000c1c013600e080655007000682041940c3d230000180ba5120001d9108 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 275597068 1250 275595818 275595829
    0x4030609020f010e011202090109090c02012007021806030307060c0e0118031a090f030a0f11150f06271806010803030a02030c07142a0d02060703030e0a0f02 69
    0x921400a1906903140d04c0c844000a1030300c0c00301d024240c6010750004034040e0a91140c805c81024005955081c80390845014009000708805c02060201c2c80d45d800b600345011151303204540440740c005142d00d00122510659003150352010b0300150b418882044800009201801406e01d00c2500d0f072035910f4030256420026180111030300820a54581c90136060002070030b40c0140b181301c103a42e140d03041419510000601d01d4403100c0005a0094413000c1508100d81d5403004500c041200c0300e54414408031884984103a5680084252114410b5100001110b09654070b0505501001c024800d094104089288070150102e81c44001c0c4d0010780c040410950380500c0c0301082802c0300580041684c0d40c90f0100702034480c017002c0d280c411055000008980380300902015140700d540c000300001c0c01981114900c85d41c03070700b1040503500940d83e0410304220451101855913010a0081c01803840d18001e81d0801ca42507000c0c450807000d140e50b8102e58a6015000c005a5801c584100030301001101607004204 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 275598318 1250 275597068 275597089
    0x30606020d053f0a060302030c0f0d0303110d02040b25120c0f0602120411190303080c04090c0f1701060e010804210201141321050409020403060902 65
    0x102448000c000480319003c60744078a01c4010400548141c07414021681c502c4104040c07494030400c400300b03106201c60064581d1015049034400c404459541d0540828002c140020b001d010381d1000007101d01d040428000d40003244400044e50b00d19144c0140b01e02c0020403078026800c030350910b100120b450103c14818a2220801040e00008079544d41040c0d0380302c40a200112813104100002841c848080000c601044082d4603840b41041d074840c00801800842c0850880d416102e661400b5620060760520319516420042d8416802441d2401c40d28155140030b0b000e807951a01920030807000a00401c00d215515000c28280c0d5060741c00410244010042e030010381d514458042030070010498190400701e042e10010003800c0030226940c03242081540b180702c12000ca1a0384c250ba400120441e5419070081840e8203ca030814001611900020154141c3c090f9004040091620341000810403440509500101e10300c0c140d03182036200d003100c100b070360401c0d801111095181c50390681185824070105 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 275599568 1250 275598318 275598343
    0x130b0408060c160203011407180510050a0e0901060c03022b0e030c03100618090b27010c0e1002030306032107050a1511070807080d06051003060602 65
    0x54101418018220385511001d0204050100000760800120b09503201020b80c0c40c0e0010000c000203001d0a4200740703040c20481300e00d000200987c0b406003a0000040801080c1c4001401c030322151502d404080e120359000c441c87e2000c0c400c82504441da01d581c0c5140c80f50103802d003560b803141180c0003454060310b4800108041400c65120014000340c40188001c0016440070501c0d02d0301150b0383c00c00c080707030030104a121215010700904000381034102054206900b01c4032102045003600410000e4181240c0030a400208400c0b00003010940040d0500002205d4003403a0100d60f43c5499217280e11407c440c40244050085010003441342c03064a0300c40300c41400c0140da400074624524000002a40718a0f280c5a49820134080a542480b0469410281c4226076400812900d020700b4071b043c81111580f510991400340390a100095000103040030a8032443c1da030001e402818a4455a1059801c3d00080910054103994120009090780c0e0300c0803484d4503900c0f6480c0094018245a4003d05109580842 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 275600818 1250 275599568 275599589
    0x3082a090901060f0509150c01020a0206090601060e01080114150d0506040b041802010807121410060f020316021c06020315030d05042304020c0d020709150504050a0b04020f13 77
    0x80030499004800c69a04d080b0858036007071f07480c0310300007030b00c10500840610101030340c40441d00c40c0c1e0352500081c0c400d00401c0d80c80b0441c1c11b44d81c0e80320300840e6588245007402c1c2c00629940c0041248e0200f52071038028110006006185c54404000c2141003a080000f0210b440c984420a02407070742014401d0603201401074030203000c030b80f0314644004540d1a60f40f100a0410001c03000168020348542024015241c0e06613050082d03003540360740030303e0f003080945002c0f5402d400440006480340c0921041e04ea03101c46078000d10f01b42922800d00141156000d2805d98203d0010402880c826070450141030980f4800c440060301c0f401d04000c0d40288041c400c0c00c1c1c5019600825160207440e401030265801c940c204007420a56410001644c280304031808401600580045041141d0120100d0801e240420507403c864525954684101c00d43d848044500605284080e00f4401c6003403540056900800c0321030042102030280c1c2c08a0200e9002a404003a641c2010541e5140032000c039000c5d50003440230082 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 275602068 1250 275600818 275600837
    0xc0703151d0d1d0d0f060902100c02030601090501080705061327140712020d0b0a0e0103031e0f0c02040e07060504090b01050c06060607050703050d031e051303082a09090106 76
    0x411103d41c1351000180410700310101c20802c0081c2504110855940a0441030314440600341c01740000050210072440f900440c1d00200c0d0b00c4180e0310580c0e040382c4a4200030200a8036040078400c295015292560080c0e001680100701c0c6e61640314401404030141150550480c19462540100d900b54503a03010581600001d00c050f0560000308030703c0c4404030000059989006264a0300249022904142c01c52818180002e100c0c0c88a6001812030303019032142c6840301d2182a907403624001d803003c0c01c0b021031200602c00c04610304c203070b142400d55840035200203604805289a01c0c50301c0c5059224a000030000141480101640e003d00b11014900382016030400e07030017483c5d00c3c0c4c0703c500041c822402500d01180880c00c0c07100401c9504000c1d9001010764080035038101000780034105034130f0240b07005890400281e101403502e1190703034030818840041c61030f0090130350b408541d9041d0103090049404c1202c503207003001ca0000204d005402c0c2e0050002e568402c0207000707121810a0591040040c480b0501 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 275603318 1250 275602068 275602127
    0x80f0a091202031c09050409050604020906060403030f08060d050303150a0602070b09040902150f180f030a0f081c02120705040b030f07030225020f060c0703151d0d 72
    0x94400e14521035480350a044001c0d2003086a80c05455030021f0b90007420007146000740040850014003403402500c0b9801c0c299100024080700388550f200c000c000444000c08004100c1c8500d40300343e0010001041035280c83c005440d441d1558100341c5500c40f02d480320340c10180091904404903002407100e0f00142560f02e00d840e10700d152034052400341c94020364131078240e1021555000e0002408a00062156807200d150910746503060b04003540500e4004400a041c2d4018a003c861070681c500380100104400c002c260b0f0b4400c000903441d40c08a036890824400c1d42d054125070380c1c0c110301801180c1c0c00103071644070a009402c0c1401d07010b044c4400b0304c04200000d00030703207100c032049079840021342c48889426100c14a08400070300c00c006035030071000c3c1480d000c41c5032410058041b00c040d6008560380620700380c03c0380400203503104544000c0b049900911041000544100440d00200c0c86c0071800540d00c1a0b400c81c0c071046680380140290f003500320540141d13039aa0032a403e0340c4440651b4040b03000111145 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 275604568 1250 275603318 275603323
    0xd090b0f0304020a05190608060a030c0501030b180c0c0714091807050a18202a100608070b0a0203040b25060c09080f06041e080f0a09120203 62
    0x440100640d624008001015901d69542d860004d0001400c05940090301c10000084000c0c240904800604c00c00003103459843c0484864050b079400804124500d441c060042d0028605209440c0d04100c6200c442c003080c902d2a00c030f4501c6200c00c2503542c1c0e614000031144c00d003000402d81218820a141d079405400d1a100c4080040d03002000c0b02c980121858100c04581c0f500700705910107584000b601348003281c0c84000514071280d040d010342c0706014910040100b61020b00e90300381c154645080600504507800c4845c0182082c1485c40402860026000c824260504000c40c00c0c0040da5515a40304005d481c2040114a00400001d414141062040301009440b4810340c0300d42064080049100720034003a1045075070b01d031800001540f0241c800a441c0100c080c14152020102040400100240344040480d1120100e541040500305c0c907030b42c0740c2d02c900c0d41d1042560018110f80807045401d00107a0000001c0c01015a00c8203065221103000000800041080e0000c0c41000211041480140c400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 275605818 1250 275604568 275604577
    0x41113060e010908100609060801020c0a030813020310240602070504090c05040903090819020a0b031503030c030d1104060c0b071110060e0a0207050d11031207110d090b 74
    0x3440c02141040708400125036284040d00014181e00400240910440182d400901100d4005105008465840e0f204a0803401540303891200e80c0c100d01d0100c00040d2048540581c040d0740b913940c2c2c52400c1c3e90351700800c0c43e100d41000401142592116910304180c0c03429810328031400c926280c5402c107400d00100a4580002d845500d011b40c0c6c407200c030902004071300007844000c0c08001e0402c01c418069810000e14031140c41c85006418000c0302c00031804461121a502152a0043c040c41c071024540004007003903620040030380c004005041d04d40f400c0f503075040c4010301c08110302e00d00554031000004024000c44200f03142800c00e18001f0881002056003148610f4280f60b084000320350740d69103410781991074405908034802980501c5806080c285e08aa00110540b01c0031000d01e551036903a808803004038410203002811a510201c40c000301d091091030324005841c22002504e04122240d600c06000050543d0000041000e00c052945030020400644526110a01d0003580044c644103155165108 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 275607068 1250 275605818 275605829
    0x20915070602040306090b040210110c1e030703150c0206010302010f0e01020a08030c0a080901050408070f2a030302060603010b0f010f17090303060901060903080d02160c03080405041113 82
    0x50106044007807000a0781610015500b114082c00302141515005400e200308403001c074450200700c04c1c80c0000d0341c462000070304100360306401130003a502050100410300320001c4200d1041094a502c102060700c1c1402150000c0d071152004074132003800c00b075500c0c0030b071000b422000e070840d40300400400250b80d00c01034503416803ca07410088035501040300103d0401c2004080903000d5100042400b26444503080100345908180da07440b1403640340d01e103c0c0c5090751015100544801c0e402e01201c0d0101e40403409024909214400403004400740b00a20f44640300030301c03d281203460740ca040400030701d070b01480038036481501203000301300c80d01214002a8503002c1401e801c0381040448010713940c00170301030795000009409890410895140500c80c03503a0340d61007220f00794060383c0100c000040980c0100400c0041e40e5008521038144030500856034000c5d004001801e94580ea4003084001090191926a0145000320104c41c0d842d4100400e02040e0740c450400703c00001030402c9131902c0102030769000c0d41980c2 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 275608318 1250 275607068 275607109
    0x90705010c11090403080603010b04050408070b1f03051f0c20030f0f03010f0e1b131206090203070f0305030d0b1908010e120c030316180308070b0a0209 67
    0x801c5040107003240440c40c00c0e864018080505000a05411281c52403044004030000e0001d81510400d100c00d9800c00d44006040c07200510084000500400905500082c05100002829070030300b00d45010301b056500c20b941c03640008845004c502960401844041d4440a0501c4440040b040041c0001580d034200da121880c1c440140781622010300c101c51108505060450700c0e103c40d141240e686a00a116098003128900c2c0005240c5500101a034480e169816040c1c0240b91604025003c0d07500214414407142d0201c00040f4141800c05007500005014503400214543d2900c14140740407103a420841f1a03440006042000441c00800c480d9000d16040001c20b09869410110300c5040c000c41c60008214401c550100b00440d0561000f0424054502110203051204500358410310407105080040e410030800140d0b100e48401d5440e50400c03852070611500c1560500401c4210801d4000b2182c50100240440a0104551075a60820240041103141000500000e5854000c0b44122140706 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 275609568 1250 275608318 275608337
    0x1050d120e04060311040b01030e0d0518100804030e061c090501020d050c030a0c05090f040b01020c0907020c1f08040201080c0d050106090611060105150c0a06240e09070501 76
    0x91080c00802100100070b0401d0040ca5141d1514070256080700205900851400822130740c958468000e066001c100d90300a0f00d43d0402c4034000700c0e015400740c0900c0429060403115480541c8074042003241c001301c42d5450071802d00700340c41c005080914944100d84100c000b1b00503021419481f1b1001400d1480c00140010304040610340706029010b17440754812001d1501c1c3c104040c0c9007903440203602c03070700d1001020440303121041c1050f102401070101d244e8010008030100340c40d80c1429032140c04400d10500448200454000c006640024112801c40040c1c126419002c1c890518885103280b00b04210b601c0a08403402e94401084541d004001078104a000008180084c00c0700c000c030b440004070854180f1542d0f03107170742015281e4601882404005100c42e900c0e02c5080740042030440c1a104000c04507100d05040200100c80c0d03420000c1ca4200034050600303180300280b11442000d140c0d0300002c0b0340d203d1801039a6583c5008440c1c9522600464208000300840c0610108000302610024240540d14 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 275610818 1250 275609568 275609603
    0xa0807030e0c0607050f06091e070b0d0902010e091f0501261f03030806090a0e0d0f031508010510050d03020303061903060203090a060b030a0c0e0403050c060415060b0301050d 77
    0x344a85c02246d41c030980100405d0150f103501c007086100104840345c1d40090110303141014140e42d200607115008800b0010700110100e1f04042c0c1000b4011401490b10f08560348440001840f4044107540c1002655142c0c0c1803000c01c26036005401c0000c2109007060310b0707550b0466440f00b03101006481c1c014080c07226000040c0d6050201e143d00f4000c2410b1a21200b086901c9140192100030241c90551081099000041c004404d07030252030414500e000150013601010001a203a08080300003e074203054a80801d1864404400019401000300c0e0001040e02c2c01c0194031004020816000b0300d0103901503200c0c2e80c0103e0717000400c482e000314040c0c400d1124100660031402100030a41c00c01400180000103001880c840083d50401c0140540d40412005c1c0d2010101aa02c900d4030000412444c018041041040f0300200c4255002340603041062404000c48100d46c140a000c81c2c0071903c00b400b1044c481c00001d603a00c41c20015015130b8018a14650500317001031242c000c0701d80024810225142640c44 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 275612068 1250 275610818 275610823
    0x307080f01150c0803040f080c0a0b10031e0302031b060f090303070c0b0c0f07061401090b010903021c1b0806060d02091617010b07110a030f03110f120a0807030e0c060705 75
    0x1040e88c0111002d5107034030400b0f280548070903840c40155081208a80480c50800615100c00d0481e50701c0080c4007110300345800c00d0040908084c1055082d0701081c4227450303080d0080b03031450008c2c9410001904007407403e4101a1014400034003009081d40c8107008004443e0342140d070081006800c51010308681d5100c8203405150300c1000011030714428041005800c108054000316102c010850090b00180c7e20380c05c42d00201c1d1044581c2a0028480703038010009810485e9281107020394030465000c180d00c0030344035020ba11041c0c1c05030700009410040108114201400525000407088483c03158800d031a800203070103a1b0700030340010312080a005c000350600340160950b0804070010030500c4e03815a075400e0103150325007080d04190f03108204080c0030344141c641110420181d0383d10010f1041d02c9585501d04035044451280b28034010f11540b6034001d40b6180c00c02010340c0c3c04040b114000e58641420100030540f01001d00285e090504008002d0101d48000ca03c03000f84110a943c203031341700c11080c10705c10f1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 275613318 1250 275612068 275612093
    0x80702060a0c050d020c101107080d020f1002030c0a1b0b04060c0f03050c040b09011206030b0a14041703060303040f031b0807120204110904020307080f01150c080304 73
    0x394425000220948065048101520024000e606a408000041800380d0700d8006c0b003c0015030020020444204941c001d0080c03039407c00a10f0215000745031925200d0380b801410300d0102002d40d0018002407242901048400c210f1446003100358154144642c0001c514000c5005a1050141000a41c0104050300c1da0503480b0b01d801040011240c02e203814003c00078600080c6100001361086440201c4a00a0082d03a006102044800345003030f240114480e8180c000814a03410013041d8203486000403020700840b00514015607a1405600304405240102c41001c01c4003072152610314108004074912440b8640b041000210b02640c90340c82da800241940300f96006080281e0301c12902100384180740c3c113610309001c20302024030901900e622190f5661000c1d4881c000c903c0c0524003d02c401030506422000c1c80401001c0030500784440d45001606a070011566040000d0f608410408003110400c41d0364010490300ca054454841000d01c010035040d4100400350221030000041810410780b016980e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 275614568 1250 275613318 275613323
    0xf060203071203111305090106110322031703060102061503031801180602010519061511071a0d060b0f18060c01090b15042c07150201090b0c03040803060d0807 70
    0x2d69840c910b04c0605d01c1e0000c02806182d0080317214000120740346002d04410680820408002c600344007014903141c1d0080000c0c0c030200443c2c00076a0001000840e501c00d51608100070301110358407031800c80300082c074100c001040d07034501e005841c05020090b100070084440022501082d04402d0340c0300f030300580301161200591100587d4109000442c0da07410f50020b4001d0031542c7c0c420750003d10ba0511801034034164050415088840143c1040c0e01c1d000b0501101489480340c29241d0483d0f80e00020101c40c00c01415070002c1d00b00004400e40e411925200300b00113014084041803d1400c454460101030164445d508240d03d0380ca4000c21941c5d0f2010181c441c03038417080009010b440b0040c038100320841c1003034800060032241601d000500340b516000d181c0041c1c1000d280081601280c0480850031403c603641c01c1058000d49002144101c04074039030700e6000c590764002285031580c078580355a0007140144503084540080c0240400203003580e007125046581100c0320704000c0c0d601d08004030341e40b2170b05600 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 275615818 1250 275614568 275614601
    0x2010b12070501140306180a090602070c03051005090d03090519050109020108090a390b0a1d0a27050f01030b090f0a08130302091f0f060203071203 65
    0x58088100001000002da41081e07070b401000031090700405080c2e000030b07610035601c1326540d1801200401c01420441e1711190305040410002c1443d190901241e00c005020744408003040018018824100800c2c0c108800302c600406c031518046c20501e403030322658907c410406845408003010b00004202004110810041c402141051441c4c0729000b0f0400508c12070124070ba40000914500c404518030001513008038030400010145000c28010088141909207140d260700b01c0e80c120040000465405405003840103591403c28110241825240e0149a10000300e40e40703203154151030798000e103000c51b20a0101c0d40d086882d40584060300c40c0c04039100311000c1d89001b0400903040c4e001003243d03048034040c2c10103032210707160310400540340e40504000d090280d1180c1004000200000c00800e086283c0d80c074130b03001c0d80b5101e500041854109488400001c4500d08114410158402e503220040143c0b00980340300502d03081c0e01030348902401c00c015140c02e030607603e035105541c02038100b060002400c442 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 275617068 1250 275615818 275615839
    0x1d190308031f0605040e070c0303090b1003230a1118090c040606030c0518060912010b0301061401090e070905040906020c1203060105070807140604050a2d060c02010b 73
    0x240e82c244400c6461007841040381c00200044040c003030012a419580106480006503843d144143c0d12000d40500031401c0542d100720150210f81c1e040c03446c0c0c0c002c0812a03018070b0410302d10304000c0c04404040c030003041c58100210030745c280301c0800a0604240781d4050032810802c24201c0004001c0c00c20343c01300320255084041088110070011664142161040b1401c2010310f440d28800c0303007129048501c25010500030401c40150404003c80091a48001004c05e8682440c100115956111001002909a4444400515a240a0080c103010341143c220311402540308800081040c0e0440c4144c04007141e180d0081440540f098013280c0c054440540107008414003844c20710000d510406840107240501040300000010035000c690051070b05a40e86070804c00d054803140c909a0110200300d03034500000e0041000488203000c0340c0c1c0f0460140014042583e001c2c2400c0d10740780220411001101c000e940d204d2504456086545500c94204d040000d280300700070400d1f401004c90000d0719520804044 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 275618318 1250 275617068 275617081
    0x70506040308011e03081b10060f09140402010212071b120302011b140a11100203090d051c02031305060108071509051305040f0c1d071d19030803 64
    0x401e514101e401000c1048255540140c1ca00d005940a020090540740c0810006400c7c2c06011000d061040102082d60900807820180303104861290380a1071400b82811020000c4c40c1031440f8204264080f22490030076440c0540c0000e44800049240004003000459540240200c0038207100b1802c50760b142d00c013510340d07c40c070758020805100f903002c40c015800c041115910403515143c80c0c01c1d00e01940c90b543c2c501d24840b00134188640100c900c401c10030090140c41548000104440c2e030359010300d02c03001a5a824451503240c240003690074038800780481044030140c0b4000010803800141c41da5400107032241c5910010808042e003041c0c0250192040c40e001145e908004240d4000715042c5400000700105100400d40c1d04a855210b4142d0040c401c1c0440b990440b00d640019a100d44208444042c10300582c1d2440f10420854000d400118003004940b00700101030001c0e290802d29074140b442c2e15841142c0032030030300216411064000e041a480201160381c40e8200d620145034401c01b419100c0ca082c1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 275619568 1250 275618318 275618327
    0x21110607030518030a020a0311030c10060f050a0608060103050a0204090e06160311040504020f0405030a05071a090d1403090d11030601050f0112180c14090a050603030703140705060403 81
    0x2e640c80010080780f000450740d443c000004881e8412080e801518543d0103680742034444001d4072040f61400d0004101c0009045020310841007001150034001030303001e003091280342c80042c680d00b080e401142d0380042444403680041501e60b101109103008516561400c0d0300340041c4c0181d610000f421410315030064240000800c880d4820b240d2100e040c41000703000a002c80a5a1171980c1103901040100024400350a00f0b4004100c81c0b00982c40003807400d0b5032440032a280491081c0180d92942280c1c4061010701041740007070004c000050012400c04032a2030000340d0032240280002d10081c60302c0050f500e016014000c6c0e44035a0f00080000300f000242e81041100400342e0452580709000d0032002181c1c40c9401140e0281640c8180d68190500b1100310442000307008514846030780e90241015031000030700d07068840024140c01e00700589180030a100340101c1100250482e40c8050030702e0104080342d2000820b43d0001a0540740c03440032044801e0007403100748240303e00580540120002c020906800 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 275620818 1250 275619568 275619571
    0x20a0909150b0609011b020301061e081606050301050f0102071505090301050606031e040303060302030304171b101b0f050105060a0e04050606011d1801060318211106070305 76
    0x50001404000b038940c0400c0307481d1080305040d50100300d4540700c1a40411110354002c10301e40c800b500010780300e0f4503920481d0880000c1812000100d807c45028801680c003485100c03540b0319205204883d580c24181d004e401c40c0014040d10780a15840b0f42e16901c42ea108220240080c100c000c581c9010001c01c20005100c0d521558100e4000d6003410007044c10b9003040d000326440341d02d043c204901303040700c1d488802110110103030060381050b0f00c0703c01c04070169034140010700c000c20141c4400c01c4001c40c84014207041400041c0310005c5402040c2c80507400c0e881d00c42c50790031100401d182154649071000b1503d1312810010002500c100205650b142c10804150300081c003490007110407045640e030347d2400e40110202142c0003800768006c200403e485500400007886240f40340c19034202811140c0006c5001400d08240003041c03030428030300411205400d8401d031000c00350000d100405100094540445c8280510b01c1e880610b0710291100040d02c0c81078844441c2c0c910301c0c80a440f62400c2c91403004006c0c010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 275622068 1250 275620818 275620853
    0x2071208070914060912031306120f0c08070503071209062301141003110a030c0f02210a0c02060d020d2313031107061805040509031204020a0909 64
    0x20000100c0c4100c900f04540c10003c070300034011880e20206005228035a00c0b10030001080d03110900005e2000c08022440c5001741106a8034440e86000c010141c0040c1e400c1212100740f002e1900044803091036000528560201c0d05042880c0d89444400003100c2007440b100444148500c1d000484d4100f01e916004429003140800d095070600e04c9803190b914402d0000e1140d03a00440c810300f28185107041000c0f0074400152503040c0041e60b01d040f100220f10650207a1040e60019540e842071018194000900c407068030340702d100411800d0402e0b0a41c0281e0034504080005e0b480d004140091900e00c55840550219400340140d0746441c14500f100c0041e4100c0724170100e80500f00802004460f059510000c0348540e0408403000540342c00c0c100b07500394a105207080e820840c02880794a03840004015260040007984d940540c1400e0210800b044808141c01541c4614101403c0c800e0342500082519034405050520b02000d403079900c00604a00d1143e80f04502490070600c018040c0400d81644102d20724 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 275623318 1250 275622068 275622077
    0x92a040c05040602071202030c0907030902090907051c02040e030f04060806030d05180307030215070203010b040203042d05010603062c12180d1103100209090c0903010207120807 78
    0x44004040e01c15010300d0240e4401680141c10402031405441c0c2850611400078090310024400c51010030750720403088440001007070703c80e1160802c600304070030050ba10055480140241a042a00007130001180c514040100d9008a01c00d00542d03039264803403001d40142c80304486c1c2d184030034480140c544d001845000080f0740b40c1030014000c1d04004c01c0c08103454480359102d80c41d011702c0d2001c4034400602d800c099601845000400b00068030b48008102d0210039100e0b07880e480e0a0144101800d5800752402d0034016030052040c403001624600342e00070000080c1442c11300f243d00e4580f245580140b041000f43c940e600700b0700000240911a030003a120034414200e440078160307038884074000d145218100c2424580c401c243c102540d0040d0405407011003000302c0114400e40c07041c0c0008904003c10300c411b9a464410080c00840c503e0104995403a1112008080d401c10b141c030710020741c0e0000010400c0c1d052040c0082c103071a49540a5048803005a030000046001310030440f401000d4020480740740010a = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 275624568 1250 275623318 275623331
    0x6040312050c070609060b0a1e0b090d02060f0c19032604140705190e01120803070f0e03030703020f070603020f18040b0904030c02040614010215092a04 67
    0x5440c54060103101d240340d08071292a0800d140e841a00030649207805a800a988558410880d96600680c50090110316042c24440001d800280700c900740315404408040d204000d0b0001c5500c40c00503101c025901151755944480c11b1014640c0030748100c0b0b0482000d4041d2014051000c210080c00c03010700c50181e5151181040000000e8544200020040c641100300000290014044644c803c9920840000780d9480980d1100071a0344c0700903410b48207281441080b41030003441d290480c414018800e4121000741044161250300c00f80c8006040882008441000e8104860040c0c4a03004801c0c0c000c0c0c2201c0d51400c05060007500d4034068a0189244e000da20000110307a4828029121100c584600300740c9841001c03018481491403000301c60343c04c161102030703020032680c401d02524031443c0070f510f400740c3c18070143c4104000ca0b000c6803c102c1c0d20000364540b4442e00e0740d0000e1800141c08000c8010546030329a007403c5860b1421005d0703402c1c202086207250348003107150926113a00312102910107000303c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 275625818 1250 275624568 275624597
    0x30b0a180809310c1403191506020601182906211501050a020c010305060d081201090c0516030503071206181a03060412110132070e011202040e09060403 67
    0x4140507461000c0016070180b02294143c028000600001207a804000848d04001c030b0041005109603480000960002c0004012640101c0825443c0c00c3c80c82c80200b10400600c400e0340040308001408440170b02140e800c17016261140e10481c0c489000b441c8442e0b1815407100c582c036403074503412a41984244001e5064120347c0d40140d0566210703140e607401501e00c1d0304003140110020000103003469803002e00041040c2c0458442c2c0010000c498890b0511010307503062010403025074aa00c02e20000701304080150048100242180240655052912959988421200700c2d01d8102c620700c00010280b8001000600d00070382c1c1c030b250100030f03030489082c0070042c445510f88220035140d01044d03404d50005c800150001d010000c40410b1101c05081217450310707400d42d0040b421640c003c01d0030403c03400000700743c4440030f4402a00c10200402d910f15246103103040702c401880f100c1c1264990381881882e07800320700c100c0c3c683e80556000d8285820035000610380030542a649020540d8150081464201074690 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 275627068 1250 275625818 275625827
    0xb091305011a0f1c06050a0207030906020c1e061309060602010c050c1507200601170a1104021317070e1803030708060d1a01030b0a180809310c 63
    0x20b11100070544001d91803518280961003040e89100141000102000070000f0070501c42e00d0b000d00c0400c1e40c01a02d030b4007940f402401d0300113190048070a5601c18a440c1080d952040081c00d04002c04240200108403d0000725000c0c0c0075601b0880b0340d90400c0b10011600500a038015003c54180341d00904c1201c0321000c056400e80301d007980c42d031f440b60040300c2105a920500b803103d039000880d602e0a0100c10140c050810101d0804030510303136040e0003c900400045280d060154180340000016140c0388156550f07402c03100c0d000c4c0d0311141c0241d402103a0030803241e03c108140e1008242401841d000700a08918842d15105607000c0d40c002e01c4456808248a824808003001c628000c010080d445c0d03440d520400d50b40c905000b0151548444070905440014204145407003884803074030f0290f00a0350461612a4000794001c040d90315040c0b404100e4402600c503150100011608051125910240c4002141c00d00d0110f00d403041c60203500c0d21024035440401da0298800203600d042c10400701095070001c48 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 275628318 1250 275627068 275627111
    0xf0a0908151927050a0209040803060a060528020709020c150a060f0311040b04110a020d030e070302012001020309030d0e0303100608090c03011b080105120303010e07030b09130501 79
    0x354075500d00c081c0f80a104807a400030500c0c05025000701c0d214900194005480c0d00707400c4804480501d000300c1131027440c0c02c00071168005006541000e5090411110141002c03039401003400c0042c20024400804550080c03001c1d2025002d03004e811355071820980b0f4a42c0e9507000d04c251450ba41001c1c10005441d0220750300c110300940d1103030341004090500d03589800c4400f16180d03944540c000da039201c02207900c0d512482014080400c01c180d5540b40e003413103480682805d5070302d602e050a03d4100141007400d40400700b40d44041ea64242484118109441100031380d2050301990511550300c00410300041c00d40020140c41040000e00e030522803851800006912804292400d00034041b2003041031144500402d03440d944107503c83c0443da103406241c00084e003550a600544440162040e4501040550004026000d00026254080d42e40b44c8502a15600c2c80144500e2a4460580c0301154074548260466603060034000c001451a040c083e100e800e038015120340403031300c661130000800010403120200c107 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 275629568 1250 275628318 275628341
    0x20f03060402060403031d1009080105060d0507060f11071e060c03052715180901050f010315421d010c0507030803101a0f0a09081519 59
    0x11300700303031039a075040d02e0800f010024440084403042004445441d030207001071044050b50358505440d860508510f00310303100609a14018102440d4a40104000040502c201c5815203400c0c80300c40018041111902520341c0c45548501401d0000140b1010640c0c44020161079512102c0c00140d031104240c4015081c29401004114140080151400f60741d02100d10103c00c0702842c01852100784c0020300c02648150501210403000c904043c41201015050b01144401c0c0c2c0e0035441941010001076840c207062000303504268480c6194441100c0c804064001080c41488618004d01001000030000c0c80c00a00000340ca0544a04c81030061f0030b21003450f150030065110511407203280004100d19000c000c0400d81406500209000001e108000040046008804007a242d00f041c1c4059034003210302d54000000d090b540101c40000c800e55030b048902c48032400469a40e10140c1d58811303103601d04a0752040700b00d0302600c1d415446021a110065214211002c0038505c44445050391504032074000740032 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 275630818 1250 275629568 275629579
    0x1080706110f060a090f230d0e0108040f060207020303030c040302091321140c0307120203030108061503010b1005030906010e0106051c0f09050d090e010308030c2a0a020f03060402 79
    0x728104c04404c1c0d0182d0141802501c00700894036190700e8000700041181040001d09004001410a900f810301900c6880034142c5030811215404000007010b0640140c0058055802a1100020882e650341191a840e5024055076101c4c81e11010541040d0410b110903401003062200180c00ca42450b0700180b001540100c9044c0c1031080e490300350382e04543c068070040074400d2502c18055040202400380c080520381d9001584d860000345082c4841d10440c801c504155402400144081400030074247d03400501c8042c210b44c0d8032902d00010780504580ca01c40c1c0c0e00269162111041154010011442814102d08544e4a642c3e98000e502113018244601c10015009100748644e007000e2648103103245c9a1311002040741e9401c42490b10841b00030142c01ca0b0140e001001060001d5000f08411000304500501d14001c3d40c95070310382078854480280040410703100080e2400c41001200910044044a44103a40d805120031301c2c0b0741c0d41d440418500782e1080c100c4007104841464009181c9201301d074080c11 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 275632068 1250 275630818 275630821
    0x1090204030c03110f0301061401120c02060c0c011b0804020f090408180607050726011415040e01240b0711010813050a0f0c08010506280b0301080706110f06 69
    0x464603144001c05050f154030070f2117265901081d603002d0052901425884145400e01d009a01c00500f200c0d20200c4201e200038145220a038000e030b004250326510221114036290fa8502103a2110700600d02c00c10045050401c8605c2603410540c03004038244214030a58000540070340c0c00c1d08120090408a400405d00300d020001d2078910504188843c00c00c0001030046801e2684036a40d1a0400d1181c1c0c016114069a0f540071040a8040d481000c604607102030003007107403000100f4080c89225005000c211600104001e00700c7d44c0c2c843e98003100310060900002c01c50311480c0390a803080d00c1340601c41418202401c81e404a180786600b401c40e01150780c020b0000911100c2c440040d580e2034002404200c003011111440c0300030403018011040b5503440b07011820110042c42c917040c0021240d94018042a84c0f40c80c003009043d807600d5102840d01450715104007d800c101c20001543c008154221040e19240072000169956002807444141c680d1a110060410400450340e5542e900c1d500c900c8060394000300 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 275633318 1250 275632068 275632073
    0x1e1a010809161509050307080604110604031703040804030b0a06030606090606020606040b0a03050a0506040302150106020307170c010e0a06050a09020105070605070c060207110a06090f0308033c01090204030c03 92
    0x7464141c0540f040c00c008102c0c41e03450002a0030135190b07030b001d50140d0704000704100401000c10481c2c0c5562100700e0322030f41814210780310f510003e801c03e0300c6013807500d00c000080380c00c1c0b064250645006550001c044031261030403144800181445210494042e0300b083c42c0400d01a10740e000340000d881840d401441c0720b0b43e0f603004200141421010302c54000203114008070101c9c4041c0040c0701030720701810091034a41010b1800911f00071241a00003a0400c032035006100f41640401100e000f6a0000c0304018408800d03044400540305061455030290701c0c0c00710103500640d000c101080c07028041d0b84100816a2000c004100350ba0101e60001d0000d80100803a10000308030b580300300c0d002400c3c0d25102e08201e906a81d020100d922411040e205540c08152015961602c900d0f642c1c003500c02441c0c4401c5a80c1b4002851540c10700d01c0c0001001c91a02000203030390140b41c1ca050342c0a94040c0c3c0303454090399003c4006954a540c1c040c5c40380d0684440f0900105840d0418000c41d41240e40c40101844102c1c82c0d43c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 275634568 1250 275633318 275633339
    0x200307021e072709141b0603010e011806051009051206060f100315091e0c050906070611030109090b0f04050c0d0302011401080102181e041e1a01080916 67
    0x1882d4000f0407961207254402280c848140c40c084000807000800c2d86200041450992803410900c4034816034042005100805004148904440e50310f00c20459920864500c000030f000c00c0c1d086190448080c00110508903884031000302190760641b40700c00c031420300740f03682510383d20125002604515010403501c2c3e141803440f40c4206000b01460002000034100c06a01206030341d6510042149460381000c01c504010400381c00410218204104a0600f4091000d0441d00079480014868000400d004c414000d0030b400031011030400802e82680c80d0b8403072040c0c00003003a40c103806981040a500005210300c00c41482240141d406c040100014a02d00c000c00204401e180011801c6548900404020380f444640c03c1d03000c1c010780b100241e11840d410310085403d8102d10f0200d4850220081d10320601da0280d9201d404000d41550003003548580950708954800700c00100900b09440c11081d60040520341042c3e8100e54400d903256401d985a01241640c0c0b049044084148001580340801282148 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 275635818 1250 275634568 275634629
    0x190f12030207090c030504030e0607030905040b06070c080f070f0f0e1b130911040e0f09010e0604050d080601050406120b0301200c12040803030703200307021e07 71
    0xa8030454500030380318620032054940403030040d00440d0b02c41c0c062100702350300000001208141518010b061040c25280103000c480f151080d81c0c020741e41d4214906050701e40404540240350062941c0c010156640d1101d559000020700040383d90081d8030002c241700d201510340c2411900031940c020140c07800c0c00313900d01103003d001c1c040d103100b510300085003014238800d00301410b4004064045285a10310b40703c6290243d50080c0203541e6070701400c00040c40010044d80c081c1d50440400c082e20a21a60351205007401072240b5211913401384103402c10401000000911180394603e00d03035600d40652110300054645001da0b00404005c5600000681c0300c520071a0300514240e00010000324002003102d20701e01c6101203442808003d002c0005088610010400c51000340e000300300001407409141070201c07070f120b00020749100205070311114804028181c00404d500101c0310030070303110755034200400044e5032500c1110180c2158051108090500d000210301c400858100d01f41405504052081c80c8084550 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 275637068 1250 275635818 275635823
    0xf0e09010207020414040201021c050a1b050604080408010c0302121914270a03050405102c01110a03080610020304080102041d100503030f070809030d0905190f12 71
    0x1424050b034005130b0341d58080c0075002d805040b001c045604050000a0400701c46030710302d9001031201ea8000d034031194042d0483e040c028141c50030508800d620b4004000d486520b480280043c07040303109010a100c603080090044a002100800c03282c0445135040d016806900071403e499030b20030000507089000d201c1c18482e550f00b0f200001580c1d0a0f101d03508040c0704001d0b104402c402c0081c500b0314014100441c0c5071011121101d0080c4034094056400404034442c0e8012107003e81c4884803118200c6005032b204c160f40e480201c0c03c809101e0030480c1c18005d520b40000340d060004590180f0241d04032804103500d40c4031a01582c0300e042a998010500138203952a8410a003148810080000c8210007032015001403d40554086c04505140311031010304d02015000100171903c2c2c14080003240e500100700c2d001079001100f110344801c41424113026070b00508086075050302a03408203070310140c1d000c68880c003510030031581c4801d815800914002c500030b40e4091841560f011007024801d80006820505c201403 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 275638318 1250 275637068 275637071
    0xc01170a020c1c0f030e0705220f092001081609050d0c0504050708090a0318080a06050f070905030a08030a0e0703140607050c2d0106030305030117070f0e0901 70
    0x2010103080502d0040c0143d94285042c035590003552095a10603100b0340007140c00e19007030080441034800291a00d02510900b8814100d410140c044140e9060080d040c5080b20041049205c01001e1003601514074448106c804449140500c5862504404801d070020010b80d540f40d500c1d600c10702c1003417038a0300c010340d19014490411400030302c0fa6204882050b42500c622200c0c241c4501d0901030005650003c1e01c40001d101026003001200940010fa9402c4550949031180c050402c415079010302c0c603211341186102c0e020f00000d000a020030303078105034040d506900e841c1859650f0400100c0d00345000b40152a81a04424007500215000c1c501550704403014032000036921102000451034041e171540101c0320380b080c0d010310001805061003415400b51050901c01e240a242484050b1a410b0801003920003160700542801c81e001140e0804058178400b4000b048025280c0c00d000c0d205801c24441c090300d072141c88511590f007190202e50765040760050b26403040c0290401b580c514005800034083c8a956 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 275639568 1250 275638318 275638327
    0xc0a0e06040b0d140a020933030103050a050d02010b1c1a010e070207050603040305040e1e0106090e0c040501020a0b0a09080301120311011a0f0d0501020a051b0c01170a02 75
    0x14404800800a000f0310f01000100504c0469204586200042810400c68410b204410f241e40780c00c07854400841400300c4800c801e8022502c00c208440c1000d0a4403203040004c40007100b0002e000039040c0255003d00d04441d29840455002c900b038070b02c00340f240c0f5003040c000844100f00c40c1450f010201007905c1030003003100d02a01040c203800311a034240d200302c0d0954581e0080c045419014800d08000c3c02050300c0e66807541c07134203440184c1701c2d100e503100c5ea90047d03010384001203c1c9840b1310403032040000300803689452035944800042c103d0340c550043c203a0020620000c90718124060084400710382043c5c010382400c0c1d0094668109404005018000458889200c98000780c82c020046002c1c09060780540e10001d1b4604008010030321002c10880182e24284043c581100f890003030102400d001c90304078420300440c001040c0c0e090f0318001c0043c842d6002080d0884403d41240242101600c040712090b40640500c81030381e604ca40386480c1c5400308042620310300340240a101c0c9550702071002840035140 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 275640818 1250 275639568 275639579
    0x60a0e04050703060501080f0c03011403010f1b02011401081005093a050c0c0906040207020604030f050d23131509170f07090f1b090306140c0a0e0604 66
    0x75240120342c0c100000341e85a20030b014540e0440500c503080128800650418589a0401c0081d48018040c0e00c203c4010052211100d41c0c09401030241c1d03240300001400142c040c2c801e10a0704107544103204015500708150021184800f200d210f0403101240e004005110301c607884034008100141c4070031301d9401174604101d4981c060410300e403402801e68061542e00c005035821510806051203594040207800c01220140210004450b04a050100c0382512251a10000030340240f0488800a40080c404140002485101011100c5441c00f44080c0e60b0f0a40340041e080f80c514400d01d415070364007415006080101c41010700507003490250b07001c69059458603081c3c50401040e800382da200008818050902100d0308001c54000001450740c020700902840000d92901d82665000b100ba0382540e82c0c400e640507509503003081ca0320b4000b40480076010440028000d061140e030b404280d5600e1b0030b125a01456038140d0100d207200740d180017440d070f04142541d50101c0d607020b0502001e076803001050001046 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 275642068 1250 275640818 275640821
    0x2061e04080d0216060f111e0303010f050607080304120e060711100306060203040e100b03010f03060506030c1509030a170403030e09010323011b03020703030b0a080c060a0e04 77
    0x18010441c0202100000150001e141203040c401022040c502c00b01d082229581006203030304100390505016400c900b01056103417034940c076480840340c411640c04803810b0082c0f0200045041e1010f200c0390a070095155418041d05105010000300004400c10019000c0303900c00b101c2d0310350b07910285003d10301c840c6650b0008559400007a000c2c1c40181c0c0d100400c03200b5142046119508000314142407001074034081c400303500c90089104840b50601c8107000200d555040c112100c010307080c0c24070469102c1d41c450001c2e100c0140c0d00d00080b10041e02d044041110340c41d0018440d02e0362100284061044540c400480b08144c220490460301407064460510025598541d0f85548245842d1807549907891030030000c0044984440304c0b4040e210120051000c201c80890351076a0b06501c910b0658543d800922281c010402013607a03036008610040010000d0390b05030000c004060080c0d4050120140500c100030302c030750452141301142d501072101c1c0d03c082d051a00c0a05007400c1d05090011503d4030301e001150 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 275643318 1250 275642068 275642077
    0xf040506030a0e010b0a08060c0d0209040c05120f040f150e1b0f04090b0f130f05010903171e090309120705040509070e190605030a0c150c0b0402061e 66
    0xc0158446241089143c001d03c104d0741484002c03035040381000e241800e000d84412014043e250380300300004404203204000e404540d680c0b100035008122400c1c034048001c01c5604910415108600210003242c0800350060145008940161901080210a5270340c0090610070842e05804c41d034403021b02c6405100306002c1081403040703050001800002480802c008050010a524851440c050307000002c070b440068040d600a540c210102c0e0181c0b503841191201e40003036a402429030884040403000c000303041d04241c80b442d1098a075400b1010869081c009401c2c421180083c1480846e038040111100b2011101d0f000246001624a800550300100b109807041008521903603000c003004003c0c508207440741e95400015540548580303401d103207078903150480103061000803034a240d85025601d0003652105000b00b5006046802920141c60400b20811076481043e08680c0b0704011161b0f010700420b440445154012107001e4155282e908004545e0810f003e000250060706001c2040301d4520802070 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 275644568 1250 275643318 275643331
    0x213091505091e01030b150303040305070e0a0218041104080709050f06060a0f0e06041d04060e010c020d21090312050a0c0c060c1701060c0c290f04050603 68
    0x405500d400c000a1200c9002c018107021121542c44501d0102d074240c2d80341ca141540d502074411445900c881250400303032441d18013403035810301000900008000340024802d00303d40d801c00044070540c1c9c0b075680000c124010100841039017600c40324012600c0ca40f076804600c8044002c0c4600b41042d884016a40c54185036801c10801c03903982e00244403c0200c800b2043e13a0182c0c044404030726041c1c01910007041c07481c5103103000c010701942c6050310007940d5801054801901000c04440519030661880300d0b440c1405480c2980c2c9649000040d0b40901d00600a6a80e483c800c0d80080441e580d0030901141d1201c91540c0b0380030b9aa0300500c0300c182038006c034040e04030750600a581e1144110428a10700e411181c0c0a803910140520380500310b0764043d0071134060b600303454015500003032060094105440e013030140c0203507030400c1c1c0410001254490300035014010190141c0240200c8a880e000501c13500c41040750003c095446a402e480007411440004110001d1391a003030034101a50f2fa00400ca42c0d402c00c1c1d0b101d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 275645818 1250 275644568 275644601
    0x708190c03061a0703031415010f030207150911010c210314040605010518010f0605030702031905130605040e0c070821060f1c03030b010c020303070b090c0108070210021309 76
    0x42c4c245130b1301d8000c134a81d4012100f8100b2440c101440052140d00c0c0d040704050600c1300c0b0002c9075400c1c501950507180180d4001b00500c400391704242c0701300c00900782508200d60100c4200d110302e001d940308640308004c1c194000d906042e4140c4425860300c1d1700356040c260404040d280d8600705207585200034610300070dd100e20004103055052204006070a1702c501940d60814205c1c00c0100300f695240b0410104554480c140039503a621414000c80c110310030090400780c0110705008004c802940309004102000700200e400d1801070325580300b126548a00d10501407041265004501c4246645008114091080030907a1030900346108044610703980781820401da01e5141c040060605255004e55000c6c2011501c01c0c4c400c40429407440901224003102500309070391110402c0d4541d026511440200d60020200c0c0d4a48031245002e2007154070450f0104141c1c096845c4c0291154041c401d0f050081080f60003801c000340300c8030030110094000580c1c130704075200c48543c0021601803920403084903558a080 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 275647068 1250 275645818 275645827
    0x170f010e0105251205040f0203030a27081e0a05062802070206030f0a0b04021c061406030f04030504150c0311060615072105030901050708190c03061a 66
    0x100c80c0322540440b001090b80300358401c0e04003c2540c07154202400c09001100042c8903243ca041c41070703c25804100080d010310000510030005a00001484080150403000b400840e01c11276100c001c0960714426149240d005d01002c6045c4d2940313038400214820030808880520070389443e220301d4080c040c4e8018a050440c082410803108400c2d16854001086a105601d0241590b01040c00c034840182403030201d41100c000b0034400d00d2140c0203980f0201c0002d1041d502d40e014001001000e800750349044081c189011800a00564400c04400c180980201140e06503a64105034404100d0014021010050300f08070202d2001c10180c40340d0707141121551041c0110309607241c007501902c006e4003900d1090344410100040c0b0340c0e0300820050003030115a4520348580c01854050080d421102c046a20204060009000c0e00d901501135841448104001d0049840ba0310342540c41040c1070328000a40d6010880b44100480b058100440340071135845c0c00525140c1c0d9401100300c1c0f48503500b00b450440d80000c4d = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 275648318 1250 275647068 275647081
    0x1021909050108071706040b03010f021b0f0a030c111009030204240b09010203040b0f0c060f07050d0504020d02100f0f0206010b0d0b03151003021003020c07170f010e0105 75
    0x352100904800c1c00c29010078105003a024000d03c11081c0c071090528090400103076240c80343d070080c55005001400070f009040070601c0c1c02002e90003064054a6541c040c00f040c2511100014128081e070031060041d00900f1041d4508451400246100384c40d580d0304a04040d080b600e03034404407449241107039039060455065104110a031240900c09403c03141903025400040681040c000c81100c0c48201ca460382ca41d25000142e0440c011765000ca09201400300d09003204c0c04050b00200b4010051509035055aa00c54640385020030f0107903424000124144400103144c50386078400c40d0801c2c002410f0900c091043c0c1c1c00240e01548100007400046c406440e18858650003d1003030045e41541e0015102d598184201c1103080e0141840c9000320315181c00780d82e03c494a003406030f0048901d040c1c41c9030040e07180c1022140101c603c40c1c0b01c100d002e41002200d0302022403191081c6d4601505017000303003100f28648403050440071440c1c0c651074414050035464140c4003909210305c40c2c204e110500045100d24000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 275649568 1250 275648318 275648327
    0x105030718140915030c012001050a1a010f0e06090d021c060513050c13020f0a0e240316030b060a02150115090306050702070b070f23120d020c010219 66
    0x38110030742840d00c04c1e0704060a075901040b201d0b0702406c20300e4109090040700b009084034900c200034001c03c6510303203814081000d01d070380c005c0008050511641400c015400300115420070441101c07100003510501002d0040c54200c00500a802005245019150f0f1680010b5000018034114082c4460150090010000d090140700d610004280302c0340c1c0c042040361200e0342c980414402441c490703804590041e0400080381d0642d00103155030f9901d0794560901d1500070304440400003c140c4243d070000c4a0a500d6107120100905e100e00901a03507055031108400103e5000d00c609800d802d161311081048050303190b0201804144050394002e100941c0012070307916100303030103800c21441c0c1864001a0072a86800c00d5918007100d5100d44001011f590b655000c03410f009440e04080140c410008000052203406100c07002c8283c06074043d042030b6410041c40c40950342006140d0001a00319000d8405d004810310042c0201003201a409481c01500780704840c2240d118400301c0c2d06100c90520f8041809501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 275650818 1250 275649568 275649571
    0x30c100807143907080c091801050103080a020715050d0c0c0213091a0105030d05070c03050d030501060201150305071503110d02030907080f03032e030b01170304031101050307181409 80
    0x10390040e003e000c0c103000c1d0381c5d511860040003080c085e541c0302c800302d801c40c0c08411641e92400040b0b002040f82d56103a28200303000d9800b62004000602c10244045140c40f003070080070406100c3e039190103103084020710103040940034046030304061140350708004002d41c4170105110070254038400e00140b5800c2d14030740401e0b80c00500c204504010f48810051040d41c60009228a5041241c10403a85403e0549000345160303400f07800003071060207010b4036a00000d400d5081113041c0d408580080c8000c806801c04410715580310311000d4040d9001700301c20449150400428802d8031200d240100b0150703130000c22841d4991010f0798564084e580041040b8812105000b0100503081010140000b08034a01c0490b941380400740c03010800c0c45440950884909e407040c0310004e0348ae26540398015045c1d880c100300129032000d108494940c4868024048414004001c17102540e03480310140840321a40001103a0a4000910300303414491040490040180c0510703203035006044101102c12882194018044010390 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 275652068 1250 275650818 275650927
    0x1020102130915060203090d0624090510150f050d02040e0903090406060c0f150f05040506010303090b0f0714032101030507050a030503120603030d140402030c10080714 74
    0x31f003e42c0c001c6075034413940c8a2503582c000e0000710300c00002c22040543d07080844654104400401e0000410502e942c1020380300b00e010000038009030f543d550300185003d5a124000700054144510004480e0145000d4042000c00d0800141042e880d640380d4102d80000b56040f141d0b40d072021925501910341402a0005010640f500030020800c80d0750350580306800e107900520200760a801c005141515a00c01c4039481c024510501543c100703418200c0c1c8400c020f000039000502c21202c0400c0c1c504018048a10020020000e00c2c41e240b525110008610f1003581540403d000c00c001510030804401d940c05650746126101100c0c5e035141d807401a142c001e541d88500d004015001007000400c00c080140e8510040c82d2049611550f688130010341103220f068883d02d03602e0b00c0c0c40c41c0020900d00020060b44564400e404036205070070311a0811115003100c001c80800141c9000003d0b03101ca12842d1101c005440e22a01c050400c140c284a003440d00d1481d0b04104d0308038482c0d07011368052401c01c0007200032521 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 275653318 1250 275652068 275652073
    0xc0306050102071703390c060d0216050f0304170105060a0312091e060e0f0a050d1502030705091e06040504090f080403030215090f070e06010201021309150602 70
    0x40c64940040e4440409105041c0140b5940c0e0300d0159401040c07045648030040c0d81170b50f032550009440c204070510000701c40038860210411441400e03142c00640c00141c101c008141c03a0818500c2d2020801961040c0000e207030400d0a0b15002e03001410401140f111100c19101031034940e800e0020611461100c0040544a0b0b0b05050070301444e6192000c000b010340740c12406024081141110558000129500c2a50844902800740710600c0049901400750341c403039070304c120b20318040100700304404000c41001070f0b0240075220108058078008200810081c8140e00700c3d1800c14036550300d00b08980003160684042240000e1002e02860403880400c00582c640c0900821581304201080b400c0c000c601a5600131541c50a0200900208041d030400f21f680c1300c134245a031540c0b6441c2c000d403a9a105603400d1100e002c000c001c80c207102004689580b2107607041005007d05450003020303200886001d49114150b55081001d009a200080c0001025010702c2c00081410f801900007003030700c246503901031421034 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 275654568 1250 275653318 275653331
    0xc0d02060c0d09060b0a08070512070509360102070308010602060907060e0409080f040e01060c050d050d020f120615041a030a291c03210e0109050f010c03 68
    0x700e10400341c0d045208105000595402245803550003849803503a03456002c09000000580440c0c00100e03a022348409031028882c0c0080740042a40e10031503406240e52000fa0b071b00000e07404014250405244c00c0d13101c0041d1038209940343c076603050081d01c207004119603500013481c1020f00d504a06013a0050006100514041c07400c880c1e03d58491105001b088100031800491480d20b07603913a000f40102541103814140c1d5444031041840e1075621031f108030b5405c8010fa10002480900420550402c150848080c02a84180c80400c4900782d2010108051160b42480088501c0d416540540703090b08184220300c8080c10051308021214610603ca0a016001003006000c115aa4640300c45103007806100c0503200e4039110040d0019041380320784426a0380c03464500c0110248190311041d030350030041d81c041d1100c2c1140c440b1650441903452015003c95078503100081d50280e21352301ca6042400c400300000c0e8082070b244510342540c2c040130041d2590740c811482d0f14001072085c4103c110080175400c041088 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 275655818 1250 275654568 275654581
    0x60e07050904060f060f05010c110301061d0411090601120f06091b080a0227030c0301020705030322030e1c02120a061406010c02090403020708030a030504031b031b080d0906020c0d0206 81
    0x110910303c8002b000c504e1074000048654400f500002c000c1c1c14600e81010740c0b0700c4446e20181e1701280c102ea058940c091004412201c5040a203012070041300b040c1d4a40c8000306940f0200030180480c0349a410149585120001d9140840e2092107a00403ea0b004c020061165400c000c1c403451000d410108214810409441d003c3c0c0ca40c003288107020f090f9005d5070010110580080d007801044880355800d54000520304040010105c021031042c000100003a0711500458458507204018031002000715581141d0f11a05182001c00f90811100b01e908004541c04c1940c041403261107030598a58031640b04291600411946018400c00c03030340f200000c11603d00e08180001d2400c1d0400401034042c0e080d5001003400c0c940f003480404003a200d450b0459945a9041100600420007114103500141c0b26034082c0241d060390100c201c00050305035441d1041440382c400c0d20402002d1101080760400020004104004101d0151201e100e000f5900141c90340d452203035540c200700300c6c540d24208540181d410045c5 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 275657068 1250 275655818 275655827
    0x2041212090506180a1d0717060a17010914030d060512060604090206070b2802031005061813200301180f090203060f06030111090a03060e07050904060f060f0501 71
    0x78843d41c0380c0354140d6991808030103d00c8400c59034004404070201113a0180046c00031161044c0144440e540e21204510700120800c9800e8080e11440d6125400340c0d07007005400014013203400c041242500005000b082c0e0340e52130680c0e90041d010010107130001700d40e08800d03000a00c036860051406496030813240c8151074000d9101c100c0140140d2156503500741c5076080d911f947d0240c9004a9004030b803480c09040101c2e224800c0320440c5035411601e150b03040c0440c0307880200c1c026030b402540d1a96a00344c000d81440d04108082e08040c8404450660040c10340c11b542e40d80c41c40806540210050014101404207a4960383d405020000a42d0301c070208010402c05a014401c0b80c4840310b11500050002c0d078520107a0040d04045802a42c1441054184650020150000b6000e0001140208040c40701c42c21811264064009040c2e480300d41600c041011a80b95080001d11064030416200c240c1c1d19080064041203050f20140c03600f5030354251100101c070b900e00c1000050124004200711151401d80000c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 275658318 1250 275657068 275657077
    0x30b01030204080a14031e070b0c0f0d051b0a031a0102010908070813030804031101121a0904060204030c0b0415030603020a030204020c0a021f080a14010308030403110102041212090506 81
    0x5c1003c1e0100001c43d46002d0140180c81c0c041504100d1854a006546884070305504003900940d00c0040b514040b078141860b190445007400400d6140358100500c030020301008100040a000701e41c081c004d43d15501601400040804203c2078a0001d0520405101a03009019008a0505584c505030701c1c080480c10040c15140c0490b8084006540c0305250703001038602c1e031441d5000900d0800041404410081c40c080500f080c40130030707a20007140c149060718a40940d000483c0d400c0c171100e00c40300d80c0c074a01c1c103200d11043c3d8098003808015103051b03030707a682d04810f4200c0e5074000e07a0708100100e801d000351000300e070401120310b00600e403e0000314290b4000030440c0d04c0340d06c0004d11440d4001103408608105002c000c14580d0010131002c20111202404a120303556130b050701000070349000015000780c003548030314004c000030440741000b26070031a5940f00f440e50001e04107805000d00d1000818046109000030400b50070301148001f614006032a044004403050340c0404144001c440c004c2c805600c41a040e42d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 275659568 1250 275658318 275658323
    0x1061d0126010c050904360516080606010f030908031909060c21110f03061c0c0f080f0c012003030408072d020906120d0906030b01030204080a 63
    0x1820710a91482180c4519448410044550a00c000c07410300c0341d00080a490b104400750740500c41c51200201c0300400c03015114401401d440c02564200d210407240750aa580c0710320405c03c0760401d4100b00481180b03030604c4c0d442900f00c1da01c80c2007044040c0d60b00840d050103a81590505010481c0c1542c0e0f012550701004154281a81d05200345002001141d0840d014881d0003040402540c0e02c0d100700100b9850a000790b401d040c3e904006070010505a51003001c910540021041b410a02030010400007a40301400c0c099102440300b84411440748030801591440d03124001401c80c040c94004402e003141481d5002c20865004200705000c500c1000c074510001e04400d19200505400c03683d1254603100c2c41c019640c40b9444040100001c2085030300050031a18011086845c1491030804092080202000c10304400d90508000a0040c242003e6464000f074000300307003e00ba071702264034461503c04462035200c0041c0170120100132254051091509141003843c003540340a0910355000c0c0c0e50808a00700 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 275660818 1250 275659568 275659589
    0xf0303070c0f0309050405090105070801170601090903030e060c03090c0901060e12101a040e030304052a090a0b090f09030403080705070e1305013813020c01060801061d01 75
    0x40200f61103030130303030704050070005200308030501304180ea1034000d2601b15402c2000c0b81c0c40701c00206840101060700d6000e00714100c010091682440c580f0005082248011814142c48040300c05200000384103051103920080c10f0300da141d01d00f4400700c515040300c106229000d02c5800380188005940904e880441c00380680d142e0140c880300b0300d0000e14100404004d00905460442072658003d2910704201c01e80c107040314140070080c01241d2154581c0701c20b9400a0107603000707440400b51018580145035a1000d170025507410780d540100402c0182d03804031740c010000e60755100d00d00b21030f10382216159009424120914040c2c90001d804640d2803080d80009044604d000c5541020040200042d0020b030140c040421120305100c140d036030010100840888480d424048441a004134801b0300b1840401d9420140c038043c0304a41e5800542d901c541d90180d0003000c28261079521035100c0c0010401c1800d002d00000b0028500300380c0c1c40c00c49290390089800c0c481c030100c1c01c0e00000700ca080c41c02e0545400914 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 275662068 1250 275660818 275660843
    0x902060d1a0307140118081c12050c0706181707020619210b010909180614150306061e0a08060106090f06050307090311060f07060204080f0303070c 65
    0x1012418960052507041c4129000400c18641e03194840d01410700c04c6c0c0300c0d8034910b00c1d10300c03103c80010070070b00a80030b045c0d000d070140501050036082100410809820310725841401c188140050303d40480b801c04449400291142c100202440b61244200f400301010905016940d10720a424000c044100c062020210300d00095507148011500540041060603400292952000d0004910100c0690307007812460b2201c03454550a00038800400016903550750a581801420001080d0082d50204400440007241d80041c9041c404c81585500840851205240041c10240c1d84040031045034080d0308908188003c40e01c03500802c8001c103c405060451007140100841c0160440d5804018180f24440c000204a034120f40e8070001c0e40c844c20580d20655403509810b0302c6a1109a41140004a0344074040000c200c030441c100351b071024000c01684c684a0b4000c1d000c50141c10a000603202c0550008080107100c0d402c211a00e080842c0402540c11403801420190a9110304c820181400176100c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 275663318 1250 275662068 275662091
    0x509180a0e030c0a0303050916060f0507150b1905060414040b030d03090c14030a02150906040902040509100303050403060504060f0504050604110a180f1d10050a0902060d 75
    0x10020400c540d60041243d481d081410380190b1348024444040e030100746401c011500c0404003082400301c200d203d001d9a50842c0c6400d6003101c4c025108902e480c2040000d00c005000104c020840c915400000f00000c9882d583c04000c100d03145902844803100401503500400c00c580307420080e10110b91403031a031a0b03415406040420701404407030150340c0d4580a40700d21804c5154042c0d00000600b4010742501d400151070383c0181c0341d9102c0010803240e01da4010010342005107000c014501441440000460500e402900880d020340c000d504054092034000c00d0601c12400d118047d151300400c10111409950b2464078080c0c000c0c869400054550341d294800a418000550001e90044401c071800300210b2806050a81d100c03002950212a902c0041c04d0400d843e1800e00075400a6943c603281c1c00c02d526040c0381d071040091020a144035000c03030701c40080406d5207540c03030451081d007120b4101400c0c1c1528001354080031520020010032006241006220240c0c40d00307015540e0020030700a00040901c10807 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 275664568 1250 275663318 275663321
    0xd050421060608070303080f0c090a0e0702100c23090a0b070305160c030515190903020f030c15181c4a0d060b0d05070e10060509180a 59
    0x3030300030900c07130700c2495800420154412040c610802c0b40b500c030056952544841348180b803041024150b404610000c0600c4007031080c00c8400d401c84e005004a44410300819440402e0b14a02c44552001c9140442507201410803a0526003020312413101d680d190060b0b44001030003000250040d50744e44c10020131280c0c10580108200c0d040003c0d01c1004600c40155803424003c60135660100301c0702c80c000c4401e030400e41d401825800f8020b49034001a010780003440420340d0000d0600041c1901188110b081200e22864180700409510f080c1801800c40c1c0301003844010741036000035013110300740d0707854940440300c0b200007050502d1000c02d0160f107202180c44000d021a900301100081c0800e0951201c501c207250039032160202565021100002d50814a0302d80c90328140d15410702c0c0f2034000d2449400c10000801d01d5000810b100300003000300002180c00c2d2240c61030070300c094000c805980b4a2405000c400007800004200400c080c0c60b19615200310a0045a82c92031890300301600c01e1783c0c0301d0100b40400c00b01e = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 275665818 1250 275664568 275664581
    0x1180506040b070c1b060e0301020307140c03070f1407060207080a02010315080f0a0303050606090906090402040908070605070201060b04061707050c0a080319050105061207020c060d0e0d05042106 86
    0x5c804040354825003291824100d20b46446184080b601c980c41440c012308041c020780c0d104080d95228050308050605a900c60b83c1d010781b1600056000c10002d0600041800705142c040ea40102100080540e06009041c5032040c19081356096521805080008541c00264000d08950a1901142085c03c010807030541d08565040801030b40180303110b086000c00002100b4074010301070364060042c1c0d1685400e0042610800000b2904102604001029400c20b4036045800034405030001503160f600d074907070b0080d40d00180e4044805503190024840125824003620300500f0041640343d142920703240d0060607a00c8611602e094809440000408190080050b1600300e6445001e0b10302845030f900d07084081c0d91044502640c240030998026810749280d2280c207040c0c50340601800d1410a2000040717265a000402c40700440c4076041500c5103585482c0c02030b100c00c0c1b0384143d01180410030403294500744441160680104603090004024441980c0131601c3d03442001caa40d188089258149a00035205 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 275667068 1250 275665818 275665823
    0x150f0309060c080708160507030e03030706090c0305060907050f010e0a1a07060e1216050a0206070b0f0604090b0112050c09010e01080601140607030806061b0304050301180506040b070c 81
    0x7601c2c80340c452080d00f104090340708040355601c4034031560b58014500700e0151020020f4000540600004002a004100d05605910010b00701c0e424150640d460030b040d03411200d001c440e8451904400c0080040c20005190070a090102800d40c0c241000007050740110010400c504110050b0080040c2d5281c1c20000000350014000d20864200700c00904038850b44650320895050340340ca8680108c01901189500742c40082d0015140ba021070814a0034074001c00e000240c4003401004c514100503a07500c0000d0103000e20074a400c000038a40300c4040e0310761001c0100994000c134280084000014944800c1e141500ca02200d8020000080d0500b24a884a5000c106401c52144000030842c0c801445442d0704965203001124450fa17200c140d04501c118810381351940101c03041c0403a1001078050b200c900c0e448803001e01000d0600b04402c0f088449aa4015200003071a04000b44c00d101d40c0c01c5c203000d41e400f881404116908400c000303548d03059849900030301c0030b0070b010320341c00c00b0507142c03803088111826440c0c = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 275668318 1250 275667068 275667071
    0xa05040f061a0a140d020103090311010203011e0e060117090a06051519080a080f1921020c061b070503070b060913030e010804111201020301030c0f150f030906 70
    0x41c0c804941000d0b41a044030500e10070002500001040510603014285000000c0c1043d21214804d60054000e0881e58a08406000c080a0b03915241c40b000d101550007401124042103281c1c100b410024141c06a9410405418071402c3c20045a83d8100c8800c0d0521225080c08076415510780c00740b071f420001035880007400e403801c0800f401441d0550301c600316201082250010b01016507900811078604584c451000b040d00080c00300004910140041c21118011150341071428181d05448040c4010228461011800141e411100745d84400d04203403a081c1060011403418a4002607155500f4009280201c402007804041d440c11444406540c0242d80c404c08598865071249809004a4001ca030305a02901c030800000e000004c80c009042d94182e0152155084190035400440e92401e006005696207440d8205e00030164032007500603050501c00800042e103a504502d402015404190712800840c3d101c8030041c00003002c4040702c0d02801401d414240281c404a14065014100e081c401a1905 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 275669568 1250 275668318 275668331
    0x10020f01020d0506090f1b0c011409060415150506070206070c030f05010b0303180904031e0908010b03120a0507061b050d0b01090608150a0911040312030501030b0a05040f06 76
    0x46503140c001d00d009044c11202c0c80314580d00c5260500c20a001124051000d004075202e040c2c42c000140010700203e000d5000110b00d540240e81004141103054585002a0740720b24204000e200141c5154480204029002d001a808002000030450054000e60303200312000107000046550740b208403400d10740c0c000000c500c0c13165242407903040080d20000541e40c550910f1200a040c0c42d021048901c907030801c0000d0032450000320180011048000d00072010301080c850300300c00c4010b000d50051000728031a0364900380c0360304010503c0e081d101e02d4a00d01c3d001e039011421084524200205031038642107903141094850400703040c401c3c040c3c01d6603034101740301c02000c181c8032001e2507022000700064074441c501401403240b030000450b40d00c0800d201d0040050298400300b402c1c00c800d1203004207521070080003010b00300c1c0c807004000c08840300616141030200c1c00190130410000c65100d03042e0142071500b410066036145071960b09003180c0040007202d0281d9140c0001c0c0410803800610701006070480d1081025 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 275670818 1250 275669568 275669587
    0xf050d0204080f01150e0423030d0e010f0b03030304050307030807050d0f02180d0209040201050c03070506090a0b060306090d030504022b0c080a030c110102011b08070305180a0210020f0102 83
    0x8190b44c03140d50440c03407120280030170114420021940a80d9100c080c22300444080b101081e600b4890342c0c4420520b0004126400c00b03411a40506904622000000103103050401d1501048800100e103280c085e810034410130000c103001000380d0328410f41500300164143d407411402c0f1880c0c800c0720340a04071181341c0300c1003030341c4100390380d0281050b882034910018801c1d03654410014140c004020003503000d280c0d0400503006510990191000404281c1100d0810700c29644035030131702c01c2c01c0300e01012507401003841360301b800003209565030041000d801030855030038041100e0780c8034021b0313174403400c01d064030b40000c9021502d41c00103010a039208000d500c9003241c00918a2189420342ca00242ca108851090103d80340b20046000c40001c0e5141c2c44c3c07060b82c4010390740c4030249441051a10390542d541d44504128105403000075140800017503407101100d02d44854040c0032540041c000035501c8100040086480d44006042c01c0900e40403203a800c0344541e2464100d10700048180c0140c0e4950011600402c0c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 275672068 1250 275670818 275670821
    0xf180106110c0d0f060c050405041a0405010b090d030c030e040905030c12180108060d06050702250e040b1305010e010603030207121a09010e06070f03050702060103030f050d0204080f01 81
    0x240c094150142c854005514040084421580c8806044030b01e0003182c08000801950040c00002080c0c10030a051696070720006049841220100e02010054030181c5040d00e8244241030260605254550404d03003043c0200b205e0000c3c00400400b8001001c140e101418011030072850421001841404820050716105450f0f03000f1b00040c0b040303803085220700d000c6200c000094940c042d408454003001c00da04140111a41207016040a40040c0c0624450002c15140d000b228410200c640082401040300140920385420003400089070070395554081c40144040780d6a90340140d0010004c02c4107454202c0302c08006061220010003542c80c1040c0c04070708090640040003120700035000e64111a607240b451050102c86048020032120700b50f40010003480c07451405540200201000081182410042d41d203001c0007582d00c2004210003003400303070003550705009180e880a01403000d40010f500d0f44ea07020700b000388103011440a0040101c1d1001c500c1c1d43c964142c070300a1030003004840c00b13818102c1c8242d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 275673318 1250 275672068 275672087
    0xa0501050a09020f0904020102100c09050a09320103030e130501080c1315260d030510150f03020a1b080403030f02063112090816050108060f180106 65
    0x2401001000c905062034a817440c2072622864040c2c000d041903480500e41c140c02000c03140805418415640f0000c41c0980309c13040c0702e502902813070300c0009442e1540f00c550030800100030004003035022000300700c411508030084801e0450f545800d000c13613a17510300030015502004128000903030501c7d0900018050100080302d01d4a00800e0b113814121f003208810f408140c803140085145041d4465030300f0000f900c02c0c900710500b000700000341d6094001c41e2100c1681445080007200b0002a150000d10040c114050488401813a40700c0c0c80100e84241c011019051031451300550082c940e011544100c03180c0a030494100d82c421141d41245080d1103403030011400d4115000070740001d13803100e91003400c65000140e1180514038400121444440010b16440e5042c640d06040c901c660b0b40c5803410000400341e85400355582c51a44490343c0e25801c01035000d01e4244600c050030709845850000f003049036000008250022019280c0380702041c400004211209e40741c0d03944140041400303000040340d580c04034454 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 275674568 1250 275673318 275673323
    0x4150504050c011b020609090402190b04051c032309100302030108010e010b0a03260c0604110a050f01230307020f0609210c070e2403032a0a0501050a09 67
    0x39000032134815a0300b081e20780b440340f000b03403c500304105140c400c0c5054202640d00c02e00c000c0440c0c118149810071680541780550150000700300105080c0014540702c0b052807058800e04098621038590351b200240a4850040c0c16119250354036503200c000307a1008201c44010b10003a12485044040040003030080d482440f910f441546803d02002e8561410f0241030000d06000340440b04141c107540720b9001e49010010001000540002080d0113100201d014203080c440210141107039281c0790406503038160544440b00e02c91440d1040901c02591056909070b803103002131034a086e544c028880c0c44007000028024040810001004002d160342c1d0000d140506403190409071b60b42512003807442303643c0b0301c81c20414880550807100740c69036840c0048041d0001107081c208030340c1e2995035054106e41d00d41e401d4840c0c00c811072500c4800380460a03a020b10001e040810390096143c07610304942402d1508040c104266016481010480044020403022006a8112000300b00b03600300745804000910b12103404 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 275675818 1250 275674568 275674577
    0x612060b07020607022107060f08060102121c0e06010906030c090203010b0405090a1404080910020705030c0d02190b090f01230a1404030503031b070809040504150504050c01 76
    0x305116400909881c005507003d84101c0c01e0003c0c0c0da007044110441c155090b607070040c06518034070f0f4002c007c200344002020107860742102203450358401032103810020112815940400c010701c46079009101182d60102c40c00382008007010b03018a9100c042d01101145890f140301c0c800010038900700c4d541c030000403240309a1410314190b80d12544103041e404248100c80c2c03410300030700c0100040e0400b5890981e03c032451290000321900c018018120007102900d042d656a04086101285402c0c80216030f50749080500003040c0f01858000025510010682c1c0c2c98001c152111101045403240c21788048800110f145003280682c4440141505400128000b0b20907007034081e0403080b550003170148100c0b840e840811021040301c04130709001c1940c40004418100000c01c1030b1030040b54100c10141c0302962080c40516900c0c2828008040c41300d207010340001124404108138030015401030101c0e005641d00381d03000304240d50b5904160404007505103000c0052410f1030f080004000c000f00300d0841940007600ca = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 275677068 1250 275675818 275675831
    0x50609010b01020d02060112030309050a03030507030b010926070b0c1b060c1b0316080a0501051f090c030b0a09020c0706230f070f080d23010605090f06040612 70
    0x120303030341e08000000340c4c00b5030001401402454400c2c03001c00000c0b400381c1030105100050380c0d115807900081800c10350011303943c0c50900c205568540035064030b0200910f410647d15040502c1c8496043d400a1001110103032503805621459050281000415000300f801c3e4840e6880c2692a84400301d00c40031301e4608103000c42844191410740280d8400d1061000180803198940141301400c00c2032112407a4144904400402c000f9045001c100c054001351020704415680c5150880c03d48034041d0901c034800028110306880c90000002ca0011103c0002001ca2201c0c21501d0a60003020200545030f007019603144081859591074000340b0310b4028590071145500e07a2420102c880010303141c00341d80581d16140210320004451405410300c41903421800c0c0c82c00e50a5a1805206100102c0031100100c0c042191054410948124040000102c060ba00d01c501c05d1103044181d450140104000d101d00480c422003d07840300c414110324440c000d05810340d121303140c14000d4150a07204910760311141c203088 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 275678318 1250 275677068 275677091
    0x4030f0206010b090d050c0603010605040f0504180807060e06010e0105010807030e120a0201021324030c08040f050f120d0b011e270f0303120e0706030c180305060901 73
    0x549941203490280c2200c0c140000113081110440800001741c407640300c0c2e03682284440c1d4035200294000c2146807a210381d034600e000d2006400306000e82c0700e1031060b860b000c124400c1c07840d0714042c01002d56100c500382da81c4030004d14054008020b00b044201c000d100300400425000100345406040e1207090b2039603546a980d08204405480c00c2103040103a540008004914880f000300c0902041c024900000d820050042480710010602c1d41c131102203a03009801b500310003008041d00c080c481081d441c09001e460302081e80540b94000c0603100810100c84c43d0b07842c200b840b900313210850104249200b43c4071200188100000b403508031010252540b0302c0d200082040358058403403804040b0071889100f05143d925001540e045904442484007494900150710341c8a1180010360040d0042d050094042400c40c1002800d116282e002008074070f00d005081001d40c0b41c000343c02c0040381c1540c039011a030001940380c2140d0540b4804400c0701e0540c40e001002c0308024000c40c1c818410707900c4400030030070a100b26 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 275679568 1250 275678318 275678323
    0x9050403080106031119050d0f2406090b2505030c15010501020120070c080601090e190308130201030f090b25170603120403050f060601080c042306040e04030f02 71
    0x150000089001c610451108a0b4040e00150424981000e0009464202701707140b84d060b42c0b0081e66150002500c050b4000012620700e4440e000f41030180381a1604038104007102c00580314040f00380c0c009145454507a0003440e0a0302a0001703456114080e00d0300c800f41040d03440c0d035442c900c0380c070303008413071070b01000440d96520500c03507021140c891120000002101c502d546156600080090344d824005030000714000da0204851030080c800007400003202c060f00005c642c203040049000c0c03007411000d1180000400d0f0b01c48440c6401501c00000f100d41b9003c20b2005030000d000d104282c0070082d040c480b480041c0b2140b600b00ca403241d41c0107030618641032003000d116080710b0009807003400442e8174001400c00e00700c1c00d100b216501c002c02604031441d60034150f42c0c002c400d070810348c4101c40541c04140016070561301840443c0e002031080c24100e02ca421b1110f03442c0e20f10700450040c18542d0082e06556001d1580001b0300b29860702c1c001d443c9950701e40c0c03580594080f08608550907004120f1030b01203d0301c0c2d01d200 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 275680818 1250 275679568 275679577
    0x607030e15091c0c031a07031a0109060333051507020102030f07061e05090c0306090d0c050a0c0b0903120304020603071b02031501080c0604030507060302090109090504030801060311 80
    0x109071064a510f0800503460310350038070341d054544848210020000a0400342050034404010031601c0725031902081c010f00381d6071020541a40300800f5280180c0c1c60740c120083c0025102c903030078045022421003a0008035490100081c10402d14404102458030302401c1280041d100c0235504220b880c00c1000c4000018031030100700074011b0340b00b0001d600c21200ca48000d03002d81407040c4000718159075101c1c81070402e02010701c81c8000e0243d03600248020f0343d8040100003d0441c064024051500c0c1040410b5140e41d810f00b40202440109484181001020700980e00601c0c0d001601c00f1005813a40b2640c00903030401c59143d1301074400c480000340c2c280505010f40303124a074001c00c0180b4690b11010700f1540341d10000c50352820f525034a804200183d400b40a030414010441d40062071342e61400350064540703a80048480c1c001d0600f0001800402c03c0407078000203036011818003580d52001500100e41000403a40400301d50383c070b840c0500c0101640280854103c82c41642c050000c82e203840ca00c0d140e00d216 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 275682068 1250 275680818 275680837
    0x3090d02190615031406060f040509100e12041502070614090f040e0609060f060a050d080906070213060305010f0b100309031b060504050d02070e240607030e15 70
    0x400294009102c5820000703000030f109540d0700256a0b44d507161010f0040011901400d40c100300100038060404013074401c144001142d040c04541800f80382151580901e8400740c4c8a10b4a80c40e404080b21810440c8040400882c199559910740c3c50400d56000301640032100014010700ca80015030074410b00c0f007000c600308221741c50b900e0603085108001031150000030307030303900f25403244d0700c054060f41c05000443c45140108007510380d906c0e000d503c0300494a801015548603c100100c00d21964682412292403d940030340b45c503955100d40300000c0e8440c001c0e140000c0d030040000c0c01520000f0a103030001e0f0201c0744a10000d1001005407419401558080424107810641503040c242d4451b129800c9100300d14000d0801003001c0180118250007003040340c1c0103440858a800c01d000401408000f80c0782c202c0d0952003c0d0502034181040300900140c0076250000d588000c03280b09803401146035104d141560001c028544d28556447d000e803000b4000d54402e4402e2510110703a240c902170348000ca496a14 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 275683318 1250 275682068 275682103
    0x5010b030c0a031a0924120316050a0f030f0908010c0e04021e0409090c150e010804050c09010f0503061005101b021207150905030703033203090d02 65
    0x8249008034014144c0d100c00112600f401c500302c16054440d03113682405a0700f07041c0100d80d0240120094030850641520160161003003104100800300c0110a95400410384a846201d410305400c010b4607113103850300e0180c03150340c480c40500100b503044202100d40c05221b450360180d26546041c0d15003243d2078002e080000c92140f40c900101c600d0241d00400740b41320900b103403122030110380200403000d4009801c1402c41907900e80c000790a01c01c00c0b880503c0140b84d00e4100c850300d0141840003c0940c2e455118440c144410100410100401070061a03003200e40070341410310940e91480741405004140c41494060b008000c0817841c880e00d144080010341d40003130400b200c205c001d07100444903e06541e2413609000f115482010042ea240b0710303900a1249c80384000c0040c5400d0031400c901114502101ca400c1c010540f8040100d07850101d080f01c1103a0301403c0604180d814000c140f8458841110144550b681078034a5040304100131002d5801010f108003200c00240740c8440a0b40e4840b000841c2101c0c06 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 275684568 1250 275683318 275683327
    0x2030309061c05100801110306130b010507051006150503100e060112060b0403061401150c02120d0f08010b0403030e0409060b03070f0302010e061c0c20030d05010b030c 74
    0x40c01c148005000402d114070203580c900511441001c101e65040e6849628141541c500704180304090103152000c40140b02d526245040400008500103403102501480a44840c41b04002da0300a00603074080b6074100341030701c540c0d10320882380b50000c0c10380d4050b03001610080210401d09520801c01e0364443e2103240d101039543d1f420308030b0014240c1130041646040216035084081300d82c0385401404001d0403031082c0640c44500b140303021400d0b03603449030000c0081160f40c0c004024105840410802851075410501004091400401c00001080070305016034803a042d4011007450b805500d0048035406943e45980d81d0741c9500c0f6003030042c451403001400280c2001440307485458035601c038802c0a8820800001c000d007280c408a82050110780c000c5414251010040096503004120b41346540400c642d400d15104046030a04500c0c03080d5000c1c002e01507070310a0303403200441c0250a40b00c041100007144400250703400520030ba80743d210a1480e460142850000928040c0784c4042e00d0250f4a00084107080 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 275685818 1250 275684568 275684587
    0x1d01050612060420030405070503032b060b04080f0c03012309071d091c080708040614270303060307050112021911160501050301180603050d020a1a04020303 69
    0x201c110240095030700035030394207140c03c00350303440c203250314900341040c0400e5128941402d01c2e40c2031016603409a4080d400410101100d4807030826802c1524110941001142d554071819078000c1c20150801118410005800320740203000243c2501d0a107a000200c5511621800500d401c0ea508500d80207400c2c042244040c4241616280041d40300454004170741e081230740c03104425000c9651842c1c00b6004200c03142401117001050024030a9006c40c26034021000321080001040c000c070040c0b44a080002d0040030078200031380ca40000b44180c000450850450a21990004c5010100390145104403042c2913240b003401c0000c4252449050004c0c00303050064540001901c003000207040d0512040d80c2002946007444400101c180f01c1c0c0c07400d551300001000050b100600d0001d450390b00c0c8801251188003008560791000440341500e11a14143d201c0c00340c090184405809280c0008141d4000d90511401060740001e40e81101800b480e5940d20f02c41302c244840ca190103080c1c1d006034041e001009104034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 275687068 1250 275685818 275685847
    0x60603011e0902030a0f0803060a080304180b130606020303070e040905100203040f08030702070303090b0712030f020f12040b1003050a03030c09080a03080a11040b030a0908070c09061d010506 84
    0xb441400a404ea420003035403907031030148005202e401221100303c044140180c900341088800d020b402100000c1d442c09080000c0c01c0c5034070f2407540501c900c0f1a103030304144c200ca8031580c0d40306041c1a0035500c144182919000c0181d20794104030380703600005100c040b1829607480c00d4018000c1d0350342c0140280c130308d1541c00f5148401a5200400a561910607004540c0000300c040004500ca4151640030700013090840c81c1c01420060654040c01307080100307012403000f0500341084501c0364403407400e0006650f00c0505240019010300c4030400106c03000480e103c0c2601920b0340103a4401c520881010714650398041c1c3c00d0613a100540000b0303080e40e00051001c00002d0003a4050300d11020b480c145200d00940d05d00945141c815680270031000a40d8900030300602003514001d4500481d020f81c001400c1506041c81d0354103e020041003045042d40720005501800403682c211400e00c1e8000d120a0141d40c0c0342c0c03035108083d00c039520030501d1036401110f60300c840541014805e416500014921480c043c407020803000c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 275688318 1250 275687068 275687081
    0x61e0606070807150204051206150103021908040c0504022106030114040b13021f02060919020d02130c0f1706010f03021b0d020c180105150a050f0f0408060603011e 72
    0x4d069608010200d620303030361070300304560701850900240000d10749014007404410003600c819040c0350060208001c002465004815404040d2800c48510398580c141244500b071280e2100f90801e100041c0300700000078804601f181e0404409201c034154442c1810306007281c20030442e0382c106242c01004980018003019209802c0f0910000030414940b0a40000d40c50301401d20b9607050111611400c49140303a0144000f550140c100c00143c0100c554408000c2c221003400080240700f4106119a6011940d8102d802c1140703100080081080705005c241c040c00c11090804800041080e0203505211103100011030351044c001a501c2001d580c4068205901941200c0382c0e1850034031718141c0c8480c02407010460108580307078550081c480b0481c0081440200c90418200e41000c2d0311080060000340c4a1110218104a00f0211103548a0f45c50400b10b59601480401442c5504009503000192016001600594800806a40a54441004260898211421500c03d20140c24044036625000c0c7d032240d0f = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 275689568 1250 275688318 275688353
    0x405070b0a030e1203060418021f030905060108010525020c090408070f120306080303010e010501050a02030705011803030e1908180616110603151908061e0606070807 73
    0x401d510300c5140745181001000500904d40010210821800e80ba003400f5400f250114801c22a400e03050940204100e40c0c4030030514012058001c0c41201910321991182030826004015542c25507116035115020301015144100141c40c5101c07025220703c0c1c04940850340d4000340d002080d5080c1240300307001c12040020419038074040c0a0100c140400c4449810f40325140c810020702a2040c0c8003000541180c89a0304001d00e50361080c80144002010903640a0565100342041c64070f40380d2210b001c81c910301c25031100920b50f500303107502d1b0201034003082c0040400610039241480581d00300003002d90703928401c118519041108540704000f1990704ca009190b0440d070101145800c88008000c549540e0103500d101c41b201280091800c00c1c04114002e0400c100d208030b688a2550500c44030842000c4140c03070342076104080c0c810381103203510041d102c2e02005103144c0381610078070705d0400001260300400403207400c0640c0d03400340000c0042c60100111004268840319030b40c1070509940301c840b42e80b101681279 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 275690818 1250 275689568 275689571
    0xf04031d0d0302010b01080c09090a0b0d050a0303020717030919140106060903170f041806031401020d0e07081002030c120907060e0312090607030c02040f09060605090405070b0a03 79
    0x585a03961980344004640c80e00030f4001162140c100f17000113200a1b002400192901c1c0c0070700012582d5071f01e0b1065903402039900a0f000c244a044580060781d10308940d1401001445800355440400d90560040d114031030140181c02d81680c42d10900a0051004480403503150300101409240e14040c0400765a0f25801030a041c1502440e9220b0302d0308480d07a40e08401c000c100704071810810443c00390310a01803203003c0c400c030605086a0001d5074480c0e0165011303609000000d8401d24031440c0e4998000802182c1080044948450405406000b580605025107000d82800c03a40048040c00044500844801100804810032401c810100a4001034055569800c0c00c01ca0844404011649640140f19400240800c1c51a00501400842c40201503074040d401180241030041000020b8410814094450070f650380594a000c8070303808480103009510078640300528040204a6205e01d0086108440810900c0d480340e0401410340c20407240200135601494050011409a40c083d00414409040 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 275692068 1250 275690818 275690867
    0xb1e16030e0f03030a0e0c10020607210c05030105010806121e01060801050c13080f060a0c030b10110d030207080714070f120303110711010f18030501020309010c02060f0403 76
    0x102411136000b0355a22041c207860741e10400669509200c076008094003140d041142808400703000c1e407030700e100401c000140b010302c0d1070368008101304001180340e01d14410003c0010141704400540710f07420038024207001032901c400180c0c007420302601e19200080808003d11460002001010000012038203031105552211400a600c40782401203e000303000c24440d40b0344554850040401480080e0b02c149031a5016502c004001d00c0d000c0703020358202d02c0080020030000540e0308290060503c00008a40041d100511910000d40c05005c070001400542c080d900e900c2c011410490607406408800b07400040100b0043c0b00081001240241c240180c5041d214055620200300c680800c480e4800512907004400b42001c04d5030500c2a00002415107020030b003810000e803640b5034841c160100321410303c03000d540b9800721940108142ca48651914090b40c0c582912454024080d400c1507034515619803c2c079403980d2003207001013401441051403000200c1c0310703a916201102c0c5045520304000c420780d00c00702d = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 275693318 1250 275692068 275692093
    0xc140a030f0e0109050d170f060d120f030c0c08180a0305060f04020103060509010b0306041d0102221a030c0f040b0705060603070605090d0b090304050d0b1e16030e 72
    0x42c0c0a29942c042c00006002156040c19424960136035042c9040250700341d9452050710400d211107400c144c0c1354103c8401995100e01084003041c01b540003600d038000900201007041c1d40507007250081c150039a014031081d860007000713441510b01c00c1d40040c240070043c08034a0582c07510840c0840070140040842540a942e40c0b510f904000d4180c40e884006282c50301008150f503094058400102410340d0310071495072500200700428080504010b2085456207541941c20420542e40380c00d040005000b15510080004541d201d410b43c945111240c8215480009501c480c229090b8580c080194855145603180c1d810102240e22862540032000800c0c4400300390512a5004bc10030648036000402450410b0b500309031a0903455400402003200802c5a0003c42d00d031002e0a10440790700040d00319180c1c880c108480c0c00c40c000c50304440c0d04075414043c1c41090140000100b4000c00c00764024141400c030100081100800885503060b1240b42008504039413031081d4003040040032148140d5070752a10a0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 275694568 1250 275693318 275693321
    0x60503010b0906030a0212010f170304031509050a02150d0608030a0503180703080a11060a05040503181f030519060503031206061c0501050f1c0b06180405011e0c140a030f 75
    0x280c109805500c80381105129501210503900705080d0184000e60800e4a16034ed840346845004e0203420003507864280802c1002020071a42c4512940100384011200c4000ca05022a4200c9000314a0840c10940c0c009006c1002000715001a030707190350703010300d9659085900c0700070110f0059020028461020000045000c00c805000d0b03116141d80c0b06d210700f0700e031000c03800c3c41d041d00a082e41d08140e140c0028000003034030000403a01c00b0034a01050400d2150104001200010400907003250b00380040d99810003d075269108a1181c4101c1c1103560800d040440c642c0d04030703001c90140c0754141d4010000070100d1815000d00d5035118200170700d49840c0034074540e4884600c0c00e01e000d09405071904c070401400f043c90402c40701b1440780360650300c0e149501d40c2010821800030303003114043e10a0800c5c502080c1c1a4a92001c2c0d00c01450030150301c8d007190704041c544540204500340c08568004c08584401043d0803150203100b900203082e039a1026680040241103220780e21011201e4103240d5505072000c010a0725 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 275695818 1250 275694568 275694571
    0x305030903070b0a02031503010b030601052110022a0726010c0315080102091503070e19030201090f06020607032a030506030105060d0c03030806030114011509060503010b0906030a0212 81
    0x40c00540c46e81015961705900040030408184241d040600b01d041e5600c0010b0424111b41301101d42c2d0440c56141100201c8044400f0188129401000103594241003e60003c0507004c1c940da801a215200d400e0100d003600105956090003504441010455121003a010006031000e149200d003800e0010741c10326003102c1d02607983c41d000c81c1d2695405401c0d640340400e19001044580c000f503140c0420300300014066183d00c82d00440c00c0c08040082454940300745080d6003800001342c40801410080301141c00031840501c000c90028848120103c5c0300115148840700b00d03605a002040c160320b03060815006400d11010b620f42e01036030300d250120130060840510700640026180051141842410b1500f901c40082c0320500807900d240c10300c00081d02d0034103540202c0390903107002d11103500ca06001074007408035060354400100d6000c5c00030a64807050910815000000d840c3c44c1030041c1e40f05826200350009219201085c101803041c4055401c02600840c0d110301c400e44010314101c1101c2c00009103140 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 275697068 1250 275695818 275695831
    0x3150106021e070605070201120b06070f0c0504020f030403050c01200a021c09050105130317030a050f042d02060d0203180109050c01031a1e010e0a03020d0305030903070b 75
    0x1459000105210701c0d00d00e49504201c036409000380f1400e084002d4580c0c81303034420013810010007a11408000302c40c0e600c00081c980c07000f4140d965451030b038100b00610035100c00f819140b200b070100000035546800d1088982103000e494025040d50b40d151015150f60b0000ea8007500c50355284c440f461108030343c141030061081031241d001c50300d41e030001d20b00031b2810302c45848510740c030741c446405041c0250700301400c002110380900c0d000356200f42c2c1d85429030a100d0150305c001c2201604048480c52104040c019502c181002d82c0d00f00a699181401140b003240306840c00340807000c40c3c1c80f01c020905100494044042c50160010500e035000e50b010a50aa000c219442c2482e980401400750003226020340185201c030341c03c021710000d2a1500c0d20f81e220030442080c607040c190f41d501c880b003110200344080540140c000340200401507010b81c210740c0541240c008c00340026500c10090301d00d1b25084100780244c1c8d130040c000f902e50ba00c030744c0e90554556101401400d0103210611180300010321241e00c0a00ca080d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 275698318 1250 275697068 275697073
    0x30d0e0a062a0b100504060302031c0512040602190e0d02040f020705060c070c0807181518060305070504020f18010c0b041110030207110f0604090e060612030703090308090315010602 80
    0x6080c01d640c00c43c8400980141b84100d003800402c001682d0002001400001b95034500c03101c400b4560400e440038890f40508040b074224841c1000240320b02070f0f01030021901c0c124001000080e4a54080700d283e9900d0550640c800b801045400c054200303603001c8140822a20001850b00358261281403802004456025020300c000a010341049240400c2038001e0481034010700501c0e003030104d104002c1280e060501e8809a80350040403038008280c10700300040c66542c640511140303000e200d90b00944094041541c440c846c2110001d85400c01380700302d450711400d824840703040c00c0c2c101d14064801c1100ca8100c1c0d0400c00d0318880c0ba40030940c440b00c8180a00d00c60810084900c5c50700c004e01c5542c150b00d10900050510503c00a030124181082c01d20800000720744540e580d00000000440b04e00564101203078103468030311280001039000800d94050802142e44406584410b4640c55483c072940130024001101d46034100000303440c150103450083c100600381e42401807000d0100c01211000da0200005a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 275699568 1250 275698318 275698321
    0xc020f1501090e03251a0c0d150605040603020d061e060e01030c0e0409020307030b090f06010b040b1207030b0301020f28091205010e0303100302030d0e0a062a0b 71
    0x248003074400c100e45900d03050003075418a085d00d10201c1c0d01c80340001c849102c0c0d04040c840c4d182007000c2090b0200a40d042c54074048814280003035880c995401c0f088030b681c01c203490b0120443d180012843c02d101200d00350394490f45480d08082040b400780d00041422204580c03618408101c5682a01c003100d820401240315020715440e00c031005100710f60440049050520346807914a85980c0904022110301040d107021a10200608c0400d103880542d600141c403985180741840026040410075070300c41444c020484096036201d010900d06841103111340d180e41d035000c000e03494450607510a8241c4c44002803d0005414903214082070030b91707000340c1d070000c0a948000303803800340049550240301150041c5042d03041c1105410034080d0640d800c50242d2101208046800700800c00d0075040462007440d50bc098a8a034140002845032200c45400200e01c20700401003d42d4510380306084041c0e08200082c02c0007080d6150450944103201c00d612400c00c81d03c00120b14104104a0b00d00100499204450b5215035 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 275700818 1250 275699568 275699579
    0x50d050307031214010e07020a050f0106050315060a06110709090506100b1c050a09060f0507111c0f36090b090a1112070203070219050102100c020f1501 67
    0x103110070380c0300740407150314104061104e604950100c9040d22020307030308155291100c240a03441c084d00000020814407401c15103030390022041d04500f0448005a044030542017100c001c0386444807003204c506d03030040102401008914851130010b4484800070003a121201e841782c0c0c81d8801c0d903590010a440561001c4103104403258800d80690092505002560801d5128449079000c203a07001d815818a130b07110300c0400c0c0030b0103981e44125010b6038448010000b580b8030181d50f00140c102240d980300800e0001d003030640700280214480d90100807032994400030901840083e102c000100031050100301c89000b41e5000b8010680c48020b46e03c0b0385035a20003000c0300710342020041509a400150b0000e082150401054036854000349c1c001500c0e0b100428418014451466140110000804201508800d01004a401000401c0454000d50309000c00749185070038120544403500c5a40d0050b403082c1f40740c00300c28055600400b010a582d1041d1003061401d0341e19a490903004182504e010980c03076004100 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 275702068 1250 275700818 275700827
    0x30c08060a0506100f03020d1508060603010902100305150a090f110a0215130c0605030916060c11220b01030e0d09030f05070312111603020303031f050d05030703 71
    0x2400103800000b40081d24010000c2000e5141000912042c090f4500c5071403480c1c2d0003601581e01b0b003103240700c3c02c000300c5807440202c50040040d40300c0d9076041d00480001c980141418001d0b0141c45401500749840380140200460003800011310f861001c15226030405250340e102c0c414000109080400815040c24414182d822a010701c081c0000c01700c0c1c04c0201080f42c6801299014912401402100c102e586003a0321400360f412005d002004622142d41c00320300c158000b009140554100c44c2141d4114040c5810700e0100d4000340641000304900c500c68100050b100090302e01c507910050401614080c00b054284104041450484030a075220419031245503494810a0403d2135881d000344406c0751040c1d4054031295003800050b010315101005c0308240003003080204021680000c5000c085a5500ca0080c1060082c0440070a41c2c0616901003410031800c041c800140ca40040c0550f1854079091440070098041b062650071150b149000060203940c3c2005801c26071b4001c1380a5581c4468503d001030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 275703318 1250 275702068 275702071
    0xe1315231905120c01080a0c02070b070c0e07030204030b06040203272113120321060e01050f01080a0e010b030a26030118110d0f09060b04180624030c0806 68
    0x3c00551200e80c040b0328580e48000b007142c201800807070002e000c10100302d08038205149600070503080903001850f6020030170300c840840100c86904500c10625119104114285d07c1036200c0a006800e074071021444528140c0d0042d074000014403000182d02c08111125500301c403180e810402150031240503001c00ca03000c810300324038411482c800e003813074071a46000880e0585018000c101d540c41100022070105809415500002841d54101d2400d040043c0c0004020b02840d00a100c1032110107400083c560400d480e800221000c144c6920400b59540c685900061480800942256413510f0440d041501c3c1400f062500501a6441d058201e14800901c030000194842c1607245c51402c00041000c002c41060b500344d000064200441d05c812609042ca40ca0300070307000e84030001032403c0110500ba152a500c1900301c00d21a4809106034040c200400c0b080b030b2106440c0403049400546403400080c0d45500000900c070120a840040d0f842e42d4000e907003500e00030380089a0031403114900b402440406c000d00ca = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 275704568 1250 275703318 275703349
    0x1a060306072109080417060916081005100b04030303061403190321020f0d110c0d050f0d0608030a021b011e020106150e1315231905 58
    0x446480074192044441d42c808401035040c0e941c0c60610004000241c8122802404010407030b036018042070740da064071108250392078000c038070411104602d104089051401200c0803134005c3e01d09903c3c100da08802500000f808115030710007400011411600c90380c0980301941c003a0342c00141042c00c00054003421005480c1040c400e50084050b03160040d54050079041d031950510780221103915480240c00b1074000080d90309601030002c02d6090154034403101608069032405028864a0280d54800f0302c180301d4202000140c1c0c1001c2055a006400b5600420b40c80d002c07900064074144012110400f11449500911119000080c003112610303410049a1082100c480d0070b0141011040000391800c500c4501d044100000150b83d02104c0b4002c0d0700550090039071038074403010180844801051070704103050452140701e8042883c5100ca8503882615116081d101d04190394a06110b240e4100c2807070307110404800500d10109040c1c03926030b0340d1005175240000700c54041060424007049440f41c106c0600 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 275705818 1250 275704568 275704577
    0x230703090e010e0403050d11030406050403020d03110f0c0f01090807150501060207050f01031805240f130516030309091a100315050a0305030c0c10050403120c1a06030607 75
    0x5003d083c040c16280ba40003945030610568030728014480002400c144103045000d40d07030110810091066941002e03225603c42c4d07082e10328100c4920402c3c1c040b200c0d81da144400400d410b100b83c23400030f13034918020720a560401d011980c00000107420a802d6078221316048401c1d80300820040c0820540002c100940311200300140110360401500940d01c02c940d200f1148664000d000488099000341e21810003121500c034549920852401c0c081c0da1490b0f10070000d00818000300c5540c0110b0441ca20f0707030b400341c04c02c1c29401c6e600d9214101220900b100080c0d043c1e80d00c2c016881c1290350600031030408801103100340c54903030700341d403408100504856030000c1c01400c105214400200f02d41d176003032a40c0b04007411414005155250004594031441d01070700f0aa400081442c4084140070000005e030400b80740c01421148402c5804c03041c040d682e82c0302c18046c000724074180401d00c002141c13a9803101811040c0e2600300f10b81c101c10b4964405d0304064610400411020409010003401d05014a41d4802002d042 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 275707068 1250 275705818 275705821
    0xa1d01080708210904090b160518060d1d0d0e0a0e07140f070503070b09010903120c0203090907031b02010b010504051903230115030b010b0a230703090e 67
    0xe1191500140c3d000c6006008500f4140b6426241d404165040c00b0303409442044030b40c10724600440c1125055500d40e502060382900714003107071700c07903c100e0b440d0710109448503121030007034824044c3c81d8001564444855844080c10181e45e180074080550003038680b001440003020062019281e44410454180144c031114401c1c88000074048416810040b107142003c591340035100c625249001d03d40c50042903403070015905007449800005402d60314014800e51001781c441805003800c0b10014a4010042040c610722441c000744154010341819007e0b00581c2d245c41042d00000716514001c48003240400d5885508030186041d009400808000c3e82c00200200c00c501c10028203d03004910595100c0c0070615406000c0c2107a0405207802541d100814450075280d241c0e482d500b0711040d000c21041c03986007400f0240c241105441201c100c0f5002031241c849a401c064502d81960f221800803420b0001d141a03000c00381186c42020010303031030b03202d0b602a00c400c12850020083d040b16404006980d04500 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 275708318 1250 275707068 275707079
    0x5030111030c03092b080c0405010801061b1e03180e160504091d10050f070e03011b031b030203092e0e0c0a06020a03080103021903020a1d010807 64
    0x408498100c080d0031040e545a942c0e05203214030308450700c05184045c2284141e03984000030481c0b00d04d640340702c0301d81300c075440350b40c50110050b080e0007075210b514001441d0748010400c25000759101c0380721001081442918030038588a8525550050301c0381c042611a40100c541803683c8401810603625134185041240c500c2c3c448114949140070308012403048020840c1103841313024000b1580208164041845060300d507800440e0f91000e41d4880740a03600941d480b0044140181c032030745124400741541d440090f100c11400716900341481ea1183d40540d0f03101e401c0e0f640100814a200510000740d40c0c0440c400402c0d0010506121080c01080700303050042c418402c0808001c218405242003031190084a15000003003440d800400c50407d003415850030b0b15a041c924404254441000d509507a00d080d0940c1e10306c002c903502c15043d400500020754500c018401450596103c081ca50782484001003400d8a9400245114805500c03141d5100d00c0c1140701c2214012900c5118010240c04d40a00003140c60003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 275709568 1250 275708318 275708351
    0x60c020703031713080c0a0b010f090e060c0a0302030c04080604120e0d020604051002120403080705060f041a070905060d05151002060f5b06030b030a061401030c050301 74
    0x134034010207944c400300380d51030100001c0050003002c981250310610656503070b001c01c9810070f22030300a02c00c400781040290154414000b0740507004d901644413031440e081102c5000c0f070082d080036002d41e401000400000599450421503180240d004020180b01a520200c0180c000b0408042c10750003001400450300c007607510781046e64102c610559000c1507080f0700c850100e080082490341030b0000c4101040c04010b102c0320001429031944104121002512035010f90006e240c0300f1200180080c900102c041c00302034001f102650000c0080c01d014001c182c072480000d50b140c104032034502605684004100c2c4848511008180c5058141c480708103541d00448002c1d11000300611100b10400d03540b001c9100062080e03010140c148200700743d145141802032182d186075010710803020a200c104c260140f23445900484807400c0c1100d14240c103200d50310b0200d05a0103402030b80c0c107156050080c42000c3c008580c103070082c0a40300b0004a0840302c3c0c1c1d819031800f03003000110740d00054007aa150495030805c0500e030 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 275710818 1250 275709568 275709601
    0xe04080901090e0c3018060a180807060b03010c0c02030705040605090708250903030305100b0910031d0c0a0801020f03061e0301061707080a11010c020d060c0207030317 74
    0x20b60486045410940424a200c0e407401400c85401070400c80412042246d58181d40c05840e4444040d968a902c5d02c400e40029030b50f0301c103d0500b4030281d2004a0002440031801000f000c1c1c840c4401250040240c80043e0840303e6841c000008112a00d4401007149414403040000c1c00c1c044808004c06030a14001c1aa01b510080003102800344001c08540c885440850b908144220301141a4034124000801022100300e4442100441e0400011901c4401d042d10745500307607051107c0640c10700c00c0a0080105034108000300b04107040c4d940e100c6105402d41c2e6004080d20122440c010841000d241c0140202c00400e50b0240650782d00c10700c04140644202400c4a0f04080229612104460303001c1c081d1032400340c0948100e61541c6000f0b40000c0035030f01364581c6210b208154090710074140c2e030303014115202e03090a10024407036000056035a0303d560051000c112241d0001e040300c480c0400ca5030b208021107080c1c086143c0540e110120800030558040c0109044000038540288a0b04141c034055180250 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 275712068 1250 275710818 275710837
    0x60f0e06060c0703050709091a0906070f0e0d050c12030406090b0904020904050702070f0602150f130c03030309021c02030303040b040203100216110406030b0109020f040e04080901090e0c 82
    0x509044414801c00c0305a01450b0040162031050350b81f8940d62000740224642103c980360410303018450880400101841200070300c02809444d995102c0480701201403544020031301c40d01103030116190700ca610440700d03128454002400e0a4850f4020040441820b4218010b180e004120500009500030506011681c9017400162590318040014000c0d004d80704400c0d4116140108010402d540001e0a100b152000c01041c0078031a282c40e42240c580500291348001200c001700413841c20503000c545c0e140e00248640b0701003002030305075886207845005a0700a9001070740301c1d46140300303601d0400550682080c0310002e009190f02c1d0761b0702290300c078040180301501070590a00090305644091000cac64480030081c0045585a0702d482d01d03203070b100000400a60344001c0301c144403602d9003828454002aa6080b2084070340c42d07840e00c0c0c000006076004110003038052406000c0002d02d0300701d100f44d10b40682d200790100c980f903001e800001004d2981d079600c912510141c480a122200440320104da02200 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 275713318 1250 275712068 275712079
    0x8030703030b030a0609030c171e16080319050606130b03070905060d0c02070914040b090a1a1f140d02061b030301080607050403020f0d031206090609060f0e06 70
    0x1015200007400c1100066024005504120a040406a000400001c0b03e8484c4d0020003119109c00f60400160240c50a00720240e002d803038900300d102e10800058440585640d420a0131484aa074440c100707601f0030b903502035000e8103003481a4070140340c50007040e52100b01518803d081085440204e101200d20344a00000054000003141c1c01e40e01c120006000b40c140035019656400d449030154005041c07554802005008108010405403100e0082401c2e1b01c0c12102004159221500d49003407880018242031010b09caa1800200007440c40c40140351840000d0241400c0b82c80d20704126600c2e007410304024011004034000c10300c840030244d070003025802006c1e982c0c440b40c0c440c544085103480c400d15400092070012a001c01c2d5184800000460680300c100007550a80c0c0c071030301002d942d18015400001d41c4000c50800c08002c2e070070007240b03020565001c0d1030109901503070098150200c0d016a00300319030140e04c40d08280801d084034082d0030004c0214030401035015103040741c2c3e40e48002d0090080351040 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 275714568 1250 275713318 275713331
    0x50409060209040c09081203010f0311180a0906141003060f060503120a0f141c1b0e0f030d1409010e0a0e010e010e071b050f0d050318070803070303 65
    0x101035060b9020120054000c0150201802020f41505420301c01d00711103102e064643c240c801d400c08203481c100c980c1507100c00c0000e419a038807a0040d03842844090b4000d2a4000402449002c5800d410700034a800000029808520f00b041c1c0c2c10365108483c40422032201c0f005120643e48a0f80780e038070807030b07401990028030002080c001002800d40765209643c14459103014140030f06810000305401c070510344500e00f96900c04002030343e4001d180451564410010300001c03881c40d802100407144070743c0742e01700050034003441504801445d0790405103200242c0b03804036401103800c01c051200c40801003203004020048811000078000b4040e907027581507102020615202990081d404680c201c1070040c019071603e40c80360244441c00070b00348103406041e00d0003000043e0111004a0745805604695500c4601031a0342c100e0840203001c00c0d00c215140c3c8214a40300054600600089900c000c03d42c1d51035a417420720071070a4003401483e900300748494020715070030031900d0340020032642150350600340030400 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 275715818 1250 275714568 275714573
    0x3060112050423011e0b061905090d05060405010608010510120206040801060602061605070809010309020a090e010b0111010209030d0f031e020c0d020a08090f0604080d050c15040c050409 82
    0x44010020f01c1c0c000600041c3d07048011281034200c0d20000c2030b581a45000d1250145a840644da69202d4042e004001040040000b0a0105d2904840b0303002d4188075141060020101380742c0b4902c5001071b5074642001c0180020030000f0300810008200b8a0003c1c040341c10090307107110000c1c0c054411504c0f6500b480030003030300310344502045e03078000c00c0e10780001c0107041d07542c4402949a02c0105c860200400f56002c0300501d0500a10560f18441c0d04a0411350500110800540003044034070002da901c034500410005400741240144240b135500c2200115503001c820b4005800b614641c00040d07085d90040c4110380392a1000039841c1a01485850042c6c0c1c6c0451003401070b0000c185002a02e142406c4003810007000b51095001070582d140488220340d502054044126141d9841c40c0c8010900001000086c41d40c0c030b00a40f2034602a2002840c081c80c1580d01d0160034a00070340801c400c0081030b00840c22126248040c07010201410b58101444064070306a030310580080e00c18000c6511880d03664501405 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 275717068 1250 275715818 275715833
    0xf040603080d02070521190507030c030f030b120327131d0a030e01080604020a21020f03130303050606030c121519080105070f0e041d0604150b0105030601120504 71
    0x40303d400072409041c13071440201010100b68819903841703a090284100d6202d440344240c0440c9c09180c1c05658401c80741d1640d5504442584189083c0c01c20592a0000703a0044c1d0b50301000703c06500501130041d581c0310103900f51248010980100c4449044503854014050345071000c0d10304182d240c10600048940a2006258804e0031400c00004544074000011040540103091010158800d80310b00c40b50380d4406c41088245d20407010741e0700000310503078405411010300c00f828020700c034008503015081080201d0640c023250011505000607100b03000251090680600c12250002e0081ea552440d41c540b00615860310320515446515060428000a24001c0c1b01c4c1000040c0c00c20040c072502100244456140074800306010784c050310751a140c04200ba507402240050500051030f110900007501d04410400180040d070005003000b840380101158001c1c0a1100ea072107248900c034804c01c2d84005c0200b42088520034104039052007070400500c0410383c0c02030f803201804c0400000120b240e035524940f250303 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 275718318 1250 275717068 275717083
    0x306050117130803040803040204061203051b1903021f1103070513050918010c020105090a0b0406060306050c0c0708060f0c13030210050d0b0324090c0303040906050f040603080d020705 81
    0x180503c0021040c001003020803401540101e000704c4091001c05e0321419000001c5500c204010302003141000545011881c41c0c100000758110b00b400c3d41d00000e89044040c80700001d11904074010b0b085001d68080700d0b42c0c00c9500c2c0c000c81d00c0280e4100302e450724080c940f800912000e841e00c02800404200b0380030002ca01441c80700940405040a140c9003408044d245000b10b16000b002415400c1a0a0304075403071051060030311400d560300007001d038812942c8909032040b00150064403001c2d201c03c00440860058000c0501418030342c2809035507148504c2e091401c00c3d0407038200c000300b0380001b030030f0164035203090382119001b080940c00c1a03600c8a02404c400442000c0b580000d4000e9140c522030a602034202c2d01070140c00d80011818045001e81504154551000039640404a00e5001a2501c80e0806030030341e990211001003114880c030b02c0c030302c0080e2460708240e01c407059941d1104014451800e0100254881e154142e03802e0081c40e0031569000c256004102e01d1701d25081d400b18800c024040c00b0004034 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 275719424 1106 275718318 275718323
    0x50c010f0f0609140609130609080406020d11030304030906080a1805011a0a0e0a021606111c0b010804020103150518090c01021b040f110309010603050c01030605011713 74
    0x141c61f042045282a24a10358521040001812400040002d82003e4005145191862000505014044180c06c1c4160000e0043c040003c2d040743c0c42d0301c181c59440c14407004503503813120802c0041000f517130456041070300d006881c8103109065200441d9a0542032030034130801800d00a001540c400e9100340c480b07039083c00d0005001c400c0300d680904038a51200c00034480c1420103403103150907980021140c0d0409200041c808030111515032810510358110340c4140000d002040010382841e2000340064140354907040d00300d8410b0902c080a20103031900410040c40d440d21803030a140f090b0750440398110144181411542e0a600000e500380e6050304070800000401400d070188805405958105140340751206041111425180c015504c0381e984500001141d92450620914001d18441c0480c1414600b020a010903640016503140c171a0506800c0c0d074403910380990003801481005d501 = true := by decide +kernel

theorem cover : BRFrame.Cov 275539568 275719424 := by
  have h0 := BRFrame.cov_init 275539568
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 275539568 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 275539568 ≤ n) (h2 : n < 275719424) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
