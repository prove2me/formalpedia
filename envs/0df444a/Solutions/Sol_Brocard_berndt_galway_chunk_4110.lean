-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4110
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:36:07.328136+00:00
-- url     : https://prove2.me/submissions/e4392c66-01f7-479c-9db8-59827b7b2a6c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 739028776 ≤ n < 739208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 739030026 1250 739028776 739028803
    0x1507120309030e0a15081807050d02040b090c070c05030712120c080409090b0906060d1410060f08010b01030c09060c11030a030509120102070804030b1806270708 71
    0x70303010768005040c40340100001245001d860460301d02c1c0c079042843e00d160405040c0c0404181e09002041c1212140c0720f008084542d004060700e00c06040c80b0801c1200c52800e401613034401d031912240b01480d651740c20154040c0d41c050106683c0c0b0310030340c680340000030100ea21551094000040400c8074000002445100a601008400b04101040b000341ca0b048013100000e00302c0b0001180104e000011a0300c51603030740d40a540f0004256a640000507591581156440d8008410305a500d0000d43c0c1c0f118035100021035003040d41c03000d42040e040c80d011111250b014030b84008003500304010f401828072803402c01c8402032030148030891000001406200300c030302c07a101c00c01030903503082d00510041800b0040c0b8050001c040e50742103c001d090080c8603401603010700d446100f004d1043e200c1c0e80414400c132902560700681050a2034510b0b218021052001004812030580840445000c10340c24020740d8810342c1d008950f0000014003441d56843d00c0c006440d06181a403040b181446020700c0064460007001a = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 739031276 1250 739030026 739030031
    0x160905030c090c1303080903280b0702030c0a030f090506130513060902031509101203030b0f03011b08010f180b0616060507021515040b01090b0403030203030615071203 74
    0x300c484403c00d241c443c50803103407490440140c0200c20000000d004001000c401c4045504808000e030751350455048001d03410700060010f03840180002c2c0d039041602d80c003680c0b50054904280c0c82c9030302d090419441d2102280007400d5881d21a01c4d403070300000b80d800504000d5450381d041030303d40c010b10203007000140201880307414858003443c0c0c02d10b0744d500648083e108050096450342840f17a504541514035144aa11075036002002440c0c1c0210355180000700c40c443c04070900d40500d03030b0b10150000e160b00e95110f50080041544400a500c0900400d0a04c4108001c18460004c1b00d101c02002e000040c0c00c403c8034040507030410400b601429a080346461002c070030000360009a030000030f00d01d1085180222080301840f24460a02c9400d40c001845035150b03400307603140c201030307070708120040360301101d012054010b41e1002c121142003e82c03003a54410b2040c101102d0781034a8036501c04160300705500490040e440081008214281016054120b500100020781403203a00d0751355461402c01d407a00c044c20150f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 739032526 1250 739031276 739031281
    0x3031b091806052d150318060912160c080f010e0c03070501031a18010e0603151807030b0901020d111801050f19120b090105210123160905030c09 64
    0x354040810101c1c400005e001582c282e43d424008261a00308071100c21144540032507600c1080e0004c181c1610620f0305801510303110a008082c840307160495018030408031042c80f090000281da0212004c06402e50340700038029410b0b180091070135610040030100264101040c1d420142d20006441020ba442c00d00b0003055503181d209a00180381810605658010b094590200e4264016035aa906880e207205400a40341e441070f0906559066034040440140700d0300000030f59203210201c41c009041d119a00b030794805556a01d41400da20b00c15034840402d42d60008003a088280e01e44507287c2d84404019905090213000381d1003094804420240a050000019040b4500301c1d08a045a5111111804902c3c90700301070003000b0121820a5104a0f00b2441d0594038480d610302040e02c0740c1244ca0013480c42401040082d01440e0342490306118228a6403600110090303126007104440031108080160b22395468030000340b2801c04c079030340b1003c4107100d0108014895903d0119424492140c00e8650380d6154 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 739033776 1250 739032526 739032589
    0x603170c0f24160c060b0607050f06180a0503040e09070902040b040f06050c06011505070605040b070e0a08120313080c010506040b060405031903031b09180605 70
    0x164241185495801000800540302d03075030007040310310000100d042c0102540c03240c01c81c4084440c1ca01c1c44402080d480d00056000400c03035080740240600c0940980e081c22010394916242425070200b40d50540c00401c10402110207051a030504c0712083c50040000c0d01480d103a00f600c0740310b03502840700349851a40009401e04d40c00c21107036004020300c5108650361561415408a19045402000c4405901101c0024000c2c824003c3c0d50300658150050100c5910380501c0c00386810185103803b06008041c041d120129445210742803003540942107640f91403810f024028030f48072500c0d5a00307100750003026050108610000e030300743c030303090400c03e800c3c1da41e4a503190b08410607100080f0040c41c1c3c02000404480b641c03810b41100b4011082520300340b02178640007080081600503406010340550206400c91000000e40c80c03e80481402410002602e007480403904000d0242c1c000190041801660300300644c018402c4a90f81507904140104581801c143c00114028221081002c07075200d441c1d84c441c40c8 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 739035026 1250 739033776 739033783
    0x190b0a0e13020f130c0801121509060f1a0405090d02030a0815120d091a090105130e04031106060108070e090a14070f090e1611120d0203090c03010603170c 68
    0x207100300401d030a00440c404000e44c005040202810320000d20044e00000b8000b421180504005030b002034143c4c2c40f624498020b80c003c28406d5419a0215260b101c0100240001e00c500c0347d052440081d1008006403a0f41408281d590240203121141e1184010680007540801526143c031594604009181c8409040740d10550f00c600005903c030b40c07030000103280000001983c3d2040003068071007003c000e658200840c00c00460b8192740c0d440510801805240750b100304028003019490782c1001180b651200f0340c001605038200c4040380440c0783c0b0484611a21030810200750b01c00000d1070000000c0c40d000400810046401c401d80b400f481c0d82c400442c940040715005040c044e0440f202c0741ca00b40c545000000c0c482e4407401d50042c007044042c0d0000c5030035982c060000748504001042d04981d400c03158030480300114106c0300d0040f50700422544d1540d01c003140e40142103101c0b100320007588908121440b00d050030220303400303240709070f24050040002035081119215100c0112442517180e500502940b0304 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 739036276 1250 739035026 739035049
    0x50603090a0203160e0f0103120f02120c010c02060c0702060d0b0d02030f010501150801140d050709020309061803120402040b13050c040e0709142205190b0a0e1302 72
    0x605021341c10104200c049281040c1d021111813010604007030f01d8070020030075001000c0c003014201e42d100300b06c03580d920f901841030349074038014610495400d818500d900e10403076004030b20a0116030b5114800f102d40c40d64100401908900014001d030700e00740903a0300181407841901013001c0a03a0300c4409100043d510303502140841c40c0c025055864901c1e5080005000b03010901801d1041c5147c600302010761489840c11506843c000c4818400420f54038040000790340303218a0894580c80b825001046104441c009140104151001020300c0e05200c00030020541c007130f035007058540c0d0007406550f000358445100250003d4050342e001406502d01c0c804210f00410307129885024508100910458543c0d01005104582c040c000313141c00c5840b03255049894400c4d9105001e840080c000d4506014646800003141030030f203900c18a05102c280081100c10b850045510000750140a90b21054624190103425002102180e08240040c14007051002d4004c000e0100740492403c00507205c1151100201143c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 739037526 1250 739036276 739036279
    0x1050904050a05190212041e24050109020705031204080904111b061006181508150103150902030a090b0108060915010303051c140106051e1201050603090a02 69
    0x7005140000b5408041c09040d034205010401134200708a11146a10a07508003003603001c4804215140d940b6110b0b100d010421801c00641802c9801c42c000030081c1c81c03856000c2e0b000031600345001034140448002c54105a0000c102d5900410a08000036808030444018400d5886080c806403241e0400102c81c3c01010060358010b4a4000da0340441d840000147c03100c000c801c41c0f44454404500d80307031915104250345030401c240b44540300f071107135500803400c0c062407901c564403e81f6016034805401d8850796a000014000c1071040091002c3c112000241104584013800c041c032800e01020f280307485d6035030f0301d200f1105140e50204c0821700000498211512240c2c0202c03040f40f903540c43d013103d00c1e26108190307010301c00d9104260011b19031008401c1054101d9400d92074083c10005503d10301c0d013002da51001814992a662845c800c91903030310240d50781c041d0410f552001c1d01c0d2a0404034001e010045180701040035101803060004500304041640d054800135218181c580d120100c1e4285001120301009 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 739038776 1250 739037526 739037531
    0x30d1e0309050d03020c071719050a051501030209060d080409020c0708010905161e090c030902030618070e0906070c03021f09021c1a2d07020d21090201050904 70
    0x34000554190040c100c1400c1603c19282c50aa491003920010480b07500c5010302c5802c00701d0f40d22702c500c0340803a40840d10b03400b96058508807005691000d0030411103c240b03a80f12550080140207500300300704100e0f4003403c00da0b00320000148076214003849000724400d514a00d074000409903085030b01032201400908620000f400711080c5440c2c8540c13145a200c102a0508210600000b00014207041a2003030761041510000c0d02c0d41010a41c1011305562a1402e00385502e80c205000141c80070014588694650741515403188810030701c440c10448582e000045000b043c0080c0701c4e10040104c2d0042d00f143c400e00b02070803240e0180c0380503410000001c242c400e480000710300c4600d11201c0c607002101c9051003260f00001d908031781185c0103c2c8008030b5101511000d8a05002d40310180d090250746d803c40c041401180303d8404019041c1040b1048030f41c1c2400410301c0509211290344c0400101c42072000c4c504000d05000d1130900e0503070080540443c445443c0e511003a00509590048080710f90080014209 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 739040026 1250 739038776 739038793
    0xa061a0d150c210b0103020403021003141e0112020a2412020301140d1103030a0c2108161407080a02060a0b060d09140313060806030d1e030905 63
    0x2003200680c00d107010300c6035414042c116590724420100350300d0407008100b00700d103600302d8120043c0061038050030030360500d542084040056036842285101945891b9030200740382c51003024490011038042c242c0c450b000300c1400700f10240365091042c05d042d20800301c1c41e0120f240a82c0000303807101d00160320030311503140c04105000b160f070030a8409840d04509916100c0c0e031680303400c901404900c0248a0504d0418045810781000e150040c02049458064440300000704041400a815540000c204c00041030148a4800400842c113008042c0c0f080700843e607003a4016035400c068200c0d4001055601c46030046102a0503150040c400d00f0808071000140381d80301c0341c01e0b1600b071807540c0c032103c10362015202e03907000204a0000c50040900b0003001925030b41c104000c50504c100036001c81d100c00c80384040818004ca60040f81080980015184080c0e8200401d203072500c007828003000034100078026045040c2940660360080842c45030080c80142c000c0c0e004242440440041000200c018510300801c0754 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 739041276 1250 739040026 739040033
    0x31003060515041d0c010503040b0123060406022407170a06081b090a0501150f0509030615100e0d030c1a010821040326070c090501260a061a0d 63
    0x1051043c2c013410000c071448181c1c0f4200550f0b45020840d801054140301030014803060000a40e40c2c810310308030f20354000341118448005200c5421031380040c00141e20110b000c0010350000c4c06248501c0060840e480c1d620300b010600145030b50340140c2b6803040d442c40640030482c45c100170b0b44024020b0103141d007034030b00291904000d01413101888501d1849803548101040c400e242610506041310080051a074043d8510034041d0780307203031002041c1800c3c00300030310202425860a02600b4403404000d40c0000303071604d0500400802c14644009a020841b0514011403661180640c90030095014244206c03000e455250400380b0300321a0b0301c04443c8140c0b01c0c00000f624000010700b08251203641101c5420100416484c02840c0a6440702400f54484d014a4000b000304c2c111040b10610156410380b4138154998840400e000c00d1540b21600703150f610310041090111003400018014841c1040d0322001805030046a9500c0f040c040240c501c80c0c3d0f5000780c000c080c0c03c030407503940400c00207080c64182404608 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 739042526 1250 739041276 739041311
    0x60803090108150a060e12072414030402010309110310051008210c010b03060411030132270f07062f010902130b0109050603100306051504 61
    0x14003440c081422180400c03a480b41d800d20791040000c0280066160034036008040ba40300543c48501a000384c00990100e0490b079060151102a02c1e880381e540300c075411000d49200800d00740218040400c90000c05a038805188101100c0c0c21030b40900e4085a802e10078141000043e90722000e140e85403041e10504541d82c4000c1d0090f43c07203141c0e2035440c42c40069480e80d2503030712110000d100b103441c04901c80e0601c00030003020000c0e18865141d030000080c412150b0380403034a04501502c0c15961076006031121900d40c03400340103000d0300038003c258038820b0140032400907424074250442e6800001e9818000f8120f030002e40300074004040d95000c203003a0021a550300584400210401801c180a0124003041e00c6000e20a04410b00910800b14400c00c20102030118040c4807a402e207074082c0d500c459100000d07988880305045035007407500c000600500c4a0b8000b5000c2007460340203501401080c0308110310413102d50356007004c83e60400c3c00032800d583c0b0080d1001d6010351120303c460f48a480c100c0511205407824 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 739043776 1250 739042526 739042537
    0xf1b06040b011a0708161406010f0f0605040303030b0d06020a120f0e060c03131a1801091511040b070506090d17010909080c060c3c0a050d060803 64
    0x40000189603600c50b1100344804006210780103d101c0208100800180d10100601c0805180340c4000d0300038070155246070950ba0141e40900d2160b00000044c014900d190b003007a4020150016291441403800e04e0140440c0140d02c0050281643c4103081130407034540092208845901280c00c550b03e10071100041d15503000b001041c0340141c40c020b005215000c00f41704101c00094010028103482e0350303404140300250700040c280610201e0b11102c4200160704040103180750074a42034855450300d0303c1441c400c1202d00c1c5480100e0941c0c144004640412904e942180440714001c01c0403038584142c0c40da50440b440355601010329820700050320710611070081031281c02105a04103541c9001c1011904070362500e0000d81c140d00c1164054010044404250300841c0c0e80b0f407042111300e04010411018900700201110032042403040003802150070041c04862045c00c0440d502a102100d401e80c26800c0b0380082d08250344401040000c010070164046c0061301c00344042c0510901c2800d032202d00c61601e94000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 739045026 1250 739043776 739043783
    0x201020307052a0102190204091b030305030a0b030c0a050111011509020406091a0f1303021306150c030203040e0c1306050904050708090a020103200a020604021201020a140f1b0604 79
    0x4040c090750303141d0b01c0441c00481c00c50418014100711011b80d02004000c08035072508031181e81d0407030701448040c2c8084684800039400390302c2d010349a18040d03095070151003000f640140b00b50030014030b00c03600395203180300001034440030310700303030b01000c940102c035174010020310500b0402d8a503e031100085c007611940050054540035950408456610f01c0304c001c40e06a003000f010f100c2c04060140e50b140c030300040d0280c410030070401480a101a940e80202e0180c0d80d41d0341c0301c00301c40d42c0c880c0c00600407080ac1085035a0b8025162504050a801c192402034507170145005200c00c80c8004004141015800019a641d2019151551046641d1600c1c0030380cc551141c1d0082c0d0103103003070500241c0054082c9503010310a51120300035007144d0090b9030044000308140c2038000c02414807526000c0c5003951140180c204250150005c00e81810103004000c10f00407045900012a130041001e030007981e51100144900d0085440d141e516441000d00c0300e030480c020b96030100c9285844060281c202d440003c0c00b00c1c040c3c2d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 739046276 1250 739045026 739045093
    0x1b0803131518120215070c0f02090f180316020f04150e16021f0902130f0b12030f0912030702060d1e0b0a21081603020d08150d020102030705 62
    0x903420402d0f80c5074075050b800514517049000018109900400d101140f03903104825281144074594001480d00c54142c035440502c3c0c03009420048030300c403803480303c0240800c10401142041110400c07107464080c0c7c280e00a00483c070000301510191039541120411410300c182ced0303034059926500a010404030803036544003040c5c100c2c43c40d030a000f130001c1071900c0d1000302088030000100609000300040e1498402c04c9800440a2841421f81d585078850000f40c1e409034600407500c210340800b007200b080c0702c1e8048200d45800c1000b40030901086d000032280d880303c060700c1d203101c0030802083c403074110702540c07102030f4000000103100117030b5462651190141041c09440f2a00801034600044100d9855000031501f240c1c007010203020064200801700203e4110001d81a02100ac50b5100c07003090300210711100d01007511400740010150144848481c810480c0381008061500c3c0040b010a50800010309010f5016001c5901c15a40300380700b101c103072680020443c0c92000750f00e100c0070b85500c8000c03504203c4a2 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 739047526 1250 739046276 739046303
    0x1409041d07060e010806310e070f0b0910090306091b0b070b0109051302040609020a0f1e0503070e1804030f0f0206010e062704031b0803131518 63
    0x2c1c003c5040d030b402020b06030345144160303640c08180b00700608401c48221241965920910806521100c00140c92203c0e500c00301d400d00300e0700d002902d883d1461700030302e0360034240a03814805020503a056844401003140d80c00d1060810b0402520114090340001d843c0a06001d40c04050005241034034203400214440717034580ea0380d074180d4003543d80601180105007001038001000f1161080c0c0140390000420b29071101380000643c0018202c030306560220100c079401040741c4440700c0d040140e0903c4006103080c000000d0000c4031641214202c00c20383c0106104004c00881c20b018406d032412803944402600d05002040301f40440c40400408030342c11000a5680c80b01c2100c020b00c603068a507182d003160f03002041d007030342041c0052000b09002072409030000e0740807203c2c0c19179401c4140344990150074903119054038202406c0080041106503007200d49401f4800054000440603022039504c400300c00d455081c030074014074100c08420b50b4960961003a90400028005540c036468a610545220310034034212031 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 739048776 1250 739047526 739047539
    0x30312101211041a031e1603020102150c0405060f070507051e010e0d0503040605031f0b09010f09082d0601080c1c060f0c0318020906011409041d07 65
    0x14004404010321803001d8011440403400c154200c0303180411150710110048100130042440c040341482c00f2411424900c100030010201403125280d00c10682c03044864280c150380000c1d41e583e07001070059403d00035010024620002c080305803409840000d051644d10040f1000010742600404002d941d80c1c0a02070b8009190b107000c02c40005c1c2c001e000b01c13468412010b180c0c01034980c050007903142908417803014007140015109100800140409855031038480c180303030085004444c44a0f8a49040c020608401e01c0f400c1d505009403042c6485c00d107480c2008a9030320b00c007100c211240e036010581c2441086840e04190028010b01e2100c0b10202c03c0305005c0000490000d80d0702e220a1140e080c0d190003500c11915036050455105c11403000110485003078805603030b1004221469004483d072596900c000c00c1c440d070341c0e141c01400c0b08168010350002e0480d01d107030001003406001034001414070040c0705150703640c3ca2070001607031919100200300300040218842d408a0071100d400030343d8614040c5c21804500c9 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 739050026 1250 739048776 739048799
    0x6050933091b040302040212070f0c02150d0e0f0d0e010801031211031308070e06091e1012050d170906010e071707020715020102040b0d0f0b03031210 66
    0x1000041c00c41440e40c42d8540070500094034642c8103042c0410401010025849038001440081004c0300804c015151125004180403015280b20080152110410002d662000299059105030780241075980c010704850780020081c4119082503030103007509a1916810200750700c40c5c24651529031145010303480e030046a900d24240801400703d4005910580d04078460f45c1d010110340c106c81c0c110ba140080203041031000300c54540c41a1002c0e44201010300403004402d0340c16400900c02d403100d03034050070001e0448160343c000c1c200310350344510aa00007460b0031802541c0e0100803c40b240c01354500f0351250600c1521001d0300d0003000c000c60081a28180d14000d0411500c0c40340d001200500426401c1ca001e950240310060529010020801c00340c00c030103c081903005000c0d80140d00100403e514050070b103019107902c943c0308019644148810031040511008840300c828051900280c44410480c0d01e1000307000c007103955501480042890b24580114050840c00354815080c241001c541d1001074490 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 739051276 1250 739050026 739050121
    0x80108060c090a0b0702061e0c0d03020708090f0303130e060a06020a021f051e030417091c05100518010608071401110c060f13080613080a03060509 65
    0x3c000700c14071001c028440c3d2040c06000442d10042c0807600d03284000d001916052800350510000100004070140e00950401c4440003c42d1141800e5042c8040c50701c0360b1059002d0740300c1c03c9001e000300103101049682d00307204441c80c00100d0b07954205015101c510846407488100e540b98010154402c0110b400c5000150700c10300142e00605001907030300c11100c01c00c20080e08501a60503c01c00f4089010800c11800304003242c0300c2c0c00d582036034480c034140c180340701000426084003003400f400700f00f044039076100d820380309540043c0c010144004280303d00d407052a2040789881518014501018890b011407000c0c1080b5900c11500000e020a42e10f8000c1a502c84900e0311440c10f1004003407602000a5018804100d41c00d03403c031064030f05020030ba20100d04550301c200a01c204c1d400f80003900d801070700d450400401c0074101203402410a8078103900d5203000c03042102c0001d03000080100f800010300b8400d070050f82c040c20303028014051505112a504640c100c00c0d050540e61551512210240002c8a400d00c0b80c = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 739052526 1250 739051276 739051279
    0x10905030c030307031218030e100c1e050c0303071124040e07021516030e070e0c0304021f0c0606080c01080402061c06030f02100203040605090f0a03050d080108060c09 74
    0x14640707810b85d5030035240d040d01c608004254544840c01103a6900c141c5442104d00e50198445109002184c01004a1102601425414011104411000b1854007a04d01030b00d0b0004240e20f00c1c041509043c042e182c01e0381501210fa0510001400004100c01821b00c401544010f03590340e96803100e10f621044101c0c0f50b203182050100707402e000c00c001c031004041155400c03004034010b4031111420714080c0d0f155050308952440303900703044c40c806144981e03040c4600c0300407414800140040a080408811b44984083c1c42408200e42c0030011400b5999207142c0c01c80381144480e85e08103c585954800307840c910f01902c1c1510480d01d04000081c104a010070021000c1005946800e072595a0b503080290075004010b545064405c0e954420b40c3e221410301c20200039501a120503003200c04144100142c5270320400034001150414801002502d400c0006d03100080c40480c0c4042012000f04040784c0107819950025007988103034116040240c2d00024864182d1b06114180ca0b0240e8403040814540d100c0c1200c1c0740d = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 739053776 1250 739052526 739052533
    0x506160815060720030c060a170c04050d0c08060f0103033216060b04062909092806080c1203041220040b06090405040c05040203090c010905030c03 65
    0x51200780c03002a41818884014403250604109440b1024110540d86150b4652180d000181c3d00500c0d041040b01c003901800c644407407503ca500d8000801c000740c0000d03041c40042684c808500311030950400e1341c0140802a200c4402641c0b94280783c0c80d261441d1048030594082d100c042001c4812110351035058941503165070040023420811102c1489040501c015189010864101002ca80750000c103900c0c9052440788040071014102482203941012079030b0b1017180341450030070940100005106800402d012054101d50600000324014030610196540c080d40350300400c1881e80030300741070304115944074080b00c0360441000d0303a4208880a0380500e43c5664403c0c2d07400c0400389003d8200e9070041c42c0c0e03a01920305040d41d88112488812030640125030440040268078a061500e821420030745504480600903418083e01240b071340d00c22162001d010f2622000014144841035942030000c00018208660f01c1c41d10100040d01d1b40c0b90520060700040c0481400510303883d0002d40b802070120001c015 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 739055026 1250 739053776 739053781
    0x1a070b0f0c040b030402120f0d080a051012080f03330303040b0a0210090b01180501060e1201150612060e160302070c0e040602030109050108010e07060509040f0f0905061608 76
    0x74203c180e04002c0c000c0368040301e80180900c150b0030038000124078204880003045001600c1e60041c080c42c2000b00b07088840c91a04c0100400410400760580441e0408441441e1680342c0e420b00e4400342c1b01d10500c081440b18000180121038004c0c03901c0504442160558641c5c0c112000307030407100c0d984407441070395255205100c1032189480700d5000b0909200b03140101c991804400f60400152125404140c0d10300c0d903514010081080c01051031219060b12240c1000700e9810090007401c00c03140103070164086c108001d0651243c1e002503100f480c03041e00c3d005100c51201e540d003d009124951a048407a422030800c0c41c0000c0c00b03410480694090355948502d4400c9101c8820201d009401002054481c800c0c1c0740f10019651600f07041c0c0d24026801020050380d250304018011781944e8041e44241050381c940701440b44440700101c1d4a5090340d41a20b0000d50b900107820016002e8100c500005840d145440c40b00340340d120407a440b10403814440c0b015100c46c0e070b45030740070307994050708008010f0042100d0200 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 739056276 1250 739055026 739055039
    0x80a030c020a17130e040503192c180f04020f0f01050f09031615020c0a050f01120b2107080312040602162028061202041a070b0f0c04 59
    0x3030100440d03848081034031165169038000f00c5074406d54060700c00381c2001a02031102c091484040282000b1420104000b40b0017545c25606901038100d080024007210080070f4080c0d035202c0c5000100f280c107400b009058104005201102c49068404070b114000c014500f150f1420603481d08201d0040503105c007404c00c1840c006039180b0342d1106000c268036010711403204c0403081d403c29050300645080218440d414200309806450711580104061091039a41070402c00c2d0fa50b03284681815000c01c0c6000c907103d030020704040004d81502103110b98440c440040c01c001803440c4030915801082c0c000216030710135a0711050180c80b4881c00000d9948101000b0006011038403a0b002003072030404d00120951070380740544a00c40b807106410075101d42062040c0004d0a1450440503018419804116071a02080041400302048005103d440c051040450310031450b04074940c1610014040c0984082c0004508a040d6116a0240c14110348009075034010509079520504018818070403940307010700d010b0070310a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 739057526 1250 739056276 739056323
    0xc02030c132f0f091503040b07082406070f02150702130509030421050102030c091906020606010f0207030b2502010b06070f0501020904060b030702010c0201090b130c12080a030c020a 80
    0x14200c5402a0005c000d420507010440003c52145006840c40212400d0101c0000c9c410a4007030191a00d42c102c000e41c24170ba086138105180c640c10320450304580e540403646448003030600d0301140690b00c000d140ca0a081c0c0c5c0c0c1e0156001f0a001c4d03108a4521000301c0d540c040200c1103070b00c00e444030078041c1d0051009002c403200c9910815014103c41c0505004081903564040c01e99200702c412000c8128085900d984906184458070181d80001d181010b0701410004025038948000703125904001640e8407403010715009100d40e0000d5600142808000c0c903015000c2c0703507100140da01d4842c0c150300c107011640c1054410711071410b502d280201820b140c55401d8440100150390103800703445c5035508101c0080144d9441c41040c0040c2078400656440b441c0c40c0c04040d007100e50310340d100810359041c0207008000034200002c1d907500080164414212080314103008241c0c0800d80c002d8100361041c8002681800075400143c07010550b940c0d402d0200488179002280c441001e0302008107018034050b103840c0c0c00c04101 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 739058776 1250 739057526 739057537
    0x1804030503040312061e12032309040501030b180613260706090302010c02010209010c0821042d080d0f020d060b030603070b0405030d0c02030c132f0f 66
    0x20320788a10002a240040300071140c071540050100d042842c2c0d440110401c0d82c1b4184014001030000380403500c91500e01401000c40030490010301126407c01e86c140440f1401650302d500c1000d0000c00440d80c40380751254880506860300284186410360985144400145c02c91003054442407200480c0c1c1a591030700d4400703008860355000b80d2146c28140d0000e116110180004030301a000200f403402c07103418080c0c2100c41510300d604c116401002a81c00782e0341c004007030812240c0d05c088030603644c3e02d082c3c2089400c1c18084804040030000c8030b00740814010385642242034040002021b0f0500003418680d074903a050030f0b0500610800d003e0158403c1c40320540e12052203841e1445004d86000f40810007141110240e0300000d04901022083c4007203414100404000380c0f144400e00c0e4a4641880c0020340d49100380c8407400c0411110b10038146c11900c01b40300c01940381d0000350501410101d00c12024006d0300700c000401c1c0d00c44109004403034001c503501100c50032600300190702c580380c001c0001c0101000c0d442f9 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 739060026 1250 739058776 739058783
    0x513050406321819020c1207061113080d081306020d060f06031d01200a1202070605190926040f03050607080106090612091e060209040b180403050304 66
    0x40001072029125102d0301e102490f01e403030000d00c0300d15086000380610005030004040b030038414455015046c03c001913003000212069802138492032180b4203600a0480c66580304042036011800222240c0144d61000985401500781c0d03803010000c0c001141c240380c04461034800cbe408215054030101d42c0c0c5138020421200d9288011a050340c64465005088486500110010fa961004440840c1418200390b040c64601c80c0244000400b801c4180014a000346010304914000142e41306958007620440f04612407200066445042d0ba090620040004550404135560080c0302032001e210076208010f4455400320048196020141000310311202c91040007907a490104404100b200c4000e141304021403282c0002e1500e03103003d600c01003040c401070b0701c05030501a0381c02090240c9074009030460a4080c8906c400603002c0000e0070000c428032203d0290501000e441103c91081c07100d290000d0810007003d64041c8a81c1c4080b80c140541c54800c0882c1d9422120040041000284034000450b0031501 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 739061276 1250 739060026 739060109
    0x1207110f010e16091b0807110a0f0b130f060f020405030f0304090606021c030c0306051c0506060a300c1d01050a03120c06110a0513050406 61
    0x980c804003400c45580146000c82c0c0d40c41506080007a29000310150082c2c40029014400c81865800300041d0503c0d0034811014005c0c070ba00010202842010728001c0d403c00c51007125040111030801032020400c07080d00b41c41000e07414002610221400c0c01e0306080552204400501071602c3d103450f40105a4240000201380d020440006d003540d0420a0f10710341120346011b55911498501420704a42d0503500010640d0080c09030640009601c00800308031000380d040c00308c3c903000314420803801070544d9081039511184902145511a9404c00401b11080c811000c071440c0361036110800026000d1882500c0800034041500008424030920000305c0910b8815051180b80603562500501d40c9650400456861003c561a46201044070404d00601065a850084906540380c1c0c40c07102692104807000d0000244445042101c50f5000b8411780496040c0c03140c58502452000380380e54030501070802d01512014020919190900c54081140d02e15544040c40030310420b803419603950b2015900e01c1050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 739062526 1250 739061276 739061293
    0x160c080c01020403060203190507080711160914060306240a0f080a050d031406221b08010503010b0a210609080c1c0806010e15040801020304020a0902120711 69
    0x150034006040654805e9502503220302d850385030821146000340030300c1e03009800c060602028641004014ae08000a8030b0920740d005201c03414a85041c80040d44000440c055560000319102d0f2a480840d45100f0301001c09a6038403110101650340009440030074000403120740441409070b0607005104119000750103007085680c0caa42ca03901d40545940002110b4000c40c100b0000c020b418000d5540640d51820b0801070314111085404000d9401054140a03202103200e10a4040317060a20700100030403240180700040140440c2ea014030500390801d00894610300020813289018007616070505000b401c103001480ca4014101d800d10b0300c14102050001c800c1040340e0105030130b4011806003a0240603203a98501d94500703440e180074a18090b080201c0d20b85000d803c55036510001040d0010400d191a100510000740011040380c1c1c200c0c4484410400054001400d403010340146100d28003c84103100d60302e645900880c141e100307011740d0304286000c0b540084c090500071095030045a50ac18103c0c1c0104 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 739063776 1250 739062526 739062547
    0xf011211030a0504060e06071e0207080d0c120203030c0702040509011803020c011709030d0c140a03020a140327030c0303040f02100807081303050c0d120515031005060609091602010c0503160c08 85
    0x42c1c08080b0b07440000b05060082ea042c40100b40c40ca0008143f20300c0103601e140303003c0320008410b009255000348030b6620b07000400c1465071b01750825900c40000154440f031032005860082d40d5407400d030140d030340400d900c0b10028004045c0ca032140d034032846c078001c065843c11426901e8000100200369a280a2003134520000e442c0c40c004030701604401c0380c3c035100180d84e24a449000707800358a100108400108040080200000ca100311071001e101103401c021007803101c00301c0d8a9045010302100d05030303544004002c010034801c0c0c040742440300c07034000c3c4d40c9258101d07007011007258005002c85200010500b0000803801214625a8595100d8042d1400c282050700c11840b250078460880002400a9080c00000750140d000c5d118541c0c00c0004144800c2c840340407040400e864030f82121000c0c0015503070b81c0000b0380303c0e00c0d40403c883c41c2c6107001306001c00c0c3e4644501540c0154a003400030200540c40e00b8032414003140501c0881e8001c03015155100a00d4400700f10848001c09444021101100c0520010142 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 739065026 1250 739063776 739063783
    0x73903080d23040c091103010b070308070207120b0109181e02180a021201060e151602041419050403270f230607020f011211030a0504060e06071e020708 67
    0x2c0344a001d100311342c58501128002654108501042c1c1d501c3c0400040040144140413a0b040308d91501340310842d13549140c3d00382e0400d07500f60f11006040054800c9a0104a0000f800505076001c9050800c130701c0704840c0f0160803103804180c0c02400d04038242041c000103030000e0720758010f10784020089160300500103030071000c9100030b0b03504000c1107801088800985402c240c1d01405810781e80780c201e0448004a000a29102c0c01400c00884c000000810314400281d06038425046178014000b0b03c54038107256002c0d030030701c0c40848880000c080760a4032130401d001725008403405180c0550351040600e0506422180191000140100c007c4080b00f0025101200300c40f4007000306100e001d164002d4a0302c1349130540c402c0101d101e8912502c0f0411100c0010390701c00007905000102842c020840c40299000c010003400b2003818666161000700401100040e1900020b1040d031103100103004c10010b034101c440c0c4d0380a0948444010507052929800400520740b068041c0140900c101c0350350942c0c64001604 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 739066276 1250 739065026 739065031
    0x180b030c0f0705011803030218090f01090218060a090e0a020913020d02070c080106050a080708030301090203060102070e040f1109060904030302031302190317120406020d02073903080d23 82
    0x71170f23004039186a800380d14462003038240100740c6111005107028081c080401805010b82008136038045072010700342c2d0401444a640507400b0f402180d443c10302c80c6003c1c0041d009072040c10510004a000941c9105c3c0600984550820246c08800d5154107c2c2c055030107504110511280383d5401c2c0800ca0201e0b010189c407000405401c4000941c10b42428240b200001c1d41d80c2100c01550303c40d034420010200e0003c2102d044402c5400c0061300ca460b5200104d0400034642c0c0507450146080040c0400c0c0401803540012091243d601000c20030f01b8103050148190f400c1b685031740e1000320381000501081c025001198014401094903031a03d18036400503511252410702c203450381c441c031035061080282c1e180d1130024504600c0c189034184109103410208404005100808a40d000701c1c0b11507400425030140c550480d807010700c1a1400d1000030000318107141c104400c54509003a5407208050504031204042569040039130030749042e40c0c1c044410082c1000c441800059141c402000c00d81d0601e00741c0706030 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 739067526 1250 739066276 739066283
    0x203090d03271401050f0403110102071502030c1009020108040201030507030e01020c0a0b09070e04080a0315060315060302042312071806150f1808010507180b030c0f07050118 77
    0x50700e505141c0e94210043c0325481a6050060420690345186210300544044a81c0614040c00085003840100d040c03000c2580944120180c103110184040e8010001e01a01000030044411140701641d516041d2034100318040e0100b2100030114025510039042182d001c01d50b070901050340c40e40190700c4e0382260b00010680e00c094103d07890300c0c5c080242d048140f5400640707440c01000002c0c200381000038500c0c03019000904e13070a0009440c18100c0d001381c101456071b0301985407c1c00003030b549190207400b13040181c201c0302031800fa09902003501c43c02403090341e042e01d162100c03203501c6815003680a16405000c0e00402d9220003007181200c0700080030044c68020300802c4400038005100041d0660554130f1607040900c841d4142e42481540300e030b20400c2c200b00308c04940342030141c0c002054404400303814181c0040c40c9550a0800b0004c050390041d541c400c2240c041040307007514980d00d000b142c40c07900050b0780071042c40d4400c101044440340c1e45400303400c0d0140070300000642d1614034507441b1411011414200c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 739068776 1250 739067526 739067597
    0xf06030c0909150b06030106050a0314180d0c0b0606250c0501110304031707060f0c020c0a06030b030a12140703120e0d2a08040e010f150203090d03 65
    0x5040051024282c3d004a460142c10b0007411100380014805010500420040180104150818071300c240c00511201240503036529031750070b2508040340c80e8548032100900d103224051484841c0c51144103003900313043c0c0003e080c0e225034941c40100202a40680d0990780c1100340240580030b03c80001d141008102d102d1840c0300c4001d40707000c00140c018040082810361a803c20711040000c5901e0002c40008078500c030701003958138091490511300801c0707002a5050000d1804107201d1041d500021a080500c404440b00c5030f0a9a90b40c00881c241c5003503004498040c1c000740000303000500800084a62101d650070003d603444c56100210807950800c410940c005080700c8608100c2040c0c911415142100c40d03000740c00050b100310400b90850000000446141040c050101001e0804040031420942d020000d26501c41d41d410306a28403502c01c2c024912040b15005001031814801503610007090f8190f005141003907241d800b080001040018140c0911801d004880c1d0a80001c15410030701d2400d0405c80e = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 739070026 1250 739068776 739068791
    0x622061a0406080f0316080d051501080c0c1f021b03090f15030423100218190608190f0905011401050d020d02041d0624090a0f06030c09 60
    0x4000584000d6403200b1000d070044d8980041d6208080100e071200c905400614414001d01d19180c43c180c0b06862140c3c041501d80414005a4000613a000b18013a500340d8801e0346507281e00000c2410340c4642940800344d5403001140c505041c60300c200300d601000440d81c0050501c0c2e1141202d00e14610350030015a40754000160303e2070903180c1030703007808441b88080d6801c50100c003d403051030b8158400508081c112150300d160800c481984420700c00c0d0110781c2001031325180f000c48007645000e501712440024400300b42e07888251243c00c2903c40300c61220721001400041c40c0c94100b00351400103011f407a0b10241c107485d8098614401c11070086084280e041c00c00090250310300c0c00c1035401c581e0900218001240300c0f41c0100401d641c0d094010020740c1d0129010b0b100504140700060050038028640040e41c00c500151203101c0c400402c140f0f02c01e21503c0011080841000c100107000f4001607040780c0d0084d6040007041c84003096a0019030710b03130030007440003a03401e803203440b000060503665103d0760a0584402a = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 739071276 1250 739070026 739070029
    0x50d090e01090603170702150c030403020f10020309060d062714062d10030e120c06040f030c05100c02120301290418090b0105120622061a 61
    0xc80e41d0040c40841410007041d070860b511100c422561001c921200d82011407601c00b03560b140e281c80074800585403030380742c0d5503a00c1026441d200e412032320041c0d00c5800a190301c1c04890030119010609250a035000e1450700200e0f508120305600b01c204c1613090b42d5070f6040301040800c00103903021010061142c1d412010034001c58820140c40000401d01c0e218400c01c0c05019803919803500c100c0841d00c0d10404080c0003c0851002c9042c15011418194816031032141d881c04650550300c2181f42003080d03000d6504072082c20390581c0380c5204128038541c142d4081d500180114100381041c0e408603110f0b1a1204524600b070b10380034074000f052400d541910341e8034032103080d00700e4041043c440fa60500e686d1440c155031501c179050075100c0982050198414105d0442c0c1c02c0a003155044130301404103228000100541c102c0000c00409242600b101e204000c00d00100d10380c0f0701690300482e014102001040a96188044030410052801c80095501d10340c01110f00000e00034003a144030034400c0641203a0319901d040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 739072526 1250 739071276 739071299
    0x20606040c17061014041412160302090c0403050609151003020d060c211b05091f02071d090d080907091e09121701080d08090a050d09 59
    0x241c1d000340304052010140d4038111081450380040c04542c411640c441d508026900d0409140130f100c80754030009000b08800340f445410003281c81c000e4030b10550703490240004070398400902c0c040600f0381840d640b0420062818810384c542c01800400b1241c00c0540c0e99990710314040054403106500d400088600707900c1c0300034405040c0c0c043c4903054800d600f545590003194421700d01c0c000c041c281e1611000c40c9903030035001c5c0014008507a100c50b0100c03143c96040308100010500042c1d48015515040d4400202c14031510689a024900a0112003078080045102501441c191900d0707096000b2080002000948403004031007a41e581100031450f4a815480c250400741c8801170101441a02d006010316000000345d054107948a98800090070700403080445030103800424400c00e40d50400c3d8070780b01000310003007401ca4405107503198402400c0991708a0f0341000d00034020703860164003000008004501c23803d416500449180c00f40c034090b55154491604082d1a11103e40c0411b1920204103e0a081c51 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 739073776 1250 739072526 739072541
    0x10b0604030f211b0c03120c03020f07060509010f1106010f080c1c0b04110a030c080f01060b090d03030f0906020316020d020c0114090d1119030206041e0308040602060604 75
    0xb6907440c0560545071401400025592012013601c0c01d0101c02c3e00100020000b801d409543c002c1d01c020490000c17510300905210104c20f0481c014040e402007240300309800644d40b01903425645840341000040d600464102d00802044401c00441203c00304240509111141c06080c02503240306510381445441803401c5404031055005400030b03860780d12800c1c1c4006002a20680c0f240703842c02c0c1a11142030000e4030050394885240c0c030225400c000001c01c04804840d2085603911003e5a85043d260207400d4201c42e520f12414030b004d00d003045600f81d80d103003045ca41075001d031107400c0001716061002e440300b0846407051001c4649990010900088030250104442904407510003000d500802c44002502e440c450440181800101500001200084800c0d145048405040b03580c01441d1428061110442c1c050028003a03003115481030051810480b003c0b094035000740c083ca191600d400640071104540d4048a424016011404000100f03900010030040040398000c0888c0d08000b4104000c41360f01 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 739075026 1250 739073776 739073813
    0x130e07090b03060306010b132d0806042112021c050108030a1d011101050a05180f1b0609100c03030501050f032a030d0c1a010b03010b0309010b0604030f 67
    0x18810407a65560006501b419254001c2c50551101d40b8110000315000c05a008070100001e40d0800e11229540341070740700741203a000401c5a058a5607044000d85810081e01c000d0720040058800f646006024190030010710540d180007414000f1645141c800c9800110005000d034202d412241031080340742c02080d0140c03c0310340280d8501525410080e1142e829100b01c0c801102c0b0345034840e011f5070300803100201c4c0300166a0003480103282c0301800c1c10003842c046a1990030300b81480001c420b5210000b8441c20904c000380000d11040c900e4a40004074030f070b0b00e4078030654000810450120580c032500b800c0d645901c081d8843c001c16079190318000e000e40304140c1060380039910444c810180c541e00010712401e07240702000c1c17041078200141c42d01400c400025800390b425204540c03506107031070341c00341d101030280340140b200f1008009080c1c4403039a07000c407c0c403410301200024070040c804601e40800840e00004000b000041c0c0d041598080b40c250b4002d6401501c2607550309403000c082c001c1e01032402400411 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 739076276 1250 739075026 739075049
    0xc020d0507030c1104091b081b0103150308162d060504060603140f15090303060108070504120b0610390204050f041a040f020904030302130e0709 64
    0x201160020103074020350101604115520314103209000340d281c0c2ca60f10012000c2c0080c024441c2e41d003401e8922901030700c00d4440da002c1ca00320001700b81e42c0c0414160b400ba0002c030340500c240221a801100a0b0440303444410b40c4032940c00303000001510071002044403031101d0f041003c001c40203040c10712601405001c4041d604002d292210040e4003070401158009a200c20000740540301ca080c00c200400319600010178511021801e40010600012500305d0300410004036441c040f1104100b440044082e22300d140315900510120380c40e5801010300c1079000c0b80e28505642002d0340c8a00310204102d84281c10341d00482c5400a10901e82855403061081401d0383c04c1c4402d540707025500c40400c81103209400f0114a42c9500840026080905d0700002944c00810509c65400d120341c0ca4400381ca01580c08985080d0443e404d00303801d00880d040d0603c1140c20101d402d412840c240c0901940020090003202056804c00030f2040c2000d402400001414046680105074900710750042d11064881e00444441507 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 739077526 1250 739076276 739076293
    0x90e0c13060f061101182d080405120a05060a0c0306050910180e07030c06091e030b0a021b0a05071a1e0910020a0c0e0702060601030e03041a07060c02 66
    0x81000042c902124041d1501c0100c42c0c2c0000100c0340141610442d45521035911420802031262161401c8074112242e10703941c2c1e910390075404042c100352821800a05596041c00200070a04e400c00c0021000754100042d80e442c0340d015038070542400c204542c0d1030407030340d5114101480c1e143e051099001a046c103986050071402c1c840b903800d4100d40c00b4461a520729040705100850300196401080038465510f0803034210315200d29000083d503195010386c1c4002884080001000441c10441c44c550300d0000f03031a4180a4110344505282d81001003405920303030303020000d0103503100b070108880e030359000010040e0000d0751092401c41c2c102980d03507010325000c1600386030713900c4005c21000449495851a03d0002c105801c01280e040040c041e1112407075006460300000c4120580109590075058441e441007010700703450380786d4841102020b482c0d0200603800030001512a50181c1d000d845c4800d801030450b0f00b4184d031001d40b00c0b100c80c0440309200c0c80e00800305240c030070001a07014603403034100e0072f0000c3c24111 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 739078776 1250 739077526 739077539
    0x207080c0306180138012d030b06040303030504110d02011403091204120b0a0e19050c060f0a0e0102210d0e07090606020105101401080c0408120301030213270c090e0c1306 75
    0x7e841d5407109400d43c403200340c110000f05010b07a200d14600000034000d2500c0344e0362410301600501c01210b094842c0c0a0505013440a41780032881c80303401550586490300c0da41c600100600c0240c01c014403c0406103c0c41c601c0002c5032007048007a100400d0070084104245005140c140400710b0007410b0780088500f400d000358041d6001180503c07000101001c8400801c040b4144246000265015540c11220000d07259480812550041414601e0360316901001e0b02d03010012a940e01880400f42c2c00d048003413000c07400ba041079800402480710440340100f182c90010601e2070802c003240e800460495602c00082081c07580a005607035102d14001e16401019144c801c500c2d62003d60115190704000602c13000540010038041601e01400340c203000c551002c0600070801d4250303802804141c1c030072001801000c400e401540a4040003200d20b91100010910740c010140700c111511700211201c1842d940045038050350351007a00000d00e0128010100d022015083c01404006610415015410202c007130120 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 739080026 1250 739078776 739078817
    0x2d0f0705010c0206040809040b060d140405120f030a0b0f0a082a0a03170706020a0201150503011e0b0102010906110706060f3f0b01060207080c030618013801 69
    0x401068902007149c90003500012542d01c1881054900c9510f403015045412a402c00305601c40e0303200d1411500d1451903014400580d003d034641480007510200001800d80300e4507003281004500141c09100320703045081c005414030707000381c10030701d1603500181340d5000c001502180040340d03200001040914018803404034400c0300103408098000a41481090400c40703148085a03501c5411503070031500e81311060300090180070300000e24582c0783c030980380100d0f5074038041c4118080f40200c840b240054418100b60784001e440f011002d82d0565603600e0403400850fa070b078010010a140005012682c45040c0d107400340440314542c02c0142440e007607080c01e1020104400445a041c20061540b070100500318400c5c820349880b820014840c0c02d81400d00034100310815016605890464090702c960341c1d00c030154959210030584e0303001c4e45544080c02203140039603070422420090f40c00d0000814804030207001d0100601c010700b4501120015070508008000020a09212558091900038036001c0f05100340c400 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 739081276 1250 739080026 739080037
    0xb01050d020a05060c070e0c072001080f06060c0d0e121203010b07081c0203071d0a120204020408010e060403090608270a060c0c11040c052d0f0705010c02060408 71
    0x24071300000740c406010604019007401017110100a00e21442d00c0310b000d0301c0b541c0211004403414481d1008002c941c40440080c80c00b40301c0e06035a1465955174940b040309801c1c0703014009581102080080c900d41403000c2c45240a12042a11844c0c00308898034103020b00034080c030010844980014440fa8030014004040340d04590600b00e02c5038407200d080c00e0600652080010810303100d00c416103c4240d500d69500a10301c52020380d150000030365400042180707501810980d25a0142c101a0300740210b00c00c2d0601d085c403c80c00039000500340340c1c4030038449084940500380320700590300401c104800c1551042e035002c058541840e001829043c80d0125921b0714130386844003a004040d00e400d480020008004408a50380c10841c2440000540383c009010390020000079038001481e2003076085182050301490240c50940e50701d80340760444041100e1485989018480c01d400f06092244001840080140c250410300c1e003245076480049241950031500410704050664000f00e0410001c1450f40c0241d41 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 739082526 1250 739081276 739081279
    0x90709050102070f051011100216020102160e060618090406091e03020607030911090c0d0e19060c1101091101120e100b0604030204060b0309120313060b1503040303090b01050d020a05 80
    0x1750091f40e540d0b4510b00b0140385c00d115883c814404600740403006e2a0703e008400d607900130780a4582402c40d01c9000756001b60580110ba1001020381c000c15130a0410700014041d1207a90a5502040010400001c84026003a01e045d941e10f9102c06070341040c00a803405040240d07002e41440140d0800716540a5181c6c0e60080a8205040d61410550b080c03080030b50b0040c0c84400001c00d050b03041d00d001f0580d44525080440000100c40c0b800c42e01280400001404000001420030303914814104c641e248409002d2120240041200d0b0100044064a003401055034817403050000c854111140301c001400c03080c41c2c91130b1103081410170f4650000c0800c08120b005841010032408281c080800700414014803840d400250840c2c0361030380000340003a8a00286000b9094075050720f00c008020480d0010f40d0006886400c118a0411407940004d11654010712500f0310142c0b1360701d408185c1944408a5420803902503000c603465500d108100160391074000c1c050a8100c6d20405c3d140215004140700c040d80307000d040d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 739083776 1250 739082526 739082537
    0x6180c06200a12140418021b060705090f01080609060f2b1106040501081f0f060f0e01020609071701020409230a021e030a0b090709050102070f0510 65
    0x2644451440290203800c00e02400440b03512060528210020980a640c02800521200f6894910b030740200b00302c6080740c504540c1c0002801d00c480e9401d0081d80b111004c1c1050741450030f104c02156806100c124419400340d1101e540b80d4544006114110b03961145480c104202041000645c2d521400e440707400410039034a030005c0394500e80104c5c0034009541d606180300741450001400c04041c80042d03e04251113140d000b4210140c1005121403800744d8004c45011460b080b0004092070b020b41104400f4480700f4903020003a96944400242003800342d0480c100280d50071180810071900401444020002840200014034040282c80e0701c51905010340208115000c03100c00d80c641003501a80e01070315a08404114015015003420390805100441d01071100708000042c1800d0403e100f07070303401803c0300384030040000b500c040409100e600040c15070201655810b001c0e84291030b107056192103a003207501d544c10490700300350000e46401203960001c80d00543c51801032001d5144c07641c20b100c8910990810 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 739085026 1250 739083776 739083797
    0x103140a0e0c0316031106070515090a021009060809070e010b0c15100f091b0e180a060f0e090a1101021c0201020714030a0e1507020a08010906180c06 66
    0x4050802d00c1900b01181d051042220051400c644800200d080364858050040c21211040503c1054024180d000c1c0080e0448400b490041c00c40c882410740c44034541381640c203002840ea0002d65011501800d050000b0401481440000e4100d000b10b0341100c8104000c04525250229809460405014030000400c0100d08001c8182e000c00000095031002d800c99001c5141c11903001001c981103120707402082c4280700000a00308154410500c0034940111049005070200d03005941420711100000d41180d5a80620300300e945800e44228050000e43d80041001443c0c54803c2c10802d0183e0004449411088144558041c0011305900c2540c0d00809598001c844030380182e040007608503800c1c02084600c01c1e103600725a419070081080301d20400b2140d410714013003840c0715540c1c09802c00e00800f080e9054407481d000c0c039151104003400d03210706110754070345481a80451203045081d80048000c0e91240120010442c050280d020b0740c80591900905500403501c440c400b003d085e02c106401d2040c1c032000d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 739086276 1250 739085026 739085051
    0x9280306020a090e0c0d1d1c0c120f09150507061d03120402030d0306031a0a0b0406080a14120f0705070308180a0f05010914030106050a061206050103140a 68
    0x103d50041000310307840d206a01d4580b603002056440364107060256482e1080803040d1a080c1e009500c0fa03032500e07100400c56902e00314000014940030954184c203000045081c13500140c04000e69480b4100941d03940b400ca04804400588102c0e030980100258062407081018600d44c030009451b8042c3d0001b0000c60920240c0d91180c25103100003108041070b010000e610410000c1003101b8600880c42138080360350b00c00d050401181202c601e130100400110740219030020211000744416006403031940005100c040280015040700d1081d800018150480a80441840405140710001003540c03000b45c045000c062403e01114403c48400201c4c0c1c00000c100303c003d10070f04010304005150b0008480b60780b403110341c0b40a240c2c54001c01142d840788070040c0010442c08039145150707040312010703120b02d001c040c00c24000d680207200700312626030075660b2048002041c0c4c1c1c0754602500141801c0e22080007941103000c0f40300079100c0c1c1d13422143c149800c204051241c01000200c0907400008a0000074a1060708003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 739087526 1250 739086276 739086287
    0x711030c2e080118050a1104061d09010f05011d03250902030c0a0c050a0506040b0105040e01200d0b100306060206130f0204020d150f06022512050307080f09280306020a 74
    0x14007c5c800e02d0300c04200032454036048101194414040c204461030013030b8540810012034024011143ca01295160402065016030750709408081d01392810030854005102003854020140414003481800010380c0c0303000e003540e600247c054140c24006626600e8032840e80256880380c45c1205003000442a840c10501c54184001300e0807540c40000c0d1202c0c0d060a04110120242c00c4c007c4034421031601d01303003d445403014842c1044006c200d201d034480c00880300c1e010001039001030b05075882c2d80c2c3c1c0300e020200c0d00d030380e0b00a14100d0410f00c0b03480c0002c0660900000030316002c0020640301004002078071000104944505000b44d0507130413280540d5409a4604100140a05406980b03d0203078002c00810710702000c400386000d446c815400c507014a06070722090000000e40304030f100c88000c100f507006c2c043d44405215410015005008a9142803d9640c541c000b41e0b010a00150b040b00c80455003070990318050401032107000d403d0314102d00244555100e41c038407900900c0002d21840c0d001440384125802017 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 739088776 1250 739087526 739087541
    0x3021504030b01060f03060905130b062106090d1d040f06051003060305012412020d021011070b030915060102100f0e0c01140711030c2e080118050a 65
    0x141a10203584d01d85010302566840302c2c0000c0400d0624802040d0000e4030300c50030b44a00e40c410b000c0309416200352580c1b02c008002030300b05904410341441964060240400341c10381201400c00400203450803072611824141c1d0380c000310b03080188038400b40c6003400f4442c15200780c4640c100d0300000c40440d030364031440090415601503a04211310141190f14950594450030469015074028046101d440350f0120342179460b801e059228241e280401c5c0000d01c070007070381150441d1020384480001f4035a50009090002c0c0080e5440010751000440640f040084c01070000410381c0441003400d604020030700b65101c3c207032040c204070700e12200400100c00341c0c800c03c208055042120010071550050304500e0000c0c00306046c40713032850303c14000c1d00405540b04003000701c8582c401c160003904064640d6174442415149600c420f925100b80841514269244444e02ca0710050180d80b000c1a10780550724a64003d40705021003003844009001007003d608070f0304040841c41c00e030550000311540c07107451030002006503 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 739090026 1250 739088776 739088783
    0x2070209040807050601140d061a220608030a05030c030703140106050a03060f05151615020306010f031b0c05031201030c0512010605010e100509040509010c030b010201060e010302150403 82
    0x40428001800b840c100105581d600035400c1d40d90721380e00d400614020294615250b5041540e800c0c0d00c80200e2101e51104041407641c04004158042e124005104520340c55400c035040b0b00f0800c15881d00d041d481c49480c3c000c06c10341c030266040c0804a08003a1550000810841514600000041038248240d01c941d64850765010b0b1803110396102c0100602a03040550090042461b003803002c03841400105084c000c0702c400a101c3d01d2000241c0100e0034642d0844440b941e100200f1031000800035000c010741c10000c27405090b0050c0ca0780740c140001001c241d036480d0540c00303040c6040c10410001128480c12141401070b820442e42002080c50030525501c81c400ba803104030520a030021041014491640045034000c0b10038005c1607100710f0105003281c03003074810319001c01d0343c2c1010320880341030401c2003060310090750510702c1c1800d001c60041020b980048458846595481100e0301400350148649890715600384020050745041c43c00c80c204941040c0030180c45080072120494038000c01c0700450340650362 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 739091276 1250 739090026 739090039
    0x80a0f0905010516080405060403200714150a090b2a0106050405060108010609090c1b03034a1e0f07091118010216031a0105030f0a1104020702 63
    0x112410418000d0109072a0201040303129003581d0402817084107114010364210018118a407a00e40c5e040e500404020507008803448c234602914200c4030203010440c01440d0402c0c000e400c3c4001d0004210b80600c0b41705030907801c91024007182525540c005901c1c000d80d00e01820441c0d85107941210410302108283d000c503107030000030610210300c06040d08500100d0301c083d281442141c4403d00190b49001c402d00032400003a540042c200000c00c5280c00404c007030355650901184c44114803000510050550b001600800c0d00c841c040040d84c1d40d1070828a150403442e11200c00183e0b01e55850350f11000f0b105060729901811103800c000c820308144502d41115107000d62107240300f045d5a18881d107411a024030fa800c0b80c0070b03160000852140c0d502442070084d4811100714135218034401c0c001d8000002c0b04103030b411889a54840100884085440b40183d40100b040700d41400044840640b5100160800c80c025041142d026410070000292840d08039804010500030504103000300e4002c1c091000c0281d0700c0b50 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 739092526 1250 739091276 739091291
    0xa050301020f0405090703050610230a0323070f2a050604060c081e070e0603190509030405031c03020705060a09030f020a0b010b0c0f010f060501120c020d080a0f 71
    0x6100e0020012134100360362802007580c2e0000c042d0f0807518102c0d1280c0d0442c46a01410030340d1441032542e04012144009070301d180b0703160f5030300030141c40d04010032a2003c01c0c0d40e8164100540c988605442c031a0300810b0340e00ca050b1400000040c04900407982d8003007404441c0c103403206541c0100c080001e49207059145035028400a0802c10b0b690ba10542c0c00352200c601e40048000c0161203050124800e18a400700c1010040041101300f401410090048081020002034a1712503038401340218010f404880d5801c0007840c801d007561049820240c2201c0c11540304200400513502c01044d01142c050200f1140a441d840d078800a070081e00c2503d10040013801003c4c2006080d5801d0b500c10302201d40640e40f40540c0d10382304502030303988a404210243c44410b0203401004044c403c034000b0000c1641003010b550504011000d0582980e550314400819592120400e1089581c000028000005810420f21202486504c06074030760004000b10002c111110001801040703c6402040104a200c00c0401115 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 739093776 1250 739092526 739092547
    0x521030309010615030b01051204050c0301111306090302150c1f1509020c0a0206030613180201020d050406081611030a08040c12050c0621010602060a11160f020a05030102 75
    0x700750303a004481039211801d0200071054406d2156055100043c1c6499141003050480e00c030f54004020700846481c4a6101c504419032803e0203003080c554680484141c0310f440b8110304003108030040c0c001c001005500a01000076940d12503004842c00900c9020a60380c20030b0601050a100c80854090040b8414856011011004d9440f29010304100460307290704648580c2000d090341710721920107403c0e51000c0585409894080e0045404c0700c0000c1403a85a40c6e0314004042c16070f07502c0c80118403140f00c071108920a550301417200510840305c03450854a040d04050b8090240240901059a108503d5400490007401041111241c06400d400c483e1510090700b0300415000d000c0780d049403116040100001c01011b0350b00d0241c840c2d9030200242c400e40700004180f005c1900010407484801980303024488038070543e821030901074922540079010911f09100c040c8140c0f10201210101007200700810307140d2825200d0740240090307100044800d42d00d10360000400f03110003034014542c10351000982d4541d9 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 739095026 1250 739093776 739093781
    0x40b03090106051c02100522080f06131e0c0e0711012003060a03060207030c0512030f04030509031c09060e0616150f02180112060807052103030901 65
    0x24003480c0d4000d1108545803020302c4042e000b503a0390200b102500ba54280c0052038000200c0d0b0300c401e400d15006007040c0582c640740c04680a41380295a24102400c0d0a100a080911020f0040c810b104024101814103846043d607144400301d0140c107040c860125004818090108210010b800200b1640c24580711414280d40d9039040c1e038000c011441c40e10300684100018050040480d2034880c0c80340c140c0c05184030a07143d9a000910722540502004404000200a440030b4044680203030340e4018006014501a417a01c6003408101030808028400c100c1d042802c104166801a4145403441d00c8100c10b401081c9840c3d9034481c486028a622154100d6959010a405003194156560141082200414441e031803090b00041440714000c0c00122010541201d0085044480316000140340c07160100088100c1e006501c0401420042c0e4000b011700d0b43c1d208600b040240d40e00d040412255103049a25542c1e4042c5c0d101781c40c00391103c0310130207902070304914148680802d56001d60355a8a40628820300 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 739096276 1250 739095026 739095031
    0x606071109180c01020a080f0a020102070611120a020313110607020907110c0607081b0703210905030610060305060a03060e0706030e0f071e12060f1118060a14040b03 73
    0x1d62143c0b1482c141150b100040340501c01e500000510303e04581e42540d015950b01c0394043c9004c0d59000c014030800201c043c8245407200040d0315940d500e0305040d14981a18010107003801d01c4290040c4140855a81103e440f180f0340b50388600c0681c1208a82404030321a800392031000381d40080303083d0800003041d8000c402452098021016106524500c0082041d14002c068025000c0314040c01400700c90018131200071800d41d80c42c0c04550a41d680d03a034915100c0340060100111a08005540280841e0002c0c90709003d0303c4110040c0c805481e2542104611a00c40c1c0304000405817038070045103c940712a0f11032009150044024001801d140456903a100310b41e11400c000a8a003030030301441d8074008608000950107182c00303000301d80c1c60442041e810f41002032140c5070726000903800184d241c803000760043c50303240314600120311065140300907011960001d0701c902040c00f08015056403408540c00c9142d440c1400c688080e150801c2c010112451201c0301c2c210410201c002801040580780ca002a51 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 739097526 1250 739096276 739096321
    0xf1209060309030503040b09070e010609080705010c030806090c0d0c020106330c060f0c020c040c23160203070e040605100e0112150507050c071a030606071109 70
    0x2405969251412011075002c00c1c1d000d000140280007050019401c0783d50b00e80c00040c0201181c0c0415219081030340b24035000e0303200c800400c0d61031404200c40003040c0300c1c1c4002440c003401e1048404007161005808000c0040071188a184035000207188495050140c44160b07190500c104203807509910013a000b81040e001e115410790541c42030321000c076a1038003550360f0000c468240043c0284105800d40f0100a082d0040780e00390303118114001c1d0511180301c0c49400c40d0513503009102c50200d0310b0910040321030000c829001c001c429481124905190507a00d0039155001c3c003419610307a0301d8003813580c1203c1180d00095150191000010b00c525041da241ca0140340951070401c00f6868020a0911245252080003003210583d0010820b41ca000107c1e0407246008ac4900f841900c01109a00100c0d8021101c41000c43d40128044e90071100412800028140e090403521540400e55210f042500004010622a0714002800001c00181d403014566552014010441a04105041e6400200c9403203061 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 739098776 1250 739097526 739097537
    0xa051b1c0f08060d050a03080901020f0a0c1509081801050c0709020403030809150604110c011d011103061c03050c1b090702011803110c0d0812092103130f12 69
    0x303c6074607140c408540c0c2c00d64000c0040aa80486070307029640340718000c0008409560078040d03101d5402004005080002107641d500b00704008600d480146003180c1c042210400d440c2c5030207072000134605022103000b1070305400078015910001c00100e580c2e20800503503011038001d00100140d500441e80140c400e50f4400d072a000e10f40d544004105507281e18101c054882c1c030400001040f060b0401d90712030703490030198018080c580700c880101d503400e6800800e400b040c00030281043d00c121800c00e01c511250340c0045030040349142429000200c0c09454450101284100c401845080500a008031100d4410450a4070300210030049562201c2e148185000e028050140006c2c42d100e03c180729142c080e2101003281721103440161422642401100c40c011614440e500e14551640c0e982130f0035010891196007507690740e81340047c8003500202c0142100340a5404007007040081c81c6c020074456a001054142c0680702e80c0c0306045071107c0b40000328003814001c03079603000c41c0c14400e142e81200c0c1001069204c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 739100026 1250 739098776 739098781
    0x180f130f02090f3307021905040507052a0304080f03030a060e090a14210310051f081905040807121d0415031403040e010b0a051b1c0f08 60
    0x144000d801d06190b0b01a000d139103050603420b0003902c400901c903103031030703803142190400e11540d0106107845103000048624981c640c9040105d0f04c6c09020352907001c0303c1440c0c003c0c1421105403a90645055540790846068031241d01c45046207000c1003510010703c803001c11240320024600000f62030f40d0040e10405902400e040022402a400043c542c0c0610782000042c03c4407000e903104c142002c0c6140340c418882c1c1c010700301c540320980c0da1040c4003000211100341941c0d81c0d00380107011001e11030107030303014500034030744611001c2850003c165503111001141c2081401307035450781c00f01564400c1901c440c00c0c10600d4070b018001840324a03005000d0680c0304080c1f9102c40b00c6511400e50720440c2042c94203481d000c8240042906003825041007503200b0460080c6d41745152650b44045040443c40c56806856001040030042d1250b1060003900602080745800d141540044005102d84514041342c0040701100c11348020700e48082102e0006561414902c03023070360803150002030240d88542c0d48000018024000f = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 739101276 1250 739100026 739100029
    0x6060f0e03030406170a0906050109140612062212051207030e120c010b090c031b0403050a0305030411100809010c0801080d080415050a050703050a02180f130f02090f 73
    0x1281d042c0e54698480102c04170107000102c0000c0710003051202c1140d100c0a110000407064060240a09055600400c400c14103900c2c8003118200100450321134007840c602c00c0f580103400305070b0541181c50020003504a50410102c2082031004004c0100001035400c0480500c3e0380c0075019048103070501d00405000d80b500a4200c0648070006003009040d080b6400440c40880c20f0701c02081d0443c144030000c915106103a0001318482c03411188044041c0300041009034561080312241002411058520705040c190745455039070ba82c02c1c247c0201440800008038003400b0095010400d072110040484131513404540300109080c40c1950024029802c0801407a1210301440c01c80f8180c1d038a400081041210b0400121501d210140007902d019680080c02801d40c00ba03070258901c22040f106010545040811000742100da0040c40518100e10600116a024003901d00c2d05040714812540035482c07400302c5002030001c1140803000f124541c42c1c480588a11482c1e5000b4040e40b081c00c41d0304404500a000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 739102526 1250 739101276 739101283
    0xf090f040b090708090f071205070e040f06090c05040c0c0506091f0507230903150402090f0403052b0608030403210c0f0311070614040308180406060f0e03 68
    0x48000c0c0d108144a00003503140d0311404e0180d920169203001c484200180d034101500700f004030380002c1100d034010000301c014400108031160040c03101800e8141c80b480c19458a8050480142005102c5500e900e414010f0004900c0c9000290034000d000700310488110301d001e090280034000c119014010f480010318150004a41c078800420000241d0301000000c80c4000024600102810f00303100d401508010303140c4013101314001c03022180d08115500d1a0341410945009040150046809d40c54010040140c44c1c0c0d80e155504601301e00c0000c00591a24074041d40d1900815501054140880d440c0c5000d01200c00364030b00700c911184a0400001342c5800419890f446280005810f40c100d400c250140226044071b2007040000c54a44562560302c9696404032520000c0b80c1540060048605a040c048041c000c22004282c54140003800c80054902c0c0c1480340198440580b080e4004141d018800051300000304c00c001d4000c1040181075207a0001402c81080211102c0c0021015100800300d414000f = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 739103776 1250 739102526 739102541
    0x30c0901150e091306050c04031b06090f0609060309051519060f050609060c07080a0c0306050f10090221010b120112030203090906030f010c0305090c03011404020103200f090f04 78
    0x80960301c00036031070f9140c45c0040e00f0082c0034100c54200801001000c2043c401100c080441c003800d034000719608e40175008111815580000c0c0d24095031000802600e40c009045c0421503403542800b03c0c8499541c10040e090110141890301c0022522040046203140c40d02e00048800c10800201300f40f80d190804c0c6411030b52140240c5412030010414881c036442c02c000503041203680003080780c401c1070b101c030002410141c2c0f2020031600000c0c1e940c000e02c02c200f40e6004450f807010035245682c0c02032607d40c1c114552a109803007500c1143e60b001502085d40d6007015030386641681d860440720140c1d40c2d00d07000400c444d4040042064270329019400403800c90030328840f02d0603881c1c241c0c0c02141801d540204000d9241c0000e0030305989840f030f0480c07600d00100c00380600030f01000d00e6100002c20340750186020703040540303039414288664540700c0c1c00c007071894616050a810540a280c0040c140003044050340440c0d0034441140f00920740800c002d550311801c4001450b0040c800d48241503134080300400d2209a0300403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 739105026 1250 739103776 739103791
    0xf0806040b06041805070806061c020906060f040e0907060221030402060306060415080106020c030d0c08030c0f040b1e030f062407050105090d0c08040e06030c0901150e09 75
    0x912021500c43d2900d81c2224507800d5207110320381e40318152550303014a041203079400080f00b500b12804014040c0741c000c00b02c7d074003041507400c03491591940b50300262010000910085c825040810002c0c8000221003d03900a04411343c20700d480c50070503a01e00c0317655480c01d100300c10040c451000d031b0005160200d800340040602e100070141c29500d0716401c10070305400040c081500100c0a00c00025079003c6140103254054254a4651b0294100000241422550031110740241d02c422686050690301c40000000150021003c0e500ca0721403007038580c0113108030000c61103254008540403440e109184000d0001e20006104045009054036029000e0702044802003062412480051000e05110f0680341d00c02c414040354105c49030700305a82c03850541004500791740c207039912800c0111030701c001c1100b083c049442d41025421095280d54440d46c0e4422405020405c141c2c00740400c01c240c40030001d018610000a15154040d81c40c0c103942458019902c600c030300040c0500251074154100321400c01e019205 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 739106276 1250 739105026 739105043
    0x2511010f0b06030a02070510060b09040509010b03030d02130312020f012a08130b100905090f030901260114101d1507061406090a050708180a15060f080604 68
    0x40f00e510130700082d041280140c840d03004840c00d5584560b4180308450180280c8444183c481105605020854400130486009a8986103610300141c0d000400d0b600202c681c91000b60b542c441a0018081203205507000800101000003c18440c90b00032410b151203e034510020810752090705100c100011801c03520300031840313045000442c40341c40f64082c19401681840b21420070b01c1d5580c0d07034200d115800c486a801e000e000c06014400010240a500c0c2c100d100000100100e46158881c01c3d100e1042562180c140440c00b15900c81020300781629000e0000024008105580d40b00310b54550740000d40d80c0e080c0704010403001d182106000e500e0b52041070498000003c0c1c51210300003841001d00f8804c8100d40038802c10f002540004c1c00170b000f40c41202c2081c0071050f020b414804180b121051000c0c0480c44110f003840104550716900100b1207078404d50792482d80c0214020245150304001c0010b41c0502000d210818100359a400c0f41c10110403105c1607605d0f141038a0ba200030b1152100390640300100b6652 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 739107526 1250 739106276 739106281
    0xf09030201050351011805191d150603040b1602030c0718050708010e0a0b040906020712080604092303040f0e07080c0403020d0b2511010f0b0603 64
    0x1009030000414280c2d650004c080204105445040c13000000d0100c0c801100104c0d41c4002c3d540ca07401e50b5524503c1003824620210200070000a1440352140245030059513801040368000c04241100001407000d03c51032580660182050b0000e00d00031900003d0b503420f043c050186030b0611000b10707840b40d0380090080c030160b222880304803059180c420250085200c213102c05d20b0b0040051110b2001045c00c008040c00c0c41d10000c00d02001e0b114024201c4003800641d00040000301c1c030407012707281e104440c0c4100080307001200300000c006020540001e070a0030b02c0403d8210401007030341002078440855403a005000e64070201040b0035a404000001c01c00e103280340b0b2280c4111005c015904400c41600c003136a0030306840e50013140051b100c942c015a00107411130f00344071102da0401d40c1160001e00c144e405500d468216001709410016502c0024108e0010030001028001c00078968001e141071008070071500c03825260020903c80d20140e4041081d480d194a10760b80d002030384208c1c1070f8454041c140c9406c55 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 739108776 1250 739107526 739107541
    0x515060403030807080a0b06160c0b031006030b01021501080c041b0e092e06030b1005091909050703020403110a06021c02030408031209100e0303010918080c030a0f090302010503 78
    0xc20f00030304081111a183e41f00aa940c1e0f40f110043c1408500082c40c520445080382004041daa440f503000d030070b86080c20400d2001255600250005407003507802d0100f821038071440102c0c07a181c1250140b004a4200d20004200c0e2640031450b50f00740c240c112801e00c1101c5600e000e2010814402c4d91280c0405c5614401084a0500c6001d45a0106013001c0590541d002c418002c094004e81f03031540345c00554407100601c00c0e150140f040b5001c8100c150303540c440c820140f241c06030040c0318082e031040c4150701c0d400c2d07600d02c4400703880d01120160880000c01d21046c200f00c1c00c003402039007103400120b5004c08400101c0030a414280d1031303581140d040303500034242481010754094000040364004011400300300004030703203044200000c1010041c00d500c5c0001614000d8000750801400e400800b00090a002c001c0e01c4080c40081a28107680310304000042040010081916815446174001c000c541c002c40d01d5041c032503000c00500340c601d0300c54441a0110501c0342d001c4802c1c400301c0c08000e01044d002e00204614 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 739110026 1250 739108776 739108787
    0xc0f050d0b060c011506110a0b07120209030703080c2b030e150115080702210d02090d08070308010b0a02121b0f0c0102011a032113090515060403030807 67
    0x1e041c00340c03a492034200310040041c00d5a040e20074000d082c40740144108900380c1c1c4000c40b2845101510040c0102c030180c1d0b0345104240101402240400020b01206480301041d0360490380300361001030845914607030300d141520194005540304150307030003040344c000303034810207103541e161a8108144082001454090180c004042e0980c010703c452103403c14260040b25940c002da0302800008440c5101c83c240341da0010301d2000000c10351011900900300b107502c060f19040c150000e42d502c00c243c203510381400801d890000c2c0511640c035540201d6002c802010f1000e4038000b04213407070280e61845016030320784240c0c10f014460040010016030011011010320104070001e440c68804204404032810400700c2410701e4555034441560142c2c010540d0303a0055a0248104d814065102c114800c0c00c0d9500000070362640c07180cc3c3c40022589d00301038940c0f94060104116004144890104c60f2541d84072202074004110444003150342041c0c01003240e841d4a850016541101c2c0d0542d902516591560380442c0c1 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 739111276 1250 739110026 739110041
    0x1030b18040609021206010f06031b0e120d0e03010c090f030f0201050403140f250b030405070801110301030c052220040902090f0906030c0d030908010f0c02010c0f050d 74
    0x40d510f03501d00844005a6650140c00c4902c08240c00425035941024030002180c0c801d41c3c07103042410f142031004090440380918981c9000030307600b419201c0d2407008010030210b2028504007003150188070513607d40b0070b0b003061211404680580080001500c80780c0d0aa402c20454042c3d101a02070201c010400078900107400001c0d03038410703d01682001d9a03035854030307104001d860306100305400400c46e0100030007041000c000343c0016040f280c0d8115240710240c9651940e20701406200000000006091103410082400100305a5000300140c8801c1041c10115030020b0004481601385980d001440c0d1824140100d69907103514402c0c641d841201d40c024005002100200c081c10032089803018003104600090001800080400f6948000c07007420040001c4580564911682e9414240710035503c1c0002c060700d800c1d009440d22155503106040030f0710051000d078032060702907082003844d08540209410182003180241c009011a60343c440d010b417120300f207120300440002da090044805a00c443e401001 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 739112526 1250 739111276 739111283
    0xf0813020d260a03051f05130b0114040303021608060c0a0f0c02150405040f1130010303020a0201120b010f050d09080d1b08010602030f07060e1005011401030b1804 72
    0x1c0c150302c100720042449400c4410500e01090b0354500f000090003c01202c041c014030094004c0786c6039410000003550700d04030f240340d40540350740d038880054569004072598045010444d6280362106e40d0bd2800940c0c48910394a424116144494001001140000e41500801148035424100040c5280454806203522014010007101c0000c0e000561188143d02d540ca030008a0b0780d541e150f090805000540b8100546560200c0c6805510f0b81031001e41c0080d58004007000e156803c0c182c500c10007883c100540303400700314504100100008105074000542002091007a2124a1102b030702a5032502100c1203050505d0120302c1a00907900c4442c4540018200b0464040001517015015160948290414201003603103a54805044a402035846c002402e8032000b40b41030740083d818040025120f01030211104007210010078000c042041d55080795447e000120210368a241c21250a003001c1c040030700c03405000d102c410400c10480d510a0003505c01c07020340a880c62424090041900624000042c0180c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 739113776 1250 739112526 739112573
    0x409030c0206030a050702010b12102c0a060b0a140118090c02070f090506060f0705031207200111161b03080a0e0d21110d0f0813020d 59
    0x3001030b601d46000e1806201c103030340300203014a0712410103800c441c00c0011243c4284050fa403030118000c80001c82d9024078001c13580100b99a0810440091407140b001c0c003d00f10314004d01c0c918201d4010020703000381024014402400380000e00fa0078807134104124000c010b8440680300310303100c0c03d5004180b50134401c0780f0044281889030340d0b010080100d8942d0b6a4280040e000900708200c000c8400b00d1600c0900a00e50003004242041c0d40050514410440c000e00b4201e004600001030020910641ea002e042c80e006e40c070341c1c910b08000c7c0245280e07030001a2040a01a60600303a5118005101d0380c070261400d01d031a030345407210240c0343c074038801d604107421245da00801b440d20b85900d201d144000c00443c07050b404aa1600101000644004c0e404610640122621540c21020030312140307040c00220303c0c07074404c4c40c203508003040100e035170183c01ea010744200d00c1145c18140d65103a100d422800d144103d552603205e01d4558019100e190603160102a40c0082d041046d8800320313210004000d2904408001d4 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 739115026 1250 739113776 739113797
    0x201021513051c051b100c0905210c060c0c1f09080f030d020a0c0b01060504081b030c040221010b030103351318020915070308010302040903 62
    0x19055140800c40c1c401900ca40c864146004101040140764400c14070b19482d0301091542442c024214081c00801d550b09816816503d03016200c140041401c0c5585464203200601c942000078000079807912400e80203910054903131a044030b41e10404000301100001405d82c0c1e4810340b0030087d407a08100c2c500340307007030140c00300c144025520b240a1070114400f2100c940c14100742c142000e464001950b12207a86a0012162000008d40200880b40800204c810068942c86600030403150324100d180004e100c08020b100104040390060050412540305100b242d02201c901081920381d18a001c2105825601a0700502c1c8107140c55000791001c0b4941c0d20700f520142d0045590180d1110003a03208611314007001006100f40039102920800781c0c6411002c11290a042d401c69401c48404220400800c0401140d4003c44850030341c0007400400350350040c9585d1151401c07840000b540088035440c030840e080c00707040c420401401c1c2a070302842e0701503c0d5903407141c0ca5034080c0409400017500803000c00004428 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 739116276 1250 739115026 739115053
    0x1a040c0306120b22120c0602070501021b070803160204020f130e07080a06030b04030c05070f030302031b12030a0f090210050d200f09150c03030739020102 68
    0x120800c0c0c00366110340303440e0504907040d501208800b050000084c2c4014042c0d00031600107880c000507511603180c00c000015550030850b009004070700000b80203500003d600001140706542c0804404594010b070f9042659484049036a48101d8504135140104d80e40c00c03801601d01503000c0c0a0070800140c18502e0000903189031281c014058005819110080003800301880e8042e4900c4e510860103030041050300d0441e102d002000078014001410480403505a400700700d02802043c0081c207039180150946030b107919019442e40c00c14804100f050380103003e0320b0156a0000b411541e140d628004151075625201e6080003e041c04481200e945922009120010f8481750303a44903038602940e443c1500c03562a40c2104080e510900c0907801625404c15282144180c00e030708464101c100000c40541d54008a0080f402c0c008080c6030181d400ea002061400007004080011481680c1035030b2014900c4400741825840c8000641a03141c4004111080c0d5850b840445072603103503e801401100c80c030660098 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 739117526 1250 739116276 739116299
    0x20403020d080703110d0504140d0c062606060304201c0501051023030a0f0f0309060f0909021602130c0e030c030a030e0a030506011d06041a040c0306 66
    0x704540d00c220008640381410391151036803101000100103407806103058103000b030640c0038134010380410f400d9404106d04c00343d82d00c010707000c5500d0b070000c600c0501968591000d401903034946484a100f049d50210501c2c80810300352042d2148100504042c1144c5643c0c58140d0b030603800c4147c4240c5010003100c800c116685a40c5221107420428407180c0c1007040c07521349642075a1002d0040c00c02d48516070000c0c081c41103003041c20300c2103002c04140283c00400160001e45071006441c0040c0040040c203031a541840400342500001901070b844440d03515940d82001c84109141d10b10b100e0020321070401c20b11407480a07800901e9040443c0e0484100802c4680000340181d60b038500081049586aa00c4040a034101000d02000d00d0101c0160041d60414000300345c07515920301c2c008080001c1803030f51052958451001c400034607040000c8469660b142e1000c00ca070884c00d4000300d400c0d0078002000440bd841d090054841e46400c01032580845c40321041484040c2050301072101c14144c0759000403c00b511000c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 739118776 1250 739117526 739117549
    0x1170c09012d0e01030b090105150412060b030106061815050c0303150a091104170111070302060417090303180a090e010b18040b220b040b04021f021f02040302 70
    0x3206440488a074241010300030800b410f032a1810306003003a86000c0c2c2c5554410701c080c112041501c00b0741c038024105800101c54852904802c83c00342007101d4031001e0081303d5108425001e01a0000c01016880ba08141e9048080c100c002444404004060080c1e00f0826080c4510b8401b60401500300301c031191030386046030070031241c0407554080c80c00c4100c828030305507407020300030428010104658000c1c0d840441c124415030050f2030080103110049100c3c540c09601c041c00503d6007684458581e8028a4025100c5a0075607064810b0910400b0803004c42d1092070440341800001401145032a07050034482c258602041012580241c940d03a0020ba035030b209001700407505401b8000003ca11031124108034440007003403601250760310b0102c100b00001e46143c2c1c0f007540000c6400c0510318031900f60340b200410012924030081403030341058184420003000b0342c0040c6c0264800c40d03045015200c2c0c020f03580b8220440d80032690041c2d00062450a41007000e14280d0809214143d000d0b160a03265004940c069655 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 739120026 1250 739118776 739118837
    0x3140408130b03010f14030f0312041721070c0507080a06060b0307200c04022808160c050705271506030103060b040f050702030c0c01170c0901 63
    0x1824405481840794004090034404005034215410440c2208000d00c3c0c0d0f004540080a00701e59880040c6e608000001140e03000004076a590081d480b0115480041540e045502448210000d06c0079415041075070103c030000162005065406070888010080141a143c00c0c811241d40c000003203a41480a031010304800801000001d03510300e05074040715610740c0403616104052041c00103103035000303418641d01d20761001c9466407101088002c1d4248030096030400d52040c0b00042c2c0000a250300311108040108030140b002c80510503007404e1b581d80360111502c500a04005140040445c01020300741c4030706009508442d101d03a03c440104501000402c40380344c183c10481c2030180f4010b42c800c21194044818031074404102e9807540401e401e4001030100509442e00c441c1480d03070b01e44465114400c1d07a08000d400b07000320b042c4100083e44940c4001004103041c041e002d03191000b54080c80d00407214180c09103001c0c00d59502c040c03500c82ca54000a08440c1002280d04003615103201044162109105 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 739121276 1250 739120026 739120043
    0x614070e0a14030a020402030c040806190c18090e030c031c050105030d02060f0c190c05120408030d0902010309201008010602030d0c0e0d11040f110703050901031404 73
    0x50340208500070305107500161040307034100640c1081e61004207003d100c541c0d0660380540c40740c451400c2c10710640a81d402c540054414841003080700c3c805035402c44180b02c0395220801150510340011070348610300c0003c041040f030051808200c480090341c0b20110110007141900d0400d401080c0c22400c40d40001211418058840340561140805206282c01490100c00416803070101113006501c48600914080c9503021000001d0049441c00003113842202042195080400c1102d41c0905400d52900c1d00343d0300782c0301305400c014503c0682012030b0181e9803a44001d6003041801c1c0b041a02a00711500120f040613100c5100d6000a6844803450b002c0500c04c003410b0060319064014812070890100d0741800b0010240d00401c900d075000710448544080800002c20351042c0c155064482805980240d07030170104440324401441350811481f0007442c4215000d0260741c85032035821013600c402c0c0c104000303001410481c02d00040d0184000f4913040c8818100881c0b04100042541021042202c06441c25031 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 739122526 1250 739121276 739121297
    0x4090908070b070c020108070f02150c0a23090d0c09020301030b090d080609070806150f090415030506130309091404031b0308061908010f0c1d090c0304061407 70
    0x2c0030003829a0004580c6441c050b000c1d1560002041110050420700c188500320140d510312a20a01086034207251404a4030b0f0345042c981e2440c510340c0c1c0402d20b076000250440c001803114070001104441c9554040941a0070509100108400d40112400889811a860500060000303a03400903500843c05031006003420310f80041903e00341952890050100300c4140304002d0999259800c042e040510341c0740208260340c960000c105040b0544107144000d0384041740d1400318030b0f1600000c1490071000d90b401c2c040e29014aa40600e072549030b020082958006c1800141c178203001e8401210218000e14241c00342541c0d82c24203000720384401010810f030350340c1d0788108014980c1103c22403011000d1045003034052516600c0003415104082d100e1032080c46a030b2030218070480320035039000144c40d00d84000c101c903c0000040000801d0f000110401280c503a030598100c1400d40e004411403010040c1c10b9000d1503541019030960f039400100115000c17603a4805a02e11003482e00905441581d0b0b40d150b000064 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 739123776 1250 739122526 739122533
    0x40e010306060e0a020a080f04062003160504151112040902030106030605121e1f05100b070c06030b0d0f030f0305101410051b03120f0115140409090807 67
    0x183c800a020400990042002104856004080c9580107840e60600361040d20341e80f52900c05800101d2404a002c0b001c56903000013030580f44011400303080c05400c441700c0e410021000b962580075901c00d14425040249407409218014090740d84005101c5040e100144651244800a0b8000d0703007104008550110060101070740601c42c1d90054117044a1606406040c1c0030780765a030f0071400c80c01394125124264103545003542042a202407411244034028280c00105030f45000700710841740070420441d0310030002909004034084130b030600d1300b0000a044990903d402500034299002919410800441c1d521020410705d80010002c81e10035620070140c0780e40c2c454024183d442c00391441a8031054042c08108160a4000c01d0a41d01000d441440c8040124032061b5118065001641564005000070341c1c0640e5020004202c100511980502151100540c2c06a074200174042c0600340c4038241d410303030485030080100c2001ca445200105150985070800c510540f0611407048594100128910081 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 739125026 1250 739123776 739123799
    0x703090501030b101d0d0803150906090f07020307080d020919050319022704060c0305061810170706021009051f060305070b07140c1311040e01030606 66
    0x20203091a0911101e5107200000b28102c042c2c1c0c01d0f030400d01280014015a12581680d04c60300d0003401456002d03483e041d820a09030310b91049800d0100c4564070911500e651801d144032a000319406400c08445a840c08468941440d01800110940c80180000400602030600420500c4601c0c080540c448a000e400d0140000310120000940350348001c040c04144c40020b030402d104001c86003a422902c025002180e94154000308003880c1c1c002c4482e40d042001e02160002e4040c0c0d00c5002c0c200a01c40356408200e0864100f80c59469100307201e0145545202c04108255810540900c400003100b40c0d6444808510110ba54400140e03030403129040210325018454004001078480090105503490358820f51a800e4254000e548001c01200c9504000a282d0101e005954040d0885041c1c2e52a103140e0080d80d0441030045074150a01c1000c0209800c01040a11203100301030452641c940100c8410400f600319170501c4988800d05000000d80c0e10b42807881c0c54000d5001e10000a80300c0c0c1010303010801c = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 739126276 1250 739125026 739125029
    0x903082b091e170f04090c0207080706031a06030a0e060403031506081009020c0a0510140a0c020c1002190b1602070f0510030e0105180708010b010806040902040b06030c070309 77
    0x700040b0a5850300810140c004a445900c100b2080c1c1c1d40c0c0c0d0400340784c8107005000300e401c50100f00d0301d020403005000b0f4000a0200a96140c0e800703d6810b02c0d650f03081102510281d0396489200d00d1b0400c07039103115052680c091a007021030303a0701c0813441c101015040d600e04542141c0580019448500e0300c03485460020f40d2002400503803920741e1851521610090401015110b1010910b50000b09110824002d00c0b41e5a8a180e208090354a05002c6c0c0c950303840038050394001000244aa1310204006d5074841c4a014108960341c2c0141415841c10800c100000000007601d0095004101e0300c0d014000c01000d09400d10b5100f10342c0c0c90340504003186169451400c0244100a5600c2240140034260310400e13580100c800468021403240740d036620403006030100040c0c418003582080e0138440141c0e1178071090b07a05507940f58211101c45564401003400c1c4c2c1c00b0a491350340441d540d44042500c50400d5085410340a00207400810b20006203404210903510481301840b01e410085240020150300450020 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 739127526 1250 739126276 739126313
    0x120305010b0f12090c0307080106050a140d03081b13030512070507172404060b01050a0e0d020d0503220e06010f030f0e160e060d030903082b09 63
    0x40c18a040e45610311028464003400103000c0f682c060004641c0380080020186030380000d01641c800b2980c405031140a01132034010f00344100302c500d40100b281640e01c10072030080c400007003808401ca981c5480c00c0d500d03800c0152244e04d00071002180134241000d000014100700310400e0101805501e10304049003040c041a00b0349004000400c803803000b0810000e0b4030801d0321901c0c89050074040b0f41c60151450b02c0e2015440441d20500ca181e00401d42c280c02c458144a10700940c02807140c3d144036401112984034910402011402d0308400c6d981d02e08007542e2031152a44041e2400030700009940781c4c170346540c0001011201c4100302e10359043e41c0035003040341e800060525040d155034500b40030001800200e541e60078442010b583e200400f48064aa40108580805140585100b201204e00d03084042d000d41c00303030101c011001c8d004a9014181184a5402250151b45001c03085003190b4036100e095002c9202004c20300078040350031112401140d1403000145140c0c0000400702450f20301800760410415000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 739128776 1250 739127526 739127549
    0x50d11030c03010302060a1e0309030e01031b180f0e180d121a0d0c051002070b090607080d020d141501020c090709080a0b0403020f0304120b07050405040912030501 72
    0x80c21100d00829070341134950445103c0d840b810b41c1e0004945030351442c08103508500d030110080c2c000503090ba20a02c0250300940c0e803030303a031030400380015800d480c0d1040703c1c0c0b810328000020004000d849003154081c00080c802e2090103580c0e444440031440310483d0010b0354201400820710450085810040f0101000d000c00350a020483c2000074009a82c01e16507030820b01d0703c8601103c01c02c0c1c03100c0c00720907051000070802c95050000f400c122a180c121401414080c070300d0407944200550000031036004485007041040e1915031a10103000c0140c000010440d84004c0c00e0101e450305860f1400605440c00c4070000c00104121000c4100802140c00340c2009540d542c0202e2501059a01007440c5010000030358502070951a0007100f00e402a485074807c03400346c0200c100c1502045011618140118020342c2204d000040305540c1c182c40b44a0703442100070b1002a0300b02c0a000a810202c034a40c0300085c0e00748182001d230703120046015184920307000c49440100344040e80203d5094418103001d046c00c180c00 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 739130026 1250 739128776 739128781
    0x622030804080721030c080a0b09041106040b0c061b0a20100f02180405070503070c0507050607031701060801050d02060c01110703120c0509100e030f0d050d1103 71
    0x6008038901800260100d1030020b10314043c000f4441c40340032401e40c0c0802d1007500b42d21000f001801894034440b0b61001030b8000002c81c4c0c105600d4000c080f640a0028400c2c1d8031911113941d203196404448140c1a08180240000a407100001020b0b00c2400d40c40005400207141140b40c0346a603601d0280042c01c5840c0c24084d00b6004d960044508a42c89004008000c804d070018840340e1800600840014200d42450451315203602541c0291019a200000c1c8071003800b0700c40100301c15148105d4019000550510001d11290300c50720502100c0c1d801101a26001501c41000c54210352000340c0607000314454501242407000000440c07070060055180a16003541014006030512203105000780c41801d020420b03103c1a070302940180401118000515514045413801a0010001070fa060a02130b03e0308400000840c0114112111540c0040c40401d0580e4845000d4440c075400305980381c0c042c494030100d403040d0380040180d00001411511016201c0031032680302016a0101c154031402070105206 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 739131276 1250 739130026 739130033
    0x216090501180519051501031d06131b030b010303081501081501050d090311070b0403110607321b1c1a010f05040b090402011e0e0406080622 62
    0x22081c180039040c0c10b01103000c0d00c0700500f03185180d0b0003d404024480c5450700b80170303244001c004490310890080e00d092200c1d000c10301c031141c0c04640d2040116a5500300500260701d00a91240303205950b4460000300c550a0820b84a40340318a00c01d0300200e4100c0c0d01d840040c0117143c1c020705180d503c80042402600e030130b82581d0009041c00f602411050303c02010100050b0a0307805001035610810040c0410081c2d071000381001070040d030342240310f4071050081c0000801e0104400c4100d80c1561380010343d074100d100b451002e00295030f202800c242c841c051203217140d00ca904003021032a0400704808145024204600340c0f0705041070b00c4801c02401030390f0541040b50840c0c032a00003000c111101410104c40382079041c103080c85110b80c412344400e4003207209400030429400314680c006c151101aa01001f002200e001401060f141c1980c000c1c6c08928030b8080850401c03000301700000c480d103040c6011016452181e010500750394003030f00807200c1c0e50001c60400001d40c6440c4c440c07641c0402d02d804091000585500d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 739132526 1250 739131276 739131299
    0x29180105160f090e0a09060b03060f0f04170a030b0109090c080c070302011103040c0f0e0103020d0b0c04051905090c0405092e08010c17190504140d0216090501 70
    0x71502400d00444400074003045005070009401082103503036460003858142c0002c0c0c010050014200d81803171400d80050790500700041c80038420203201c040700c1e44da40c039094544c0c3c4000c43c00900860713402612005c0c0807240c001c05006400351407181c0d100402d10030328082c009448002c040c2c00c04910315142220603a4241d500405641d00000c105556559500c0300303041c04c9026100d1a14030a00140c4000f0510003000010b0f51100225140c6440218419807195103040803c0b40a110181d0b00c0441135050078003152043c0c50340d9400004601046213030039901d4001ca0005264040550300000030301e00c00700100c1c141112059403007212100b0b42450241030400240f200c80b405480d0781c908170001c9030181c00d1081c1c6c2c182469140101d0089600308030340d503482624081d01583d00202c0022302036013001107408450f140200d000d00111460640c45010704460710001780401481998140c8803c080241d81c20010f100c5460480e1340355002c0d0442e1500481c01c200c03200700726031050500600d00401004441c0325613 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 739133776 1250 739132526 739132561
    0x60b031003060509100e0f0607031b260a0212130308071b08070819090f06030b1504090c090608040507140607140309100e0a05090429180105 62
    0x2d80002400d49490280c1ca00d4811307550045e0f0007091802a06150b08840042c5243c184c03c442012a10039543d051000c606a94000b080c501c4199002404a0300280c0211442c6000380306000403100520b80d44c0518250203401681c03101419a40054500ca2004095640c00d5200d02009c4e130b03050f03000b00680e90003804080d004098000308801d42c540070744100035424004901d070b41c0140410341c8800c0c523420003030000d0b84940c400b4000221402465035185010b40c44070750031251104150034685260030010307406803d009505c1a40030115100d80101c1c0003106010303101503d11010001185143e8100103010007809805c55414420400c0800002800025042d42500c0410528550780407071000411003d0286c00c200800c8202107101c0c0e090710400000c05090410f1301101e0895005039241010780f001242550701c1078004680a10600a0782444003040c0c0d0414800e070304203c040b4061303c4840600907021349001c1c18403400d5005000307040001001e60031458204138020489406d1a001401c10192003 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 739135026 1250 739133776 739133783
    0x61d0d090b04030f140105190c08090a08030a020c01061d0903121f0b0a170711030d0b060f040e061e0f011218051c051309110d020a0210060b031003 65
    0x70104131100f0041d96404024030000414000e10050401c01c9112885294514041000720f140600020400788150246406500d821703002d0541c115641c1c455a119071320080c04158810b400b088107048041e0244030324030050882c08460401d42d0b0f4409036071007820300b001d80502c0141c0e2083c0000000c0605011540703810041e8011410a4020340181d490322248081d40b088441c0480842c103403561582000ca01c5a0494410031a0b4846540e4003006036001180e040920205900c244a10f10b41c1e20f040d64884840c00d040201064181005031294583e02e500070f0b00401780d400c140e40107200c03103820405180c455500c100c490700c0c41c209458102245503403980b04c0d0307003504016070b6120040e5010050780c800d034150101d052000502c0841130070500d90700e44086400c0c0d110030b0030b42c0c4e040c000040d118005903001d50000300c00011341d0070b24142c000805800c01021206091000b0001014242110320090131052155005012904000441001202c00c10341c800342c02070104100300581c0c1d1520180380706c2903a0b030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 739136276 1250 739135026 739135043
    0x121c06081e010f0501180e010c020a0b060f0d052404081215090907171b210114070219050d3b100e010c1e061d0d090b0403 54
    0x710880002d02500c0380c0c0d040a2540e0349440300104512081595006260b415144203001c0c00c1243c0740c0c00350884e0448110180142c019440c11000101c0c419405504041c1c002c128002178010705002845540c0c8071082120a81e1251070b003c10449513011588581104012405150b80b5003034070340103101d1042810b6480c0d03030343c01c0b04001980390030880d00c903112000001d000341070b01d0300d030242c039a40e9101054052103251100c441e03141e504400b40060324408203004071200c2c40e0414201018450980b890242101d55145c0b407050440450100340f292005a15550301040b403d400d040001034201a584280400c144044242d09800b0840005100e01004100c0c43c280d101c4540e0045002425000601032800d08046480e14000c01c0d11400c81d00d02210400b26001c0030103085052042d1014907807a101980402c0d07034200041c010512065041a00882c08491010217680d42d648100450b45142e1244903401240c00040100040801512000004500340312411504205407280c0138000c03407000500c042d0 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 739137526 1250 739136276 739136323
    0x18120914060f120403200105040c03020d0212010f15051206010b0306061b0f010b120c010305130614010f05040c080c0c0102040803040801050708250809010b03121c0608 74
    0xb9107650440f0404036991210f851181403903e401410154039010004080500b103003c4241c1b05418801c0b1400759605c4601c25450701c1c5182d081c02015040c07090180c0e403190313610b00380900c071030028041c0c02c02d01c61043d040091822000d072030344403035100e240c0c020900400900d188410000d80c0060194155a80c90700e03159102d5880b6000105548207000c0f806010306000301035000513034400a070f40581322079840028010b9021030020303ca21800700d44035414040c0c0c4150b90100255003c0c1c0e00944c1c00c03640070102e003402681c0c1d5895020960b02000e0300042c0000640780104500150050300d440600740880741400074010400703005001403800b5201c502981030006412950407000d504840040038002c094985455450034603d0003044119100b0020410480c00180b0760704102e1000740c0c00011141c41078020094102d42100c4010b0020200e0f1015984c0c0d00040d03040b03650800500600040490070741e9642d840d029296510007442c00d5102d45c0d03076070415000b03000d01d02d00840e4005410301040a40070184 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 739138776 1250 739137526 739137547
    0x50306130b12100b010509031b01030f0504200405090304090b0f09010f0602010e0133050316080c0405040c0501051e0307030507030c080403051c0f1812091406 70
    0x62031210201035008003040d845050321100442c15400f4066080700c2007003048a000c0055800d442241c0310180e068001014000107140410403160303c0810616000a07100c140440040c100e51046c0c8040d0b860701b130f40141e0700000c601050480e03283c5801c00d9805100500b004800c480d030301d02450040c207403901d4036044e0260701e5807500d010154100070000c040510559441e0100c10032103086000340070055091840349015210140135040507000d04a600c2e502d044070b420880c13850390703031182c0000240e0702445400291079607040042600c2c64503034074101034400b840e02c849203151040740100b4038003031810902000040dc518860500480314203082090343c4841040814454011030400545200004428481b0700e681c0350b03006912030442c1d500c042080b071907040c6040d68a4907040310002c0004004200615040c07101c981900c82d074180108001c958040c801002a041e42c60452a1400e0050184024800d00030f110f01048009649800e00c240c07020708101d0750068618220000c0b5000341b10010701c00b1040d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 739140026 1250 739138776 739138781
    0x103081207020a0b0105130b060d06080601140618040f09030f021504020f010c140102030a090c1e050f0a050904060911090906061c020315041502090108060d050f060c1306030c05030613 81
    0x23100f00510407030b23036800e075404100014180d50154045500c40c40700081203845c02001c6146000100030302442c103088001016503c851030318032000e0341254940320102040301c024020151601d00c2034445100700e20300e160000b49065072810000d04229103807818000580c0356140c1050b9102d00a2910710510385444c04c001d03045400c5420420b4142d0b10010401c50701e88007944c0941442441407405001d000c4d503825620741d05038200b400c1c10507490f490140400c110f161031103281c13144450160000414a903143d00044003080100c0307068518680358000c902c00c1000750402c950b50640119022482414103c500035038039000100503d000b01c1c401100c0000041080002c04e41482d030080444508174230b1015402c241003070513a070440d180b03040a000b05d40c40005600a550b0b120606940b010060b40d1203c00304084802801c009031524028040c803c144c00006001c3c540c420307003c0d1661a40c0d2902d50398191400e00180798132001c201441c0661100c2c00360b9001c0100c036006403044071080080c04078041c13038000 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 739141276 1250 739140026 739140041
    0x605150702012003030906070c03080a05090c0310060e16050301150513032102190b0408130b220b16110406061808070b07141002030103081207020a0b010513 69
    0x543e410f10004544034100000031803181e04d0500c1074980c0c0392036400050701c5804581b50000d01060880c0001205498103900003a840004101103c541d580000003180c10f20146030070400350f140e03c82200b4014120748010642e0051500361145580b0824241c0042942c0010300454030500c4000b0494030074907100e00140c4660144440142c0041541c034a803944100243c0810f09501440b01040860312034004504912014902031095200c030007242d0342d1010303481e0020011144040144515200d060324003c009015190860825503100511800d16001e44600842d243c842c0181d0807060104848000035598900303d040243e40c945804e510745140b80615a02980d50414908000054000c0d84005030402070420a890072038101d0700c540380d1a4652240380541e10304014200000f600050b05005030801c000b100d0802d6801150b00d5954036000c1e81e00c00e91050b42c1d20a0041015881414103140c4203802002da400101141107040d55200384151051140c288034256207200c050104910707402588 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 739142526 1250 739141276 739141307
    0x12150703061a0301060e0436050105010e07170412031d0d050d140903040e13050a0f03081e070e15030117010c0c1e02012a050f01060515070201 63
    0x202c1100142c0c0200c1ca840e04248100c100040380c079120300c042030820380700c0e00e41c0c1c04075030301514525040c40b5401c000040f8040344400c1c0d5050111056040440c50030701c1594040d0200003038110030b60030010f000400c51a034103010360001048100034400020200d4291190042440c03c001c182000c0142041e005100c07640d001b041180680319054400691041c014100b031401124200309204080011240b80f0008031011180c5500812040c800b42c40e60807540c0e030f8042100e1261103250308965807000d00b0040062012100461700c401c441c1c0406400c02c595541c0501d00f0a04c4000d200b1200c042d48404000140c401409e1000702840c2d54015164240301e444000f4641c61025529603440048441055458154080652034007580b86c0245101d0100d001007076030800c003070682001500c07680900b1199003010407410320100343d24105200f0080188042c8001c486502503850407003e060050821400c0b04022070f07180d00d8020f06000682d14071400810300340303071070032803540302c401e544010b0715514640e01c82e4a = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 739143776 1250 739142526 739142549
    0xb030403080106080a20030c0403080d02030103110d0f0b090106090e0f01150503120c1e2b12050c130314070b030709090504052104050307051215070306 67
    0x84145070304030001c0c50403076905980d501019580e5829081c11244000310050303814001d03003080e4414100c51405950800246140b0500e03017566655500d001e80d00c055443c0f00c1107500800100240502c59000782028501654031050118040d550039440c401c11800c004c2440641d02c020607000002580a0000341c080320a04001001028920540d40c103030400c01e03640c45600708920b07020704030f181e071003038104940f00640100303905038103201d102c2202d4001440308007003403203641e09080080c207101860040341d440050141054901c00e0b014544a9110705410403002048804e542420a500030405c8982d46040707000010300b03840c1c084103040b0034820560300102003040c8407804401e01101602910440b80354074111002155030341c196120328001150aa0081124182c0402c010100d03038121030760240c0700394141d90400e400402d9150045040441540c25204041424001d500b0108911805020210340c0c0342c43d030084200010307907148500400c1094601c212008512294041d4012002400d29030008 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 739145026 1250 739143776 739143781
    0x90507090e0c060406020c2e05070605180706030c0c0f110909010513030507080910110f01050c030c0a1b081e07050c0f0a0b0c01090c1a041505040b03 66
    0x41005000d01c100100c500b8040c0381e040700528940441210116082a0041d11502c84e18404100e4440c5404000e101c4080d00c02c402510b03030060000e42c038100c00000e078035020340328069400e0900c11a4401040811481c0b40c48402c10400c820029a0004a03800b6203800b0604072071000c81149ca0400525000b170014124004103001c00012100d4503032225402c1c0c0d112550703507036484045406c0c0c0b0420358158041f1003080c1c00c1600800d1007034005101c081d0241ca01c8919025668000c91540900c5e0300b80140020818a184458158240b004000b80710203070b002030060f414642101040e1344005459540c64880008110910382d020b50103007240d5003482d01400f000310205041c03070016039009030070400c00c42214500030400c00c1c1d0400107440c00c0035008001440d0f00d60301c00040c03000560108170710503030001207142c000604021000090a00064000000c50541c0f00b9190448041e1402d40040000490349a05100402a030f4015142121180000c8690700280d485083c0c0d9584543d0304500d00300381c8000304 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 739146276 1250 739145026 739145039
    0x8150a18051506041503110d0303020c060a05100503010207031b14070b03041b0b03040308070e040e0c0a05061e0906041a07020907020313060e040b0604080708190b0604050a090507 79
    0x29030f10420080c0c0d4140500f0b1082421202d4115090200405000302800300304501d080240d417407152680710341030042c902040d1400c450700e040800c5954035512500d8201304039220b108410b070b0340010581540203508100c3d00b59005800e0810b240316960034000d8030107604091001141801c00d10f1060740040d01c4000b034035060070b110154011a401c1d41c80324813124401c0c407420101c0400720308548410342e440c1d00b103480c0c0ba642101c2406028004008002d58501d801d48540c2e61071245000c040060002854114030b40d00500030883c9aa074041485007400b40178108801030045646440700301e40000c0a99a0b0000c8800a11540165007020019078440a00044c03060000001071000d031f4000c6958840960b11400d080741d0381c1c81980d60f020411083c82c4e00c1000f0480c01560700c00d6440e20b0003031001c5802004c140c0820300302e4000303070300403502540f00c02410090034200f441944036600e0a210845407071151621000343c403090240000c0e00540e0f4907400144894015400030030410f52240c1034625255a458 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 739147526 1250 739146276 739146313
    0x4390f1b021914180411010908010c050703180b030402060c010e15011e060f05090103090807032601120212010b0a03080a1202090906090402180403031508150a1805 72
    0x30340e04501d10f203c40101541c076062062081140c4e403001d401030180d4032507881a901d0690076444034140820000d0100b8140420300418a28901c10b0740d0700c644a6140342001854907501200c05072040c940c030f0605005035400741d421603601c26010303140c4956803100240c0c3c081c01089001c0c2c00c80602c1c021540c0010a1160310b010a504981c03061a20a640c0c900c02c10300c0c0e204040d414400c02012030307101806403c2c580c0c007079805091034140c141400035550f901522040340552210604a00280c400755803040c044802905804941c00385015030001503042c81042241c401c0918030292145206400340c9400702c4003500001c4010b10040e062910469403450809a1a000104900d021405001051690003003910903103005400052040c42d6903104c40007032054000d00038100b0703a048041c2c0e194000d000c034146881716014510903a000160500c03200f611041004842c0c000d280950802c00394640000c1801030415003042a80d580065031130141060340002002c180b000521a0080003605081c040340382 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 739148776 1250 739147526 739147529
    0x220c080a03030b06030f0a23010905040b0f131b051002010b0306070e150a020102070f030512100b0a111606050702090703090521070204390f1b0219 65
    0xc0d1000d0041070600d90401101740012941c00d0400d030b2074a070004040c11000c2c0c2204c007901e03c9414060042003e401d94a1035080d000341c109840c0349031146d00340000c028018510307660010015808201034100f0000c00c051035440000050216404110165884001c21003031900030a8000d00d0208800d245a102902030546c0f911030a20034010395000540d403074010000c108440310000c00710110907041e00c0b44c243e03145d0400f140c1d4004641d42070140704000b0b140e114001103914001c1c2c40c0d0544504100504d00f000810040c8200009002a50100010b44284054680540b01030900c000c0701040d640c05d4620b0103ca1150070031170600302c1c810010b6000d8204005040b400c8c02502c284985958803031054050358841c90303005140f0382c0300c1c0e0b08551100c42154010000503004100382440c0c01c15070340004043c0c4180880210114034149000e00d0741003100720111049241c4400c80b43c0c449240c8040141078039462200d03071401d10a000840c1c90080c40c40000c003210450f0b004107400640d44050040b10244e5905 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 739150026 1250 739148776 739148783
    0x2130b010e0a260c060f0d02040f06110709021801030c030b060d0c14091c03090e01091d0c090a0c02070801050405010c020706140f09220b01030b040e06220c080a 71
    0x7203441200350799038040360f01110b041000d06110318004440003106c2d15540421101200250709101c0802c4650701d500406000340b4855540014114020284900b403650075030092582030310404c4a8141d000c2c50400c54a1040d03001d080000c2c500444403401e078040c00c401c0c00704c15840180080c03a003000644540c08241e040c4881c2c9e4079448041c80c0301240b13480a01c24004969403040c0304c011103001580c810901d54403801d100707281900305103640c1c48504400c1142030700980301640d11088643e120000d03810030350018440c01c5000701a038801c2c21000c52907001e0003401340800300340c5a000a1280900800c8000009d00c50b090081000303140504000707008015030174034a0018043c0300d50000740584900801951030001030281894070b024840b00b20b41d554024034030644c200d80710581510030b070f4181581c0d0901083d4808404521216024001400c0340c82414005100303511340f04030310b05074100c0020260342c082400e100346c50030300300c0805013280c01c0e420b621001007040c49901c50110308050041240450240f0 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 739151276 1250 739150026 739150079
    0x61201060807030c02011104090e120f09040b010309020a09110c0a0b040b0618010e13021806030105010b0715020703050910091a0c0303071805060c06040c0806010302130b010e0a 78
    0x44c1448200c1c240d80308041400e00d0307640140001d0044210941c40109001c1d01d01c0d0841e038031131f280d40e0035101075600150340071051000e0200d501c07005420680103440344039109203010400d040700c03070380010010b075100e000c1c180d20349135517120100d5a21f01c00d00480304804554412079482034460b1a20008039035003160103d5000140902250f02403d1078810203c441c01c0c03284070a03910341e003052000303182240014600b1001d04c422100000150b04e8551440c404d500180d2100040c0b4a0090103060960300c044c0d020030320240041046070040b03414014465980a018540540d98100e981000c0b01c15005082c0c0c2d20750700c0850412234590031500320101d5011180c00382c0c103181242da103c400c1010f89018078051100c03160020800a519544510107401c000a00e0302e400311010354a50001c034006030407680542c0f4840e8020010700003881a85038110000700320703400c000e00e0f282d8110342c0860400f07503c1e041c0685126843d088040d000345e0040c03854001404000c0c1104100c581e8903420b410002500a414400e11407 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 739152526 1250 739151276 739151291
    0x408070605030f0a020702041d0109060614060906210c04030506060922031e021e0d1e0c06020a0c02011b0209060609010309060e01020c070f030507031106120106080703 74
    0x500510569104081d03040c3e001c040b55840b04030b440065808924102c0c2c2c0b103a50f0b076030032460305503002c040000c0102c1030b80e00015480980b0300d40401168055000980c0c030065200c01d00d08680d8581e0121101d40c1010381d14039444290070006010140e1281051a0084407100108200e40003804081c20880380140111040b54940c0300070b00c0307840c041c161001c0d82010085000c048030305a00c1c4c6c0d00503599074464600034203018500c4036084580e440c02000e042c0180c00000d0b040c0390084001807960110f1100c04082c080d0544c001e68040c0c000345807800000b66030301e2000c501e0400e45004010848031b66070810030940d51355001c41c800601150f8480c0c001c030b001c9030030001c01201c2e091300c111643c0c0003036a0103491a40c0d19110350081000d42c2c0c112100540c10075403900e05d08800154640681144404803100158449006011841c01d00724960002c03032071100824010400300360000340c00001c03a074210040390000d03c00d04010a07014440c4100910f51040f41c1e8000180b003d52040c0302c103109405581d400c1141c0fa = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 739153776 1250 739152526 739152539
    0x7030f0c02010509040c1b150e0304052b0c0308030a0609200904110c06010312020a082d0a0c03030f0902060d0e032101030c0902032a04080a08040807 66
    0x10040c060019000810511801c0d1107130409034816810707540a414604001c68807000c07011002c024000084428601c281000d84107e00c2c1c60150104030340603180034500301420a0081500d180c002c0c8d20106140003c20b5244c1c014540104580109503009003815001c26107d081c010340d61703801500c40c200c41e80e10b040c4001414251a1069a02c13200c4080702d200002480300710035094542003690195070007a600c001e58103120030078030014034107003034520007418656246052110740200ca0062040a40d00010a4040050103000c01c0741e001c1e40f2020840310242d00b6084045d14414800e0340c10b100b212a000500c25541a044800f141c1114802d0341c085c08580722480c81c40c4160f401c000c1000790415070621028103030305107581060080f00200800c403410500010002012003044100d03815101110200520034441c3c84100500507140d072010a43c81c60808000118444901c21301c030f4201c10004408403402090702e081150005c00014084038502c4025003042c040310f40c4603100c0d0782d01502c990a40060780 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 739155026 1250 739153776 739153787
    0x10c051e070f1404050429190c051605030702060a120c030b0a0b09060c06010b0406021005060108011509030503030a0f0b1804020d080903010f0506030d02010b030c010f030b1507030f 80
    0x6503020365241022100f00c00003444050000940f003100d0b030f15160088081c8185048400d400307000381c0d00706092000d00b412100003175550013400403000d0150a0580032404140c1007030032604120001c0c21038101c101d486003000d60940c024018001e620aa00180900c0d000c1e600600c1c59002c54010302040001c3c0350f840e44240c0c00c0750381031960341d80c004030800008c001d020300e444042e10351742c58090007041c6040410761110381412000d030803001414002040a1010b15030401548101800000080000d4144500080c1c500c0005200d2075030315012540c03054640620480d0110300070f59100b41100c1d12400c0400c0c41101401c020f01c406400f0a191401c00c1107540703000807001440302800c030040788003501c5580a00060400e202d0080d1141c00c02000056075a0b102442000d080c501e03211000115030421500301030034030000b0300d0702c003045a0520f04500095030700828060070b110000d0811041c5089118401c0d0042e00031a07031059800302c0c0c080c9a103880112188001d140030b030f01c40d5a4403500150340380000e940 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 739156276 1250 739155026 739155029
    0x108010b09091f020d091407090212010b030a02213423030703060504050a0e071806050409120201151a09040b041d120f0304060209010c051e070f 64
    0x90070f5000040700d41890340c008901c1c507001c5402400c054581024940b01ca010f03612104001c071420901e08040144603401402144058450448103500d4080344100c0c0c11122041070049020317103100040403920b408085c0e81200c044600b00c039409240008140102d4a418204030f50220300c0c4114252a1503500b0000f0b490f258023004200401c40541205a400700e0354198081603007800041e4811a803100728035080f018500c103100c15900030074079500f404140401d440c5d0107400c801c600c13402e0500e11240c0b11000309410303058403015090507001d90301d0280400058141c6901c010341182c03404d40b95005019806002e100c1c0c0c0c1c03101c1c2e0002c0c410702e01d42041480c8985014881c503074411840e000e1159aa4648800810110714000d001041c1c80502c40c00040031612080f030040040e06405102c0c424030b030000d00000d150000c81c500c10604090503e0401c800520004100505455000945510b50f070300500c0000a01d44d04107044070044102e1149002034401e0707504030306000d0720441d800060030002100e40c0a0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 739157526 1250 739156276 739156291
    0x4090e06010504200450060909060405071b030306051903031b05070314030a0306080304060c03030902041d0a031205070507080d2004140d08160f08030f0108010b09 72
    0x42c681381c50440180565242c04291109462030495000c0e400380c1c00303201001c8010464601011401d000c5000344841e0508000107e01441c000e108502c1213944450300c80e0b911820555003c00d96a5900604450360782da1101030380c4e00e0809480c41c52081c154917510680690301e09492514000003c4903008040c03604610004001441950006207034000c0e503070316540064490700450314841c0d181d45e01c0900300d604030032086215500202e0001c801d5a03160140c2c00c000c115110244d80346c00e041080051a400c0502409400d25455084227411915250b003c2195071015602144500b10810420b68841e03400c000c059000400411844140c040c00b481424082c0c00541c0b6040e2501a40d640c860315150000f203c110b0700c055444c0103880c640c07070180301c5081c0c0d4028540c10384d0303503645e0800503181d04441201c00454047d03501810300000140e800001c03113030f0190704070341444000e502c980392400900800c040001d200351808001e0002d4250440215816907000320002c1c05000d8000c801e020074001300700d5030407 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 739158776 1250 739157526 739157591
    0x9101b021005040b160e0a0303080601080a090308060105090d211103031003061e140106021e07091d010606090e010e0f070e0a0b040b0304051603081206040204090e06010504 76
    0x45650683c10080c0c10154003605006d041c03e0105000184905205c1c2d0066010452100801c081585d00000042c6c2c00300f202d4008010f502001d480c001c1403d03c0040c04141400350004900c45155101100c2c03005840e40906108803004010404001c2c1d624600748160200c0c200d08a02e000079000402071746d10964242c04160026032a64584c900641145000410f99200d40900030984044c14080c10380c145404014000d9254540340e0020301d403800c00c141c038510f42d820550b00c860743c280012600d03104885034540046440510500d012100202c800214451076113041da0005130380c0c3e040784540e4102c3e141c156650ba45030707030b80d007420941e0744408031109205074400e0b4000401c1107000b00403100a001018024001881d1640c4200300c0340e9115030014006044048200002c010040000d90400d8464030480710503c0c0c80d541c1c13000c407980652040800c2d900f501200049070307600c135a4161801842e00040600071108210021750f2100400c1c054103008906080c2044004400751020340d803246c820b403091 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 739160026 1250 739158776 739158781
    0x10f02030a0c021c030831080906190903120503090a03110c182403030403061a130903110106062c03030f0c0d09030b0a020309101b021005040b 63
    0x4031005441c440b0104c0e4403166041000703000c1d80d51104c0282c00c1e140b0a440c0d10350703181046542100d800c2c0480312010310300300d0b003070854541c20600410f03a0034520b940f091540c1c0d202d900220004030399004007550b9103428044000846035103a446500d01e42100d006003910b1407081c0ba003001c02c8a583c8801c546141c8194015181c000c006442264031880c88005101590005041031001404c41340b521044038070f0031f10103d0140a61707000d80147c2c0603402900021804819402c40700403079202d003e9488080e14641d0340c0d240b0043c0e58032400641c0e00c2240401030103a0440170f541c08603040200145107041d0005408210100b400420500c00d81003610b0703035a16000f43c0e032a50a50782c0142e4511004a003c980c440b0000c88658586082000e0000b10b185841c0e040d4a4080400c2c4851800102081c2d072400c000407040304001250014000070381154600300e01683d030ba40c4510f2240c1c1381043d29005440c51600c1e04071000000c101144124038000110342c29125071018084000058620039100030740b01ca01c15102 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 739161276 1250 739160026 739160047
    0x20307050f0a02070305060c0a26040b09160b0c0f0d09180906090b06122116020d050f0f0705030c0907140301080a02130c2705040f1a010f0203 63
    0x38100d0360b241c40c811a04507580b40d5840a003004800d448003c0000030200d8030b20394064020002c080c1490301620307102c1c84414000c2074902c034400042c0000c1c5c105800840405c000013818800030b1400f16101e07407481000c642d030741c0d0403662980c080e80c03c0700c2e0b207030281e05112002480c01203140303041601681d4404e027401e410f0810500d59540c02031055090070b5954455040042c10b40e0085811050044a04d0140c9103880e00503c0341940c0781102d001103980042c003600070340c0c1d150f010803881c610f1041150b080d216001900e0b4103120041038100a94001c0740414030b4400c105001401328400003050302503859100c4a007480554030704c81c03800b699034950005041c4200604004100300e038080d01d5031906600d40f5604112804aa5000381c00400c019005804d101c410360626090590070825540000c0000d000e540c2001800580003075a4070700201c0c10401d030b440c820012064004081c1c5001402004501c4a051100c5e00a04100304403400351200078416658540c000c40300301d000981d254024601e841c03410710 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 739162526 1250 739161276 739161307
    0xa02010f02010e060a020301050a050901060c03200f0109020406090905030334020f0c060304110d060204052e1715030712060203042a0909230a0b010902030705 70
    0xc0924219942d0390590328801c482000a140111030100c0016642c0d4105800d0000c2c10006270822800b4100c01c0d8010010540e01c02e074441d60568141c80c1c0b503040c00080310a03500103200c600060139114030540b015860340c01010740c043d1070b196100b101c0401241e42c1c0c9401450542d0100d56001d0581e8106100140300c0c034130364401e0310311441101d0304004901030003040404190303081205c120300140e000d81503070100c40300c040101d00e000302000c45826055144c29592804100e12801c0703980d001e6040c8207401c400f040780e15019900548402408c2000f60362844410341c003400110403080909803100c02c80d40b14403d0150300d03d81e070500c0541035031083c560750f081705610b60300c4210b0030811740502c0349203030005a0076401000550314a1291102603a42d0038581881d040c4100c1c200060400200003881e00350304504041001011030b40c0b07000020884000034288900b02c031241e541034020030b502c1c00c1c2e00c1c41524900443c007400d54900c200500210350b40c036020151708a000460340305012810030480203102d940e140 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 739163776 1250 739162526 739162547
    0x15080c060703180806010611060901060f0314010e03160b060f090f090a12090312030c02030412020f0d05010e060c030402030604030e2706040609090c032d0b0610020303090a0201 78
    0x20035100200f50395035403101d281c008240e1010307000448040010035822014003070182c02400140082c00b52504140b0000c412524910005103100d50318800c040095400303402900048004c5800d0742c1c2c0f44d01c08603094142091340342c0d03821a4080c45000004400380b4007140110100080a40b05840903540c100140c032500d18050070543d030781e11500140500048a00340040d0703c0f884665aa20b0416286160100070071b015007010345d080c1400c0c0000800003c0c0d0000a0710100c824190040101c60503500100e11400113140c403030b60301b2100d9014458148141500401041506081103501f130303541c5d120201406000071307076009615402c94404500800e1150282080000009024482d2850604001340d42d40314400c00540366030945600300442c600d0f00c2c1c807500c40144243c12090181e200f040d960f81d01c0715119800000d0000d04080500c50710712010115000464401200c810503031041d80c00d0070004a80c00700c5000b0710615051201411082c0302101350303400b40103182c00801e4005699401903c244a20 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 739165026 1250 739163776 739163807
    0x204020708070807080d14060d0224040902130608010303080c0a1b110418050a080a030b19050a05010c0b070f0509101e0201230a0f05090115080c060703 67
    0x1807100b5400310b25002c000700401807041003101d80d101c000c500c41d4415aa050201b035600d0680c60300410a0a440340c9408ca0f02c03855048400c00f40d586d6900c2104440d24403503021601ba551408500898020050ba0052100d29000381301c0d41c140d21340d1800c044648003004d01008002a5064020807000e40b007240241c606d1011a003450f101c010b0990800030364805510009036141c400d10703080f0b0042d90030315224000c02e0044a10030010a100107448242c0c1c0c0c7d0b00c1040000300100000640401c0d2a0700c030b54002d10803443c00400101000349031182c520f5a844045c000d40e4171604d507c1341c0024540d805018500071040e480f4054510315a906002504c503143c0c0e540550341800020017485002e0b944102030070207903000079110300040c1007900f0021203800c1c501a54a034196031410740303854040b03c3c03800d6034a1302240790f2082c022038907510003402c40c4c050801c05002e80159800c100920200600c19001005418006c4641994050340c0b051400c1e03998100c2549250000c10400c00200030a200381040c00300400c6 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 739166276 1250 739165026 739165043
    0xc050f091c060b09010510200f0303040b0103030201060b0702010f1805040e152d1914091c090b090a030209040311060c0a090b09130c03021801080108060402040207 72
    0x502502808001c854484200d51050341d5034408216464a015500d000d018107076040030104481003c081d00300300641944401150103000074a480c103104100c03586075410004143c0b612420305181910740c02000b03010441c0903509103440800c02d0a801070030365901540580d1148446840d02c901500c14144a0030103560a0354510004900da8546001d0f80b0312401c003d000400c02c5421140008490b4003010301056149500140b0216186051041948181c281000b0201140e00c45c400c940d144100c0514800c40200d041c01c0e0b603140c0d80a000c101c240e00c141640002e0724116a0541585c0700e00803c050040d41c003088a0301001d00c58101c0b00c40241a11402c0680391141c01c5450742c000641045c000c50b41200012f0164000741c030b5141043c40321540052010f19514140850418041c180b00828001c0c1d00a846010031052543d980e82c002840b1185010034007000004e215500041c0a9030091005920302d815000d03070719010b5442104011b04035280c86002c0d1084c1d403a0b0f0f41c00c01002c1d50240c2c0b800c1e1440c60 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 739167526 1250 739166276 739166299
    0x1410020f030708071a010b0415050f0f0c070e10032009010e190f06080d1407030819150302120d02030d0506280e151c03090807031b08010c050f09 64
    0x2d003040d2054040c2007c0c00046881da031070140300700300c02038400d0628020010107225101d494401c4078141c402c003480350b800487c0c4a440301c9040d01e240c0000b5070b2021020030180804c3c8006890355600741b0b0240c030302941c0c0d00c50b0b89401c00641e510514148041d080d0304184009c00400c103c940c2040250781115007104140049807000414100b0703100348104810314182d42d40d2040201c15410403410000441501b031540c19040014012803160003100300150034403510030002103161400044042004010b002d00b00003501d01d00c1d852040c1041c07140000ca0145103188017081d102c0a000860101441140e80110b1402a6416080d005000060700d80c58103c0010306d40c03a060304500c08a0440b038044034664240c421840d1580e11040e0ba0710107407005034998800c034000303841900c0b604403022018014808003200c0401600d0212004416980704178801d024215020081160300c0c00c00c58000d001b00080682419141c41e0214229101c20003000085442080b1610740c516104c0c004d4482140700410020041 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 739168776 1250 739167526 739167563
    0x415080703110a080f090a080417152503050c0a1b0501020a020f010f0b1005090d0206040603020912151f03060f0509010e060c04170109020a1410020f03070807 70
    0x20f8019101580104c2d03102420450380c1064001e8080e4040c2040004002036030054840891503c40d034000c4e40040d41850051189541d82007011610700c440007204005680313040c45920750200c03100d14404102e40201000c00c10031034400c0c0602801415080c03140c51806050031404d451034000d003c0a412040502d1081802140f001c2c800303802c01925a070050300074510f6111500d800c54403104412a45145010540da06580302c4545903803c2c4541d50528130795030351030140020010410307410000d60110000802095203036254010300754000741901c0035503580355081d100d01e403560400d42041481c5030741040000c0981250048920007000024030138542141c0720344030780007900e2035020210411303610354041c040c2c4108248901c40b00544480b014040a09184040d8070181c400c42c49003000c10074481e40c0c550540882940210006035005011900d90760341c800e03a6040102801e08514821a41186224455400803407050002e0705039070302071803410210380e4481c8400e401c0044140e501184085889401 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 739170026 1250 739168776 739168811
    0x2090a0506070606030c0b0a05040308030c0c10061a0304050a1e06020c070e06100905060f09040e0c191a07110405090c090709050603150f090a060e0604020415080703 73
    0x2902c0c0151000b285103802d41c109400e10116071f501c03026290344100240c143c042c3e0b000f41900c06903584500b10580e40e4803010310108250107203451001207809161039400400301558840c030120740c0c4d840c1041c2c0a401d690420102280812103002d001070f001030865000041403608045202141c0c002c20b11410711231911000d0898100c4100003846030b1108000f03008016100ba0329a034000c1c401c883c4402044108030340102180f80601c1014000c24001c1040e81c481e1318120140c415681000d0403c2003c0c004080540d80e4415031034008030301130543c00c2d10880700c1c2c1a83c85a204190f40400882c10b901d41403d440d816800d0380403540580300701004002e1090796643d580181e5008041580007001000500010031204010143c02d01d0203026819200304500d441e2101031f170b03a12142d1030f000700440c040344a0203c2d6821003001103080c5c0c840e0103d0104000d1600b90303400003060350200004a446644d42206110482c442d80c001c88240390804091440858814240c25900103882d02c1c0219040e0b00660200d0384 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 739171276 1250 739170026 739170037
    0xb0f0d270f020301111c0504020a08011e0c0509100c1505090607080601032f07060e03030712021e030402040b03071203030f11070311190309171f02090a0506 69
    0x1c140d0342481c8001d042d45000d0203845000490120304601d0000381071302024644d442000043e80841d101d800280c150760320030308060014401a0000c1c4280f00301c2c150180c0284000340c0011043c0c0e407070720b00404038140c403640590b03c100d030004d0704041d481d09203a101940c5004034004200c0399400d002072800b92400d02e6000b400d006000c000000c0609050080002c0c0c60040c1c01400d89042610b8440705102d28003031508491000c03150f401c044440b4401c1805205000c0c4290340c0060324040c1400d20703042625000000543c4030314050b5a91108840541e440701080e4480d8400122030041200c000d070b00c0301080c0307400a41d040351004000060030701c0d54101217420015680d0241c2452500300781c4075000d00d5054080c08440015428081044048250108500307010382e80002d400c011250100c10f0018804004140d80b9124200d03201c285418107140082c000d0006000320303070700300c802c4c29000130030f244002600300c1c105890350010195001c0500d107104002d410074103150741e01c521019400603140e12401c2c005d25 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 739172526 1250 739171276 739171283
    0x203040819020a052a270a062301050a18031a061e0310020904091b05180108060609061f09050a050d05030a051309050c0301091a0102301605010506090c0702100e030d02010606090b0f0d27 82
    0x1013140390c9a010401e98142002c003c45524410480320009036a000c240f40074500600240140c444034040040380c01400d4603500100302c038010621a181c0c500990040800702c1c1c0c0201c40301c0204121000d0500ca4502c001e02c00c1c4003003948a01c011038441d00e4075035059030340144090200e40742d81c2510b5021845180802020a0210300d44110900003802c000700682c02800040d10780410304001c66071020342c1ca100740e021f98002c000000c28003c5440d2000c402d600d004000c0f4074410320250820341040d154580c030a01c18001020300d080a680703a129022100b042c81c018058019203030306045003018098903241030202e16411a107241c60a400440c0103405800c4024000c2c420916905003440c0080c01c650000d46118483c0081c6401c005407503d50350221056154150f41c01c0c158544e0320501a50644003541d51154580a41459160050750550000c0d0032a07006a89502031a0741e18003141550b031207014684181e0800410469180150541145550b9460812001003140782c0d0031030503140d05402071046 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 739173776 1250 739172526 739172573
    0xa1d01170403030c1d0a03120c0f140d0906021903022d0705010e130906090804060804150b060d0203040819020a052a270a062301050a1803 61
    0x4c0800c031381d100e04d00c0f5020411902a65403a240a4030015201154504c001800601045038625a00c2d210340081a0002c0d480400300c600781394145007030284000301e005c040145114618580d00194418140801240c40741c1d0003500c810149400c240845000c028801d405500c142c3c01480510300803209880108800449070a84010718448540c0c144541540080e040041442084600f0ba80b0212840303079103400f012002a4003621403404102405006802424120b408200024030079000301c9003500c00c5114108000100013031011100071659040c0300d960b0080d9042c8151800002e0681c001c54019010303d003903e040c6800741082000214601c03105000607003003070f1003000c1041400c004010040031b0b81c0e1a804c48603086501802e24592444449502c41c5400010110740b1071041d6198072440030501c82d080280f0310b0118941d40107009644601010708d0850202c01e1600c042d08031512608510581d569403801c0c10900003141c0039801400091384484400400000040c0c0c002240c41d0046c1100054 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 739175026 1250 739173776 739173791
    0x60e0d02010603020f0d21030e060c0307030e06010e0c0903072411060f220c0632070b040201023d090c1502032205150a1d0117040303 59
    0x1030040c54000d6020703280c01051840d11450007d0182c440c4118089007a64130301000e00e003410005c078094602e980244a4600401c4140072614a022000314440c9405460038010109424145a41d4180034440d552030b007647d05011501e00c03641070004101091005085804540c0c5402e800048100491043c880749240f0364400c40c000ca81084001502c0001403010703200d075252000114011060080c03079100001e1000d105420040116008440100d8100740f40e855060703120100541b600c004a01506250300c43e960310041007016000c41050403158400300f0500341000c2c0e50f03800e084040c0141c001c80c158060078009400c90221146510039600c61031162954604080700e07220201088140a403001c1800e103042c010110300c2108040c1d04469690030888a0304440d990200d055000d401e4654480400c0d10400000c5100354019210030f072007040301da0b000403100a202d10102807140d02606004501c480c4040c42d912208410441c0c031980042c1091682402d9101141014800482c1c003100803030307a81c410 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 739176276 1250 739175026 739175029
    0x608010507020123040206090d14060103020f030a030c02120a2901060306030305071401020c0102040906032109090c030b10021e060601021f09020406080307060c090e0a09060e0d0201060302 83
    0x1425800c5503030130100d0203c01c135044220f9403e550340140040d001c0c403c002003040741c3d61500311090002c140c00082e94000903190301907642d00d610081c40140c0c841c100c1c52100540d03601c0c0105a00103019416150070100c03142590030701c547c035403500030514403a019841c400c0020a14020105050302c850110003015000500056440d010b01038020a0405247c62424800241c01100b150f1881c2c3c3c100e032485200400c0c041c201806440390740300240c8a0b5001240c000344160403a00311400340e901c290801f142e005920042404240800642c6074001440d4840810403030354194044410404a03180100b40c00c00751001080000044050a10041c2d01400344104010705007498080150046009000241441d1000075507402101c6000002d40022040c10711a00550394031501280e40c2c06030003400303000e903600340098483e0003804042d039101e8104042800c00340d1040ca083c0e8150341030001041015256013a40800908821804540450741c0e070f04803020340d140802c5103010100e03066002043c050304620 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 739177526 1250 739176276 739176281
    0xc03060f11030a022a1e15040f030512010e0103050d020109081b0f06010902040e0705030105010f0e0415080d030f0b09040b0403140f0405010e0303070b0c0310050406080105070201 79
    0x42250480364500845158804140c0c0c0c00c80b5004001c2c40409a1a01d10958100c07100c0c0c000319009003159070181008014040d40828404000a10000254910525510717141e454004e228004041020100b0000317000609071218044840c2c020300e03106080283d0900c900e100340b80281c0201c09022a03800040040000c00c014441c56100288001d1003140361aa940302c0c0c26004c1c0007401c421aa41600c10081c0c225020001c14428000e03074030031604030f9656481190300a500c640a00c00e0a0300a490018010a014100300c0e4121441a5180c02d5a040c0c01c51080f582c0b001800c2030315a200e40c503614140e6008050b22a5a4043c00d8400007402010160803406022121005030007908141080c0032141c590761041c13481980725070032559000d0f50341c0e120720f0120780d004104035446d055a4404121203100c0c00d41c2c10094025510283c13601c040d944642c40c05c1583da400390040003040d0f40101000980009100d4015542081c0d2001d0342111040c1c0300c90024081d9195031300680c0c4943c0d512400c0094165090 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 739178776 1250 739177526 739177541
    0xd211a10030e0a080906090303070b0601030b09070206010902130506070309060f1412090f10051e0903180402040503030c0f0114042f0907110d050c0d03050604090804030c0306 77
    0x3800c0030012011040d80e080d8650f0000000034001507804110b014181c0c9900045845813030000702600d55444042c0707020110321405985c039500003458031000030381e181041ca52540c0100c6c1d541e00100300580c644a1000c0103580a241d082600d44411b072070005a82c2c50b820094a820381c803c1e1182c220342030034500300802c0400c451440b0001c11540c08040686d2088060840d00c214958108a01c0240c0d1441c01322890050b001003070750850310904950f01e01d001e1143e848140183c000c2d107504e52034020900c00b1201c48240c25681050990802c104000c1ca2000d40900304948510160000d4185950f410001e4196000b140c000701c0360380c0102d0303c3c02a00c01000c1c8600d0420307481d10349540640d8107117503d484030030794803801402c1d140301070640743c0d018000303001d0020000510000300440341505d4884070050594458105c0c2e01640e11441c2010411580144251130807802c54800501000c0b500000450190402030181c6030410f986640300300c04568008000c00203180203a0300c80c410035142d8604801241d066 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 739180026 1250 739178776 739178809
    0x2010f020d0c08071a04030507060b150a0e0301060b1605010b060a090506032a0a260a0b0a15032f0702040902040f0c020c031b030d211a 60
    0x21046100d245600a110201d00d42e4200700c59036204c44251400428024102c40c40300d801c00121005c00c803c141e48400142600d030310a00e001e0000c0c490030401d210355000d507148092000c0074148001300d9100d10892070740c200c50317500070300100303050f41e645d031407014550301600700ea140e01c07807180d0b502505204017400344002d0608156421450030300c21240040500b03d01b402940d10a040000c049913500c2490300c100d00170740b41d01800041498412014420a40d4050342c2c940740402c500603903200c01c460070b00c0c00d010038500e2503080c914401e0340c4850444000300182e00324143c0c0b013101090b0210b5802e0080003000041000390b10005562292071280000422400f05649415410a00340410301c2c02040143c50b1610b605641c045690496840042c000d410402c880d14003241c906002d54011039400140c3c401c0360070050703055030030b40c009903403007400d048156128084d0154071158a24050511551980355450301a100000e1034600d80610401a81c070b840b0034480c00903c036650130f1800392900b4041868401c00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 739181276 1250 739180026 739180033
    0x605240306130201030c170112021509010c1b030b10080114070207060e060c0d0f0e0f0a18020909010e0f100e070c03051903050a180b130819050702010f02 68
    0x2406810480b10004200d8001e04154807501e600300701601401000428104110401083e90713180c203010060221030750001d92061011440c44042c104040c81101c481040c1a50740741c0a10007140c0b41c445620082c3e01c100c44103272540c400c000010801c04404140101e080c0441c0d488668600304005007562a1000d2244141c1818014014820b40005444003111080d081c1401450903d00000780e4074001d2048040c080d0040ca040f1a00c16030b803244130b08515094980703600203104190020b00c041c1805050382d251308203410b80414406900c80112007403420794001005880c041c00d00c4041a061442a070000488081360706c1401003040130b000b5520b601440d450014100c0c20f1503c0e1013400346203c05850041400340c40031144041c144100119288075881410015950461080080007448101c0b18003580600c3c110169002c644500c000f09009030700302d6480661380d00d881c1e00da03428105603210102c410041c00c01410520040300b040007403400110340c85903501c1d42e5080c0005070101a944034074504541 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 739182526 1250 739181276 739181281
    0xd05100c1707021c181a0a0306060810210204020c0706031407083402030408010609020703140307050705120316030c0207060c05031c0c02070801060803030708130605240306 76
    0x101341240d503025041c0d20349082c00c8095091201e0102d118000c0d000000903589880070f03003400300344080040c440b040840e681081100d0707441c2800c0700c100c0c0382a1030b68900c072035508004201c6038002018448400301c48401c100c81d2039030558005000c0b0391040d070510071260450481046000d80500c20341039941981e0140d000c1c1d80c50002001481c60350020a012040c03481924407a8540c0010404480b84901071100c01035040c510003800703556900540300f00c2e0810340c00e03e00c001c601650307a40241d412150381600c0e00c403444444009104260b4200400f420b007009030a1242d000490400c02c40240c00b04160b85400e030760703400d010048005140381400111300389400c0445046000e580064044116015448e1421a02c0160700c3c2c40c034150f10078010b01c1664074801c5060a060f400392a40810380091454003180c04403030751410b40500b69804c5106807060b43d0018000100010b019004481c2e00c06011054980010459924101261400d40d98090300b40381c4004c07403030000d08141d1168a000d4100b01e00400700c51 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 739183776 1250 739182526 739182553
    0x70f05072102130e0f0105160207180b061309140609060f12030706020c060907170c09060103061707050f0d0f02100306082e02030f04020d05100c170702 67
    0x40d540100001d024041c0389a886400040940c800c00c2c9541c0007506940358046401c4006011f002c0540d4401c03d01055045010503c90001174444219010b480c9417644003004615014000c000480d060b44d0800c1c1e08010700481400c070b6104140150040103400504040e410104410b074100041415004a03440024030480e03580e4062402441e4100312400c104a8400f41031aa046009424005002c5030010900031380703044010518610a070f4246080b0340f8502c1d80c4454507440c003900d007101507040d50080c1b160304185040c88620280d0100040c1004240295120603e80b00c03140c03c820603c02c00e0304040d40a20062428064002580c01c00715800980030740d4540341c00c40c010560100091240d008802c000076030a00940028000f0116101541d42001070001d01c514280c04442c60400c044010f0415074007184030520a49014504040502545175519800e1120070190078800f6140c1c0d1058024200590f0f11030f01038044101c00d56079811404244280a02ea09540040c004034195042084c826400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 739185026 1250 739183776 739183829
    0xe060d0e060f01081e121b060f0c0406081b07060b0111070510031805060405150c071703060307030803010b041d13020105130e04081801090311101103070f0507 70
    0x689100701050100e5000500d140d8940804a1260b850411007c1031840c10084003422640c4000c6117132040c0c50303095881c00c0804604210448503d00c0d54102404240003151194410b9580710b007007603184041c05524000300c00c1c015001400c2c102e403001e0b102d03850038a8a50b44a000c102c0c5812220700102420381c1484001102003425100c154105a614101648030392012010800c0058212055a00b00d04207401c15075251b411902c3e014202d400880003061201c682c0b00216801d2130340054030145030011451520810b0b0740080c0c00300b0361510403004c0110200b07041d02c4c02140240344500c070641c1e4a92900049186c0d07034503222801d00c07a070180c4200f080310782410102ca1404150782441d2040c1d80341c5c8152101140d00c0d24503084140092884c00401c003c01400c04000c201c807107007009810890285c1100119074050160100420806406515a180703041815180b24410040c2c01c100c0d440440d010005881d40d00300d030070300f030b1920710803038000c0014420140725100c003a02600304548440c0402d035128808 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 739186276 1250 739185026 739185043
    0x203060a020c03090a06181403030f0c010e1b0f0301110415053a0c1215081207060501170606060a03020418091101020c0d020409030e060d0e060f0108 66
    0xc0305400080880c14000180100c5540080041410202e9522410010800e4900e506020326a200011001c16a0b10a4104001c540d082c0200214a424401d03220312040b48c2100740814855900d40040000090781840f001c001050f8602802c54060203540800c507602080609580c0aa494a103d03487d446101c0400c56081d01e050100101405c0302ca64402c44591144070040e40900484060035039214089080c00951040031100524140c2010000c030300441b2128540e41000c9800d4408a421000054106240303d984003071002e207155079034507801410b080e40c4a1440c1055440000d416081100c144680b901401400450030000c001e110700072907036140042c10740ba1107060301068081e8a0340c4250100c034042e0051400039045030840c07100c2c0b03902134201d54204644080041c2180c0100e948001006030326410000d06034840302600d0b800340001440c038407034190204100f4001604003030300c85000500c0c440c1c1c80e524001904807060001d250408070050095041e103490720004100501000402c01d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 739187526 1250 739186276 739186291
    0x30105070f021902031f06061d0d030309020613090902040e061e06031c0201020c12161403070609030804110a05130c1223010503010b0d080c010207021305060f0a03020306 75
    0x10f1515a482c000245820f2403212410b81c17000410300941607042103a0031080480344140c80f0001d4803a1410500452603101d04689070304615040104404a0702c03e0b00941101782c000761407103190100c5101001000d4140d81c05c03d1185036124252481103003840c0c030411009045d1f00000d0840380c10304441c6e5030652040180c00c8015109100c000c610036580a00440711070030640000d00c080f513541e42c04003034080c0d00230b26911030b15406022101c0030f002c0e52a5081350902c103012045901e666055564031801ca4030000419103051100303019620006100e44107621425000781c41d014150718040c9081c143c090381c0401d419001d25686541080f207900c86200185200a2400002ca4101169181101d41d04107141203202c4007414102140c001e08002c0c0502c0d04442801e00d6840c4042ea2208245421707100c0c0c0d140b080c0d400c92000303280c007004503103258080d144000d560300003d4644801600041e900e007170720f0014020499031307a0040c00b01d680703421040d41040c075006135a400402c40c0f43d9000603895400003003081 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 739188776 1250 739187526 739187563
    0x614040e13050f03160b100803033c0f0c040513020901030b15270904080a09030f03080a1d060606090102010605090a05010807060c050c0402090103110d0902030105070f02 75
    0x41e081110510000401d07014101c00c4a444072004032009a102e107025500f910a011950007051102a4801c600026500705800851540d119001400c0040841e048240c10020505840c82c3c4c844c48036070b60302010f04502c54550342007420001180000610080d044240c203000070002048940c880c2201800510300c02c9400588810300c820050300580760100015920102001340200407100010103000c841c00181901c07140041001100c0c0c10b0350810101c03160380020340c9070000300000c03c080e004111074100740c50b146041664940d180d43c4c1400307060f00700b00e02150420b005c0144024031407203509200030507079880e030020800345248a52503c00241c0f88034010180001c0851040e4001d4102a006240141c0030003107502d0f101015400910080c0034190150280304000130b01da038450f05004008a81203c054070001102d6400c0100a40c044440380341815100d40c0c0368115442601e0151203481c407204000b00360303003c4c40c0c4101400c444008090b241400f9106a85000c202c0d400070b4000c010400343c1a21 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 739190026 1250 739188776 739188811
    0x4080a060c110a052a04050f090613021f090b03010e010914071709010b0a030503070204050a200a1b110406080304061211040b070c211a0a240614040e 66
    0x1030128011507001c3c41d41150034441441114200c0092302c9120354103001c25242079469443c94100c404480c020040c0d4801c1c0c4180f96400b801040c000e019540c003509090841c242680c0b0103c3c86c503250000d2b8400c4034501000e90042014101c0d42c01003501c682d8242540a12030b1070111b4010341810300440d1002c1522000300001002840300350302c94004c8010041205225543d2460b007242d89600c04c400c00c80c060790604021407199021801a03d51003801d071400b6071141c0340ea140d02400705400c001e141c1c50402800031704c0d01110950b02c0c100d41c20481e000380d030f0829054500c8000c2c04142d84603903200102c5540100010441d650f80005111441c40400c0380c08a01001110b6012103940640e8008a18943c00000c0e894100203131801150300711020708040580004141c08000034801300510081d00e968030b00508400725010000b0219488043e03280700144130004040081e410034038090501850580040b002d00103039802140048220303a000c3da01034501810f00c24000c8422801808940888140300b82 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 739191276 1250 739190026 739190083
    0x6050306040605060d0c0e03030c1e210705061b09011202040b0a0504031205040305030f0304020d140f0f070f0b07020d060216021e031e0304080a060c110a05 69
    0x8800003e10340140a10745854401000c0030040c034104101001103070480e0a0800141404026503040001c50703409048001080170b030300700d040010b50344c640240c0d000d040442003012401001c005165074042c1500b03520b910b494600145440c9028040101034820341e0007900002c403009084800b0302c1002e2030704045040c03081c01c107076010f0300840e0482030900502240c207110140d400005001101d0092505003100c020340390040e00c103072041340400751540d041041040c0c20b845454006580080c80502500d0a2401c1926200d030b200d404061000019005000880c6c810f040411006200c4418200a01000c2d803421200c442d40081a120345010800e0100320b0109540c0d030104098405500018290340c0c3d410341d41c402100369a2842002c070310030200c3c03e21600000286040d080f50034070b809001012100d032801100c0044e0442c80000040c50321080101183d8640c0038000414102e10600c1e020464403419100548604000203d403605984010b2150000c1900010100264801c020700d0b5101d0a62044 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 739192526 1250 739191276 739191281
    0x40f030f0201141f030c080105070e09130602181f020717190c1205030a08100b1806040b0f1206030313140f0d0f05060a0e0705040e010e01061508100f0605030604 71
    0x1780040c02100d02d01500042e19841900140d10400b01a9140184403920b0b00800030652000d4481002615062141c07400058240d8014842840b03040c1e0407243c1d41c041440001c268000d803041d600d807182822801c41240c13640400c270702d00280110f80b0481ca0040c0d108222107607a131120810244400a4100c250018031880c03a031080c000d811304075200c000000640c01d005a80307038031003a40b81000600417800200003101e0400040160382100040e00d16142d400078071101005032106001c5d5010108000000b03040c00503000406103143d88a10aa446600102210040c100d0003807050f030007034000300046440742a00c90007050565204955564000d200640440c45506140905680140004404100b4402c051600d02c1d5928418411500296569040f41040c1c80240010f440d143d8400c11042c00b072442c040d00402940500f03000006020b42d0b818440da03094070020362001d07803099a000405c058155000e0411740d0300401c40280c54901c61314140310301c00e00080310310a2004104010011070059075558 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 739193776 1250 739192526 739192529
    0xe0c041116290106020d17070e060d0609060906050a0f05091f08060c03091b1e15031e01060f080109230c040801060515030a0903110105040f030f0201141f 68
    0x1100e03104095070719402c0103591180d00c1e06e420741c045444e02038500000b00a000a1500c60400c42ea41d500b041c0c1111818402290840c03642d6641094030340350081104179030352007210001d0043d0f10010802920746024000c0c03110140d045030181182d030802c14401520313418016604072080c030f2500044a00a41c8030044108541d030011a0369000d240e051162a031900b07070240d40100042c1041d500018842d040040d00c84040304020b64001c0c14042c014100c0c2c0b044102071079114000500400c05140782e84581092a500c2102c070410b034441c1c030030248150a4920001180545800c1c180412050341d080005860440148584078205442c0d910192008031117151080d0307052740282c1580c44034180300012055030303005401050000c0d0701c0d0000c0090b40b40b500c2009450007200710700045140d034648504882c0a00b240c1401941400f68526038425614400d100e214800c9004104c0d00c0600e06051800400d4840d40e004848216814040307098298051125907503000b1a00d4100c400484040800c1043e46e00e080c2e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 739195026 1250 739193776 739193843
    0x39030c070f050a080a03050f19020d0f020c0307061803090b0306010507080a0806010e060702090115020f03070b070212041d18100b090c12180309040e0c041116 70
    0x25407001c0f50401c0192009000c03c2c0040b5207040c00f03180d8501004005c1d80000311184003c04079801801811801c0c103a008000e1270802c08070204a0341508410b04041e640f06030401c0c140c2d580005142002e201441c0b141441d10040344518060014580d1001046907006000701c08000c0e00000218103a60300580c02c4031006640306405a4035006101406020903100b01c0703030580401c641140e020040e207003410803643d03000d0380188100030503400d00402c1c0d24003a00001c0b4403401d61141000d02c94201b1010005856440e00c038203e0070303100c0d1800f41c00090400501c44002d030319004080c44140689641d40d9800245501c0155054100f561006100800114651940a51400384c04070075942c120103900028110102528002965200c040f1080c0c218403d00040c0c940303511809001c598071540c2d50ba213050202c820300c004c581c200b100010016040f940d440c10680c3c0242c5c40b942151525080070301a150306481c101c0e603501d080040c081703008454180c041d0402480b0181030a00c0d140e00c5026807014501c44d0a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 739196276 1250 739195026 739195033
    0x1200f12011409010602010b01021f060b0705060109060f12020f010315090e060603060c070201081003060c031a0102010e03030c0a0306090207050706110c03150c07050639030c070f05 80
    0xc1d240202c803001180c189400c2e006040c441c0011401c140140a140301400040c0c0c020821800b100843c01c0b003401580c00c0080c00300740c84500004410096002a000150149024160b59490420780380704036007095100a040310f5103c0810824107216810b0085c40301d4040c0d0390389619a800000480040824010000d10520208130104000c085a03001da184480c0304005c0300c4d9a5140c0c08109903480004841040c10700c2c4040020720015403240d080315410200c0c06130320f0903406480c0d684000a81c8d0601c007904001a990780015580070080724a441800542030000f080b42d52114008180c880c8401042005c4800d03000034240b4100d8803d0f880140100100304046403070702c005107401603c3c1d04003407150343e000030f103521081100c030741c400710f006101414001e008013080246440042c8203048024043c01e03940c042800030502081c02800450720805014500c011640c0c400c2c0712010505143d000c1c003400c0030382c0b00c1c9410f180f100e0301c1600300d9401400f02594561183c2040c5045221007080341d000604600 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 739197526 1250 739196276 739196279
    0x515010b04060e031218010c15090209070e010909020a02070b04140f180f0604020c06041119060206061c151a09090c0d08160f020a0801200f1201 64
    0xc91090161003030391031035607500c0100340c0f0040800d030f91282040c4110144807410000e0100031111403486480c040b07418140850744e0400764031441c154403d08400303250305580740c00200085240140c1a41d9003d5201e0402025503010000000c0c2102020302608000c9a40000d440c40514001c1181d480104840302101e0b644503251044054020744d00041d00e8003445000080c4600d92514000c0107030b900c0041140e100640e81ca08100602d038100203049240c0065003006102c030404400e02800307224600a00d1860207070b03000c00d400d005035030403100200501c90040d40c2d010720015902285841d00990308544182c2170903400700c01501c180c0c91034a0010b010210f0304094056450882d00605a84132720560000001400030301400303c201c604440000840c0c12240032a003e500c0c0c00d5402001c0d040c025586e5504203501d007200d10340c0b429020081911610140c006510441c0b4040813000060240310000740110107002111240314605806c850044a02c0812026030071003401c0e0984502c1c2c05508201d0f0141d5 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 739198776 1250 739197526 739197539
    0x1b01090b0c0a0b060409200109050402040902120f19150909152d200307120f020a2010022808240d02031209030f0a030207050d051501 59
    0x4a40040c01200c0e01e0f10f9501c0021a43c0c84c0c0381c4540c0e03085541244220010350103650100000c0c80151960905002903400049000c0d16a440540701520300030a006079110020a81c69003030010040c1025400c1d5000c1040021101c03900c1605601401160070201e030501c0860a640072100c00e0360494a98036107001601c4c1c0501150030700d1142c0c5042000d40401400c5403226501c205900c84080f82141d8012030102d0300b69070410381d03101c50b10b9600214400386c100c40c80b0350325a01403680195030718070000301c0f8640010007240891080c00c04940c000001146000382c4000301030410710107003a00d249408018034002400d81428081061658804d03d0219a101c4000c0d0620142d40d007080380001c69210001e4006c0c00c418002c10b001400740030081c421a0400800c01d12515108850604854010464030050401070710104540f4525400d812581d40c0c5035117100061516045010102041d90307800324000303c010a07004a100c0f17082e96000e81c0e0302c05078600c10b8244a8604901440c0e600c2021403070400002c1c0c01c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 739200026 1250 739198776 739198783
    0xf0a03060312052a06070f0e040e03090a060903150b030a060e060f06010314060f04060308040b0301031725060e0a03080a0c020c060412030311031003060f05091b01090b0c 75
    0x52403c4c0462203402010301e040401d107141130415a1080c0d0794040b80104107000d0040350800b00900380d92400e41c030300d6101c400c0882d0a490754000d900415a04c040760b0084246040c110b030350060301c45c924110906516544404010958050410030503940d20341e100001c07600d0138084c1d5071409070004024000000f902401950703686003110012185100e600100b501c41d8860300840410340808844803400740c4460ac2045800702000742c41d076510560325000000000d21030806440142100440c41e0b03180c0d852350400c90407400a42d010f13001c014108100b04964112401c071030094119a801c6024248a0640b406000800a5011001c7c2d184207640c0180105503012080c2ea05c124885002480b10010400041ea9110104410580d000700141300901410002d040d10201c02406458007107215021642104425401a20840508541d9040c140207120031030003040b5000082c0b00040180c0e15041d40d03a83e4554a0407680c0304007010181c5095011a8415984d0002a080c10004142c5d00c1420f602801c1d41c = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 739201276 1250 739200026 739200037
    0x21305030a05010c0e041a040513020a150e0d021324090509060702071505031b03040f050c1e24160c0e06010507080c070302151b060c0301030f0c09020d020d05100303050f0a0306031205 81
    0x15681313b48002541419a6040707c20343d0b02800c9500e5800205010310083c04580d110200c8207070300c0c101c21884a40c09450502c0040061110000d00c134100464145d0901c0801010041554080300307081000507000c1425520f950030500e00f5580f0398444042081c104d03101c00c249184000300100620050058840d0f050703200921920480759240340502c14040b000d411b12855a205190031304a62401e42070041c01071041540040451201000309031a412440d00007400c0100c8804c61040d121080021030140c14010f0700c00b80d400070a2500d44440020440e210f9805c000302a68000315400c8501c050030007202c0051035000f405850f4040c181842c4c0c1307900d900300c401840700c0c2041e0306c594420001c601243c0280600c010040312840d503030840d05c446122100d55801203690103a650b60000d150744682c8003502e04441c0113480584d4a510032509417081d1800501300000c080d0209108200003034110f41250643c0400001c2a0f443e0300005034150f00900c0350354000781400c1c041c10310400059034803800070030 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 739202526 1250 739201276 739201319
    0xe090a0c0b040e15090109020d0b060d14010603090b07030911041122030f030c051c090f1508010302041817030609010807030b0a021305030a05010c0e041a040513020a 73
    0x1281d584c82c8220424010040e4450340c101500c400148030400721031300140b0791034503503403800f05030000d411001c50040e902146203103040e10703a17483c4501400280d1440041c014906843c050090648545030703202014406451300041c942c3d144040c0003081001105071406400050080004001c07404d03050116600c0f284401d1070807142c2c1001e44690100d82036003507040c0da41202d00d02c800562660307003c1d181c6c141c400c0d60a030341c1441900c8040d080c0710703189031003000c1030f40701c0b680d030441d10030715000240c5003002c920380241c5006841c000221041c01c1c1d1100d070309411207404903008980c1c5000c600d80ca8008030000707a40540301ba0b000150405125080c080258003132007054a103650300340e981d0611507480b0142d6002c0204a0244032000c1411000d054000d060950050090070343d10540c2c6000180c50410301040031902130351580880c00200c2d401a141c03064031001900c082c001403860b03004800ca48200121814030039681c40000c160004a180c0740089500e50141440d4540c60b200c080000c054180707800400c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 739203776 1250 739202526 739202549
    0x11407060e0705031f0c030603050f0a020414091f061a071a092116061a030c030a0609060e030a050d0b011b150e120705070b0c070e090a0c0b04 63
    0x83c4505000441d1610310140720a421484400d0301c0888010340503000e60b0700c04050303c4400100c0410014018808446080402012000b040e0f2042c00306030b451481010800d001c4c4130041049030714010900080f0120585403864050515541e220014040c5400091080262010003081c1d034404000030041d9030700491003011100d0080841443d05501100d01c100f16030801c903030a00583e004084140c02c1070150141c0142050082a560144185121002d4030001c0d101c140581500b020041c102ca8100c400f40d0252035091880c0010075914003082d040200740e295240e10290610071564088500116200140c0c2c0d80c03021280c60040c55500a160303148559450407041048a41c05881107221200440c00c80e020901070584800030320120102009080d90b0303c2d1039002011102c14003200b0100d80c51050070545903003081c18034a2a01d0159009802e1031207082105030001030000401604440c9613910880351507072403142450405090000003003811444039808114901c0b520060b10aa40606648 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 739205026 1250 739203776 739203779
    0x16050a050f133603020705012619050a06031e020402130602030319021602150c070b1801080103110603061504060824181512010e060705070c0e06011407060e07 70
    0xc40b180620003c0c2c005025a00010040195502400007035010003d8400600f1183d44402440c2550040840c0c0d2a1000050708a10700071280903849001e810500429080048504564900303181c043d441c00d0300c2c0031291444521800b19030b21030f01104c4980307000d003000411546c1e4500001c0e54a401c20345007002034142c0241000202d1482c1e1090b18040e420450000c0d0b0181266001c0c01001051859108100703d410080504010010800100100701c50080c4039560316200003501020144400841d0420181500401c0418541e034185414428201d80f8565643c44031400180d8420903503042d0109103802140c00034042e500064118415a401120007008c4010328030030160241161141720f9010030b0760044103025150f80302c1c2c01540800b0860904d848000750f130f40084d0001000b482000070310b82d164400b420045070180300c125000800382c1821400c201095980c1d014481c81e9020350b690039420800050322aa00c2401142c02080c04619525546c028a040440203400100d40d0007001e80320300c1c0c00 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 739206276 1250 739205026 739205111
    0x30209090a0b070c1703070f030b03010c020709020c032701090909050d0804030516061b140d1e050f060301050108070812031302150c16050a050f13 65
    0xd0404001e64403084030b03034203951110001e80300541800340a8a2002c940e100b0b403c03441028400444c081d0384542c0318032100e40c0d01040c00605031280416214040d1341054000c4c1921900000c0440644040901c09611001c0040c2040c1ca14051100340c21461110a08843c80760400c10030910006c14007039035a010151b031114049030036217070b07014001042644603166558030741c0d2003500c444d90003500c240b031f0845c505202441411010f240562054031420b5841c0e565614a000d1242c281c004180d45c1e0030f0400302c00703140d40d0a0081a001b10464111102e44030410407010b4051f22022842c3c224218000300300e10f0601c6213204106000c216072044c0a076107400b00100b00601d0003d0b24000f141c1614008240003620588945501d0700082d007243c0c045040242e00d800181d881d10f1001c0c0c0f202581d00303015034949010340c0034189010740c0c04000e2008001030045c14015a01d03000499011740300d0a4500b4141800140082a0301d181c039012540900741c5400028000e0305d030f140c14462070400c00b04403810440c0340903c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 739207526 1250 739206276 739206283
    0x3080f090615010f0c021017100f05060a09030219050414060f010c0c0e070206070212030114010806010c140606010908011a0d02033408030c060a0b040609140103020909 74
    0x220140e0141100750301840040d03104001203004c892161030076181e055000e6000c0783d04060080301d00c0d8080b40c0d113a2111120f150180c031105610410300080c00c4000c40c6068004000e0840f0790007080c0c0070340c03400a00d07680e02d580140c080e140196405003051031240a080b00384070810125000380703072240381041d400f9000100d0b642c0f036041c06860f000b00105880400e401c01900d03d40c040d51002c40303204d1034044000a1000c4c0c9603a000c1e04c1703180145c01030f1005151621009050031484075007521000014001071050001ca60381082111000703080213621615280016140004070320384c024080c407030082402c41d102002041c00380c05201c00fa00d4600c0b80c607849070b0741c0c10300b83c0750b0011004000084500c448502440d0000c05211a10b0000d002d90f00905103411034400303c184440d60030007650b65a0001108440e940d8162000281103010140d42010b103000151a01e8110143c03038402030320380300c1c2d00c0d0303244998942d0301850090a04090411410030103d070070407520b01c070910090b440740c1d1a290000d0140c41c80031 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 739208633 1107 739207526 739207531
    0x9080c030a110d081b19030c030e0102040e0a0f0207140d0207120b040312021303030c0506182e02030127020c1e0c030a03080f0906 58
    0x20490190140c0400c5840201550028410364080c56004c4051a040b41d1805805a014000d16030121190300071040d818090401d0021040f030f125406512040300d120050b10107114030008a07060b1030803801180b103400156140040014603501a0b940700d0105051003000040c2005c00603200c5c2910015007010040030740c0c1c484441c1540c1581c04212604c02041c00c000d01507010051035650540810b00580010203000000107070708075000d1140c0503580390203175030100240010380c0c0e800d0082445020a00a4846008840101d4000310150b2411031a007580b940050504080c00f04500d00c291203c10400904048410350712180040207000540c02130225a20036240ca1060300329070044032040421612000c0d10400c0146c8034004041008031a42401641c002c68100d518031041e4249085d041d95194180030300ba488004068200034827600414900c00c24044d42d42d140840341d507954109 = true := by decide +kernel

theorem cover : BRFrame.Cov 739028776 739208633 := by
  have h0 := BRFrame.cov_init 739028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 739028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 739028776 ≤ n) (h2 : n < 739208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
