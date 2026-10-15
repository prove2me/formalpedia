-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4760
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:38:47.598102+00:00
-- url     : https://prove2.me/submissions/d71a1c0b-90f7-4c9e-9478-c2c16fa0cb80

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 855935251 ≤ n < 856115107 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 855936501 1250 855935251 855935279
    0x310090c3209100308190801050406030309030f0f020612240f010c0c0b1219020f09060d090b070815090f060f01170708040606090c0801061b020a 64
    0x110204200c4901c060014024051052101044001e4503445105001c0e82840703044140e00c00c4420701102c044950303c0e1140c4240d17a0040e40300300d580c94105040000019040804103002d818256802c1050320706503500640489603c0c0000350030070f50b110018504110303013080f4854080b0381c00340425072918a5a80c07142840101515924408051754601c4e8a114089914402c6d5400c0020440210300484400556800640607400e6071052598800402e000d14440001c00200482c040c410900f480d0a110600240c02c044902485003401044a040000b54800948840325000c0710416503411901d9480b100802c2098002490454035204000e42260055001d0784511401e54861801d108090b0030064041d200310b03510180500340034042840e50603c4a62201c00f100107041040110344601c4419489040843c2e1400000700c13811704200c1000702c203010369002410307603400504c01149810000b0b095180140181b80030819050000740102d030395a1581d10f0841e4018000000741038a43c000740840340 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 855937751 1250 855936501 855936509
    0xf0204060b0313080a0509180609160507033902041d0703060209060909130218041101030e07050607150b12030f1c0509030702010f0302090f0f0310090c 67
    0x68a400e100190840141007240c0c4118808000305881070310303035a40c00c00c82c0d80001e812042081800d120701c0c2e03c2d5450324122264080300c090b500400ca03251002c10042046401840c00100704948458904d010b5000800e4403c62541410020040134a0001c200303600880c215503c401640b00130030700740d03005004240d6240081d009036014042481107480e841030324202d02a0812080d07000c8401080030807560703405804a8140101014680b00000000440316001601e2080b00d04c1480c400040841c82c01d541d041000715980007211071246080e4984024101490800905140e120b00f100d2801d144244010b4014113001840c49854240c1424401c0a030604820b0320b00d0b2161501c6103d1040d0301d04031000d01459440709008624148400e848581180c01002c0201a24160000b11100300d20071030040c2441002c440c0010340e210300c00c0703000041c1004000405541498810030141c81d01361110382c40300110300e4082d98900209500303280032910b0640303001c0f0381850700f40c504015001002503110800b0115 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 855939001 1250 855937751 855937759
    0xd110301090c0f0206101802041a030a0606020a0b06011803020a080304060e0418030f090503030a080a050f010501021c171003050f010b060304021e042424050f040f030f02 75
    0x1604003890700341d85e0b07a08155400071070118000c80070400d034481100703403624050078080d016080075600c03040103c061002000405030054003100300440d0120030f105907801810320344010300f96030051361035111f4015000b1b00b40504100001544508006131008440000c65010345000d030f0725581c589125072a604103010700000101012540001840c20f406110f83c043c0d15042142c81c2807003940d90503038040c0d103510b03610024001c1c40c480026141d035041c0040c1203c00419182d2540034608400480c0880c0c0000702000c101c10841c0c0014403640c1d0380001c0c502c001e4800401c807002e110708401c45c00d544d0050840c08a680c02c545000c100105140d85200300380c100d0348200101c40740c00d418400c415007a0345118500d50381100c0244001000741c40c0c2110040d0204214520040388507440001080c252130314100341d807141c140200f642c444400284409a40201400035260703408e407154141e02c07498083e1460340741301004404074a1941402015045070700400099000720305940d5640307003078030101d042c4940582c49 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 855940251 1250 855939001 855939017
    0x7050c090910110702130b1c08040e280507110f0a020a05030a050d0302071406071d0a1206020702030304050d0b01091b20010b03010c0e1c020310020d110301090c 71
    0xe0ba0f18007400b9144002d60040c08414000ca9245c1214000d06440100c96440340004a02c2c0da092084103240800980c0108040ea50f01c03030405141000e1589e0180048080713941504e003070200300303200d0780c004c80110007035030001f1809807103000b4100c6000a080826640c103000c0c80b031800081200018840da41d8130b01c02e589441c1065030b61010140c42d0595050040d04a4001202d4111143d01c070380d004041e0603224038410b000d50000044007078076099080b1042e4020071b05206198800072060410510804000c8030540c256509000441042c3d01508a00a0609801282180440d0ba083c010703a006018041e100079086e00c500d0074074850b9400b003849080c2c2c0306840d113189440c00340082d2158134180350030307900c804038a0304041c00c0707030a03040103800e4149646540c1c48404000564080c01035031024100c0d03544c0d11881040d20700412000c540b220045015910750780c5041001601d0114000c00c80c104624001600c60301000c1c407681c09455400044451500d0010012904030324541c0551600c200039038079054 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 855941501 1250 855940251 855940271
    0x50f21120c010b0f100c17040f1707090209010c030e06070204090804150509010f180902030c22050f060714070b0a02010509070b0316050f07060b010f140d0207050c090910 75
    0x41d1054541c07504c50002401126803c0100d030b011045400c0418905441034230f029a82e40500c202040541c000440220840e0b9030001960360030030240c00500f26080c0110300e4001c1c408000f80504074000001000e2080b00615410940e8840c0d01303484415801910900c95145280b80945065005020b000703850108031a1160103244214281e80c400403040c1c4843c0303104500284292400e40400004204c0e9080c8680c000c0b801c12944e00145000316521f019941d00e4807055014500043c0e100040f404e5082c07024038081010781c0c1c5041020410314016500d880d81c45910f4249036450144141016403039204141c8005030300005e41e0001c1120309100d500801c100e40701c2d820ba0749c2c1ca83c10240700780d00e40c46105001180e41c0c028030307503008a0b0781039240c14001d16200540070103617450781019400303031001035031040d1020301c55030016044000b4043c5860b200d40c400e034200c03030201524041e10120818a9a0200c0e44000b0418100440a110750005003013078283d00d031060030966102100c03086401c9007030400065031 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 855942751 1250 855941501 855941509
    0x1101110a200a0807060906090308090d02030c03190908010c020a0b15030a02011101020c0a08070c0e0c0403060b040b031005100f0e061905060f030103050106050f21120c010b0f 77
    0x1c05200c0d025000e0010301d1081d445000054100c070314107440d0b1035960311418001440610811185078401e4070b690146140545000d0700f86541c0038001820f540040044006844010080300d4003074001c14400c4542201c0c8480403a003e00c199004100c2c50740c07030980c0f0030b81543e030005601c407165441204500242d598100d010407072400b6028143c1c0d090b40c0010000b000660003000b000b058400c142d000103007028030f0226500d15110b8441030590f50007800203079401c14491904401c2d40604031a96403005523007401040900c60b4442c0340710290425641d0b050810341680d640d0000003126034000c04071a002261090b18000504043e2182030900c0440300c000220342030407106110861b180740d0842242951341809001c0d44c2c000c1c0920500b60150004008209940e0300000b03000180c00e14080306440790304501e05242105c45941003d0710807003195544403801d5407200d00307020f1500b0b8140805035040d0780b408541e41c42c000034041e001341003080200d10040c1c1c7c014158003c201d0003908031210481400100148 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 855944001 1250 855942751 855942797
    0x130602011e11032e0603140601020f070317040b0a0e0301061406182e090906030807080703030b09090a050106090626030702090711010c020607021c1101110a 69
    0x9802c1c01d0824000251911a624807800006200d8008813032130690f41c40d0200c0101545070803181c0425507a0000d14442d90101e031000b07a101c1001e00050080035140da2415568101038400140b0303401000c00c00b00c50329000f503000e03a0000c4c0721220441e5100d8880d15405014a50060500c1d8083d40ca064000183d4a6000000000103400507010528100441040c00c4106010035103440c0c000418155190a03005404015040307a05564041c0700509051007004041843c56440f1101107401d20f03400740045070510b0200d598140d4003070794003a615000d82c038060700a0031207000000e43c0144010204070070b0100c042401425184903100803c038282d1200c1c094021142e1500509aa0f203a5030a14580a1560408031041c0306442d442100c0c01c00040d540002d903c2d00e01141c90800048180302a010800002d0150040c11007080c006820070389408040203503100684065011001c940d0811a04464005c9030303800c0f0854610750090044140c41080f0001661182072401d002580c1003070300000e010450760301 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 855945251 1250 855944001 855944021
    0x5241314062d042409050f010204031709010914030a0b1006020d03200912060a1509050610080a2406020c0307030c14220b04110a09030204050705130602011e 69
    0x50140a45041e5442144c0d0504008816144a03500c400240121b04200142c10550007490000760741c0341c1c11031801c104030300300e03042c40c042d203440e401d1001c0e602d9a070700070129a0985100b00c1c40341c05842d60b0794000030300d441c030500005003210081105010007a005d0441c42001d4070080e4081f140003110051040b0215442e0b814514402440c6000404280061200905d0303011001004071199000d007404a0381003030300030756407807010b9596061051040c840c249403440c002d00e046401007059203003d5021803041e10011000f202040051800121085515440320110074868010903000705001501601903050b54001c945c0584070b01840018203140015003102901d03400140c1c1a1220704d0504010360b00200b100301d4990080141b8a103103507007040c10925858200400070041103c501c404248012244100c4210340c503900b08000d02c030081078010801c401180d40c196400103890b610324000f1944c81c010000708010044120100240c2c10340d05421142d081e848656400c2d040030164440340e000c80d40d42c0b6074 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 855946501 1250 855945251 855945263
    0x1110d090b090406081c090e0903090d0606080714040f20030c190f12020a0e12100524090106080c0a0207091805241314062d04 56
    0x1060080040003000742c45003401c0a00b01064494407095103e00f804140e01000044403404000034500540c001c2d01d060081c1245170503c0750b1810b01c00255501c0384515260306000307a012460507400c0102d00d602c070384010810300081c1d41265440d0752080103c08642c04413070748540d081141001c080101032190342400d01c8280954036a00d4640300d0300700903541009014580c054005e0105102100708516100070329845941c0d080c10352030440001a082d18000045030303841601c140202202c2d141c000d030304c404215404581e106643c1c41e40100d524a400c422004160340c1604150030320130b0500d42004502074020324041084600d046110900000200074412400040d07414004100b440e42c20707200800c2c02068902c15510410b407644040000c1c1c550103294440c0a20301c0e000c5000c10310209001140e100901c1c044284615000d12a64040303006001e000d000c910b1514005200c20403045526440364405031400b5a010ba2400c3c0352801303d00800030702c0c0510100a512002e250800030410468030a50303100c8 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 855947751 1250 855946501 855946517
    0xf0303090c090a0b0901031203020d1b110f0c22110c06130503070305161b080c030c0307030b0c07060515010e01020a052d01050108101b020309010e01090e0405010b01110d 75
    0xb42350707264a0120442c10000b8154200300100141026006222030350799103111540f42c0e00c403c00340007800010410b545031515000088003060382e00c0041032401e0b400c00101c1d426090101000720080c5420503031280c5141c25460610070051140c0c0601c090036a00124600b940c4132541c0710b810050416207502001095a00b0400640b40002d000d40b0252601d220342001c00144002d055440320f0b0705910302642c0341c5888807111810000301204000170480050150b0140200e180307503101082e998016404000c1c16112060000380350360180c0015100380b80c2d00002c1c24401030900c644651042001e464259001500704030800b00c85500008102c400a64820020100055030380361000c503560003c140705502c100226045000b201090040601800810020301040c00c0b417640f0507004c58880036007441d80544a18021110300341c010045d20b443c2c074400e080c9010400d0785080100da0a00141c0c018145079100c0301c0c180014000c0542c01800c2c084000c0c5c0381c01c0034425040644c5640c51015031040800200a0 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 855949001 1250 855947751 855947753
    0x1b070e0c0301090504060905031215030c0a12080909070329010507060c051b07050a05090408030f0c070c0306140f090705010e040b1017010e0f0c0c0f0303090c090a0b090103 76
    0xa900880d1722601071580040e881c10150b643e00d080d64004106001c2c080e141d02c040c4903001043d030312019070201c0308400610710307001040302290b280002031148148410758407644006002ca1281102c0701c140004102d055a031078010f002900620341c226034100303203004203829004000c2d020034841e40703150016141c49003010744c0381d45d90101500b404ca403201c040040522016080080e1910250707601810707100076003104c50420007030118450f580d9004903ca414003000b88070101d0a102d049a0f0024200032100380d25a44811142185220700c61000f0041d5030041e10010a0101c26031040702c440802024100b0181c5031920a046d0394042a1842c500c541c0060300c04001640c0141d51910001e02c000d00045031400e90300000520024014002a0201b0070301b200b00513140880000725400340204030650391950401c3c010f04406884000d03c08507060600040000000c6420003090441001100c104d9a03030303140030844207840d1380e035400d18140a03185042c00300c0c00000440c06400504000544030700d205030310b1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 855950251 1250 855949001 855949019
    0x30609020102161404182a030c0303120e07140613030f06150602030c0613140618010e0c0d0303110c0a060204030b090309010f0e060f1b070e0c0301 65
    0x2054808078194071880488408a5121080704002006100d80084943e07020301d09100079906020800618000c040140000041c4c0e622142c3c44054661b03030504c20301e84580c0381220b4071240150005001000f00000010405030b0000d9048040b2054020901c42034183c030b4582a90384210b80034075121401c541d11545441d09004025010036081c106207a43e420f5030703070789629142b16100c801c20b480d07a030340350340569089454081c928030080609100451414070340314465500d82c00081c20064255001c6000070045c0980b1017840385500031642d0590381e4508003240c17103000307031841a00c2c0000e50f9401d02e1028421000042040c0e045d4074406080e211140c0c034a6078040b1b00801c43d28080c424504810f00140200c08020001e101d0310900c1240e0043c0c0e40d509500b04107200c010020078080e0207500030407030a07400740da000c4881e0140c0310903400c1c1000030b980c101001404501408018a1050201181500d020306401c4d001c40d40c0b0340e0242c01505c0c143ea071982c0d60483c48820881e0a2012100c0402c010010f04030 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 855951501 1250 855950251 855950261
    0x20d0b01020d020a06110904060816080d14070201052209062c1008100e331528080a1a10030803041209082103060f031207150501050603010306 63
    0x80a0951b50702d45401a00000e003202c500b0341041410740d0040040c01c5100805403802070150045000801941d03036100070082c2034211420380740340d40d00b40110f0400110f9002d00182d034414000000c03c03050f9441c1591a549002640307120b600041801c2c0440020038021202c0001c8030300c00d00d0400520b094580014918500c64081d1a001c82c230000302c070000410010500013929440d00f01d080c04613024205e03400302454000343c1d200840c403c0300d03200c0300349000304141c1460a100e1a002021b0035000d941d191400b003100888070f031201e0b41240400781c40040503d042010051054462001c500340c3d01c0d11480009d40e103040c030600040003240384079500c846c2c03002071075007507a40701140d400c007004815141d9883d01c0840d0402d55007201c1d0550810145a82250450a0751018180c0c8000a02000b2040307018101d444940201c1c604928034000040f80064a4030142150b060502030201c9049171802c008a031a181e00460703003600c20481942e00003082d080c0c18051b46040764802400f980c00d6900b1511a60002d10b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 855952751 1250 855951501 855951521
    0x9040e0a0218090d050a0c120e04020d0c200304051207090f0608060619060f1808060f07020c010e0111160b0309070501050306130207020303040b030109020d0b01020d020a06 76
    0x1218145503080165140680460140940800a0502d0508281c82460400b292200c2801d220040c08207600c145d031703c85400b00000360406a980c2820750740700425201540340640032030304280005003080e098542074000000500441e42d800e00c554a01e84240701e030f00080595205180c2e0010081001585400000300c8102c009090603500c1c80780d0307103074041d00444100c110411401511150200003198080c05804c0d80714005680400910000700610f044980c4580103142c184820600300d184482c0c8200f4903058850443c40f100c160131340d201e500c1a40e8881c42100d20003e00f1900000141c0040c2c40400c0e444111041a1145100840c1c09801543c0340201c10003540f240d13200c0e4000070491009a10783c1c1c40000c203500f2001c10341d01d00f04070b8011814607100d600028140701c0d04000f48040c5499030117001961701d8800c100140c03104002d1000a003144655800124049804000441c180446500800e51031446030b108101d1409004010b81c1c40d41d5001e00d540000d60003071500c5401080013600001c000e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 855954001 1250 855952751 855952753
    0xf0606060f031b0d0b040501060c0302100c0504050303041d010b1303261602010912110f0f0d15061409161e020a0606090204050607080708210a0b0402090609040e 71
    0xb2000310f2407110380149502100c42501d8190f205000e0400348141c5000d46054540003585000c41c3e1000ba50354001c43c040c1240440d80c45214003004d40c490404d0303801a010042c1a00d5850303583d10780741c40f0800006880074400410290001401d6513103401181c80c1e02c450340040b14401c51031a155410505c80f01c1d80901c04640e1030728400d126a1902d140207003c29607a400827170411540b5800010030407440d42d0071081e420909400d0310404120400300300f00c90654100e9400031b10010540108011611429285402c000c0b540105000c001181c58402c403800084c1c01c0411069903540285c01e40002da100c09a0782000c0301c940070800b05094100300c11207001c8a410462122400308401c0100c252440c810400181c005184c07800400070140a820000c001c8100198240340c28500012031600c14810001d0585078005400002c009a0b403040c0d0749046e043c44e95512480d002002c031100003020032542100114502010002c90746868401d03500010760150819080182c07400600008003071554400300700d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 855955251 1250 855954001 855954031
    0x1b0307050d14010c05090307050906130204060f080a110d0b04110a020d02010510080d0503090f0601060503070e0a1406071106030406141515210106020d020f0606060f03 74
    0x540314441c844180502c50034a8182280c40e078501e003421a00c40100e00802c0000401c64483c071558009111420380d0790840d990301c40d503218540052740c10404220140211400805c0008645030002200c207010b40058072405100e50383d03c00b5200c201d82d105542d00d4201c120a1041c000b400013980d02c0311140c907001920004081625070210710a079000009400300690007004a43c08a550a018041d0081d0562941d010003e0500c00115161340e0b01c140102c0c00c21030040005150014100b07c5c25000c1c0500030141d490a5071903200050240e44200e4011f00402e41c07020203172815040c0189410110b03200781042c2c60400c0424400c0010350f03400309801303903190140607155002c0350340e6042c0150301445c400d00700050007501c01c090b80c92040e00014401d5003a400307456a15005521020700040343c495251104507966140d080b11000400041d8200c150074011034400840d1003500013032040714a482d240c084901c0e50702810031883e41c560046800c5500440280016840020301e8000355030072191030f90881d8a = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 855956501 1250 855955251 855955259
    0xe030f0d050d0507020f15060f01180b1c06060c0c081c0806040906020f0901170c030109020706022205090a0b061c0929070309030503040209070912080301090b01050a021b0307 77
    0x221341500d1b070b007c1040714105402480810719005866410508082c01c05001040d00c40080110390320040c0306041071421300080c07049007101c02c20301782d00d10040b4101e401c0080c01d13245d6500900b0440b4401040701c0d40700088802103402280003550119803015900a6080b100c001c40007102d07202805403e554000d5150b800080014080d80080d03d00352007082080c5413a84401c10004000d1008141058036024401060024085410084034152141400c002d039441c80c084ca0003c4c02031051a140070024241e1141138a4014115648441103e00c04c03502c01c09262a140300100484001c504403651000703082045100c00c030850741c0020b0000d00f600e000091105425160f00858007801c00c2842980304000300f6480d415403031103080035040315051804001400c0590380152040c44080c00180c2b142210200049119116111600107001e402800d0946000340e0301d0b0801c51500b003809180d0106062140c852402e504c03c0003580c1da00d113111350003442c003041c80c015502800400da90065425019004002c9 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 855957751 1250 855956501 855956503
    0x20f010f02030d0c1d0103181b0509010b0c0115060e010e120106240201020f03010b0306040f060602010f061401050403151416030e2e0603060504030e030f0d050d0507020f 75
    0x2800714039060b160150340d8058108005ca00001d122140d81c10305182c06840f4606c5984200880c80c0703154080c0440300b4405e2144900c0c2d0f081010b80d40a0717948452a40300118943e4008800b8200b2852984001d0103102e11148100d600c2c41050700510340010b041440103641584502d081c0c0c1400200541108490000c0a88050940d00c140d080703884018038045400005401107034940c04180c103588001c46c20000c00f20744e009110322041c494454200700200205980340c8d00d55001c120704110720341d02000507503a02c50004e0b019004464186c2401403030f00300c0005010f0300c005541803010314140d5486240a0450b500c038180a10726004181d581035075862511240b68059a40030701a02c0500b0010410b00100040181501e491004042d0b55402c015058420074420701440c024405d801c64500c2d41c04030700104810000e1040750f0000d020282070400380010b0603000b8020b04400760050b8281c0d005d46007002d07107107a5540303550204400001d504102803903c55145902c940d800c4121441692451030074a0f00036 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 855959001 1250 855957751 855957761
    0x1409030102070f03080907031a180604062003060a0e04050307051504020a08010c080123031504020a171002070c03050d1e020d05040e060a0506130918020f010f02030d 73
    0x1c58001201503038a030f00740743d0400e42c0d01d540040054024907100b4203655039619003490031300301e8407460207800000c201076015600d00359520360b80c0700044407072614241c100071000d0003181d1a1009012088a404003904078601e00712031250001609400c1000e00d48114508244401417094a060000340f000c0400100c06005e0352001c01c44040403500d007800e140c0100045000f0583c043c5240f0382c50842c04041991704620030904542c00341400340c0c04011550075103028035030709900301c5030f040c021000c0c8855072001d88000240524025288000c01a484030340303d001c1005112030541c0d266001140e0000440c0542e0001c1408600ca0b042c0c21190030750f02e56407540340c00b586030764000101e07034041c035105903020004524404c5010340e4802400e5604c5031690141440c8103230700519604203510000540585c5901651000421000e02041d54500c1007180000b02c40650f400340340c1c8443e080200c100d00c3d0403920303c0c1d1020240d0300140040142e071414001519030494102402c4154081030100e0186072003031b8462 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 855960251 1250 855959001 855959003
    0x3020303030108030a030b041a01110f0f100e010c02030f1e0a120c031506260903070b01120809120a0206030a0c1808071503060308040306060320060901140903010207 73
    0x85884181c0c11740054152001c81d00c94034040e602e4527603004090b03450102d45102c0e0308020b0a040c401042c2da19070090400950340c00c041540d11801e003000030880c030b0000d02c80c2c0c2401d0130324404020841c24400010b081e9502c40740241e0041c1c0c03003404800c505400c004024603491600400340e0480e440051901e4000340c00c0f000c40b0001080c41410400792182d0300d4080c1c000803081502d020031048046880b10925501c41b4042d12040040104a020385407c3c0002441d1411030711403203986451400e01d8000d9541c4c1c3c04000c0407036944450b10000114440c401c2c00e110300142d4050180c40c18030000b4000c1c070205c4114001119250b204000800d80581c079a04d0045001e0410001c0100b00701c0c0145201910402209410b41c5000b00d603131714100045800803e204003a1041e008402115180d90395044000d804c068001070244000080d0000800040341d2040c0d003101d11401994062000c45480707d610082e1219429800c480e0030840501d0662240136039040321403c0290340c41c03d1145a0000c242240c0103808 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 855961501 1250 855960251 855960253
    0xd0c0b13050a030f0b06030109080d11160b0403120e060105060a12050403050301050315251103191b110111071a0310051e0d021203030403020127260403020303030108 73
    0x5445405d200c0e0080c450340d4800e86c2078009100b440c00550f151005031144902060415030b50b456910750118030700c0304035481d03440468040c403020401c031704008541e1302d0140e8045000c250800c18141d000e240e14010030649060010240c00b85a1a00040c0b01d407641c00200035170108200f100805801c10014072a540c003490081d510141c4941c1414141468044e000141e00c056520a000308660700a405048070605103900321044500901c4280680e079040e100d60102d012408086041c1e122800c0c00701d0785060050442d5542141043d00e00b43d2440b01e5054040040d0950325512081b881550041e01d090074204a090b04440f240741c2d492901007402c440c806400c11405100100740032a000c10020300d03102400007160300d213030b1119140c041100f80c40c0c2d03044829030051800034600320640da03d0117107401c0e11f0061001643d641e8501403400074001c120003281e400c0e001400d558050702023102944c1c0002569400101900007910168600164403003455004103511401c000c0440141c0f01803000d10700902c1090 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 855962751 1250 855961501 855961523
    0x130804081e121608070c0302030d0e010f08160309150e0f061006081504140906040506010e3315030f07170114010c121d0d0c0b13050a03 60
    0x681c5090034214030803901c1c180407409102443c41c0208001c8808030950380402c0f001d98600f00e51400c04041082075001a6040c01402480c0e1209608a408084200026a02c3c5c00d00d005841809880d024020b448003002e03109889402c11116010754004403c6a0140c1000415032043c03620720016100d880c001c0700c029420003103800d4400c6104200e160b800980701c4220b8101707242402c100904808005100c0700301c1c03061544103035640b0b80f55a40b000c900d0214907800381b4200c0c074000f804c06a0702d007000d0302d0445042c82800000603900c1191308225005030304241030b0b101c0c3d2003060140d05100c3c408a5166540083c051681e11505542e028095011441c1e2982400d0310ba1412044080301820002c2400081c40b5507084401120444400a2415140c800840044045842c0700407500746c644102c004000481d41051000000d400001d000c55140701001d00241c1c1c40c15807010310580d8600c2503001884120540f20074040c002d044000f8203040070140c000c584d41d650f41e4030001150460035500a0780c000d0649 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 855964001 1250 855962751 855962803
    0x7032703090b0f09061605060106050712090810020915040801150807080a030c031808031305060712140c150a0b061809060d0f0c0603140f13080408 65
    0x4001d40c0802400c0c454502e6042512002d0741410a10900c01490721552000440c0c003400900032091981054004044912a41c0c45140242047d0700c203c070181c510080c0c41d480700c41014401c0e2141d40698440750050701000350f044e034059000c4c0d00055481380c1c0c000050403003503002000e400301a000505030040080b920310091201d510004400740c100100030742001d442441694000140c0005032171741481c201e02a03030303d070b81000c03144140301071010035102e2807441c000144c100002001c0d1002c0941d010740319544c02d507550104800e6210f2003400514a4050001c00507401d4001c2103d00440c40c80380b982c4a2030803025010188c1000345071200060f03035500741d0080c000010064820b6525142e01503030b4031403502c58540300701d0758407406031400288144140c00018045803580c1442030080355000c030307506004000d2403511421138140340c02480006842d0102c0c030f644104a0f00c250501400c0c480800744039513215036118a00e080080303041512410420440003035440000c0000642807450301100900c240780c6 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 855965251 1250 855964001 855964007
    0x31b0e0c030f060306040b04240e1c03090b1501051e04140d021f02010e010e0619060b0301090209150c0616050316121d0318031902040507032703 64
    0x43c1401e8040d500c45c004101c0010405490f0307171307005500000c001400403c2e1902d07400044616122045090b420300103940c000400005a6515440308802c5204402c500f40c04100d08682410001802c6005410040307080390f007480104d5008080107150140c40c19140e24110300d071140c0040b8080808200002d82008035031016101c00780c0022041380d00000000003a0000bd460780d04d4031034408548020b040c2040001130007507000305144842074009000c5001561480c94666104a0700d6800c00c1481404001e04003400d4405c210580d018051901e09503424900ca800017074000030070940e0010422034000008440040180104030380e110010b101601d009114115030840d004902c0c07080c03220034021300c410a40d0703a05504407081c40c00c0c5494100f0720740c2d0902c0d4030060509140c95200002d0404584111032401000808601c0100355008052006000a15507500c00340d881001011805a07440401881c10390807003600942d1900d4003007601e2300d104000d500d5400c43c00c0782480540303401940c50170415030 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 855966501 1250 855965251 855965281
    0x601032001080105210f0d030603050c040902010504150302073014190203090a03081b030717031509100503150121080408030a0201020318060709031b0e0c03 69
    0x1e00c0c0004030b55241c50081460084103030701e02d141240c40805c3c901d031804c004100c05031010b01a41c084860400c07099001800400340c900040d80c40c0c0c05401c4800c3e12609180c02208070381d80c1d06035942031030685003c244460f900d004600100400d5000c01407403012880c0c40c4108101c4001c0b0010f00d0420610014182021010100d0300c00d0030b11041105e51043d0700780e0481607692003101801c00c49464220500d04034294801c0412640e4065190030011007800034102c040c01a9040010340c0745001002c80030940c2d40c0f8061074100030030724556241c80c449a424010082d51300480d502d18110b0202c0810400103400000840c0d140a900c940080c04101700e02d002c010160f4094000c425815036941004420010540d5840039001d0340011410524108080d0390200e400070b0140d00140d944a0070280c04c028081e50040e150420f4030001911000c3e0814408a4400d00581c1d682e15111215403a540c0d444500f1900052070000b11a419100040c8030341c00e01d01c505208102c901c002c20b91300d00d0075030000c0245407 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 855967751 1250 855966501 855966563
    0x150f080601030b090c1b010516020115030503030a3902070b21070513030606031704080c10020f03040801061e0503070918060c05070b2404090c08060103 67
    0x5414043d07080780c00c0c3c407041c00703003608080300282050381c031100d020f184003000c040341110145541c602010000342c00c03084561014003000c0c40e40284144444e0924a22034020a4040907001c0e4108001003078551155501064114031090341c0c01c040c0c10181700c45100880d020350500c0d4241c41042c400d4010040d8144100401307801c045900b43e040001240741016a00005946410043c04130700c00319a22500400a8801510f540c40174802c44c9500c1e407a00c2c002400d030920080b10b8180300a000d0220104191090b40c0c162100c0000070700e498012002000904802c0300030000c254068111b1300b0b40c0030142031000304090a1290000b1501d54075000c840003c21650080320424012029001d1090355008034894045515140740030950701c0c00e2004c00301d4880794881d0001c082c3c0f86082c03407207547c1c50303000005441114001e4050800c10350302d518500fa11199070448904002011100d004520f29117a4000690140102c810b40c2c2280c2c0c90326000b51500c1003c2c1c20a8542020010481c6040805900310755624 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 855969001 1250 855967751 855967757
    0x101d0403170c18030c2d0609010e09060a15030c0905040603170a03060b072a0f1206140c0910090308040303260114040e0a08040e10150f080601 63
    0xd02d01114003450b6401406000b0100185030190340d0042e0350708010141c0b00900080014811320490403d5030180c404100301da20103583d49010688080c0391080035114400410385030300000c0820f1004000e03900c28010300e901d6100036040700100314041c14920081d80701c213164900145a40d14410054400344c1c05a10840c032a508203407003400081c41c469040e9203034115480c00706882c0c0364007000580141883c4d411026020602158010030301500344050b09a2440c034200803a20040b0f0030180405914481c0210103114182c000c2c10002101c610141c1040c0c140a0400040c00d4840c003400740c10300100c1620300007406000814141c100345030001c152000100c490500d01101c40c50741d078900c0c54034011072001909210350384030011110f0a200c8484411048a0301ea07076406580c44010b01c08400840c076104501492030500c1e01c0c403100500140c1002420b410070b0919003000d180081185048038020217014130b61150403c0050a07040b540b07903e428020180c2c503103030308013954448014a070b041c00800c580c0c10 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 855970251 1250 855969001 855969047
    0x6021e0310170f010c17061c0b060301150e011706070807030906020705030a0f0e03030906040b0708090901060e011d100c031809050a1a010f08101d0403 67
    0x521540712014000c6840040320b00c400006400080c900b000b400001000c901d508011060161562203841c1e002d04c400d040e00003c1e11510340e0f0050000d80401441d5440450910300790704400300d44142c3c81d072507000b2401400440d03d04100c42d401a904503d56000300c4074210968010710001c1182c0c961f56200c00500c00040c416031030803480041000402418040c10302d41d950f030300d0109020082d01204c1215810208a0307a6451880c180101244217000a440000310051605171051501004445c1c0ca50700003800d2a041c41c0c18005100700c95881520110340d410004c0201c610140c90b00000d03240241143d8a91400e00b2150000146c0f00c0d8400504c6503030090b84d140c1103c525682c4030528041c008040b482c2840c010f90f01c900d0f05503a80c410544c120968000c0c404c40005000344250490352060040890501c0300702001200555446520310005010601c840e881c13038082481803c1c0c1c680c2c0041d10704815501c403035480140e0582005030b903241c145203016404c100300074560040c0900b56072036540200545 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 855971501 1250 855970251 855970261
    0x1c050708090a0323070b0906010603021821070807090e010b101215082104030b070c050a0606120b0708040b16091a131406090904050a0f06021e03 64
    0x1071a582c034800b000302445a4109280d420045201c520510412004640c994031501c604180a000e64100c4600e80c00d84104030020a04d035201e4002c3d12484416002c5080000040030304100500c60f10203894001d040c0c01c14a480400482004050010034071003010b445400d050241503000c1e58540580705100743c0c181104540d19469800c010b81c95008149403e02d028491100448007903da25145000b840c0424000440c4504003c50009604d4101c410801c40c10944220608403c0c001c501c0041d1049401c40005002e060044a103001541e12a0003507a08003400d035540c00c803c40c0e10580012200c21104514141000040304449030420000d007840c40f400e00e010b03524030054800003010300001c07242c20000e0402e0180281c4007680903040380c13245031503101540e80b40b02e600f54100724806040341c1288000003c1c100340c6405040d090102c00703004a8a000849401e01c1040500038108840328810860500049201449180482c40c0302c6e20000d41d0350314000c44840c2e41110740c1014440102c90800c00d204c = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 855972751 1250 855971501 855971503
    0x602030405100b13020d150303031e11120c040f060e131b03020c07030209181e07060f050d180b0a0c020604021324090501090614011805061c05070809 66
    0xe00c161103140c026aa58611b141000301a00b2002868001418070070804000c042d010b4028007000c2003002e07811452441203400da070003a1000c00038024181d6404020700c0c86a00400001207a0141c07c04900d5132074107a0b20b1507404031103111540118001041d100c07101076a440c191098130102c03c01e04000f0b200600c00c9440d080c00c0c04001c04101d034107240d800a01076031494800d0125100454006210b12034138030304243d41c0111180b000441072070074095203003c0320802c0c144a03201e5001844020050064a05003001540c481d141c010049013401414040b07144180700b103020300f460344c0118459030f043c5040300d80340030040080c02030301800b20241000d240c12407166000540542c0700e50103c840c12900701c62810400d004240002503030383c2c1e06070061030681800c14a40038030021120001010031290f0b80c1d0308001d00c01c0361424041c4032a5031032000d0070b00c0c03441d41c032841c02e03002c1c0030354802c990389035456030340000500c20ba200c83c0b0008880e5610300e1110001c40c1d09031003816030280b0030741425141e920b0700d1000c007 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 855974001 1250 855972751 855972769
    0x14300f01140607031b030e040c1e030e06041106070816060b0307060c0f0c080d0c26030a0c03060b03190605090c04030b072102030423070b09030a0f0602030405100b 72
    0x2410302c00002d2100700a00d07208400c0c0140140c00900200440d05240134002d00d41a400306503012b0f504020701c1c2000026109200e1001d8400300e04015010702e84455950510750042e400309103601140901c40b080101d207114004085a00314080040700c07001c01443c00c441603542454540d40b19070404141040299007050000c54029840708842040600724942903111a12503081448903200310901014903a403c82c001c9000107009101306c20001014400600c03c1c1c2800d0302c1e80320300d010800c6c00802c80c8854181c01880305101c460402061040d10ac0c80c0c1c817812500304488603000380c664804c100c03850030120300c1280e0141070141c5088015103011402e00703116100e01d21000f004102a80001104148680607000040340400c02030444500980c40c044042e40003501d09071203280340040b40d007aa401c91815034962503928800030f072014034034110070800c80b5001050010307014098400d40800082041c904070341428800e000041c2c4a081c10304000c5e227030405210401c224140b410351143c000d5a221a05 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 855975251 1250 855974001 855974027
    0x4090803010605090d0f061415030a0b07020a020405091014090703080906071203050103140c10051305030304031b060906021209040f0504050601030b0714300f0114060703 75
    0x11030f54034400d500100c1c1c041030f203c02006e041018912109010080c140d0020080810310b0303c5010b100703882e0003110482c60044178a030268103500062a21000a1641200c0f40d0300480a00540781c81c040d0b1034010405542c001c0303520100340d80004001400d01601403090f1164100c14402111f010319100f41c00542e109114000540760000c045000c4000e43d803000110364216030f210314049030107120741c2c01c040d029203402e0108480044006208c441c1100002a4040c00100020400c2001300c000e0202500c040c1d02480395041d00b103040d1900403500d41ca003003000704015446400004548062000b00310441ea00b01e4200f0410450564010401c0ca60300081403d100e01144a10303030368030916a000140117154070314215103010b040c4020003042c440c010410504803400780c6020b03406035481920454404500d0900b00ea41c0520500c042c0c42c1e002c0d48240e4010780000070005003280415401004960034030100c0340301805a1604c001403082e1140d41e2103424036680b0039115542001144e96000e00039130b5168407 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 855976501 1250 855975251 855975257
    0x8060301050915010e0a1e0b180c0d0504052806050106020a12032a0203090f01020111071b0308120103110d0206071509150e06011410052110080606040908030106 71
    0x4141b481401e5800407030800003841c2c02d110300000e03140d01c0e00054110302c901c0fa0b10178032590102107003800540b00c04906c038618049000d0314101880110000401000e0005c3e44c42e4400c4401c030b03a40380c3c5100003045c1d4030f204141e94006065a15490540240c2e07505030080d00c00c540100103c000010760040048004000500700420f5090302e0440d0400000e120401c030f41914052003c4410300560044020a1101426200b00b001e40003101d00690907201d4840d000c4030f100c032003000b0fa1008504c0b40749180c9080c5044200c2140d1031513494403154106d800180034021052041c1004200f00000b40c9006002a941030f81c41217451031a50700003507207a02030104007070100440d10051440c680ca090f44110142c0303901000c2c0d401884001e40d5460002c0040d090303880c000307100d03000001c034891111180071000044028859071080c03000a100300c605030818010a000c4d000200c0d0030080700c00c0300c0300c40c0c14403800841001416051400038050315040f00640454081d0f171800703c007500851118000c49041d21403600b = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 855977751 1250 855976501 855976529
    0x9010b0703110d080106021c021b030307050d1106090c032a090106030f241a131401090617071d0d0804060809070815060103060e070806030105091501 66
    0x4181542c8a20800100d0030142c05450000030384a500070b00298107980c1d41341d0840326001d94009001c4440d035101c51998016034801c1c8c4000c05041100c0300743d0704038008081c0076282405003ea449502e00115002940003280540f0222021050200a6640d21640c0d1000402c0044107610100361150b80403241c0b81c9241e07861078440c103018249545854802c041c05000f0950a41e55004003e004240c80e070156400c09081960040074084820080110a44010119904249440e190075001d42c031041d010141c0710802e000c501070000c10f01452174010301035050400740d031400400004207050940e40005c000e1000341440e00b000f00052036801903008401c0e00341408800d10a44010380d0703450754981c20660090807865101c040207411805001118115141c0205503194403034801d8603800140146500c540c020f0b0312038070103a0a0306814035000001030400085072612080100424501250080081035017041417102a0809114075980407442e00054044841413061041040c0783c184034040b0b00e03049134 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 855979001 1250 855977751 855977753
    0x309091116050619090209060402030901182a060c11121002180f06030c0901030609020d05190b1302210117060618060603090a0516090b0f09010b07 65
    0x10844003206194559060704900034a8000d95410044a8800e044690a00d180d01c0310000e0340102c82c08558010406001a074591050000942006150450940d00d50256403000d00d040a00c2c0d250039402044a5082d81818105032802e44d103481207100c5071013003098020018584e000d8034810700e82e84e010501030401d4600600259401c20b41c011a261240942043c040c10002e9035401000d909105c4c810070010407440c2c8040200000384421a1074000d40d0070000510300300b44080061610f600141000140c0741c0d254054002244c0080b400c41c07644503610800d000c810241c00ca00a03020481c0400284401056135000c203080034104600d0740070b19500898004c1580394400c800c00c144415809071448a0341e56004070014081510711441ea0500511001c5070710350900c0c85180d03803031400350101c3c9911903d6020030711605910040103280c0602488105c207002a0061141c80c01c902000c403208502c2606000e6034000315030444003224803480d801c0c102c3c6020b5480e80c0300c1c1d03141102c403d0500e541d220015 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 855980251 1250 855979001 855979031
    0x2803030213050604061808070503151f0303080a1a0a050d0c170601060f020f0c100c05010c0f030b01091802030408071719020d140d140c2203030909 65
    0x107a030001540014041400300b280e503400201080d1499601200404150390b41e024207441d004103009141c1c2640044120f403080c900c0300c0c0c00d060b4100d95030015450300407800314102c411106a0350811400501082c052040c000c10f40d0050000700ba9008402c40c0d82e07604050000354940c43c161180301c2c050a11845440c2c1031007201d45d0f88078014003a41c2110b40401c08a05e0410783c682c0f809010701008166555031410013148002250380c2c0d5051401b005024080d4680c08101000750055410000c12400724480e0002031000e010780c0050140c107803a421b140b000c000d04054152000604014108988000f040080510800030088403035500c1c1401680d9440764201607d180c17140d80006060010151035410542d12090024600014030f07440701c2040810419080362121540310a010010386032040f80208420004010210514001c2000030000c0c0c1d080c1098510003012181c01846078808a80f8182d07282104080030b0b00c821000e460041858110303034010302080440e00800301c00950743c004404010702 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 855981501 1250 855980251 855980287
    0xc02100509070801090807061808180402040504020a090609080a05060a0b120a03090806010f0803070201080c0c1b13110a05030402031e0105040c1e0302150d06061128030302 76
    0x3d040e40007485040b1160500a400e980028812144a0f00c1c03c20780c100024070300c000d0125a80c0d4813400721803901d41500c1c00b4203404614000c030154000e900b004002240c1c1d84500c01061444402d44640100e50b01d8400040c10340b0380140d00100c008d0b00400b44c1040010b902040e101d038041c2810100107110182e450210700d010040e41603031441d600c0f4019002083c1a0049111411941400e040b100705070389843c20b24010006034810081c8660041c850341300150b01540c6615441407602e000c060820b98554103152070b110b00718202500a1000650140030b600300200715510f0444502d405001022034003800720310f98030504800508000700840841c0c2103680a0018030b8040c1c2200e61102208400c035100c1034020f000c251403c8a036514840c500040e6000070214404000e4100c1c00f0750440d8501d19006d11240960168000742040c4081103c401c260400744540009407c25071303500100781240d201602c0c50710542c0b507060300000406c51840106a00740c0140203809540c989000358079840c0031000105062 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 855982751 1250 855981501 855981509
    0x307031101180f140d0f08090c04020409020c1b0901210209040b01091b08070c1505010620030c0606060708271302070b062202031512010c0210050907 66
    0xa1000d24090a00c0b1043c141c44090034042c07004031603901070b110b41e030a45c1c0718540005000400d96464403011103500030b0f2003456000c1105000d43d40781c04038400c0054100d0b449a08041c0311260b01160640f0101420040d038180c0001145100e100442001d00044210304140310740840303806101500d881d05810601e0b02c0d04602c0d07025202000c0c0e42018500008900d009002e64103403289000c0403200c012469501803080101241c036074072025101d0200c1150b2030a0051020349828180c00100502da0030207100b110f0080a41c0d41e21080303c070303440c0c80c0c0d08080548160b0b00c1790121750050001d005143c41c08034076140c20240c100c6031250750703080c0f03441e00258034010208113003002c0c1c23000c0166070300164600c1083c000c1100200e4245040103648110b8900301c0c0958400984083d1407400060240e0801c842c06845090b01030310980801c0c24048440c00c1a1b80c0308a0301c900800300003e06081c0d2070304142545004044016000344481c0c05000e20080d500e40310154000c4116845102080100302c1c2070084001030 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 855984001 1250 855982751 855982781
    0x1505072625030311280207080a080705071e06031d03120906090d120923010207020a090207050a0318050a0b03090d02012d0b060d0b03060c04080307031101 68
    0xc1d95401010201500c000079800f03e400d10b2482e13252520844112508085000350702c41450041001035042400390b240075600b03510541c4400715035000104451a5130900c500003165440c1420301d0014105a22680418600c0e0450030045810188002d140e0003074861900d00019007001007082ca09a024601d84440e032240000115804000c1c20314007034074400d82100c4100c409586802006564541c40707011024009013440d01d503110507601c9504241d014500921000f0100140348039141c1221582da0301d0304e03270aa035001611000b1070910310884c00017482c1c848005c505260741500c6064072141d108000404121990321000150021024968040c2c8009005000c03c0d90b294850f070b03426588140e4404883d849a04030000201d481401949070500c2c440185403250b40041c1600080f549428102107140342e101c40c4542055211070000d003650311501080810680417003805d0609111025201e00081c01040105208a80c000422600c2441c1c2c14601b991503040111b04890050040c2000c202c0340c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 855985251 1250 855984001 855984037
    0x30e0402041517090c1c052415090103060b01090b030c0417070311091305120d0b030610060c020d0c030303090311010b0a06120e06010f15050726 64
    0x211070103030001d02c0e00315041511903194003e1108640607400608a40014880c0d002810402c1d1504100c080303910340c56400c404403460001c1d155a141c1c21b06442e400e120390b5402441100304604030014003a0354012901e0020424030700c183e113012880303103001400007070f01341c42d201d080481d61a4898907211005041d0800c0550726801e10400422250740305100d800c0741901020010100304101080110840c2e40c8214425034903010320b0140194504000e000304090301004081c100420030602801c150680904001030390742505914800444007042c03000c82c080c0e80103c0c100030001d40c001340e611060b22001e00300440554408e100051510001c44c0380205468032000002041540542115032014400d4942c2d0a14090b14a0041d0899204051080d4403009040d0b04100e1280291810290b0380d1120030086400c50391b04440c40d19141003030740450a03440c40ba100400c150681002d03010594103051405924102b51910782c0b5101541c41c1c407010700c0344128802e00071601a5400102d514200105a07601c0b0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 855986501 1250 855985251 855985259
    0x1206030307120302180103060e0f1e100302010f0c11010809070305010212040611071a061c03090801050a060e1f050306010306020705120304020603270a0b150a05100c030e040204 78
    0xc1c0d041740003c142ca0744004004060310790700900501065401100b00903215503610f03001c844900e50003404010107440100d076149110340c00005040d00c100b0424150101c0540b8501c001010f81c04002891010042e181c0b02100014080381000344000c8402d03c0c1030942d80e16640302d9541081a6940003c06662002801042d01408500070611450280c1010001c010404031107007268481c0480007030459070711550400040b4450500d01c2e400120140c00c0d110307401000880a10350751200300095022070150081000807500c2402801e511020342e00c3d092000500e010701c00d0040b03600c05003032005803004000c0c90030308204200c003071035000340b0005044030f1a55a4a052100c001c0d0701201c0c050340c503402501544241180c02c0c5044234015940030300360501d90396620500ca6001080040321020324030110f02c2d0140b88200401040700c602e800b44030254081d042200d415400005c0910301d01d8011010320702e0030003aa5842c03443c01c0340402e407141400c480031043c610381203a01e21803403452a03512510100d030203e = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 855987751 1250 855986501 855986507
    0x1d030a0e04050903091008040602090a0603091b1a070204020f0a0908150f0f15040e010f0f060b04031b09020d091a040b01090c11010c020d1403060105120603030712 72
    0x41010000703640800060f1200c0c0351503501c0344103070412241c21040301644075941c588108025076006011f544010300b007140300c40c001440b41c0c41a5015100181c0c5404441c01802451002640156000090303039030704a02d081c4803207445112200080c02e80100105014041d9207031030b0103d941a21540541650b101403202e80a01041c9150148000500c60041c046400100da54030301401852070001c41040ea40e1040282c000c98200104a90040e20003106644810b86942c065840007640300b10010890652040d005011228030b54965068141020010485458404122016039400134504107a0000841012151040341c3d402644168800507403484482030650000d801d00303103d10f10350405900d02000701c0003d60803ea4019115643d820010003810000b94030a802c24023450420058502c0380c07000340c9084409008000000d038014074045100d60b6071204014059550f81036505040d030500307070300090a50043e80c2d07468005540410105080382e80030030584041541c4045903503041e4200080c02 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 855989001 1250 855987751 855987767
    0x14060405073f0602160c061209170306060c0703080a030608010b090c1305040f09050c03060403051204020409080a091404060b091c1b0501080c03060607061d030a 71
    0xb1012608442e94001c00494903a60208182c000440c0c4040701007074110003002a8288118100c512503400c11482035552814110105a640204150002e580c034101c4080c144c1d0f100b40011806040c5880c1010001408000583d80c5030511148011788035070710000070519522442c81c8241040c4540c1c00004208488031000300340c0f28038681d0b0300380011a540d003001400d80303001c550a01e07030003c0700000080c0c080f225a4041c10f14840c04040b01c021550343c51020038102c1c1d00001d1001e090b641c40d2003904041c40030030806004030aa0a4000340000d00e001e450050660013100c0403440b040d0321707002c04203040d5915500000e11180d0803078503845e0303a4001c01c0d03406081e480c0544100041950083d150062514041c0b20303a80843c1d501404080c03070100361804000010117100c1d080342e91800c0084050b80031500c46070100c411500a8203549405a0800c0c00140c000400280500078800301003080100039120700c0140c0d000158014804500c0d0380c4900c1d000841d05454003c400841d00c400b1038100c111039130100c0d02c = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 855990251 1250 855989001 855989009
    0x9080f03180d050a11030102190503160e060708030604022a101b08090f010629030415020c0a0602031609140108071107080a030503090d0c0b0a02071406040507 70
    0x40c4110700306080107001c0c1d80e00c441c000103012070b00201200c1005c100225068120100020001403030200c1c14154681c3c400000b00c034810010300f011080111440514440c01c41d81c3c0407c0c1403520320000c1400000741148905100141182d4011021544984454040d42c0d050021038110b090250382602d042850111007400522151140342c034000c80350021485103503441c1401e142954501d80d5420f105480c0702201918480040c07040c0d501c44035541d0340a101e10405801e450480b0f810032001c1409140d0245207400d00d040340104c00b0014400007541160300188a548401005600c45c1c0a0900c01c0c1e051090503400504494000810403404190321100510305604c0c540700d0104198483c04000300c8042e05007402d5000c00d240030701141d107060041040e000201e5080741250001b0740c8600f03159007403900740902200070640100a001074044103120580281c0901d141c10000120030f502ca290601d00301500e032070a0550b00003009410300481c00c007505c80b42603180c002c031600e82c00e02d850a0365407000103100e = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 855991501 1250 855990251 855990277
    0x207020415060f03150302091509071107051005070b04082d09010530070e03061603020918040f051c0504060e0112090507051003021201120309080f03 66
    0x12840d2664918052074000381c50140e0f0f034401001d9400d201c181c000707001c1005e010f00525104d03400000103070345010701c691059541e0305101e10704100980501510f120080c2c0040c081c0300e4800b01140982800080a0041310f0003120720348041c42940c1002e649a02c10104080d110640040401050200d80d40050194a20440d070361103a0305214900c055541407040b001d44202c5108110b031914030340c400d0014041c142c00c0100f051001180052524050b000c06101118140d0030003010082510b800010071900100158042c5c01030b072900d2007034160382076000b0303950200340360b408241001c458a40c04241039080c840d03049200128141410500c07510104400115114890404886d00b211110582541c82129079143d2506180c20120280e03290502d0350030b1581000128104800400003500031640310301c0c01600580b42050800e002d00c91000a072100b560103140c0100841c50461505080c0181122200032000d185040185000c403114607459100800c01c2c030070310f8540014460084003c4c054034100c0b01d = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 855992751 1250 855991501 855991511
    0x606013e07061d0d021908060a0c260c130303180501090b030f0606090d080a111f0e01020d06080706080105010914121c110f030c0309061e0d02070204 66
    0x18004403424014014041190f400d080c860400c64284002040358051004000c41e1509081d0300d1249280c0302c05034003441e0765500c8081400500117a510a002c201c9400e460002d08480e0280325452a0403464002005240c0c1400009004119582c050310b607070b0010704c0f032000f00c51992810010100042c03803400074503048440da000a03080d802508d000040358070060445003540c0d10600d501500311001409240c0141c003c0118403550340e600105100c049204038244c2d61558640312000301a60310241084001364000110030035204101d054110041c00011004039681840c410004e005e80038003c280b48e40d01c1c3c02d205002c07414041c003140503425542290380300b00150380d81300e00440c0d550704a0311036902c10b480640c030480d14074107201001000c45010801100e080310202502914a40e440c0981000091841c2c80c28440701e09042c8a200852090a8000d5040c1540c10046a8403441030900082c417500000030100344071141d11101103034644d0a031160588401c02c410681300654811a4204c0c440da01e01 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 855994001 1250 855992751 855992759
    0x10e0d1806021e0f101407110c0d0c0e0109020403121b08030c16081803010b030601060e01121e0c0302210c040e090c12030301080606013e07 62
    0xa2001001101d845034000c0031040450702a440580e5020004000d80d8010485140c120080c10000b0320300d03025903e8000204185408040403860348054000f60411400b52643d00c420b6000044000419508442900da0b05d42ca40c5004040350f5120350000200c0c4d0480c000006070001e00740c1c040d00c212401002c0140c01c200cd00d2204660240190001040c040021111321001caa01c0001441d0b11691510425141c4034902d00c080c52900c034480b208550150002464174203009034080711080c0c0f0070042d402070000940100001e5240c0405004200401034046241111a0b21440b0641035102100404000c2c01e500c10039002c0c1d486481004075484141443e00c031000c414401e10071502c810700c55400003152603c10712011002a1409092140300100c28000860801c0550120602842c00030009020407201642480f014100c851656411038100b8001080305500114032591700002c24600a080e0900d507140b8980c6448042e000d40c20340007080210824a038000180000b11162003004541015030b80d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 855995251 1250 855994001 855994037
    0x510060816051e0313060e161806270b0d080d0b040f061e0b03060307090207210c02030c190b160515010914010b03060105030414010e0d 60
    0x240c501042400d8101229200a8030500240c1a10500d2006440f90300c08000b400698540050798007820b59200c1498032810012544980c3d020741c441f103005804909500f12100c3d44c509503d10844c81c40c00d1042100c0d64035440c960b403140c805095200301c60320041d034881c100080380041880c02106982c0c5010255002482c08040c1191100e5025800514110501101c01e0190016003a030316041a2038402910b15002607015802c0508203501d000300100c3e0085019030a44143c1c2da0000c40002410030600c605505c002c2800c0c403c0d40d0ba8034501503915102c1d0316200100c80021412103a003500704510400c7c0c00c940c0310b106400c0d040c0c000c42c12140c84412203000c00200c000c0b01c008104c01c403841850200a0501c1c1280601040c221031403031001342c41c1954441d581010040200c4805078501003006100582e000d102c0c98200204100000e005581000840c154030b1101406003410b0080100000d03040081c1d0f008281100c0e101d01c40240a03224410045e41c0d99100321400303d60108541040b2402503002d = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 855996501 1250 855995251 855995267
    0x9021903083c0903010608070801150b0408120f0f07120f1815141207120903020d080a09020a03050d0f051e090a080f07090b03060f0609060a18051006 66
    0xc0c04028114019103030540700e607610fa020940e4280c0654079008000b0b11000c061010000822006001143d00b1040c805c09488021064100704102d000500041c043d80703200141006940c4d11400c04070303a5859125000d0b407098080c5400e081d8400314000342c0c40040002080500100039000d4541005240740c0140903a20b80c60080003020b000702c1c02c0302e4100a079000751425543ca02e10740b4205403100c070440d0009403040d5440306070351000c204048028041559403000f03403960038054400e8200811555541c000b52103070211036500d070401160314085003404400f0760101d0b60599005043c2d80801c2e58a1030311680710350003c40c1000c00b0a0b0100c140c100024000c000b00c445100040b1200c0450566070518044150826903089404c6a0781e0040405e10500c1001101e4082491100414005182aa19800350345071131076600d012341c20980502916255a807c0b01740c2025040300e8200703040c0e4503600481e0344c031886540683c07505a44112002d10105031070313000c5801620310451b50b608035501e640c401c0d21300503 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 855997751 1250 855996501 855996577
    0x90305180d11060307110a1a0105191a0c0a060f0b0a050d021215070207051c0515061504030b1008010501030209010b031314060a0c03110d0902190308 66
    0x1c02c203140c01540ca4a050300065501c50007504081d14054001c0e101c8615000035010304880c80c065003104112900030710400030b4010b141c110341421140980c540ba070250181e552003060050320069601d46620b60010b0705a43c0026079650071112181038601303208018014110705822070a141c4600c0407168103103801984142c40d805001c148040c00d20307070300b406000321030f50a480d41030340100848a140ba10b10740320381501031361140c2d00030070000381000c0411013880304686c088424940040300b010300040340811a0f680081c50546030f014507039948008201c4026070250660701080c0b00050110800824901ca1802008480c0744110f4003500c42001ea0700300c030742c00e01000e5417000e070380c0c5e0041000b01c114800a43d40030000300070002e001040d0b980e0b81d01d0200c5006081c500240c100004100580b4143e2003441c15510842c0717014483c1580700c141d4000a48a6464402500d58654036000c056450b8103042c00805885c20303102c180440d070780b420007000703642210900315281d600d2004c0321030040300d14582c0c20303e00b9 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 855999001 1250 855997751 855997763
    0xc030b33010c1514040b090c0f0a060e0a0302120114091603120e03030a03060303120515100201090b1302010f0309022218080c0c0a0315050c0c01090305180d 69
    0x4065070b41c46820321020854039143e42a5141d007100405200304031000c034010382c45111050f00070700f0460900d13410205140d2000c0e002c0d5000c0601c00002e07607030340d00c1110700720744582c00c1580d00c25142030302241100b00903800194101403203d40c1d0710404503055000c2c40f05c075034156101a0140d00c40305140ca41f42c11315591a07640b403080f0440d00b8808680005000381c01e01da007904040c2c980016400210741540c100201a070003007591100f00701b01385a0480c5d25a9007003208030b031003002140707000c80030b41d0740c40b22203000e4a40c064082c203221084101d0003503106104907034000582c00c5040c81c1c01103c0401384444801e041b03000640c10014480310501031b005a480303d5600a052030810f00051f8658085e0076455030795900040c1d10b80007540392407560034960b030908501800490f5030ba0110040084e29102c8040c0b00306010300017000b000c1020411401414a464134a05030204068403030000c00c4400340a082c045034540d510b4031002d2410190001c00030010120b101c20030115000e441c0c0104403403029071140150030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 856000251 1250 855999001 855999017
    0x3060e21090a12050d27060201020a0305182808180f101b0305040e0f040c120206030a0908040e1003061409061603020f180411250c030b3301 62
    0x2406018403003544005c07911b8501e0030344180c00740c8074540c4404115408107005d0b075400101f18a803180d0600501c0c0e03005484002032030400c00d903045026620b04840018010b041c2a00f1030100e0a010180e451700c201030780061106807248110f050300d0a03441c0c000496075102d0070b44d5810250803414a004140034a0181d92a40426003401090740780c5808600841103007048030070000400d00105020740036003c1c0300011100882450145000300550f40160000c3c403140b403402c8480e00060b625041240d03030100719240301140991051501c0c80050140f504502e070340c20002c0041200c0c4d80100604002228003e810900640a100c00d00a01202e000e840c0351000b500400c000a2006942400080e040c10081c903005240031000b00c04410103810401111038601d070f003201c80c04c2c070310f1074940510454070880229051801101d009002600c2e01003519011154072100b00c01d80603c121410000000c58010344510802d207010320489240106031201002200c80b200c1c8110b04001619036000102d03001170b155540 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 856001501 1250 856000251 856000273
    0x5041a010807032c01020c0609120702060708040f030506160318081b060c1c020a020303060d0611070f050f0a08090111100c0203090109061803060e21090a1205 70
    0x6040920000c1c00c4a8103000c0c2405400c0400c4c4400282203204140010380b1030354201502400c18102600c140c025601400180100c0d00c071100480345031369412154035660b96800d103021003542c001c039844014540f410003000006e00c00301013095440f513022001903001020300280240c0881d03e0034026441300c0c2c00c0b101c202d00001a460750050000303010300e0320031165907603003000c0d010300d0142c04981440c041c050100b8138120048814503c90444081d00c10294105111070784020350f6400010b11040c450103c030501c560910020354041c2d50003007030101140365603100c41d043c400d451014a00d003c44a41c800c2c04884058450003081c0001e0065010001516017000917004581080414940c510309004040c50102d241c1c2552042688110320354024540798061a000544404000c1d4802c000b808404200001180409400e44003603036805400040c02031140c24005181c200ca0086050038012003034500c80402c800700c4040d01013150304507000d1104607190040526410090b810041c0036900c42e0070540 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 856002751 1250 856001501 856001507
    0x6061008090c1018080d02120c03090f01051e1b0c03060106051b0a29310b040309080601060c151d0a06150609270609060306050105041a010807 63
    0x20f80c10442032030140401441c041030600000e5195000c04810b51140d041048226014002203145400b600a201d003009004c00c602a11784c411030117000c0c444c0c502000b01e0121030703000e8010380b8480e0503c04070350504036004500c40c50305540305d12000e441a60405030452080c040015000c00301080203806000140d02e000710070380b5280c0210841103080030451881c000708401c1044400c00c0c3c64001e0b07071100380f0f000260f005011401406445220314515800802c0582003440c2100000d100103a240034080811041d100152090310a2004241c01281004d12040c9507101c691201941c00200550311700e03990b200c03130948212030240d60042c003003549400a85c071040042c0d400030000034484040c070018050b84074403542c10303e8001c0400300c4030b080c1d9401d00c5c4842e00e403803500101e0141c41142807540b42c0c00c2c14801064184c000402034042001c110580c00c185165540d00410300402d4499003d00456850703180c140043c200902400380a2481c00d8400441503120801043e04040c068442d10481e4490074422 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 856004001 1250 856002751 856002769
    0x418140c131a2b031d010c0308041e080301170f011a130f06170c0906010519090b0a020d030e0a1a040f1704050f0a030503270a030506061008090c 64
    0x3c2c0454036140305608000c520b2031081c1000d080c480c2d640c0d822000d0003211440724092a0901080c104200c8000e01e4000070b420042054100d5008006041403440440303862000783c0301d0b00c2d03004240010210001400600d600820b81c120751a140c107484030207041030030032422105611107218000d8020b01c02c49101c0d04103e903404e02120309003071021880122048009080e540c1d1640320002c00988603010250740101400700352890001119031200718107100000800318000c407826645e001210483c07540302c042c040c0b42d822000780341c0425681d40f144006980a91034010144000001c42d00704101d200d56080b010030b0035010164085d111a00c1c028a01081c0e07003070058020310485004000790740740000b140101e402240e0b14004428010343d240e06040602506007140704240e03000748520601480091008019581500c0400385c0b00007201089001e4a02c0580da400c40194201040740e2020052101c00310391b6030b12030361040d41d41e04500e2a0ba001e0071038100344100d807000c09641010070307810541d02d401044 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 856005251 1250 856004001 856004029
    0xe04051603270302030a110303090601090f140405061803090d03050a09180510060201092d020d2108010f030201030f020706021909060e090103020418140c131a 70
    0x516800c40050000b0b8038103400341654268003680c07000c00da101c0265806002c040c0084c40d841c0c050750031401c0c10110a55a9030040c0244201240ca0701c0e4142c01c55420359100ca201000d1029103095a4140303800e086031910780079140c90301e01e04542880503030f40c614008101c55034000c014012401c0c40d00350b0b4a04031400d8000b181428208000c1020016041c4860b84005081c18030802000505003410121400c01d004254014019039051100c00d03404120384040c0d8000c030422010205884058031428140303c03240d000d100940c05508052600140044500107181203c1e50521b20f004d444d00c0d014007919024401d00c104002072400010074001548650010004800a0040903040444a03a80c1406982021009200b14603a0710340001c2103a40c030000c400300030000e9041c142003190005001c5500c1401c1400003034025910350000c0040c03a081c0c0303120070b03140540144166850740004031340f0baa200d20042249900c110300c3c10b000300d4005402e5105103046402d0010041c1c01c0b000361403040c01250808504 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 856006501 1250 856005251 856005281
    0x207030b06100c05030c01060f0e090307031134050405190c0210110702090601090b0403111309050d11030a0807030b0a0b13030302070b03060a0b071e0b070e04051603 73
    0x81002e00065040000e1b040d172151450000c0384903801c0040b01c521503107255100d84043c603032240600990203000300881d0f001541514000e000000c101264a180103254003059407035a051340307445102d055030140144119048807000d03800c20b680c3c500401c810390340203803a5940900b100c00201c0c0310a115550002c6807840c1940152001c58080108220445141500101d9011400600c0b441103240480146600940c00d00740106014107101c01480c4502860000528170941d81515140c540d840c020545940c12803408140080d02203403030301300e4540c083c4000c50b41c045444c1945954800c90040265004d815495a9000150b0303250301c4218050400b143e80305404c040040c4000c15010482002000da00b0894005106d1aa00d10320307000785040099804002020000c0c020720050b641c8544680381152407594180e600d070102d80c14021101030510210044040540c94070000f0400b8030300000e803240c203a6403280b811001e1501d05100541e4411140c50b044038510101d82d0701d2190095003c40c14410f40030f8 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 856007751 1250 856006501 856006517
    0x5061609120b0106020f010510090f0609060603020702091e070f030b130501080d03050903040e102c010801090f02150c0703050f01150605030610030b041503030305070207030b0610 79
    0x24a88508004186000d5440d80040c42c014440e0755010040008100007100c02041285001d0012400401d414040d44241940703418141c030170f682c81604590050199018100070060791090050020b501102c404c9029508450001c2c0d90204e4a03002007a07040b001e4010020b07165240d000031503a44500714200400c0c59503401c0c075002e29840d004151102c1d400d08d45400261075040050440c5801d40170118442094200300400c560910088141c030121101e04d1212603ea46904102040011a40e0800c018106c10204124962004c280d11200401c00c01c900080e182e90b00c550b5000e00303841d05210003400d0000404210b200605241500a20640680c840a030604500c3e1100505120580e4410384260344018008152503900784903001d00b548401051004c1203140443c0503006010040c409841240c1010f20b401030310b8081e8004040440d0000d104000c0d40800704802d0461100345c0c042900001d285c0800903031420300016040d000c1d40d800280d0b01034255a10000c0100741c100d032603a1081001690 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 856009001 1250 856007751 856007759
    0x50f040b030703050916061e0207080f010b1f1e021c02060405060619030308150a0b071b1d150406060903030f0f08070e030c15041e0305061609 63
    0xd04050340c003507840e0b81c0d004546800c045240d585400000c40a0740301c80c0b00c05010402400b40c05c05210483d0005c845207150710440040003d0303003060000e40c04095a400344818010b603100d010340c4900040a03084400c1045404058030101c0b900b904444840c0105512400c04010760104a00540c402e0404e0f204552062980900d00321003002450610405a801001400204034050020980c000c2d004e81d00c6885c5c100b0f030324040001c414180c0c400641400324103030100714514880d0541240380c0102501825103181ea5259516007903102440030349900810f410b145451040110a0300c08603401e0b9001e240c4000c5030100b546419001c003400c000303118640c10020006075152030141354001c0410b502c1d00e0504074910708000d403854800c4800d0004109000b2041d802042c0c0100130346810400c10309d0725080e03424100b80442e00d040103200074140d1240740c05021485c609000d200410513a808030100c00010000040045180c501a004c0148150040d41c0040d469100a8414100c8400a882c1c00d01c8811b90b5 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 856010251 1250 856009001 856009019
    0x90216020312070c05040207030503040308130c180507030e1b0301090c0806091e0d0804050c040f0605040b01050c0a06180609030e09180703110103021312140a0b07050f04 75
    0x280741c00520b0700d4001c1041018801012443d60040000342c40540c944291950000c0091000820080501c4040300c041810b02104e007460356062036001e0040c50303005450310300702c41001c10f14100c200d00f02070030540064031030b074483c1c001c14070b0141c0d08000030000c0008102c68000010560140706401d503680300c03000c00100d103846070102d009080b60400b070107031403c0c80322450342000c910a2008010500800c00891442c0d800034068920600d545095646a2201d203401c60070700c60070540c51540720781000c503100c52005050f0f0105044490440e410005d02141a0064626026450034098650010f555480104003070350000d1507184103004480107680070f10350741d002c11122000f1040d00050f1000d55204203900303081d200c05811600302d00c500c14070000010000d95442c140341c04001c18045080380003080e90b074002d405440d01a031800e6508a0391a40b178400f0034260681402c0300341c2d0922100b03140243c101102181c1d00c84410381040742043c5503943d0a400b07442c45c0d406144843e2102604010028600300 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 856011501 1250 856010251 856010263
    0x1151802090415170712080f1b28030c0b0703020403050304080106050411032a0d0614130e1509210a080115050403020910120b180d090902160203 64
    0x644103e22043c081c101400d04182d560361020030303040c40c1c0c455102802096281c03011b140c0c00c40c0e07100740c0c0d00e0f40c1c845464075028100c0c020416414901120b031552030900c91404542940060fa0b000c0c4096010150b4854040213003480f040b0117404034540c13000b04d40100c1c3c080f083e80342d80035140303007805482c00d60381c3c0da14035203558400d0f07000c041c460b5500c050900840c5490701540c95030f11a1701c179071f00b82141841609801400301c542c150742e140515501d01d2a040c40d42110903161a115106410800d590707a54070310f0410102d080b001c180c45581540d0050b030f11251141f083d05844c3c410311004065001124441c10b000d5500500101c846100e104e00303010034580d403041c0610b600c40b5114042d0303886016a510107030940c081a0404c2c0445a07000407018001c547c4102600c0840750100c80b560400e885504145c0b99080442c0c00c107420510100c2c88100c20700c5041003055010700f80c5290740050200c410178000c1d80314002450ba010020f40b0031102044060340070303000380c44c1e00040115803043c0000305900081c9420 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 856012751 1250 856011501 856011521
    0xe0c060c0d08161202030402030106030605010b13050d0804030b15040606090e091b130b06070507031e0210080702160602010b12070e011e0305150a0e011518020904 72
    0x540100900707541d080e441442d4581041c2e608441c00162200d440c00a41214062400c0c6100683e000c000602599004d40080e0300a50308803c0800481d40c684040340c03841d9204000380d95001d1031032680014207041441c12002d00320740049000b800d05085a032180303c0e940c000380036429503814021144030076a51301c1c0f0400d002403900d5101d0400c0542350009400f0820001004e044d071070742001c0c00022013241701c0c4030340300100c030300c11100d00040c04104e107018070040c4920545150481b902103800d07810843c00040090a4a010b070030b02c20302d4440e07451400c2d0918900070070002e402071112041c000c020b500500d0842c0c0c0200060064900000d0b21000130601c03081944e01c0140103030f440e9820521a81091001d01e44401c40d01c0c0040c0070060f0801c4d10390b8113040c0d01031092114400c04076401249011400d41e4100155500c54141c50b0000080210013140f44401d8403110a905d25140d400041c0110500c00d070742c0340c0389004812540c124508100c054404808018211803e5020040981250f40310300c00c001080d = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 856014001 1250 856012751 856012753
    0x9010e27060402100e130e071208040e06060301030f02100509030a06050f1f12170d060f0b030f070f0908010c0c0b070e090a090f08070f120e01050d0e0c060c 69
    0xb4941401041044680e00302140c0c1444100700c280d08031921014840c45042e408540080395121010580030315200306a440040810b805002600402410b2001442100d0400e15040e055071107500400c1130070700c001e1200a28900d00c2d0142100141014201c0500c078280d241001c900f840c4019001c030341010321849045402c01d0b034513010810f81c01c3c0c1c94110716070000c3c100302070404d001da281d417010b5a00a83d103010b9609058a400707029070402c02d9810030314800c60072403e403460b20781ea51616850080c1030f107405003070f0440d2021507012070203c07150026640301e0714280b68074088035120b8a200313aa00d428402c270b1940401c0004900417417000800d01514062406560741c00c0d100b400b160500391841c80014048104200420b98416450360316040125080850fa03031000583c503420349800d40c802c59940a0080c0007140c081104801e000c1414002c64196000380d11548580d4000c050480f114074181010074007148003031000e030103400d26650250740707600550400c07907502c0300d80e02c00040c01a0b00508900451 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 856015251 1250 856014001 856014013
    0x1f030507020c0a030f1401021603181a0408101a040209040f020a020a0312050f160306030b1023010807030e0708030301080c1e0109030f210f140909010e27 68
    0x8112010201706c5140c1e2214008608100c903e2002c402001684840641000403415010b0f00c01000320b500c4800a1508000b19009818800120f46d116001032244404a00034100c0c0e0804150050080c0060480c2c25440d000c44182c107241004000c0d00013144058009a43d600302e076000c00c2e01440101100d10b9246c00800c0b04440c41d10700140706071130040e5000710060a081c00c0c040c031a201b0b8115645c0080031040300610301c1c1c8010030100c0007002c17071384e00180ca51480314061004107107405000205841241c40111108120b114048100502c010811400a84c02400044215109610003400c121980080e11b120aa07214112403850b0020303004107410f904a560142c40b03070325010314803c10340c0550003981003040b80400d001070550b485600c000b40c594511000c2e450300704000000c00c983c03114044146c6110f0383e9090500140303045200c0c02d000022a080708010504210900141c4d2001038008085030341507800c4c030b481c66102c01c101408112140400400f40d401d0b00c40c0050780c01c3c603a05184402424 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 856016501 1250 856015251 856015253
    0x30a03050903070b041d040302031204200301090b0615040302031b01090e04260d0c080a06061713061103070c0215030c0d090c0f06080f061f030507020c0a030f 70
    0x1041070401c0d404803044032800c01c010044010300240f06c00004483c074803030048640e503a040c26400c0d440b40c100003034a2110240d040104021208415103c0f04403051101c1524a12103014182260b10903c809401100c02e1400160035141111004690801d44840b40d42455620750210349404100e0070100581c4281c80000002540c0c000c44440007044208900c010321700341a1141c01a0708401a41c03802580070210302090400b00440840b608807143c003008010710003114000500e440c00c10b484143c1c0f0141072010009907580f264460824004003462030b0262511401c0ca5120300046841c81100c4607910f600e010300441035040041d5108a455440341408418184100081908188906112980140309101c03400300c0e00ba058036503041c0c015400158030281c50406505103c881e900c00e04c20100c038100003090703840d1701003041d5001d2542520b940005486500130010341e414680704e00b40b084081c5d1a2240700451094000c540c000100340190341c3c0e00083e4101240c198429500141d580d80d1507501500 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 856017751 1250 856016501 856016503
    0xd0c090e010b0310090b0103120903020d061d0304050a12050a05010519060e07052d030a0b01090e0702190c05060f0a0f0201141602010b0d05010507090b0906040e0a0b030a03050903 79
    0x219131650042802c011000d40e6503161050300c0c006000c0988110040c0e14425140790080302020055a00207126122050003468114064240c011081e0304403600b540510941440c00010350f410707900018980d1144a04162503142c5400e100207055465218120350344002c0b501c02c2c46035500502e00e07840c403860072020020b1024140c4850b81d10101c82e075462a410046000e51000c15103800e001180c0780445801e102054120b03c580140c0e0014040040000a100300e50705643e020f4581c610b82a200c0305e490555445154452150444085e00582c2203a202e001c8603800ca0303220207823828402c0450400386901c03071000c03803d2504101101e011a11000900222841e0083c607910018102c0340300a1004140740c4207541082d03c800703844c0074100b0302d00d644c80b0300b100b074001e4200a126000161500315881898204207010744403e803540004100d1407440810102c1c1081c00f281e041420241c40e031841d05140c03410441168034000d02c0c140d03a087c1e03903020000c620740d42030001c1d15019000740d84076500c51060314109 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 856019001 1250 856017751 856017763
    0x60204060806121c05091305090c0f0303040f0e06031612062702100c060510141512070c0206070f0b0c0403020f040b0123041514090d0c090e010b03 65
    0x462210380c445600403600a0b0000c02c42101341255103840c9480c1c0100201141c0c0b00180301181e80c10a81c00d010402594580000d01403000440c200c500f21800d10000c824075450303118a001e0034102c0c0d0a034001c14402034421404454101e18080d0460707891461107101000201416044601208071003200c95044c46124098003034526490316843c00c25000252080c404072000032802400f030184044448001c2e40210030400c001c030340000003401640360030380901c003031500c0e18010743c0141b0513280c00840f15030034040c140c0005d9500c0b1015952808909540f207050302c2e10010070707490802203042401d03030050b2500406404824425000001106e107c0d20f0016400b9a0041000040b800180810405039448443e56214448250b50009031000c5840040320740f010b058202e0032075003404011207204d88010400802c201c070f08030f80301c0d0203c20300c10380b80490302590020410384190381c0900c840a040d141c91644148400d01c200f06c400d04075035455406406030b03034115041c100f6a95407086000c2140c03d0500c90 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 856020251 1250 856019001 856019029
    0x2040c140a0807261504020d02180a0602060c0706050c0f0406030b090a0b0609090a06050a0308040303020606010201020304020a0b2d09041b080408030a1e050910050c04060e010c060204060806 84
    0xd9904442c4100e05111090b9006110796020545d0240c1d040321a1641e5049425280109800f5940c0706468010440b5035414801402c1c022528002c00148051005c101c682c003803000420002d141c540681c8659001d4030020f404a1692141040640920a10380d0001c100411140d1804211909610100b000390302000b028400c10034100b4800c07640380e0343c90004071084404122164450b41c1c40d5500c0b404014421604400d800c1124050007005112001e030240046a00c01e500300d400076503c600049085c1d00046d203009400140d8420240220744421340a80501e451700388903610b0000c0f0070b544000743c0030f00382e10110211060000300091142130a001343d00b40342c042d460202c3c1c1c404c001ca000040007a00d000708040c1c040d140220100b000020940c12600138014510829a0381401d51441d8500516040e201d5540c20320808002c118000314a0144500c06c0c529945414149842c2103015903040c00750000302810004003c0c0c6820010355144060070180031076658010161400c001031110f05004140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 856021501 1250 856020251 856020287
    0x300309051e01050f0a1115040c0f08190809030a14010b0102010e0303060103090c0e01030c0e0f1603021c0e010c0912050706031a1f0e04090f02040c140a0807 69
    0x300240c1d5607600801214007071000394602da641c0303108440c0f00301c8103062101440980e5000724000914008682590a4010340c0507200303c5054aa80d00304078148515107101e60400c580003500010f041e2032410800b112801d00949800d0b240600b00380003e070030315000790811240381c3c200360713101a81c1c01d409109202501c00d00780001c21079a101004090303543e020060109040648072007247d800c0058480c0b00c0d0001700400c002411265031a0326007149400d60310b00071144c01d24060400200c0e01004c80d510701e4060780c00c0c0d4100005900f240c41c4102c0103507201c0c1e25050002c1418440e400d40c00409032041c081509501000015000b1880d840204040c00301e034070500d407072011201400e000c2074010903401c2c02c1754698103000a401a5551149580650307900d0b030309a0010703006070301d501c0807002da029000c1c91489a40d501004403e0a404020494182500c0948503050108402005080503400002158121f0809140b409032002d021030f0140e00401180001130002d005000b005608026201c4101c01c8100c = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 856022751 1250 856021501 856021549
    0x90106140a1a07020a1802030906100b03061504050a090614150f0705071d040302060c040b120603070305010c21060b030f0a0f0c2604030930030905 65
    0x720030122100a0019160b0414100140000031035a5144050340108404d1130341040040c1e651034050020b40044030300002a0244c07400042c0010b403074207826025a0340c1e01c0d0200303007991189400d01c075001d504001000340b540300800c00400d142c3d4444071075100404c0503010120794541040c00400848028102190003510300f0401c04506102c0f800a6034255103994a001e40c9038103da080c003c7c034020507603000864000004001420241d00010224440e0f0b01940032100c1c16143c2c01c026512a10071881040c0841c07000744800007502e00d0140740c45400035030080498078610f44945035942101c0704051140c000c00c0c50803c000701501c100074101c0764414098501007203081d00e0100071000300d2200a200d03000c680c12900005506070780c640d10070204240d0010307040000c82082c070700c050408040e00b44800c107494041b8281c0342c244180c00e41994811a4540c1c0e0300c449444c80c005d01030452151001201d040382d00d9007002051684401044d03819114060b58800300c086150500f8403050303440050591007070140074 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 856024001 1250 856022751 856022759
    0x1214010b0109290703090914010302091909290108031e07020402120f1005120a031b060c08060a090e0706140d020309010509010b030609070626090106140a 68
    0x342e1607408032100e803400400f0301450382d0b410002440c0284034980c4494008a03005050543c060341c54030542d4160441080300200011400300c400c0c1e401d21000b0741c00500300000a10b10350303c0c008010301700a8817100124943c08259142c45002c030b0412001c513040f0383c0448003900c1c04680708051a004040980c065071a00d0102442c0355215160b407150030b02d101c0c50010b00030045494030f0781143c12001c202c804290303250500d590303401401c407015101d00b10201060b0501160518003140d1411504050800500c0101000d80e07003516800103c0500308070a0140d087c0704000b0039082e004070030200d09075035074060542c07501404015141d4155001a0300e428540403d00b283c8074000650502a03172082d003400d11460500c095a4192441100c01000a850001c03081c006580c205400650081c405c0c00000c1c0003008d107103c2856981d060440d00140e4603031249500b04003550003104000703c00307000005145d00d690351326070b1522648802514080c00c1a0364a6030100040200440d1808118004a5090700c180b4a4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 856025251 1250 856024001 856024007
    0x4050604020d110409050d030c1b0f02010c1703040b0c0a050d0f1104090902100c170c0a02042f030118021c0603050a030e03030403020108150406050a1214010b01 71
    0x100900c000d0281019101c1c5809008904640080400b8010700520224046242254075030750300c130072030354040f0f810200c18401040c0076082901da450002124845814450b0716031034280c0405d10026810b00c0842ca12920201d0f00700ca80c0783c4a4007402145443d942d060a01d0610034038100205490811403042c409011030f0359020041341c0700718950000215200c2ca000c12094000c0c00121211104a04001400581d0303500d603410840c00305008860318a50b107800348a058801c41d02505009205048440d44040c0015001002e012042c00c0b0706c00300d0307135000e1166000c03a085880c11072903031120421085a0b040040035103041441d1340503581300781904551418070095200c000051440320069008510102c280c0000325034035214800d1584d050100c40c0d600d040041c0c131894041001d800203103503411290044d041c00001c4a00b100d03810707540c2c03401c03642d100d03030700c50180e0290380d16480d500030340302c0e10000380c0c07551607a8490f4060800004445800100d61805009404020368800d00590600d1400034441c0e030 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 856026501 1250 856025251 856025263
    0x1140702270405060c0a21150602011a1e060a0207120c03150c0f030b0111011119050f04050405150d0803011401090f0b03100e0a0203010302100305040507030327030b0402180405 78
    0x8602c20842d44085c7d0a0900c040035080c040c0003020005002100000c0043d0305400c50280c044000b25038020000c0c000c0d0900c20440c610710504010709007507612080503410683c009203000210703407042d03598194a5002d840c04112804005440200d01c507001803040c8007001580c21400d80110108000103011054080e00000c0640c0100003890b540b803000740b41c0d6034065012100c0c01c07101640204004200400311020a410030100002c0c011800c4c040341c04042d00038000c6409101e440c0640c40d050501d407004010141c40300501b609002000176509040303c2e154191440600d6106801b0345413a5030400c2242c030884030481103128100007109604015000500c3c1ca44c100369000d108289650b07a50300d11030b52205038a1903208191035a007000c10003c422003264080d5060760701c01c841c0102c1c510b821307104c200c00781c45003950b010b803460f0007910003000000e0044407503500c0003030380c118100045c20601800c0c2010a00c42d5100b50f980348180d200300011860000c450650284c000c0c001081c030390a00c0d1302d80300d035500d03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 856027751 1250 856026501 856026527
    0x41a04060902013c050405030f0102181207181e060e060a0b03042006030a0b0a0902030f0f06012601030b06030109051f060509041109090c01140702270405060c0a 71
    0xe00d03004041c03c118418001c46000d0a07001d03048508102e0b036008030900075804450181d88cc50040c8201036080c3ca0850940c0d03502992010040c07907858184240743c40c888031104002c0d00015034843c0c80c40710680712045040030004400704009101c0b0700c1e000ca40f004801000704410b20505040406203c02d00302c2c8410350703070000c0d080311803070302d03081c03d1071402122540500180c030381c1c0000e010042203605d41c42038005620043c42a40d400b1140d0380d075444400180d01058501c0950020a400040c01192410001e16404201494a9001051f006c02110030940c0b520f040c0d0b01492842030b0040c410b101c411640950444401d0b0002c205100c001c0d01c44546a1007140709a105d6502c44081d00300c0c0c0c44c2d8140cac202c0c80c05000c004000b80e1a5081c5450300005400701d04c91040e00405010340080c0000720041104000f40c0320685070301000304613901e040e1900e6803020740c041303a011480111207542c05040902c24021140c3c0f400410380c1c1400c1c2030504c00e181070b50080814036181d104001501c1c1241d8841c13001d01141d = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 856029001 1250 856027751 856027847
    0x614011e0b0d0b120703150515190504021c050c04080304060c060915050f070e09010b09010c060c030209120d12020309100e16080c06030609041a0406090201 69
    0x80d0034000a402c010f000b0703e8149690155020007522610038000c80c4803c2160300c211008549403266061800a94134110f60308048540700805121a03400c0c2401c088a51000e855110000c840d280d000050482c1c00000d80c0401440c900c0200000d0040c99104850304500545420b1707040c54900503d49039284500c0c0900801c1100400c52401080000e8100d0b41c5000c3d4040200b010340b011500b4000000c0104a07030403288101d0400200e110507001c1c52046440500140c900710b01a130a004400c0072a51100c00854100124a006d0b000407500364820f2245a545594002d079580504504000080c1c005180c00d80040c0c00c2072840d901e65a41195403910810703480035015031a03980d025440c1d4102461a10031048a5080416044140300f010944031155100c12003140305250b210300401d607885000300c031001e030020030800c08680326103080c004a6034406e100b01c9180f942100f401001c00c0304a6015681141c10300c2d2600c020004640c4c104060051246820901d0600c038041c0d11a802c0206000e00340e10411 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 856030251 1250 856029001 856029007
    0x9060f090510032c0a02010f0e090406022a06010305070510120902010309020301020705070501090b12060d020307030f0f03020d0305071b2108010911040305030708091c0614011e0b 79
    0x85590280907411112040308040c0136440060074294496006035400c0340000c2102c1c1110b40e41c01c0c000d02103000d5060780600a03125aa6031941c03103c2c000d40c412070003825807403240160300782030319840c0d4611b542003100003002c0c0c00c06524515040f4a01010350300464861000700072540c140755401040c00c000500b5441c00461241014001a8001c060207200030b501540005030810500500150b080c0440b01e0030303614075039101ea9440c4511000d0041006502c111407191011442c54580303c3d84031045580020b041e54007455407a07803803510071007007403000721142502d0306c1101c020f1507018091008a4101c2d41000e102a28001c84020321340589144079103d411414015407080c0842d4400420204003281044182004189400f0302840b41c248202c140207030900048590340110070081c0c404480d03000300158241450b0b652040340940052a0b680e404c501c208005812100440c03910b945224003031b80000404000343e0004058201050304102c01e002e2951035810301d5100c510502c541100d15680196072 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 856031501 1250 856030251 856030271
    0x4031103120f162f130c050a030f0605100801030605160806091b0a02010b040b03070302030c01080a0e06070e0306070207060f03111b0708062d06030f01090309060f09051003 76
    0x410301c80e00142d400810f0110015048102d00c6915000c0804c04075412280705c41480d14841c01e0728501c0c8424400074038140b02c0c070140c0c1c500940041140e80c007003c0c000304010340c464010400c0c581d22240e06200040b940c100400a2000d0f9114241c0c00020703480d410039100d26403000c0038002ca00082e11603401941540300142076012420000050040d0300040c06a6a40c2088e500078041e28000c80c485104529081507021645800034115080b654083c005c4d1142d003070404010740b01c01800030714a045081e1140d2840046040600044e881005561694182a440c10051600d4078400410303040545d484000e05000180c2c02c1504038150200074035000ca05d420002400c0741c164011400c5028615015035482003519002089a400f510040c00880d030342c2ea41c40d10400c03e12064400e280c0101405198106041f2446181329107074030106c041c3c21540d41c0040012003a00310780c0d0216055000403c51030051106a5010302041c2d0f00409518042c00a07905240c00070340096503911002c1d040c0b44e5102d034815 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 856032751 1250 856031501 856031513
    0x601080618040c080705040e06060609010c05060901021314130e0106030501050103081b030f030c091f120507030e0309040507030b030a120e0406142404031103120f16 73
    0x56000c070203881d03040900341403a011615002038002d0001a00505a011803981170511540c100300d400c0078003c0140d525072105004496210003949410001e04040c040007049040040c140075013480d200069079807030151102c00c2e401360581c006030a00b210600124925a0f100d000007000c1e81e8031402c0020781d8501c0245690700500466000602039402e00300004180407014000d04410170400320188803c0d151003022503102d21440c545481c6495080c00840d030001c0402c0c0c040c0018150183c01050440700000000d0719103004103015000055040440343c070021198000c440c0c025000707003802d02c8400d041c40c0c000e03922030007403140d80b6000302d030f44800055401c0c2c070981001c0303152070300034082c0d0b01408020b050030752410b28416501c80c0071540110044207503040074070031281103501544007041105d4096003040851a40503c4045000164030010711080d89101c0c0104011441400c0100402207982c05160510400c000721684130101440b0450948444070110758890b08028a0000024001e107850 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 856034001 1250 856032751 856032769
    0x90112110c010911040b0303090109030f02060f18010e1903060504060b0a120b010e01030803180f0d03140109020307091e09140106081b0a05092202030601141206010806 74
    0x403a55608040c600c40900000c00c040c401c5055094130181b0904050801340b642ea07108411f4038500254101c0001c10204441040000c403e038802402c01d40b41031100103654040d504041d04034040301403914400380b40743d03812031202c00700c400c0c041c0c0f40407005442c1005220441c0040c1e200280055840310005802c012259008051001d0024140c8452a8503200001030540701d4000c1203800880180000c20001c0c40880b071030303040380c0c1c0c081c1170640395a490132031280700c0341300d5007401034540d22030300c00080c0703801d0303024004d1b40014003072a40c00195445c1d41002107801c600d4180e228000c0d8030310400500c00b41310347c0000a003084d981c00b0204114021054801100900590761007408071038030305120120144105005541211450b41e1441c5040c1ca8804c104565404280611035510808021581c241c6004401030000d0000c014007030f42e200301610702041c56000002d06918440da03400070070043c0540e00014003005014541001c031f8103040b9007442542d10804060942d40c1400300f85800942c0740d41e01d078486 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 856035251 1250 856034001 856034017
    0x10020c04091113060b1e0705060c3403030c0c0506190b041a09060d081209070e19051b190e010e01020a14070b2106010509011211 57
    0xc00c100000c000c2c245581d030759184050300d9100381c880940091907042c50f80035480030f4030303140c410051400280a03511030301c003592122003100344070081c0410b0780801c0701400424491600c91030003c0d42e2303400360b00517101820a683d20a51340150a9a4188072183c030750000c06003003e9040c01c0c0000c442401c00404e44611101e460014401d202c3d180c20090800d1407a8061f02991940103000d0242000c40c1c0e0401082d50348010301d01c0d10740944655080c800e03107040005580c0128000e8a4501d8051090302d07000c01070382c40b501041d9004480c0d003090000c44601004030700b0003400c005644451034280f076110700031840321a000c1c0e29140c944810104504111300185606a111440702640c0d4560810300c0100c00b4201c1800d01a001c280315054200681d40504440941c8000503800b400382003226541300011105091050352213486242004114441c038100107000000514440006249501c00c0403c44410010602c070b0410a00740860181717070360404156440504500c42c0404c1f01019400800304500842c40307 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 856036501 1250 856035251 856035259
    0x1e0314010e3d0b040b0a060c060b040615050c0c03010e0a0602130e0106121b0512130204020a0504150219080c0a0816020a0e04021c14010c0306060f0f020c10020c 71
    0x240b5401c0c0c603402051000029502801110035800400c60b6400e114492140400da032404070b03c000842641c000351806000910028050742c0340c56144c02d4481ca42c12645000c5000020010408201009500c001581c114001d11800d50341c502080e8035100b00c00c4009044503008a0f90050b40e4046205180140c519188040e1056039a90001010001c1401895029501c2d082c016604003d0104642490041a0f1039013841c0000c051158159184020079480040c4054107841005980e1380c00207050320036059858a84980c2083c030b0074014403491005c410155030011520400700d404680b0345014480e00005425200d01e00e9012540c100060402c0c0140000b074002042e50104c0743d00900c00007428001e0b030b20768105030f85031400c0ca903483e402070720701a601004000d0011810304842c0200417001d4030070b81c81810080d0b01d5040d1103094405074800d8402194684605000d125400054524001d520345050124681038410103900c85a00064450098840d80c1c41171800714000c01c050034000034068 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 856037751 1250 856036501 856036603
    0x90203060604031b030227180c1003060801050705031803070f0f291e0907031214070605041a04020901030308070c1407050301150803030a0507091e0314010e 69
    0xc46110107a00701102000d1551f1001c0010890f03c40b054040e4051030243c0d01c000304800c1020700e042103000d40c07510f0554002c01d5242d490121b0300038028001c16000b1461034843c143c81e410701305840c901c4d4040f038606804842e8810300240003c140301e0320804001c541c010b08155001c0c40755047c128907002803a551300c00b134851410741034201d040c2074500fa14801e032a11002006921343d07075422074645004c2036604130b110380d00061052000c505500c20311001240282008134034030794169800b0000340c04c50b40e01941d005548804210074021010240c0c1003401c420980c0036010f00d050740c00504100e1041c040038040100080005201f03d0148021020994119043e007240c0350032889003070341d00c0f4440e0150030300a500301103d040804544d481ea003025141c040e006541141d695407540d5000300002400c10040115240000460907001c10700d00051020302e980840c6540e045082c4214201d07080804007035079a00d4100d414160400c045031010501d40e1410000e00780d02c2c040300400610014148003183c0d408021 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 856039001 1250 856037751 856037779
    0x8160f0501090f050d111c020c0a0f05090f0f1302010504080a08031602030703050d0b15040e100f0b0909061302030f070206070503010f3f0c090203060604031b0302 72
    0x251060100f814400d4003140c1100a0400c02110782c49040c91094940e03500100b51344560010040e940c410001092040342e482011440014004000319400240c0071018283c0c1480385007458454164001c03550b6284900c1c1d41000006504040002080c00144480f0070640004682c030420889000348a440e04690300160141482c40b00750b4400d0f50130301169003800c9201a50710b070010084e9031180da01915a50b04140a0f14140400b170011550032680c000180600a011480200080c0001d05070030340224000c1d1030218100b40401c0016000410b054000d008208020052501101c1d000503040c1c031039248948a590109202c03450700002c84a07446e00120401058902404901d4481c824135800c58507142c031140c4080c2e41d07a110a008025515842d00c03414480504100716005c00382e00c0c0340b90200c00b8036403280c0080400240f0440561349900407110100280188507580201a080b048030071031460400302d0028160703200301e01c00108240280f100805181c81400010401190040d00d015a4800c0d0 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 856040251 1250 856039001 856039013
    0x5100c0804060c091806052706012a0609060e1b010f0c0816150c0203040e151504050a05010512061512010902040e070c050d0e030a080d0902010e0d08160f050109 71
    0x1081c02a640141202c000c608d0f018801d0044001d5400380105000c05c440e2200001140c0094006140c0001130308a01d2031544a4000a02c2054503c1c0c02030000142e03610440c075120301980c0b01c07104014403c1d0b0151141541003a203e5840c0407408009090200c200042043c0554000c8503a5501501d4804c011640c60616400031104680c190300c0703510140d010280c0c01c0c131000300f00c503000f6900d000140d20900c0240221410129503c0e0010002117211980c102480700060341e2000a5590480020000c41c0800c503d040c40c1d0070000203020242042420700070315803442c20210400030441c1d03200d0390065050b604daa892990031105403182d54002d0ba5281e60b12440318001950203440781302219000900000d16141c4074004502c20140d00c03d02030500c40302c011008075050111000440e0307041c0106500c00d000114010005d040762040070b203000c41c000080b4000508034081014846020303c4d0300001003c0002d4415040340c1d48204070f1144000c2d00c5000d0704194030301040e980c00080442d0f28000441c402e01030 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 856041501 1250 856040251 856040261
    0x20a0203070e1b210606040608040f0804170a050f0a080706110c1e06010603090807150f090b0916060f0c030c020607080d050912090607050c10050705100c0804060c0918 74
    0x76020913111855140c5d0818000c90f44924450341c000100c500f4085400296502412044d80713018003083d43c18140c464440740e01801c00861700c4041035100132034640422000703019400326260600090302d980c0100c0e494103aa07522800e8001400d06a68070341c2c0c0d01111000c401550340343c000803011100600340c540140c40000d01e00c5000307844e0318030400c000011810311078040e00714096030118120341407080603901c0448103518812a20300d441e8440304c40400444c036522501030a903014030345602d52402d207460840c3c00d01c4115000000451702d900c4043c404140c110b4040d1065550a00c0c003c018144c0904044500d60580c08000f0b511074000504142808000005850800303076004041020f501c402044a50310818051007001440052114605a2401d4005440c0090142d0300795800405001c0018030154580e56001d4041040410f0304428040300f040012201100000e00704048440c3c2d0304041c11610b0000e0000780f00d141c0711280905000d01c122070410040109135031051134141d240e06401e000e01 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 856042751 1250 856041501 856041547
    0x12021c080328091e030e280b09010203040e0903122403010b10120906110304030810051c03020a12020708120702130e030c1c030606020a0203070e1b 65
    0x15505000070b12100c04640306200700503038024166884040101c0c040d00c1c1004040c1026000d001c124010940c076070719034102940d490900d411510b17402c01c0c0c04070000d01c91210160007120002006010750001c50760004115810391380c3c0c3c040840da1580e14004003c1c034506c25000c1c40624006242c3c103001036040544041440022101c41c141070800b850030074103089408103112941c1c0810810320b00040d0034062055100050781000c0c0114441c803860711480c00f581c801c00c5000c1d100000000c1000241544008001c0d00301c090300100016144c58080006d861003481b007541c241400c050360200d401c05008008449a81c1d910019503002084620340283d2500511322800c2480c0c0501c10a580030560214103e40c2c065900078010780803d69202c02010042035282c24103221413108020713510281d40c00b040010311000034009a030007508401800102a181191300c020195400380301c5090050b540480e40105862071a500050a0354a40d20144480d500741c156004200200280850140c40b100c43c00819030 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 856044001 1250 856042751 856042801
    0x8180f0604064113052b08130b0606070204090b07030c05030c030406020d021b0622150f090503040f0f0e060d021207090614030d09080d0f0c120e03010c0912021c0803 73
    0x40111b072800380c68543d02140e50a030120348800003400055100001c0c2c0350004005411142090340583c04541114149601502e00f000c00d8410095815894040c800e140c003120326003a800d60400076500101070002400c0189203c0d000326801c030145005a058820144c500728240c402d54504220b0b040c1c0325030003074690740917404200c00d0780d03c01c0320b1551440328980c65000c0c6042c4440c201c03007a011002040c02c04151800300e5110013964001c9002080580041c00907103050410441c0f8080c81c0c07019082c050345c805900103001d0380401100c0c0d40d5000c00a290b442c1c054a0814841584005242c208080d42e00311040b01351500c9000310350790f50080131600c54140143c1c2140d41810b0485400da075184080d20442c180750b440034502d1424540301d034080c01d18a40035414841e9a001346aa1031282c51650031111400103851480460054a024010100f02e4032140c18040400c0741002e60f02c60f03281c4103454002c1e018040216030410005001449480f01907000041103840f0304040d54145500c80310311200b4201 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 856045251 1250 856044001 856044073
    0x3040b060109170309010c0512070302030c070503010b010f050304020f0a080c091f050d030203073306030507091d07080a0c140108180f060406411305 66
    0x42c0030028548041c0c5003050f40158105200c50004550403580380384215280e0158040340c08111024102821103203104c0e401454032405034104561804805a01c6140b10340c1c10164901c500c2d0340c00c41d801070181170f031526000c0d54a40da40d0021400d50007c090b8029000214064000b42181020a400c001c0c0030003100c48185070307160200920b81c440c1d4001c3c548520707100725034020400c900d0030b4070084c120280300740181c905041c01621181d00c000403140300101c03007210800105078650b080c00f2004142000510007042264115100c02d03903152010f01132005500d542d00c40010091a404124002c1210030300300f114032194858031402e0b00c0d00c100c50710458078488501404a400c0c11012014600d0000613503900700160744883c071410504c12803072040c2c202801025aa00c5801e5001c0c4005032180d801480c0103d03502c3c00a80c22603001080c210441114401c0504c0c0c107012001001d000e100035030081c41c80303101301e54440007400740481c44509002401486110281c240000c2e9202e0100c4c1c03aa0b4560100d958 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 856046501 1250 856045251 856045259
    0x30a06051e040b15030f0102030403020604020f190504050709050d0c2421061527080c0609011110050f010b07050c0d060b030709090618020109170c040203040b060109 73
    0x111011007624001e14030700c880c0d8000b403465000721901392200700700242140c0c8222000c034401e0382268400d07075060300160801c200304400d42c200034540c0301120b9015100f4000301c030700340000c02c940030403640a00c1c0d20840c2c8a001140c200342c8180c02d02405080020088000ca09151504642c1a01c0c984503030200303140d07540056020000200d044400005240c0c460240071044041d100c030005500d250445c00455880201103481010f808241c0d240c40c2da1500d804658024420304280c1c500118207400d010382e000b85100340103120010800814040c0143c038203e031510050310042e00d2502e00b985543c40036106205618a0f81d46494104a014414071000032101d0b90326021032080500c110b50025101e07920429804c112400c05480c40b440300da01807000000c00030400070020b41403542c45d9024008058503062000217020080c803540342d6100c0e842e4000c3d254400c5583c0084d100c00c50520464182800c4600034103c641b50038041d03401c24000060045650386030925012030002c43c16245a4000b0b42c01120200d = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 856047751 1250 856046501 856046551
    0x30c070f090902091b0f07060e1510050f0d1a01140a0506090616020a080f0622021003020d0501120b10030206180a090e06090d0f0503040308070c02030a0605 69
    0x140b00d00b40c003e0104034156880034444c004401e280061810301c03000070030440600488003009407000c10710845012450100808045107061030f65021004a045007400b8494840b482d0503d003c1212420b581d0310f00b9620740d420000c1c0904030302e04805010b60030001c0c0300b80d50b035084600c003040c180c504004c4107008010410060003000c0000c0c0c09035940050b800c2260303d040d03140c1071002d0495628800d14811241400b0341c08145074a81c4c540c012030345603100c85207203404400c0038002d541c0e2282d110601c4900100c0c0a64a01e902100413078000b0380241e480008501c2e90318801d404031a000e4100d40c80500175541d44a0020f0181c60b850741080d02c002c842c12010609090806e0802c13402c0701c1d0002e00090a000001b01114490003031300124031740c0106085000600c140160082038100b0088002900039440c20703d821600340103a44285908114010078103201160700117081c1c0f50415014900345000350707542c00c2e0a490251986101135414800d450700b500400105810180c0b0891441d082c0701038070605103000b2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 856049001 1250 856047751 856047761
    0x10e03160806250503011202060714010213080111032206060f0906150206010b0a030e0712050705060304031b0f0807060903120b0102100f0b1201060801110306030607030509030c030c070f09 83
    0x58006201003004000b00245040140c454500082c1054601595603441d140486103901d0301c80a1030b500450860ec906822000400c01003104000a00c4407aa84160814851000420039440c5813040e13403560050b5451032004501c0707290f10200401c1080e0315041c0d400a07c2219210f1480310b075081c0b88020070800380108a071038418946400412003a420300920301800d070020013001080507605c20020320180f004011000041048030300506500c038103802c0140c1040043e4010b1030142000700140400641d01c01c107180c25503003181016841100035880c1c851506590250094074461001c215117080c0001b42d4032400da05882629008201c1012192640940d20030141d0f150160308801110310294081303800c0380262290505001400100c0e02c400184810003400d00284c45079500c2c042409681800d1252025480001c0c682900b946030080001c0d83d40e03640200050105034840011070703039450041003920b0071440000180e035114400c0c070013100e03600d2559205000000401c0301c40025003810034032031 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 856050251 1250 856049001 856049071
    0x3020c0a0308071101021206031204061403042303190807020304180b060c03040f05010305190e070b0a0e010207050a03051510050312032a0405010e03160806 69
    0x60940c40d02552419148040020100c8041c0400c0400000ea02c100c00e200070301c442c110340c02c0c03901c4850a0450a00d483c0c400054a40340001d4070820003030007800c2d000202d42d4503400240207925601e58941c030703101c072090400000c2008144050b940c0c0040014010015105a540c01e07049081c0001c00040200d603101d00590340900907030401c102c144151482003d40030105410300d5001b181450f82000401c1596002c860919a01d0b08081414090300016140c4200144000d18061000d410b01030106142e400034821550303401565281c2403454140c1c24083c00006012444c1036544501041101030481d5000a0245005028941020443d80350040029096940043c0200410403c45210b128640f07009000480c1001c5c043d8400256664208010f281c0f06548035000f40c3c581c20100b10030203c000c0c2480794a0194003088070001d08960303084040c1e40848000f40303000e41c100c517004c0b070109080241403201c005442c0400e0002103a41c00780011054015504d815110791008088440080c1c076400300c0c44 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 856051501 1250 856050251 856050253
    0x50415140d06090c0e1e061e0301090c030c08010e0102041202060a021501081b0405060114090d02060d0c020d050c0703110105040e04050127020105030a0f11161203020c 74
    0x840340c80982001406000c20620498002412064548844e0021011a0700c00d1031125910030400c100f1500f2082c010310ba480c18050980e1845c1040c10001d040100d184510b01c00351860403181d07000564094022a4880d40c001c184480c0360303622030510f002d04040c1c43c082c101f40c0d0340c28280740c42000101442114210744c5d4074645440035600c2a801c000786980044244400c512408900650018100308114020b19454000300781404c1c92200c0b5010054590700c0043c8507601c1d2108000060340c1002c1d008004030549015a580d0b010404001060041d13600c002a40020340840c0d800d010b200242c1c8200e07146e240640890302c4007035054804449038440c20054003102d0b080441c04000098445055225aa0301414050b04050700c0e2844180d8820048500703a40d0341c0e440c1c03410a003c1101c2400c41034024060030040c00d01103082078002801c2803201074006500c1d02da49024150141500740c5c42008520340c41c01e40e29984e80c18100c2041c0790040143c4040d9204400d1209a05281e4003034400c490750181004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 856052751 1250 856051501 856051529
    0xc0f0207080c04022d0a0e01030603110d081b0102070501060b040506070b090304030b0a0b0111070807171207030215070e0d0204390e030303041113060f0f050415 71
    0x44240006500700446601c0042e40078507441c0c44450705c01092030002440c010005807140d54184000f0003050b0303810f0790f041c18186086400d1000ca5a0040003603000c10003500c074030362001080d00c1e00b056079200b03d80e0100800c0341c02c10802c03815500c044d001002138a000700000c3c001140c460485074901d00c2688221a0f00100c10030100c2c00050082c04895404a81c0705c6c29281003907a40c1e02d8450325040e0482c0e840d0301d2250795a50000c00707503800028560078040b05000620300709090003842d035514042c90003004e00060b403140440300c5500003041b402c2d4500c40c0311280c007600c1c0d96152401a540300c00b0075405c03110046480001400b400c1c8038290484000c0750040400002250903000d00c001802c0d14050f200c0c8800903c690701407190317a04204403180c07007600c1920200001c5070001c001d0142410700007441c400c1c0c1003041400040346110056142d101400c83d00c40495503c010040c81c02131180303600c040020940e0007400500d80b90f200c180da00444409880074040c00180b0003000c0001c7c811030107880b61940f040 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 856054001 1250 856052751 856052773
    0x12251505071214070308010513141305070503030d060806010e06031911150903120708040306150f08010b1302070302060a1a06040e071121090a09050a0c0f020708 71
    0x1071002505502d110b080221684203c030b01c20010303581c4016016804118544010449170400c001141d401c0c402d0002c04100000500e2903800155001601c2e00c0c00c403240c010340d01018010188070b1000288002001c80c0d036502011451003010341000e03c00d0504500072000001042d00c803c1c2130880c420a0f00901910b18a5031409501e0244821032030292660084071580424546a0000035010003682c182100d4507010a542003610300a4140e95808500c0780600941001480500550b000e483c1d02540100d460010280ca1121001d0140d003c00c8040c0c0340b1050000d0f00070010740c403540c039500d41541d07000c11102402811505a1154410040059000b000003811110705a0f2200165a00400c1e40c400c03e50101c1c40021002d0300300f81c1000c510080f13801c040c0160190004001c03403a50000781d01a1150010b0032800c034404000c002d43c0c1e07080d10308000030b51050136030b82c014501f4041c1c41a035400b040542400d02003540141113101da11000f00301064450303d144c0e4000600041103a1114004018101c14 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 856055251 1250 856054001 856054013
    0x1a0d0207031b03030e0129130207021003090c0f032003010b130e0c010315030303230906090f0601150c11040c0f032301030b061225150507 61
    0x94a400c1d0308129480980c80040c02d04164040c010501903900840c1448490500c40d085481c60103034051300d08000c22170f03481e0750b01d014032099280150859008603031140f04445100a4814000001d42c4003030350030b070419942c41c1c141d40400c080600800c414401d2948985601d1683d80d51703404081d000058412803000ca03040310314a00703c00c0791f00c040d002107502050b0038040b8100c0c07c000c000d02c42481d070b203992168641306820011085008000d00e4140301821040000c0f00d07890030a400042c04043c3c40b217111700ca800d00d00c50025102c4055015071040c01d0f00d0000c4005407164421b8030004205d0280c4055260b03203140008803541030303c00440c400c035500d040300340c3d007038462502c4220210784444800035071100035542d074812003041c440d8503250780340350310840e40000301240c1c26150810700e00266501d07805181d00e0f80005880c10f40f83d100c40619041c0d1a041c0000e0320001d0441c04003c9984075445101000c03080054010f92503400c009c0d2000d54090b00c0e440c420845028080c20070b00062010b00910300401c44c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 856056501 1250 856055251 856055257
    0x5100302091f05130c1103071112210a1706131d120405031e07060e1212040501120605031203071412010f12050c04051005030102031806011a0d02 64
    0x8240b499840c03265950020440041041000351000c070340e1900f0f80702d6029049101ca20b0039915220140d498070f40b07660f44000300007008900e040c0c06030341c9a2602058428040250700c84402d42d016013128610040700e50814143d000f842c840002540c0305d04a641d54600004125005d450300610300b503560303c010b900001c000d006800040d00c500c01d142030404100001071000a940300c0c0b1030841c9a650300e00740030a1615021300c0c40c0c0e0a0b0306989442903181401c8002050b2001030b03c0c2d072072428440340380140b400101c01c0a0807c0c868034460158648411006200c1c400a00c100e60f000e8031b481c10345d402203140c440100c888502c0341a03090740043c0b410043d9154088025580180981080300c200e820001c5801a240c120078170390884049408018040003041d020b05100520441c0c0400b44440150350700c2130f44400f800464980140d0329600852005151025920301801015000715103c5c90802405100128110380c01704007406800000b1074204000076030401250381040c03105240c0bc00180302c0100070340c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 856057751 1250 856056501 856056541
    0x21611061605060108060619090c030b0301020a032007080301090b1903030207060801090e1903030b06180f09060a0e0c0d0e0604060609060623071a010305010510030209 74
    0xa420800300009030500c00c50300604034000c00c0280619170402c85100c0c5005d401406440c440d05030f4400c00c1c825042e400510400f0340b54642c00200e410180c9100a170080c0c81807010490385940045035900b407803a1f056100f0401d2081c02e20145444415408420a00344607105003d03000c08010401849410b4890b00a0301c441c1201402e1140c03504442251350115841540007240140c1000a0400c141039101d000a0301400e80840100b18081c10400c4055865042454004d003103842d8040042c01d05000303502c55844400082c00c040d03980c600d15800c4003a0200500d1030948243e540318001d140b942005000117200d15806003003c0491400d1007014a0189401094101c88203410050041c555102c0e01800300c1c040c101c0002015542003602c0c1a505450b410f420512176645400c41c03c005860b40410000c81da100c1040e8104822401d00130401901d1107480806000304000b403038080089282d41c103800b41283e000d00300030001921084540341c02c8541c40c2c84060750008050740465041750080c01201016 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 856059001 1250 856057751 856057759
    0x12030402030c06030f0108250e190501140108160e1302190c2f010e0d35040f03030503060d14011b0801030f0303150b07080901030f021611 61
    0x1803202d58001400b1a40112400705c0071542d007400400408604001030b000a020000001c0c95a0401c0500501c7c40b0f00c092050f01e400001d032101081c0704200c9e000030501c004034054018403156844003110000780d07590026542c001408000050020301800ca1801e60446003941c032544000340e04010000b015002600000080d0784c204880c4a0318050b03c030741021200d0b802e440b100035008550400b00c89640313500707011407050b862103480c11807036101e885c642d54840c00e800d007000c0740c001300d0420110b40d9940b0407802c000c100039241ea260035122801000611064400da84e48060101d081001d25400c03401030340305d20360403d640a0f105200180c055406150702c81006046c001c04910242c8a0885120701a07440c210f0596407000f4400c02090360900240701170a05003000c0f0f0710381d4035554620402500c00c0380040c04042e5110205503901e40742c240820014054010059200c00c99428484540c1c0c2c8140315850220f460000d05101d40071260003940e45000d12410701c400b02c80c42c02c0d19100810780e0055206940 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 856060251 1250 856059001 856059013
    0x30a080d1508030a0206011a03060f12250f0f0605030a0b010e0405070306030b010f0b0301050d2603061e0907180b0f07020406090b0603040615050904030f0e121203040203 75
    0x600b00c4108094080d8008941c0280315552404201301ea101030f051040306030800080003009419252403244524560741514050302c80b22444000e00c0c2003038465086401d0000c420810942d42c1c540f140408000d458201114440c2d00c0d41e54100c10003485080d02c50040889c0040c000940ca40160358400342603a41e060401c0b480c1090540c0014048500446ea440301081da03c910610503c01d0141e0002d02508241002c08111414603050140d9404141b06107440b1341c0241902608103c4100c03180c00384c19030245080848405003ca02d545260411110a03016602c001c2c01c1e61940d403034000c024280104042c003441c004c2e84801d842210800c20450000c122049ca800001450030324040c0103104090840c4c250f00c2d01c0742a41c0c0304000c1550416403001152605101703006147d643d4020403a90450340c00800050050341e46e50041c0080c0e00c003175000b10b0307000521384104400c1c1600401100602e00507030341c544c03462254410810805048131942c1e13207055072000450f0441d8401840c01586c000b0300080803900 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 856061501 1250 856060251 856060259
    0x915030b0c03091b0102030f0f0f0301031a09070f12051c0c051009030f2601150809010c0905101b0503071421160f0308090c030a080d15 60
    0x40080c005486841d014940001040140030091040c6051501500440030382140c0440c0001d40d00d0184814005420100041c5100c46015580c12206030100807500c2e241c881d0780d40d040c449160ba030100c0046500c8840600005d541300c00c0480d40d039054895001c02c800f451424101c0d003c0e4a0001000c04540c2c520403800d4100508601141103407e210381603440391168007180c40d1450070320074016242d0044a060800480c0003c1e0003001d20030140c1518034140074174410101002c1110b80641c20b61014130351040c4008507079002c1103490307600c3d03609050b100d0265a44410a94500721251000c0510014204103410b1000f0300e0020084040c0010920740022118440c070102b10901c1080d90080307860f5840001d44004220944841d070102002c0040540800182d0180840c1905105200d5403c01d010025a5072034940d41a034100009a40100880d0141c46540c90064851a07040c0c501030b98503c41d040300351986140004040d9040ea510861107810480c00916407005000c00452010001c94151404a = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 856062751 1250 856061501 856061513
    0x10e0115053106020c220b0102070315050a05180c12030d150302010f1e052b0e0105010902071707140f150109180231020408010507020c0109091503 65
    0xd802e0507490041014080ca0981c0191616107180503e81c01003d01200b00c84026010302500007020403014400304443e190000102e00b80328083d00028802802100d00303918007e250b512440c4101401c0700100480d445162a0f0389000070b0341c2111302042d80c04180f81d12244c1c100704468002d1210503200b12414285d1141040040da06848214121b50801040030015503034801002030303904181e4201103040141002c120305242e2108401c55080c86800101180d9904189505601c82403502d07403010300c90b42100180d200508421085002c0c50360038607002240b01c0c0d0303062080790080e6612106e007501e04046030842c440c450b040b000d0700751200b0600c500141c80c00c2c0310074803070b005102080001814844418402c4080f40c404103810010000c1d260040404d078100d020341d9218440380d01168440d000303c160040310541403090581d1100305a0002c89621000d41003074000c3c00070740d80d0200c0244060b545080e030490341c0c3c0902a100d00d00050350500c041003005403651184a00200d00a0300382c162a450b07480341 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 856064001 1250 856062751 856062817
    0x3060503211c0911010f20100515040c21090f051903030c0305130212010b190807090926040914040209071418010207150512010e011505 60
    0x4140c082d101c82501c0104250f074600d01160a5090030007480a120b00040100524a010f206800ba21f075031003103072041208200001d0076140102d500074040c500d401d803030003140100f203500b89500450800d002c181c4190f0060041c01d460403040000c1c010040c03051081100601882d6805907120b040c20030300704000c22414810122908404507494401e40b43d141740043c12120075001010030140b420003440040380d500642241619012129800025100e48246005084e68200c2ca54801c0d038003401001200d60b50105c01e811070300c00e101a00e100a0795242d01c04290b40509100410a00b000e80b651a801400c21182030042c42c500106c140c102920b070008a1b040340d410140704040340c0d81d2442001b0071407400c40300300c0d80d01c09124030740002800e207030700c2d05e03140c182c000c80143e0160500f5020264001d6482000f0b05030040404084c10104a43c2e030000c05402d95020044030100ca110741c90000c161400f0042c100c0c2d04031342c000c007034203203942030203110480e4580c01055080c0c5d0006032075042810010740a07664 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 856065251 1250 856064001 856064047
    0x10504030b01080c0108101203111911040c030b060702150c030d0902090a0e0606092d040605060604180203100914180109020616050703051203070f0306050321 70
    0x4c014031842080050310b01c1c0e000070150460854551014020100c10000b0702d05469031504013014140c103407040c2141000c1640010914044a248039401803000c0c502102c0c0c51100141d0b001c10034801c4c030340412015500c20419154100e00200010801400d011104005c0c1c010340d0070080d4101004842402d0035036205603d1036080580f54207151055180c07900406810503801d6600f0015070381c840c0804d82e2110b0000700502d03c1010361000246846881101d45d5080104040c03980658820062204900c81e105840c260360051802c0c0005485040070000c48050324000c5d144ca0740c80704501d4002c2c90280d40300421090100301d81c644000b907216098001c412030002109942542490081050304000c03100c994450784503810406d4020145c0c0340c00d0116204e050501003031400d0039425060991408a8030392009200348520901d5071000380d810710180d40943d03410754030100c0329906c1902c1101541d0440c000c041d0315403c03402117517100e07903066031614501c80c0000c04180d00b091020380c5c00201017500112 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 856066501 1250 856065251 856065253
    0x1051b04230a0e07020f01150e0a05090c0d031d1017040c0506070303020702150f1602121e160609171204060f030b04061d0c07050106140907030e0303070c02010504030b0108 76
    0x11b000001c03135400e00030700918142d80c500c801032003864441300108059024012003841d81d5900d000c80e080701b5040c0302006801001074244070850390f03c1d160080c607020700c0006094075410300302c034441181d29003007031f11454000e501d0f90703102c044030311080c0681080407001c0c004a41c010300c0642d000400d601d40b48040d00c85a4040d840c01602d0780f0041c0180101111403ca103142a007408100844140d6200700503244000303c00c0117110b10b0307003100e0310116070400040e42c040c0400b8464852010303032000742806100b140402d03240580700d4580c1014050b40c80b0640d14001c400120300020b0007404a207051140c0400c042c84860120340c02c46000031641075060b0300c1a04440005501010410781181d0940502105500103a41c00c022691400c02e10f0400303504231000000081d020707500070402041a52003500c485940007402001703440c1c0c1c4d03a44e604403c00b510a0240380201e11000000e082c0b00d0207446080100c0038071401551075a03503440c0f001c407011924407074101e05104c000d200100c0401c1d0840071007806029079038 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 856067751 1250 856066501 856066513
    0x601080a09020a2c0c030a090c03021c1b0e19090c0605040f2c0603030d0f060303080a1a0111120f0c01061a19050c0f01051b04230a0e0702 61
    0x7104000e1103036200c041ca0003013040c800740485104808100d13584800c50340f00009402a007440d22105103103940d403001e503000004001c00099103a13084100800c213440f400d000c2d141407070700343d0144802c103215108800600030428000399011040c0b03d0503550a690484c0c00294443d4150707605440349205402102c009000403405101e5001c00d0a400c4c4007900e1100c14000106084e800d403401314821698a44550201002c00304165072006c00554210b00102c2000b40300c04184000510024100c80c8000d60010f081c4d40042140c6014034421880f0700d00160700e000c841c6d40441001922407103c4110b01d40310034401c20000781c0c00c03103c0041c040c088c3c058011100680da298000c40780b03405c0d640550440198500098a500d40340442e2408075000d000340360301448925a5404800d5030980503014424589000d40000c0000c00e80701035101a2140040c110844d40d200012400e218060107640504425441194003402002a991012402e4001c004104141c01038698240042500c020380390000076078400307 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 856069001 1250 856067751 856067789
    0x50d0b2707030e1b061b0604030203120703020711091005130506150a0503070e03010207140a200f040207060f0930050405010302070203010617030909011202090601080a09020a 77
    0x42c0603003c0002001e00081c0300690500c030704448010180030055110341c070000342e20581000c101e00f01070020075440d01036902e00c1c500750402a4880d8820651031808031560000501554040d10035100100d400c10801140c0280520500890a0b805840324400a1746207000141c981d55000110740c20b10349280000c5030b5402c017a03051000d52510038a12444104050007081c01240e03020060300d511030920b1511045051074540801d0091045c22001380004500076030200101c9400503107403000d10310409801c210080b19941c1000d07580d04001000f0751040015502440c41d14203900a04070003030144500054020964262800301c42e140c100c110340c129005444841100701d03602414014206015110741034000c030f0b00700141648524001d06041c158040303000d02c25510258020780c09030840e140b14100c00e040120780f03a6070301d400c440b03070085c410290280045840100c45002040090f40680b019001e52181c00041d6a042402001294141c0da15900e00f80940d981d810444010041c41e880c498280b02c0c4 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 856070251 1250 856069001 856069007
    0x4050a0b0406080714090a090f080403030f0908030f0d02041d0103020109060201271b0608091902030c061b0d031b0e030601031211030c100b0907050d0b2707 69
    0x1d0b030142c45642c10030302d8200808203410300b03000d45c0c6040440d6000160f035500b08000f401443c02c04400f820035082e110b80b070400c0002400c01481624040d440d030101500d030600d422a85001a4000d50380540c00c00d03c039240000b401100584100c0150391005400d15459030403000481d61b495081d60198481600100155604001c4140207060380d84024010002032812506809413804c2d0810903100e28540320000744010002120740b5401d403081c04c803529a907580e00040c4040801d4541e01c003a401140040c1c2c8201020000051000d9400350152009050110802c41d1030780118034814110407001a0407149407105100548030a0354a44000607a8586d00000ba1110040da0704e0341c10a010049000f80d2490707800041c00d0313045a80c0030030310b44000030088008075010071000c50300b8081c034880400d07208080c403c04a40301c0f809900d00170080140c15400b10401081610564101c03010034001c010b04034503030f003990300a428000e00140059050045055414000084150944410116000c10f000d50381d94 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 856071501 1250 856070251 856070261
    0x901021c061712040302060307030905010e0c0a05010c170d022214010c0b0f070e0315041101260a091a190506011407020f03070602030c060f0106050409180204050a0b04 74
    0x282c601c000b40121031203080100120710442c00043d104140220006524900c01d4105001c9142e11034000c0c0b0843c9410b40300c1540c0d580f00784c60170f00e114a58a040104881d4400c00420070310035046200010120040381c00c00c20294014098900c020341c080102a140707924500310581070201d4000303084085480c100c0328409580718021002e041060004c64240401d407804181e50b04207002d50700c849445d0301d440000b42c1c1c00f80d486001c0346406005014500d04103082c0ca2001601c00c5010b074501a00c000c0c40c000044603018494130800440385a41d4607601d000b075400c40905a4010011100055000020785601400340020340740c60b81040c88100800c00c0c20b0b40301d00c180b0008803c0f1b201d0280803c1c144280040c14020900c13002c500d500c0004500380c400c1d591290300c00713030f800000501600c0303516854a0000752130780c3c40003011504d14440e5001003081d03810740061050480b41d40e036842a0030a401c0c2260400034000007030401c50140c2001184901680e6548101e900442e586800042c0c1c00c11400180800e0311 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 856072751 1250 856071501 856071539
    0x7030b090102030c0708090a030c081605031203011a0d05040605061c0206040506130902030403020a1707050a021c050d1d1f0e031c080a0b0906030d080901021c06 71
    0x10740180140241c3d003130118162452140e005502ca900c1d803500ba00400c551000c5680f0141c2080b4261800003080c01000c1a550050402c404824148a445909242da58450440480d0314543e0400040008048608805904d565045d9506150455090511095800c103075400d07100c199840d000e200d00c9161036406d05031104105092030307020b820243c0004405010f144101801a200028030b1004000090050006802014421501c0e4102404d000355900801803080340c05517000c4086494440000c401c1d03900f000d60000003442018155400d010407131000c19100f035014085441c0d044002007040c80b0055140c00c8540c3ca0044c08050400e10590644a1044160042400b0041c0d0600c010800c4504109290301e410011403903401100400d01c1c1c041240400100c2c3c103400c40f041c403207640c0d211003114042c016140c000d1000400190403c00015800d840382c560613401080b1246402c1c0c060031009a1081c0303000001418200e401032074800c83c581c200c10403485991f861078184104811040415148 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 856074001 1250 856072751 856072753
    0x60d23070f091e0303030b03030f0708030103030305010b040f03080a1b052506090b1b0601032006160303050705210405011109030703110f060d020904060b0315040209040b0d0507030b09 81
    0x8041150848010308940d4003019081548a001c00c0c04123482c100704441c80760008162040e07031036401d410009416042800203c0000e4244400010038407403a0f01610141c81d5180c002105041c034640d035000e03040c0e12444042c400d0240014405051210852009a00901034005041c6010491341c220060f140000200788400d802c9040a000301a84002c0450586504114166546070800c032411041507014415442c54800c40001208120308070a282e212460b826400c5017012034a9020060700c1d015010a004400c0c003604000c00c04a8421340150f9003200c42c03820100c1c60512415031014480f12030b401c0681c0c080c074000052008000092041c40388980644098504008807180080c1c1c80d640240b101500e0201d203101030543d990780302c8aa0401020380240007a80d103104102c160340194018400451159162a1000940b180d003030080320b10584a1101c0f0b0166001e101007040300940107800001d80083d41c800e29200140c813031480000c0c145002d480104286407445c9070500494000810309103617 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 856075251 1250 856074001 856074029
    0x50f10091802190e0c0c0d230a03060302030712150902030a02060307090b030a05010501020d020a0804091505040e2503020105160311070306020912010b060d23070f09 73
    0x7420407030380126203030a604031840e00e49521180035103070880440f40c015162940300c1400f4000d9003490b0b94010281c10300d40d1000d030380c10041409003d03102e5041403461520070f1214503114540001b0100d00520010415083c005042600ea030003003071400816410010307036880701d101000103104039024010355142c80741106001c80000b0340d020a84900c0201c000900a410100100305410302500105014000800003541c1364505001e5800c0544028402c0030302502074417040381c0d8081e20124034217040c0741c0c106c80c115141600c0c000d503540082c140e03500040881013407600042056501e81c010f03070400b03d421900a0030201003000b9889107520350314040d2070755222500380400040c1d07086030a4132880c00e4541c0c07800d6078101d95802c0c242d6a0320002c00e031030649401803140c080b04100b6030340d01401e1902801d40700241c0c00090205001c3c01c8401c104103066000c1c0c0700703108040044015400c40207041c42070202d0000015040c03000c1211300001502c4440c040f8600444a03102e69500071845d100034446601a144 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 856076501 1250 856075251 856075271
    0x30506071407050c0105160b091f1401060e0301021b0c090c040e060103020304020a26010e0706211e0b15070b04030f09170114060a230a0306050f1009 66
    0x20b1303281c0c6048082d43c140007000c500340e20640300419407071406c5a0000d60f28100c0d440d100b0381c7d1644800c0d80ca0280e003101038611818405d040903901c01c0e44202a003a035032110450f400c020301611060009203440341d1540d020070482030344120030300382c6146200500f0000c2000a44c2e02c41000355408005141c0b030000f16080c84100100c00c209149650800001e080041e82c2e80c0b100e0000c50301c00c280070780020108842c0d1898030382c0004c6006101ca20b404500300c00801c00020814002c544580e501c0c8a600c002800308500e00788101c981c01040340c10741600b402c000500024101100503100d00755a030350766034199224802d000e282040299030800c05018001c562030007100d6600c0e04200c00c0040e00c081c1c01c000c0c03040c0c2c0312565280180b46010103000c0305d400b02030080c119641c80f0380c081c1c42400f50030000000a00081000c500342442a282034800464075554045c1e0700040301e104508401842e0b4ae40801188400001300700d141c8a00ca01803480100c0d00d20366071510b071500050311b00050788001300742403419040203 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 856077751 1250 856076501 856076503
    0x1e050a060c050613030c0c0e0a0c091520150414010902060d150b0d0209040e010507020a080703020c0603071706011d060d0f050a050108070b030910020a031503050607140705 76
    0x641c00040c1344074841e9854518102110b44140c0400010b0244e0714500c0041581d1400c5400c40784100c0c140c036001e000042010200300c698410754811220448040300e030082225020780008142003002c0100004103144d00c0200b03030b1503d040712520440030104902808180484081c808045040b01c0d002800943c1103036000c00c007107103e030100c00300e00ea65030350007000d10b64041418940300415107100c0903521130f80c0c8000550020342c06050001d2142c1d140001200c8040030600415105034155000783c81c4070b400d5902c03041c0b62980300c85000c03811800703090303d0341d02d480e542c00b0301450043c03102c4e945d51449807541c42ca400051907409440241800070441501410241c1c80c02c0d00032030b850050390182c0d10f802c10700c00e54202401aa0300121106400c24040242040d400d80c00941220015801c540505545807158003503888240c8005099410003450366a07840354a03002410072001510300014031003100c5022085061468100b00c07000d0b0089c00034000d000b5400440114482169540741d440c010701d5032303a01 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 856079001 1250 856077751 856077763
    0x16050601090e1b03100f0204180501030c03020f060c0604050d140c060744010f060e10140304031d0a05010203193c030209010203070b0408041e050a060c05 68
    0x8550003c80201803029910f0a04c1068014940e0000171302c400c0d1003040740400a0341090044060b03060987c0141640d8040034010181201d42000210300b526042d5024400c008400e1008250801d2081100020b5102c04016131032023680034501802c0000c1030140020600441c0d0f2681a0a64105226109140c0c1d00826100d80100543c142100b0402d1185005038920703800c00d0b00c24000380c42d0081544104521501e4508048401c3c01ea1160b160380c032040b0b100710000701801501c00184225810707102c50706201031a000310001030f083c0119004800250810b030355104032001c034001a030b410703c80c8440c0708180c450910009000c803000c009a504000000703549000704a442c400c00400742e000a001c86010704e0305183c07140d241c1607045104103500c5071481d40d4084034000c3c80722501141614904114800e01c00d507400c8440580c09075145c00c1160b02c0d881c100f154040c00965514604000c00117403030048004280003154004800c42c096440c08040005120499002c6c1050020045031080003440c04030300 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 856080251 1250 856079001 856079023
    0x4050a02031e0415020a180e04050d050306061603020a060e1b0918010603030c03080603033108101d06091213050a06050c1e032b0216050601090e 64
    0x120b00e22a596030804000c44802e0b0b80ca07145010784001250807602c2d40c004840c0394a43c1c888400211259542c5d0004d00d0300c2842160054025005543d0a590542c403480082d500701000405450905204640f00322005070344100c200c015034859004c0c0c00c104020750090010058624010f0300303409100390b000140800154422030720030707128100021114411080001c001c0c01c0d80c40000c01c016501c901e400752414031718204c1039010603100c03c0010164903000085401403154100c17242e4003c0229114201c44009400c80d01140224540000c2014542040440a401c08108000c1840340070161400554103081c000544950000c03001c01c1900d0340d00080e111020b02007481200e9498520100f108065402d03600b045500c2500c0030300c0040c903241d00402030501d903050b00c02960511021542c01c0040c041c1c0c8042001c555410030b0100784000e4000e00d9110a21070181c0641c1e03459482c1e0300c010b03002240e100700c0b24036035040d401b81800c405003d010072520b405810140c80400000034500401070341c46a040d00 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 856081501 1250 856080251 856080301
    0x14010512060613020a030f1103010617010f0b16150f0b0d0206070311070e16080a0e2806020412032006040f030507051605010e03011103010909030302070b0109020904050a0203 77
    0x36800243c2e906c02e5001c2141d4034210f01c002c014407201c20004900310390080c0300d580001203038500c00c2500302d440d9100003412220740c4100c60384050314211007046260401d41e2041c0501038007220400125804607811011807072160b00014020903100413030001c58000c00c00c064014002d080c4210010f80f101000c640740300c0d4060500f0032580c2004030381540350810759040355054088450034002045114465a24844801c0e2126406070703503000d09813003c071800c0142e803000680c031048003400c0c000241552a102c030030317040c102c1811407a4980c607044103981c4264402d822119540e03e81500f8160310031040d080fa4444001c2c89041c4c0e0402c0c140070780d5143c0005c0c0010707008904e00664174040500036000c450103543c0c484160390070107009064865202c0001e22406010820312a410440380c030301031207401088200e500c0c00600307690800c00c688004013140441241415405c0110101007202d11f40c0070750003440c1006000d40d841c400901800700707444001d04440022401441441040b16500c02083d4881f81541 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 856082751 1250 856081501 856081507
    0xe0913060f1e1e0510120f1a070203120c160804080d08190e031204060b10050306010906051602030307050d030c17280204140111030c0601050607151401051206061302 73
    0x1285d034000761400e82c0109412081c030700007a010014004503810290b4080c95400001c8114040b841c114110304550782c9005070010084500c0301028402001c2d006a0724030766290905184455107920000101001d680312000460208240542040849180203651921007541d00780380140d02006000405648022905c0e5203050109840400980341e880300300d0081e180190520b42003400040a800603058060000040d9080d013550185046902980069698a50451500c54121036940002c2c0154078000038040301900581d400700080c080d076a00400281044440380c080240c221102e0902c1d1005000311030140c2c0c004015016000e5038800c03049050340c69280781c0e81d10702440686180234104c0c2d00030302c04a03000c1802d02c2442481c0c00c502c403003038a40b1038480c20310800655890041c802801401d61081005000c5428240c025004262140d1010888100106035003020f85010307180182580109500401c45843d054040940d02040680503084908016004c0360300d00200000c0900e9180e000 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 856084001 1250 856082751 856082761
    0xb060403021507080318100e0d1d090405031210080d030203130c1e050303090a03120917032503020a021c0606090c0e0102030a0e0913060f1e1e05 64
    0x10b03000715009a581300340400d07501d00d0b0004009090360140885180300d44134420b0f252003e650a4482e4081000480300100314a5484030300031540c010119595040d44144e5556684254485c0c1d4110781c003852040c0091038035484500d15542d20804014183c2500070500082007140c810b01260b13007070440407685002b41e0b8070395540104940015407010018020a402d03c07000600514a50a800c20b0325901000d4001c1c040d034a00825950f405010840b59200c48100010000100c101c0107804243c03001d0f00340001c8840e034505c444101121a402203003419000020f042e2a501c000d10100f80c181c0780d2010611540c440307540c900030340ea51949240240644104a2080010001819802c0352641d001d60180256a20307008840d0282100e495444045900c15108112547c0080103580c600e0040c2c0c0d4038100b0a5030707058100210004050440002c141032000840046034090081008420451801190711303865082000b403143d40310034035500c4030741c5000d280c04210580000c0101855055001c007165603150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 856085251 1250 856084001 856084039
    0x1021b151e07050906160605060420090301060806090606090c030708190b0312040801060f0308160f0602031608060411120406060e04050a060e150412111608100b06040302 75
    0x2a03000b0030342d817008002c2207601c04403040d03280440c102c0c3e204d01024081a04c4010a02c0162080006444210210b041c58600e40b20700307820180c075040c40024008501c0700c1c1e0300d006071810040156554a11074020204100080c10081c00e11500071410020703140ca14a00071100918000c0d010b01501604e080751400b02001c05a02c1c8c01840e200342e0002c007602c8034039140581e00c088580c42407041c3e507455420180c001a100c0700c191725520840e03401c80c0790741d07250052000502d900540030794001c9031481056a9660085161072000c1e5100c2c44040024081349100d019003d0f1800000500c007600c0360742488980e05d000c0d03100c1025616407070348a415884041e162031178020b0240c1303c940c20004006542d0b03800c00c01403050000313055010b03e0103104108040f03220083e0282c4c0783c4c4411100c6e9101c808038600030600045d07104410b03022914552506d2b61320664020410740c103207405c0300e852071603040d240311081c801d0711401d1151b60400e0810490400050030b5074004998140250320000e840b0781c200007003001c03403000 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 856086501 1250 856085251 856085257
    0x80a0305040c170709150b190311031311100f1107120b19060302010203070b1e0c0a141204020f0d050f011a0103180204020906040801021b151e0705 65
    0x700241c8590340c10326000080f640d165094400d078a42e00e401c14411004150211203840309641c000295640307400d024482669075050110031007020140c1e00d0000c02a01508100594010364062480c40342840482c180004480340100c0910b02c80c9001c1d1100c3d03062150404c07800320f805800350504d01301c0e040b910b0040b24140401070340300340030918613070501808000c0181039552144180008886801198070950012500c0700d000007405030f441006101c012464140e00c0c01d5001c03040d502811103090024400345585e40c000d031000e034008000400c00240300c1d50822800024030220800c19820040d205850041c203220141000e0b010707040712a241c0445403244000c00c1d50700c5800030220b0341003001c0540d8144c001d00d454121740c0402d112082c2802c2c80303503200303000e083d0111000110912035144141c003044000c1d80325500741a4031080801c0001150242030010341100202c00c405220318200c624074090901c0307081d0080d519419400c004011401c060407070f07440c42c0d036940703008a1580b80d07841c2e0380140c0d1184 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 856087751 1250 856086501 856086509
    0x105062d07050a06090605090a0b0a110702191a070507120302010213120b0105090103150f02310503030f0a0509010509041107020a1e030215090907080906060a03080a0305040c 77
    0x8043c2501075070501849811501e20203108000420191b510000c46544881c408a4010325400559007c14540b00d0960800e010f24020320b2107580c54082d1980c0000c05070020300c1141690b0103600242002025103074202c03240c0c06100d446495260240d0b41d6030705910f03031155004a001c8424003100380c7d000d0601c00d42c16a1030380c00a4401c240a804e8032030031f45600321220f00604944450740b440010809003080e8103400d048030f03440710350052044450304101002d400020000760000340c0c00c0c40205e08084103d00d540b0480c4010702d40600c00062103c914005110700c0e60003250103540100441c000115400f4205c5446000c00d18010391502072110040b56907200720300e01c65034014100f07201200382808400c02001e10354401c40f40c000d41a595001120f1541201040310b940d03208001c4001c10143c00d003246a8425482d610b13410314031b441101c0001505c600c070155100c50000c0c4401080110440e820000281c021400720b034280402807035640c0c4e48075648034071b40e4003030704150311480820200040b12070001d000d4 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 856089001 1250 856087751 856087753
    0x90515012115020333090a20130e0c0a020a02011202040302060f0d05060d0203120a091502031b030906071e0212060610090509010501140d02030103030201060e0105062d0705 76
    0x30f0a007948410032800c246655955001884c180ea00c0006100768044200302401401c603084075950440380030010300c10700234000742541860f10381c1d50a0080c071500800e00003018855009056080040700c50212400426480c00d41104000545032a0b0f00080c4210000d982480c007041d4000000600402038003c990000b0340100c800300d00000c0407000304000d04081c020b20142045240d88640411003101c101c10300c040c1d0550003c4030b1084071020010000c01c08500306051004181d5560503090000c1c04940201400581000c250001c100048048080050500100940c00c0603105000140544105600182410000d050610750094030448005115400900c0c4c01103407010500d80300e4650f0000c94032203114811804a0408041c011a4480245e0b040030f0070350490350b800c1c94010746000340e0000d82131041400134088000303142c010703000850185100f40d00105200740303400001e0314a20010381009119582c01d1010841401021a4041d400702444a52182c140c2200d0b01010551044003000341007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 856090251 1250 856089001 856089007
    0x3151207030c090b011b020f04090b0a0b0306011a0306010825080403110706020604110a030210020c0901091a1009050402040617090705011b02030c0a0909051501211502 74
    0x10302c44162000800c843d190f11040c03086038034120044031198080350038500c0301101059880054202680103441720b45001c0c000050071403194071017101c841c00c01c0703500007901a10f40039295154101400b1040c01880d800403000001046400117410900000b8079450400c1015000103004040b240d40c100b00343e25a81c0c018964071624207038020950f600864054020404540300008900700001784001100d40c0390303000d014581c94668805401140760041c0940c03140c4119030210151380c44194800121070700390001c0951101b00c4080c814002c405a00140310f907403400d000d100c509062048100c5121008544c000301d407190240c426615549a90040754006101180c041203c5400030066000340681200c0707020309543d40085c1d5555014580240e50003d080d810b100c140c2620380d0310740b401f03080b4801020703a41602d0501000c514008040c0e8060382c0040c0e250002d9000b0312000780b0000b200c0102c01a010300315507041c1540501c0080380c1d100c6200c050000d0030740740401e120701c01d030045202001c001d5003599 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 856091501 1250 856090251 856090253
    0x50309101707032d020a080c0f0a050304080f040f09180b040b041a010605070c0801020c121305030d0e12070f060f03020c24090114040204180f030203030114150315120703 75
    0x86d0010f4010b440458008404604516840810355451080d461402c40c60114000c408449540001c2c008440001080c40030040c81e81d0a000a0300190580d0170301c071000342d4982a00134082d0340c1c1c0c2d1300d00301102e01c2000005101140305941d034164025002840005a0340f40c0707150421007084244800c3ca07400d61518000b2914560040050052601695080150b5506c80d807e01d0708070720644a0601c1e45a1250710b09080c0e8111a6000d411404545d20240c80103d40e2880843e040102150185d00000d079100e50300121340c0340014414000d548190000c040c46820122a022911074138000c200c18021824810501c01d4440d40440e4000e40219041d1419100c502c1407070f980410303c142040c40150510000211540b10521030a0740c00d100980700305800f43c81b150203100041c88100c07805840c22480c40c4580000c2f502e035240b80c00c40315200ba40103503569890020705002190400460501c1085020303240e640c52640401034907004001c2c00c0900c510201d079000001c0700d403882c80c3c0080d0380500500078000 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 856092751 1250 856091501 856091591
    0x603070b120f1e0115111516050f07050105060a0b07260d090503091017190906090c0312020c130b1f0201060906141c0204110705030910170703 63
    0x2248103268443c2c1003065a01b01c034042c0c4030000b00c603016190701000c800060b540c000d41282800c01d607001e41040b514000b0420012011b5038007103c0151420380d107520501025042c0100c1c42c4000340305080000d4102034040c0c0d190b007108070313180d400d00d0500c55402c004810310311080b00464420f0744c10f92400304400315081c40d00c07640782e810444a403032142d841440c04103105401083c55032002140001c108078642e448120b036004600e840b01c0c4000703030305030f0318004200024064401c241316140039282814001d8518588002e034640e11074291801c6401500d01e24100d074403020146c10050042180c08100e005280000c52040070100e181da03607543c401c060710f481065406502c02c5007900c10310401482400c2e215819132000b445801880ba811500000400c069000d14921080318548000c101203000440610103c05580040c1c3c0c090b143c503000085c01900515001c40102043e40180c1000108101c0101c141c142c07a10b03008140c5014161104d20750303602e150041220401e5010324404c444940c44549a4107 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 856094001 1250 856092751 856092779
    0xb10020c180906040f15110309011a01021b03030f1b0c01030603020907050d1b05040608090a0c03081602060d020720100e011101140603070b120f1e01 66
    0x4500414210341e00180304489006014818155840285980c1c1c4131a03484d02080f603005901910403040d00c0135452009119809814844c203030381c8a1440d00c07401d00111301400c541440c0c45007030301c0202d480c150a03440e0b40c02140742a2000c400d4011084943c02a9000c68110301c22035801c1e0701e0307101c0c0000740c605010303091400c800c0400e002e040444003100e03034040056003180c0c40c3e408065408001e210000d00d40501c224000c221b1408403800100f203912120034100c400e0131038107440e00045040801d060100307943c0480c00c680d000c0b1384180146a680801c0c1c485a842c40041c0c0809000140c000400c0700040c090701c104912203030390240c079040e983c0da0020702100c005e4001c10800c446022040342400d14200f41020030841d40d039802000314241084032142a54500c102d9003440f41401045145030040c12002e2080d40c101918608055241d07160070002c15003010000d41011074040000d000c1d0300d0320740001c09141d80c3e0219640314041c5054903040200320040c181c0c0403084c40704100072030022a0710000f131449 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 856095251 1250 856094001 856094023
    0x171008061602070503160e01080c0303070206280e15030f04030509011b0f11031c180302060304120f0804120c02010306210b0705070b1314070e06240316030b1002 71
    0x11f04452030b42c0b200403c589850f030840f80e40b0342c035a000340f1810025281820080c0060307035001d880c8221a182c1d0803d410a5079146950403008504094016181802e04041150f40080411426455031410329a0f6180810002d4805000c00070003094081069024081e015083d840f00b0582d2000c0c884140307416094146800b0702110702181440742c140550030300062607600c1205819203151028003a02c0c0c2100d18107890070300c0717000b40c504c138910000250710b54100941c0214001e04036079490a21010000e48811030800c0c0b00c0041084030420080401c0b40e04201c0700f03008002d0301d0003032103141a034001280a064150058084200c031901c41d40c00403181114503100e030720720640c9884c01c2c03503581c0c803020fa4090061032000f0701010011700c000b400c0701140090b1015110f11a000e00c0e020041d400b5449860142142c02c02400340c1031010902c002031130241c420303a090034245610014540d40c02c048444180c00050000c03030000a20380d203620082806900501c0c40e51501600d180b120f02c80d2141d00030358410066030 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 856096501 1250 856095251 856095269
    0x230d15021c0501050406090c050a120605180f09121c0f02190e0105130504110c0303090d030501080307030519020a20130204030f081b060717100806160207050316 71
    0x21f000c0010701560103c0240c035114181803c4108000340c4402009040c9090f543c4d076614404500c40c2da40c058000302c0001e1410b21145640350014540f11000c00150588242c0e610011048040d68a440219203c41c0c0311112030300c080c4000060804007905000071600011400440d410b92203002c50300d22641d100c90b080d1741d80c019400355400103440b00c0c41100c10003407910030421014072050424ad045140f0b50305202200070729004c8012845425504250f40485041d004020503060403640740c02024050148040550b1900c003040c1d5010700984620325031548804030440196148500a0083c580300e581c02c0041070040e20300c0002c1c0ca180c061041d80b8010304c06c1100058843c104195842624140c95200c0c00000960f6210307241da412940020010a500e1000403101c100703400010b022807030046d485501d409080c8940e40341c100124510041200442000010f001c00c029000080c0c100e8100c00c0b0943c40803458610040224140703201390700f04030341500c500d5002c91300103802859210100c442d600 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 856097751 1250 856096501 856096511
    0x90507120623010504020f07150b030d0305090c09070c05070b0d0c0302041d13060608061803090d02150f190905121b01030b0415230d15021c05010504 66
    0x742c048402c0200e020303906122030707504600501807420580d00800e03c041c5c5940e491070801c03625a440310ba1038214116964170060310b94817072840c281803c11071145071429605080c0071903e40389041c6175030344540c0803281d0300c61070541c070104244d94020781e04c14094a4000c03050f200c8803501e6030b0100845910101c20244101d240101e810300e071a2003403090b1810343e070380c03205022652103100f1161140300c0406045204403402200c4800300046013071040e000100b110b42c0141c40d040c80c021010710190401c501c1c402c03900b500100002505955030340c121200c21070381111842e0b00351100c0d429804040c00380c0c480c0d14a0030f00c80080c210b60004004102800c002c00c0315030b14503a026880b41c003800034650003a00241110341c490320114038081240d080f820b100400614000890034640000a0155404c0c210364a0002c0d01ca6041403044440109500b0312088608440345100c66151000c60b0940d40c0d107081c05042d59000c45601452880390350115811408011709c600490110f1000400c001c0000f0720400b40301c2c3d4942 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 856099001 1250 856097751 856097771
    0x20c04060b070b0903190215010509010323071701060e100806010303050901050906070f050c01050913020702060906070308070f2f07080d030c0e06090f060c010905071206 75
    0x1406090240c0310380c041c0c01400c10350a640d502e25800b80292485002d408107000d00f80300c41e02d083d01e0707010320303920b0540c02000b080c04450955540d020041e0044c5025803000d80040c000b18540340e0780c50001e012098108000b11424022050401c001c42e0800102c0e54918108004001c805402820a5a00c445c5501c085910b1b0320031218804d99862044070302d070f41c2106c1c0040010034040d8015217030080060420501d08000d010000707107541c0c050740c8215480d82d040c0c600ca509101c0d00b00000c0c54080000c0c00c0c00c600c1d100748013001540100100503034039400c9400041100440d1101c40c16a80d2100010300b0040e111905460080c2c00840122040340000e1801d40c152058035101c0c50301520700b80f180245011125100034690940500382040c00402c921130720b04001a521030421145186400301d0383c000a41040b0384000400ea0703911410010711400f001d11040500d46c2e56510700d920908002c03070b1810b55505804485a0141c074200034054424020340e070700041c0700800c0f07121b550125031054108028071010 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 856100251 1250 856099001 856099009
    0x1e0310060e061002120f1903272d020306241c0f05030d0f0b06030606280507030e03011a01180b0408101401180f0603080a0807020c 58
    0x40c441e000010320001c0104581c1e04150114206401c02403065500039a2058039440fa558000c0f190440c02c100000351080c0340b07a6240000088a020501d028000080c02c04500031010060195241d0820707080f200e03140c1002810b02240b0744010740f50185804070344086155540b040c101070303401ea0082c000d010000d000a100c448500316022140c41c0c00d10003104120052042d41d40e164500f64416098003440100171404c6e00703d4003030b00c10f485031000319581c7c65a000842d094076200c281c0f00c0c8446082c1860704000f40d0300c40040e1b9034451420340e8515120300c0d41d840640c40c0311300f5240318100013603d440c0880d40c41552020080c800140039840d54200494104d09060883d50300742c102420166000310070205940c45409032a0121440000110040751962400583c550296000b01002d23440310604848a0640b030207507052040a60444810940c900301c1c800030340e01406200944120750768050704040c00b5841e40001c001c0d58100c1600d54a40b0081500a401c8450564006015105900d00e0004501e0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 856101501 1250 856100251 856100261
    0x11040b06120109050613050a0e010e03070b0a05130c15090506040803090f0f040e0616050304150902240306120c0d060e01061e030b07030b0603070c050a021e0310 71
    0x800381007040240c1c42d121030180140806006641d0141d40c0705142e12803601540902c0f070203082010800260b001080003d40e08440320b6040000303645d0024080c43c000700303c941821a51000c0d20f62000700342e03541c510720321110070642000300034841e0100e8a404949010310b8048540e01c1e100540b100c040d0780d43c4403001c00c0b07100c0c0150312034140f15070301c10000d000d40c604001507400810180a0b024481140c1140005820744a0405009105d544600b08100c1c1112145844107000c00050900c0e6203582003d4031101c114204003901181034a48848454045440d8081d0000c010b80040c0c150170601c007806002207070940d00a80b0070038400d400c40c0c900100203607808559030140000080c42522124015951040544090382030001d00b55070ba03c100150104400c0503407000c44d0f14130521840c02506514180c2d50102c0090f00c10310401d85026030f40c00ca942c030340e40c0480e40c11500b03a0800c040840701d070f860510301d8840900002900a0a4038851009404c11100c1074158420101e00341c0d000c1e00c039450b02e5402190 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 856102751 1250 856101501 856101517
    0x90507050906040302063a1a03150c0f03040c080c030c1f03020910050c0d02070806011829130e060601080408040305010203010308070b16021203091911040b06 70
    0x10001c10080006180c440700510700d04070b07003110a031412045181030700c4034840b14420040c90802244086902c922507841448d10b040c2d80340c030400820a503020042036a0321002c030342184e4040e44200100310f61085400a49190810a2032800d80e0380c40c141c60080303502d0f4818031821003d8850321036242458680864000f00021000c2c00800409035810380350b20405214000a000f4194200800845038a90b0301c50b502021105482d00c65603100645006440c180082100e607045411640040c02090004141541116010015129035011410003507004101c03c580100118031200500d0b61300e14241d4000c10180803080b10085916106403140b0001d50368a100e05150783d4000c140052219809407808a4010b030082d54843e04103516070740c45600f2a4001e0301709a5454030301042d0501001030340b00302660301c080ca148114041c450704220281d62860305184500303104c2e0340840011061700081280d0510745240003e283d0781c3d490903044c00d09104000c030025900403070510402e150541132000403a9003403 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 856104001 1250 856102751 856102759
    0x2f030d12050c0906040807080c150913020c060a0b1003090308061318030c112b03230405041505010f050706090b1807081911030a0b010f0905070509 65
    0x3082511010001030400030400e00c0403203818007800503940c071070202500251241c2401840864107106440f443c1a005004d028411541480341e030190030386403420356503807103c20fa40520010340f0365501b601c082e0140082c081c80d58807038001000b00f184140d410509803010242d554114012890300220142c0350504006004150110f010558a080291041c12a61080c03840040d503001c1d14140503404c0001014107500086030103014406112080310070040c01e0004441c0151152225860005065503144041c81495000c0007035000340f40c05200403240800c68036070002c095510500c074032426600300d4040d9900643c5450360110301c1d00c4442c10080240c8205840310075080910800440741c6a02101c01101c03216118504400018061030280b40904006103400c01050040010289064000d501030303151a4414209c0c00c0911265600519690350440c00e940000051080804d140072004031008114103401d100000c1c04840e0040080700b0346803010b40a001648888a044030540940b103100707540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 856105251 1250 856104001 856104017
    0x603180308100f080d021207020f010c02210f0606030303040c152102030109150609051917061603060f0b0c010b0409080901030f061d132f030d 63
    0x801d0003844142d901c080805040824903071a5210111091404e500002d5980e00140e024205281c0512903420221206c0c003e1038103200ca182c0014036840c800700720003030501c03101c1030071442036446080480c0240410b1381e0a07a00c1c1d02c0145400d8968452a058180720382e4014500414124a4040b003140c0c060b0350800741002d9428200640d8031f8169084541c0001400082c20001c181100d007200010020b221000f80142c0320362500e0780344410342d02d6014800e000000e0101c401d200d11364011503800243d4100340c0307100340c480c0b00302580070750074141f50b03000380c003001014900e9940b11440000b24548164a6041804502d5118440036420b4901c580a007100b42d020a210900c51604c220018102c800300301c100104000c460907020804440b84414182d0f602c210018003542c403942c150007850a800903a8104000261a01d00c09440e404e01030029551600412004214600d4a01880c08100d40d0058140000c3c8981c800e400c1d407428581225010021100c0708030002d80c4d16002c0f4442001900d039480f1061 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 856106501 1250 856105251 856105253
    0x703020c030d050a0c0f050a08011502100e030a1710060c02010306230a06090e040212210403230a0b0603120a03230907030b0604021611010801060318 66
    0x4040e410040c820500352005002140e8a00003501466000340c0040100117079a000c032103c01404d85864002450602c00c04010074070300d5551050042d4112040740d015500c40c03241000c4201d040100035549960580d0401e28510344000c0040b00800c0050300503141d0300e848440c40ba0400280e810200c86000b0904103025080001c2809660381040c2188145000641c03035031118480d0101c50086220aa0052107480400c00300d030501500705800380c121810a946501c0ca815800207040c1001080240211049006403590060422501c0d4078001480f440d00f04c1d0705480f28041c201904a80310a40d0000c0d10b100a10340f00c000c0002d038001000319407201802c0c00310f8003071311340c030640c6040500701a80510501d003000c000c1c01c40000140209860617600030580036041c4041074000f0680501c642000341c50304081c003229010000703a0404595202c045110305554400000300280185600200000c1180c0d1044c001c00c0503008504400d103900340ca034841940d80b42c0e80e044040328403600440c1074110000907028 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 856107751 1250 856106501 856106507
    0x8030a030f1b0c4b0503220501090509011707030c1706090613200d030309060c020111091e03030d09020a0e060a06050a0e120c010f09050907 62
    0x110340070440050104850002c08410040b251903000c4030000a0840008182008070320740100c07000101540419044030241c80e00071402d4507078034008110304207071a0806041012010240c1c44025004805d4039114500051955681e005040490403496202840418250301a0040100781e48015000d20b0301a801d01c01004a84096610083e0a034400d10300f0000c00140701c50302da82c01406e0030580c03580503881c001d08035600e00f40300038292582d03030307000501000103501700e4540032000e80390022520f0042e00710000c6c49410500c14201c40a070000c41144900c0f003810b8040d000010990320079103080085100b203010407422150b00030701c40b0810030f000f080420030a183c10340328007a4407640b130610b006801c5c0f40d280007e885c660290403c0383c0c40b16120191a000d40c50a00714903801041d6000507150180742c0600000c003591118000c09051100c081201d64101e8469849410300e400041c100b550345d603054030b40301581c030108410610300146180f9511134203148588200000c807440a802641c094580c00300a07 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 856109001 1250 856107751 856107761
    0x2c0a14090109081605010e01060609061403192a050a1d22021317060c0406080f1513050f0c070807024507080402090a09080412050c10020708030a03 65
    0x142c45c1e940d00c9072070703207402c1c14030a206410007014039890321510b40d8074080001e44610485066021a0003051040140704200d00d403840c0500d0f007100000280ca507642d5000c10761503400c0c00102592464010612941050700140102030380380d000c0d2030300035020394180e03664458007079108821a0000075200010703c1400308080000802445420050305007000424801e104154950002a40c500054042c6140070f20900c01e1a410a000b00d0340d0364a441e0a14001900c2d604000c2c000f0354101e00e840e40000e404503100044240042002003150b1300e0401c241072044084c02d4240c5030103040340c8041003c102c903c0e92080031500320070b034030011240c1011169004c00000604009030826200007445a00e5044091994a41d150610003044411001102d00c40450344840084c400f40c103001002d0244005690b0300c2c29020303030041c0a2800460364140320701d0074041c10700075035014083c1c5a1060740320030108800030a0400034681d00ba00d030344040030b03005a800c81e900d400a01c80e6000c2a0010001d85552920076008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 856110251 1250 856109001 856109003
    0x20129010f030f0c0207050a1a270d0f06060e0702070504110409020426030f0405040507030f1d0c1c080a0504081605010807030608072c0a140901090816 67
    0x4001000c8010264140544844d0f61051006801002d010b21003413922540ba80003604809902c2c100f030781c100c515042424412072418000300509000071030b0201e806949013105003600580030840040c4640b030841554072804c0c0e01110204d050103404103018148059240c4180400d0380140000c51801e414040280070104040072079000c10403001c0303483c02e060b000500080c0728403090464007d8100d981300314200d0031802002c18a80041240b00302e001021019035080c0c402c111800595521100020f8000b000802c1c0030b00040c80c105081000041c510740300c0a0700c02d98148064400214109040095418100a170240d0070a80d040c814801f10362480081c01c044441c0b4244249090344402240d450b001d5440c00c50661480401414449940e01801c00b07500072441e400c05005441c100130b50705460356030502400c0b002800c080e21152500b0074440c200000104c605600c0704140c04c2c40c5c0450740160664101d46030079104084007007234100c401441071590042d000380c20603043c0070198a007400002c0200c50 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 856111501 1250 856110251 856110257
    0xd030806040f0b09040506060a170d0f111e1603121b080c01060317070f0206090607020405010305010b030f0f030a0e0a0e16030c020c090114010311070b07020129010f 73
    0x80f034034402e4440c0002e45000d14050030042005150140c2001909100e80d000b0124007401040001c50301c0100007010400c900f1030f07052448a4206582040301c605103444848126482208002c2e042c0c00200422050706c91804c200b81c03014031600c050000384035103051100501c160800341c0c454070b0b044c1c4100280305848060003002e80340c0c5802c036241d0030080e802580e0041c2d1030365581d40e810820840c9013454170058480c805003403130614005440b40e0f00440811a00071b03010700b030001854921981d603901100c1d40075a004008000e80e50312418060b009040c00155540203220380c41c0103104418001550412004044004514114100c0d40c104e85180002d40005c0d049011044045604a1100d007428840d151015200b00c0c40d210500d0000c0c00d450b4201e400c5019074118000c1c1401c01d45810911a0544880c2007028a5400304040120000c2c211900c803d00701000c0032441908002d0303107190032402001183d0090012004695517513419a00100e990a8041a61032240c0030f254014000803000c00c030141 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 856112751 1250 856111501 856111511
    0x408070503030106030b01230318010f06290f1c0b150c12090a031e060e0f072304090609060c020a0c1203020717190b04060b0d030806040f 61
    0x3aa9481c9540c00a81203400480d40b100003603001940c1c05032035040701d44415000c5104505c0d0180c00446148005044480d0b0f5540032145070f51401e00940020b8100314048800b0804581d59402e1690003c50b08016240c0c1207112044800007121070300c0507035040d5842c1c0e15925207011880021510110668250440e00584403446001d690352105500716031141d510344683e54406c034403030b000741c00d03c1002c110a0590307610600113580251220f543c0142070300e03848980c0f4110f40013481e240041380d092131513005101d2403c00c904200c8200c3c020508501181104084401a90300c40c0005031408922070440d00f03e260084804101d02e103499000391404d640503090011b020300407619800255203030500d690000d6031180c200740007040142d0f0384276001801040c0340b00e941b45500c4c0e0340003501d0340d001c0d20890215030300086001109040c244040b01624441c0070300403201c1e011910b450030f100001140c01303980552800c0240b64050402c1d08051000341d50598910f100c07039951600300310040014001c81042070382c0c2c1d8 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 856114001 1250 856112751 856112753
    0xd030e03010f021c06030b160306030503030106181202130504021309060204170303090606211c0807051c0c1403090f06130507140103021c0608100c0504030b040807 72
    0x80c401d420401050754005a03440592641c030602241840c81c94503807145c94074004202250130981350342e420130f42041456404050390304088020340180e030005009030200000003d00e8507000704928600d504120b403404003082c0d0390b400076000004035840c06500000d6850382c80c8840c001c50350125501520080c803919098403941c1ca42000ca80703a0b200219012540018140304021100f101100e00078440001035156241c0060384540b60744000c0c10003405101c00c1c11440d909072284020940c1850100c000300e40c4501c0d00c40341250308080d03035180c0c0d19003c6031001c40403410191084048a0909400700804059000d044014600078411000c28004105100002c036407101c0c03100740114050307106d18005010b03980000300d0850070f06001030b01c488007a02445e05818001500410b81c1800c80e059642c8200c450030711680141d000e07101d1000340b00c0d04041c9982000d0078000e9135500101c1a00c400d41c00300c80c00610b00c182c100d8206e4520002d9040429024042040001c00340c0c5003ea034014402c2e03060609100c02 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 856115107 1106 856114001 856114003
    0x703020d0b041703091507090303022e1103041b0807060e040209181f14120109020603040305030a050c04030803191b020c0a0f050604050d030e03 64
    0x41800041c0510074205003103c4100341c816a110756900d00342c0360041c0c40700903112000800002007000300c3d034218420032480381541c0d410b400804a141c904000f02c500f0010a0184c03030035103182d0201c1d03400819220b015905540352003081e816101d041c82c0c17914034449808401070307918201078907404022403140000c000701110f655041000c0e82d030455002143c040e226400070302d90050400d001d049107080c0b8142c0814032403c103181100f91031782c0794046000088203107031084031100310341e4000e411010300d042070900d549070722403400000f10080c096010070b0090704101c07400d40c08118040108404071209009030340d4080082c007503880c9040d0440e51103d2084c040644210030900d0885400480d03902241d02c50028170f60410305582842c070713031318a0081d901c0c3e030030080d51401a40d011600041e1072985114401c10356400400150800d410681407041007044245c0503410041604010380c41c68030 = true := by decide +kernel

theorem cover : BRFrame.Cov 855935251 856115107 := by
  have h0 := BRFrame.cov_init 855935251
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 855935251 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 855935251 ≤ n) (h2 : n < 856115107) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
