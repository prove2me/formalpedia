-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2025
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:28:42.160652+00:00
-- url     : https://prove2.me/submissions/bb5e09a7-b4d9-45ca-a0da-82caa9e22a87

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 364028776 ≤ n < 364208633 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 364030026 1250 364028776 364028783
    0xe070501141b03090411041404090f02040219080601140f030c041805190915110c070f080d0c0804092406120f0b0609090618011d0901020913020a030603 67
    0x20042d21400c40040002d1841c92400c03103003449030042c039450444040c407a900c1140c0d01c0c002d0313402d0f450480d41030275003100100c0c50149603440080030b0707560003090681c0d010744051b100c10300d044072501c07404580115245800c14800e18211224050340460005a40b1542a0140c00a00044001005c450034601140c020b41840200a22a100c00c1c14601c405450305842591130880182d41c507420100701445040c58968112441c5600100280c000400030f0421803c0c014800f1020000304503144000c11203100100300d42039054000a04e00a00d150a0040d021205001c001d48800008007041d410401c3e00d0540d0041200020b001c6540d600a51800c6010302012104110501002420381d800c05884010622131110500240300c03910300311001c42c1c0700b003001d060b80803c0c1400a6451810a040d01550040b0b001d4241c01d00070b050b4400e580ca007082c090780942c04010070500340581111301610b42d141c1007003500c0001d40c00e00b1125800100f1100f8904029500c40760f0205d40540c14500c04c0d000380004641 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 364031276 1250 364030026 364030057
    0xd0f09120c06062103030c0926010b0316170a05150106080a0603030909020f090d08040512030c1e100608010b01090e0f04030c0203120c0115090e07050114 68
    0x18140d00600101440c103000e99070180b8190000a100000d400422848016082c080e0810381160b0340581c01400013440c88401c04c0014000491064400100180c019000c0400b24103039001c3d41d030105087d1212640c40d1070083c0c21000c3d100410b10103108640d42904c8115a140c1c0d0f0702e1a40034051864a0420140603100c2c2c4200203800310100e100d8001c15058402903541c0e8003c2d940c0c2c000c2c031070341070b642e85103c01000151302403010041151941d014088040304044d68502d048440c00001c2d001d24815401030b6140c2200260030007481c6000c1c0c003088039903003964002e54244019032111980703450311101400c3c4103c030190301c0e41d00981010b104024410403a420100402d0341c0711380307049000340703010036142d0f003c01c030b04513030200d45a1280c0400c18411480031f48089915600c0e82d40845828602403800c03a007510424140c0b507812000f80001d0b00c0000c11030b100014400c820326008100760202580074950f03052401803032000304500802c00005031082800c040841c01d40c0011003460b5846030380c4c4007201582c1c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 364032526 1250 364031276 364031303
    0x10308031e070f0e0117040809010309060e24090c0121021216141c060803040905190504030203070f030513080609070e0601050316170a200408030d0f09 67
    0xe800410703a000007a91a604d040b07201d6111401540d00c80d0425114654110345400000e00281d00b11004040815041c5000709a01200d0758400c0c00340d9105000031207144d0440500046040818102c03511a004044800946070a100e5052900e03064246c64407410031140c0411034581040100d40301c45001c0800320115030f81d0798140090340c0c0e56017040e107603001111a4241010300e568420398104440c03a10f80c814280c03604051504c24510203203c0c40f42510400c0d11f40100290054003400038000600381e403030000c50240303030203135496134104200810202d900b40f0782414000070075800001d54903002d0340100c0207950110035050942c3d150242c901c2c2900c01c0c081108010034400c1010138298086d9000310304440c0800d440f102428030305e0b01c0484005d40090014000944452401c140c0010301484c0c6050840c00800c00f94068840700030126140303031f072140c0c440d140c09480f280d484d00e140c0101c8042c03104142c106400c207480c0036240e215400d0010340b1107866a4034008000b60300e81c402d081e8254010700100811 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 364033776 1250 364032526 364032541
    0x2070f0c1401030506010f05040603090c05030f102909100b03100e090d020d140408060106050711040603020102030a140909010806040b160504051201150305010e1002090603010308031e 81
    0x2000c1c82521280080c0c00c4c0b8000c01c0031035014041c0d6200b592159203415061501f010700440c020b001a610650386070802c01c1c000242a1002d020743c50b412031111010703100444d156003503001624144441c49030704480a5940150f440306c050f603842030800c411500b201d016210180401c0c454801900036034900354000003400204a94100c1c510200c2e142070304100c440da1340d90949035450382e00c6444500090b03005503071b0384070003e4030038003400d00036406145149042c152990318446c6012026000a8007041000030140103210f101d05040c0c1002e00b08660502549003540c2c0001e44038000c001d1207005002c90308441e0301160700c2c0e900695510b440b018140c0c200340d69603070503d503691743c60030742d0306884054181000c03030b55042c11a016003008401a031280c40c600340c500400d12440380117042c9944055540c0e01c00c1032000300401c212103401180a0300001c21004d58030700c64141042030380c7c0b040f075041c80d10400c8804440d072112805d887c1101d07001001661a5070351307031000107440107080d6080c607118041ca201700000c0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 364035026 1250 364033776 364033799
    0x20c1605011202040f030f0f0f0c051807090902030c041d010f080f060c03190c09030b10060e061e030f04060501051c020d0314070812250302070f0c 65
    0x300e8100360ba890300198240d2585004130720440c040c0304984100d49005001050900503400c40083c41000c50480802907030f22001080144840c048400180160081100d45000c0896180c80b15040f04004000d0600b1803002e1325200c03051090290094020000507660030a2005036401004a014040c05142281143c5480c240090003050261201c4c4000410b925a001420314a00d0000c90024072064940d210040d406420040c4a04d21072808a01c495045074168080e00c0e0240600b40c4880b583d80e401e5181071850fa100c0148020f14203000410200074041e03001000c041120740c180c3d0718580c0d500310365400402c4a0101c0f2010407600d4000003d00800e084210003d40c4194095803042003e80d0301c0f1000c00c101880c1c50003981e660403c180380144c000d803909172940720103203102c0c1c28402c000290442d4094051340000703c0603542840c01084810250f90340d8500d4661064a421031800c0103040400102000d11802c003c0350f0401d540400d045007008103946850603c40c1c0c01080d03001e1502c0d03854442420 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 364036276 1250 364035026 364035029
    0x30b252a03180902091c08160c030c06050c010c052d04030b13060b0102070308040e090f0d110717060f0403020c041a01030b0306060a0b0903011d060403081b04031203020c16 76
    0x1101c40580762001b445403c00c00040c032030f610000701c919002441800044007200804107848000a03001d00100050b407480e03c1d1402006c5940ba415100c1540b190a01d0131940243c40342c04c01e00008000302801281181d6007405901c000c0c020600120520f0791001100d4062a0001060076011205006034007118642201c3c0031407140c1401d00c004491240120307210b085074030009041c807009000a1003c841c4010306568418840011194400c04010b1102c0c42c0840c29140e40c400306510f0703040004072303900603c482c2000d4003010382c50005201f00e0080c580e81e1801c00500340b00f8140c50700390205040510900040d00407500090050085c030399a543d89010080f00034540c640842d2500110101c81d050101b0074034865000105402882072620100c1c40e0a07038000708140d581035586011403d1080c00ca13009601d079003411100200742c0b614045c5006050311001602c0701400180842e42040f103a81036408544c140d0380d004c10f20b83c0e44000413940581c0640225400e1403014090208110752510050b02c80a0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 364037526 1250 364036276 364036279
    0x10501031d0106031109090d1e11010c03020a12060f0509040c090519051e0414030d1104090605010203070525030f03020115050a03050a060203040804030b252a0318090209 75
    0x180c06c0d85544404542da54800c4800713102049400101220089041c2c890409088190900c1845000781d640d921f400c5a200150301404a540072441c81141c951100d4209015a0000c8013000b0080c10040d00158444207807051612648000c00081d08000e16130001c90010400548140107a003001d040750880e0542d4440b09168040c9820000341c1d0807405860304421000910200e6081174907661950240ca000c1c0d00c089503003520003001450f00001051003081140c11510700b0749610395081010380c00039240994003190442d4000d21842c000f01d000481c101c94110145208603034820a0140003950101180c1d0001d4109440110584141a01074000b601091003d1598582032a2a2404c1210b000101d00010382540d118549640010381907a00954025000d0110681082d59950311005001300486070200050302050081da00d00780d003a0615040c0141c41c0c2170007454444508401034100a84404008448003009150400c0c54098285106407541052007e104c2c43e844140380da001c1e501295655 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 364038776 1250 364037526 364037539
    0x11d010c1a16030605090609101505030603150103020a090b030a0c090b010806040e030403030507050f0604030c0b0106140d020912010f020702030708072601020409022106010c0506010501031d01060311 88
    0x10070720b94401d120b4003090316401052180f1540f240d50030300a42c244000c040310100b450180c1d01003600c81c00d040802400e108a0b64645d42d076443e00000b0300d401c2888614042800b140c0c004014001a900c0910b0319095841064000a05018020009240c03107008540605040d640709004101416680c002d0304035000281c031456016100c01c020f100441e0107400c1c2c0b014094205001c1031001901c40d50080000c0c134002c1c41150380082c0342000c29402c0000070341c0c0c00c402042898107031204114881560600500c100c4c00d0200ca2010100da10f00624411f20b10052030701a80010f00310316a5481001d41100c002440c402046126004100b0070700a522005c0141c0c4240b02e19140081c103510002007100039607802111a41000c1c20f00484442d80b0b20144002201035502804007080c40e802d02e02c042d2141d00002c82005000f0060078034801030041c0702800d81410010002000e4020a40015095045450038600000d8050031100204480c0c114241e14264950910b000003051041e1412029030404086842 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 364040026 1250 364038776 364038811
    0x20c18040b150f011206170d0f1e051b010c0503100f05060702100c080c0319030c1707120203180105010605070f02010e01050d021306081302011d010c1a 67
    0x410b03009040807041c89510444040c5440e040b5481884215a101d0900d003000c07481d1515000c45240b0024940090700e055170280702d42c6843e80354400f09115445205084c0814178982500d0245008100e500c030300e5042c03000c0003440c282c0d207038481400d00764800f038883c0013040300c0400100700034510b90040e100f98411124040021412203503411002e02122002483c07280b5100180d800e021648060001b40c9092081164013180465041802814800d00c400702440c0ea50203003100c01c0c2282d64414400d03104042c603041c00c1d003c2b000e0300300f0008000d0fa0346100000040d03683d0701c0c604075a808015005000d1050010041c4800360020442200d142c08444009200581c1c9a00c011030740c034000c0300301c042d060344030320700c580d01c09035000c0d0b81c041003903d00614100d0b00d0f0006801040050b0790003e503400c0c03e01d480c4007004102603680170022981040c2c1d01505450703c00320300d8000070020021884821200b00080c000381541d68010f41e60710307402c1a4446040b01401ca5085006a02c010007151031b00344a01541c0d14 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 364041276 1250 364040026 364040041
    0x1020706020f06040f0203010b030304092414010c14010603050705180705120405070e0f041b0b071704050a06020a030e2e180909260306010f020c18040b 67
    0x18403051000444004049666882d110720b0f000511544041c4d807d9543e0f01c0740a5034684092000300042e0002c054042000d000b61100401e416400d95203207100348074900301c10701c00c1c00380c00c460400709400240b82c1110b04d05d0280c240740c1071150b1225040c44041d031901c0000020040302094217801c48200315507a005142c1940c2d1071070601802201c0c0c50740007070001c00181240b901402107440e00b16002d42c0444078619120f12401d110403c00380d03032000710603070301c04d082200300a5040158440181450400b1f43d00901d489000006809003002c001d1401e46440900c1d4040a008015180103000040810001c15a80c1401945800e20300a0640014060414054007070030844248907201140038103044400e0701601c40342001403e500000400c1010b0012a146482c2ca61402c0034058860b00c0700005100e003161400d112504030205112881e030b42d54a00180c098a41601941e51000003820a1011401008000c0b418100e4030000c640d488000c0e1886e074003041e40c0040c40c181c400d40c414640c40d9900d448200 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 364042526 1250 364041276 364041283
    0xb031c08090f070308070302070b03010b0309010506031c0309050c0907031b0201050402130515090a020904200301030303090c08060a050109053d0306050c0a080f130b10080f0106050102070602 84
    0x100d03082003c3e4003460040002405110040103041e02901c1540c01140d03e50083c0034455200383d2000d4420741e400310502603000004c0c41600d4002c1d1007100242250502108101a40310300c04003c042030603510816034042c882d0038459010884801000e8922f00c4c604003902030010901c4090400c0c0c00320034a500c0e01d1000780140b00b464060782d0000c0c030211122640c5040103028200080804602c002c100040754200d4031070340c0046020320841800961110488800d1104540120302401e0409847d40740ea003984e045440704881c10f407a010314000c6482c400e00d0908120511b501d03440399990b4454007003042206203959024034140c5980f8501071049440d07210010395159203200c0c200380518102050321940004030250903c0408a02182c00d150540d40d886800459100b2220001ca41c00006400d41109500c04115948031380f4080c4030050909020b0108250040d1103400108490f04500129040700741c420310600040c0340700c1c0c00304c80846900000050107030245101d0a40940304d040c0340481c00782d0010 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 364043776 1250 364042526 364042543
    0x70c0f02060f0c01020a120507050405010507060504030306050d060203010503011a0105390604020405060406080a0809060d0e16060908210708220b0414010c060b031c0809 75
    0x461412618425001c010082c0e1200307a0b4910340c070380c1c00c0050035072001c02070001d071200c50300c2500c03400c622005840c3c110040d9040100070000300a01007100b44410b0ba0070005071030515402c41c40003e0305035074919040d001411a030b0031181d80100403c9203030081001540081d4140c440a4009005001c0660200600e080c003580015001c9002801046405508040030f003506459118030107400d40b011003500d88604031a8280fa46182e08114200002d42c00d2a00071150090b409035000c000042c42c050485454960382a4000d110702e00000c2c0261540d030703840c815200000d001480810590895220070b1380d440c46066200c1d50782d1240400c00140c280c3c050142413044036041c0c1c0103804a150351a2001802204541c41d04070340810600c4001701091011001c0c0042c2e10380521290380d848084402100c520805500038558940108814494001100c1020211034000c1c01d1401d50260f140c40c011028140c000c0c0742e980c1505c600030500300c12140700521445854525141d00802d44c489200d10b43c0c61740d164 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 364045026 1250 364043776 364043783
    0x601060c0609050c06030109020d050c04032312031302040f15210c06030c091a071e1202060114030321041a010909020f0102010c0906030e0325030206070c 68
    0x201181030340414000e4020500552045003500c2d4480084000030310b080e042a04071000c9240d000c9800d8180004900c242500244201c4002c1d051514503a580b4070980a8920301c46034410490206003007914040060100c00d0451042991301c1389088071804402030071056060740700d10f081c506480d4035030302c1c1440780c40700c100005030038551207905001c02074a0106050000607241001d004006002c2800803c1c400d0282840b6540411000020140200010b07041d40090000c1e4242d81d0020346401b50500407203510a5000c446102d1017009000c600c1800b07444400058440780f44003514600382607003c591281660800004410320780304540c103169881c000c0071529568000315948902c0c038800c4640050340d1041c464899080c0e1b02c0450a81e48e04640400ea2102600646600041e002c41c030b024031420f40f81003004c5c0300800086e4841d00700108002071900c100014183d440f6005c4c1007200c005c0c8101e5414032001003e0255070080c49044001050310040c0c154018012040801c0c1c10303510030744c004ea113610341 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 364046276 1250 364045026 364045037
    0x60603040b0402040b0f03010207060603030905091003150902040c08040303050a0e060a11070f0f0c0b070503180307080111180a05130c260f07030c02070311060c121b060106 76
    0x210b60307081c0300c01407142104241d03001d60301c0f503503003030300f0765002d00050454500c1000b01080e4103141d80342c0500303034221980145210b6214401003041c040c0f802c21908081320b8020b03010003080000343d8000b400802d600300c0c019401a041001c16090b41d0780110200780194826076040005544d4185080c2c2101c09032420a41681c1119011421301003080d044641c0802e40707405000c1c03901c02d0a07550345410360307000d401c12560702e02040420070510246290600042c1042d0f01039519003105076459075280e11034414402c51804841ea000441038074200925000f4000000c0200301d0b203601301c01001699080302c41c40c28902910a041e03030200e41000c1c40b005c000c40344080e1501c0e001310902c61a4201030b001c1c0240c1c07102007141c1c144901c240c400840354100000c0f4640c115500003030508014030030180c84014101d4003032500b00340444d5600d50340050080c048940000d807204841d21284005141072040a401141510413425402d1240c100d110080c00d100d00c41c4034800320703a00700e0603030b4094494000b44170303c00120b034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 364047526 1250 364046276 364046281
    0x51815131712130924060e0f0409150f06050316050a0b030a090b04032601060206150102010e030c011506020607020606041e050a1a0a0e010b0a140a0f08060603040b 72
    0x2c1510b80500704806940b42141e41250320340f00b0311000c0314002040d20795076455480c03005244030101c110130300250605141c40c458840150020412090f130340c5044038022a40c4c3e4503a0300610840e00103841107c0d0012000307000100d80142444085c0807a4040d0910074041c4024980b081107142c03614004417440038040c0003885203010900070300d0303400c001c2850f4901ca8a81142000240c60031030b001d80704501c00d03200d58040d0620070a030141003401d84030304000d60300b0842005008242c0c0024860340e03c904007a07d86400300c8040300040780540030003507080d6040d10002c50054140c00c010740104005804501210a0b021b45c0c41904980d40c0000b60756410251300b1900210724103080c143c00c031104401109440e40c02c070300500302000301180c2d01200c07101d100c141c2c0c40500100c041c0e562180c640c0d8040781112039449250509110088004040c07244e146100e00c0019190b24641c06100b0340c0f4469124030f03403211b032103200d84a005804051010500000204d031540042c09a2400384243c07401150000b11051807503 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 364048776 1250 364047526 364047553
    0x203030609071b050706080708070c020d0206181c0b060315060603040602071a0105040f09080f0a180602030904050c0a052a0709060510020d08070518151317 69
    0x180d24110007054a003850f002448041481004098010b107015a50014245000c1200500164000c0c0254040200106410000d130f42c131140300010047d0122006951803c60b0807900a003680081c0b50140c0108a91503140c0e90305100c00c7c407602c0c08600803590b01c3c200390b484504140d150a010306001c0301900d00038000c1481170428502640d405840303083c1c0180b80c003245440d10104101c08050b50319000203140018825420640511440f07420111814868040701c0d54415015024403216039890000216514960074480d01c02800241410624819650b0300e8600081d12035000d0b940d038500460912020402c0031a00004960078011203985150408200d0410281819a15901011042030540d60300d1100c407024441c40f00102012003002450915003003d010741240c038030000d0001d54000885000d4020340000e1003540c071001d00e203001c0303a6800e201021100c0340308002c4507058015540380d03c61580250341d0801044a0404410715800156480701e0680d0b42203250456000160400711442000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 364050026 1250 364048776 364048787
    0x1d030c1504080d051812040b090108060f1f030e03040608130203010905010e1e0c0a0302150403081801171b0c0c1906090b030c0301030f0201030e0604030f030b01020303060907 77
    0x400d11a00c2ca20307250105032030322101a07600a50355103044d541d2280407000c3c03400041080501c0100102e500504051a0010315891801108051414008540d001902036a03405040204900c0e0003040d01c0800e1005440d4a05131110343e5041c000420315040ca40d240c441400000c0d07508490840d56400100d946860313080b001c02407040012a015034a03804c64100140d001e0144105032081a4000c16403984520503a85040841d44201101600480c41c91030460316034150342030a894050741c03140264400d41d8071a000c684903a80c8007611450011500020409071800e074504065001d0340d0346882c000b407a00c108031020a080c0da612201030544100c00103042c4403c8040c110303a60200054410158108e40480c81070a10250440c2d07248226100501c221900038507602c1c043d03c00c100086003907180004800e01c0621040c00044d2000154400100c00c40e03100e904404511004502a84d920b8202440d014000c88104014400031a040c204013601175480002074a20410006100034055100c00605480 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 364051276 1250 364050026 364050031
    0x50121021305090115051906080606070803090a02210601050906030c0d151103130303020d02040b1206100f1403040507030503040305151b07060b060412061d030c15 72
    0x30007142034549240032561070720946100d841203900100d02200c1d0704190803101062504101d114a04c1480c0c1c2510720744041c0305440036540e0b01d0800307070b070552140030000d001070007010002007411a00000700090b150001c60b50080e007038420748045000001c42c0841d9100845d040030108803503030004004015070701c3d14443e030303c0c0c00020240c180c4071700203058400b040640700001010f603507004e01401e004907045000e08c40c544036006036860250460070810165101000c0d150030240406030045010300c0c0040241d4101c2e002408007603c102d0b40d4aa0b50720b4215a941000c4580390710403035042a0b0441000c0c0100805c4a40c1c10342c0366038014241c080400b4400481d00050300c152200d210700721020000030020001000514000c0313004202102d50308202148101c0300404000348aa4440c1080070507079040400d0354903035a4041000303d4142198008030b1007901079944403441595200458070113110445e406992254407080303d890010010700071070b507900c1c4518420f610319940104038125920404228164 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 364052526 1250 364051276 364051279
    0x61a0906120a0e030a0e030d080906130201030204090501060e0a08010203090c06030405030d0608030c07050d02010e1002010e01021b1002070c05090703020c0a140105060d080328060303111005012102 87
    0x40c110450049044c9580c214088a00100b03142d05000c0036945000c101ca03268600030b0b4a045480d0f40360000242e034413107a02400045048409504e0b150441e0302927010340c0c0140c60b45500c00c00543da52400300806031001942c0c9607000304c013a1280071603c40e806008880c441e100c41c0f80103007405554030b014420030358001413083e10070707000520011004800c540182c000a2420000440e2903400c1c44507801c1c01c06945600c82031007445100751050044c2d8121450000b000021903040c011075454000607809070880600300841d03548002514480c410006032283c003000301050444101d1000c002c0340d44124421001c028100c000c004008201c0c600e0410000b0754021000c1c034001d8200400003407100d00c1c1103c0000201c0e81018035409082284009200d9942c3c091800c44084110f8005a120b4848611014014154078035071007480211042c0b0102c0044954030005104009032552070400030003d040520210703546002e134203804107200d01140900c1d41600d0707102030400500b42c0724041c6448000c81c00c0404a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 364053776 1250 364052526 364052531
    0x309030c090203060a120c1206180308071101050f0a090f151b0e0f0f03070b03190b0108013807050a02040507050f12100e0406061a0906120a 62
    0x4800a10511500e100401c101c40700580c5030306100017000481d001d0398001d001081c41030120640814903001c1c0322130445181d00c2c40b031112409103041030005000c140e52140d842041103602d090404d90720002803403040940d5078034128040c800c0300c155400e03181e094811605034612400400c842515070350001030454450134403000c003d001907079086c6140104188080750581d0f91480c545611000d6070305100100070514028103908840c1001502c080080c52805d402020500f01401c07150b141049410090310401c0301094403441c0c00050035440c04081c0a0f01090306007083c4c1c1c0241c0b00e501500c50b00703059860403495aa20344c4807003140662242c04610f000380601403c1e00a022103032180780c2c01090751034040d0740600b00015a40c0107001c01e807400a400142041810041e200f0480010020382ea0540301ca4921a0540d4807182d0340348091540d107812041117004074509000400c2120ba02900c121800a86010000d000c803024900702070144d541596000b03076080041900001050400c03550150007080c00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 364055026 1250 364053776 364053779
    0xe0411011106090a03030b010c0b13081b010b030717120307030618020c0c0919021c020c0f06011a07080a1e020d021b100f030e100506100305071b0309 66
    0x780d403400c00165410100b0b90040880703081415030502480029403001c0c01c101880302d14541d22840c806000400c2104121603202d860010812910704542e03100340306207001c160b4001110703501d0b8004c00d0610031892091140d11000a20520a0401d500d4449501c40c003804070b8100001c801d541c907038030043c1440101a6904c00100304025044404400c0c0c0002c4000180c8034401c0c0c41711986815049003105204000200400038a1480350f10fa080410040c080c2c05601c40048030030144050200d0300c0c2c04044240086a001814440041c0d22000e684214003100c00a9a0785e01080b09180340006181072a01020802c95020842c0080200b41c90020307840d11040100075001d8040d109800703002c0700701c01070300800f001c1c5444560400c007400c0c014511010402c10505a4000a001c82c04148448000c3c00441d000c0010f526000c1c0d8082c004840402d070a8804d036014408604c0300030720044411600c81c0c4026400c01d03042610074803607648100c0b244c0d00d91107001411211502c0c450444054106c0400182c01c50 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 364056276 1250 364055026 364055057
    0x50607030c03090f0f031a09070b18100c0b0109090203030f0307210f0c0315121a16081e01051e061210082b030b03011505040f060e041101 61
    0x20424000d201c01140350b031600d41503107030040034096001c812175047c41c0c00d00e040c00080c40b80405e85404aa400d4900c0e40c3d035441c05012801d0550384001c01c1e09500c4041c0a01d40041030303801170498a0300510840900160741e0b04c0701001d2003159183c50b4060f4040c0c3c410b12007800500104001142c115030542071002e5821401602401c881d0214001c5591454543e0200c201e1455a8040c5000340801420300b80000e102d100800c041150b554880c120f140b940301c2e007c1a09215074210036251001001621501e1881c00c0910313005210321440220f000294030a000403181000e1110048850f401d5990540203079103481c040107026900307201049500000079404840d159141001812800e090341c8a5098500d0114404007511900f03900c02c4103941c012414484c03c2200d00f0300503d00410081c4c007007440050140e2411001000c0308041c05406603e002c0c0034542001382040c0c600110343c0101e4013031108407102000202038136a603200380c1070035800242c00326001401500119072500c0e0189011203601110b40d8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 364057526 1250 364056276 364056299
    0xe071d0618180601060201060b0d09031b11010f050307050912010209030307050c030105070206060607031103091e1302040f030f0609080a09061404030b060405070c1403040e10050607030c0309 84
    0x155260114140c072414203810060030f100c5103006100700d000070410b8900e4112103241c1403103800281c0300026070303a012400405009004420260000c10050103ca548515080d0b0780341134250100360101c0d510000000105210700100d901c1005990b0f12a41403610700c9040c48601c170620714020032155002d02c5901e2054508001500703403280580003e020001145090600b1510007400980454100d58100149070b02c41000310f4402130350606c1d000a0550144032501e0030760080b8103641e41d00c90040b0302c0340c0450060880381040568012684100c0c10000103140001700c1c4100c0c40b44078400280701318100f01241e1200e55841c10980125004200101581c6e5503903825031206502c3c5020507291030041c8009540178490242000b4500900d9281904580310f4007050a17005120030300c2642c4600008841900c5a046120a03d40c812044695001000c15081e1a41c105004803010b05064400290726091345200701070403284050708440ca0700305a920112004c0f0384268003542070100c600c0340080d00c8417915 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 364058776 1250 364057526 364057531
    0x5010f0506095a010507030e03070303090306050708040203070b0f041a1b010b01020703060b13060321140a0807090b0a02010203010e0c1e03090f01110a030e071d0618 73
    0x40c500c03c4041410f01e10190300b40d21030100c1c80c3c80c480711207a10035480d0003a400a08103074a0004d0a01586400c1a443e0850320310b0f00606005801d07020340c52001080581002c464801c0e244522400d00c41035590310800c84542c0e00848003c0d6255005070070400c00a0004001042050f00c00403401d031506403620b030107102d6524442c101d00000c42000488001138090042c0e00b88604180000a1140c1d0f40300d640000e40c0e54a440c0000307041d00755103410202650740c1d43c0e40110b0581407909428401c0030350703d00308040d0810411000040d900045c40f9080d05452040c4140380800a501010781c2c10030610071011210442c00408140a020240318007243c0c1861040c007402034402203900143c0e6075070502071103001ca02000340805070303282e40a10566020404c980c0684070081c100500c42900c9030b1b070f1040035a1034605030321a68003086d442c00c050544100429401031071100384ca07031010321422105004142e619001445110484ca101550806803038040b10551908540014000080043d902c24542c0c0454003e = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 364060026 1250 364058776 364058839
    0xc12010b0405100e101805151309021203040501050d150321350601030f02040909050d050c120903010f0f020a080f0112021c050d0c1505010f050609 65
    0x1480f410090040c03c840715a90260382c00c0100c4105c2890159107405001d400d148030b0300190b44075000035194440010f01c0344010240107180c0c0000360f0001c0d001c02d0086c4054081680100c5680c54110090440001224111401071b52514544820303800b13004014036819100616540d42030800001194a400c845001241c142013030b40603038020303980c02030001c1c08001956135400b0444264249000b03610984000b025200d01c0140c800d942c0d82d000101d001300078a40d542d601c41880440c020510020991080b2459441001141c041260000c826543e5010340c104103056030f0312480646020321010800740404006c050004218031a0500e06a07065600e44010100c02c2980441d000c0b800c0790b40960000d8120150503080340711703075043c10360458610360b511402901414000302c1d0540140481e641d03160020350008107a030a10320b4507681c02000811140002e803119540e012103941804080d200e480d048a8841e030060080d84e1600050040e10740041000c01d5010403441450801030360200300300c0018040 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 364061276 1250 364060026 364060051
    0x40606030b1e010905011d0618270a020604050d030c0b0f191104061b0206070b090f0c030a150e01050a0506040f0e032512020102070308180c12010b0405 67
    0xc8115100850b60164050440142424010450200c50207440041e80c01e2101d2020442c4c0c1e204c0010829452098494101549080c010802000070340c94401d4404443c1611000c10b01c00750724030150380c0d2030401c100a5400391041008009a00d0000c07041c10401c0d12900f00f280310fa0740d01c0d407103542e051002110321400c0c864080c0e00304a541d50030720502101d4207103440c50401c01d2100000103014280203a00541c0c090041e296604240e401c080d2206000c22035000f8000e07503907020285000c90440e00300782e032800000d01c203008401444030001300300411021405001001d680c000741d203403962102140303c40d1907285561140043c001e05000e010741442105600c00103d030905280c0103110071100d00b0700241d064075151400304404150f000c811074054003000240720041c4140c40014024142171120010114880091607400a64040d000341103658081e442d18421580c46551080880c80710010840d000c2d0030054003d40240380001140e040b0f00311000001410010340c90200302140c40a81d0062503045 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 364062526 1250 364061276 364061311
    0x90f050109030e010327060b011416050114150609060d0513050c01051e18060706060603060b1603082d060a090c090605070305070f03031401050a050612040606030b 72
    0x503050700a1b0700d50350140c049080da02088501200c0040114000002c242a850750080300490b8802e403c0032140160450106a59060711010400c80b01e0107c98200c816500b003160362500f510084c000743d4411030310b041c9114031807000c1004106207540110b6025034007100902140500b480140305080c030855442e080e07000401c0503420120b152a02e40003502e41040070070070040c0300041103d2000c3c02740413608084217448030240070454000050ba00c030800c1d04500041074041c18844140c10900498071540c40030028107440340900601d91082002c28909c0c030310344005032400039200f84180c7e0b5000f07054080c040b0b00040380510400c180349070861f1021a030305220f0240403141c900304a0840c018000194200030030807071103801812556084c407481c0280840820040c0515008408a03404541d001424110507050303440c01400030028a0203400f0040c0f510000843c06041ca42008401d5400040105042040e0b00038140304000c0010030494a490311150000000b4282c0c00189000c0d44002c40741c28001c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 364063776 1250 364062526 364062529
    0x1a13090507030f02030705160f0605040b1605191808010f0c17130b100b12070f030507050f071403160201230d02071b0305070f08070f0504090f050109030e 68
    0x241e03030121003d41802d204005102d001c0c4d810900f220700103007140c607449454a01900f00905a031060000141c407040c2804c081004001024078094030400c1501261000b0b4000300300100d8841c0546100000091b030f1301808030704d03601d004403c00222801d83c91280c41301c00e52640c24040c251908141601071254407984181e005035000740b0041606a214510701a5520303150384148a0403820090180081002e8400304007100d260350b003418041c0c0080a280340d0365441a000c11644810221018000901c0d62030500d58603034030031b0090314065402541c0721420010741d5507071201c6179400a4800c032003c010398400b1842c108800e0002c2c3c683e140f000c0ca803000c1c0d18100c500000d055181c901070082821ba1601c2804840e0440d5101602c21447c0034040040e00c5642e03618000800309024446180f0f40121204000204603001900302c058950714021191440d6480c192503030f9586950289022811204406018500f01588110328040c014087c01840103a680c0b6842c0c2169010001a00040c0c00030f076080d040c9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 364065026 1250 364063776 364063781
    0x22050c10080907061422050901080d08160c021518030303040b0115300e07141e060a08011401050c0a110a0506120a05070206010f1a1309050703 63
    0x4a0650074400002d241c9a0041c940340c01d118000c1d0300074060004101108605800155140d12070b05011200c030f86c0000c0301079200314901074464540700381384100004c07072907840205858100c0c01a9445000301c03a140c00000c1c1041c200706417420390810904040da40c0159407007090020f81c0c074440300c0102c0d80d07880454003441c14a4051030741d00b42c0070754410818000000c030002070f8141114103c006e4001c007a0b52a20b400c0740c1c0901003404a002c01c08140d03074226444c0154011224103559092001c2101901c121415a00c4000a10480c138120078192069501424a5140d40c081044c070401000015641c075400140503800030081c042c0000c94850043c0601820000c004128480900b46a42080000f4103500daa5540308d03a4000c0c40011008600c0001c0c0e20b40517583c90241c00000c10031610781d0000c13411840d0480040311080c490504100114580a0010510034180c4a4070000c001300c803070506400c9407003610621020400708104100240900901d16512000703801402c03408030b4075040082e0002d09 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 364066276 1250 364065026 364065049
    0x9080a08071407150510060804060915020d0b01030b0f011d2b050d090323070e0108010c080a0c02060105011815050c0d02070f17150717011502030a0822050c 69
    0xc20302c46c000d07400e007c801d030094103603903000d54402d101040c1050f080c501049001c10101e03c40d450310307002003550340304040d55400450307400e18280c0e0100048205801000301041d052041640460f030301d03001a1104140d2002342090a04c4d000c3d0410200707144245070440a41c51104203030b64640324410b01003080000c00d00042c0840280e40c41d081c3c0c0d00a0858460450140c045400c407031492481581021460fa010300c40748004040c40945c05036070b5a560740c2114040c007007010b0400c0c0010214000201005440c2c41103800195095009002e982c1c20880151003924085811084840c41b4a60014510b1481d6080310942038040e070700c564444001910440c078200034008441c043d500b0002e4180982c4541d49510030440fa503004c084c0701c3c041c01416a842c18103079104811407480307800c94108085950012456030b1420743c0e9282214850780e90b04841c0c91040c83c0904518010781041100b607804511900866810004803080c001a100d103600c0c43d1300e455880c051040715290481d0a1150107840c1c00c240150 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 364067526 1250 364066276 364066291
    0x50f070c0611070308030c07020d02040507030c0323070e010228020126070323040f05071d130c050d0b091902031005070504030f06060f0909080a080714071505 70
    0x383c1800c4d84c0d5404014003004000c0d1042e200d0120381c01c41590745c0e20140c18201500070700100060b0400740c00c02009440318900c2103002c40c0c202403884244107803c07101c3da0718901c01c80f00e01c410340fa01c0b03119048900001c0c4109140c1148200c03101c0000510038001d001c01585500081e440d4050071610001d8201c0c65a000380c1030101951011100452110b0340725035a0000b168580080d2180c05105102e030190f40b00b0094030258035440c401c0004000e0700e04c40301c4031118020b40480d898160765902e0b8100203044401d58500d1300c071054020a050142800d506161240b00d0300c00ca60740180c507480843e038200086141900e81e00040c00078814190024800c0c0301c10140c003c565505010f5541c1c01181d980e000f5081005016540d401c0081c00d1503105006940c00385501ca080e000d2400c1040c02d209000d010140681c51828240c00d4000031401418403820412a034004411400e02241c214255240c4800400c0c21050180d417284e01c0880d081080010304005100700d0500e40c2c2c1181d120b5280c012600300504c1074 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 364068776 1250 364067526 364067533
    0xa020d081e070f020708191109010302060d0902040b10051b0601080c190e070c050601060906090e0604090506090a060e120415110115060f0c080d0903050f070c0611 72
    0xc281081c054078055000945003014104160010f10481c41e01c1030a03807251a550045043c0c0030b0304c00c20441c5200036580d0080002d200f11072030803010030407004d41c03e1000a40c86082048210301c241000d40154500034001030001480001040110301d40c5110740c0c030300c10002200003900583c8941ca40340d0400c04459000e00400043d81804109a074411040714014030543c9103e07140300130340d10075032610005000301074008001420301c5940641840d640d000b08031198080c550001c00c6852107071550008440e03240d82e40319102c6141075070555254401034045908607407504410702c0483c000f081168010880780000b00909200c0b400c04100301d5104840004072504501d1981c0c3c032144d1198242d03400e44245603000340b40c60200702e6003076550811840d1140701035401c0a00c3c0c4141d10500e000c18600711112502c0d88080075219610885034030f286000000c206200c280042c0301018010340c09543e409200703050507031030000300c120410416000100102e4103e8216a02400f003168000c441c001201c0200005 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 364070026 1250 364068776 364068811
    0x5120c041b030513081e0c160e07020303060d06090f0614060307050406051f35090d1e0219050307140307030f08060a05040c020c011b02010203030406050a020f0a020d08 74
    0x48803d64444d09540500990104141c40351010312a0115807c40c0d02c20412a50145c000c0c842c1141c0c0c9800c80e2003070509401c07261000480aa00200489105000082c8009181403243e92010010544010180d601c0a074402d0040d000034070b140700b0742d5003078414241c0040e810714110040526001094001034060350504104005a854038028000c1d01d40d100450700c400d130140c02004a50540c1030403d0365203ca003c500b29103c54a200825004440d40c030b50800301903d940d09034501d5070f14180c049403400055090301c0d62a03200b450300304617552091000d1042d40c0d0300c0d0b041400d00c01001c0d070402006454035000001d007a030030020001c2000603c0d002000c00b80d410310715681c42c040c10501f21700703d00c01c0900072184001440c0d0394400300035101502008008002e402c2031040020740d22282020b0843c00f00c0c03650692844e0000540881d00c103015416401140755603502d0784c42401503e00a010380d1411074090203094805000324002d02861451540103200d03028034004010500300d4094454291300103043c90 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 364071276 1250 364070026 364070033
    0x70c080c100f0c050f18031c0315060c02010c061506200601050a120302031e09040b012c03030d0204030311010606030203060d06051506030907050a09050c030105120c041b030513 78
    0x1d80d07400c80d51700c000141e1120107650070b848a05d4403041845516018550500c49250310f5481c0d007040c040559a020000101c80506103044400d460250401103007042c4a40c03001503203d12104d54800d841003034085041c07e031032820004609441e8004501044180580250b01280d100c440074520150200800d00c551404001c070300c81c04018040e901c1599600d0b02d0b404c050500810481d81d040c1c42503508110440b0780320748100c925400402aa84c4141c0c10040c43d960207600c90b5050101c03900380d110820031004c944131510301c241d01c004000f0740c2d0517002c140100201c5840c10300c00b80c0b005600035200c1c075285041c80345800d82111910b0f013248091601c1030043c007080340c803801003096545602103c001144d4503503004034003124291105040d84100000104903c807030703010500380f048900a80c0d11100c6540c8904d07808094440403030340814001002c1c030041089151041d690084001004103880c6404044400b02c4c05540c011942480529501145030130403a505210b2140c1c0500d900c1400518090f8665 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 364072526 1250 364071276 364071287
    0x440a02090a1418030408030a0c141c11150414120301030c0311061210052d091308040303020d08090f0c04020f0903011b0314100e070c080c100f0c 64
    0x185036001c652212850300800010400c02c585c007500c5010112515803d6900b00100110603c0204449503000742031503100f004800600032400404d0030035424007800c0c41078003c40c2c1c02102403030100d8461107294a004e403c41801300b403890207a4010200c01060203107105d0402e1078001d901d400060142000c20040000c201061442d0054035801a50304e4600c20005000401c0c1c0d01501c0c505481c205400390500450003410303031440046402c1904c041502c004c100e6681c0c042c012031440d0a030080c55501c00c0002c2d807032401d203038503c0d440784416020111052240e00d4410381d94008e90011070241c0d0041001e000e0550300480303d07076848011000100701014450f00c10a440b620181e107403500854001c00e2000d101507000f415502d64103805002002503005120721100b026007119103c902007881c00d0f00300c2140f004a5241a8441c00549100c1c045440c54800d2649428600800c9481009071121320345002517540300042c60002e0450009200140303034801400203c510f0b02c01c00c6031040789885001f107111504174 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 364073776 1250 364072526 364072531
    0x150127030807060e0303100303030b0301230402040e060901020a020c091303030b03010b060c0c0a05060304120c0f0c060c050c0603090d110a0215040303030e07440a02090a14 76
    0x84503480d42d05529162000d8640f00d5a40710386800b01100300002c80c566070a6441c2200d006e61703024491000000c1c1494220b824810119009134100c000c0b001801d00c071000841d8100d40701520010301c0c490790240d080e042070300035280484140d400103502c044107a410001d403500285c0898140c070f22424010108001d524203024010281510f6070301400d01681e00394401070481101030300d241d0355038008801d45500c13a01008202c034480c02034003401080a04000301607078030a5911030840b800800303140c00180ca00d1603403031008650141c40c081c06c05c1e00054003e02074000420440e1220414410360b440d0203070610049040003805840c06104028418400040c60700451880341840100071040c082403606000700240041d400032141c40701402c82903c2c210003401103a01030344e001c110020040c0c424580b520b03400d00c03039042a00d00e05900c2c03100503090503d11110384c00041c0b42d0004c40c50481421300480f0707840c8100065032900280e01603019170901900c0f6661050f00d040d410001c482c4044a1000c00300c002 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 364075026 1250 364073776 364073783
    0x23040c0804054303050d0c200607240f1413120e06070b0705030906010801021315050c0f03041403030903121b0f010204030c05040b090a111215012703 66
    0x55108a1220040491503480a190040103640c0c1e40030318942c014020303509a2604031a08411505010111823481030071131442000101380c80c1c500307401a00c030300410002e0042c5002d1074010984003d80510803501c00c017142d00304951400f0401e81c3c028490104a11001000090b03100c41d2680041c0000b000220624500303007460400d041c02c00070090105e4018007902c40000c00c04c103d2071044c8001c4503088000342d846042c2030000c9600c0c1c1d07038940c0c41880c280c3c058038203021142144540148445062015480c101d04c0c1c0929109081640181c8001d1520f04011004155600005020b010800030740c00186400c460940040d8502548180800c2e0b83d026140d0300f8892081c4003040c030705082d160380e140c00c2c411117140400b2a84003a442c680d40f80e00035031052000301c0380314004400c0002d89042c54054200e03a23000046c1498400e540b90200c420243c8402c00b10fa4204400c200540648043c14001d40c0d0701803101c4a400070100c03c2504000740020100c0648500001c100000c0708004148054100007920f51 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 364076276 1250 364075026 364075123
    0x90f0714030a140405100612050706080a022109060601090503120307030e07030302070e0601030c020606010c020a0f0602061803130311030703020a0b07020a0b040f23040c080405 78
    0x6520038034400408810043c00b00c03540d43c280030f0100f03120000031840c524182c0040100a005c1e42c5500322a50050b110400402640202e02d003081818000e5450a038406c0d044500580740c12030404409055a84007031183c8002c401710742c24001205404c000c0c0c25880402802e203a0305060412000999545140b80d894080503000800600c900d031090708615110000c3c442240d4a0a07100d04d40a5110001d90088035212801000003808540c824040c0754074849007038024006a0300c4030b0004480c2e01569003000c0ea0000181840015068582114400140b1140e40a0416810000b08040c40522034400c0d052469206003d03203c03402100c0e21036141265070011491a41c1441440442d0800c001d5a00c007a6120a212100003050301041d4010114503208503201032429482c3c009001d00d90041e402900c0c0d02c440443c0c0d09120240d0700100c0c07a0724501100c880701c8008040700c4000b4040e2006054028002001241407204210041010004145484402d0484401d061500001c40c4502030241e00c4a0340 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 364077526 1250 364076276 364076281
    0x240623030a230c0f0f01111203010b040609050f030c2803060b18010e22080301060201270210120e071e060c0b0601050c101a090f071403 60
    0x80d810000488800c0e4000d081c035819040815280014211408810a01d401080d41980c0103140406415200c440c00400300404515810011103a582140c29880058440d240ca007500154000c0003550081103404c181590341c60a01030020240101c43d800030380205807000b4220b0103680d0118011140c0d40082c0d8101070340992a5240151158200869000c080d0115201009000c001c2c0c020264580055901d080180c61a200300806210b092062400280c0314901140c1030858001e101c41082c038100d440d580301c42080c0d4070799111a50081e4003110140c0c1d9910f0001d07074014400231340809040369550103440d88810580100b60801c0d00170349210100311080a20301d500d81c110394002c00080c080b940450301400e07180c01c0359400141c02840d6010059410000000301a4810015074142c0790b41701d800402241c441c54010b5919030018403450425020b60014459980726911443c20310788a65014004581e0031501403002200000d41510f440c44140000c10100d6500281e0170548442d030340e4191139899 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 364078776 1250 364077526 364077529
    0x1030b0c0d0204080601060912230f011a011b03080c0f0403051006030c05040b0609040b030c10090f090b030c0d020a080a11040f0e0a111804240623 65
    0x500c00c154005100030702c04900801c0294000913294180d13010382e110105010b4460035040006100d18a00424110b100d201108000340b10700c070760803034003103000048801094214a030b4a00355a01b04400c001d6840090401c0304007980d0119440003201109501c0c506041c0c400e0302c00a100380b034028038002412100140d0805040b046400321002180c00505566070030b400b040c0d044000c1c0c12940720039204551140800f18042c0f40501c1205080c2034010704551506030301406000c00342001076001a0b1500408948034a0360716501114245044503607182007030305082040e0001131945940000e0482071902e2688181503c0001c2c1400d0110012602510602c40c036100041581072550803440780e50003132a50840401605a0100181e040102d03014000036590141031411252a0340400351139600c150502c5003c5040c185501c452404050909114a104007900c04006002603404a950310b203001034011420951003020300d490b480310744007800300d00d00e40716985910440307440e8a110007010368035010125 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 364080026 1250 364078776 364078801
    0xc01030504030c0b10030c2301030b030304180204090e0d02061e010b03060307151119051509071a031f080309040e010b030609010606020709020403020901030803042906100908030301030b 82
    0xc50b808007424420f20323140c0c040440ea0100c10121981c18540000c0014102c1d8024080c43c000c950010700103506251602d9140300c031100e07000c0b00900f1582d60801011441d603460f40907030404800300200a2041070442d401c0240b81c90001005030f2400d1141c808001a10001c44403a54111603801c00019140d88899000a043c1001030b40318481e03082000420884c0d05400c050b2211030041150162414020340c803402c02050b04a0308130080154001d100840314030811049203603006401d0b4004c0b5107015466440c6980d9401480780f0311300c2400d50120820400d044403030540604003c05030742d000c0c070305407503d810303940d4a0294100140c0b1441c0c59514100030740ca0b00354450740844800408071641c900300641c107140240440d000b01da005009004c00820355040c81e0080b5022254054401082a0f10319200d5200b15040a401150305003840f800d0004260305500500400d004424107640c070608000081022028000302c000080c800005002c2001e00004019241100e8010321504400c1d50740e407400002 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 364081276 1250 364080026 364080029
    0x17190902010e0a06030e100219030905120d090b0105030312041e02030601260609100f0e030703030608010605031515010c051204090501090908190e060d0902030c01030504030c0b10 79
    0x1040100310200140c890740c907400020084030b1300815180c007040e2141f80002a8801e10080c800c20b11156106682858840c0d4071035580203015808be60880c1c403010844000c3c5610600c400a20292500c1204007032108400d916401841c0407030046180440100c4484403507103004002610700f05481e43c504036220b6080c8c02180c21680d00900345c400d00d40e1180ba04245109095a645800d038806283c912500b5500181e0b007030003004e240d001400c0009200c00103401401940203109800c0780c0352081c03200c1b0280e04101074038007031b80f00b07440100765a42480300c40b600311603495000d41d209610800c05074030341546100c41143c02000e1203d044001a00c5000143c3c0d000d601140001d0107842694202c240d04520a005001a2414000b003072081d139a07551800c07800c2cae83e140e11001c1d102c220208500e03810f0113009134040510000c28204030103d045418001032443d000200b25070045600d0399000800c601d018002d0740940760090030104941e007401e4400070651101d49000425000747d42c4007180219449101010 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 364082526 1250 364081276 364081279
    0xd03081b040e0f060103020a08150612010602030c01150609061404080f030a02010507020a030e01180e100608011a1c0624020610030b1504060305100b0117190902010e 73
    0x541d11952414624020030b8101c1c0c9810402c20280045113030766100e4000c4484540e81075503161041c2d10703485982c110030740c0340410156111500f00f0032680080c1300d0380b5049000b4412600590385609041030030509661021000c07402c025035548040c0a815044035018041d0781c43ea1038902c043d11211406042180b24640243c1c50a2281c0001c450301804000000c00e240003a5a0090065072174180059940d050f621000a0100b610314542c6070ba50b521818200d40700d06101c001c0201540d6481d103140700c002d00c0c01d40d190300400700d1701c02050002c035400c202000c0c014031010b244006049803002e820303c410300455103a484024565103c040100e0780d6034200b10041d050030311000107408000040f075400c0c0a07407000d100c2d025001d2240014140101c20010104690300603044036007076a5103c24800d2610080000d0b00ea2040d6600030100200388104194000316420083c0006c0300d43d081400507295003141c03e60104500440802c006104404c0c8560340c540c110407600c0880c00b6131062006035003910402d60001d = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 364083776 1250 364082526 364082581
    0x5160f030213080c130504031d030a0b070809010c14161a010605030411030c03100b180a1512050706140d090c050f061303120207030c1d01060e0d0308 66
    0x4540000003094130048290115002c18501c0280802c4100303480e411940540414104d80140201000807001030310800300017030a561010b42c01c1d41d0b4171101940196072039000181020100000c2010903c00c40c00306400b10306044004510035519120386103e000036100c64034806401120401503940c411034600000f200241c1000e40c0c417040002d20079042150151016102c20038014103034100496800311703009000d4040e0a4079403003070042d44041d0426201142c0c0007560981108045c940707080780b032030007202d00f44000f044ca420b0000f40919900e6540c2c00c1300c0658900020b541d000102e001800d5170413119103007082040c80311202c080c40801d000d1600c88000351810040103404000c05c040201099034801c607403c941c0f039501d681c24008540903882e42c007190f401c0e560b4010310200d5205e2000c964209400d2044420181d02c0c0d5440107000c8006034000c640a14802e1003240920394060a0280584414076000e0403850b40f060000302c1d80440c418015042c0714031180070811103440c44101541d03003500b04500d0b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 364085026 1250 364083776 364083779
    0x30212011e09060b01050304050c120f0304030302031201170303070c030905090a09060609020918040606031a04050d0e10081b0a05070204140124050c2d0105160f030213 74
    0xd0201030846090b0448a1520740321029007198003c4054a0103660003130028003407110003801b407016007a0100250384152003440d20800c4000c2e0208001c0c00514400c1e80070350380710042c0c0782c1091420001038025418a00141c5103150300d1200000c19244d01251a2a00b10000201420300b5602c0115982045030001000c20030070440009035044480021f109034020000e03071356560180c1089020b0420601e0780414040884209240242c1c1364075041402500001071f03166582c3e130b5038034140410850b03d5080b50f00a100704000d019041c00403c28201c21030600310310090007000010f6200703109404200c11f000180340420792580c0808012100c0051101e80305585a64040303001c2d2203904900012445142090b2048881820300380c600b904a40c2e21181c29420326400b442420025808652544100031040c0420900f2030020070401c0f440e1003155000a88401130485490710301c044458216031140e040c02c050284840c0030039942408454903142001c881c10f2403030000c4011b031003845c0400c0400c2d2101d850 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 364086276 1250 364085026 364085081
    0x41e02030d0f170105030c0d0516140312031b16020316090609200c0a06020310060305060d11040e0705031b0103060618090b0d0614090d0c0b0103021201 67
    0x142e000100030394030340c40314043e6010001d58a64909003d065003580181c6043d00c4941000c590707111005114070b0079145882600320b41031070046955404400d84d401005140059410103200e10a00c03000880402880c1d440c1490b82c07000b82241c1e4044085500708001000c02c0e01e1400702c401c0540312503004003034541c42103070740008049000181c001c4004041c5005c60000b480113007881481191403208100c00031909000520b0f03651504120b51030326241c0101c407400400103070644003d40c03265601004d0000c9041c1020402021a10000c0005010303000d148010070224084114480e00b030345040780c01060180c4490045810a082a030003540c061140030315150302204030140b4140d15071400c0c1e1b001c010040d03491600720f540c0580d40740e5582a12001940c24440000740e50050340704c89101804003807490700580d0724401225401c6074041034404209040c000000c60520139600510114a801403a000454403428035494040c800284103581c41c8800220b0300c58207400c080402a100200d40240c1c0001d400d = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 364087526 1250 364086276 364086287
    0x90803090109031e09030b040321020406020d090b0d050405070503010c0e150901090608100b0c030705550b100501030c1409120610030c0b0306030303041e02030d 71
    0x400407004516610301021003144640c840b5850040030f9980d945d0b40d58a581c079400e5028102410070f40c200000e030b1034041d40c60207881e0901c000c4141d99107801681d591910300c000b803c2c034138102103c17010459041d0040100400d29070555810b100f264400207038585551904074501081940721039055400c150742641d2280e0021901c03100030b40150b803514200542100d4215880c440c041c100c6000c41d604203410300401340b2460005900130150f0040d1100c01c0d0300e4801d44007903508500400c11459000196403010041c0500c0400000c4a04403181031244030201c5d01131a9241d02035010202c1c42300281c3c844000824a0020303400050340000c03038041c00c1041818a07080000c1d0460780a00034a07442800060755500c02d1142c000f8040547c0d4911450038034507400f01d40c20b984090039072940000f6003c086921b04d01e050082c11b008540e019070400f8181d1861610001c400c445074060340b1107039400d00400005883c080101d075401640010a1084030400c010b1303514900c11803c00103900340c42400c0d101c9990a8009 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 364088776 1250 364087526 364087541
    0x8190e070b13050d1e1106071202010f0b0a060516080f0a090e25170a050a0612260c0601090501031103061006212c0a0b0705030a0908030901 62
    0xc90320b805080c1d00d48040c0f1581d10b100e254000e10441d4030f03844040c07582002c02503061595200e040c018402c6011b840c0010346a40201c00e095581220880744c0305003035902403140d0b4017858402d0303d0074040c1354260000204070802910400092080009007646005a4100e400d02140c1e0320589103074661401318200e1445130800348424020034a00580420b0601a07220340620031181116420040a00584115000b4550012003403d018402c85502c9c80e01c20001d103814800c1c1e0700e400000039603150002c060350030784001e940202500b002001820004c40d0086d03000d040c016820740401c0c403041c2d5903101290214070404042907150700031400007080182d071030380180e4120b0b4040c6042420704440b02c010191203880c140d030a8040b80c90004420840c1c01c0c0079102100803058107000400c035440050709030000350317025108840e50950720404880808448410505803101c0c04800800030600c00c0e41d201c43d1b0940d4050b090500f407020200010b40181d00c030b9000851469440030b491070301c034100903510300d001c0e2412 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 364090026 1250 364088776 364088797
    0x10314070b0c07091410091505030d0201140c161b08071d01091e0b120714120102040312030f0603060204152c04051e010f03030906050a08190e070b 65
    0x5151400365000f6812200318013900c41081002140c1f45440700d103074010280c105480e4800e6142d000c000450340e030b00344030b0041a0303c03082d000840c11841042c0100807024004103100304007030341801202c288040e500138000519a109032045020b0020042808010f40c09500c0403515109a18011640e01d5001c08000801640340b15005903503602c4012a000307072200201c0802c1144020040c8580b0240c0c280c1102007a108007800d01d000001e5664505820000c56030418164110091008500c0f401d0286591494550100086040070b09665030000c121410b040c9507409c154841400b40d5050026601400045038410030031942c4903501d80c214811019641c003100d001c560f50305400e01c0f00440c206e01540e5500d900f1000d03420b00a0909081000501c0050407001c009502ea0f035024019164010156010f05905c0710710207a46480d40c507004103220101e81001c010440180b040742512074003e0704094000080018444410711220041d00c000c1c848100303502d844e842280400a54000d0300c00c0207040c900036 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 364091276 1250 364090026 364090031
    0x2041401060207060e0f010c03050a0c0b09070608010506070b0412090f030b060306090a030503010909110a03110913030c030c0510050a0c0e030a0203030d0509030c0106032003010e06010314070b0c0709 88
    0xc41170030810030042e1a4210f03401b08101000190001e480740000300ba00e205a4204140d0440c1c2c0c1c0d0311035410300c00d0700715000381e9640c1c011380003480150740109000d40100001c8500701d05d8510241d690942980001d00000c004003071000c0f003201114000c155420140250b00040505181c5d01e0400c0c411aa400b580c2c018020700448000c2003206030045030340307588660541c8401e40f0b140d10f07009060303000b45109042138410b4800d5100c035800b250341d0741d52414000c2d801003103071040c000501d0302042120440900100d00c10030329284610b00081d00600c15a1200f501410603082100380c3e030030524240785d0000700c5204410b140500308505840641d01440c072440c0c40d681c8980c281c08007001490340e110079000000c7d40c543d00c28000e50300c0c083d580d40c0080f0792015141c408d6a003080300d050406c40c01d442144c0c000b154424612100040e06d0200c1c040800426a4128000d02c081c040c10200f0390340f5a02c040c00050400c1c6004064224104001c111440082c40030b560390554400d040168a610b5600304e01810149a0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 364092526 1250 364091276 364091297
    0x3090105150603090d20070f0f0e04051c200106150504030503040510030204080d1205060616061119120f0b1e0307090906150e010b070803040204140106020706 70
    0x30050140ea12614001c0c0c005c2031040701d03d0009a079110344a0348084c0341c000300b18440c03d40034081449948002c100c1c01c000c0302c0c0c01d1814040883c07204003581d00142040e000362020800030460000d000044a02081d01c010521504264100c59901e0700a1401d420a07003021104e03800b00c141544100c08440d030482c0c41104a00a00c0c000f150340d4852848080d03d90b0b8400d00043c0803170b250030f0f030008500174914180180fa040ea100309450410000190709801310f561090100c00d165124000d21380e002d0400c544840c83c151914440c0b9120580e14a005808242d645160708243d42c26081112000c00b4034020040c04440082c000800660708100e010840b0307403c02c0e02c1c00c035440c1221301405540c0c8000400c40041680f00c04690300d42844440485a4140300300000000c541d500c601c82d03002141e02600022a07004036071038285109111580c040d40303006280600400c041441030303054444642c0d000300181d03540d0315a400000c001e40082200c010303000104200021fa600d40004020044400f19120f190299 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 364093776 1250 364092526 364092529
    0xe01120e1614010507230a0b010806070c02090a020703090503060108010209120d090b03090a0606060c110108010501020303150d0b010602010b01110607050910030e061f0b0327070b0309010515 84
    0xb105250419408544188040c3c0001118400c0d020413044408205c0040220130500180c604035010038182c0340c40050724014403180310244003150380f054483c20803030310301186030740851404c44006014109091b4007107072140c10107115848a000810700141110244e5842e01c8019000350710042d40d084c801d8201e120880126903011400784600d85054542840c051319080404240d50700081c08044507028010350640000c3c0c40b88200005401e840c4c1d208245803419181c13864084d0000400740b4140003450004002c1a079001040700e520212504c01c02c11104101c4010920790007034120010a990040c1d000031458550543c0f0a145850b42640c841c007403e0540c0700340c9903c5510503141c047c00240100214920360410081c041690381d9980340020703181100c1c00301c2a08090040d15910b0140f00380c400309880c0c0c495044010300240c041141040d28600341503c11004032a401003250302c40111040d10010701020a00c94240102410407555907a03281c845c601380e0003004100c2c1c025041d0071440b10606240d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 364095026 1250 364093776 364093799
    0x121e0203150d05031b0f0313060e0d11121002040b030a14190b060c190c06050a1d0d051209090c090603060d05010605100201050f01080d020d0e01120e16 67
    0x2c80d0b00304000c2c0d0f10304900d4603030300005549202580caa417071091002c18a800e80c2e04000802d0803150b5040103012203410300394000d11030488804d000d8031a840c07000c01c0304042001a00700c010300c41000c40c1e000c1c0614050b0348005041c04640404201c10074800f05000440301500740080d841520b200f041000b01280c00d51000d90040c00a82e0080f8031421a5022a03c2103481644802e0309680001d10490a1215040b40d20340307841d07800c8500a2944000041f110704200b01051540e0203003c0c6400c1590801800110042c240b0712403075022084040b0100882d07250303481360528801c81a800000b513079580d241e580701111607580518030881c000c400403800221079214941c29101d10b0345001300300310b203143c80f607204000c5214601402a0f445550303d2000264503503c9030705003410312900d07030004100783c80e00814034103442a0590280f051030300801924580390781d0100b1090700600240c280201c13288000e000492f5280185001c08200f03e00e041c404504400d80001c130444540ca806003502060754880e031142c4074 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 364096276 1250 364095026 364095049
    0x510120e070e0f04020604120501090303050c0a0f050906040b0f07210e01120f05190b0301090c0303081b03040c15180909080c0d09050307061806121e020315 69
    0x108a801c40c04511241280a00c00d03420900040c04181016214000c0c0700d180f5425238812907807070f035640e21a103003056054046c440d40200b4460a95007010600342c4082c012008100540d010000001044c1409135203a10070744010304a0f50280684883c024a403401d0242d12800d4195918903c2d10880285c040300800700c405058820f44e00d00691700610001903d5410503610110521911401407020782055441500d100b1181c0004194552103c0c48520b42100d10fa0701419019905111800012600400e150b804681e41860140e0303081d6559240c812248100b1100082d0182e000824401440404d540c41015241000b810314040712415509544042101003003044951941d101000b0203c01980002001801446014501409000d409051196020b4843c0110754856400d201c6400d0401040016214904100d5101700006c080642041c0795440341c40208841014000e810407550b0300310720514680b03800b040700e4011240c403800d00039410844809401d402942000c00180c90403030003482 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 364097526 1250 364096276 364096289
    0x4080304050f01020312040b060f0414040b0403090905040305070b07050c0604031202070215040f120503160f0b160f050403020d0204050c13090c030c030e0c190510120e07 75
    0x146031034903203000d01284420302011241940020321a10b4800b4010328440c03031090307101d01410071003450441c0400c02c0300450b210266014614104c3d1161450b01c5080c000b5401070780140703030201d059072503250894010406400072000741d400c010a000c10103801c0300140052500c24540a2410b644200c4200e0b2075000d0011000e003950301400c0030401013406006451110390550700702502c2c1c220076070041212525921001c550490002804000042c210400d810140c418800250042909515241e9a130b0245841d03891400c07882e158680104400e142c8541403055102e651041149841031101c0705e0102c040d08a880450342e91100760401c10300c50000c0710142c81c2c1c02411100111440d4090000810004003480c0303464800704111004820009005002002c1134440030446074000c0d00003c041d103518000310400d25041c80c0c5161505040411007020a15040d076641d03804d0703040310003c442412480d43c030507900302d50b651002200d855405101ca0000c100704200500c0181400c00403980c1c0d480a901ca040f = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 364098776 1250 364097526 364097533
    0x30c0206040f0804091409011103060d0303020f16080706060806090a030c140708030c1006030209060f150f070308180a0308070504260d030b060f0d1806090201140408 73
    0x780010118414181194011002c0905043d10f5000c4034049502c0a0030310711344100e034101000b0480c507090003540000c0d204032120500314140a0041020a0801c900041c01d1603004204035002c03020101c03d441919100c1c0d41110714040c00341c20108090303130240c00103031202400c0c00b40c04075590f94001030b018040c505110081c40003170480d80701228802103565040f1030f620010601142c101208000f8440504200000745958009404003030f4504844580242003080c01c10b20100056620038940a0f44032200b0f607812401440301100286a12102d02007501111001284030745a42000d40080c1003141d03c80d8441c09110b0f11140203070f0fa0224001045056580c0c801d52101c0d0020740f0949041341c000c10740f424494201903e40c26a0240005d81072614083c403016000e1391260000c0800c0500094141810200302a80345807001c100340e442a4540321008003000100c900784240213900080e2205510650000808070a2901c10f000c0c00094030301ba0f00040c02302c1810001540350000702d6085a4120005 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 364100026 1250 364098776 364098781
    0x2412050c09120d0504050114070209010803040e09011e18020d0c051302040305030702010c230105070306140109060305060102030f07050f07170d0c030c060c03140711030313020406122001030c0206 86
    0x4442314650501d00440300c5400b80007000060b00d403800414081e148003405107441d00e0520042090340000201900816810625542096041621141210b044049d00460981c04440383c02c80340d030010b07100080d00b080400201d5000d002003152060140c8100712040104100302c40f141c0780a0f4021808040c0c110307042009044010b6008110400d8110b202e06512202f501c03140c1548101140c0e403000c44207035a5141c904101ca0242c0c14401d41c0c010f8546180350141741d04105000810381640d5020700da05041d0741d2004221076070700030020f0f101d9455107514099038900342446d016407280d9080354042140d04c10a000030608003809035103880b01e03040303103002020841c120030800c0710b00194169081d01804900d03a22007001c035806000e440c0c0c0820560f1004100c001d106040041405030090201042080d1030407a0800903001200301c1f40c2040383d03190304000b4820640005801400994000b1410b0300340d6804181c20003940c03981e643e03090402000303900810b00b807180041d4107803819805140c0060700300500 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 364101276 1250 364100026 364100029
    0x1020708030f0615043b0a11220509090c01120c0c0f05030909010f050d080d02090d14070918030f11070618050301062412050c09120d050405 62
    0x6450b0340410f00400c40420704094200051895020340c0150564051030940c03800c02104131212220740500924650035502020325049102400c00b0301240c0259442e5000946006940c10503100100c0000341d0440ea000e210700341c09442c0420501c01d06005400410014040b01030129138249501c5e01a1249890710a00e00c42c05002040d540d244041808511000e0202040d81c0084c200700051040e4015aa43c03840e40f010070131b80c010140e118520300708029100b4802c03500c1300c03002ca200d61544400410703110646000118007900420850341d0700144903d05500c02e00508407018032903a107080c029500320a40342c1c4880b601b80e07181d900ca10340c080c02000082000203031081d1911001d5007080d140c8075000794034a111031800c202003640108002100d010081a141c11052020f0f0003e0000710020481240340003802085a407900421004041d216403498811601503a0034080b104c1c0901800c0102e071800c60708051140c0c01c03803c407890081080d140500420480056810b01119803610b03602c2c140340c900b00 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 364102526 1250 364101276 364101301
    0x14130216080a02030403150626100905150a200309070303050c0c09010305070501020d08100909031b050114160c0605070e0303070f11060403110f180f06030f0102070803 74
    0x18070742c80442c03104000000109a400f0400440043c47c03003030110b052032400482910a1440b803d1241e111001c0000e0007036011000260303404185402d03c80400c0d01101030600c5070406088080300c40c04840c940c0d040100800d11940440d03001548010b09450000a404904401e0700040b50300e4406503210b40c405101180c0140302030400612210210741075960500003080c01404284d004662039404036605204968061000d050b0000b0586006103907460714041e810000302441c4218588150703204215414144216001609030f030244c00b00300554003003803900500804207800c026200504020201d141000900340414001103983e881d68441c01ea00e807169401094040c050200340b200314020382072242c500380041c01c00a03004180e40440c6c102c1c0341c14801c0820842c251881d204101c02c100c00c0c800203048100358403400380c0039101100c20340e82550106e07200c0e100041044c1f403c8641c080070492001c41040705035110b00343c142c0540c1c4600c61200000c1c0d00340d0103882001006030b5402d00020348042c5000 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 364103776 1250 364102526 364102537
    0x100f0303050d020d02090d0c1a0f120c0c0a1a010605042402011509050a1109090c0a020111121b030108031b0a0f05030a0e030a0c03020405100504061413021608 70
    0x600051600c0035100c00200310003c0087d0454059420440810084005071503034241466210340c86441d01c0d48a1846051f40e101d00c22801401a4a040124000076011802e0b5030003603400c2011a0400e40306414400c2030b400500400c55200b210041c004550781384280155021079a010340ea442c040c0c80c104075501404275004006100719960380c800745050380c0c03a1014090040400c8180010123007400800041038480c03902001034401c0c420800200fa03500c8103078015070301c01802d804a81e1140591841240944180d52220f0140c588c0400c1d5260a10412100503020b88070000d1b01c401c3c0754444210b541d855001c00d00c103154450304144040c0101c5001c000700c440134031a0341001d540c00c10034550350783c84400b04104020380300d41d800407482c07400a54015409003075022044000b455075807050b40c0d0b903241d40c41d02c50200038040d588810119102541e2507510f9000750a0080c0300b404081d03202d0401e0203840c0e140c2030343c0d10310174a81020295071082c06442190700d2202404484d0213510010788030711886130b105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 364105026 1250 364103776 364103797
    0x120115140a20060a060305061f03030813080d0203060405060d0b161103040303020d081806060f010e031b0f01170601080606041e0504230103030e0324100f0303050d02 73
    0x301d0302e01c141401c1d41804194810103010a0018800e410741c280140b07084d100400c09038424248800c410003201010b120341084170350519046d131646ea2084541d0800002c4124010422a40490f00186943d150303009103100d00e00a840800c2943d035040c0401481043c01c5078060a20704c801c20220f5010103006c0c41601c1702c030f00f0a0038071000c180b07410400c0601d0341d403183e40b0541c0160440444480c0190380050f1468008110203060081c9007110301c41142c44030301c081e10340342c460380412501040c1d690290319030b600c0d4108010180c0c1c0e605c40c4c01c80c110140d540c905008407841a00100d41419856004404c0c08110844400c00f084065980c4801920f0340c0a0142010758407603c140000180c1c030742039599098500c1034414403107a0f0f99242030300380070985032140d013240c2904c00d80360324058520301007881c81d17411290189000c0207161fa03c240441e080c4044980c0b20001d0807003101d1f900c45203011a44801e40511010006e1034800740d80c27030003800d80644c40360000130001401040310f1701500c060b80e0090044c3c11032 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 364106276 1250 364105026 364105067
    0x70906171e06030f0a0609050c03030a051c1107060b0a092f090603130c09110d0902060d09050304030b10050a0909021306080a06060b031612060803120115140a 70
    0x40400c01241742180c142011240c154840408108100c818030400c0c10f9903100383d00441c141b20010001800f540500310b10300744406880310b1040c038007801d01c4d0401041d04001ea80650340c3c41d121401e00d00043e20800620a002d242c5e10000000c0280752407007500030800c0c0b08070314120000446102039070030075004480d034140c40d0820b11040b85517a88502c000c41c06912513a16000030702d4140d1a0402c9402c1c2564003002c011f600d40050b06601c0300900301100c0c500c203e801c03000103d880b104d1000070403a0140c40350f00f11361503160980c1ea0003000760000051054074000d007426209995241c025400324240c5002c2c141d004a101202007001000a400038115244001d2007181c03207055210b284406c643e00d41d07114604c90784c45401e0039014807100384500d50140401400840c40c47c9810b80d207016016164007460307000c2110341c0705000c130706000300d0b40110090090b8100340caa5070f60f22009084000202802500a8070441c44180ba82d105c4c00f0f030400989030310032014620704048690109407061411848503054400 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 364107526 1250 364106276 364106293
    0x815010c050a02041d0607050306010512181b0102120c0c060717030708040b240613030503040b040609120201120216050f1b01030b1f020f0105070906171e0603 70
    0xd07568045d4803980d10001c4d03442c51110796801c00e03191500e1009401803041c400c00f0402e010590341d01a00321404150444001a44c1ea02c2c0e160410100304003000d0030184d075001c1d101102d508803240740c1150007104001da08455180d8100203002c1c081e44a074a003c1c0d00c282d800a0018142c60030601c002d82251401811001481882001e5003952540101e40100c0000d22040400c400c0000181103aa040040b03400c0b0201d04140740c10309884132607078511a107031040101040f03100b0790712105141c03400519441001c0d00d03101d03556140c1244207500580036010120b81090004114113151440c090f000c42d80584d00c0610004086134904c0c001c0d800840e200401042d030401c0034001c20300030801890407400d0b01e0010421012101e02c02c030500700c40a1a001d04240c1485802941d981c0c40840006561642d04803900d0041c201c8602a481c0030b4424851400950074242040311254020005400b01d0b525604d030000303000e0b0002c0030168902c130211044080d03e0040e044100134964982402c036800b1034054222a1001d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 364108776 1250 364107526 364107529
    0x19031b0507030303020901200604030503090a0f0614061801090216120801030209010819110102010213060203070201201b04061a040504061410030b0a030210120c0815010c050a02 78
    0x1c030581e0003e0300400e800140b240a035590040c06401d420692841c60f400030414146003e03283c1b400500301400300040400401d9000c44180000b41301281d20604481c0845585d2810030050040703000400b0b00303502a000001e416090400aa0201d024041c4840003075a092028102c000e42008110300c0c01c0d031060fa40300c1000101413040750200e42c130140c1c9400703a55602d144100a070040058011462a07045211014030001c2c250b0090039074580d000000e8900d01c02800c004038024085c01428030403000070044006481a008801804964000c0e626a407100300c1c03035104240100e8120085401640c0129500c420358003005510380b500d0300000f0004540c55981d10380c52220491801c2803021b8244002030100501c0ca0240310341c600030312242c0d844400100c40180004d6000003044030b03880c00c0c0350b00e490441038203548152035a000740d540245013081241c260314000700171580710400000340b40d15009140307400070b001d503045520507440c8003c10510381060750f004407110b0907020801c0b5464803031140b014005 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 364110026 1250 364108776 364108783
    0x18150f0904031409131b0e030a02040b04020c1903170609010b0d060807151e1b08090405010323070308090409080904020a02010b030d08040b04020f0d0f0501020c0f19031b05 76
    0x105c10b0200c000f24000c075400a03502c0d08a04c00300500c105004220000310010345010600e01c210725012100020b40411020218000e4400d10075012003a00618190141081422030707a6450103019641c0c44100d0b845200c29091501d00a49019600480010041000c402c80000401412412408c0482c150390380351100c601c0c2958542100e5001d41222800700200c3e0382c4a40801c002ca16003501407080c10300c0368030000c1c001c2d414645100e0450341864510206225541089401c0391102900400c06580d480c2881070a248114031820291500c4000701d01c041c1c580010001e060b01c0d00241500d103004184030401004005040c070403600c460b000e00c082d404a0751144050300f441c000a80021511000d543c04050070690be0b25440c0c010711840105200100e1006400030b54016816501a140c4103904d100081400195031402068124814a04c03000c021064000c2c1140e890382c40100d48840080d0242951508046000c0c0030200846c084a00c010138030850105111085034240c1c5619009540c480604 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 364111276 1250 364110026 364110049
    0x7140c040c03060501140f0a05090111030304030819020a0e0405100f1e1d161202180f0105090315040606120b011e12061a18150f0904031409 62
    0x120b941ca440030021940c2103201350a55600c1c3c80c0c4440d01d4030187d030300307041c4481c01780990b0b000401a01140e80c1c0701607400f80c87c624400c0512081240d072a8a040d140042c1302c07040844524104046450360b61a05070340500039106000b400b0348520500e82012028400100310003401e000c9481900d5034006040d0b0131010b03805000e003849442035a00b443c5094840c0a41c60402c3e84400c40403013405d000601c008076002c9070990803010b0b401040c0030344541820304071403d1107a80c000f120304130310000b01c41c04241c5c48458108240f1205031810350307e4802ca84010f490501031400d180b40c05802107802c500c890a600c4a403940d01510030741e070009015464014410b11000004021204c40591200500500d030244074850305042c2c005c0c2004007224149010004902c61044000f0071040d100c2d0119891140751640b000e080441c050011102242d050a07499201f003000d89840b829031205810301000750400d4549000a040050401242602c560b901120005907180110034501070521054441c0e50750303d2190341c2c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 364112526 1250 364111276 364111301
    0x5010915032004030803150303031b0d1b0201050402040e061501030b0604090e0a0b0603010504080405090405071703090405090c060403080c0f0a030804020f010906080a0c030f0e070806010e01030807140c04 90
    0x25200c1c0f07040301107c0c00340906405910702c41c4d803040c0100001d41039101802e860450030075800300e8880071220b412801070030141c00d00482c4044a011820304069055000622440c001c4405020803c42509107a84071141926003030159240c03804000c0c120350107504420801078002e03000b0f9150950b560111801c03107400c0e0311403980d585c000c000340d042402203081159800007801c81c0204032605103591011014801e9120301c034000c00f0301100183c20302c02c1c240134100c010701c0c00c60001446074115036059034496100c2c24810744560701c5e190101c0c0080c0c8002860411858003d0b060500d0503041d520749010540090200041d41c1c410806610805441400b00c8110207210b512103400301c0c20720348100301044024a05d000c0c1080040e00c003c000311a0b00608070ba03089803000c140000c14440005003240900710384911120001d05091500c1a00e201c0010568125941c1c90242c91003642c0b030703480d01140f000080c4009060000107000302c5021501c80350600b09000324100440e08184c24410203d8240e03040c442864 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 364113776 1250 364112526 364112543
    0x7080a0c170a0c1404050a060e040906092301020408070504020c0313060e040b010203120c0901020f03070f0c050303160803060d0204092f0109171e01020d060501091503200403 77
    0x1c036003160008504c01c503440031814658101030600f00403410310201449104e04001780c030700e144049500c441c0e000351101c42d001081400f20041e1070070080031008282408241c0c4110421040320b1964040c402c3d2015a0310540140a03864030b01400c010103500701e00c0c0b00307042c02c0c042041504c00786009040f80e80000c0145480f140ba110300d54504200c00c07200c507041914199001045052123000a1041e01640072540d070190796214408800102d20f040743c202c0014186101c0040e03070302c081c4a0031654468015200c1c484031100c2584520500d500c9000e10b030607002c1c4080408100000080c03000d0044c5501100240140764001c0c1144c00143c01d81d0300080c0266031030180d42c0c1d8568071603408c1152031200f20110303a5105402c0e080500c0000d00560070303445000c018610001204400401c00e1220f9040410800c20a140c030307001e01880c4a000754803021054000f6841c00308000b9855001d0194102110007501400f55404185481940940404013080038000c1c210303803030524a070800c1300203440030318000d9140 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 364115026 1250 364113776 364113791
    0x150a0e0f0a120906051204080c030403030203031f0f0e251106070203090f0402030c0d0c050415140f18061b060c03160507060e03040e04030e010807080a0c170a 70
    0x2880d1088480740c1c54410001c1d044404d004164005003100e445000105150b103d136665400e0129a901070b42203041461b000014000044c181d00002840c010301c0c0b040300081d8102c50035000300058130064403a101c2d80d07581e40c0ca01080b01183c5440d04580c00240074403001d4000b00c0c080140340d04000086410804590710568040145804102240d0f001600340011840c2ca141c3c4000640d5450080740c200b0310882c0c0000020b500e840007042030780c4c40d665100034280b207260500b0300003034195003090141000c1207510140f0300c6407861003111103501c20000780c000380d0b1a02c3c0902208003070302ea10861800300f1010000200e043c6503114400207000300d81d841b416508102d44c2071807040381810000f0b09040a164401c0c8280100204540c02d0f284d0000081d081081c0c4e2103100b8504000134040540300403055000104000071000070381d1181078802c91180c2d540307081801380d600044d80d42d001b0544101001885840010f0000101c0c1c0d8071000b0384000a0a2802280742c28064014010364226940703040d00b0746030701c3c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 364116276 1250 364115026 364115033
    0xe180106020f06061e0607020a06090e10060c140109021306090b01020f07140a120501090201081e01061809060b1b1203060405070306032120150a0e0f0a 67
    0x807552214003140b02402050a005001401d40c0c108402001440550100c50441642c0d500c0c003202c0c10340c0e43c064200c000407540c1c1c0001400680c05442001a09440d001c00503c0c0304e0300259696091759529100c54490b00c8036911804d0500030000640358003591b80c0c0d1802d201503659a5045101c008607180042451402c105a15081c0e6400065441c1554881c500d4000c42e000003003005010b88503a43c10380301140141074000f80e070944103540324034034220001e0365100030700006410185c0300074003e89500745c0544418144c900303258001c4d020300d0406541c6000601c0410b02c101c210850704422461040c00180d02c0d600ca0380201d420795800304601302c400240f075880c03403440c0032140d0b440302201c000075020311500c81c00e861036503100080c1601d10030340d42c810010702aa0700076031211010750303086019041c50110440012809404041d944c80100c0d41c1462514445146890381602000c0b6410140240b42c4030810554840c81c07025180e8402c03591620403002030b41204210201030402207100601c4140c04a08 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 364117526 1250 364116276 364116283
    0x503100507030c03090302030306063f0606030402240913051006050708180d0611120c03130b0a0209030a120906020a080405010f0207050a06030605040e010207021c030e18010602 78
    0x5901d205150030681c040e17000c01c1c2c0110980303500c41010381e10166078290062540b990b80d20038000102c000300c03c080020f1001d12258070240b01d08900c0400840581c1c07548402c100043c041102c00940c00903010303000301515101060006040b000303507042603080000000c00540c5c9041440c442007911580c5008000e804a0307c05441801001035040c4030345001d045446918092180b4520160f0038030600003541c4007510342003007034441c0c02d070089020880884050a03c1010358880120085940040b1001c01c078001d4421003240e01525688800c100e10a15981e50484a004000c10b00c40509900740454100d5440c02c2c0700c032801041c41184044032440c1c02000180c02000260003145c115840f21000030001010030085400f5184242040b81e40b01c03444001c01c0f4501302c0c4540103560822000d0308009007203609070b00300302c4c165031089400340b118403c0d21200034203e028108019610010790b41040fa440c0d03182c5e182e4141000e0103890646081c0354100e0200380c41320b4801c0c07408050904c8510042050a6050 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 364118776 1250 364117526 364117541
    0x4030507050d17010603150329010e070806060a140a030501140109061e1809020a02100506100c210315050f060412150e1f1b12060801050907050a0e0c07030c02040204050310050703 79
    0x208203400444c00d012000603703180e0001c0c40c2601800b0001210341000c4d00680c00c7e8240310803030843c00e580c0c945650100a0240c2000c0c881e04240c0e4002034501d804960003590340342c0c00e030385141e51050340c082c5119100240d4810405609000e20001d034401e084900403450324800501000000942c0e52410014000e103005c0d00c030119581c000d440c020074040142e540040314801411103103040c290f680140e0504138903000c1c2140e00703591700c025440b0002d511541c141d049503682d80d01c0304680e2540242d540083c40750000d0240521984080100400d000f02d0003004000c0d403039a4014074045464183c0b08e122001214015903508030558407494154214001300c0b00c0700c8202c941804000d00c05c00360b85000000d400b01d003c801000520825100c4404100c0340b903401600144007003002840181007002200d0748508060183c540641c1c0c01c20404221611400d060710b0043c20310503c560b2400c00030b030710304541041007084105c0e486034081000140d6560304110b0f004003000708500014035802c01a07406011102e40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 364120026 1250 364118776 364118789
    0x90607110111071d07090b0309010b0411070c0902030a0908040303030b030115150309141501151103041e090905010b040f06080c040e011404030507050d1701060315032901 75
    0x4410a001d810210604c24041250b81808101c1c640c0301c1000594010080341c11000b9031141c04800c10405c0304054011540b00d1001781d41c100301d20064a000d849142c81001c0e40070300780c9043c0000411100c503866000b141d100201d0780000848407250b0b56003042e40d60040e40154006a00c80c42455017500e828428806031040b40c440340c0c9006480c000e0340b190345440c000840d03070915540c2c1401d0300a10040d4210720000050200541300c800000d115000f00c12034083c0100580d151240340302403422401851042100703900300c0021403c00d85851102c5455201b0200c99a486003102d040006040a0900802001070720840012034010081000d00c03048802c9500088501810b00008001010010441c10034101e0103440100c0c0300240d09422074050300c1044580300e1003d544104010030316074844d0240510600c40c0040e036901803820002202c441c20609001e40c5d04240b41d800400082d8025444102121031440b00d00180665070749420b81c1c0d1549203421120100740207a880c030003880c401e10000780036052 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 364121276 1250 364120026 364120033
    0x30705070e1302010c06060f090c1e051b0304050402270f0a060e011b060501061206050a0b0a02010e060a0605010306050118090908040f060e130504050d05030c090607110111 76
    0x4014030040b2a049881e0400303414058002c056009020300c0d6009400901b01c05403111101c0c5a5440580307000b449142caa0308001030446042800007500422400240000c9513036040c200340034281402045115040b52040b0b52104000006103034565002600441d0208284c00706100c2c00c40a0b201e04038007414500314801e10b9181d8840b14644e0352814803209503441352030310301030750b100d94070050306c0c102044d041c6038807071003910b020810800ca0150440c1d4181e6600390f4030600e4094008601406688503402056881680c1071001c3c00314500490142c041440140700105042d1340004007113060a40a03030326110310a40328501403099503014080d0b140141402e2822320b101c074183d0a4011031840c0540200b0311941c0d140c8002d04140302910b41610090040107069030b0701a41e40f0500944403020304481940030710440d07501c40003801001c3c4a01d40c8a070707070810080e0181540d201800c4070f0a6100405201c00300c081070000744110b4030b60f90041e02a00b4411540c602480d0041000500423000841a0030319591 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 364122526 1250 364121276 364121281
    0x3021b030909010b090a08010207350d0b061b010501050a0f0e01090b03120c0c18040206090d21110105010b0901020304031b0b0f07170f0f0d0b0909030705070e 70
    0x1180d054803141151100c1d644ea58540d0340c0716001071441590340c1e0221600390b0000c1090418010319414895070f070f00c120b00542c02c1c0040c944800203003025400c8407a202e400d130300b804485aa40420382041300b01450051004c2d00d03240010340001140d04030a11a006181e5690f070050000d81030080030003010b0440843d00121940c54511052004101402481821902c5044402d604d1306d00f0400d4105560051034030544600f400c0001d542c2d00d08240e0070ba507100307031600c8100030f022500f80a0703030601032074000e00954540340b211810312105024489007241c00c40c00d4800340e91001d0045103000b10b0100b80075a281203412801d840b8050954106800089000f00d0130044640c1503a0000211411207511440480981c02c000d0040b003491031880c1c2c4000046200001c1001744001600020700040b03206102c0c1070f070030750007000920502c1c2c01043c07000700d004d00c0e00300702a15001c25a4006802d01c8106550b011912051020208450042c2658202912b610116024040100c1844014041e10703039822a540e151 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 364123776 1250 364122526 364122529
    0x1030b03030a0e030703050304180c050f07060203060a0f0b18030601141c0602030114041415011b05030a08040b01060f05070803071101050403050a030b04020306060d0209030709090303021b0309 85
    0x20b2141c09104001e0102149020303c1c1134405005101c011034018065980b62079559640d800241c5541110541c1c0070302c0c00b81c58400c10b0380543c054800811001841d5814a0007507554040258000713081150b200c0a4000b001958514220740c600141420328809529004140c01010400c0e2803c0d101912035003024006000d0544801c07920f5001680845500d819541c60800400c00b00c20000c0002d41310704c1c0000000310b070303030070401d8968800703005c0503202003010410a1700c80c10100d400548032000c062070003401c820050741c8551a000000c01116240d0300e12030341c4581c1c400e840c5600c03809a00000c120303100100001d00806410440c010a1282004403030340d9141c580040c12071050540c001c0c18103502001140d80c0500c01c9489044929440e8000c000d182492308000d001900015075010001e0b0502d41c018440c0d0806009681c000e41002c1c08950411400544400103034100b400c420707401d0300c00c0034000201d0000303900a0744a400d00035200141c1d0741076290300500e080e003040c2446203201d6108120b0100d03607 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 364125026 1250 364123776 364123783
    0x3091404051509041505010807150206070815010201020c03070b0403080c030103050d03090c0e0702070e07021603021c290a0b180601021204080708010c02191214070f1101030b03 78
    0x10b048482800c2941c0f6407501d24141001c0040c003d50413407030900082600100080ea101c191009a210030b0484207410104a0783c554080310300d0310008d200e40c40420b581c01403d1119004140c4140009410a0318030110140342d900301c02c205071501c2072102d007071000349a0017038079054010b02c460a40900d5581183c80b01e50381d8a442c2c0d102030301015600d4036018140f04400321140003800340c283d0003064070308018000030f5031010075025096a00f00c040001c24081400040d011402c0c0d1070300700305840b55616580800c0b5900b1b0f0050207010305c0e03052007094400010400061402c0c0c1040c00260080c503520031103105082080001c0044102a250407003010701c5580c3c031103000540500780c0001c81240e644020040341007a0300040c1d0010790b03d002040108008001003680802d50795200000c00401085540c00c90781c5620011000615884507007803180411001c42c1c49550701e00c51810a038184411031422518540e0000c10151556103000036580d041200110251400c02400d2a0520420186600090700d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 364126276 1250 364125026 364125061
    0x7020f03071707060e010c120b0d080f0f0c1b030105040804091a030102031518040803061002070503030415020f150c0703030f0c2a0c0b0901030b0a030309140405 71
    0xa103a000030041d52041c1042c1c0d0031203088030743c41041071120b6840c03401464080d2664041e00d1010401464000c0344601c1240311b2904c80030001824051940c01e56110f0110b40d901c001c00581c80007904201202803c0d20340402401180c2c1b09400401844100c0303001c80034804c1907580d0580c1701317034140418040070038030041c141d400351928014000b80681d0301c1c0c68000076084401d024160194004010400f40d00c10307a072a2004400020745422528011030781c113400340303135408460041807040c080c0007191440c1040b408013003202540e80115030140d030301d4600007441c2d03400991111007041441c052560309076134180710b91480c01c41e00000420010311010f0f030315080301600405400200320080740c11010715129800c206d216507a404000c12071011850002400040341701042090740c0440200300c120304100c07110910403980c0114200d09014200b01c20307412030b6800003c819041544400700004c03169500c1030104000c0d88a0b440b002e0036107213403034512200c0004106000b03224915003400c00c018141003441506 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 364127526 1250 364126276 364126283
    0x80607080c192a02060f0924032403071503110d0203150a0305060c162306010b091503040201020109080408010209030106090c1b0819031407020f0307 66
    0x140d941c0c0d407040c101c40c49004903030194444408a07481014050b40050714011034080034101c2500090419240032107140d0039210094214404000840d5805034400160409540090854100c4007081c1c80d1040e4907160803e428590040000601034080e20300054059400702800400c030b4607021040020f41c9072403c070301ca00006610860030f0b910100d842580265a40c00709480a241c482101e900d00034003c0d00103e508020900130720a038075480386084101402200d6011004242035030b5101035041c0250800518180f201e690004110005242004442101820b44004000b107540c201603251511030181d04c1003840700c400700001c1d07a035034031883c80f4881d103113000301c1425a803500c652004034010015000d014203c400301203404103e20310190024100e0341002c40c020700110780c0703408000c1c2c1103c5034914043c0110301840780c1d8460100c204061007203103500030400d65041c010007885d0f180401d00c01c03401400000307541d03103807640b44648810f00007500071000d0300c028030800080001c06966440358203000b8 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 364128776 1250 364127526 364127537
    0x402031b01051c05060406060201050105031f02040f0b092e0302031008010e070e06010f05031801060504020d020a030608060702030a140403020d03080915100b0901020111070507050118080607 84
    0x9400d0350340140212001040780c0c400302002e01100710002c03401414107481051266082880010352640305006050584400402030324403904003445400340c0701d25080100200940038040000c8152000344080300400b0440402561986c07031108002e0003025860f0801880d81c41000040e0380c10fa4172041c1454498100d0800507920348803508001000d503455440710040c1d44c2006280c0c1d0703440c4404a12001112910036056003951207541c010340e00118031255442c00602c081c00040c0451041241110b420f8181100005d001e03900d0f0804a0182e0f4008414100015000079814013495414400c40004081ca40d000e0030260515100007510b80c468203588904011040e0030030445624ad003c222001154020007203004c2220394a006000c200048694800a0103200c072004140c055184155229001d07182c518980c40342440c000c10a55005640d40c91304640d81c40b0044c04004034120001d0100500a27801001d1161816000400c94061211515a82680a10704126800000907642d4120385a800d04 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 364130026 1250 364128776 364128823
    0x30e01140115122315010807120207021005091e0d03030c14070c170d09060f0507060e01020904051e04020907110102030717010609030209060d0f020d0812070305040203 74
    0x4840a003410f1408580103403410501c07043c06480c82c1c2c0130201075145035400c124156170300142601030001d45145640820f642c4c0c2e0000303076001d1158034240750300500c1030310042c141170043d00462401440c0b040c011010440c0010451010314000500b0700c6041840c00081c1640100000452130310702000034000d007490f840e4405032121501481d026490040229855070701c550705400c06912000340d40c0b00b44104a0340c0d103502260001004600c04001607407507100c0040662800004444e1003180001a40800c01e080c422071000851a000322003041700d84000142c1c513641c0240c1008100e40b0064426140d070020002514920a0181d541c80d07405a0110349614059540340301c140c81c161072985c100509940300100300036074281c000300600300e1030311010700d411100c2ea03c0c2e0005651311425400041e40c000050000110240b40c0440c4042138203104d0741e0a554590415400b28114420783c1d030342268120300c081244095102040e84941d40454646400d0096003000d801003034558800980208101d40b00e8404c = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 364131276 1250 364130026 364130069
    0xe01060308030405032109060f07020c060c01061d1306150e07080a0b01230904060503010905030d0c05120112020f190f08030a080718081606030e011401 67
    0x800031900440d030039660b03160510f442600c1e580303c0c0c62171620011501240042c0c1c10030352018a0310843c0791070010815501d0303641d21a80351400041030401180701d01545100c4d03d1300c0304ac001d800d9031a07041e0004140355051215080d02e4161041c008019840c1e02c20410150501440000b111545c10440000340280605c0f81c07802c819616411200130082c10906201c9e001e0b40c80171202e4498224154200900d40c020f4004440c00c42c0004244400c00b00000b030140910801b1304002c040c2c1e0b54005000194040d9107030f0201b400e569110400380d0300d40d0030220349408102c24078010b646c00e0b003c0c586001031500040031000540c021043c028003200300d88a040000c11501c510b004090071300340007040110600f4001c1d4040d004901103010b07100c42c0d0314103002d0016280c64000280c807507265a98030b030300c0d105655149040328a640745000000c412032100d0b5000441881c107200e10b8084202d42003c1c20545401c005015040d0b0306c0c43d216000582c0c0c5420020041c4800c42950641995038003908c4408a415050 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 364132526 1250 364131276 364131281
    0x301170705060406170f040228170601032001050a03111209060a0b011b0b06030712050102090a051e1e270c0c0c130e030d0905011d0a060e01 62
    0x10401500030700c000070f0101d442c0d80c0025138030300c2e01004510300a031107940d4810500140d88044c0c900a4118403125850070f030541c030b04404031824000201e1500c01c1550b45101c076000c1da0400f00411b0382c203904020014014040c07255264521546116240030701e1040841c0003d03d544180384503a01051740d03401c0180814102002140d1146084104240050604104003034032880300b03445490b801c9241c40d40b01029540030b08104201d484d104925210142401e07118040100801803050380c0c103000d88080460325620b03081e0200710441c090000180c0340c00c01c050a2003040f443e244c000c58421042280300300051461566500c1c6518010303902c1642c010b5007440341020301e600001120380d0200e11007000c03249900180b080341d010740c041151100d0454940c2e04010126104560440f07444d038101d40450f4400b070a2201203102008521070b400140408000074841c25a00464000d42509440d004184203010090068100c86160071100c60b080a4492540c2d40d520020303044000d0009031103c045003a00202035 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 364133776 1250 364132526 364132529
    0x41e090c02011e140103080304030224060114040302060d0b0609040f0906050a1829070206040210110c0f060903160e0a050402010c0b060d060c020d0311090603011707 73
    0x241003804030414544020740030300080c100c0000e0002c4a0241215003446a008150003040e0700c0c90b2441d0700c1c0e402c507110030070f1030344c40200150b055114281080d158000ca4404c0c40020f113a01d40e40064003410a0300004050040c00c101c844c109890a000510150b80c605085445030240b605000940b0240d05000c102e05000e2030a000d54032620740403030780b160a00d1540020850510803107003082569942c44042045982c2d403140c01c0c40030500450309100051490028a40f04240c00399801030f00810001c403030040314001c9500000580241c0240411402c108120311809126400c0503000a04140c500c19560506041d40500c200d00303a5400c00c44945843c411075081c2c41010302910920f00b1603251760508509284603008100311100001140c0d01c2d6280310701405140c2c16515154188883d0300d400100640c0a40069030145000805200080591081201042d11900a40985a04003d025040f039040c0451540c24a1040144101e9503071480c0840741550700c103101c156800414019214a4500329 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 364135026 1250 364133776 364133789
    0x8061c02030f0106140d33110c010e12031b070507090c02060903090d03030207060e07030b01090e010203060d0f03021c2a05101112010311030120041e 66
    0x15020b800301002d00640010060340c4254000d11204040d010500010a4805c0350217803083e0f040c820a0451110100d1000741d410080002c0350040044800708001152041d10000005030740014074040401e00131702035481c43e109c0aa000c0c140b040180390f9008441d2200602d1070309803015000c0c01c980e60580440940e104c540d081401c540f0070340e1700d40d041a0010002c1184000140c8a19000035107605d100008840400030094100d0ba5000c0c919601a80a9046004119070b8a13441c3e0b440c01c47c5c05a010407100b4000d6003e40d040800e130b9403500103414121040140c5c841d08c030b41d004004010300385d00d0b0b40b884000d0080e4085a040c00b882c240e801e08904029442030500504000c842c103910f29142d00a84404203268402030500d00e0303041e807041e82e8076031a00301c000050203600030110b101c4424030180e01600c0c0070001c041d2a0785c6400400080b282c2c118500360411520650750881104050809100e48590459140311084d04414208021007443c0502d101ea8040c809114080d007401c8207205800c540101318 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 364136276 1250 364135026 364135033
    0x306030b0c0406080115020a12120e0604020103060b040f050d081b060108070506031510020f01141e010e0a11120108241306020f0405031e010b01020c0108061c0203 72
    0xd20304110007565000e4496000000c89183c0041503480c3c5074602081441b0254008204a06190765014448500d103001c1106001c0206a0890111558028040034041d0540586a586810320015048550607001141600c10a0206005d644c4512a88c031090f100c007214084012420ba1030040e85500c103202070380d25102a81d00101c1804440099030506840c04202a14900d03622082400880d00007120460310b04040d041030302c9a0750034481c1d00c13518507000a04c1034512400003c038410f030a4884060906141c0b620340c00400030074503031003a00700a50346640305071306489500d0142035001e15a4003504e22400706549880301684403901c9000c442680401c090805da1035a9500c0c03050703032601c40244191902c0700b0940c1040780741446800209100c3c0030315507507008034034105480d610000e4203c0e980e410001c1d4020003000c01d8513a0100408211461540580f071000b10403042c5d4a1309641d40190882d041d03602c501c0035001160382241d02e15501800960341e05a40c41344400f04200100c4103a007010b5051301 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 364137526 1250 364136276 364136281
    0x15040b0402360303070c05010e190618120305040b0a1101060f212004060b132408150310052e030c0e0417040f03020a050d0b0c09010306030b 62
    0x4a8a006400061051000c0c0b012040145003070503128855000001c195118030301003400b5542c091703460329074911000341040c02410701d445486004103849803c541c0100b1206280c40c014501218403800c0600186010700000e040303160741c05002409280a120710451002c2400302059103c3ca0840782c13071110040c02402200d944508842c00100e2500030300398006441d100500e52513200207805048151702c1764640104494138040d21000c020741c00d4600703900688a410008275500141c010f031001040038180c0c20011841c001c1101c84407089800c01c00c481c0d000000c1b80d58002e42e006078a15920400b111140c044003201100040d081c41c41f80c101c2d410f4003600d07240030b000f60300604c6154018522002c242001d40280c00d50001018400303148001801032016030300c02d01c10b42c29203982403074206105664183c0000002240d40800740c21541181441c480745540403c1580b400364010f800a2105591040803894281c440c059a03c00080104c0c8030078000042c400d0540e40700f54441c40046412610540d00390 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 364138776 1250 364137526 364137577
    0xa120804090b030307062d1a0405180102070b01050f011e0c020a090207150e0106050a09020c0312040b04020a1d04060b0312040303090e010603330e04080703080c0315040b0402 77
    0x42c7c0d03050004200040e014100e02c02504541c0b26040700e5110b10031801c1e245003045410400035260040101c805c50502e40d20080f02500c0c240080c2c40f41c1d61094a01c454658101780610007021303a04d9030420304000010f10781016501d00180d076120311b081e052900c681201650b0000c42c0351a0000c1d403001d0a61440003600b1002c0c0100c5008540828060706428004442c00c0004942640c2c218007030f107039021000000410900d5031a030700910011041d0300076603080403141c140380702c2c0d80300c01280c044e58984285402c0008505d0507035514005060001c96030b140e07010010340c050500050003040200f80d035503110b0100c149540c042240c000118250741820b9a02d6840e450000c0c0500d5413407103642441101030002240c0740303000f8042c0901d510000020008021044038810b141c0009505e4880c000410003440443c0901342d80340c0c114845c0d40100c082a6642803c0d280040001d0f40c02800192074000a205111580308259414400031030b08070740c00300b580d04000e400a8000e00c20206800c0e05021643e120002e82d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 364140026 1250 364138776 364138811
    0x103060506030c15090f04090210051b03070f0318030803340c17120a020703180503100c020708010c0c050708010507050f07050c031203060a120804090b03030706 71
    0x3040150103950780340f000801030013020482c109440420034014881e41e00b146c03d1004015085000080001c918a29980c0200d03480c4040f0101d0200001c1c0009a01a0601d0000501d900052000d500075454150140c5400711403607000100103080140400501e680c40800a844001564108502d66038a0900340d440c1d0840844d4240115141da004408c07282550000d42d900c1e07084841e45071180510300c1c1d155a1032000511091000d1180c005040c0003400341580c81c1c0070340c0ca1083c0c0031001c1c01aa01e081c40d04014003900442034071141b245103801020300880e00c010a42c1c1904104805001c43c0d100c155200076030401415412441c031961800e200280c1d480d40c04020140c40c40d018409071100ca85d00d44072250f0a1712000c940311004540b0030080845040c032014020701081b40524142c56403030b2680000281403000c0f50303040b822178078000b00501480d4079083c020b0100810160410301c10b104001c0d41c0c1d400b5640500d102d0b030000256905070010154905004a0300901da10040401c134061885018409 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 364141276 1250 364140026 364140031
    0x20a031119150f020c12061b03100605070f0507030c030308061f0305060307030f0c06030c08070c20040504030e1224090a021207060e010302090315070909020f0403050f010b100804050307020901030605 88
    0xc2007148c400c10354083c5c032000e10443e0b0140740081d00e61354000c0e041000503543c0b076008400491b8103090511180022130001c0c49150007841c403e8408601c03007451403d0040020704050001d6100f10b003400200700f00320010302e03451841c01c200c5090202d403a9681100090a01300540d00141421074059504410840c00703110038015a011a1400c22914682c0202151222412a4504045010751284001240381b042ca50f00a01c104103e01c14030f00f16551340460305849043d40c0403030100e40c0da48004c020501d00004911000752102008241c0c5440c080751010300c169800710a40010b007c02c802045c41003030240040c00165801600c0400c40d0100328404d00e6990380c10380300319000602088120320f0f140d80300e4000ca80b81040010010041070195500103030400001030646000c4c000c44a80c00262402c0303a0000d800341e602d007081320316140da1170760405604029190031081c00d141d14007090058556284083d140100304540380c1b8224583e150b1800394914400d80e040070350f009084a0001007088022b802c81c1c0d2 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 364142526 1250 364141276 364141291
    0x4020c01063c03080c030d020f07030306060503070504060e0f0d080309060a06050a170c04060803040302330706140f0601200303071803020a031119150f020c1206 71
    0x2d0925507411014003003040d0302801140d00341d681c0e01c0410100d0000d8002d0244408003100f030300e141c1800003e1010172030b0321038207001e01c10880100310711041c0343e014880c41004001d01d0402da07217140f4203404000c2c90307071240c0d0080c441400038030a12170500c0e8072180f2500682e05805006441300c4100741c00c0510f40d9400490b40c5500074400c0c20001111890a40500300403280c0240401d03461500305a1100781c2c1550301050344d20140702e881c0700c444050f5a50300034440101650ac0141d40d5440c158014411030b410307409107000000f403196034010f503507001a000d5403120351400b07000c0d079480d10a94a0a40702410b101550f910740c142900c1d0074440c9100c0c03207895190040c507098966024070002a40e032225138416154070161241c0042c40001c00b480d00030030703050140380c1c03010300750b0881d10391668001080c000954205582465045292420500b040740050032504400818014020b2030092101060340e688501601001480403070704031803d0003000f58003140741005250400c6004120806503490720b017107940c803 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 364143776 1250 364142526 364142579
    0x601030c03020a14101b0c06091a0c0d052503090f0e0f04080a0201060503030c0307110102060c0702062a0c030705040e060a05040c03080c071811030604090204020c0106 74
    0x40c51012000400c0701d003e001800c17070802c58003103080555184649809040c07482401c040050001440b01c00b60034040c01c11760b11a103062030f00b8000d08010309204940004002d00d42003100760400c0c500010f406440c130701e440c502135540e081c0007049400007100c2c40100b02590b041c0b903143d1000f0180c1040408040c7d4000e250008420350b55070400c0480c2d040c0076240821491030120204011400000051004110318000811000c1c0d0740e401191551b1f0048403001000d400100d242c40401000600791103440000748001c1c010b07030070860003502c1c4520402800030300c00c040c00902c8514070300d00c0011190002c0740e4000310301c0f02408a040c10980f99001d0205240c40303401182c1c000300c0d0500d0507201d01514911550300401c03095960280480003041c02070300c01c0d9850f100d003410000000c1c2444000305040d0745c46802a0a4651a2003031034400f01001c0d414460600f801c00202035100382010042c2d0380d00c0b40040360086400a80e60000c107000344588214480c0650070140045441100802407400414001c00720 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 364145026 1250 364143776 364143779
    0x30201020c0402090f040f060b0403080705010506030f0d08190c020a141603020409210906090f0e0c340318030503070818040203040609030e041122080601030c03020a 73
    0x81008078404c44400660107101c1d06a0380307010382000e900110070a402e89200003070341625040711141d036420540c81100c5980d0b000a420040003428020345800520aa0092066450807070b0350f2501c0382e20f006400c10411401d0300000c0c4511011915081c80c201c80c00004200d11060741e0b42c02929522150419600b0014004088241d1400020005801164042c100d0042419a420040680349a80058894400008074211114114400e0044404260b168009907a141001c0a407900f00c4c181d00072014051241c0302042000d80c421181940f0441041500356190f010404c40c0b40081d400001d810342042e41d00c1c0d0100f108142c1e12031080c00441c000c0c0c0320300e440201e403519121703420026808020903a810911441000400c3c82002e0017a0343d030f90000b0740e003180b100c14000c40c0482c2c00445040d1000c6403103200040c1499001000c0d00b821490030707a000d115000008021180a00c5803078061012901001d0318103032203011240e40c0710050b2180d541a900d15503560304040050b0100c1d40802da114910200c0c0 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 364146276 1250 364145026 364145029
    0x80403061524020607030213050301020d150b0307020a0f06140c13050405130308190e060412020a0b0105010f12050c12100807060507021804060c02010b0f0d020603071710030201020c 80
    0x30b8615140ca00da600030580343e56000700c110701940000780c4007202100c50640c081a030f0390b004e0016000b20040c03410001984882800113100969007548180705000c408c0043c011642d5000c10950030043d00104849260305291034200028040113000e4180d5660031024031079903c40c84402071082c00e44155840074540d48510401003120f001303445000c1075040d00c011341e02c0000c0c0038100c29540003214600c0381140c182c0305d840403415205a201031480c0791b045101040100030202002c4581c407000391000f07000f01d0a9a58407030701c06c40c0c41805220b0500c44d48146021180c0c3c4030340c00e400018900040140050300342650350807a02c0c2c110301e08884580500720000340c50006040040d8040301d01203001003103410719041042c0c646600181060360800307600802540e8548a40356514080c901c00d2100280dd0044a01c0003400c603049008000c0c8200740e0340003845034580e00c1540c803c03c007940454480744d9940703e4040540388000f0365104525100030304820811000004d0081008490003030b000ea801c1c200a810 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 364147526 1250 364146276 364146329
    0x13090519050a0614100525120813021201020f070c240507030f091508070807082418040506040302060c03010b12060a030203070b0406111501120804030615 68
    0x20b00013100c4042010091500e443d0640003a0303d485410264034080310031040300e801e004030b000340b803010048014040c02040f2401185d11043c4002c6d1178170300c0703640c00c1000b41c0b02861415004064414a0041101c000e981707000c4d41152049030101c206681c3d070760001d10304045074422920074152010494807814809072801c60800c0303808841540c0306c61405171255800d4071003c52040750b4508004810714041040c1031350381c114900c01001d0751101c180d94075100c44018044d890091444040201c81c40900c407880703500702d8202880c03c6451406280d09003202011804d60a8424440440c0b0200d0b0300c180018480040f80c8a40100c3c042d909450460390307400307a6515584402c0c801e684040c5010400c103101e080401c0302494001070010095104181c0c0d03900040d00c0e16609412040501a0000f0100030303154011100c82410349426010305607400f904242d007100e10b40c051003545040d0511080800410034510100e170069503015404104503070b80c208404802075041e0144580144000188544603800351 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 364148776 1250 364147526 364147529
    0x6030703091a060d1e0209010e0f0a060b04050d1a010b07170c0a030c1b0e090708070e06100504030f030c0308071d01050a090f0828080a0513090519050a06 68
    0x140169004d04020f50310780d0300548544040c0c110054001800740b00607a13803009010300912481303400e4a0b603410110000e40703a60304041d0140892a240140402151301088103840403602d003180e4030042d58510342404500d2801200f625a40280031600209402e0341c001c02621829000700d032003104070409620100800d10545160000940c00481c3c14400644200c0341540068400d00d2070100c1c4a841680c2c07402c0d00c6505421200400ea400010440f410f0001c200c48070003820510003c2c42014a050b01400c054007010f00700c18091128445041e0586000310112001075912010080c040741c49401d0003408500800002c03000a14004041071405126808541d814800c607505006a6030b200001921958000f008500a00508030f900003100041d201c120303002014010b0251201e01c25880b1065010315440840c030b003110418002c01008200c003801a6002c202440c20083c1d500c604046103840041816400300c2071213030414041020200b1045110040340940b03003003e221607103034031041c001070718410f = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 364150026 1250 364148776 364148779
    0x117070b03010303052b1508060606070305030c3103230607030e12040806010e0601030e030301060804030302040909050307060b03030412021c1403040f060807050a030e0c06030703091a06 82
    0x600000303442c01036943c01100030301c080c4071001b8a190310001c0c1c440300740e0307595018900f20301403000d0702006028002e00501754080004c81c3d1103031034069169005402404054103144051308080340011a08020f0446079180449891004142890401c05030381503030b403c1e0004071080300c1c4604171200c83c64400c0c02c4050b090303280c04006c5d00300780d981d03101c0480003000b2500c00c0724080e01c1109a10030a480ca04030050011740414005481b01d0360501044006d24480a003209041620f0507095035245130020054030b040d1441803030140410303201c9040c118080d00440c0c0008000034a001280c1041200000040c06102e224000c18490030030103c0030503460f40200c3c80381650310b0f0f00050f2401c006180030b011080307003414000503044c0c1c0403801d6100e801d001e0b42841250201039200160030700015240c448044010550b52501008919000b0401852801a400c1ca0f00074140ca52601e2003094400340700178400c40001500c100d44a04d031444c0010040c0c038114800382c40c0603440107168541d0148401c85c03144520380 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 364151276 1250 364150026 364150037
    0x609100e03130506090d02090a0207140d0834050309061b0316091a03060910031a0402032a011107120f1712060a050f0307031b0e0117070b03010303 65
    0x140c0360031310070650f210780c036403650107aa002080001662030514050140b4000d0400685a440c585444840700c13001030581c40da650300c1450742d43c1103e40c2c0401850751010481c03900002141d8480d160001c50800f80325080010000181c610803116400000786100d00d0518003202c00c40d407143d9008a08038074000520500d90001040011140408680c130003401e004646008260b00d695070b1000c100e081c0c43c00c41904040c01c400000e1007281d107081400c140e0840c440e0303800029540e00d1541c4400c80384040759440c86400d00074000041c103550382449006214103615000341c8075000541210f06d025449810810b0104007400180156200e0008805c0709958a05030400c10510254a50800711400341a0880da15200560310303644070b142c110040e1501025541d040c0f2440d09140c020000000c0d490b07002180154201082c0358199600000d01608403900300c403418103142c6031510030800c0440150003000c10202c5030000002c4880074681c02104a2743c00c0c1e8151035610b5141e441c01140c40c4420301c0058000303038 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 364152526 1250 364151276 364151279
    0x611120a050405030f06070201060506032811120f0109380d05030918040f0b0a0b04060609081501180f0f0c0e10020f030f130302030609100e0313 64
    0x4501100805080c18103080042c1000c1d41c54000a14005d20034116400d0742c1c10040a10840302c1e024020a005083c3c2181c0e000d0552401180100d0b034405001146200b0506d50140540c0100c081e500c403c00c01da0a900126a5403030941c0511704002005440b209041039145000040005141c07003106080360000c0f0f40f440300c0c0c0640b22040800e42c41001e0400e580c45003c0444094541d81700190401c42521500145449a002e0803c1010340c90b094038030508202540001c0000084040c1a80840380368042601d245030303214443d0080c018821204000d030442c2c034044001c501140c120841c2411541c0f004102c03012982e0208501400c0c18081c4a5003140341480301c0142034421881d0081d820408000e50b0014078001741080000903200344c08584e00201d2041584502c10781025429080c0c042c0e410300042c0820710702c11441503501c0c4a110700044220300c2c04900c104040106481100003160010200e940074100100c078240c44400b85089044254034000b0044102c602c088155441c82c0b03040001e442c44030703 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 364153776 1250 364152526 364152553
    0xa060e03150c0d060e010807060c03050405040c1205130209060609031c030237031415030c03011b020f060c0307080a18080d14250203070f1109010611 66
    0xa14014141c40011881407054103c6845580304820040a06000050701c2c2d51400891030b00380741550b0442001c1082604401c40800d4005085408440c0191000101070004c5d610841707241280c240309140050a0409004003050031058100c0110700848100425448100800c40d492007840e480940580100300100d11200042c107100f04144901e090144c682104260507215046c0a2020000d00e000c294040003281d6180d00b2115898246030306003000b03108101c1a001011400040400181030a0000a08180c1d1810b001810000801400920049240c4500e021960303406400590040c0700740255032151810000c1d1040c0568180c201c3c0d2840c540340c681089688107002400b846840751542d99258515811440010f4031a010b14070140e12415551075120640346031000ba00358410396001801640f0520107640400070060302000009060003000980c154019081d014214140001410081c0500310b900d00841c01e400725450120381e84c943c2e5003070703c0d0180c1d003250b59610b0381d21000540c40346 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 364155026 1250 364153776 364153813
    0x62c040b0117310317060a0e01030c03021c0f08030601260711011515020c091009110a02030a0c0c0f0305031209010203010302010f0507020114180a060e03 68
    0x320081807400481000403020b4503401c2c1c10081d650701ea145030f19080e1512408403000c000140300e120b0f5001210040c107158500614a41000d8891207600c0b603250003150304c9503510340304c0000500e200a0071000669480c03c0202e440e604511007a4051000040201480d10a40600b150496842015001003a005480720704031904002d114505128609000046402040300401c1840728038074031220719454904070050503003410303486c000203581c109a40b080c10711080210b0801074078a000316010440c0380301042207103480e6205c14115044005801030121403003401c0300d40808d03649060300c00e00c801c10040024030341c02e00c82c1c0c00314280140c10a2000c0807180e8840c0c07080e850405d000d0364034045070320340324501c030103a00c1d01651080f9190350001499031040059220525482000ca100841c00c562543d00041c041d0240000c07180e00304100002d91108580c000c0c80481032000081c0a4540c8810108520003841d030150050280b00d04420400000c1d264410120b01036403580140140c405001c2c22039102c2907 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 364156276 1250 364155026 364155041
    0x30a0803040f15020c1c110d05030618070c0614070509061b0316050f0a020f100207150e180601090513020c0f0a0b09030304030804110111011401062c04 67
    0x3940c5070806074880c68030f0141e00203800500d6a8502600701001c0340c0c0996001010f80c2500340081c82080031058024580100301e01421700c0050031300c180d1703a98039400000c2d074600d01c005142140d015000140700003690f1003150f07004a40d106000811080707004009a6000002c2100e80c2d0340001c2e0108680ca40a090503c082d0840f81905550a600425001403050a41d044080e41554003107490b10994240601000b5a43e038039011078000c1c0250743c00c10780100300c3d401031802c0f50b0350281014112440d0114802c100802c014980c40714003001001c40f00c03600508100d80b081c061440380b120f80c10710307065100d826400c960103079105851302c0c0d5140c0d18120501a400c10100220002280d080c0508803000205010762650348000b04040c001c41c958618100c0c2a00c00b01800c01c00c1c2640c014401c003c0041c0d0402c040c80d4000d0b8100003c0c00f0340c2c07004040121029043c1c1d40000780a54281802c04131001c4544595a041c3d8030540c403107441d034120091050707075031612040710580a00003c407121140c506240c0d00204 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 364157526 1250 364156276 364156283
    0x110601050f0117040602130b090303091009090c050d0f020909180102041a090a1508041b03050f150a11071104021210031101080c030f0c04050d060f0506030a0803040f 73
    0xb14107802900c030f041e00201198250b40c6150009007000d40e20321018083c0b0040c120a0400701e080c04c0d01840400d0740d9026404c10303640902003640303c0c00c0342c0c580070303444802c0200340e8100d00388150180404000c0aa4000d0351681504d20300741080000603200600944054520140981c0300d1039440c1441811040107200001804d55401c100101c0c800c1600052200c2941d84007c0c110740d501021401d004c00054158002c65901c1c06405d20f1411407a4031201c00e9801c0b54000358464001c2d040306800c148211f019600041661103226610244030f030010801d0880680410408811540ca2411003015148001107048607920704025840000b51000414020143c014000505056920880c1400340b0002d45e4540c1d9a070066480c01c00420404445940c403540c000e01e0064640e080c407007038162642c0006420168000e42c424009900912070000356030041c100240b03003169880044c2001c2005111840c0700849580c00c000000e010360500040790001c1c0d550248900e0700e940d03101d440c0d07220001402c0d1000c5 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 364158776 1250 364157526 364157537
    0xd0e0603160806040608030f090310021606021305100225050d03080901020d02070309150504030209150d0b0c0705070503060f0115030209060403031110090203070918060207050616110601050f01 85
    0x2040d02c480410141c51021820000c10790758601e589c04061070716200d4048482000d004002c172201d544100c403100180e05900c0310025840c0e040038481100945266040144c03c030080b8000d8401d0154000b490035a413141c03040c0c0c09100614105100903500c10580a46034114050607682c800007440b4020184d40300480000043c00c1c10280d400d00001d90b44200000d80028183c4003050050350844414518506e096050040c5424076560214550b19402081c0400d044003a410303468098884407904001e86910208040d050301c1c105070b4040040d0051a4169181c1c41201004112403d0014446024613072642040310355030b1030000c0d1480c0c04c0030041d0780307041003640034000161261181d0000d4000395209460307103d40741a2901d8a54685915a0140c2007500c2c2005099005a1000718084c420351f0240700300803070000203461421b1842692001c00400092001880100740b19000c03030500c3c0104040c0f840c13180c100c1500c3c5400c81e1082e800804a504d1500802d00400c030710714205407504103504060518 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 364160026 1250 364158776 364158779
    0x13050705100c02010206090610051c0605040804080106060503010b12090a08030703060614070f060e0a0b010b04080d0f02100b120d0216081b060306040902030d020d0e06031608060406 80
    0xc100c00c941c10a07018004503040c501540210368040c4000c546c0101e0f200020b00c0b5900d0980d081c01c03109081c07845180d0081c54810074511681080070245034149030000390074840750a16142496580d4402d106680b00c235441c2440215100e0710940c1203038100c884122503207090907000c205540e5003407809050070005110300c01172007001484031009544502002c0d02c000402e140b03841000b61170340d0080512a2001141004241c0000344584003089115400c8100012420b00f116159460941c010344d000d440c2c0341900000042001845000380f0a80f004c6078250307030f40c1c0d4141560a50301310018481c9003002d03030031001001150b480ba9511840c075800c801031520901c030390307107062480c02c0c0510040d40c400140c03c0030307506040304452017035458014003a207801404c400d605160200107592070005000e110f4080000441d04036902c81c1c201c0d2400036001015510707412a00c2d203001c2e648000b030360008404654400c0c0064541d00e0303c1301c1680c4c49040508014843c40400e8101201e840340700508841d4031641d2441c0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 364161276 1250 364160026 364160029
    0x61207080f0709060501200c0d21020304030803011406091e10020309060d0e0115120c0e0c07060f27110a030c0b0a050702030102130e10050102030313050705 69
    0x40a0040881401910050602015181c10802c858205040306400c15030104481e9901c00140241010301c1c10728644e81c180300c05001410004e00e12051a03001444007104814885003c4100b15888c142400a07401002405010f036200e002c3d602c03001e840100b0a20042010b14680e4268001d40c4500601151070030001070000f075240b4100d46140c03200c40c03104011480150405055020749012140001c0d41802d0060b000a2118843c40c0b001c0100c175900d522803600d00135001d40208030225401e481030398075641c0b18048640b51885800066401584030070000075091640c1c20200d0141c0c0503400307600c1c0740040355181d90703000d0b003404407000c81000d65840c541c080c03e94001411042c90350b2800240c11012a07282000b05e101d5003551051842400c10b00800c00025044410050480b00c01d106150785810750001c09507010300405e60041d4055000007810031891079009280400e40d6044800a48183c480d10ba29040b0f809442c080c4901681c0100041600e1200311200742c0c1d2000d00c07a00488181944440 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 364162526 1250 364161276 364161283
    0x10819021c05120405040e151311100c0b010902070804090b060d110301061202180d0203240a18050a0602030a0609061202180915040305070501021c1d060c030612 71
    0xb95a0b41907040302050505c0315181500401070210711401c010000c4500712403007410b04800c0904050003007001074903c0e07420004103446000403110010640302e1211040e00c0302900b050204c40040324028194400410504803a200b07031141140c00c030180c00d0503d03007000710510050500280c4150b01071024410440050b4440c041d032804000d076000101c1d183d514010000c1c0290701d0003015150f02c54018841c07900603030054080b16002c5641118600c40c02a42400032901345441240701c0ea4094036030003c0b8145421032048a180607c0d0783d02000c120071260504404481c0041f030000031320a030440c0c1001c0e4003085030b07074018503003141200e2800107103299611519021141c843d4880054100011059000e40ca070090440056080f041c2c4c8185440c685072082948421405240a03144032529010030181403164054a0140354810021540d548115010341300c00c0070142504c0300000e082c06a07208148001000110720203010900805140e1038203200e07000d00da00001c090035009021034000755503e10041 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 364163776 1250 364162526 364162543
    0xf0c0902030a150504061211040e0307050106030b100e072001060f030b070e0306010312050f070302010b03120a0e040209030c031c030b0d110112240806010819021c05 73
    0x1940043c0c403505500f8210b403a0080d9900c80d5110703a1800d14104a1070004034451001c040c2c0c060301e65031044001400260051008083e6007402d0300c80414420208001540480c040d03d00a100d03c402c1e030b0392350317403074500100c007040c028042030110840224200d0b0b40604000e600c1403280c6408041c1c00c182c00034181d404c646c5c1c580d02250707070740540366801c0040c000100b81c055004081403a08407000481000442d699032810300c0000c203540c40a04030009000e1007402520000140c06000740c0e81d411040c1030080c0a01002c0746420722a02400005022b484c0c151000c88030b02488a40703680303030704c40d50080402009400907164160035014082100c80f81da41c0611615407040342c5012181450303440c4e98401403c5802c0c84000c0d50140c1203100c80310011800300b007143c2082d15000d11389501104e030050b40c803030050011100000d100e058401105000c1e4040481880300741c40c405402c465140e0f0780e50310015503c0481d1800380072030b410706d10b02180150910450f0450844510140301500d400700e0341d5018a4810341 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 364165026 1250 364163776 364163791
    0x70c18021c06060f080a0207020402040308040819121b020d03050a09060201140408070809030d080901150e01050603040309030c06081501210e0a150203040201080112050a0f0c090203 80
    0x10304800d0040c51520381c12011003454204200d410b04042001e03181c07649580d81d60050050150014800107105d404403846160f01900940d200c5981b40780c18519500a03004003200c40c02441c440700c925480c40d4802d10802c070381203045240007002c01003041d50910b60b03140c003c6801c86411896000540c039000f004a523802d20a07505e09a54020307030300d0000e080d000e40e50442c03402c43e4107054407441141080300d449904540c1221000744c1e5501e03145002c552511901c00b540d074150044c009138500072600103164500c910440360080c403840e440c0620300d850750801c3e4018064a250000c2c01807140f82090b1024603400b6100782004401543c40e61260316071410b20b50710440000d40300a082005600322540d003005103440a0078042c80301c80040c240d080c8443c04044080303080c54be40b07054000e00c0b100c041088104864005a032200e514000b10082d00282d4001c50f02607012800c20000041d403040134101c40f010251300113001d88024142c9942e11600c030000da07142030302d80c01d2070b201001c528580c01c0c0c40218040c052 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 364166276 1250 364165026 364165031
    0x20d210b0303071a0112050601060503071b0303050a06140a12020f19050f010302070308162010180203070e0901090b01080c010809070503030a05130306140f090a17070c18 75
    0xc1e4134070f419515407050f0015090014220250710008900051080c151039450030032580381e54030301004440c084180d24010034617030759956001c0c080c507030550700c410700903c50402c0911021361221504003420a41e08e8a80c0d8111075441c01c200b21401728072014054080c801021440381c1151280026940004040c0d901c00e011005182084140b40010660340007400a0170203609241e0703107460143c842540100507010880c540407404c01aa172040d0100c041c00c038094100204403214882d801699545514160b58000303203021042030100e0340840c06640c00350740c02070052103854240828031030f4000029001201d41e64a840501002981200309075003c0c214201c0208050310500000601e849000351080c826500802424020b60300c000c4110381b101509070408a07994030034a446908400c80a50026140e0b0341303802d9940743c10b0f820f00f6a150380507003900080f9a000741c880000c42a00d68100420040018100002130f41c100400744001c0c081c040d0046c6480a6220342c0d403014000107030880f10741842500d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 364167526 1250 364166276 364166303
    0x3280c08060711011404030e03070503030408010204081605030c011809050f07020c2b0203150703020c0d0f1d03011404140f0f0c0409140a060b04050106020d210b030307 74
    0xc0d40f2280c0c4512500d0514003d00c0002d0060150405260018101804202075000d484040c0d40b02084032500030301002d01181e55460b80d481c4000e00070741007800b034410780740074048070310f01c1000d072692601c0c0550310000c0c0509044108500191059a00361a00700c00d164112000001d40c5411442440c0c410911001001036901e020107000b030a09aa15404a1040702d48100ca0306103c084000514045400300c0d088480c40181800024030b400149680c8140b050807410410042c281d254021f0704804440700111040c8074003035001170700d205032440800c0f03001901c44440c0094a880354030075894541c2c1c010703000086107440c580d284803e004085900303642c100c0c10485d561a600d601042102c10305180a0f01405c803000a03485140c0d101c07010b00c03005520072900c5100310401d0201d460842c0001c00d803140c04a4070b28110f02c0c500940a1b1244003c0326200300e1a00000089590001c102550707070001551b2080c200c0649244000c01145264400480b4240e42d8420780009440070402041203c0c002c038490940300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 364168776 1250 364167526 364167541
    0x5300a1a0105040e0d0e01031116021503090c061803030307082208030105091806091c0327030e060a030207110406150804061803081f0503280c0806 65
    0x8600c1a88540e020f075140c81d0441c00c83d41d0001c6220841d4050529210816012090040380605100311039020421000508160040520946a5003092080e10420f0307c100c0300185403041c5000840304410309030401c4040044a142400c0100360f0100d405803000c03101d4110f003000ca031075504110b5400011076801014030481050300c1c1c01c00080c0d00c2800b43e0409060700140e0720340d001c500041c482da81c01100650701055030000d82403101110310000f501120781c01e1900004003550f92040c0c014951450180001030403205110f4017034204107141c887d56074154910300c0014085000403c070400c0d400c00810743c41c40710742666038800400115549948c00360b200c00907401d01e00301d00d901080090b80302e14a0000b08000d4031117504844c1000280d035050024a40d652400e203500500603407251a4542c400c0e007446d0f0390805400010442c001d034604a0894620100d000c20060210b0300740c000c566042d4461588100f5121002c5403851001419048032400031400703954221800e21280c10602c0550800001c04c40070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 364170026 1250 364168776 364168823
    0x10b0d0501150504180e0d080412170106050a0309050d090302010909021201030b0414030409090605070c0b130812010303110d030203010501080613021b030c120405300a 74
    0x5400c2070740980e80150b0042c5000f801d9031055114000e001d01c20300c01d0291000006038802c18004030104240e48000a0328140180740090459003100c07003035035401c282c2c1c24645c425603441c01039030004407050900343d0030908241d40307541055030880101512521082e00061041c003c801484240b80c85c0c40d800c0f241144000350803440d880d00201c0f8814030511044107021213814050b411690040351038034694807075044c2030382d40103007108082100b84400034000401c050709a00090026004000400040c0c071a540300b124200c1e0140c20213441c00c02c5180100e0544200c2100c140c1841d8450324946103000b414048003d0f105409074802c0c1c0216081e001042c1d07000d241408000c004c00f203d031600710701e0366040c10006003d24502400090045003a006655100b18555040b146040b01a0825042020344001c48a649500c000000e0815000b82e08200c1e011401d08001d4405948000301240104d441c50701c2d072821108207841503030004045020a0601000081c01300300710842c02880360a8860b4900d0042c40403 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 364171276 1250 364170026 364170029
    0xc0706060f080f1c0e0a09020c030a031a0d1202010609050f0a1103010f12020d08160519020d020d02030a080c0f06060a060f0c080919030c09050c0d0507090905010b0d0501 75
    0x1460304040e00c00f030450054080d4642e0084d00600380780403010f00180101c0d50007445a000400900c1c17000a00c16407a640000c040d01d10250590b405101152500c41516844c00341400820b802000c0d0f921490002030300c80808940c4078a1600c000924590707507906607403e6440666251506a0b0f207030f41480118551800b4007050b51007520032035440c5500d841c03444800e0560600c40c1041400c801e40d000000c551b0ba0501c904a082d40102c0001e49414054401081e03811032400c0480e56071013000841404140c009609a10880c1c006004408483c49d94003800b400c880202c1e422649401a278180034000750a83c1c0c09030080c5d0001c13400410041c400d02480515085c4003802c1030348588008501000050750059050b403c036440c510300b48500300780514013030544e8012030079401e9118010311580d00745000c0303d1090344201d03402481000b02c85544c480004080f200c00340e0780c4841c600001c008205010380303070790801604400d6614107222802d50310b103001c40031aa42038000a14040c40081d91400100540c0149070 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 364172526 1250 364171276 364171303
    0x10c0213182001080417040312080601020c01030b030a03210e10060e06210c062b02070b16020a0203010c200d05190c02030f0705031011120c0706060f08 67
    0x102c1c5208900000303000040c0003803000b0880355000700620303030003010710041c1c03002582e101124034000d07449075201a0103020211070160052194034904581503100b030260807021036029015100e04815903c0031204030300c0c0782030720140f038450110360800d1000b50351007222610231400c006002240581c80402c000c2d18400c2d40a162200e41c07400522280780d9a12140e10440011031040c142c00951340c1020710308010304208503d900c580c002c01c02040341c0b8403401e8135071045900f80104214503240104904204e0003161409448a00054009440d407044a080460001c6d002c1c01150503103401540001e00752403c07016108000b481010755160802882040f1403e800e400b14081c01f20f03030b4100b05c4014154069828240c6603001c8005108411302e0090070052017090b0060141d900c024039213a8420760f03420b582e12078503029110b03401007562002e08510551101c0380207421524a419101e20000c0090034002d44039250307445e802c01074800020514458580103107160115000c0c1c003882d00c001c1c5401c00000b483c0c0da4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 364173776 1250 364172526 364172573
    0x11b020d090b0c07060f0c0b010b0c1219050a050c07030804090b06071205181201020a080603030f041404021b01050f01080a1119030f14060a06080c010c021318 70
    0x201e00106012801c1c405a92841c94000081601802c0c21120038850031005400040810700114881d210ac10040501035244000c450760610007400d40c8610b4803a8005041c0da1400141c246070501d4480d034018608600c181c5455420200d5080070b00341011510303442103444000024081003516224091100c1240040350b8072030a00c0d40070b850b28001601101070036810411b00103013a0030613248a08249110034006408060308007443c42d400c038000d40c851070780400412241000920346240000c126201e1a0003000014101890400401d07506801c283c02e8076400790302405041c1c0d0080c4002015249000500c0c0046000d00306000880e00f00d000607009501a43c10640380d960224003126508200e40d9000d481c00c460010380c05c2c100d00d6408450342c000a29110a0741001070600005a0080581e5401401950420344400601804813902c500c00d40007541c00141001030301c0c0d0301807032007444594006800c40b2841041e0403101c0c2c0407104020007c1d940303611030030080c00c01c1c400c030131000f81950240607640 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 364175026 1250 364173776 364173787
    0x30e01030e03090d06110f0c16030f0b0c0f0309031201060311070f080702060c100c0503190c020c03100e010609090f17070f0c031b0608070f02011b020d090b 69
    0xc80b6103e115a208032402002d40d40700da041002002e40c003c41444441038142600c2e00c6460f5180482c1b58022042c80250744030744480000ea0711210049070080307a034880940344008145950b040c99500d8018140f9030410428003030b80c040c0358014002140300e484014080c0d65a55401c040e002005078040c0c0002d0b04051400880e4500c1000d06804c403000983c2080480030a845286040360646c89481d50094000b0404601d44004100004148803078100f080018000883d540301d0441c1d06020071202c12002d071600540307500c8040c0b06d0758003880b0400a81d1059889a211800101c0d15216003180c001c4121942c5503000740c1e00001c01e02c02e641c05800801403d02c00000140c91300000701c1e0040720040c0400c15031901600301b0130303041003c440001d40e024003a11b01410090400182941d07682c80706550117100306070b90801c02c0e10901e000c9402c0e0340d643c3c0c95012598030345d00021a890b002d108103e50540d13580740100712030b0304030071003403500c60014581c0149021540004010030b5501c07198420f0101c003a0074000e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 364176276 1250 364175026 364175051
    0x1020d08010e010513020405040204060504170c0d0605130f030203131a070212032b06060c020d060c05070507170d0507030219022e02011b0207050d020103140a09030e0103 75
    0x1812411244201c1da17074004d0190948400c4001d10503640210341c403d100040004030203400401404c01c8901401d1000440503002850700d440b9030701c182d5800d900000e2200104000f4006501c219000250b201450040c03060550b00d41c480c2141c110021f4025900218084450011940305600542030b42201c80c8035040e10b0b01c804e00414000c140c0b001b8410603500c01c121040c00010010307241da48001803071498141c0b2040005448600c2d51502082601e4100030010502c0da01507003102c0b01c580c3d40600400480c481036241d410042100003130a01c00c11204012020200d482080310f42d01420081200300210360208180510707041a024004040c410184100c10100b0b40200b001a0b200322104030048054003e0b20000c1d600350b0825080d40c003050310b015102048000742081a0b0500c40f104e4000704048140b00384d05e80100180154820010b9002190138041800c000030030f0402684107042c01701d07610410f0480300d8a207100465404007002d07650b00106060503480720055082100a00341001002800d03031 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 364177526 1250 364176276 364176299
    0xc02070e04081611010306120305030a0f0f0908090a080d1d040609020a0806031e1228020d0909090309090c021c020109020f060c0606090405191101020d0801 69
    0x1140518440c03450380040e082c03000c604101c0308000d88190440319407801501d008100031042d60b840c00d00003841c2400214200ea80d50744030a05450b007684a103801e50707503111084c07005408103d840005c07050315907600c5014405980140000103228420303031900e4200040034020032003c5c544c0b040b1070643c00759500010345a084821076003100c0401044101401c0981c01003000b52449511001955100180040c40c4591000545000d810700b1410fa030700d0b41559200e0001128000051028103411030807194101e01c1800c40200341800b0400301104400301481106504400014001c50240c0c224880d00361080d82e108410030094045200d041003452070580340203041404900070101c844e60784584182d0014000c0001038915115025004c0c410042d054000f8060503a180d0304a00a04640c0c0f11107c43d0b01e008010341c1c09840f501402003650f582c1d14410130100510140045e02c050156400384104c4260491262551502410320203111901c1d45000902d4070405000b8241088500d400501400c00e011 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 364178776 1250 364177526 364177529
    0x91802031c1710120b040303150305101e06081c0201090b0a091407090615090b0a030902012604140f1b0103060e09010e01062304050c09091302040507030c0207 70
    0x8041e40e80543d4070103000300750344070b010782000d01c0081e02c5010100401031840020b61142d403281c0d8090040d007200101a05051001c0e000047c0a9000501d01d03030f00c011095480084920090040d000d1600855040d01d000c44843d40c10095090f041024014022502d2600340e54180310b00b44020450051951175030302030820080c2c28240c0b900d03265070418081c414031044244203030014405a501c4640e0300d0010400a0071688659442c01080d00341a000813401985500d0850b40070842040c5001241c4204030300400030780304105c1c1441050f14000d505903900407405000500f01c8075401c4880c0c1458140782c94141c151952048031a440354003189500c02c0007280d8203200b1504151085c103e540301000507800760046812540d140c2880c03c08020304103a05410a0142d01d8004008102c119180d41025000c00610f04120b03045022180308400c4c0d07414241c2c0116485a450070240741403601340d03800202600010f682c002508444440ca0005516140c03140c0c0e0b4009100f81010800c58803188000b030b45420f010b = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 364180026 1250 364178776 364178807
    0x60221030705071b090b01051611030313060201020301030c0b04050f04050a1b08041203060305190515090102030a060f050d0204051306090320070b090f0109091802031c 74
    0xc404520120301442c10b8890850344841d074000204500ca0000030310160714400d01d43c0c6141404090801540280e01f01ca045a0612142c1c0000c10065100c03040e0810200b501140c0500c004c00c0060481c0c11151446005015198005030362545075081140c9801815082013020302e01c1040104020369401598605150782a200880c05135203503076403080100320039551a5800319220f410414550317405800c0754415441240001c0221400d17a10480442e0064000203041e98010400056203124031250004400d20074021220159810700404240c0301c000d6690398450381d00401440549603013809004046c004044407480800e00c0c0c88005004401e032851301074000d580e030b04003182e25460400c880ca03040380e410200c18840d480c91460010601001c07000c8035420242c0f03181e50181d8001010035090100c1d02842c0e0302070300b040c0d000d1040003210300e08100c0b4030f810311680910000b9184039500940b40e00815440b41c40a54009034018903042080c0040e041ca504140d101c485d0b400160070000581c10f240c070 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 364181276 1250 364180026 364180093
    0x2103030906070f02011505010807031409030a2316140a061b140306010c08040f1419060f0819060b0301050f010c05060106030e1e030319050f010306020a02010204090e010f060602 78
    0x4070ac400a03401002c080c0001403503040c0703800070030507001d00c000010050403500c1c9d82d54481d21241a41d074a0b440881e1500920b590301020007892000210340001311000303a02074104040b15140000d0003034a410400d88084440030b13180d0701502030100c400c542041200c8581c1c1403600c020003071030071070380c0c000d00c401030a281c1404021030004081c0041c0805850182411818010107507850384c05240e035529801050622600c4920f00d840d403100b00d0ba1642030200c0f40d00751189141c00340d00c6002607619110051010800d403807400709006008410b07024140090603032011582e6039504150a2001f499540c0064605006400b00ca03140004e10001d0303281d0450381d0341c0c40c000070300340d00c0400320606003032120403182120084158502008940880194064080f540e615001309564160183c00c0e1602111b110501100000040012500c150014001240c4610005103440c3e1030300d40c4101164419001013420341c0d521207251002242c4c41c85100d01800c4140000c1406403104103072001145a00e0320700040080 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 364182526 1250 364181276 364181281
    0xc09031f0f020f090306062205040f1a09191a041b031a01051002030a0e040204050d08030103020a0b030c0301060c0314030703050a0606080601020c2103030906070f020115050108 78
    0x40c0d41e80c05203500c0079464005540d11110584211055044005070b10710074000d51b00883c46500e4401d019001002942110000e002c0011003a900200780c000c0081c0e4116100901100002c0d02003003500e084024480040d803400d0030710b150050f18040c51602d25070b040c1049a1401f0300030031030304015051061488004001181e4603442e000b2213640707282c4510554140c590001000b0800c6405a42c00c2000026103011326a81e030321800c10854000700c403044000350f0400c00903110b0301880703481400880000a040545010740e50404220540c0d072600c2d0a6605507404401842186446020000100307214083d290850400e40c00c150080c2c072040c0306d41c1080c4010b44c4441d03000c01d401090808a21180d02d03105584a2a14280c0500134102c03c50791207511528010021075404d00508003280509010f900802040b10900c00740303c038003500c070300310080c98410445141c0320440f400c0008512070f0100c08090000d904064801038039103100281040c040d1790600e0010340c2090f00480411007110001d10f0701d0380c89038 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 364183776 1250 364182526 364182583
    0x28020f06130209092d0c010302070818190821030103020319290108010b10091701060e070315090501081f1404061a06040f1e0b0c150c0903 61
    0x500b400c40c0f50401001c0f800d03007040c9070301d1145e542c00c00181d0966081e070b83d00070342d42c1004408134401c1030300007001c01c0401c0c40b640702520008d40f12440800d030060a103400410310510110080d00c0e05900a00180c1e000f0000c000e0702c100e80068060359403181981e400c3c25541150300090315140b14258a04030700e0030042d0480240002d02142152541103031555a41d81846114150f03011a42402028030b15800d01cae120700558105a000701802c501030780c2e01c800400e400d002079030507140710344c4400c05040e64a802002c9240c4180e16005405070340d040d10001414044050361680c08132261380250512440d08004208012000c90320700001e403402007040d100040559400001012801000750000703001108210422005600021016604030010b0348602e9402d000c011007880380d806030f03400380c0e03c01d10420008103541058580050b408441c0140080b40c98480348110b40d0400044000c859200c030b05020f100315050880c00760031080c0c0302401450440c1280c00302c0c0c1c3e0354412060b0301c082540b032044001100d = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 364185026 1250 364183776 364183783
    0x20304080405010309023708151513021c060807061209030c050a031206080f10020a030902030d09140105032806180e0c1f03050405010228020f0613020909 68
    0x30303c800e81c040c00800111f405010040c480e80700c125944c8000d20b07a6000c44c2042e000154010600b502c0d221078081a40d03141c000c0c0c0d080c2d000c0d002035280c011000f080b10404080e800d00140102945d056038030f44031042801c00f8201516440d500c03420b0540c0102c0024807030070b0b5008181d0080c28080c4080401c1d02c0c1d650780b4007100c081d0807480c006020743c00341502440405902840368030300382c600c4140c14441540c4403986103440f09110383d0f6030308840d403106280101d01039003038000d40307031084041c14001036600d402e40200e800d05188501070000111440b0040c011f01020041050450b0720a181090562404440d00b03410381501d8112040880b15001100c80301c040036400443c007401d0020000c00349480c2103800718001d0030500c6100c2c886030040000844840c1002603064444541384245028a101c694000343c0c004d001c06802030b50740d95000c002c211000b54040000d041c0848825100381e074082500b600c000d040038210490200141c20001c14401801a4a85020300903501100ca160f200d4803000700781861f = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 364186276 1250 364185026 364185049
    0x8012106050103081e0405210f150403140307091202040b030d050c0f01110a080a2004150f05091909140403140a0915020a0507080d1202030408040501030902 69
    0xc8a0401001104201050002e001c1110704205c28151481110201d44000e0003640109504941840c4401c1600c02242d000c03000245626400e0321036646800340c905e801c143c21940101c004200b0390080c4410103a0041c1b50360701002c52a0b8a0364154200f030303900142194900d210302089450300c1c001050540d69141c0c001ea500d501c00a044401c04c481110000d4071503042030b448603070b1900a0030710500c003024060090101285041e04c0140c076000201c407054130440c01c041e040c088040d40c0e0700210350941c045c952185180e1440c05000544032881d1403490400d42d014036101100f041003a10300e03000c03040d40000039030f09400b00032500341c00d90002001013594041c1e203560113440c0c4141060521801103c6c0000036a01a0303010b0760300c18848242c1c1000e80071103803040c034101100144602504020409070010640b045419900c107486024144d81c03a40343c40c003070300c03034002100c10340104810701d00098200c0c400d183c0b00c0d6001b03002523045103481c1d16203113480e00072841154140b585809060045580c1c000182d42e = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 364187526 1250 364186276 364186283
    0xf030313030b0118050105060d0504031b050a06052203030c05160b01031a1b030a091505010e01141302160807050703020108280e0c030708010509010506060a080121 72
    0x30040d0790303800d14800c40d4000303205603132424040b074030040560340b0a400303040d05841c4058001032414101c0140000100001002a010010b0b01343c0b60149170b0481d1182a0f00d00c500032002403410a4182c00c0110860f580501043c0311400c0c102020602030f007803450741382c01c03898050030001101700c40000103840314490700880200d0007042140c40000c0150800d06981a0307401550180ca40b14a280c9030340405880a60702c0458483e08005070f82d06901c0d800d0001c40e4400030440c00401c440000f95500728090012498048015403503600503c00400380700301c080d00420051100c0b41c03254070b0010100300d1386202180d0b043c9001e5000902c80803041440e03c0e0035608260320680965603101d0609159803281b04030300040340001c4540020904d101d200808260400019004241c10b1000c410030940080010100c03078007031800760307138414280b80d502401580e006003100c10001c111450441c40040c00c40b40014090f900c150f400744007608815030b000000c00e06442000c181d8182992244a18946072140191300a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 364188776 1250 364187526 364187557
    0x619090606020115060203070807110301090f03030506101b0303050a020405060f0a030c0206010b0313030c0203030c0d02061303020a030f0203090a03030507060f0908270301090c030b0c0307020c0f0303 88
    0x3001c03541548141282c0585140d0802090344840e800ca842c1e105550000e82405403e00500c4007054020f036044a01e03003002000000c011286a50703000e000c480c0128250080b82d81c0c1c904002d064104014000c49510f13240c038000c4c081c2803840581d0740011043c048060101350b5603900140b00211036134100c4000d0503004000039220300a42c84148a140c0c04000d454000909205045410034000a0354034141c0c1c0d01d4031012419a0f5a00c4e1510140b110b03009000c0e42005698140e40300541c40c244020411003250070050000005c00080103803818402030484440e915080704d5500110354045400251950b0500e040004503052040480c61350150904175644801d08010000401d50058010090f43d44148001e110368040c100103801140d0b441070700500301d41310410807548607040d0600007541b401081d992022512403547d011030308581280b00102d030354400e1840148140301502d00303141d0b03100396500300c11403641c45c0c0312000035221a1178540c40740c0603500708031882d2115901401a980e9503024084038 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 364190026 1250 364188776 364188779
    0x10603021b121314030a020402070809041a030f06040803070c0201110706050a08090105041a100e0c030a060b0f0a0c0305090301240603020702010804020907030207021c020f0d020906190906 83
    0x2c400d10b5845003005000c081140da02c0064240310000d10080c126000a01610700c8030b10030b80a00001c1c0d88030000841d05100c08201c0d1450544c2d40f8404c020741281510030307002c20a2190f200781071070300300322444240c1c85501010401000075000011a43e1040040c60880e50304c2c0488d100680782004180e61740c0416005001c0f000c5542030344440904a2580281c0d12a0740d01d0b264021410300701c850542c0c000d003495114641450101c00101601504008624500050b582d61444c05080d032083c00d481951900c2c0000051181c41820743c020ba101034141d45000798a444809288c0c01540d103e610039540c10300103c1428201458060410b640c902e60000c2c00030b124041c1e01c5650700032014001d40d83c040d011002c401010464610910070788981d1581a101d14805d916a03030200846103800403c00004c25408124000043c0c0b20b100141c00d4284851480c0c450b541003610410500c0c441169140d8010404161100c0250340d812200c41c0d0800419107030304607140d01d40d105d1340083d41c4041d0400c4200034100b200 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 364191276 1250 364190026 364190053
    0x2406042121050a0914130c120908070203011401050913020f04020a0201022208030714190f050d031503060f09020627060c070519090908030103020f18010603021b 71
    0x30100f021582d919400c0241e140c4120305002021803c1981e0040800c00340c1d9500400160302c940003015413418121413110000d05914140c500b403140446041c072000c030b00c00046060034000d09c13506401158042a59604060108090340700040c19070342548041005103040d500c5603c000c81c015000035000395030320002c50602030b0207940301412189101d000c243c0e100425890000021090318031390300281d89082c0c070945a013400300101950071912802070300c0340410603241000800f24018400e01c0e0490000900303040980c05d00039402040000e060410310b0034a1040007942601060340d81c480000510591110984402403090079402500311000080320038203840f410200d00100a0039800707210300040f854050018502500d00c0d1800720341d2000d0300c180114509a0407414044115014541030507079200c0b0102d090b130310010390035920014000014006e6041512503525511300039030741e0898414412614010170034052090504041d40451a00018868461048402c140000840301641d50000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 364192526 1250 364191276 364191287
    0xa0804030b0609071215150c03090b040503070e07030f14060a12050a02010e010c150c08010503032b020715140f1e0604020d02032406042121 62
    0x103407881105400010002d02d4004034440c800e10240d501e0240400c121034a80c0003500841c1441c00c41284511004100d240003000807800300402966050410b4405090207450b000c56a00400d00c44001004180050340300090300504070740b03800d90382206682d81c0d120210010070301c82e01c8070016036040200d4112000c046154450240e10304442000c40e1aa445190a840c0c0c0300061f80205190007400c260409903000705034540800c007040c1070440d1141c015030340d03400c1ca8074101c00f1001c07001507071b600052020940c40000903000d04403d0300110300d800740d0f081912150103000180d0b00b2400c141151000200a103540541c1e81080d805244003041411900380c41000e840414121090b03450b00000250310003804c14415401102038100d809100a105aa0f8144026004101940041d002c11203c042031149100451041d10700c2c041032940f1034603000b0202200c500e8071405521464040c0406d21018003601094100c2410135200c2c118140c500749800d000340c44864450b205a1694441070095898200 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 364193776 1250 364192526 364192529
    0x230406051b012a0c03090b09040912050c010c05040b1206030309040e01290616050c090a0506240909040f050303010605040303110601030b0a020d0905240a060b0913020c0a0804 77
    0x101400560010740342e0102c4407800c01410150000d056042e0407c9560381d503900808000c0320107040031564100d540c4035080100c40301c050040c005130b80015140300203d42807140242e0311034180703001440c05103400d603500c1c010f000c1e1000c49002c0440b050045010750f07808008a4072034040c05007041c041c4040d0030760818024904401c25034072403142d0200c251228401d10b2905114801b005003000c0c1480b0500350300c1d690b203483c2105c0848103482044000703032690340d0760004280715050310341c07000c03849103031610912030940040c40b050000115610b0403041d0309009041560b203584c40503500304280d5592410410342e11110624042e1041c0000400460300c0350341302c0b0091040da4041c0d11040380c155480020310303603100c0302440050140303641c42000c16668800340d002052640403012010034484117030b40340ca0f410a028150117000308030442000c0c030351200100190320350194103c1400c225071840c2c000c0c496054032170303040d50a00c1349403070001c00060310289038183c800c141203d200712070b0010740314135207400598000e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 364195026 1250 364193776 364193831
    0x702011808060a1a2707030f020304140d0f02063c0f0c0f07020402031305070b09041d070b1c06120213090309030b1b19230406051b01 59
    0x2040d40303d041703003004a6400e00c0141403a541d00d01403003c0104041d07a186018004400301030311000780290781c40c242e0000d18012406060f0103001c6a0880b100c1c3d52500400032450707410721121134511545250045440d541c001c0d40302c403032802e003000c05605444e0715001000c664074444441010401d1542c51010000740b040031091054091a154400c01c1d084134019030031f03000410401003022070014201034014580010b200c002c1c1a0041d41c042e43c5403030902c590b0382c01c00b021802c0d020410034031920b414043c1e0588004002d0f0b18880d40c2c3e02544203c1d44461543c051603514010010318160701c0301c00c1b00000b0b22000542c0d0801c201c1c250310303603075202d140017035941059100f07800005e00c41d070000790303c0d116105c040d648c191901281c55165517151400440e0040c240b01b00c1001d8202813074030b00e100c0f0500070a09484c0010101d020720101c070030003805481d6a8020210804900d603007030100146400225001c0d40c285050140c1c848103a190342882100300458001d12a5080c0700d060305419071261500340700d41c0300 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 364196276 1250 364195026 364195061
    0x303101406030c18010504050631030b1812130608010b040e310302150901290a0504180510050601020a03031a030601030b0a05010605030c0702011808060a 68
    0x2044000c12280d40001e585a0300071890400800a0042c0035a0000f4000701060500b0303400d040d074640015560303400881c43c922101d01e400010b078091104002241d0703c56248200c010490504533122100707442c00040480c0e00752011a00503c082c0b480400c40a04614000f407501a5256500503954000d0111480395074040381d1000000304540300c108054900b139800e0386c04074621503607503010a10300c2c0c1402c1c00041c0b02448001aa40c4ac50f00226610517541540079400a0020319803014180806000017000d45039140d00d0900407240c036101301203041c80315031555071040888048400000300751240940c05203038810301d00200d840d018612034010342e08460007803080ea41c403044860302410940e81d0458610340181c0200191100290095010304261a008106581d040c151640802d1400200b070b00240ca4100040f010440c0854042c010715024001d5480c0550a5040408040707205006045000703042c003200c0501d0383c03112010045040000c0c10f8813021504241004141c0e0001000342051103010402e = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 364197526 1250 364196276 364196309
    0x16060614090609101701020c070f06080c03100509040b0a14010e070f09090204170708030909070813060603031d03010905151e040302010f0b030a170c01020c030310 72
    0x3250014038a0200081d01d4045603907204002c202244100420802c0b941c9241c0d440414110a140c290708403954054000584d80c484031800a0b103070000c03550182c4588840c81e10705002580e48448100e421920541d0101c1e16520b4640c0803c04806407500035030b400c0003040c01080b05111002014500405d05803108110916110601c1007108909001d15a1220886070104031054419640081c4001440ca41102140c1e01c660304d05080c0c1e40b0a501c040780c0d80d0241e0882c080c03039501c103204c0803009141c40c0b002580303403d085a0125840600003004c030020f104040740011980d100f9822200e405540c09442006081e45901d0042c140c100551280800b80c4204c1002d6041402c0c140300f00c188154104c8010900c0140122070720b00b400e00000c101544800c210203c01c0b101d031041c0090517010314807a800100d001c00c1401868000c4414112685200c0d51103148850041003118054064920100484503981e0600c0c0708070b03e0184c407d4003503948040c03200104020308280c00c1000d100c240e84102320343e1203002 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 364198776 1250 364197526 364197539
    0x31202010f0c1107140315010e15010c051902040b120d03110c0a060504020402090a060c02041a010503070e190603060f081203070e01090e01060305090606061602010320160606 77
    0xc0f0707207521000c0039607108080038000b20420708445070242100a044034041d1141c00d546800d00702c4282c2c006801d40202d41c4c18400424400840b00360310110a18001c00302c0d03500c64946641d2120550348800e03c414410038001e042d51a60341040340d4a00d0098030207140700b01186902652810150b086c440020726040f001c0c0914450b0f4400c40380c800d001302000341499846511582c008080c09801260b00603400c02c0400f00701d480311440f0000510b107546074a47c50586e240180303c192070780031400700d0b41039105c400310301c00716a00321080e030b07403c032215117060f035684020413010a030151901460004a03102c14030b000511282d16030040c0d400d84865100e50880c581d61110300543c2c07a00d41d0310415415031018000250b03a07034070810000003191340500d007480c6200c0e542d42d012001d4000a80003040086d807500f0070400110020003940c0e400c80010b40301d8900d40318446018a60b4580071203030007410180c131800403002c103091003507821608285c007020300769860042074644803112100781c4045610ba4100800002c1c1d9 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 364200026 1250 364198776 364198787
    0x212061905030c01050f090a0620010204120f1b0b040f0f0b0403080c030f0301060804050c01110d18090c0906180302060301090209060c0604030201150f08030d050907031202010f0c 79
    0x201c0700080d00a10100741180c006490a030401801c03a44500700c10302480005507113800301080185000d0325a80900c26480d28034200d562180d440c0d840b016801080100094100250b0181c030a50700441400d489401034541103401940d009103130740140d010190081410703000a0010000c41303008281c1694072660752581c0150302c1e8024845e41c0030400c828032040010606980051041e40c10402c1524a000825500444103400030f0f00b16000007a00c04080004209041100e08212402400d243d1b140c040714403941c5586121812150381013101001c03403075016641020100014102e00c1c9014426000c42c4800104101558401e40740064416800c0380c3c2c0981044403080d080e02d401400d5207113180e0900740b01a01941c04414a0303500003004000d001c000c80010f00c0203d0089100354000302e09524407a6881410203805e8010f059940007c110410501c080081150304070100c6800c0403899076a461042801c00320380da031010300503440320b0710180078076a4194011035495a0340e00c401c201c01045804110351 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 364201276 1250 364200026 364200029
    0x20c040608100504021c05010902040e0c100f1101060806060109152309040203130c171c1106010602011b03061508041b0905060a141804020a030602120619 68
    0xc0303034005090b00301a0540603000356502c180040c0204002c415a8201114850907020080d1460303550703908900114034060003191480080100103103820380d505000154072240749811703602440240c10505c49110b0241088503912440c603c000c004559440e0703074180c0c0358135040b07668500140411788046007911602030b0282030310741c00b99101100e03551407a10300c174012000f9400ea01c000300e2090100000b00c0da40c0b03000079881650000d0718803401000740d00d00201108a43d41120300542d1160392403280491002480a800c47c001c00c26000d4039807078820050b81c050400b48590706403402110300124101d07070150421407850301c5100a040031101d03540c4003141100c40c03a00030340128001a55030350461034030034160190010f02a22151006c07504134403410300c2803008da5100c22503039a00c03101001260700d850003103030300103155003002e200704c6103410000540c2d24120b404040581c1c8a00c6800b14013952101e860b404044c541c8000115685e05900340009007041e002c0764101d100d8600961000b45c84882421501c0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 364202526 1250 364201276 364201289
    0xc0105030708010b090409151506050315190306060608090601140a0b031801060602010c0305060906010e0d0528140c01050a031d03040b03040224040905060f0901080607020c0406 78
    0x82030b0341d08002004481e0f0b07200000d032036442600c5014400100d10b0081050190076605940020b02c00061a200d11055030560700090501c0010f104201040008656020604c0c500700c07680c0020080f541070342c0022000d503801c054108c51070300301301080c80da401c101c3d018000d50400e41140c0030b6030380e00c65501030181c0004074030725004004858100100e90451010396007040900c1c148000010310106507500b150465840000181e440f007000004440e0140300e001d401c11000d6406107428a0550006881d00b289010010b00548d0048001e4040c008103108820031000e035182d8502c62a0590380740040e84220b404400e03600002c0300920003026110016100484eaa0180c40305400c218410600b46c0c001c0c940086140c40025516205851403101403000304054115950f1490b1a420303c1c0c010310165016191000081240c1540c094140390010816542110740e07010b000b107683d80c1c461000c117603070901002205d43c0000c600c400114000e1004500d661003191682e08550b0440c0b1000f00b0041034904d10320510 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 364203776 1250 364202526 364202537
    0x12020301080a0f02060702041e1103060307060f020a0b01030f110f0f010302090d02060301031a0106090609030204020d11030f0117120403121407030519030603021003050612010905030403050c01050307 88
    0x280026a410f4104100c0341c00141001d042c02c001c0c0c1c01040640d030101c54101200c403001e1500038154941880b405c0100b010440c034003030451900501183c1da03003089001d07600501040c042e60001c02e43c403c0080341081580620030004550352864600040015400115405441e9407000c001070304050140c1141000d0003010382c229a40e0510040d0000e510100d103030b5821201040d400409a2500c800460080d481580f80c101c0805122183c5100c424040e002041080070505e410040030b58080800000d803a01106e0042c1d41d20b0090303000000500348040d96000480d00030040204104840814504903203491041c6010108001ca18580b0380c6112400f0f500283e0b014001480810314551820400080c41d08111030703540707400c00070b00240e0f822850046000540c0003441c18035103c0c1c92580b500702d10b174442c1001d1103014215800580725405030000b9000301542c800020320740741e0301c0304c103d0544030310a00c00130010440142002a160b038403500060713030148103e0185446a500c19021684610034580d1a03 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 364205026 1250 364203776 364203793
    0x71a030a0c050307271d060f01030605061b070e04080c0d02030a05040315090605090303100e040f060213231504030c03030804030c080a090602100606021209040603060501090203071202030108 84
    0x4031452000031030302143c5808030172000706500d06040500c403020354171102c40503a1351601c0d0080040a41070844406e04160812008100d01d03241c1c4d00546030707200740b04117107c5501a48800340e645808510340c042040142c0010900c014480010005c00840c2c45881c141c1c2c060194440090783c3c0c9105000b0613000290742084108041124814040400180c240c4085088880794588009a40042d56444115000003051160000103a60410000d055441c140311161500d41c8648414a1044c4000780095400007544c14110091114044c0a403940e03002424407289c1d1101e03c59110710740d4520182c0110110500c800720004103105940c100c0c0d5100c02400d0755141165400c0343c0288024208509215180e0380390000240001c0140c40ea241090350741c4e075032261504000901e0400407884070740c1c0446c034240042c00055070101d0b4404074501d041d44450754a40385038000c10000c0c01150b0025001c10310380000881c16000c180c00640c0500f03000d0717684070404600c081c401e074101d201c207100e08403803644090034 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 364206276 1250 364205026 364205057
    0xc1209130b0f061b0a082802030307030b19170708011811060d1107020a0501112a06040306050601030e0d020c01081902030a06030302060a0b21071a030a0c050307 71
    0x100a08441c660440c40c4c03102c41d00d03040c01d2420303101000445d1140b0002c80c511116580d000740c89090380480e0141054810103404001c0c3d1640700103066002015200c0144402944641200d08000610034055420041e91402681e488603007003829060309004980c00014402e005008582d40c0f40600d0131110189000c0f581c4220418100180b510303003010060060348080400b6204503a0710f5198080403681e036810038810072100044d0742d00118140482c00c80080c4014200249205460260030300e501a0092018240d11204414140042e4400300c0058003008014842c0c00090003400c2c00c0c1c805108851850112603240c8000200d50401a48501084a00d540c481c09101e0340089640421250400ca41001002070303074011643c040a4035249c41b02001095410407141c0c0e800420754008006100302580025100c3c00c0011580d900340205510500c0010b0f0140040c0b80208844c10300040b5400450400304d80350b0b002295400707509840e02c404c18141c0e03401141184d1288506540302094405d0000 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 364207526 1250 364206276 364206289
    0xf0c0a0f0302060f0a0e030d030e0c09040305120709080307032a0201120c0e040614010e04180f05010f090b040b06010801030b01091d0d0917030702012001020c1209130b0f 75
    0xd80390b03810048030006c0007050361400d0101503866422513601240c0c2441c0c00300403510781a2824000c80c00380040904005c0425031110030348403032000d0030100014940b0751020482d0711140c19001030b4140e000c001500300425400c6269160a170501048480e61501030803078080300c030b244110003c1d010940002030380f02600019440709005810314140700c2c0d8842c0000000c10202c641c0741d0080e00080c0d54100700400c542d030308040d0300552418201c50500400103040c2c50081c0000b031709100204050f10103809401042029004100c07420140507040101c0b135942c0c00c000b070748103d0131342e020b40b4281c4064002c2011540b003a440281669003041030b424180e4038204100008243c0d510301802041401c810742c0045440a00020458081c2640d880b80e0a5041504016000c9030b00c280800c2e42703038820020800142d030480c0c500c080c00c246900c1540d4040d45804025030191140492246044c010702072420614440400a480000700956002d00d4000d120041c0d481281c0d90091325640c00f080254800340c0e60b01d890f0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 364208633 1107 364207526 364207537
    0x9080a391103300d050408041a1602011419050a0212070b0105040b0612010603060e07110a15150e010311010c0b0103030810080f0c0a0f0302060f 64
    0x5441c0200300958046040741c02d20080c00c0300f0180b00852816a07501030001401803003d850140780840e1698460300500100c166032000140400071208182c0c0c4c100d030142a0403e60f841441c0e00199803600000c0344001e050304040020f5108c03951800080d01c0401c104c0d8658035110101350030b0207410031000320751303035001c00070280010004681d0300d5045904540081c4c50004e6445499400300d4070303d00c01c01d43c2418114181c0400020303043d6141e070082003101c41c2c0c0030885401d5190030100300c0d0507903407244409407554024034520000c50389800503e003210140c10400030b00d6134440c1d4a64454440507500c052002c1407004010000c0c00946455070306104801d1034540b010322040e94130604660f8040c00050100820480040c0c5540b040c03c1c040d0019002c10350488148030304100e4110f40d0f800044107018042d4220080001b00c0b1032121005005a17540280f405003030410262000c6c0c50341c0c008 = true := by decide +kernel

theorem cover : BRFrame.Cov 364028776 364208633 := by
  have h0 := BRFrame.cov_init 364028776
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 364028776 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 364028776 ≤ n) (h2 : n < 364208633) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
