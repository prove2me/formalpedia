-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4087
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T11:32:20.558042+00:00
-- url     : https://prove2.me/submissions/c1dca363-4cb3-4e61-be2a-ad88f1835862

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 734892086 ≤ n < 735071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 734893336 1250 734892086 734892121
    0x13002010311070b2409060910080a030806041b020312071e090317042603520305030402040e0114040510090f0605040c1a0c0118022b0605 61
    0x5d040781240c0c9103a00b05450740794100300d04000c0c0c1c80078400300400c3c034030301e0720a5000b5000750b444e6509841841c0c0d41c0d0951850210551b20803000f15a00b00200421071070188200c0c0b04010342214200300519505100944078422003211107554520200031504940c4100c82e11030b1031200d803c418850802040c030002d0513109040c401160b4200c0c8003c0c2121001030344000f540d0899444a0b1030b10303480489804400302c075460f880b448403064841800070400525655522600e4060080e071032000100321181c000e0640c1c4c84e900d0b41940da0b40351300c0c000c60030240c4410300303c5000103404d4038003140c403038883d440000c02401b40c10518524542c20320000c1d01401c208045540e005078030401c1103910400070380e2420025210440009012004405d0b00c602c0803a08680040c3c0e8000d11541c41c1c84030349621003012943c40510940518040f04011034011900182480307810340c0c510421145c51840e50403540003c450f01d801c9400c0d0000c000191100040031096400c00047d5242c2c004018015403602441d03442801011 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 734894586 1250 734893336 734893351
    0xe0109020301110f040b0d0912170915131511120108120a0e030a3e030c0f0a030b0f06040b1c06051b04080d08013002010311070b 57
    0x3090f007801507500006040300c8620b0400f003d00c1e401c06180658444107500018005480203071101c40d400d0018120312422a2040b109417107130620000c0b800201005c0020040c400300c940d5101c2a50714800006814400d0f0384072406003960502d02d1510718100c0c4109404038032100f400c6041c40c4425200c01c1004010701518180c07050b0301c0782540c0ea1001074503a903030f1302c3c0c07c000384602c1020001440c009100e0040403000c03d001900321070320515240d6030f240c80c010110301210014002090180e40b05604004581382124903807402440f00c6644170002922003001400c2d0a00c00c0e810f28000d034503607803038001e4058002d513004092040c040c50000000c0109141c11590284918900340c04802546800440200c0b080f950701084001c00e030345995260700030b0201805030840741841c42c0e80c0f20303000b80c001d0000384040c10303089e00a0080340558003c00341c03200070103030007817540c50882200171100303200404031040f85401d104a00c1c1d003031314000c3d0006a00030400551100489000001d01c042480b5980d00b0440c0274200 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 734895836 1250 734894586 734894591
    0x90506060f06070c03260a0e0312090f101701090606120501030f03030f110a050c060609010803030a0c030b0406090e1005150607170c0604110904031e0306090e0109020301 75
    0x31200100b004030b12420000900e00c10b0807120034804140d604c0508902d4190740c840001085042d54104901c507000710b40100300042805415111508003401407034001300700304680508002c00b4030001150488401f01d418050700c4094603031103181e4424030880a007030810b88407030141540c4903c6640c0203002e035401500d0108132254012503840081d0321685040300e4200c40150142c0030243d400301c0282110000d009045921034507074074070701d10b1030200a200740394031078460550314218010111b0514800505d0a84540c0c2100010030000401000312a0303c501d040074005002040c00d0403c0d802880000061901329152080205a0750110b600c083d8100e180d05080301c2256441070040401e40d1070840e00b850307450448480c9086241000e10141c8489032080318100d1820710325584000094000100600341684203005000612440307005517130321102c1c107407241c421038a0305450181492001071924a050750515084801c028031a500040183c40b0900c0140500600000e00c58040c05051a05a11a51 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 734897086 1250 734895836 734895859
    0x30f020d0215010905062809180b04030c05031204030f08090d090501051b0312010509070801060e01050702010e09090717011e05060604090908070303060905070e0f1309050606 77
    0x380002a00b458103031912008030304a0382000ba1000260102400240e04203100c0f00010003036a49800780b9802011075205560480c43c6003604940a45460703c0700c0c503401d4240c000c5010007094500080c10381c89034140c00c0c203000708111490600e10398803c1413186440744800d10244420180d00070b0440794140045d949100d20b6850b5800810784484c02c0720403120210340c032104100100d5000e0405001440100000d500410120900440c110342c08400001c1004680d100180981d00d4140c0301c0360f401503403500c3c2c110460b41c149075002e41551002d503801414010003159170000c580c400c240390705450902901c8003030641041145e06981c0c2900303000d8018000c000410134100b00c4070510403060f5917480358499040765600c04901400501c0e000d03090365008941000003207589887ca004040f40c0c41c0c071440c101c665540326030030700034100c940300e4112190450400741400b444560002000114500843d800c0607600403203000100c002ca96200d44500042c02c003003200050102c00306600d4803440b403c0c0c0c0c2d8104401e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 734898336 1250 734897086 734897113
    0xe0f010206060901051c05031303050d020f062701140405072c041406161403010b1b030d240e040b041e020d080306040b060301050f0103050a020f0403030f02 69
    0x107100446074540c101035400b0040005150070705203218a0800381c81c0100d008400e035141c142c03c50341f0500511641000d00102001004010170803203098814902c00f4002400c00c07491501d440d0130700541580030114106452041d01d0301f04001510300c070307070605000b040003112050410030b000c00704803010b031624010048002406210480204840460400740d11a40b095411846500c520301030401e4600700c160142c1c02c0d818880800200340541003048203c2000404d001c8010080e0524a040c042002c20a2004004102c180c0084d146240340740c4680c0a040150101d0091850152240321302c14207003040340c090002c0600c0752510460401d0814140d400395240c4601e034240308030548004164280742d40000380803e00ea0310240940c550800000e00d2035640507000141d01c5043c920f403d5481140c004280026883c0138070130940c800c3d074262003550440d890800000c0c0340c56203c100882c141510b40c00028900426a4101c0320328030400d2075201d0b203c2d0f8503810001c2038112114803540251240c440d43c9044e0 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 734899586 1250 734898336 734898343
    0x1d10060f060c0215070614250807050c1518060c040323010603320601080d2106090204080712080702011d0d26090f061b0a030e0f0102 59
    0x1511040d03240c01e0703845089642032010400e100c46055400000600c040b900141c540d010f4040e4148900000502c04e04040700351452394290010a4107500a80c0ea11025a070350b042040540e0129040c1029902e03551640102410f00341c00d14041210f91034804100b1070303440e1903510900340a5501c0c0048810790b40d50407101489074884c034000038103628642d030a140742c86581e008030710079045100800407030080d0341d0743d9804138000c41040b0310210020134041c0441a030a0440071200020400400a0845502d408044c0751a03289940c0805c0800840c0603000d014100701060701001c0403a00703442000103d40e1a51008000c0d0000d000d809071a0182d07840c0007414600d20064805c5154000d450545050300b598010340b2100100c81c420304500e0b01c619196422507580500103807003140202700035200c60307042c0646503160038541000440940030074001c201d803d850341841c3c42c8600c1401d41d600380d41d800d000400840c940c1c840304252802803042c0201102019130045000e070101d00141d801d03121180850b001a45c4 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 734900836 1250 734899586 734899589
    0x50d030f060512070b090a09090602070b07020d090b0d0e031b010c1d040c1b0f030f0c0302150703021306020102070204060f050f090a110a02010e0c060a090e0603011d10060f 76
    0x180b0303405007005200560f1744c08001c00000100900b04a000caa03200c1c017002c10354500f1001070321010b601007184d40c18080340b082029807041092001d40030b5a90940006040725006000d40c811400010690001c6580158042600505038a0440791600404401e107581d48a42003c944601d50a145005140b680681c4101404900d00d211600040114200380002401c00301c0161003009520841802b1000b8480d02c1a81700da402101081541c030620b050140204045440742010428541201e00c00300e50b000c14a44c9120a280325051341c252035020342240a0b020b010103030070004482250005c0d882da0158010081e0034802d45040c482710399508051240c200c03c600c2519081502003a4442c402d103415040280e00c00c1c5520000601c02c030400c0e002e01e0064001e001c2440c0940c1d074514000340203440030400010720000441d5070f10301d82403030418001e00c026008e100c4c0c0c00c03000c4c454001082150340d01b9001222840c40d41048071145030000350041d40c1d03400f42c40340c406034402d10301100424440450108e00e070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 734902086 1250 734900836 734900869
    0x8010503030711031903050309072319051c03120209060d05101e06090905071704050c061201060f1119080f0a0c051903020622050d030f0605 62
    0x40c02c18a5680765600c610b507420070069454050228181640c541e401c158444090007a034030f1540b240381000c0c03ea480c00d070980e00701c404010300356035101e8480d0600b541040c080f2041512649800044d0491118451400d904044d40c44240700f801020018202403100700f03410302036516400d8000c181c5070000d00300d105450b02c1d5a0491800c01c10b8681c10000ba4009540041d0600f448400803591691140350380c4002224110000c0e2030010304029096000300d40b2000741c0180d010802a5040410300545061007015040703e40111800c002002d000c01801b03400401f600160007682e44041c1c4810351400c0100900503d004038414981c0b02c00e00341c2c03040b52802d02d0034400c2c5d0b009041c1d0041d020a140101d85415108a920040c01c010f5044401078000241900849644070300d40c420b0854500642824141c2840c4030713408508003e11b402280c0d0000740c080d0449401041004504070507500040c1daa901e54802170880e210319400c1104a5038035a101070008450078204000258a4104001007030b800b520012 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 734903336 1250 734902086 734902093
    0xa181b020105061c0f0f1e030f0329040902010507140105182d0106050a08060a0b010507260f13140a060504150302040e0f04112707090909140d08010503 67
    0x10070000b8402c10003e00158040d41f400140c650b45668500500c1c14100340450002e00d00c0100741c5801d0350103004104050000c00b0640e108603111071020940c07d40380300055403055803680451025a4003400c22a0451038020050103d5060400211400b809040d1500c0d01c2540c1803616000c1202001f24049200f25060811001580c11598100714100181d43c2c401803255621100045c80b503980217101c03001049000080d24042ca841007a41c0c0444581d00d070118180001041048001401c81d01d0300d800350b226201044100303003984c2032081198064450b02005003a000681426102c16a00b0904100c420280c00ea006110110b0240039800c5014071500000c030300248424801c6070f040d400140c4109074245001070920355549140c605022051320038400c88400f40c0d082c0014015510200c00004c0d01c1a104d00741c4480c29458040d00d203545002824880044000c0401d42e01440f904548000b0422510b042c8402034241c20000540512800c9810070361040c010b481c090710b4003524150f4103c9100a025 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 734904586 1250 734903336 734903363
    0x12151a0d03031b030906060e0105031905070f24050906120903130314070b12070e0d15060e06040506030a080d06091b0e0f0a181b020105061c 62
    0x103105408050540c11070030706841c2c2d01e903225520540c1811003084a01a6000300310302440e42450310494015800c44003c1d0b42c100c900510072500c00041c0444241210390f003803d00007440b81802403d01b46c081e080000f56444001001500c0e44081e0440346540d4541c0d46500302d240d58658050740c1c1d46c1324401d003c0790400014022496483c400340c000540c0600c4100a991505280d980a28410300041d002291151a4400d104400c00020032107100a440c030070122901d0081825009010000024880c904102030034030680d02d152140f04003001500d40c000003020400303100b89160405802036000d40300401912100242140c5418054903018032000fa015001d0550207840300c54150348180b44207801c45486200020740110903200e01c0340c02e45121202c540d81601d059000030100c07100407011034455801c0b102184c62685c1d4100295040702c160301d4560710034144406078400505000c1c031a1489207031140401454603901900418840d03003044883c0110301089000c0c5601010307103200040d0014a030302e400c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 734905836 1250 734904586 734904589
    0x60f0506150a03110a0906090b0a05030c030603101e0c03021c02070311070816120b01170111070c06090b12070c111f180503250e0112151a 61
    0x50280a03083e00d0701041442071048256a1030340188208000207010b0034040140c65032002003d80500005098146000c40041c0011f0590201406032003a600e0b0000100e0f100d940c0c01c1185040e4040d1101040c80f041000c81031112401c2c3c1580000b1007030904020b46c0c440c2c098464030031501c03484540c11004c440641e40c0c510000c02034024100032014402c4000c0a20800380c01040800e0050145a0040400340c2e000e441481004060703521007070719421031991900025211072203c605485050704103504140c40b46a14601500b18074007003002c0d1110000e13080041c4446100c41c0e40c1a141282c80f8045c0702c0381d841041040c144200614580c00180781004202110300c13070318412450034003d000c1080041c08600004032803441d06154400003190501e00c21001c26004444c602c07640b480c217a0005209407603c004030303450703208041e80744080d0500c1a540c01c08082c41c4100076000f41607040947c1d41e0560716040b603080c41082021083d07841c003001d96040b550407111070248414840320015119240a880c00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 734907086 1250 734905836 734905879
    0x30f11070c03060509120d062108160215040303020303060f01050f1207050d0612050114152206080f0c100c03031d24011203021518060403030207060f0506 68
    0x2801c0d608035001d0700c6c15011041205e54040c1403000801580044c03050b1400080116182075110040c2c001ca40c008074a10200710860281c03141180001e4002201229910020701c84c11b402564100c9111800305d4040185580040618400c80c8182c0d40aa02810b06200664181c01103464215002c1410807640c086580711088164016413a428218149400c6031200c0713040e290542c00084800d206c6030030303800c1840801d010340e96014030043c0868180c9d06060100d0440b0023480c0b00600c1c001c00c5518141c1840050b03a4201d45900600a003041101e0345d00c03071014540310301c58140d00900500c601c00200c010345c9013074010040540240e0b01d4842e0380b10915901940545070b02d0807215028003060961003080a0140a01c2c04240070410700810b11040c56242c1e0b07038009170182c20400c035484080c0c940d000025000161104030041e40380c0c2c200316503503988000a18011000800010320b000c2e603024441050b4141c1c000e0b0051a110b000144a5201480c00716821580d0031900b0a903c0004915100310303012082 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 734908336 1250 734907086 734907091
    0x1a030c0a03270302010f06080c0d081614060108030316030e0a0611270d140304081902041a0906040c0e040513020906010807020a06021315030f11070c030605 69
    0xa05011038424058014000b000e4448a04a000c503611407010800301030f07081c4600b0368038800c40c403401c004850801030015504e402e16654a40a141707030204181c00d201e80d0000792225503045000b6074850035000c1c503261000f42c0c0d12101296107403182c2800418045000300c180c0744194078198151202c3d0000c12001c0307000c0c0051031031a04603400f91b24510341c003045060207000080c42401d050317a60303110101810041c0404c185803c0c458103049501c03001904e0b0759016030440c652908201c82c1c03440380040c040990f00f50300c10390b8069221803060841c42c10610a001401d501194000c03501000702d01014042d20840d44039030721a555002c200100000d995141c41d0f4000819000c0a01e400300b4002040c02c04181195800d4460280c1500c00030100c2045140c282c0e02c4540c0300600381b07400040c504000c0d01c040c0d0396214800009202c0354012404a42021184900c84018184040d8161008603903c001400034040d070b842c4203050720f04180594082c1240e000489007456030004581441301e2a6484080062130003 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 734909586 1250 734908336 734908357
    0x9010e010c1a01051e0f060f2101081902090f10150c062301030f1505010306050403120b0f1318291308071a1303091a030c 54
    0x148260351000c1000c0c0810004008400b00300c01485504100c200f012a2206400100500401d00c00d40b41701502c5242d229000d41c5802e6460680b00d040140e040d0142e802552904c081038444040521000c0b04e512640382d040f249407000755400d014130548051854603000b40041d4101207520301250b074071440369014a51081c0700c1886110307aa600c4980014100c490224080005002ea14482d01808214800c844c7e01c1444494150040400e4203034a40100d101488003801d4042511440c4080c0050920421814444040c00300b041e913031280360840007001c0c16941540004c0000003030f418480a1842143c0044134010003504c0b25140c00410443d800c2d2031182d0410060f9190b070406c01d180ea020741038095046100300c02125140c005825002e8221003c820803000314108441484440d103607555800558a030407510903136485001d401c00a00141c1d481071107205503d042800c01800e110355010811143d44642e071b80e5000d036556440c2c0f0000c1c00007403240744500b04500308089141e403181d100c01012507800 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 734910836 1250 734909586 734909597
    0x10f0212030702010c09241b0b07030203220c1a04030c17060c040605040314190b1509090316020307030c090501090b0118030b07021002070501062909010e01 69
    0x81005030444542040d02d419001d0303911003e460f81044d41220000000e0807080310105000c00030f5414900c20006555580000d01c9261040380242d191001c00101c84550006680f140078104903c3c02402980304549404041d42000e503a031641e10345540528101c0c0c0e800600c2c99104a0401c181540005a1869000c001001c100400030000d01c02041035002001003800040705104100c50490030300310000c1c0160441c0c4002c004c20b01c01c0316000402d403402c5d281c014050514040c04e061445151240b08640e507004051400b510004101600b0b11a511a842c151088981a800715090012035402034402014a0300306200c801015841c56103600000b900081c11140d156076281ca4404428035113802a0440c0c5444d10014071484441f4011181d428100303181c00c1c0c124503680f000c80448032440d03000080141a5070404158440e1003040b09c031840c050342580465035000d1a10b41107009190034403801540032488242041d5142036900560108a5012640c80c40d007400078004403010302c2d44100c40b506104 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 734912086 1250 734910836 734910853
    0x1030b0f0d050102030403030b030604030f1b140d02100207151505090c0c070f03021012020f0d0b0f0405060108040b0705040312020105060f030f03040b03100503150f060f0609010f02 80
    0x41d2554001070501d4000e0000595038100382c1401003c0e01e00021080d40242d100b0b03410b0000296002582030041c1100380b503c41c84d4402c0d59134009030140d40e10280680b808000b1800071106200110704551620105d40031202d0342d541506100060307000c3c1490103846144010158001301c10341c3d80141000520742010308034016120070008148a4054841c407803410310100340514401e40802804000d02070a2a80b070451500c2d5038001680d00c50007904c4c90081041560368000c40c40c0361901034800c0049686442500d4210042c0030000401a0302c0c00244110003044030000541414480d0030b0007048103035104021961282c0300d402100300050207007020040d04000010100d012240d5016103035006a0000c941424000c08000499001e0060544a5007122a51800400002040310200c03000b03011036589070340e25100c19003581704c455849550180030341e01d105030407031240800403441071403d20100c8189450301414040802c1c020801183c004004101540c030a40c001c040741e0454007114411035070040d = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 734913336 1250 734912086 734912089
    0xd0f06090204031a091b0d0302010e01050705070215040b070f080d0c03060503160602031b0c10110f120409090f02120304150503040503030121060e1e03120601030b0f 73
    0x2e900c10742c020356903071186140700094a0301a0101e036400030181c50052128940c000c080130000202444041d12508072080380c0000c26000390480401220904001c00c51440c1028020300f080e401460f00300c6c0307d041c10009540d410090542580c00f950344503001c00c0c2c01c2103d0703580e68000190b403480084d2103a40c070610403400d561324a4050010140440c1d50041100c40c0351400381450030320682d02890810b01802014000240c0c00010f03521020b11a214291034a080705003614113000d004410550440d000300000080c40d6041241200c054407000d04803503094a140c8021920f03110205c40d224280c200800040281c00c10541084070b020340920950281c1c0f500c1d1350f00164100003902c80301e20041c1c05c041420000c0786ea0220383d03249072441c24203241d80f442c03400e03680d201d449201c14054102850f4101d0600c00e20820324481c03420403281e0100301046540701102000342c0d956003414081c20081070b826030002043d000071007034481e4200030103050b4155071204001500500310050169810504010240b88207 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 734914586 1250 734913336 734913341
    0x52809080d1e0e1f05130905070f0305060a0f1d060d240e010504030906020601120c1502120d09050d17040308070e1905090f010f0b07020411040305060f1006050d0f0609 74
    0x38030f113407600c4c3d5581c1c440000319803040b0061aa40315100701c42c80d0404202403240c02442e40c41c03000c000703850001200d548200010744107a09070703007046180c0005d040c0c01107151480c03108421024030301141050b19a80e240801c00060312030402004140d042e0f07003400c05003c0894001012a030352591180842c00e4005540241d0860344115410f80002e90100d40402005406100460143c650313820308840d600c146440e203110740c0c50303070784a0781010314103040ca8903190314400d0005004051203642c00e5a40c40c01103140c5100a000e0850069805002d15501c665105011b0003015070304404002c1c100c8043d694584007941c0703064005080601f48034809580180e5903481c0401c40d40c400060442c0505a1424202806080c00d002090825404003003001408000c40040d4203400300d420034000c0d00c0d030f18400c501c085400351030181080f00c549240401c000c002c0100100301ca51249400049041f041d55a03100700c601703256900c0c4680d1000c00c6040288150000203500040d580700c140900102d000c540d200c3e8641c08 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 734915836 1250 734914586 734914639
    0x317070f0b1611060c1806070507120b0105041a0f2404030606080f0c100311030f0103020111061005210f030901020d021507052809080d1e0e 62
    0x2c41990307020b50030407180e4001e0202c0c0303e80c0200320001c203040c2c03503d401d50b41040d1068944809134100c2001c020006943c1c1c010440c3c4040c0d600205403441c4e00d0f5030310491081022114400c85084104100100307540c01e00340319985030011204c80302c100c40f203c030b0018441c03540451007ca907003250f0350320003001219041140783c81071041400481d0307645034070f1410300c4402c8540b2500a49090340280040241d00100011002d00c2110111421041600c40351403d0300240a4000d4a1007a098003100304441400100c1035541280c0c000c1c4c86041414560603480e90710f80e0b00881d449150381c52068428885424118802c1c10000c1b544c1121000084c1c80300d89803490910035414295066100040721803c959040c45200300c09a580c1c0020060031040d43c0c1c1e4200324801c0149190100503012960400c1d0740903616403140c40b40c2c000350404841a0240d9030003400c5241d107000701d8080340b06d0b24041c8241c061081d044440f02e15401d4800c15141415032070b08603822400380c80700a0380201c8407240540300000300144000c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 734917086 1250 734915836 734915851
    0xa030309111e03070812040e0c040e0403030b120c0d060b0103060e04080306030c090f0406111c14072c01020a08030108060f01050105120f06130e030d14010317070f0b 73
    0x700c40c80c1c0c002c0d007094681007013a04260100c0d045003401c001a080b03004143c0d01030b90014400902541d403200034251050041d94041c04040c1000011300081c103416611901030f540b010380e488800c0c00f69041e286581c0d41950400550005250060800800d4040d406400d00c5101450003140340ca94034412079243d0001964280ea03041c1000040c0041751804200070030300c210040e12400381783c1c0b5005031011030200340140041e00094031151a0402c1c454660221036120f0310b07104404c0f07020b12481e50494005c01c2c1410043c3d41c9101983c0110384024002c0e02441040d00c0e841500203400001d401c22003506062042c1194150301c10b080c5844005a0a180a50b000c1c050000080c00c05240c102e442d2440800c7c1a4000c605018041040c0d4040a1011482070342c002c1c44101c04402d80e8860788049200d40410207145040b8134540384031490104c0c0084005c100110054100b0f0198028200051820714070a1100030034074100f42c44240c115010a001038650349000f4151800103400c2c5803645044100202e8810 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 734918336 1250 734917086 734917129
    0xc11010513180c0201050c0f0a0c080d021e09280b07050303090c1008010302010806130c020c01021b06030613111b011d211905041701050402030a03030911 68
    0x1d10702e02990702c100303d110555840280090700300061402510b101e10920102c140000050001001d401040210702030f60388080c0450f07a54060041b288000e400043d2045107001a0034440c030443da541c401a6500c0c1c0700010611412240102d251007030184a601e41a140200c50702c00024240c8a0400074040840c041d10246d030340c07481c0402259041c4018401141c3c8540024088413040c3e603031042d8030700d05495080c2403030041f03521000c0000d0000702e030083e0652816410070000d8042c3d981c1c00f1a2071a4944801e03000c0750110ba9441c2084260702d003625000320b0300300c8010310009085107050305001c04000304031080040c28409005020180d54024118888580005c04400c6040c020901c942c0950341404288400014030800b86280c0311079440103a039a03100c50840103000c08107012011100780000308540398801001400001d02150000d100300301d05c419800380e00004000d41070044034800c0768028054001300321156426001481e132813030300743c441c1c803601140d01c091f81d01c450603840c6104488000e00f = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 734919586 1250 734918336 734918369
    0x60806190b07030c12020d0e040c050904090507060e060304020d120c0516030b15090117030906031f05030a0302030a0c1502030f0f010911030609070e1005041a0a0c11010513 76
    0x14210032190205c0401c650040148500e550307407220300c504144030b040318081003150044004444074015015080e42c06803400c4800c00c1003241c000341840403580719441e070710101090407080041c83c0c00304682c0a50408031415007000014402c20003141030003c4c500740700c010032140c0d48825140a04d0302070a0300788903682c4c00062051164291003507901142e0b140030b280c810000400400c103140c6040c0306108482c03040307a210a011040c14002c0e15441300f03010307151030740f240781192400c00f410010301107580da141180d00020542e82004a008840030390944c000703520344003841c0001c072008c0040c20420303034840b04a082c03040c40f0240c050000714055840503007406083e0800002682586c10182e000100d5140350030140f1000070818016a40c0c4924201c1d0440c05540c0e400c00306a515401e940100c941c0b000b039610341601712030b800101a0064910208048080340383c10314200c405403241107031032004074130f01884920008142c0164a08200c1040c035081d420041c0d05403400d0f0200c484c40c0c110300b1409858a81d0f = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 734920836 1250 734919586 734919593
    0x50a0305060a12030c1502130e07030e030301060e060706110a0f020c1008131e0b060a0303090509040507090501090e0f01020703140d0b09010b0307080a06060806190b07030c 76
    0x602900080211100685035183c21501c400700320002e8802000c0c0300d620900d40061103600400510710149008056513191200d07101c0038022089401080544410f550209400350320030710490741b243c83c001c0002d501d186d0811a040c3c510010400105901c168200032a0307001511500030141d15024003242d0079110f00008401410159070102e04c0f1046600046401d49141e44201d180c10301080740703061112154807880d04880c009131424002601042042c441001c0b40d0340718414480781c40d4041c1403828016140c0100700320381c90f111480054001800038a0621103403900501c4590000d03c0b8104a0790b844d0f03a01c840c2c000a4407000d034001050325a4440001c00040700c14400b0340c0c172129688008516000071640c2c080c10502445448102000380800d09250f200d840354040014000700410459056035602440241c0703520031180a4001100303034010a401c400b80f4003900302690f41a07290020a0760300c110501108004070300307050070b5004041c1400100014103074002d051480c040c1d60345c42c0e82e0344401c0c00c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 734922086 1250 734920836 734920841
    0x18030712032c030a0e040908070c05270f220b102c040c0807030f11030a0b0105040c0509042301082806020903010c090f050121020310030b0403050a03 66
    0x10b807002c00c008055020b1482416012003101c0015401c0e04140c2048043c41021400800c85a00001e2403070200203410300901040601d9602241c10880704091200341034540c1800015108078808400110040401c0352107840e40000b40d80b04d0459120403814040c002c10000c01c4801501042d9802e800c0442404100c0c0840c0c09244040c200341c07440c489201500241c41e00c05660048060301894000300040340402a2803103074100203050b100100c1e080d050322070411140b10400000b040b541c142e11585034500e2803c010a4044032a40c0102c00781101740c5c644014007028010310702070b01007004400c00285007030b030785d442c071035817510500c968086130050381d0701c20310020030342c0040e040090254040a210326604841e20300125400c0034141503045101035a14240300603000345106240d06508201414070259846003021003140d1440504c51031940d901c81c0155031030b046081080c02400f62820000d282a24103800441d040440442284200c0365aa12024000c40c0c1c1074808400083c4009a041c800300c2c1e160 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 734923336 1250 734922086 734922131
    0x60103091e030f031103010909031412060109050109050303031306021e070506090106080a0f0f08030c07023c12070605030a06080c0d060e0f0607030b030f030f031803071203 76
    0x5003010030a21744200c04002030b60005125964000751690404020144920f807120b101002c058241c9407103242d070180d0803035841402c0340c106000541c19040059250300c100c0d2180e0031590302402561550320f40408448a101c9035000030b0b1007a9408012030604204050064556110680901511000d19151150403d00702400440c100d0303045c448240f04062010030984261507006e00d185c25500520303c1c080d4002907414030058015100401041020aa05001410703443e04c2101c15846c0c00f003a00d5038041c510500501000d41c0c1140c2c00004406242d03c0c0d200040201c41e00405e60b5201d0141030000314504401c3d50000d00c00284040240030310358505004200c05088000003901100040c0300200d40d203c2da00d084080c08644d04d508100007144c50138440600c070f003440d810075260580f406460140240003507041860081c4122100000195404030540c0c1300b0004c10301c400d503d103845803103260000d54107921026041c1d010401c01c180005103140c50713001a583d001c0d1408a000004480e07001000c4046 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 734924586 1250 734923336 734923367
    0x180b0a02061806060603040f0b01030c031b06140d02090a120b0109020901021024060806030706021606030c050c01021216110a020405090c0310062d0e060103091e03 72
    0xa0011000c1c02c00c1c0102d0711562044040d43d0b05501c0760740b1402c0c01e04141600c40300c0609103182510000c8244078407014a041605d00400c0054917070403401c06216440e121a06c61030000811b09009041064480e07401041030703c00489001d81018200d000107030100400b6800300d2001c0d040d504400b000c002440410074014010100118101051000040c0d207900c1e48032202010075545044810f0f00c0e44550401c0d83c40c5400101211141e6915400c0241c142502540d045110b4820039100103503003480003842c2c0d2040050002c241030900e03c2c06505501500440684c4401e01c02e040c4099020070209201420702181050f1808003d414441a84c2c1c500c0c1300c0340c1d5106030800000e5800008203000000e0b0f01489150306860000d0300c0e03610108000c0c00c00306021142907150261201002c0c00040076080b41043c0c40300c084040d06117840f502c00c2d0000d5600c0c0408890380350740712300304100510b5111818155100b40d06040c08510491590780c2c0041c0c0070428219608100c4241203010189a804074064000d040c0 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 734925836 1250 734924586 734924611
    0x105090708030c060103030e0a080105070c05060c0a1409012d0f03231503010221070e03070b0a050409181101020d0c1103030717041d01060c060c180b0a0206 69
    0x515503d407540304d440502001d42400034030241d038451503c0b2840c0b02d00050140200800003820326103c000d20500910800f61034521030795010030300d10b92101c02200e005039103d80300c810100b0002c806181940c1c211228203414800c41d070000a001b880015017101c100c480003144940d400f681c0040103031200b104a0781500802d07242180712560101002e03180c50980341000307840445903856040d00021135080e1480300d0341550000c24841410124501054860002d94405010a0703480c0003003161003c64420b2665459408881d0800210010500070050185d00d86000707442c16881e041ca840503103003203134034028403089a04504000e11032411070300040080248007a00381d0036100c1c4c80080914015140c00307003507000880003d00c01a58200100d50350a54840e42000070301a4a60252800c0c0d0464403814441400510403000807800840c0b0642c1658826203580540d0f03c0b0341d403544001080c41c40c0da01c42c10f0121401080a503076004600340c40040c411400e610b81d40350018a0024140b240240c10360b0305200 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 734927086 1250 734925836 734925847
    0xb1f080102030424200706180203120f120c0a030e120f0a1107060806090f0103030507150b031c1116060f14030a050f090c0f0405070c14010509070803 66
    0x281810b1001c4841404004c071040310f080d00d106040000d01c203404000d07009400441c540c241e079030000782c00b5100050144101300100544845a04200210386000035410342012400c0f911052190020784203190130191a6820121f256182c69204501550707180032000001c110381e010550306004120b44008110040c05034207402840b80369a134007031648586110400480d500300c901e4030402c1131004c251403040844a071640c0d03407880903203440029110a4042c008207000540c2030404891014100c95240c0d80d61840c001003612040355009544000d08081070321004080880da800700081d080452000ca20ba0368801e02d110406880818030042106036508468021380c0c00404030703140f03403046410504200791003a84070302080300e609070b6024014004503000300078019042081c1e070000380308000c511002e05560311280c030300316a200001d154041d400f41000c0c0b84c15060341020303040030703810214034244440301c000300703a4940c003800d143c2c025141e07071603951102008101d81c0c04011010040142c01c001d141b805 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 734928336 1250 734927086 734927093
    0x50a0204050a0b010f0f0201111603020c10020712020a0312080f0601020a0f1403120907030b0a090f0213020d0c11060115020d0e0616062309030405010c0602070b1f0801020304 77
    0x1700401101805000c10b158144500c0750003034200a40e0603a404c9402136543c03224240102001d124010107074018811035041034044d00780801d0b80190085944c008141031850807018182841c0d2896049800200c2c01c440000044c41c035841c3c0d800074524980328041589082000c004243c01c1c0180749030704641c413440e90b02001c0741381144d04069485c4c01041e412820701d003804440d07145200e640d1542c00710703444002c1006100700c0c003c030b18030f0103a80c0300302c01c1c03040985c03908409801030ba526004058050601d07007c964005240c80d80c1c04584c07038115031201508010303150305840700315524000414042005050003903006039050080601615004007049041d00200341d00035912070310103002505014235410010100c2e5202030a88500b00017802d0b5a0106e014903141660242c06a81038211600d0400c000c141522030f03020a00601c80d4030102c0013141003500c0d02004441e02c005003581601d960382e00300000401300d0074000e00f8a03c02c00d006401c03101220340701616035170450035951044a0320392060041c007001 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 734929586 1250 734928336 734928347
    0x10140a14010b250b0c070b0108031201090e01150605090a050603010e04030f020f0303012301020a0203030a0507030c0b0f1015021b19060e1e09060607030507080304050a0204050a0b01 80
    0x40ca420b100603850500f9195054071050b050741d0b01600680d075900410445005c1d84000f00740891180160070328599075981115079902a031980380208000b01d03001402010050b6000248042c0288008180c2103044140000a0b0b4240c1d005240098000a426451400c0860002008007010341c0e810740703958500200a80d8105010f4002800c11001202000b11180300304650280305400c1801e4940c4c2e56580c081035070381170381c0400c0d1000040c041a80008480c2d8000b00d501560181c01401641c0350004d0800212801d6018003011000e0045442c1c404000c01e00a80700345108036a004002d040c03600b000440203503685210743c0b10074600e0300e99003c0007021aa02269046d0302040d1200c0540380a140c410014032098000c0d4252003100c87c3c40c6000082c0a64400c10000c200c650035640c2040c0b020300070600807112510b80d01e55981003044e0001007207450506000034072181d40a440c00c3e0741401c16a035683c80f041c0c2e0003a01e080c1c4a5620142c070840a5103040c2c410f0f9500002e0b8580d0402038200341d031001030013 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 734930836 1250 734929586 734929597
    0xb030705180705090303190e040c0c21090e0901022119050a0207021201050a0e30071b0f0e010e07080702030c0109051606020102030f011710140a14010b 67
    0x8010f0041071601d40780e1010002e44100c2013a943c01c0131810b911028005000c04843c940c414404c60030002d05142180c012150710390201d030403849844540e00b80300b4482c0001c446500008040200f03905000481028604110f40617840b520009682e80e050600480d00105402c0100940c2034600e00502201000c0056080f032200c810100129041e0780b0344050100078003a800d0b000e5001401c2001841c00108194003040c81440d901d03404100700400300300e005070b440358102900c5c01182c1c400d8024056444843d003844009a01340c2c14080e180c00026516840700c043c0b09854a4035101d44500c0612030b425420f90304201620307044d060200158940b041c9009541d1000d00000305109102010400179842403084400454524009001d050800e140096440310b04c5680500f905070a0100071a87c1403040c001c40b4017a6006480e10111a400c040d8155942c118406001038548036a10003800322400c140100074030a1182c4800301d040e03140c410b81c40f4055402800b215000041114014000808040305642 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 734932086 1250 734930836 734930851
    0x10602151602010212040605041709010c02190b070317090a0804050d1518030809010e0309011d0409060b09090f071e030b040f02190e0f0405031b010b03070518 70
    0x7110000011041c0c0c024400e440c0c0a80301c6440d0141000180032254001d40e008074402c0e10080c2d810140b020010012b40617808140d0b0004150188440162420401004200c011180725104041e07603040c0000c0241e1204c6400c0300400c0c50411624003850035015500d50002e02c1c54017501051840c0d070780f00304c00d622032800343d14459041540d482d02840100003565091a08501d0308004c01240709034201507804030140c00720000303064000000c0119406005040c0c00280070710045050200314001034450040b403e445100c8070358889000e14032655a40500e400a501070703600000e491640400340165000000c0254100340e2010710419540d1000283d04800c4404170031003500006042c5200851600c0654800f48c620302170700c802d100c00d0104082e20040100e1084902080c0c8941c0901c400d8002074040c4501ca40d01c00a5000096103013606032903040e40984900d082c1c0b860b18840200079190100000242100307a95550040956400c042040c80003500c01116464181d0f55408501e40000320300a2410 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 734933336 1250 734932086 734932111
    0x50a030f0f02070b0706021c1a03190b180607080105101107090c090305072312101119031a061c09020d0f0803190207050309040c09090905030c0601060215 68
    0x1403080c0003855064601c901200f120710205a000a0400c901809c05d0340303400000800e511460707006030301c0c0c00500322000781848294403500b60b12507125001104801002201c6c2d4800e01c40d1009210901030000c18818103603a107400000707505080600c00c00e00c05402c500c0d0140418040e103a0303152040043d441044407801800170a07040e40c24503089032003180607800140385100d4940080340011035805030900b0b004002c20031480c411080c004100100401100d0501c154000100405200300c040d003100e10511189001103142c540300d03018080350b041c3c50f000c8020000c1e603207104101e00007800f13441d00202c6000c00ca40c42820260003001d0000440d007517199850606030b5400f0b0b0f8500f19280d040c0ca4408a58000f580c0c0740032003070070f41000d20443e4000c85014114804032540c074000700041d4404d88114540241c001c40c140340c0030301d042c0001041d00300000806d005581074005a042c50030b00507021300c60702c1200950740358008041150b00c0e194041e0031400030354110720740b6413050000104032103134441f0780c800d4072 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 734934586 1250 734933336 734933347
    0x40b01050a080c301b01090612020901090b0c0d03050703052202030c030303070203031006020a03090b070c030c09060603150e2703190e041e020912030304050a030f0f02070b 76
    0x144c030340c803034000f07000300c29004a00180840d2001d0114000e60a075807001483d0b280808101c004507a030750094011680401c400342052403250a480d4041d007007040c418100300c00d030640c440281c1105078021801508899000c40701602c1d1281c0e05010380360300201a810244098184810301070504030300e00c444c440c0440f10807032a480540d901009040300d01e140140c2520364038181008004c5d02c9a004407002d1080c21500d440c0014a1351000403d0100140c0655444981a080054100503030744142419180703420491360200108015000c800300a000e036110010724145001e001030309032200c6400300441c100c00524100480c1d207803d29210390000c030480741c0d42406001054458051643c0480341c02d000d10010400002640042c520756005007155112030b041c000310b00040000350b0304003d00303446e104102c842d6500c804c85440c0d009004590401000d04042d40c02d4100030030f00d1500111410341c0c1079800300205405050b0000d400000f1a90365142020002060304806541d48559100310114110f00040 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 734935836 1250 734934586 734934619
    0xc030a0c140f040c0915020a0b0106080903091f17130605090f0706020601060e03030c0d0f020c271f050618040e06101d1803040b12040b01050a080c 65
    0x40d203000c01c240208100704104c4400b800030b04584060060400c4000b1041200342c1403800086c002c100a40e121101c0e0340c8581c20400d040b00d0500e409000600c0500c41401a20401c1c1d41d44d2404000d20824001c0051904c0c00600c0001d19003202000103100104a130000c2c0154020000240201182c002201227440d842c0c202c10b0307038503001c20240c1c0c0101ca030044682c0030605690101d0424101c503101e0740c42d1840001060100741e00c903c01c0c900c810200f68401c10090460301d0150030b6160000c1c6150054a1000385548081682110307481b05ca0a0719418a442c82010710030a800d0158001d180959020280300c00145250f030742280342c1c01131500c1031101140446882400c1c0701e078250b80c0d100140040c400048094800b603076840f03050302c0b03c08000e14494401324550b030125000c251500040100c0d00043d40f50002d48005070740e0425419842800104070116203484201d0003007104c03800b40d200c000c15500e41801d040b4101c020603085035120310208a01006641c42c0011495050302003141c003a1001e05810a = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 734937086 1250 734935836 734935849
    0x409051002092b020a0b09100f140a03061e05060339030a140615070f060e07060201060b040b12061918050114180406020c01110901020c030a0c14 64
    0xc26009840c00e000580c058090602e0b440603180c030076160102c101e07444144114050113150b0102360007484000c4203140d03a5104002011106412341030504100d4119185010540e0141c0380d10300c040b0341c40318020404c54040ba110b80d02015138005d845014117082600045503444060507015007075101c45a603032100c5000c00c0c10045002c0d001750745118030300b07107000c940030a43d04220b844480c124074000080240b231b49103000b07143c440c14001b070029103043e11a01c400a00b58000e218203a038100711216024001900030700c601a010041d20005101e12460300c44024250b98030344c1c00c169007502040c00100f24280c103060684420403040ea1036042c20b5034a41003c280701c10302410440c810070303c03002c0300003900244401102d203d54968034010b00c616038880c00fa408041c1c0300c5042464004416086400384140c500c0501600a0b01c564005483c20550b481d116003960a004168070b003048000552801540e010008d00050765400c0d40603104265560715140d150010510451031003e0f40c901010200c0da41c0c1c030 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 734938336 1250 734937086 734937109
    0x17071509090c03091119090908070503281e030b1801030305130b04050d02010c0309120b100603051005060d0e070e0603070b0304051207030c02030a20040905100209 72
    0x4400410070b451402e40001d000d001e07070f80780aa48072240b1007104411800c1070036808640d12400481e5035000e500c0c104940005024400c1c06664140052151000040d01440284840c05408070f554070030b1416084d0f009480c081c00401e00c1c1c2032044410044c40d03245d0f00346c400345044809906000a40c409020042070300100105540ba031880d8440700003100b056000005805140b15803110429181d80f59164145548618040c40b5444111801d9000c0190300c52401b08011600c80d16041d10211b070790303035613011f0f4900075050221020030a440c1008424060005828000c208500e003d00050030006030354124241140201d03405034100044481c08515503070409450640000101d43c0165910400342c40804416514144070340a03500000808501d01000e0fa0b000710781040140ca4900c410b21031040d6650300480c000c40500c01600ca000e000360b6001c0c40002d034111300903680102404900c2e00070440c1c00a00000d90f511a0b403a01c407141012540000f000f000183c004100140d403110700b54001503454114 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 734939586 1250 734938336 734938349
    0x20d060207140c030c01050d0b040e0703030512070e010c140111131a041a03040203011b050705010501080d0509040e070509070207080d03060614070c090c0203070b0117071509 77
    0x14080300b0012022041100c28082c00305545050032183e040540b01e8840f03c200c80d00043c81840043e5404000358084181a0402040081e1580e04a6501401c0401c81e920980200310080b41096641c1100d61030640d10401d146800c03403c0e1611800040c22890740e282010740800c0d141c92120001110940c0900d041041000b841c50f01e940e403149512242d41076034003e4644030b4910003040c40c20500840c1c256401c2c1d17142d4420801c6036480f15588403427950002407040ea455034a54011402d1079001d00454102c030011551130f00d80e6440759080450079190103078050000d60380100c11083da10740d400386c01c0d145900001c84011034010301d1822a03c0c40c0401c650481a80040c1000600c19441d030005422405c4440c40c20a440082104520a40071584944509008a40c0d602100241d00c00c400c001031552500c1522858510b50b120030a0030110ba101d03400d00b90250b0701c0040c000003401100b140d881d0041000232441c42c11045202c10701901d43c0028403032810103c00d08800c0d10111405448148085c050 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 734940836 1250 734939586 734939591
    0x4061b05190203070e0408160c0f030b0109050f0f190608070f061706031c0221030a200a030207050a05101b030c0f050c01060e0a050403022a0d020d06 66
    0x400d1507007103100c0c00c81600201c1c840d229120000170317840380b07040c465481030f50003182207810a08400440070840001c0c1c03030b04039100fa90144002c601443d0040d1050042c40c0250b00d100740035818071440b641158005401003c0c2c201e6100d0411501c480000390640e405140e0080c001d500c0c1e100103040d140034090a030090304c2036005500010515202801441c42210701c0c0c0e80e1080d032141040314003d008040d0643d4807541580200c88104542042d4018204802200307104a6185d20011185414105811581000c603c2e40020901038165181d0244a010035151450240862001c6c080c0543e144145040038060540208104091041c04e0000440040d04401594100810800d4100041001244c0f1107500c005041c40b581849111b0f104440704544691541c00281d902d010058405c0e400c0a04000850340d01c5220124182c1d2a01c3c5445000b43c4504c4408201c605141c50041c2c22b01c085001c1d04c1c0340040c0c4680380d501c078000c80307039202c10000481504c2031610403540780049000500382c2c1d440a0034407030 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 734942086 1250 734940836 734940853
    0x80705032512050310030501050a15080106060c0b0907030f033203040b1008161703070206070f0c0306020a0e01020705061c0b0424060e0108010b04061b05 68
    0x200c01800030484840010200c0d4407440306020009104400180011101140303489180380154011a008540044c0302c032003c0c0e0740e9580701c6003501c2c0215601005070b0f845800e440440791503030300400d001d000503034024882d96007400001005044600c1000d0140000d260100340c1d01074081c01214091a04910188045c0345241005080030010038009a15202e40440341c5035110000d2110445820529012529503103c030344035a00d41140c003a1040c148000007050020745407404000b40300580301c0780c4800c07044403482c200d0049000c051801d038104003074008001e07810045c0d5840342155040c40d80090040d0388100d403810040184406c42e000140304d14070005140043c0c82d0030603e07004150500342d0071a40040e48a00910000e80555456003032081d0592000b84c0794105250001046100c014100180301c05903c0303ca00081074142d01c800700020f220400c24025280e02c40403192a0400a00b000051549000410320680c4030314401c440070070032081d05074003110180f210b0525407103030440200d46108 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 734943336 1250 734942086 734942093
    0x1060f1409100207140319030507050c1026160c050f06070306080d0228022b1406010b1801030207060e0c0418080d0e0a05010603030801060e040b0a060302160807 71
    0x43c0110700031182001003400c5010780600c0d00151f002e584114082c42e200404486542c181d4403a00500e90844850040840c44541c41d10340f0382e00031140142686c1c900b00000e2517480c802c002e000c011140c0e000080300384400c0210100000d40a000b6031034480c070700040110b10505149050100c2c100c01403009004074018443c04652640040050341c00030403d032104c2c41c240c40c200740e81d00c0b2090780a1802010104550303407200003175000b07034482041c0003070404041c0c02c481c2c01400490514410f03402e030b592002a0300d560705200604141c00e0b114a40c22009140030b5040009840040c09400500310451040f113206590a9210703806584039603500c18014014982003119113500e03102142c1085014528001e00c0d61640c4000c8101081126044000c152500100302010000b8001c2401d03a41501e208010f02980050401d11800e001140255074010703542d410700b800102150321403807000d03115605140d41d5100f00d03a07a550000e1304552207414010703903800340b80c0c0030708521506441780036110a1010840b042403 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 734944586 1250 734943336 734943343
    0x91303050f0c07090c050a0e01081905041b060f0e060703050912070911040303081503030909130b060d030807030b03210c060a061503020903010f0f1406030601060f14091002 76
    0x40c2d8201c80d13070500040c1c1018000310781c01d0242002190014000c0140d8078810350140c502c058009044012140c1c40c9005407420300142d500a440490344010080d603501c1f0700d8840d8444050282813145042c1d2030400d00248024040600340240c03a2040c00300041c0c004c2010f02540844500420161200b00580c25041c042ea4072290903105940b00740c1d00705480400da05403210200e80503254140c03035145080c3c945405c070440311100c4200b1240c061000300a04510b55861100c654418041c42d016504103c003149003410440780050321b40d5010341e20f501b80100002e07822a088561184581c074000070f42050480000c1d28040d504500003c1200b1a1803100d503201950000401d449035860023220b04030f44652582c502201d841e03101d105509032142c80031468035440381c1c0082a41007001400450b0001784c01c051942100c680900301040c0550341e400081c1d00407500e10526600210442c0035000641c0f4001c2c001d460104482044410092007034496942005640c040e07600040000c3c007031500c20300465501070754 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 734945836 1250 734944586 734944589
    0x61608181816030606120f061d1902070201050a11151e060a0321030204050a0e01051c11040b060c030f1b0316030e01120e011a030c091303050f0c07 65
    0xc0c0003030180941009500034001d0004950746a619816525045031b500750080a4403500214031340e0700c40f070001510110410440650081503680484c403414001c070340000b032044600e40707050036134014400e0501503a009815202803203254100300c0c030201d00041c0743c0b509140914102c801c26210200c10300a010110100c0d1100211404020601e1a00c5150070400044600d200080c0600350940d000e04414804004e420801400c9043c05400d1940b11000905204116000507041d2603055004009a18000c804800e400b81401c8100c040d050664403218980104900540d02458803034440c064283c44101c119010604550280e9403109000e41c000311603075025507001c5503010418000d442c0c100001000300ca2040e403842c4c0300000d01d00056503056455191000f520303818003010104000d0454a00c1c01008150300c100e000001d0035414512103502180080d01c0c0c3c20303000e1782c045240b00c00c460716a146510b800038030a00c0c410326400f08a1a04446a100721409800703211000318007000d114000242c13850 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 734947086 1250 734945836 734945851
    0x30a08180102060c040909240b010801051020150408030402040e0729091e090c0c100209040e19051005190b1207030506040605060616081818 62
    0x880c0d0000348001207940e0f81003074440c1d02c405030041000304440003440c4d2240054502c1088259503501c0b45018054442c01d280b211005e9440d11982c01d5803441d0791041d949400f60000f1a8942e84083e803914009140c1d0402c02c0703e1120005010108007201c1400b003185900c00443c0010b800140e15003460080b03040d400c00c4d68102d00945c285401400c240402050081c2921501c009001c6900303c00a80b010f00044e0319049442455004c04c1101150b455820380b90a030381031034000342d4648400800c14041045001443c5032407140e02400f1140b6080004200303081600c81d94a405600c601c114800074004120103d41105c20388140c10303100d290a4088004d0301052070245055443c0f800d02802d0002c1074900c100d998005402c0c200329569040c086580c00282004c00141c03900c2c070307101e0310b0950180c64074115401c04d1310740b5800082000100f007858054a540404103071001814281541a40d0040118001c0d0051007440081244480d0030700c00312101c90a00030007482000000340004072107400d8902920100d = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 734948336 1250 734947086 734947117
    0x90408040e0a4d09040f0b060d051003080c03190203210a020421031103030601080f07120e0102040e10080304051e030d0512060909071412010f0c1b020d06020c0c030a08 74
    0x658186c10b11500107101e0000e0507032032a256881d00e29100a140041442030240d00c0010080041038661001d000400c01000c0150380c0c1d4070a20701100013a058034100c0c001154401c0103001d20850b814045088040b10108000d030950701c803140d101020340500e40000201c1d01b068072100342d8806881c0c40c0d00383e0050003a21811200500e24009580b00e202c21504603000c00e0745072011840321008400780c240d00265901c1c0104000501055103000d5075510641c11100341c0d00424284840c03000c031418607400c41c04200c58190005d180070f541c56140d024920415101d221408070b075290502421000380101d00006041e50131884800c0e0f0b014007181c000204c2e10b41329065800010f0468106501c02c24080c0720610000d1a1035450300003801a03200020f50b6070b9401c003034100c0030b1070381e425000d00a03411200070041020989079036400c0c0042103055600008190050366040d0032016850300300c80110019081180581d6400344210720f9454210a42c08103509841850b101c00e040c0441e08000c1c0000003034443c8c12 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 734949586 1250 734948336 734948351
    0x305190c0309051516051c0206010810050903070c0b25150b04090506100305060702160603020310050d0f0228090218090408040e0a4d0904 61
    0x115204200c140c001008582c0c280c0080c0010701c0c10380b0030a08010707040740a07189014030305a46040c3c00c04959004542c1b66215031041c115060300f0341e03070f82d544903019840209a03542c504035415584a2480c1c40d00286a81d0310340c08602c00c0036082c0201d60003944c1100100210a942d6404001580e00c0400141030003190050381c1a88004c04c0d1000b40380031070300000e01d8507401100c07030f6900c40281691705603203500c40c0d95681603400062003481120711809030064101b005501d942061414410020014001c6401c02040560b000000708141419103d0500e001a141d54400111116000301d03500829805020070350b5020410030300902020301d942c805e481c02c445001c220080740361001c10341d40002c02e0811038850203005440d0240d0243c0303400d0344840b00c0617820386410000314142c030205071410340c2e01e00c10020b814445000ccd41c0811a4000c4240a01000ba54050070000c2c2541e0040f026800d49121200d01c903018882c8006428030522030203402c0d00344140b2a158526109a8031520019000c0c80c00c0c180e2 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 734950836 1250 734949586 734949637
    0x1081218040507032a021618150f0b0408012003130201090b03040b10270f0f06030b0406050c04050f21010f0f060503070f0509130606030b07030e010b0f0607060f02070305 75
    0x4407c3c21200155020301c1003040c842d6100c6c024100c1d0043c0340360000302d000300c00104a1440d034a080014006101015a5941410700150a4400c560041009901d082c02464180e1901d00200d940c0503c0e6100c070013101e103560b4401200c0684140c0d00002d110340012050000b0b100c545a0100c1c0207030065603503800e806d5958040070b4549400d118030b80d20b14145518100f000311041d504414100c5540400000b0f94103400c1c00004125000d54000b62088030302c4a00700010024184a52604840c015032098189480c06000520007540e800e841740c081c081c002d05001300400740e44500f901d030300c0080d0001c0c010301c040040c01000514a42c00301d158010b00f0a540050b050034013058070001c0d924044203440041d800c210610072509400307041c1c24030300d070131412054000c1f600d2403013404051407055450400604081500a050303924140000c001d5034501104024550303a4450004035424003600c4890b07c1e0510f07130a0640c014003400224140c0280006007080400d60310000401d030300386100148104400d540c08 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 734952086 1250 734950836 734950873
    0x30a020306120a05031b0a0f0501020316030b152203061e050f010b07050a05010c0e040e03090d020906121903091e0b07080903100501081218040507032a02 68
    0xc009004ca4008201070b203181d98071600050740640c52401110101841c4d03a45004020b40c0740c45043d00c1c03503580401070003d808000312014035035003924a0107100d0b9003c1c0f440081c1c180194092164541c0b000090507404d1040c51b0541202240d51f09150043e00b42c0d920300303289015094515a848900252a00c101445181d62252030b01400c0da2800d0003010f40c0c204001c94080b50b00c1064240d41501c205481040011024007070001600807994030071003103c8084050100307555101c80601d4041e0400e1090b03130380e40c1e2683c141d08100950115100342c0c0c99115280490904070404060044c2402050500707018002c10380c22400401c2d202c2d503a90220a503550003e8000d016080780c0300e80c4201c06064041001095003000b400c2820b025601262404840e0710000b80740c800c40242e01128280c0f20401008659030900155074403072440c1c01200e250000ad81d442c1c07040e103211030b80114483c0d90f6070000700d03c690b48241d001140c29415280c00c811240e021654176041c0801c60341e0346000510542d01e1000c030030250384 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 734953336 1250 734952086 734952103
    0x40c0b0a0507140717100b010f0807080415060609050315090703240c0e0103111c020f0d051e070201090812180706050408190c1503060506030a02030612 67
    0x56503418144030079aa903a448442c25040400c05511800b00003003004070595a1900110511000901e51b15044401690581d49400c18080c184001002003494140d000814254402d1907440d00c802c4540c1c50b45006800c40804404516030245010710100351a500300645000f6210100c01311034110140250f003902942c3c0403a044e4546401c4514100b0010750b088136480540d0050a10325517a2446820880040f00d039480600400070700c88861803011035070144100413410710440381e907030702d8030380b01c1288503070310f454800403100c00c407640081c05c8600400c0c4038059882c03c2c0c2c6101403e125a040c010b50020f001d070a402c613000c01c151050004221407900500c100e412056114003181e0400183d090074001000e001440d0a0341c1a001c500c07122100c0c801808030300090140ca4403035646942c100410036261403003d0403144d20014407211407001181c04450010101d80300c1000c1c01c6c03881810036008802401c420b902054002c0700103c00d1010030356080d005540f1038401510070202c00c92a4901d0143d440001 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 734954586 1250 734953336 734953357
    0x203040f1707031401020d020720150a180308030901060320011e1106161d030a11010c0b07051902010b28080a050102031b070c050d021c0506040c0b 65
    0x200b00820014280c40c00410340c1d12038460005080500d040021401da0b480345400b04d07598510800b000d8002c403031151541014032029511440340c045200945141841142906400d11402a40312907480e030342025408003565100140319120706042082d203002c0c2c80e850000711040d1440000c03100004122103603c05035400165525500c0300014080710340580c00310580c0c1002c008001b81c5c0c09919540810040b40124620841d07504101d945d0200108120fa41e00c0c0c0c15140344c0354000700301300300c3d80d400134400032000e030441d00300c14030f0300744050040c0d43c1c04c01c0c2140010480d44080c010000c01030b801c06c004d13185070840d070320400c01a420350303000890032902c0d022281ca07070142c0200ea900c1480c01d8004d5800c6114030500750200352a6485484581c5407440030282100c0c0c0da1340010400502c803917a141041002c3c03980002450400c1803ea41d45c41210445006190140428101060a540d80c80703091451841c100000444840485e041140c0c4460040f074060306d081d0504400042c0005255007210b40344000b = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 734955836 1250 734954586 734954593
    0x10e0303090d21090221060f0c0403020108041b0e24040501030317152e02010603020a060804110d03020d030501082d01020d0e07030606080a1205160606060203040f17 73
    0x1c2010f041008000300c3e001a604070800640c07041c880e58106510032443c51034240285660f01e070800c0541041a0010540402c4210621007080141d0b00403803000c0c0c0083d0f11080d035005042c01c0e00c9154030241c2d80350f40f16103840c8140c44180034000005005410b01000f440f01407000d8915484e0600c0240c036001c2c440100000c035411403401d0407000070604950095508803101e0380d8107000d5000039804403000f401000420041c585804001d14080d0360540d10f00096000900c202455500000c000c09102d100300d0041c0101c0400007020400e80a90401c0c031280001c02e1f6001c010001e00b40250b8803c0a0180440441e2400740086072448001520920315450342e12034410860140d10403e105a20369040b10210359003c0c0013800c4030751041e000d0600d1a45c4c26800406c5824a035042030400d44040740c2c0001c0303880e0411055000400c1c12112a15414895800c100740c0d21007250b202d08842c007183d0380c005845285800e8000c42e4456000c0014000c0780c0c0601007041001b40c40340711094940108104e6004683d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 734957086 1250 734955836 734955887
    0xf0703170306040938060907050a020309180402030115150c150c0e030d050306090f130b04060507030c140403060e070b03040804061d090f0c0408010e0303090d 70
    0x100314801154840380140c000300d0100ca0a036030b200e032264040320b0110403201080b032921a0f114810481d040d2051540c11300f1005900b00745001c10310f41c0c84050441c9007007000001c0d4901e0014000c0003100c01c8034201800b03420048092450114100e2800d840c102d00c42c1d4244200b4a1a0202103170a90050b00d4800d41c80e007000109400701504c80c40c840d000200c40752017010289a00d940507034810060b21001031740b22075010b00f81c0c0301c01b0582040d07102c4800d8014400c09000307110541e03d074561600d0b41301204035008002c035114602007070f807241c1120000420b44101c81082008001d00c54010a0191907a900c0500070045150429940c5c252000802600c126003070108002203203190300803281050040c42a070b4000364440460304003030f91003142d0585030714000040800681d540082c20b00003500c2044494000d0a0743c800000e0407110700038008075240c54180000c12030020100080314001c06d8980000c00006070307141e00c01a205d805c2190205043d0149c9a404a0110f003d9000d10082c4010301142c1e03503900 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 734958336 1250 734957086 734957123
    0x52b0206041101110124061e0206060f060d02032502071a07060e03030930190201061d0105030607080405120a020a06060605030613060807050607060b210f0703 70
    0x441602c04046559207400d80c1e92660400301541c15003803801014580310003404e10314050400754104070310448d582070b4005002d100a0707010442e00e801c00c0301220300c03002c0300b40a90002155030240071010508544004180520254048541095054034401510007400400426078031143c440c416503107141e120010140c600e161080051a09520036840021444625641d05296070412506014603601c807001c000c440100445000600c0600c804030706115203280550110303a03024841b448401640b26034202d100341c40c001e404c400c1c0540514061501c41c1c0501d030343d030420070480030b104082c0240104008100540e128110f5244103035005002845c031000806500d031820381c0b0449242046000d00e42e40200001d013180201c100902c5035546040d1607090030740421107190408990741241a15100c02080308203004110602110380c00c0750001d03240c10140c1050006060580c2d101a808124189400382c84c0c89408000400044884100c4890400c440c074525a20b40b0680405004c2110080007218072 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 734959586 1250 734958336 734958347
    0x21201051507030c0c0807060c0c09021315030f0c05120c0901020a2607030503040b0f01230117010b0c0f0c130c020312090f0c061e16052b0206041101 66
    0x1258070030340d4038215003546e4460326400c14100da0840e90016560807054018468100100805040320034003c42c50070078160f51212908031248241d030f240d400e03000050380849010707911400305010404003d2046100c0190010550380c0860f0124040201d460041102d0b56081415a091780c007040e001003038441c41c40c2d10382c4800682543d141090100f4089030340000440441c016110461082c2c584503242c0c00c10b0303d028006a20000d142d550300c84078100041010614190010f40907000e2241c940300c40d4041c510048030000ca401c81442004203030783e0000650488124000c0030661800c3e03040d07c4011801d103030400c0e2030340c8102c540703294843c0190070180403a05255001c414038a5990046920b07010b401c0172140c20042044031340e54100d4001c0600f010351410140902d81c1c04a40490b8403900e0010540d07111407400c100c180441da1010001704051030000e40d5200b1803c25550433034101c80301013556150034208070503881c03441d22464920110641c5d80500000340207000715802284120302c0410381d03004440 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 734960836 1250 734959586 734959607
    0x13e0a020d081e04090c0e030f070303110c0a0f050a050303030f0105040213050d0609050f03040e040b0727030302010b150306010c051014102414040306020c0102120105150703 77
    0x121040e420740e1407440c00f201c5004200074442d4910229880d40d00701d1018051b0021500494081d40040103000c0680c180413a0f0350094036414101042518a0a650b103880e2071200c010643c0c102030850000304160301d005040b44c003180c0c0200c030704100c030a0b2a64189512400180da503804448082c2005100500d42500034019440b00501030b20305c170720764410000e0200600c0c00d60070380d030040d038030300120051000901100e2a0b00d038080b0021440c180c50b042c1c0c48210200b00910140c00702110300d02282d5914805c10100048000189401240001541e401a50b2408511003240590f281401c1100681080010b0740a161041c2c00124110b9072072900550301040d1388841241c15000b20003402440c00b0f518820f00d0916916040e40071801d10300040b404d0328140c074035000340041c032041024915200d19890340765084540f4600c3c0102c05620240422501405190401400d61b400841e00314541d010540c083c007200400480000d04c540d07612014401c45035828200004001010041100440e005468103c03 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 734962086 1250 734960836 734960857
    0x6070f0501090c09050a0e0f0a031b05060c04060905011b020907120216050c040905030301030f0311030f0c010b0a0e0a02162306090f0a02010806013e0a020d08 70
    0x14142e203495450410b82400d44d048130449942e030300b007070103110452442100740c0b13007102400900000aa49051643d1500301c0c182c000c04000381d54600d034546800720003d401143e40e104003103401904041103824626049030203004005680c03031038000b0f0550712036090800c070048011503000e0700141700d40034060f56400080213401800484201c1e89084241703440203043c40102c4240c1010000da01d890004d04182e03078104c0551142d424005450007043d1f000c022681166848010a44001c0c9189001c1c0c860180b03140a9000038003010030041501401c002c01440f15000100c020014981281d04000c002c0e801c50103141c8850005800044180240340d004000c100440c241961050186a5030a044100c0d81640c02d40c410310b04035000704005800b00201c0f82c0240100f0007400404c085d5942040d9125510040681082580300c0410b813981d01a81024401949071454042c041c0d1180540c00203400d60462207519014210026100c0c20201142d03141d40240d0042c1a0904150300d0385030017039075410404078107 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 734963336 1250 734962086 734962091
    0x80a030f1d042c030414030a02090105060a020f1203040c0518070503070210020c330403080402010c0614040506061e060f09031501050a1401020d030e0c0a080a0204150506070f0501 79
    0x4011128041e94541000040fa0780190303903450078840030022052440300c005000f9840380c84403e0042e500c80d0421415154151b83c100d131510780243c022494030021221501c05800fa842880d04051080d80007107100d0303030040d51400102503440d401e00140c01603001d4096203400c104000f0440300341c40758005540020451049803001040c4404400c02c80e130101c03003940b26079409444512207100c1d030003c0c03c000c800380e0400c08401e0340c000d030301c6a8604043c00400043c02c101d83c0c0c03800175085a02030650841d144c2d400100402c00050310740030310043d00c1010780c3c1c141c1d03081c454100010414582582440c03c06a00d01070b42d400400c0c01a414803986402074100702040361824081c08045480800a110300d4044004c00130440303515203014060700c0c0000d80c21505003010703180754105446e600010403001c1c2501525000520403128004541008500c030b1040d61320004406002950400000e40740070024003c82c3d0400601c149500320383d60a101620500d0b41103034083c0a40008100c540a82d440d5450054001 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 734964586 1250 734963336 734963381
    0x3010608070915060806010c0b070513030b1b03060d03140c0a0c1a25060b03010e0c04050a09111c0b010e01060f0315050402070f0804080a030f1d04 65
    0x40c00c0c100122500008a030a0741c0d540d0000039142c45801d2071000700910304000c90035040410000b05804503600c80a4030301248603000c0303007015210301d04030307100e0743c1a51103c60302a07500d9141c10070b55040140c401c0d407035510b040800c001e000d80c54442200d018100040021380300c04400d03542030f030f818046818016064002808920742c69074040c481800c4551103030408030202810004600c0d00114034000313115080d81c0a0010a910342814007616a15580c0b6a4448103085002d1800341c0207030000007030035601942070070303d20141f1000014643c0c00113203046a090010f81d9400b40302c08101c49108030080e05100c40250725100d54100a0303940c02c3d5200e050764a4030490003040c0c840c4c2d040f034a400e1f840544032046100c010000d5550001c03004403611610f280c18001594814400495042d0340d00825104a500081420412a807c0c040ca081c0c241c0c45000a41c6a81c1d442c07004a40300c01c02904281c2c04900c0ca070040c01c0c100745c40340340008803016494210f00101041d0005210040441c0200244405c0d480c449 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 734965836 1250 734964586 734964599
    0xf1d1e040908070c06080712020c0f0f0105060420030402060a1224050303030f0115020309040923070305070e0406090f0f05010f060807090c2703020411030402010c02040902030106 79
    0x14000d50030b0140940c65640d2606280c500041300040d440742080040c05001d011105520a0b03020690b6100072070096200e15111310b1041c00c0080d020240086403145c440d840c09441c0064212a104003011902040f4070b40d181f50940324412100382c0d840c03540d030b0400c10000f001440c001026203010307a610714020301401e801c1003166003250801918640d44140151b03600c0c5402c03800117141c41c0544003c0c0e0140d400d40c1000c20a1240c2c404060140001312038007452200c0d0024401c00c240c951515000304140620394080c208100d072643c000300751000910009070381c0011507600160307003822682d1240c0149822071800300c401304800340107003089542070b032621800303c04940000900308020b4012000346c10174003400d20b0840d08417a220f4442c2414a828080100f1003c0360106403041100c075407110109802d0424a02140c80c0c0d0701c8100150140e0111004050070030100340c1c8041c090b248292000c110b02404045e400c0380d2400202c800138001801e10501e01700508190b00081c0903184040c0000c07811075100c11 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 734967086 1250 734965836 734965841
    0x209040c030b0c030a05071d0f060c01020a17100e07080a11030a1416020a081c0c050324210106050a081b042307120f020a0f1d1e04 58
    0x241d11849000000c1305020038011507100c1c59030443d0309400c1c641c0620160340750b40741041940c944064418005180314406503203401d41111410150704001315540c44140c08081c10a400b08080d005102d01c50344001880a1807034224907095030007282d120082a40c500340f04548070540101003005454503046000726425a8070042d40c0640741c800004a205011a0540d000c041002444000451484100400001d4010410510035030f006005d29a0764099000c0700000c0720801443c1174641898040200c4485030703c040610b00446036030300c3d1484280800e009540c440e24001c4d0081d0f1b40400285010b9500c0c2c6940c1000c9076144510100200310a0790342c00c00904542115882091650460328200a9807900c5d140c0304102c3e03220880341080390595001d91690b0344211140c0c0d01030020500d02c081034006000b03ca80f0f034002150184213120031000003402c2c1c00a500103402c03440102c0c40310682d07801c2c0c480c003c01c02080c01d0407190546c0b40c41c102d000010801f4003501c044074151240503d80c0202d0300c035195070 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 734968336 1250 734967086 734967091
    0x22d030415062105191106071416060807020a0c12051c080a0b1e0f0d0c03050c130516030b0a1a04051207140f011b06091704050604030209040c030b 65
    0x1070070143d10303a003500701981400e03007403010150507081d501058800941030788459000c48809039030281d1200841d01d400c1200d42c800e0404001144030741c04540d0401d481c889000360a0311815607403002652540f9400f41e0361041c80b040020701c90420f500d018440c0c281c40c0141b000d1018010390854482006254180c0d1130f00c0420040400081e03000010000480024001c40c0740418080d50b020102c0c071040805d445c0106030f03222406229101e103465046940e6500d0280c0b618542d04114500d510590300d150466542c8454070226003e01c40e0741048000c42c2e400383c0f040900c81c1040100d00c420030121420110300500c00204ac82e0360005000308040380903210150b507411381400000c0c0803540c55013048200002140040c18000145e401610207004900916030b846501f0941034a410f12000c08007801656007c0da200b4100c3d000c8056841000c0074880d454104d804594018003090045644000d5040340c10320a07801080c1e00040208000c100609000c0c0340c0c25441405a4240c92600f170700c2e540c0300c1600352000e = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 734969586 1250 734968336 734968379
    0x120c0405070c0b09070503120405011202071a090d020607090302030a0b07050c070f0512030702030d18180c080106141204050c0d120e09040f020d020102070b0d022d03041506 76
    0x205106904081201c0005823058011403802c291401000030700820768000281e000640106100e410480d610a00d0350410141c81c002c903481c0d2916481440c2e86180061010005100b45008a03819600490741c05003500d4014000d400d0b100140c1c0c480c004448405050b11081001c2002400c914220500004000e0000141140310031450201008000343d0408034a90a50b081045020700590b0000b52a88912403282884069000320080640843c0b0300d0b90301140c5903080304010140a2511940074414208080e102c0030300e80d9889070380444004080d6403440b860110104620a100d03038403480090390151081d01140e03c2c0c40010f2022404681c8201c0003100d241c05610591007249400207034000845400351814020341c41c040d258088101d4449801a015002e440c10010941e48284800c6c0c1c003828014400d19a40c001000122000390303c184081081401e61043c5074035000c44c41450344a80190141006045445a0711042d42201145816030000d90f03490f180000c0c01ca8201c0b000d886400398 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 734970836 1250 734969586 734969593
    0xa0806130c1d0307060e011d0a061709010908251703060a09050705250501140a0b0a030b31081905030403021f140c0c0c120c0405070c0b09 61
    0xa04840c9020344802c0c040058882d41202006021a0307a2150300c0c0b41440d40246040c0e1080205005111902c2c0d01c1a448540c1180e821380012035081d8004009021030004915160b0f856610100344500703c4001302c030004d104000400210380340c03010074000722425000c461010754281d8450380e160303000502d03c5c428098521601004000031483c0c02c80c1c0c3c2d03074003c0881050500851520441c020602d201c0c52100d0b02c403d2248800f24505078481484420310b869101c802046101d005c034450842000c000c83d0510415420015401b5301e600b000401607048036407204141105032658400d01e421031841000001c03103500100c001d0403410b031a0604038440180203080640d581c02d00c40c1403411480d85400148401d0003000c00601c0002940052030b190030110f0981050510000680c041000d0007000c091302500602c06c5007403044054a800007410b02d11440c204071060010802d092244c000100d6114550030f80005403203401e5420039801042d40032082c0e150140d6042c00f1a52154003206040d03541041c641e1 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 734972086 1250 734970836 734970857
    0x40f080705040506062503090806090f100b01210b060711010e0d05150c0c0d0e0f0a030201081b07060906291311040f0612050f0c0a0806130c 62
    0x1040d03c1580d41141050340c07510f2604103a5103140300303620604941000485e900f0400c1d10305040c428010480035280140568070117007058900c542d50344401d039540f00428001c24041d8850a10144248414010103840e410800040385250304500d10700710f200401025100c4080100c0e03680c401005066281c410044a001174280500040c42c000003100382a025000780c0d40e1003000310b040024022040b210607000140c0c0783c1e484d03450403400b5004000003510301e80701703100300466055005550103c00102c151480b09507000000100440d01000e0b10020380425913031800303e40e01544400803642d41c4101940071134586003003641c0301e07003c480c0a00000d8400c076a49815244e0078842022450b0001d40c202c6095050704100500059000c00b003141112864598400e0028803a025000669009080f8031482c06003141d030300c0740050007a03071080000000c050302c0d0000094859219801c0b141c0550161402e49080244002058624103030150009500001e024060f8101a80c14059608050404d036a4040c521 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 734973336 1250 734972086 734972089
    0x111c1205060406030305040b0a030605030f07050315311a19050405060705090a1d070810121101020c15180303030f0604110706050708010e01091b050f040f080705 71
    0x540300605007070b1050f820184204042070b442420b43d015110a005583d030313500b040410a03801080c4507403040d0b815004c1c0f4210340c01800b42c0407910404072981038080e210b03403c00d0385501221944040b2114a140c4803601c20444840e555402c00c12080800c40440080f15000d9445c1c440800d030210109110030302028003000810241c003621500045030f0b240c001e01c51030a0941d20a81c440000034000b400b00100464006482c0e42c0c0c0441802c001c11000028020101940360300c7e40000e14129203c001140d123040201d641c0203006d2803410100e420a826901000c501541c401c0190303c11880c400c1e04520031160403146941e280d50800d00390075041c5100c40ea8840c924402002034109010505201760414000c001030b0b69800844242d0100d4200d070000341e05403194000154502038044041c158925040401070341e83d420500d0103040c0d0300c5116207491f650303a88189000648890010040c0060801ea41007412140140301812103410130364800d0381042c0d200c0e030300038903140400c0d444120345500c0450204402e = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 734974586 1250 734973336 734973341
    0x2c1b030c150702031614042901140d05090c0f09070e0118150906020d02150606030703060b030412090f0518070e0d05060103110603091c211e0606020706111c12 70
    0x1404040c14140907000009080c4451230100c807100b03641440154038a661101e441203007202c0c1c1c41da50150f02000345040c100301650355884040d02003400780701c500c0c0c1d010019181100c01644aa4080c0ea07038059049c030b0617001100c0c81b411200000c0d007000e000f0b910109100884036503030280c540e60799990000701498000000d00d803540e506c0d603450a41d001501c0820008071800c0c100e903840407042c5da0a5130b03691034215044000300b02951042041070740100c240810408100703070000c800c4546640701e000f45500e4000100000d000c5110b09a440600760f50030003518540d500311140d000c1c0f804d003405075592036540003180440c1c018003800c82d400d400031401481081180800310b40b009400351000f5046140070842c4036600e010030001101c2e5000764401d1003880912401d0340300d41d50301120000c200d20841038040c2d0b0b00a805440c0e1040390000f085a101d500350045480351108846c82a0b0041002520300301081e9a4250500c204070254003034182215801da003082289a0b10403030603950304454009000d1100c04 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 734975836 1250 734974586 734974601
    0x916090608061003020c0a02030601171c0531120501050903030702030912010f0212160e060a230309030322152c1b030c15070203161404 60
    0x2071000000910403151948200810ba440580c14016070f110480f040152030800040c81c002d52503c00c060000c48d070128582821051040c1c00301c103c400d002400403510340c05001408151001a00500c0850090901e14103203401c000c100b600c01c040e83d500704910303204004109820091541884046117003c02c8000d1044039823001d00400998210700f00403800940300c4c03141821403031041c4809404481d40b203c00390700100b07070002400c070115502d414800d81008141411540f0700286950a948803d40c64095407106c0d02108008047c1c0f450552030800590381150340d000f43c050b05035980c1d104000c5c0914603400a501814060008645a02d041c481d88880c0005046194003080d00c03401e8140005001001000e000018031800400c5025140c09140300001c1e49846403119a5444800349001c070760041401e0301e925070304040010341c0c80182d40030306641b0300001441b039800c000305908040380d48400f2800f900c406840101681e14408018200c0001c010413a008042484001003045000380b510384600304 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 734977086 1250 734975836 734975849
    0xa020f0106080705010804031205190f2a0c0609050c0a17030d0f1b0f0306090209030a1e0209090105010f060f021b040b03101d0a02100e04060302091609 67
    0x515401c1900e0241c8a040f9480307900d051026107000710b402c01d4050300744034680d80c0d5598401c004a2910042c4c1071031060016252448a40c80c0030015000050740b40100e800d41a5100f082000e400ca860300f4454940d0b010b00075010801012018401c00501c3d180502d00c11240110018520365044104104003841603501205545046415146041c50003000b0b84100030ba4103e00091a60000840030003e030a144080e48050501c4a08402d0002c0c0c01007180448022640d0f01000110b4075075003084128410005030742c3e4154041e45402002410f00d2600c44a030141490007031a500411f40d0114071084000d45040c10540d4640b00107204c81d28591141d2001080c4602c0e060742d0074040c130040a52201d800300c5a5820000d500e9100109a491b103410003000d038800074080304c4041c000c2c3c803c584010b20003100d860010b400b40c08092a018007000440b000b90304c2c1c000700100d425141014056401550301541140c0207600c81400201591754640901e00c01c001e80324144040f03803c1c1d0b21006105005940280 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 734978336 1250 734977086 734977091
    0x120506010503012a18090e0d090b041a070c08100c0f0512130804081f0608071806090f02090108060405071e020a08041403100501050102191401110a020f01 68
    0x104144c0503d9988002c0b84050708a048440780302e00e8800f110b1403600280400881210b4600024003081d403548040ca24018144c01d8a811160012086079401c01e140b081801c001c4042c0b10502224040103665007001d00260840b900d018030558542c0103440256214001680140030300900c080514041d07015200d03071920f4400a80d40140c0c2c0041d2440c01403042c4c0582c0e03000d1110020b242c8006103544102c600360010b10705034a4640d02c40441d6518604140b10500301d100842888000c2419409440181e45881014050040c1040c00c1c1009207540c1c44121b04180e61110300c0000c121409114a200b610304503003015a030359401100246c032601003c0c0c983c90051f4030740306c01c001c43c0903440303802e010920f80c40419100c2c9000324404c00302d18005c0588405400c1d0031002900040e10345008214210745d0000f40d00780c502c8030184d8001001110000d104d02070250b0080074454609051100c0840700c1c25101d0011000500040820305003101c00d0f6007a50556000006181c8440c00e030108181400c0300d600100a = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 734979586 1250 734978336 734978351
    0x905100f1e05040e060607140705010905060f1e0d0f0b011d03101808040f05030f150a0c030e0d1d03010b030318010201140c04051008150d02120712050601050301 71
    0x42c203910862058001d120300950100b81c5036582d100072203a0722a04050340041c8000c9640d00d0503100c070418403c3c0d6001c40c0c1307032100004490424105994520700500401800e141504d00d5031201c0109c01d0440e50f110042c10040c080e6884003d21500b0908810f402c00015004501c50014010401c1489a18066410540c10810541d0b0006d490305602c0010500400c010440c4490b0700030342c44100000a0205202041c04100d80c0c440004107000c8400c111f084408007120964881d0700d030b8610540e012610000341c0300281002c2c0b600d8004041e040b606280000707114000080e00c03414040e00b092201c000500503010405510440f1400903070402c030850080203040c50800029580c1e1041043d198882d040b00c05c0311031210f87c004e500007001c40c180c2c00301d02d0b8958034244881103001d6015008481c841d1080c488004d030341510451006204640c1c0b00d488103021a190000c000c01d460883c0000c982c8000b2050030104024814040d03540100070585100055039620302e0a9410004160805c40c0a072303140409 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 734980836 1250 734979586 734979647
    0x4081605060a180b1803100509060106110c040507030b030f161a0d020a0203031806070f05071502041e14010f110a0b131505010b0d020a0905100f 64
    0x8442c1001d1580c10012085006012140d195000a034052a803200300843d000042e0b00f054203140d6031504040b0309640814030205401405c03030b14145c1d0301301c45540c4107400500820b0b001d00d030030103200b8041904546c107540040000400380c6004884a40002e5165948115541020810340c4094551a070281031001040110003581c81028071401258044c2c03092110710683c0120308070344148601280c159900c660042010355207034000e0f90079082440c1000c0c42e400b65281c2c00320b505400f8503055076903003001c1c050202085446400c000d01c103494900061941c400003408a200520080c40c0c1c102d180f4001d12400d0800020100d800d81c44010321250160140ba104c0c2c0c1e00c11100b050403005c81c14440844003408a0741d5260410308a402810300b805c1c00f0521403a440400c07a40e4034128426100c445042240350f0302c4400340ca00038400c1c600e0050092048003e508151b070040e0181031401e1070039802003076584002030800c01c54442c44001180404014825041e0301058002d5000c0d140800031010b0076082c070 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 734982086 1250 734980836 734980849
    0x24011e030b0111010e0303012111090a0b123f28171e041106070605040b0f010614072301020a0e0a080a0302100b120604030504081605 59
    0x4a40040603590706080e9510b80c02150340040851060b4000c10414038a15080d41d81ca900078095030180c651281e41c1140850350107450a9151a40842d4500301d007150711040c007580c064054802c02283c1d844002505a58a542031400030b40d00c00c00700100000c2001c3d494003c4000c0c210f0780d0f165a81920440075404592042c0e80f0101584880c40f0115656594400b81c4081460a041c02040f84400c00f4504c04016622401566001c940c003507503600c440d118650301520707625800c1190140f03425030500107000300340241d141c8608040003810b04c0d86051503543d1110100c0e20f00b181c2c1250340740c8280003031010344260104031030f0140c00c20b410800301c90241050302d00c0660185140050801c00b16440300c0c1d5064491540f0040c00d001800002c0d91070728004040546603080d0b0400b1140202d03030450700000c1c4d00c00001052040607405070003601e0781c4824040d555010b0010404000e07044185120b04440713030341d02000603c4c030550095840a842d039007410403060402d0085103c03050003600600c4148107958562 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 734983336 1250 734982086 734982137
    0xb06090901050d03020f150f060a050306070c0618050102030f13020a030b070c080a030207120e0616050a08120f13080306090a060816090b06040f0e100e2401 69
    0x4582c80b520450480c0f030100d01c2c0c40504903551006d4001d1982050388540031900080c0254003050b0203440703c3d0b40b10414005403258a1140b564583c1c4810b001c650368034020728a090043e40a1500441d61124030600c042c440ca030000c108076541d81d4000208102014001c1e00c46800c1401074142000d50fa480c1d13000030700f10358502e0001400041d01240850462405001c0c4001d401e43e006031a40c2d243d0040b044003030000d4004800c00d41340810038a4403102003900c070303218042091500a0620781002080c200040112605501c2280c0921819030302202040000d0702900e2402603c28007559149060520300c01c0500002d8025290440350043c0000041c480c502500d074420b800fa20a0780c501e0f60340e411118050f26103a80b00c514103004081e00c00d0b24401d040c2564509a60404000388401d84424040c041248264032070f5aa4613901e191040c00311000b004080c507005441c0301400768005850300416100070708140c540084c03d900211018800441660742c5014903442401e1403900500c0300c090300c1344000d040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 734984586 1250 734983336 734983339
    0x15231011030c060a0e0d140a0e04090c260304030206040314150405100e03040b0d021c06060e0f010309030e100201110c0a050c060c03090105070c180c030b0609090105 73
    0x500c09042100200151024264500d003110560b044c2601101e00500c00900303201c40c40c0c01142e001c054031a000301c08046c10806208905880c00010f00030031545000100442580152680d5401020401c140f0031800500702600d00e290319100030b0850a0380f440c01d40f04840c005034006010030005680d868094404036a00000800000d00c1980300c054103044407605602005810030301440301707015000030a03044070281d0100c20000c0e00e600c041c19076541e0155108401a190f01003040e18034415094000e0152030301924000c00442c00114940300642d600380c0c0090300015401c2c880300180345019994031400c28801c1c2010000f80b500707a1401042c5204d01d032056802a8401e401d4005001c1c801d52045e900c901c00203900d1915010558203207030b25481192019a0303e8800e0b110002468230708001210080c52044004600e088040b200541d0550008903081e10200400784001441e40f54441d0141040644488001130076818414040c0486008a8645004a00c10b0011078440e448150001b415104c0 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 734985836 1250 734984586 734984597
    0x80304030305030c0c15090d0908070b0702012c04060b0711010804320705090f042a031a090d09030f11100503070206090a080a2001152310 61
    0x7143c81d01c9031304900c12444500380c0f621480706040c0d071500011041c0c42c000c0c2c40e1002625140d060044040f5651030b058003450310b10780c1008038104120207110006100750b52040c1003c29031440810800c821800100e0b00300b60980840c55550152440e1038400c0a018000d2500c00d00d0070040300d074690910b86039501c0c082074148807180340482c0a00640d07070b621101c1e410b030902208a0b00c2e03504548180b00c41451414583e22840f03030b440082094a401800300348a015000140303107155903136460701e2004480c0c1c5000100170b0f541c00010400c2c1a215154000c000d10300400d200403d00c0d49003801d60221480040281d107254101908800c80c0c1a0b0000401003100d80103111104100301d01d0070190100b00000350003941c001e00c803850b0804c01c584c01901962082c280d64091b0390346561101d84142d211000fa01000388139a104004c41700c4c1c440d0003a02c1c04c030007040e00308540484d100d48405c3c201d0b0840d000d1a05d9417a04040c10b0f8010000d201c444419101c00000180d0040060f010f40d9021410b0081d0328440b2006100e07 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 734987086 1250 734985836 734985841
    0x20f0d0c090b0309010c09090209091603200c061027062c100b0319090f2a1206051b030f06100f0914060906120906060a08030403030503 60
    0xd218600e030034068014019841d94034202035213200c5c02420344401050100b40c007080001921310b468826900305c520b0283c05802a940d07070440c100100c6506e40760140c00d040d0703207010b541104014811095912a2002019a643d2081100c554500704d80100040265652044180705201c0800b8000a924a175800200209107811240700094401d94115141003500711055070011a48010803074181c054403019042143c075411200e0504030700078040c00907070a204102084141a000040000283c00d403400091608000e54805422140100c1e0a444003c01c0400304201034a640b0040c100220b0324090b8034803510701e40700b10640e0030310045901900c042c1d034402c001f030441c0c2d40c202170101401d00060b01d480d50324a05816000c060240594000740540380140c10f000c5060b015941031038010301d440c1c540e184c00034540307180c2200320a00041c9903600441e0610140001d62690405400364050308081203203a45804103205281c40c0005184a105400a25080000c004080200c0781070700d0709031500e46d551b80d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 734988336 1250 734987086 734987111
    0x15090103021c02190c080a0e040608010f0b0f0a0e0a110412121211090907090b0703020a0b0610121505060403030309020102070e15041d030a08010e010603020f0d 71
    0x24000c0b00401c0501c07104002c44a60b804080c2d0303006003c804014840c1402c030000058046842003030314800108001c804010b4a2940b60090034200380352007008101040350fa0b00c40b001039003520074403100004e0b00f98a6140411051401500e026205003090340c1143d5030502c2c200d002e07100418040c0c00801c00036550864031002d01d0f034400403074000c1e10494001020040c201e103080c007090401d0929040c0040c40104901403d82e0342ca01404d810300b04c50448143c2810400303004c10203000400f0740400b0901c43c0d03210000a14010340006481854002c0c1c004c0d01c081c14003410840390649004015178421030900303140380f880070340007440c0e412080a005070004103841842c8240b07554407803540120b81d0050010500100701989a006003040710b10030f900780c40e8520b41c5c80064400c0c290094824202454034a6000c00300c034207050307000c4d5288800c183c070030031410040480340600b0344e807000007050000b401900042c80000c45c6840c1c51030040c465842c0c11460400007030025240c0303014101d00e0707449054607000300c030b00007 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 734989586 1250 734988336 734988341
    0x20703200904030504090f0c0903020f042903010b1c1e0812011d071b0f0204020409060806010e040b341d030f0c04090c0e04080a0e0f15090103 63
    0x103540340034001850074105400c2c0504150020300c1840303000c0b420600c2940603801a070007001c0882170f0f0381e02d90210441c1180d00700190400980d000940055075126403110a10900d02805241e000b44100c050401c0c810105240c292034556a185010307940350290701000048004080100a400215200c0300a0724080d04000d800503550002d001c0443c046107a09403150750301e043e20f040b2548400e200b0311000e603003030b0032501c002412140800030404100403210504100700c0800d00c80ca100e00350302e81300134403c1ea0001d030032601b054200007906540c0e490107000000c0308102090141107404d4581200d4500f0350740d1182ca240e00241032090702cec1d0041003520429401d000c6c3c80321200f0014417001c045d049084a00801001c0d14000c170380000f4001c1c001e03503016810003240218100a48502070801114444244000340010810481c2c01801c0c804001554007a040c80c11030040d07101d02040e030b9586581002c001c0c505c0001641051080400f01060343e481d96800c00000b9215200303109460300c070103002005800 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 734990836 1250 734989586 734989643
    0x50603061b0c1c030e0105060f06130e100608060603150d020103113603151b0c0a03030507031413080c0a030314010b04080d05071e050c150307020703 66
    0x2407040190f1442c06042d661490001044a5601008002501c1050a0a03038900750340e0160407c0c40303800ca107603c0703040900003001e030318003da4011480240c0d0381906642000782158002c0b454029807501b407060580c401446034100600b19420703429400c007601c2c0396850111021840744681110013140d011a4007c0d0458030a60603507010380303516008a40d02000200c1d07402c0410314049107203001150144400c3c502040703071708607004e80101507a0f41d2075000b90000e12000380c802c00840300c580f80005d155205000042c500103004602800007410a480c028090750790141400d000e150814003015500040038007903583c0b1030450641c84880c07aa490420340800e11403101000f10a0103008911424540c158108400145900c44150360580c0c3c4c9158101e5140210301802406400420354052040d100d40d000d840390714000c03041d41d4850894490b1100e4001d0b0110030840742900003e801c950103240400c98000781c01002c810315440c4d0f140043c0d000f52a44520300000784071412107103491803221560301d035101 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 734992086 1250 734990836 734990857
    0x702040b04180203010c020d050a030509070f060c05060702070302010f05090d0b10050a090b03030901080c040e011403010c02010605030303131103030d2406170a020715020d0e01050603061b 83
    0xa802d00300c00030035908202a0681c040d41c20b102c00660814800540188c2c1e2485582d51780c0d04110140000314003504018019400300e104500c030104804441c00f10580040c541e40c0c4402c076901940785059410654018005019500115810005130360800341c2d038140050795180c400d582c2d1032010002041580310041c050440c40c00c0c4001c100c2c114240d4a00803056a00840d0300c040216a1449a482036a02001d9101d4060300140440c52880d406480e4640d00590b08a540d54240390b102c00181040c8003003607002405803440c052480e10942800e2141120b21940d500c000e2100608040119950303100282850070294441000340041c040c800c2c6400c00d50500c001e09036a600d00158204501404910601c0304403100a190080c80c40000c04160700d00f21800c0391140c81000360b400311701c1e54008000825072821181c003040030b0800643c507100100e030901076003200140c50340340852184003100e00c0003007420703c01d070701d0082404140d9070005102c59020380c0882441c07105414400047e00940511a0f030318 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 734993336 1250 734992086 734992091
    0x3070b0a021215010e03060c0d0b0109180b09070c120f050d110a031d0d0c0212152a041e05120105010302150f0703080402011b030203070b0c030601140702040b04 71
    0x12502d40320f4641a596400703000da840552001154040545401d0141d412071324024040021a000301529003088400307100505000084941c4e6550440086503603600540389a69500745185403071a00c4800c030754020125182c0240b04940b070780e664058075414000075206000701e940021900d588948211200d491908805010b00c951403074102440d9000158204042820300407814812802c884032041c2e0799101344001c02d048146a1401c0e0303440c1003000710070b903000f82190410704040718082000054101122800b8072043c41c0a2221030b4034186c00e02c10b0a40c0030030502c034024100054a106581c03e031003060060828420082c1032601c5850005d520807500401152070904114106501440c101c074000e40300c0c001c00340102c01e41c40c01d45200c0e584402d4030384002881190042842402e046074494030604004403d40741c08101c8403c44800c101044005038070000310138041001814106800c171b10080c240c0b44c2035041c10300029100701000103500c82002c4000c92100d05554468000702d0202034046e004 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 734994586 1250 734993336 734993341
    0xc09060a0b0c0109053d060509040807060f0b0d02010e060d05010e071b0b0a0902010905150a0e0a030f0311120a09060e0108060604062f010902180903070b0a0212 71
    0x760280444100c1500c550141403403505003103440782141d50039681c1b1000c6220040018512803c144004001210304c4a959000301186a8480301d43c4640150b004913145500c0381501d1034480284d50f051309201c04154200903002c00b40343c07185010000d0f000d03424203144160b01c09500c0441d02c64025200b2200125003000c0000881c1c1c0b04402e9068040d000c183c2e594160001c0c0c030030007141094607140c0300030111146e040001e000582d80364800700c00c0501c1450810344c2e042e903680004084900b982c031102e00c124000206c3c805060741091241c100c0e2030f012703039610408a10310b440360b251a0b000e04e0006000e0014007400310600c0141071044a50301c404520469481d0013001d00c009125800501800020404000804845d9030042290902c554070083c216450706042840c01c41c1d40d81000240180894107102c5020652500013010869000d5000000600202c05004000c07803060306118414540612009204c810b400120444100d260009086c88590311039030364510084c40b82c00c0c003010601c3c40312003e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 734995836 1250 734994586 734994607
    0xc1305060111070501090b090607021f0e040b13021b01090c17060f060112020706020409090218040f0f0c0e0f060405070306080a0f030212040b030412030606020c09060a0b 75
    0x1196000d85020390b00e115052007004545543c40f02e19000307240c0403a10fa01000c01c4007883c404002c200c40807002d400d0318101042940802d010b04a003034422034441c1101c600d940e00d0a5484202404501c00031a0140849400c1c1d50100e000350760845424680c941d0009040b145803c03a114943c0d1a440035a0700070003a80d9100e0902081100c19405101030440720b080501100050014603180610400251500ca58030b80c0d10065a04003051840301a42a03000d00820000c25014406000109014400441c2c0600144104160040080c255411201440c0c007030102040500843c034111607030088021451082d40c0c18104a10050b03640702c2c80e460b500030010400c0010b0141405401400d042d1020711450316000320a4090b2002d50064030700c1036000000c1c22000c9000c0f000180c80c0caa003e40180e9101c0c001c01898039665038001d800069180343c000083c0002c0080c411401c1180d841c441c64100180d50520000945a13200240d80300d12424000021600a82d00e60132010000c003030303441c80542c0c2d4400803403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 734997086 1250 734995836 734995841
    0xb07030c170405040c0e0319241509180f0807020406060e01030506060a020a0224030115090501020303060d0206031b0d0c02061506040e09011514031606081303020c13 73
    0x5024000c9041590012807180541e60071411910b0050148c004411101200301020020340c00c03c0da802000300c6180301240808007028600c0c4103d014000c07407a030280c03008220081d000c0d0303400100040c0c07600c0c081407144c1001c114402034032a4000c0c0f140f0b150705080e003084e02850103890b0002c0e5200b850b10800140701504403114803414607080e01e00b4000ca681f030408200042c01403022100c050b030000590900140351018520b06084103580383e001c000301d03007000301d04100d8000740c22000000300300540204005820600385c1c00240400d1009524500e040740c0403c03082e000c1208000d01514022011400d11201c03c40c5150390442d00c080b103d48c0724000c042c099009440d40c0700d0141c01600805010842407181b441d42d071105580c02401301c9140918080e400c03900040002d080100c13955880d0301d0b1b030341c80300e1a00103024002c0021128404003503562b0b108060070001c100303042d0724200f80c080c2c60411030309401c01c0c019680318031b07803000d0304180c00054201039007486803c42c1115482003070030b03030394200401c02036 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 734998336 1250 734997086 734997089
    0x23030a0806041d3d1d0a052a090c0414090f04020108090f01091101030c02010c0c110310110c010b0607240e06130605090c0a0b07030c1704 61
    0x1241c1c01d0000342031000d601c00300c1c0d40d0002110100c42c2c1002e02c1d44d041c003080a68070710303003040400e0300441c500d41d4901641c801d02e0000307070b0031840b140c0e904c40c0c3d401c0c942c81c1510a02100d5445103400609140d1700e599803a40d6450903100108410041c401d0031200042c01c00303420b051003c400280c001011031070300709800e90199010340114070b902482d603c0044218100302e07402c60720030b81c030004100025454a40054800e030340020040401072150081d400e000c0c41007070085041052040f8401901c0d65940c038009410b4a501d8441d4004582c502400d2982542d401000b07407101c02d4105d41c1c40341030310903510046420007000301e8110a94a0410b401d065049400720010400c0e010402d008100503070340b503801c000031b5102d03c1c40043c2c0300410521070000f000100140d43c1b010302c1e220020014980350140205410300c001104c15070748102c0002c0003281441114040c0e00d600500b407002400340a8900b50000380004040d0058056005000c60480200b40c02411040d90481e045000d079030541c15504603541c0c296116 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 734999586 1250 734998336 734998339
    0x3030c180d0f05010b150a0e040b06040503100f0c030c0f08040633060201090b0c0f1621080603070b0705070e091c030504201311041a120423030a0806 66
    0x10303450406d40100d280400d0b583e00c80d00540e541300007610008104000f4000c038070703802d03030f807200041100240c00c3e5400c001381500c50000810101d40c6924600c40403088070b29075005903040c14106000611415070110b00d48001c4291811302e191030f5107644c14030000401030030964000400503400d2854002c44560301500480c1d5007007110001c0030303454407070887c240e81c03100038000c055036002400705807944500e4000d4078440078840d4055040c00b64203d10300014880300e030810f07142800c690030303401c400b5080303044444140d02c02c07801c080c1135605010020130b50707480442c4508114408081210030800400344010300c014010701c95001510305101c3e42042c0c4806581212014000c2404c21640031f07a4000e015a505c2142c05c80c100261120385000044101040c030005264480011480c2c041c03015400c0c41440c1d10300e00e0b1980441d85030750410030100b0142c88840f240848040017400404403204c00e191030941c1c0954010119400030f101d50708034a100411060200c0b8070b5000100e98900100d61190040307225540 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 735000836 1250 734999586 734999599
    0x605040f120c02090c12010b071106030411010e0405070f03020f16030e1f0c0602090d0209010611010c02031810020f0f0d080c0a0e060c030d050a02030f060303030c180d0f05010b 78
    0x4906440c0c1c05580305141d441b2500c0e9020400410140d444040544142c90107800910764140349000043d5042e4411141100c3c20b00b0364114681095074032048800c80d022040e80c0130421401c0400000d06412a44030744841011780000d4a50000401c80b420344510541300b10b409150404a8031b00a0b145000188000b80552000354a0002210800c8030300780c01e007050b50721355039244a00e50300d4150184d803101d00c80f80c2d00041c44400040040e150443c4c05402030141b41d40715201440e1200903036007510b52640c10355013158400d210483e480c198244182c85134030b1044641008903000642c0a81c240f4400c010060002e000b4280300740700c40d0a0108070410000c2181d69048102c2c0d443c0032555200d03008031050840001d00060030712000d4100400100300150388081143d0400b0001d034156826507100701d40350801203402000380f0982c4c02c04c6007041134101030101e000d1811403a1845540e01035008141d1072511036400d610f100345450310303010303041c21580743c012031406c9411002d4148103001c0e00141c003140e070040d80c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 735002086 1250 735000836 735000841
    0x5010608010b190303210905100504120c1a062b02040606090e060d0302190302030c0705090121030525030f0203030106020304180e030a02061603090b01030605040f120c0209 76
    0xf280e1071516015681d0549440000c1003081000034211461820313000c2a0707907030b142c0d404d4000c91010401c40500100c0c941010503149841d2502100207030003040c500051041c1e02c541d0b2800a4002c20701524540300301d502450059403190000341098907590105800ca5084600070000740c044081d00002140c0213450900c16070355100821110000c03031380304a0501440040105081e07181402d00000d04a0082c4101c0d4410b500c01203200748c51003c0010202c0160340006851002100305010810081c08201d031195103d6240c0b64203548003040030131007441c44200c0060f00c1002c05001380151802212900e6926a24a9041c0f001094501d0310541c15000705243d02005001644000b0450341610f2940c0d02031801d00d441c00b00105840020300040540050302c80030403100c0660100080c259440e0982d000b4095824018030240c000c01102e00c0310000c050410400c0e10100c0e0394191054110390b80180300140e42d80d10390a120303114865800c0300400c500089203d036211981d2090035540002c1c02254240a541c = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 735003336 1250 735002086 735002119
    0x303060b03060604031e240e010203070207060507290a0b090402031906091406040b07030605100509010219080307020f010e07030b070207081516030e0a060c0c05010608010b 76
    0x1070000721030381588020100404d20014026103005a005095400c4d22140c00200d0703501d500c02c031031080107680b10300400c604e402c502082c154003800e020380401034021403031401e00e0140291a44803900070081405000140c500c02c0145c04040c810303e00c008051014804030030700c040f1320b0a1007810380d020103281d41020300d80d22443c07030918070700c038010380d030040080c4000e14680c140c203030740340c0c5171144255509a0303202c20b06001305a145614059048a01010f071036103182c1460b20318615103002e07090004051901d2001d2040c1e450303240380d621070a2030318144aa250141400101d02c0c04481584074141540900c0616041141c0381e009503019415640903914034501d00c420040c00c950031103140820340c1d80b141c1000c101003100b100e0745030303004a400c0c4142e404054030b6540e118908543e0398401201d4002140410800442a20b08003402441c1840d05002641c0c0080d18190780f00340b440000340943d9901c2d02d0303c540e920b006003c2407074501d9002c0001c1c009295034003200e50003040491903d90242800310084c0004 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 735004586 1250 735003336 735003359
    0x203030f0f1e1303150e1e0105251d10021c0201180b0c0708130f050d05030d0e031e090301050f01120f05010b120c0a0e2206091b03030306 61
    0xf400c80020b03aa01162843d105e07644030150703000002080c2c607511401172002e86c4003808110420550f41c1c031468403022148071300d6804c581c2d0040c18025850b2100000a1300030060400c00b1150180a1400051000c00212441d0189100c400310581c04892103000080c11500424464500c1c1100000200c5142015a0503802c0e02c1002c1c0025105000d01d60607100015280d010498002d00d094058a0512040d40d980042d1355010481c0000310301c180040c100900003e40c81c00e40041c210684e822943c9514980d15143d0307034014034000074881e41d00c2c1d00c0d418108240400688852100d0204039841d05c1e095800e9180c425400818024041d50070500082d901c003441d404000c1c100c418010781c00c4e00c0c40f01151100d071808003445c44101c0d169500c510035000680e41d40c4008940d81240c0c00050007080d0003031400c100ba0034000c0d90001c882107048038104142052200c507a0310780140d0500d4101d4080c0085d10380300d03006210980d4010090400300d100040810380308066002502e03c60f03241000b203240c172003229922 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 735005836 1250 735004586 735004597
    0x190c09050a03060f0204080102030c032a0703080405210c060c040303091526010501020f120412050a020d0c0f080307020d08090616080d0f050603190203030f0f1e 71
    0x2004101600c00b000050f07150380c004450001444401414552104465401c4e41d0043d00e02000380d8601100f071202000d2000d0b40e80f90700d140241c00d028100e08039010700d0300460241c0d21004e0244140000004c09001050040c0144424042b500c007a0080007000103c0c02e03a0480c0c0ae80c2c404030700c9000b0016507510300b00c02c2243c003580d405840d410300191520201440f0f01c00020416001c02c80c43c0303410b14508806c0c4d0402c1e06210441c0d40c181ca42e103981000002450300d0220441003010b940468840c1c80c00d464000111001d543e01a98250088502c1e42400c80c0360000b808802134106d03100440300c406108003880c00c44162101c8001c5d582a8a5641d0b020540d6400b03a104040e43c00f00307071004120300155135100149070050f4054800d50030044840c2c803001d2075840015050b03480c400d001030500407810191141044580424004000c24203200002c00d50b56401d82c0b0105442d40050b500c1c220a5507002c00136100b0402000201c582d4500341c00040003413030382120300004010b8500110004d0303103400031000c1da203 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 735007086 1250 735005836 735005839
    0x2030709051912050f0708031c050f04140c060d09030f080702030f2812110c031b03070c0602070f0609080c191509050f0a05010f0e03070905190c0905 66
    0x320302c0d003400c0843e1520000c441044440d44036a0043c0e0039054018850040100140405903484401d92040c1350045d520141b80d22000c1d603e070004000401d0074000b0f0440e00701ea00000c04500d0311010560381c40c900704051028503440440801c036401d40310240d40106070194403d0b580c04682200c0c40d00152602c0f038050743e8120140c0c000344110400038403480040c0440c4e04d0f00607107014071000c2d2207044201004002c03002e00000b41d0040320f201d28203c020f00400e0340702013020801600c0c0260810300c40d6200c0c0560041c16160001405225200c45010800c5e81c6285410000c983c981c6552500065902d141501c2032000c0b4280760400010118001c4019800701d4817200058041e000d405010099a29420350703c0c4440014801000300b5034000710160744002c94403c0d140c03809401e040c5010803e060400107030b114401c0e44607483c10b0005981c041c074400e807242c00c90f060504651182c800001e05101c404d4101003402841d0400300502d03043c66151010902ea040801000103080d0540d04036114007c3d401182d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 735008336 1250 735007086 735007129
    0x411e030411220b240703020d050a09030605090c2701080111090108180106061106090321040c081c1706090c07020307081606021203010312030b03030d0c030203070905 73
    0x42c0c0010145401440d0072040051510741d402c0c8445540c070f81034541d01c400540c042000450381400301a0100011001541d040c1090386c00c2c0402d003180140b5182c0c160000406090711a40801d000100c100200320181000406201030080d080d60a01d6101c0e6050181c56011b10b868000014881e50621503583e028224550a41c40e00d01e0000040d07a100401418500d40d800602d540c050700b0f00700a04c41c00025200c01e0303031040c1c0140303500311640340f60080252908001e9041040b1101d040030b21806170460700142040e03011815a1241050a05d8900310b40c040c01035405041c2c0c2882c1c8414107417000c4442101c01380c80780303140d4000d010f400d09050745c8100c070782c00e800682c80d90204044100c103902034003003544010101d4810700d0720b50422a051600700b80000050701c070024010b200c0c0e00d8050000d00b42da0040100d080c0c0c09c540c9180c841418908000c240032083c15603c180b0207046403002d0084a4110070318490a2042c0003012000038029401101c281e40010207482c80400c5500d4031408013440c088544484 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 735009586 1250 735008336 735008389
    0x61a07030f090f050f120a060f0b0f060d05070c060207120f030b030c06090d210207080d080a050a0e0a0b0a0e0102090105120c120f040201411e030411 66
    0x24000b64007200124150b00a818140c07151441b0740070012180901c0c4651320209d0300c2e04160342a0300a8928140c0d10318400d8a007503500740819150741060351506414050041501e407031b600e8080d507404035881c0c000741a19000041b01411b000018801e0007c801071503450b8610019000d1003101140c0c44003401035810341190310701032101e1030700d00042c01001c0c02c0101040301c22610740c1c1d11441c01c81c0409010341c0841c01d007200e888041540500161008000c118054040300620400041c00c6c40002442440310b2551040480e03411035050303000c0701c0004c030f50700c04552121200b82003540140c00e045601c0c5118608002c0841c02009040c02030ba81840d406031125424030b80044101501d041004000340103c8100340040f21740c042312945114041c4103800c2203800c16003024000100404407201c00300c400d00c0ea5204d0403a010741c4024980c80c28031601c51282000b403000740031060b00d40e481110800c1c02e100d2079000d040e11010f8400c200950241d4410344442161403a60700c01c1c44020143c49490035a2841d10301c44 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 735010836 1250 735009586 735009589
    0xf07060902040b130e0105060907020d0305130b040302010f0e19021507050102280203031b090307080d0306061d0108040f11040219030b12060105011101061a07030f090f05 75
    0x840c0e604144010310218100000d03002003101030b90348041e01842540c80f030f03604810f8000c00b88946600f0040944a84109151005019645003000d02c00101010b40e583c002601e000001d81c6440e240d15440b6410b048541442d0800034043c150380e0310700032212407a06a0300035225100045401807001225014101d01c00681c0070056290214000c05201810401030301000800a2004203c02460502001803040c0071450b01e021240c2d18a2100040d98001c04c00d10103220080704040d40c401c2c5444c240255138031540e20110342801d00980c4034449038403c1302e1842c00303050b8064102c401622450b545101c5a10480311059200c00b02c0c4072001030200744500701140108481065003a03815000e01c1c00301c4d220740c2c0e810010074105d91081800c442586410f00000c8206645805540300e03000007200c440481841e03501140c2d03101d640600c81c0d5410300407191542416400c080d085035008242481035515000d07460054401698082d00302100080e80c128400b02510380119601000da40e612041c01114900745070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 735012086 1250 735010836 735010841
    0x110c06070c032106090905061006050f0906160209070338010f0519020102181905010305060d0f0c08120301060c0f0305070b040c03020a0605160b040c0f0e01060e04020f0706 76
    0x5240da103d42e0b00c0d8540800e10303000d030b40502d01105200364000c2c40316141c011285c031b059030650341040702000720030001c0c2d046404142c0140c40c00ca001c21240c444d44ca48141807584038010000302c0080d0000c540004000105070180d1003031180107800320100c0d08441c07c0c6045442c2e04100c078681c2d005820b66110505031954400c1b4000510703222542840ca01c0d10743c081304415541180c071951000141e400043c00c44d41190a042c401c46000b03401e40b8407440e0a4004200c0350f5400009024460401d81d8842c00500c0d82c1d078400d00b100003d6a0480d094051303039522800d14455281080c01100c00501c50208010440c542c0d8a048038100d0384682e40b540000361440d80c0740c00b01020100000e80410100b8400c90300803c102c0001940104d2240010307000540c651700c1440000b40b8140d205206118092200603c07045807060850011640030546e03041c80c0c0d80380c0c03621050510094203d88015281110045811800e182015050b0380c801d40b01e01c039005884102b0802607114403061900081d009200302030001c0c0482c2c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 735013336 1250 735012086 735012137
    0xb010507030507060c0c080415020c0f03060a0f02130f090b0906100c0501060308040620010608070e090709020a020a0b0604200d0605130b0a120209010b070c0504110c06070c03 77
    0x10301d086c501030710242c0c40341c0b51950000c1d000242c5a1140c2034414104035010020f20005035001d440100740b6a290000090f02d980b00248940c1015446802000c080b2403a981150302c242d40300d64102c5001c58a034800e4905000203409074400c2c880c908482c0702c51a107402440d03140300e03140040001801500c007220483c0c507580c94030b108503030750f640710380e008000504a000500045c1c449135440e004802c41c407460f002405110b600c01d90340170380d240c04020f12034600c02250240a03100c0410300c1040507216050b14500d44400da601210900f0300c0130440c0b0064560104403600110300540c190511501c60408010483d81c00c040c00b031520411216014002428800c068103d0130703000754000803001d0b81d40b00407404484102280d02c910350b07035468889655140c681d40180150194a01449481203c0d602040c0b0041e0180140c0c101a04045007400401110a58000c0a0000607205000d090004a4001015002442c03092203900602e4002002c8900c556040844190559200b640c00000200c2210800034034 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 735014586 1250 735013336 735013361
    0x51806060a02030d0603211805012d0206040b150f100203090306070206190213060c05030c151510080609060d050a080409150b090f0a090e010c030b01050703050706 72
    0x18845486480c44c5445034100441c041c48102001c0300701040000d40c469a084076690a01c8050790440d03040907002d201030000c0e01d10070b00300100b010106408485c0041c507441c001d0707190001c0300002042c2459002c80d078203000320b04c80c0001e8030180d112080382402c1e10000030010f40d040b420709040c3d84107a1814201141c0d0078170803401603d281048200119042150407507506015030f01c4441800103000c0402400c0c0c000300c024007811030402124034500c4040c1c0c5494490a03042203501c803401d009000b01401114010700c032110841e41d0180c40200414003d000071242e0f92801482c207619004203092036150a0554095662011011fa0311142001100ba0000c3c0540d134004500707418002c0080c0e020414188003d01510741c4035110707485c2207104425601c0d000c210080c0c290344440208980c0560310700341c40911030308139aa0a5205411130100d4221505680070500d083d0400d40301c000310301c8041d804081d006105136410b1000624400041d5220f102c0e040000380010020000707000491055484190072107003 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 735015836 1250 735014586 735014593
    0x2070807020d110f0a140d03050c060f19020313031101060801060b1306090b0d0c0e04110901090e010b0f0706020c0a0c060801061701030803060406030813050a051806060a02 76
    0xa030350300855600001d41c0402c0f0740c24000880002c6251802c2c45488954010445414000358140010b02d071018860313800e040e0003450744215440c100b40c01101030310018000742040742c6891400d003d60b25542042910320b80015070744800140c0b8024040c0c002c50f4451402d082d0000c86666603641e00b20760030aa50300e0018003555a0f890b0106800000307000324402020100c940640b075030001ca0280100c00ea0035840308042c0400e000080224400950654041c80c003241e100054540f40050151010110451115880343c90110181107010340d0001030144280d080c0c0c0c0e90058180c40f810b01d0070039600c0038090180424000c0c454a6a1000110001c00304144106009424044440340e243e1034205004021a400c0703815a000303008640d8030650850040c1a11302e00888803216413084501551018003001d0072055002000403031a40391074210600446d0700c003202641d603080360080030002034064000c2500c1202180b100041500d0030588600c0514074221032503189841e100d0400089500c588444000e501 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 735017086 1250 735015836 735015847
    0x706270b22140909010606230409060b03010602060f09030d09020f030303100302150a08070c020f10030509010c02010e0312060d0c080a0201031d070504051302060304050d020c03030f0a03020708 85
    0x158200700d0380050104071042030a81103884108804240010501007035170385000e070b04000c090b90184410801a0300700304c66560651241e10100c400d4400c980104111504001000443c000503100a50407241c41d60b0990f6040d4440780c6098150200c02d54010600361300a000c1010300d00e000d684191032a5100505450000069a01290071500301f05e44402c5803404d0b845040065003090038100d07002d001134160051800b0740110026010200140090003003094440700403085480d24501d0341e40038280101504218014200b00034050300302220866076a5082100c6505031a00500032080c0c3e040005005d542000840807604a02d280010030711a40840c641010f6000f19003030003100380c0584ac0100141040380814000074054a05807014505075007030340040840d42401c0410f0440580d00c00b120b0104249d00c40e0210040821180c0401075031000c1c001080c80100100001d20450b810780507003e0710900000e020400d071322800707401400d080d100720408c14a2403052180d8028440544181d40c83c0e801d00 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 735018336 1250 735017086 735017137
    0x10504080f06010306110a050d050606070f12120c091514070303090606060503060f0d03021f06031a13032f060f011a0405042304050706270b 62
    0x107600300640d480903084800148140078007802074443d521841511285001541300d001001c602c80c0b40519815a95120b000c10340c141c0c0c4807011600c1036078102040c0f50104c012820701e0181c0107050540d0802003103060b02ca41800016a000303282d40005292213a6005602d0044004000006117140f4020064110044560307111484040c14480d030107640c00040301129840d0020031141031b07420038410720200784200040c545d41c1704503200400d102035446502a40c02490207034540750020710018003240c194164001800c01075440102168054180c0001030001c0aa40741e00c44c2c2d0381911040214034500b04080e004ca4000d40703400450364044611540c3c1412030b000c45100c41c100010202d40150018008e06c142d01e040a0040da000d00b11089140c5071099660307840d8205481213101d002d000301e85480e01d02c0501d9101c820b40042403089403217a101c482ca454545a0b856010900407400805c50000c1c003000d654518554044181c20b03001c441080203401c0c0390808865407c14400f03803408003d8071483c035100c0b = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 735019586 1250 735018336 735018343
    0x5130f08070203072c100918080a110c040504080a110c0310020d1506020c042c01150603090213052d1005030f0c010e0a0b04150f11060106050901050408 67
    0x10009000b02c44551301483c1a80a00c0540c0b9025070700442000ba400d06c0060620150003500310b844d0f10100142d000c012444101e11000310100c00707840d101c804260003030310640102d070764001201d01100b40c40c03a2501050400c002c607402694050034030303041442460b070258060301c04a0b10800a00e411075014407a0800040e2405680702880800c054012684154020550117010600b1401c101c07480440c0742402d0009688030b03200603402c6d00c5076890b10811540c41c04458080b903420044441d440c4003000f424080180600b811405500c803400c40d424000600c03602c2880703a01c0e01264000c1c014a00c44014500344009001e0181071100d03465050360094815a00422080780c840c28442000e40103880d0584103080c02d07449580c0840c0c001d40040140068290001c07030f071100c80c10400d0030110351690000300421810030781d6401411040d480000c01203111602c860b0316100008441d0360341076124458103c111b42e00455442014000d503c010014400140500060400e007138040c945541056566100c4515 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 735020836 1250 735019586 735019589
    0x11d09100f090b15030a080f0f03090c01091e1a04080607080601091203080426040906050a06140306010807050c03040f05030d03140c03040c090f0b0f0405130f0807020307 75
    0x2026a80c2d070011010460302d5419036074031985203007020010849180200742c4940d0310050082944100180304004035045200b13996808000d03805031a120714080c0c14644e9110004030700c0c640401c22060000406004546884039001300341e000804c0d260b450980380541503141184508007445041c8408100301ca004c003e0640b0401043c1d880b400701e81403110001d800b0280a800049074807030080e045401003074100308402d42041c4c1c041849502c480c20101c04900000316540c10b4011800e00040005000d03010360030500640c0d0301125581c00c0b4564404040c0e8008000244034401d03c081400041c12940c0a0701c040713540010b003820410b10342014421440e0455000b50000030f03100040000c14881401c04101c00b06c0a16814201040000b00083c0001c540c454001d0803808501000030010301049480702000008020000040c00b55008011494020380b8161460301d014408000f10002e50b85014046c8a0045c4140d02d8503030078965064607800b0059441e21070581da01d000c200174650058900304128030 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 735022086 1250 735020836 735020861
    0x9060f30082b020a020d0c0c03050601030f03090501051602090604090204110d2412030e131a010c0c05060d110f09030f030a09050616050d03150806011d0910 69
    0xc20072201c00c2c40d0340e440c94110030705500e03948107000343c95600e900042c032901a111305003042080500d19240c0050b001681e03401c0105140604400001000b0304107449042451003903d031400415114401143c00e07003d21401c103028865842e2001c80075040549940380c0000f40588049512501e540120f01580d0780da5820300d002220006110001092902c18409a103585051140d840001038500005e8546d480c0100c02c91501d401c0f40d0802018042d030510b02d2a0800582480c0c40d9a5440b810500100311644c80d528103100b0344810b078842580300310f00183c61290312007101c2c801c403030034081405a241c10500e604031000703640d00c00407280e0141c1b1001034020428040c02083d030707800034402814142070101324440b805600900044c40180c2d0001c413900240d030402c1e6400303074441d4400303100c041d1042d82c4d0a002604c0d0740140c10b142c00c02d40c0e500d50405c44041070002d40c001207040d500e141d60340da94a02489031000d04544400d2103110810402100340c0c1083d4a141100c0108044062a4045a50440e41d28 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 735023336 1250 735022086 735022117
    0x50d0e071412010b06030a0c17071d191502010902030a150b0a080303060d060b060d050f330402041a0d05010906030b04030804051e060109060f3008 65
    0x5003074a2408801020031088004000d02c2036049000c0441c03100d01018000c0640c5a86505140750203900c20303001200c0000c0c0f00f01032060316042542010740343c2004400c00042c02c048807840030700d1034203000c0035900345e98903e1117034103030a1841c040710314003e101c2031659841195203a030310343d501503030381007245103074990144117a40340d88441c2da034a19044601c3c031307a900d90140f00003000c204400c0401001303a035071094084c0c1d666004040245031820003890301600c410341c400d501060100520780d480d88001d00c00e14144114031120f0b11100c1c1244807a42e901017104200e00c070200c000580c1d504450b2551a01d801c400b60025013000e44a0420b000da2041c47c0002151020022a54a0703044045005160060000020400c1480d0441c0ca42c695a094005d0000c0c062001000125040042c104140740c4c000300c0c140ea9038111030a1001c41c540e02c1e02000e21038402032500b01a0017040d116640c110790700c1102c1c50403114410701c010070b091804140340308013400d0382906411341c406000318281e24020001d201010380003 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 735024586 1250 735023336 735023369
    0x3031a1203181c030e03030409110c0c010503090c0d0c031a0a05010906030314091815120f0606010c1505010905061e130902040209041a0a09140601050d0e07 69
    0x54100c6444450800b441041800c251190940f18060121a41a0940b4014100c51501c201291441c41075501c1201158508400091400031300c201911415001c44191088a1b85840c01100c940c0800c0c0c8070704807203401c1540c00ca0102e1401d000d0503440188142981142c850352500d82c0d00c0d007910f0b04170540c003500100703000704000303403600d4400c1e54050f0a142d0001c11501e415a24001e0004044130351240142c0d41c0058181616651058020140644642c5002c518a840030150503800001c21607240203040390345011a42e0300340490401c24803030200000f040d195842800440f030f2010502d400381e5014000040c44852401075018440c0a840401c1d400300355410406e00380188240c0d1584510300c0e001c0007003004545940c0300c5002c0c41c00c902d98000045440d01c81d03400024000d10651070710766031081c90000902c2e10240015116604844103c07544441682e441000109580703150260412015040300003580d158000c1d8040c101e52002d207200018035000758a0f65601d4a405a045900c0304403c6401 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 735025836 1250 735024586 735024607
    0xb03040308011a1204080c160602030408010c030203010b0d0207141618140a0c0327020109170c04090809030a0c080607050a081306020c030304030e0406090c0c03031a1203 75
    0xd0381003042200f144580c5854180600102410409400100400000942c0306015401040302c59882c04440c03004192065980c0c00207507495000c0d1240003100d5085c985da031441903020b0701c00c0c3c0f41250301941c0054604130900201c2c0d002580810b0f41195aa0300e09009110010005c12480d0480e10101400d2440e10703007010380108000c0e00d020341004d841c1307080c005070380305607220080042c1d000115584082a18070040b0400e40241492004c8144414006003a4105540381441076156081c000e80300d240c8616168500b683e41141c1c4500702d40e240d0307800790743c00340d90904040e44503150080c05000e0040c140754054000034100105100141c42009070341000340540780d030a200e820381080c2e80e401c2203442c00083c20805003640300e0040189039035400b400668820300800340c04079440c001c04803068039520b1500e0702d000703015440340104940c040d03885d000c80460701c000c030391007600501c0c2400e0311038101c6009075907002c602500a0010a4000d00d40108203400e860300d40b400942d1128501e100a1512120b5483c0b = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 735027086 1250 735025836 735025859
    0x12010501032007030f140c0c040b192705070e0102151e1f0e0414010c17090a02061c0b0306150613051003061d0609060d03090b0304030801 61
    0x101490305a4080088041c56112018103d41d1078a9050824507140c00c110042519545080d082c159415500003403216070140c400714200e840703400101c4007040101c4005d0140110302c28121110003140c841550f0500500d1034240d0341c001e00c1510514010582c15a90041c0c109440301594401c0c046554102083c842d5030301030010614507424110003041c14a04100a0035603502c064412100d003000b50800304111441d10f925240e940194402901c4d4242c1c0e460f100c9069010088809440e02c40c07254040803003801c41806480713440107013540c2d01102d8001107184507a0030740000d0440c89551050352041001030f00c414000e003003605805903504500613041d081c44802d44011840702c51080c0c00c07807002c00410443e0700303041c8040c1410650f031464131121000700ea40d0f01b014203600300d56480104031003103006050b455003003981a1940850b10014034681c11408141a280903900c0550082000c0700080c07041c104980702548250080c03902c03168440e921201a111944192000c2e000540b098006206984058 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 735028336 1250 735027086 735027101
    0x34706040b131d0a03090608130312020a1101090506070e030a02090a1e14060406080c01080103080a1b1103060708090604060213030213090c050604031e0203121201050103 75
    0x1500c0c10301c1a1264000040c1d142048a001034040b2561902ca0000216000003070340072000d070050032980d2809031400c000d0102500d520486000490f0708000515040c0c00e0545901c0440d41742e02c034610640f234084050806034204001010400c10031800da61450042401010f8507180510050102424054001081071001043c05406544103011500050f11510f2a0701c0c2d000d442490b00003010400482c400140c54601162075854a04206044030703c0d400c0c080d0b1075070007103030203d0307041008070b40e10148980c44a81103450580420814030042002c50004130052040030403504d84000380b00010104070030003070051401540c0740e070090002c1c65403d0a08100e5103410001500b0b010840b480c1c52400182e550000070170040c074054010840d0340e03010038034800000c060355000305240040300007828444020705410b54152612400740b00c0c0011103003448000c440540e0380010100388034074140758110342c001c080c1d944102d800d8440c8107043c01c501318840000d4084010407020040140d45010001005d86184 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 735029586 1250 735028336 735028339
    0x10615141822061e06050405130e100f1401030f030c0203071703040302100201150b07050a0c0e06010e1903061508060103080c07060e0a0e040203070503060a02070501060b070c034706 80
    0x401300c051040c15046000d43c1c0072a40c086440800360004051b030400604002e00c104c1581d48114003080020f01402d40040b0215000084200402d03140f03108110081c180a04c1b0240c41c0d213501c280c051010901c00c03a118564103001078200e8aa03565175642c00b480715104484030021035000072909208501d01260b01c5080d02c1150310090103040f0041c2c00703040c03c000481c400d407004414002050001c00c1424400c107280c845d0014240b411007540c40340c801c211208210742150014801030040309031850b00101320007802414084503000241180d94150080c200700383c600c00c50541c002d0740029208020000a80a5880344610300d0f155071a112070613280c04510740040081c001e04030102ca0316a1034100c600e800300c1e0001c480180046d241c90022030b0400d1360940106400d4020b03401041440c440d190014581c06104200802c800da03950350400c9454060b45000802c502440ba01c10404501c2c0c0c40000d140d140e5606103030700008001541c2114a240a00c00300700000101d2541d581c0002583d00d01207a4001d10 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 735030836 1250 735029586 735029639
    0x3070e090309061c0f1d0f2a100e01090b0f07350c07050406180c1709060106030b060a1205070207030605010801061514182206 56
    0x2051111207071203010703440419025203404180202d0108005881c0d00e01c05807880020400384038020140000390401c1d40c2000d01446400003100f20800000400c0310060b940e960141c805181c090500740d080d441c4040c0103009051011448640541e1502c4030803140000548458400d0b040080c0007601e101d0490b4001d10388c080b4140207000011704083c0403a40d03015400800f441c074006850051341d00d403000008031070041e0005c142c00000201c4a0200a080c0c039501603040b204001d40e0346082100765105400b0b41d801c500745510410104407820b42007603907020b4241c00c10307500701c00b200d1100d00e010755000c542c41d50733081d481800100515034061003040030101044c0c820074501526404050039804900d03030101500f0399103000181c901c078401d001c404051640b00d10280312a50350b41c0e070030b140600f01a0017212542c5c549415105007190084844601428000711481d04011005d505114905a5088010703005001c041460280d1032004090141140c40c6010000d10079040185409014000c100c0d001910300 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 735032086 1250 735030836 735030841
    0x30105190303020712031101140601020c03010204060504050402280507150603030c1709030a0609020310060620120307050d0507050405031f24181406040f0e070603060503070e 77
    0x80e400f20384c10081d514840c1c81910103254624040b5805900404060040c4d445c08001d065003001201100340034100036801c4508085003075041500f00d1049105503004180104030400c01820160080c01080040303031000c0440142c94048440d803401c400c01618002107000500ca410880340700c1802e8842031820804014507410359401900398048520058840d00d0310071600840c5c0e208004c2112142d01e00901030324200f070b80902e0218080c002c80c00c130403440b038040c4000081c01440b807481aa4200c0b807032982c4501c6441c401500c1e000c5000c0e0507015810860140703a418022100c500c50056001c0d11195643c00e589511450090044486c040e00d90b40800000b04820011760340c00041d072910f4041d64200f074000e08150444200000c000c03078805c401140300010700e80b40201c41070f000d048088981300701402c42c00c400341e0360030b80088805910340c0d145080b0310741c000304009080c00e80c8501c0740800d01c0d030f5000480580e0f181ca901d141a81e40c0c0c7c8581c0000ba201d42041c061030a081c031204000345880c012070212070 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 735033336 1250 735032086 735032093
    0x801020c0a170313081605070807060801080d08041709150c0c09061f020a150e0708060610050a0e0d060e070b07050d030c0516030509010e030307050a0b15090c0301051903 75
    0x4d001204060003050021a01026000c2c8070008407107200d900904036400143d64800d540c0c1c5a014074801c103404200e40000000d0380d01800302d9503544022595407841e4803540e4503540c20020b281d45105013009121309001000722504c44520750078200c22011200c645074400100480e240c902d0850038540104403e00030700680b81c88107019903481c90a0301e150b2030f0050f080340034101e1030150784002c00b03030503810200e002e01414011503001c6807020720344500f5914066203070030010f903a66100742d8800342c012a0604210000900c1440034207101c5200d8a4a0201509540006481e0703422400c0b09464140d41d0b552402ca0a90f410044040100b602003540d03810040030380c68207600d80560400200501d07440703441c4204131030b124600301c401c031003203030b880500b098140d0b424000c2c41508040820703400b2070b41d07440c0b189040d803800205a41c41540d0010041500c090140c0e41c00a041d000a000351903210060780c0d510701143c1da0284040d01c00c00b28074542e56140d625210400505100201762407907913503c03102061011 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 735034586 1250 735033336 735033361
    0x703110d030e1c0c090207050115080601060c11090406060e010f05010e06030603010605030a0f0506060933060409090c0e010b0d02030903131e05100512040c0801020c0a1703 76
    0x426003c44010703614100080342c0326803080111000070300c0c40c0c950002c00b08146a50340c0c040c02030705006000030042941701c04891110303c0868000c2e040c0561062004103e402d1080b00451101ca04c0b5801c40140f201c000b01c040342840c8010341d03086480d141c60314000e1102c0c0e42840c8a407030060a0032100c840b03801d403400c00007829441d03032104070f640030320000400520035071025005200100009411038140d00c010b4108811a20001c0400f184e660044801140552038008500c60241072020000c038140c40d40189060b1900c0460701d8600b406c00c0c22030a01841c10b0703560074003030401400300150109a035070903894041013440480e0010309403c60b081e8010f110758090b02040e52a40905100016603036203270b8890341c0d03166001e0501c4048401e807414101048403600d52907506403100445a0f40301d680c0b40c45504004419480d002c038040001d101f446800200300050280c9604035000c3d150046980e600c80f03030083d0aa03403040c41440b589034083d681207010014500340c208035102162044908508205800100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 735035836 1250 735034586 735034607
    0x90f0b070203042102040209180f060307240c05070b040807080111090105030907122d080a031805070305070608090307110603041e11040c05120105091f080703110d03 73
    0x100d002c84c00201a085440320f80c100d501c008070040c0070342024071405001040b03268045510400c542e911f41c010829604000410f0f0059651481e40042c031000951625811000b005800c00104880c0c0f40085010450900a810190030400402903a0340c1c2800783e0503123007440310740c495000d0742c3c90424100011000c00040c0e0368884001d10304142d4a498110081d46804000c0c0c0010303e40f41c105d05c1c3c4074000c0140611000401640030b0741008a0a05130003452142644543c07405800400100940d0f50001e1003030788030307113140e00c1c00da5020301025903951200da02d1300f21550011107071a48200340904ca4180c00c40c05003503001c11604e00462400446a55058140c0a50420140260804000701c0d00b0007803040079144070144096064840b18629003030100001000d8030899010b103180010207400c25214008441c080c1e04004a0f50300d440e403a000903c05007507001440300385003c440f07080c40c044c401614081741001744600c00c001c020890450900c000594962503c543c443d0040c9440c03c0000b9400149511 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 735037086 1250 735035836 735035879
    0x6030112051024120b16050c0f070f090b130b0303040e190e0d02070e19090b040201080604062303030903060124080f0a050c09032409030a14090f04090f0b07020304 72
    0x300f296142100c07c5c2e50500802800648500030921b480303041caa8005031030800ca5540c15804550650b0ba0303140303c001c4450152101d600148614140c0790100e00035042003a03130f8500601203d141991311001c05410344e40c2994100314044402046468003079181c041c0303c81000c2c0340c2c030160810b00500d80019503108480d100d0340e03040114100009064041c05442018410303900c01e41400f015210345481041c01ca0700325000c901081c10f2102044082c10310384600016910111031641c501ca200d52202014401da000001d40e242c030003008449800d803004c0c491180200810781d501c080c1840c907068606140c66000350362208118402081200c846d000040113034210030700500000d020340b554400c01c1e080f8400c40540700e0709032044c0c0d4001c200900c48136019603901806181205090740301c1e9604640c03203105890280c000600c0c0002d4460480d036034100200f900090041041c140d003d28040400c0940d1800c0d07005494013000d05243e081032000602c1043d81c0201184040c51510703084c2019042260101e54116 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 735038336 1250 735037086 735037111
    0x9081608041403031215150406050c0f0d0c02060309010603060204030f050c011b020d260a08090a03140a0e03061305011b0206010b071a13150203040206030112051024120b 75
    0x926546a0320388010701e103e41c120050340d23510380768840a411036001400300020340c84cc0241c025850784011408c400c2e480030541c0c404907103500503005c02c00990806000d170300480d507a070f04d0000b001900910041000710711602400f4619041c0f4280366041c100c4480c00709040c058402c080001190300d0742c0b006524294102d0300c2c0c08070555036040200000c0b094480c248040d60b9a80401406020300c000036001c8034003c0c0e5200e40d043d03640d580300d09450b40c1d06814002d000c507003012419039840c10407038044c103031403886031030b020445404190010b0b01d020000e6940750082c10345c140440082c071030f080c0200111410101c00360891000481c01c029a0781d88144a2548034940200b584800c11854032407001c686000710340301c80602d003041c2d54212100030480e281150f140084e01c4111500c80401d000742c0307104540040c8002d040d80c0c03130040c110b040d03a1940901100c0b2401115004002c01d80303203100704820070014900c003103100c150000008649040503000b0620500040300d040e000507006000c40399001044441c034 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 735039586 1250 735038336 735038371
    0x1091703040303200408070609120822030f0c05091501080a11030a0b09010e01030b01060309061d06040209090307050c0d020d0506010803090103051b0706090816080414030312 77
    0xf1401041854100640d0744900c0740718035114148500a00241c0300400d080d522140c0e80c404059030780d14124400c88001028101c0c04c1ea0102d0100d8014140c1541c864010a485140702400a1404043c5410440d81d84039010013071800e0020500001001e044251020340a8ac1080441c80d0a00ca418000d01410004100005415100300d40c00c80c42600c9275200c1c40030b80300c2c1003074000500034082008600d405484000000201503ca041c1207504a0350442d0307504845900b886402c401a203420300c0c0540b21107850b01c1d12404074498007c1e4134141d8036101c102030451403d1607c1000a50031018210000342d81c000e00a10303010420110711220085400c56114402840300d1021540c810102c60024040780034180000903c014040024030641d8800d0780c08000e561b541050703142d40001542018100388000f44031120014aa540c030980030036000e00301c000c0c20a41c40c02c0781034011410b481002c4403e0f54021901704070010481e908158110000c4000c4d6041104061903888a000014000501d4000c010341c1d = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 735040836 1250 735039586 735039593
    0xc02031f020d0204030c0302151215010203090a080607121127040e030703080c031510030f110a120e2112041101081006200c09070e030f0109170304 65
    0x1128041d1802e1102952200d699040800c0c02890503c01680101d5007030302400503560210080300c0c20f407907440012681e5600c0f202c90f840304e0700703202d1086181580f100300054040b0ba9107042e40b030f000910300807006200c0c51034618001080c4030084a8051400d90a11a0b4010808a0103065074441050001b41e00c1e1045c0e04400c0e4911002004513001d074100b0303c1e104000485d4203012004141141c025114002c150325030041115103480222050000c0c1d028000ba160540c0c079100d0111a04181070313107070106609d500c1d62800300c100c0e200c8071141c4080090000b000011039800c64101030b0b140c1c000d5201040b120a10100302d40e00c46a000c0340c05000000030440059680c004c032002c1d500701c00424030081c0001c0c602450902000203003915013502066400b8001083c0321107808282094a4099407078026401c42040049040d00c1c2d100288030030703030161500c17101c2d807a194803e0030b611401c51a9540f0360040303001d906240c2010000701e0000102c1e418100e41001140100e1080780210f05070280c100e5681d942c506 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 735042086 1250 735040836 735040841
    0x31806070206360a03021216170c0901030b06040221010902030415051506090f09040b070315061e11010c120e0102040302010e190b0403030207150c02031f 68
    0x5038001d40c40900824201c03010407582007500e003e038810142d4400c102e00390001110030070025440c21580030000580c144014103184902030a815240340c202c1e10000c100c0d140107070680025400c60700551001d51845000c88404014240030484280c0d040c01440d411a210f0700c0d0081401004180550340001d08284081c25a00d401c2c0b03004108100328070b500d56102e8503d40003170360040e00c050700c0881e0003221150580c4c0d614070646000e482e48100c07030140c00030100d05010b02034102a00044e8401008140980c1640700c1502c058130a03032090340e44684902d0000005021503108010144450503003500500c07072150840070712803118400648480c0d030003071f95131022a01c0340c101c00507445084d400d06c9030300802c803030704010107490068200b4418081e41413008003445c203d01485c400640025590b034006100d604100300d600d40c41031070b4501e0034900386072240800600d03988103a0003140164040e244c1003040180d54120701d0b184088038503180307051603030940000390b944d00108030309025816110b800c045c40140b5513 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 735043336 1250 735042086 735042097
    0x60e070e09070501030b0f010509090402010e06040905160305040320070f06030b01091e0314030708030906041505070c120e10020d0201060b03071403090a0203100501032102031806 79
    0xd040300c0158a85011180d80765100340c894540442d0030507a403034004d480c0071004000700d40c5040e1b680c5424042c2e05d90800900c40b4010f001a8144032828810307801c941c803044000c1000c0d1440000120355400c04840700303c0f844441d081c0e40340400d071030b1000740400242e0080c4c09001403600f5800030035a004980002608001c00c5038001c0315000340d109030024149805400012030820240c840c40c011640e95120004085c0d4200c01c0e00c140e11060440500019a20000d034502818116088a081003920395661055600c181c4000c191903201c40104810007030700d585416044003030494140518140200b000e4200428000000c000c0c60040040c1c6808501c1440c16003100f410041c506081c040540c100030352500c8040c122640107500302000801c446c40c0900441c1d0040c4120b030740380214a0514080c100d034607000a00640b4150145010800140c0c4d010004466403404040300028154510728140200c030007000f403108009087c0c410881a2282c012040e18600c070464001e8003d04403101001a0092091 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 735044586 1250 735043336 735043349
    0xa2601030f1a0703050916030b010b0703020705040911131416170c0406200303010303050702010c1a01150f0e043b0105010e100b093c040b010804060e07 67
    0x44000f04a51942e06401003030150341c1660549002c040ca90514809801c2c440c080605180145001042030304500b40042c04071500920554240d0380e12140000d094481030f10782034a40c2111080d0258452030504500c290f0100b00141c10019441921820b402c020001400b040f60040502200525540a400200c00070f0300700a40c003002618100798160100c0d040b6020300c00004440003a050803591030400d01814050b41e1800540c10741c6e18643e0b0450746544014022410801310440707603000507079111404091070480128030b00a40d030500b245000c2c0d4002000000013001041e4400079040d030b420260355402d07050142d4001c112102c480100380480002048942c1c5030744a490806030019003408c9180400c5d620b50b4009204590307a40d141001103200a45a20340c1c2900c4040c0b0400c00e101d00c050080c80d205d01c0c094810309418081d0700f82881c01c0d61242d007030090680d143c0342c13030588644460000214070541c01c0718104548403166000815020380204000c00841d541d50a81c155038504002c0384009200 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 735045836 1250 735044586 735044633
    0x1207051803010509010c0e180c030405030f03160e0406050139110a05010e01050f0307030f050106180b0313150b12150c041a0306040b030706050a2601030f 68
    0x51010400e4000c0c0300302c007650000034404e048003076214540030000c0023800c1580c28907010103864000c0350145a910145c421222803204010016001500c3c034048c41c812092034a4540c80400c4101c000b419040d602c070100d40c0b150307151041c244a42da820040030403810700085401100380004040f071240c0c1109954103003482d05402c12108003000030b402d014142a0760280c50804c021651130700107481c160218840240800c100b441b0003031444005a02656100e0003616000c9107141811841c034080b03d01c01e800c00000a2903035859000725004000e09040241201e403038407842e40c1b4000b24844920803213000010a0048229802e0b841b52503646c00803800404014080c0701d0714561242d445554192101104441480f80c10008030004050400d0b2011115108680e1021032580d098280311540010070255020703a540341d03030340c080d80c0303003000750b031001d045203031902e903500ca10000d00278000b04880c00600801d6040312480084c9000c0a9041a04495015141d401750580d246011140d0380783d60340a44074800f0 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 735047086 1250 735045836 735045841
    0xf0e0604140a02070c1401050301170a231e03040501050f07050601091515050706050702160b3705030c2203020913020a23030102040e06030f0312070518030105 70
    0x20496801081214400c8456120059440c064500c944c886c802450703000c9102030004104030124142212650700f111030070f0394106142035a031001e00d00c2c008120000e2a101040c40d0703480c00b079070800241c00c440c1440104000230b246004400ca0740c0340f0a50069904120000c64040800c41e0018182c0300d172541e100c02641c00395038480e8072680041246444d0142c10b0300e18118001500040c04007441d0320003c00e0361b076a80c90110240c07118005400054007a038118070550500703500d810072645104002c1d05040b80401e13600c101c00060040c3d00941d10030b4070340d80e601190409403404c040081000c2102d4403a81805a100e544850001046004030b06503c240480c41020001c0703601078114800040c2c9100701c40888181e00c51f07402c101d0b0402d1403440b000790048803510f0180102c072000518010800c03001c868001d010034000c400709007a6040340d0b2140c000c080d409001d2040d00d14080c80240c100c042c1a030000c41c101002c4041d0b440440d8005000c000c01e200c80000c001e1070300e2000030703841c481e5242c02a0080c0700ca030 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 735048336 1250 735047086 735047101
    0x91503050f072d06210f09020a0b0a171b1207030e010b012708070f080d14120c04120b10080c01090611010209040c1e03020c1509101b02060903040f0e060414 69
    0x11f06001804a224216001d408600c0b200030b1415940603020554400175003041215014107111800f0b8001b004030940e010850703081390002c900900c0309030130000d0390511500b00400050b0036a1405c036001c41d166414500e4034002c50f41d03c00964004501814100741d052403043c8280c2e01030755441d030050342450040d503002041d500140c6601408907070f6400200d800e05815464210740e0b058001003840c031092401c0007030201142122104c00d03081201001681d142c240da520f450700c01d9100519085820021030820060640d4500765808010440c070005070000700000030000300150303c18040c040c1800001086000d00d840c0c00d5050310300904000d8002c02c03100b511400040c0554440e43d980e80e0944800b80d018903003483c802d0007a0b0380e40703100f0940200122003403540339500c04100200041d01600c034806580c0d90002c4030b402000755540c0c2c640621008075a14250083c1040002000341005074410030003008003000130301d030410883e2007014000f0701c50b0300c6000002d000303899241c64030080c03410500c0074003860 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 735049586 1250 735048336 735048341
    0x3050f1302041a0d05030415030218040e0f10090615030b06090a0603120903060e121b2506090905090d0309020105160804080d18091503050f072d06210f 67
    0x148c0715600480d028000101604030305074440d0000040e0a002c10410300038407820182c01082b000c00d0340d03c0658844031088552140f034505241c040031a0305441307211b10002d102c03181c8174441401c100342641c880103504644581d0380c500c00140c1068001d032290703000100e60b18038076805071020715400400091890382c0c00c24010200302e1a40030581e80240b03843c00000e820380d400a114402c04100d181c0d92410b2014015440b204d0076492418180e940c01401e1101c010601c0c846041003a002c103c40c003480d111410410010f00400e01c9802c4043c13580d103060140504080005802800d08515180105001d500340c0300480d00c60045006000d41d0704407640d540002c1003d14009807045d10440d1044603314801c10302c04583c080d56601c111521040c0c150018401c501e465041a11002c04811896160907a80d584d0f151416800003407101c901c1d000410305111a00d0201c00d840b1100c591350090350a2008041e51a41685125108101c18810b81e03026244400c485100c0040e030358803003640108031030b0100240c45c001 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 735050836 1250 735049586 735049589
    0x60703140105030f100e01061e0305060601080708040803060d1505010e0717010b0a0c08120f0606030124140a2703030207150e04020d0c03050f1302041a0d050304 71
    0x1012410500040340b24100042e14100000f001c100904510701e21a003224014580044080b1142d52a8100441c00700e0008440001d0116907100348e00846141d420b10500b00140a01903e0401100100b4081500e42c007d0110f90401c0d001005141c0c0e070744442c400181040c2034848010132003a08401d8039040f041c001e41c055030403550389a680300d103259103107142150f074905405034660004400e04018401210603002030541e03100541052645083e9640302c8100319000349680e6000340243c00b08000c00407001c1c80d015a00104281e90660865050001e030124495652a07403551040e041502a500c452080045500c81c02e03086c1c001c5560ba24180350b00400c06182e8400c00c91490007602d000715038031030701c008200c004c032078040d0b010f040028101000c46c1c2402540d13600032000c108040400d090700756510710080c100012101000140d46038804405001c0d5a001007200c1140d041c0c000c100000d491450805032445941110009008a1405082e444040c0c0c0420210340002240a1042c01c1200000040c030 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 735052086 1250 735050836 735050861
    0x90301060b030601271a1c0c120507091701020d0e06060913031202030709080f0a03050f0f16240204030c0317070b070503150a0b070f14060703 63
    0x100035103945541841c0e10041d5142400281580010141c082c6100b49042d00d1040c0d18804029040d582c02c0490b1040320a4a003404200400180f420750082c030014204040031102e0005100340107400c1c0024129081c5074118103281c0d52108001032580348200c503036102501c10160500d801d400c0c0e070007540c0d0003034202e64002901107182c1120b5420b00c40c00000c44510a000050020900e5500c8440c03880b002e4414180407010b2001c40c0d100e00c0204c0c8402d0010b10310500242d42ca003c00301386400c010740d16005024000c1d00d0941c10070041c0001095212044900130701d13581c0e820b03565850341035501e2011f83c40b1380c0c0582c4d5200314a0b00c5540e000c00c0124110881039550390032012416807003000d1200124030592100404201260a0801c0010a41c848145a4038040840c160408030180c030b44260f00c80c000c481c550300091001082100754042c4000d4206d000304243c80e80b455060034100400c1041c400c801e405444441e440b011303882000008030b0a44686600301e410703541541007206000e40a8542c00c1c5661 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 735053336 1250 735052086 735052091
    0xb0409030f12020708030a09150e06060103060605031e060a052115010e04020906150a031b111b24091e370e010906090c12020d09120302090301 63
    0x71401e1810a0003680c100f61740160302a40341d616052030842c0142080c4804507076400090514403032108031f07031040d03030250026034018141d50b00d442000102251920b400c1b00d001d011007030043c010070075990f0640e0480540c5003051203e00e9124840001c03001d80c0340354040c1da40845c03440040141c0070400004120108400c2c000c55203001071507002d080c1d86420900801061080a800040c09131502c014505d070022405480daa041c0766a2054400155201414002c0401c1d252009221302104003032400708204204e15140085a0103080166220174070122000e0429824030010550340c0d8034a011151900400c40a02e030b40c4500d1158103000c6a00300300c038101c2c800c0c6003040078000f543c95285007901090100400c424004444801e4140d500c1c11201d00b1040942c4802d254040300d0000e140c1140c01070400030210118541c03602140b002a1555600000d080d40e041200c066181500459444100840c0400142e22070641800f00802815614005840d00190110040b1400d130964000c0c41d1a0b1003c2d4000d = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 735054586 1250 735053336 735053357
    0x16110d0306031b030f030e01170a1508030c0a020114040e07021e07150f03090203190b060f0d02060a050c070f03061802030d260403030e0d020f0604060e010b0409030f 73
    0xb035800080148405170101254410001c0042e00c02c005564003ca014142420752039901808030001c0702d400ca0700d29035450f07a80c54682c1401410151414020981440114a4030099100654071180c041000a040c402041141c600c5004480180d402a010485082c441440c182c440256644330b0f10756034007a00c45207844e250410850201d071200503900c00016040c0310020810781100c0042d5107036842001c0540e1b800c44180180d60900c41c1a0009685450544400c040c07414100d1660f4005403485110740d002981c00846d0781c450a4841030890780451700d503a225802c101c2c0590302c6104a14015075a4005c8280101d201c010085010044d64000c41082009003108550001007061140000c4c0d49036010350103000c5218401d009990f1002c1d40e110020860a04a0f006154030260549086020079107407140f101440104200211503c48640300421a0b1509030000c95161040504054805500d807180550621170035000711100d90b0001e841001410502e040061410368200541c1c07000602040c2d1 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 735055836 1250 735054586 735054623
    0x1606050a02032205120d0b10021c050403020a031e0602030703140f07082403030d020d0b06071203090602070b070f0801060302280c0503040e040605010b04030b16110d030603 76
    0x654120156004c1c0c000c0650185000c01e0a500e6005070400035400741e114801c81465841780342c0034071503840307480c0c005280044883d0001d440c2c060405400d5420080c0c18001040541d075002045800c80780c0100442040d4040d4050454401e400301c0006410b4500000030b001081c0d070701d5840001d207500c1c00c641c4002161203260b03a00040c02000c0d40d0180003c0e9410000c52481e40c110078107410112502626114490007400119003150007090400c40d0b0180e02041b02c515440060013007120312542102c02618000d402c0d0b840d6041d00c121110f0300c108141d03481040c0810071034103904455085030020592005440c001e00000c0031400c0ac46101340c0012246400010010300038001d95029400e1498680b031031103864a440441c0c130f115848103004000400d155200490030510040000d005840c150203000d260034203058082d900182d00094840800308010804141d1084403103030002841c444031454105511004c47d0901028002c420590080c3c00480318060f401d58400f40403a44600c00e0030700d0007130344e140 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 735057086 1250 735055836 735055891
    0x3060c051b0312011202030c2e02160f0303120507091d090d0503090706050310090c0809010e060f2806090905012009010f110102070807021806060d021606050a0203 72
    0x1710004c1d0546d10201c041511490401030700085d10390a042c4550180340d04030700300710011098007a80c1c4c025800460401800548003100030018002c000c1c1c80f00807603840d580d4010020082041070101640c0e645011401480c070942c1c0490080c00c5c1200c3e00702e80200e402c451020000c0d0240d903160032a00c2880031020f08580200c0c140c0c0d1144840001810006180031001d0710326520080108015481c0d00e41e0105070002284120041c0b40107941d104c0c407103407820070380c200c0c02c540f090038408006500100800c0340300d08410f04860344c0304902d0051080c4c0e041040180c4004c8820100740800301c44d0808030f000c00c116101e58030415050380290000c0c00185039128111035115158400c0242060381004010b86075402001011900205850300c0c1b10070300c0781c0231965822600080b4044801c40780c00590f440652a000f424054109a0718444a441d400d102001035090300c01d90796004011500820a10900c1064044c8010041c1d0400c005204929044e88008000e5008643d42503038203c4101d0807541034031074003 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 735058336 1250 735057086 735057119
    0x10e04050f010626010608010e090109150b060c0a1113020405030307030f110105040f1703070210240e06040c0503090a08070609021801031509080403060c051b031201 73
    0x210411503183d0078a8800c46000e02c95403088840d1140e207000040400300d03000341c41c41c020f082999a1310400d50514140901100009d040f0b5011030381060a03110210340300214807101c410b0075040000f48503410780086502030041c400d0700e000e6030291a262034240161010340c03d039013840c211740e604003143d010704550301203025500980e0307055401032104400280c020600b200d0401075905184008001c07000c2c03043d00b505c4c0b00b21400c407180e00c00310141204200c920075042c1050701d40d811100d030540c584284d0080d510607000d201d03010100c0d04c43d01e046400c0070070b609104000c070480c002c00c50351a035140c2c0c001511101f400d490b0103010b2842c0808003640d0522400c1528010503401e00030b824100841d4640440c01e4000640641c0d0b40c039500e591207c0182e0720301c801040c0b030320504007400304c4540c0745003403008540b150f8403440c556050500301c860000a4907442194140c1e5840040000c4042215a048446020700d1000c1c00c3c010004181110364400e0000c0503200020000307080c4000d5030781720856881c00c070717212 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 735059586 1250 735058336 735058351
    0x3060e0103111507050307050c011d190b0d062408040f1506120c05090127110427020f030606031305010c17012c1315050105010e0405 59
    0x501c00102246648036200100030f10034403100394030302100405688640d000f00e44036480020350310100841440941114a02404d145900300544070f02d40c0f1900c0340b100307800b501c42c1206940c110000c0050300b82d040007500c0e050701a0b0b5203801d1440200d40040946020703041c1101c100458004007102100b80c50780b210b104030f80d110308254641b55140d003510340f04d0500032210022004c42d4041c604907144074a00081840c0d01250596028038100888400416040b41e0302902e0204018800d52007244c00302c00710211524414002d000c03888450764003d002002e607403030000d00c0000d400607548826822f01e011340440000c1041e0540070038030000301244280140070820b090140002805450301d440507540c04000080800e404159030743d50242103070464040c050106580c071901d10000000d1000300d6001d4680301d004820014060510400c811103a02c02d502d45565031600024480501da0601107141035200117600001d030003082000c0080c0200740a020f0000d01c50489844813480c0600400380036298 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 735060836 1250 735059586 735059609
    0xe010606090e24090c09100f0e090403081803130b0301030b01090501050d030c030318030305100b0c0c04180b0703050711030712080901140108010212090a0c06031517060601020705010306 82
    0x1809410301c44c032960000d080c40307044d01c020311102401d03407100402a441144166211460b017604035101410302a480c1e02c289014103c12820000003e03000301455810186000800c10b80e200c040c84d16070310394802c610800400900c101c5c070000751000043e000d14143d034890300030403400b60f803070715034201c03c4500c2442000d602c00003076161340307001c40c1c05104140f02140c003910300851305d031a98060344416102d218100710700080d606c0003004481c400b0410002c01502c40340b10720528000405034965600c003001e00485207e5071780d40d05510204110301c00d29280d555400b1070702002e145015003000d001441e040b100d05011450281c15094212804021180915030140351004000103103038080340c0000700245420025981c8903002d141071040c0c1200180244084d600160f91100d000d400d5070203403240589202025070014010400290590b01c1010a4413401c0c9800200040e0f1850040d00240031648044103200c0c0c0c1410f052444800401c0452045c80c3c280c00b00d543c001d42e0342004404654651180c0c000014 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 735062086 1250 735060836 735060901
    0x803250e011412090a02130603030509060f0c15160f0c0311010b1905040c0201050c0d0c020109081809011e1404020c070f21020f060901030e010606090e 67
    0x10b0082c1149010540c001221504049484484000c019400d81301984180d010202400031443c001200c0855418220810301c10140307503541c0945140166540f50f4031403500403640a001700000c2c020307290504958011284201ca412180440c035103800e0702c542a4079a4404a080812802010540d14025980c1d451400110082d03c0803102004100306c0305155540b140e59010090f0390b07800300511b40401f546404000c061070301d02004111205c001c100d2043d079042004000c42d0a402400ba2a03a400c6000700c0458020090001207004101e844801000c4400101714190070301c60b4040b5010743c40409480c8010300da62540750f80314031162501886061000f000b0380521040c00c020121140740b840c05030000d401c0c112910103150030895143c11016086403d07003c02c012005240b840c98400c5c90324203035440f80346e607641c0d00401e00d080c0c0d140380030b01d000e5440080c041c40c03203074400d0340030080c0c8120f038400800034140c6070040104260114811000304003401c0e404113004003410700c103c0422030450035900f81e500 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 735063336 1250 735062086 735062089
    0x7021521090a0b0f090f0d0203040f0e060901210c0b030a0f0605061b010e06011e090203013c0e0901060614120c12040809043e0c0a0803250e 62
    0x2103400a045d040343e070141490b8192110010840f107083c000f515005181c440d820090140808106940704a0001c22411300740302e001e07125801c58a049d14940401c4900220205120380121804810000c01c0c02a9180d07001402c0b644001c042c6000d1a11004188008a000400c520998590f8010070380c0c00003040041c0304120507406803281401c08804004910f003003074003c03054107065003640f020340715041101c000041108444070200c007400c040c440450455051410070001c0c03403050a500c048030398001019803210381d03c107442d02040e11800140150301e103407130380215800c240d415140030400f5800e001f1301258403805900c206a00300405030003e4101005030440e4050391001070806000380c40208480c034900f00150300a45c3c8a98028141c2595407031100c000d1200f1a104103409610180704d45044031039040b58080c01c4082c038202e032000308480c00712070450030350981b10f107401051036845282c18010030010b018001c1d40c0f0500720368640540c070410b0b440132021403140a11890700064010104800c59 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 735064586 1250 735063336 735063361
    0x70c02040b03150a020c07050301111b1b010c150903121b080a050a0207080c24072c03030c0105010f05010306031e150e0a020f01050a0e0607021521090a0b 68
    0x35100b0b0707041121f40740d50350340c00440d0031a822401e40600c10000056515103a43c1144000c4060000120003042c11710048200c04d651031280303604084c1000280301d60350b0b0511800480b00642d0800c101c0d81000380d140e5070301c0c014060107610555101e0146c00c1805540d030080a000031210b0701d00d140e403038103210356840400034001400f0007080c120040c0c0d421710881000c62240c601034520301600c1d03801048401030b45510000320043c41d80154400350310503c02c004003594005c15003e40528030140c0d113030018108514855044003085411501840080b61000d80c8580c15040030b0704841e1081c0b4403900f05600d510045047c0c2c1c440740400b600202144002814080e42036030101a40750050041403a010003600b00102a03502a1040e8a81948044203076029031401d21220b03a00700c070090a03c03920307047c10380f0005004d0a0022040c540300e460042202000d54950400d84901070702d200c610281e840e801480c44c0310b0500c4e031034241040e034984d261001507070203000040c03101310203074008100c00100d590301c5c00702c1c400 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 735065836 1250 735064586 735064597
    0x30f1606201212010f0614030604060503030f0d0f051618050616051b1309020102120a051309020c0604080f090a06030b13021215010c0b070c02040b03150a02 69
    0xd84050700114086084050101980e202107036500c40366254000304a03024150310603002510b00c43c0d002103040080c5070b0490320308000701814150f015240c0d5900c00020700108110703403100d501400002503158370014100001c0c082aa500d0b0010040c03904418640c00c100c45080310340740321004610b201003078464094807003802c08500d030380c0070b0401c03c86d11000030848581051a11303400e90307201004c2100401c0700600030a8200d00301202010486a0240005000b000b9180c0b11070420582d968400002c2d648240302201d0146083c0c803059a44240f4420020042d0303020145913a40046e0300d82000c244462940220b4000b41d0b160b43c0103111548032a2180b03032856001a160300e41c541c03005c11501c0a149c840d116220300030302c002c0d1000601c424055050224440d0400c0b43c50700d42c4d5204104644160400d0442c041e008201002a000008041401602c410a9048000c0c050120307110410030409d5000706400141c500c00e41c0d060192420b41c1080c56602c84c0201e003890500d1b00c518002039048829a4080d15 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 735067086 1250 735065836 735065867
    0x90d030e1c0507060f09170f0717041e030510021b1b0f0406030519050c1206061009140f03120a170108060103030c0809010903021e030f1606 62
    0x107031a074800c02500d0702030703500311500036000c103001250074070034032180c1d11a000c141c01c061034042c815402c07650b40e0a100c01503c651002c61199020600e414052034080a07103034520350001e1003d02185406010300320f141c2007880b40303a403031300e040c250200c6205045c1030815040301d5001c401020f0084a81209501070740002c0d0007001040003074185444150b0081004c404088102d881002e1010904020300010304100d02c6518015401c003101000090400920515002c0013031102c50f4000c07010346003da0030000b69483c496400301903c900844240c1e030118015000318000c0300c08a0b0161020f44c07040d1501180c1e4850400084406072035254581882805111040001400e98800e1007403e0011110740d000228084006001c1150440b110448070b1021405080c4810003008158516500140f070740342440c00050840c400460414126401543e60328040c59005006464259200c134200798120712003911107101e84100000c0701414140440c40e10100f05a0a4211121504180c0180e400010400340d0ba07 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 735068336 1250 735067086 735067093
    0x90303160501180605091506011b06091b080706020115030f110a09060f0524160b01030803220201080606071b0602031306051201031709100f0f0206090d030e 69
    0x4950f414110911481404d03c0340000292508111607900c0c0781001c1103403c0c6241c5220b0b542071000680c0c0020302d210300d1504484805002c12001d140c0b0390b01a0003e070304001e0055070023141e40c1c000c0b0b9003046a49006c1c0e400c0c0408403565580d03202d100b00d00b6102d801030282050b2100310030900100360303000100702c1c60714007840d402085280f40c0004580100b645602000403240d0b101c400b0700000f46020344020061904465406091a00c400b202003100d018414888252900003a4030010000b0111080040d6401c0b1006051540e52410602c15a03882140d1810f83c030640e4900f01c040d038615001c07505400c80c2d01a910f88049039100070602c2895442041e003a03801d9101c990b01d0010380070050001d800500700c0c0d0350180d42c695005046c4641481d42580002003031240074450000c0141c11400c1c00d504498001c1c404c58034003042100d00c3d2031148500c0303018a41120fa1111640d920a82214100050103425a15055001c1750b0302400c80c3c40f818191484542900010542482103200b90000401001807905a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 735069586 1250 735068336 735068351
    0x70215220f06200301140906090723070f060b0103090f0201081806161b050c190312170c0703080f04050705100906080c091f1404031103010e0102090303160501 70
    0x20b04100c2100f9002c000100030000042c4245454800400d520300740c180c0e080c2c082e6041501c00101030b450004c101c00f00300030355180e48111452842150900807a100801e8640c0c884540c02c1003101c6840d604002d9a006040c01c2440034107510a2141002041d00f10144107210200c5500447d000c14010300800d100b21100d0b942e000480005201d0240070319010325800701c0c5282e001002401442d281d00c8001141c18904d074101020600c0452410b810820403900c808240c0c6589260700709104c1c043d00050702c154691840b842d41540c000386031025a940b81040c2d401c80b55202c02d005103c2e8032601c0c00043c001070703801011400488a00301c0d0b03150810301c148141c41055440b0400f0802080384908040c0015884403070400c445034002d040150403202c00001c00c0c0c68292400041062140980c2400ca41d0002a00e4610b5042d8803d1150040d900040d80c02156542d80e68141156483d68004c2d440d40b00c1d518140020b0140f88051084410f465800f901940c14016800120b03140000b00820035a903030f5483c0c1c03c1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 735070836 1250 735069586 735069611
    0x61b11040504032f0640120e01080604202104080a0e04060609030b060406090c020c04060e0403020d0503090a0807140f0601080304120302070806070215220f06 70
    0x491110381d403d8035100b0600c040786010031031400501503c02004071b2096a40808402d00208840011704940060250880b5a40c1c40c0070161040070758020382041c1c030403440c4004103a8012088944d10500740d0720085240c945900f08411100071f007408109400b640346009008070307088000713001901150b00300042d40380182e0600350420401210111102c450000c1c850349500d802603405020550141e904010300c0d0305105020b00400080c0c0000b03440320444a000408650f00c1340c001101808140d641801901e001e810065a1500d08880f624807a41c00c201001c02d1800300200d40d00e104603090f40c000c00321041491030540301c80c0d102420510311070191020302d00c0406c841c0c3e001807810074851201415101d4424625500b030010552100f0307202c2e004074004005040c000020f0701e094601141c004420a802450160300e000314a9020070542d019042c03c0200540d00851088440a00b161808481f5505d210901113400100a40d441c80c0a480c2e4802c100400d0101d030070340782c180e4402c01001800905846 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 735071942 1106 735070836 735070877
    0x10e03070305161a0f090316030506010611030c03030604050709120803040b01052d0f04090b0702061807030807110d060906060f0e04330501061b1104050403 69
    0xa014912598107201c0c2c000f8104c0f140005921149d41c038907040e42c45d068240702d403001091400901103000240402107a00107070200014601d10750750300701000024140502030390704100c9031550120306413103c83d644409080c0107000941d03c9181a250107282094141c214030302131907020b11104912040c030320f0890814104070410849441c1400041140d05d816820141c3e401414051128280704000400c28001e1071a5030986400e6614020750092003a0710251300c400380d511091081010602003006030070701030300c10007425121482030400680840c03000f11080d07031020396807405842000390b50300c9540c0c001c000d4500201022403900d040880b850000900203440341c1c603040d21010344031041044e4030300d04200390380d00d41c840130402c0503a4000900b001d010f80c00124440d462003500c00204e4003440421540c1c04485074080c080d562007440046c01c1c01400031410302c2401448184240a8035 = true := by decide +kernel

theorem cover : BRFrame.Cov 734892086 735071942 := by
  have h0 := BRFrame.cov_init 734892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 734892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 734892086 ≤ n) (h2 : n < 735071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
