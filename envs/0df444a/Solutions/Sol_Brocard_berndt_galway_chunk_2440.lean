-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2440
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:43:42.098077+00:00
-- url     : https://prove2.me/submissions/5cb5a856-a802-4690-b920-9cf6d826eb23

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 438669064 ≤ n < 438848920 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 438670314 1250 438669064 438669073
    0x80f21070906090501090605030f18010207030c0b010909050604031409090108030d050115050702044b020906030a0b1f09180b060a2a0f02240a0c05030903 68
    0x85002034010115800750000007038110000003150740c4200303244001c0f5070042e02e910346182ca4070380300d04940a000070180402f0411031141684a024244001e02025001e540c80010584040c030303201c00081e5040e440b5100742410000148045503000c1188d030740059140c104245010003903541480c090041a44151f4406108000001e20348004030042c10606d48496080003580e80f2202241e4001078800c1d010340018000744010350040c10641d000180c040003074400803a014140382520b845a81d0201c682d05012403150603a4011002610284280703862030201c00c0d402c0c40b030310030045005804000c10140401da03c0300303144080d0703880b03031441c0c030790407250701007410b204500305450141c602c0b659072080c1e107080000c040b001d949c070a9943c46061000c940040402c0d203403040301308007141c0d407940540303103a510082009105020074901080e6441554411140c17081000424010000122036003403242032003003482280019582d941504955000e01076080c40110b0b21514207000d459802020401a0180700307 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 438671564 1250 438670314 438670321
    0x15071a100527070206010e18120a020717010207030f03021c05010603020307170c0702101e020a0b0f100302040e010209090a06050a080a0803010e07030b0d0f060501060c080f21 77
    0x4011940e9441c0b02d40001c04003140e8540d4001203035601c200f44a10400c0e0109030021450741c080c2941030111010300c400171140440d004003c0382509a0010711010090380c0701140420440e1001d601c4150700f080220000c600b4031985440192408460010300c10825a0000380f41403154004401c02ca2218811031040100d0340e11050050005c2d801070342c0000202c0d882c445444c0c80c0514584800d4414040c0c506201e0130160760b0740c2031041100c80a0504014440304084540c040448407850b000101500e0340208000e1459040c1010b0303803030006d041200c1e0f010355801086800390308501c04008480e13050390002000ca0300ea0144038020700031214160791042e8094140454254140c0008081d40c404a41040c40d0316915030519981d0011994010090f02040c001000340050003411103030300446a003004980115054006080200408001c232407141308107a25006100203845220b014090317a081444159000b9212a1040d0242084110f0000d40c00174801c032030380e8a06800b5110701c00a0310450703074040c00d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 438672814 1250 438671564 438671599
    0x7050a03020d18050114070302010605090405160b2b0b19080c040605031002070606050d050f0d09061205061503010f0e06040c0c200a080c15071a1005 66
    0x801d8940030500003034907083c02280d10003c0c683c1803012900161240020300d40c44000c1342860390000001501503540e40d44001a9603100c1003c11403103135209070054105810b0340b02e5691125000b40c0c004840c818003d1020340d00150140088000300461514014400c148008005000d0400e101c0e000b50001d12003886c0740f0340c100080b88040240c83c1c4800541d0301c416a024140801c5543c03512807164568444004e0410004450b4000c04c0507a008000214220b5114408503119201c0000308413903950062a03a1188044103010741c17002c02e0301c036207401560985840c0000309121910340d071b5445119170701c9010a081b6956903120070b5800307070740c001099102d6a40d144401407000c01c612980c40502c40583c0010b250b407405200340b4000a80c941c4500301418990b460780007078400301d007008110890703803009143c03e60f659044130003008000c03040c010144001144180440c402072a1422101c500d414004280042d8540320b85808030800e00c4030084480d41c0322840b80d482c0c14076944c80b980d00b111b95070b042d914502 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 438674064 1250 438672814 438672823
    0x30405010e07091e050c0403150e060f070f0905010e0103020a030608071e0b0f030a0203040212010f05010609060206092503140109290106260a1b080412030f0207050a0302 75
    0x1320610b0910180c0008100190050f640b040360b0142e546e007002c20062002400e165580032240301c1491001411040712180d00d4680395003581c95140780b040b84810030082c290711580b44d440d800d40074034003082407078a07150010b0110000c6086040c10716030040394500201d48607070710840043c050b001c1125202d5a9401042c010b1800102204d0002a541540440c7c81031409c8100d40d640005c00c1c1e6414070356914603c00030000c1d0030161080344e10090310207041d04070ba0400d000318200031104450006e955403400030080c001c0c501d40da20020564001c041003010b41c540c0840c400c0000040181c940541001041c2030b807680303401d9608010203050311000f00048140056010346800d610807000300380c22034942c680540910030340c0242c01c040c036000e10005001d00703842555111040e000c0c50301e14a04000c08200401a13064088501e820629660510356100b415500050303803a4003028145084d0030704198580b4013514240081103c14140c845800407440ca085504440f200e0360060261042d210235032030001d444 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 438675314 1250 438674064 438674081
    0x109120f02030d0911090f010e311518030e06090414010902070309140f010e0303040b0705010b0307050117010e06011211030a0f06060e09130606030c060809061506030405010e0709 79
    0x9040c01200050080140301041c0d41a42d00c0890320030340340e60320348034105002b190700c99a19054080c00107011000043c400e0030000d19a00c04d0382d901050850100e2840c04a50102c0c281804510800e030513007000c01d03000040d003841d8082c2501d446c0d0b51000c2030004038020b043d41c3c1100b1079841300c0d82800082c041c8142d5001e0907030103119980d24140c036981c030f1000d4280c0d03c50a5840c01d07803080350100401a903600a801c032084049001d42a2400c084d59102c000f080c0b03800c242000e9400ba5102c0365094581d1505110721005071400742400c8035142c00c9820340c480e000d201405003042011902020440aa0150400c016641016401880304c0c0c441903c8518042d00260780c070045041c04c00700c1030103000115009440903203100da40c401c1820112103040021004024080f000e88c02c80b54031303182000c216280102005076005c0e41e0b09070041c5240810062038944000c010b40d0741034102000b8461507076510710104403c3c44084038025100d4845040243c014480800260030718861408000760182998024040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 438676564 1250 438675314 438675319
    0x4050616082a01050601020a0209010e10050307060201151a040b0a030b0303190e09040203100c0c080a050c0706112d0a0b100501050315040513120e0901080109120f02030d0911 77
    0x80d1781c592000590b0b0352080b4080003988005484014403e11591a00c401d50228809001c0078400399584003181c1043c0c1e5640010005035100c0280316000100d10004500401444107449184408418a41010301844c0a0310081c00c400080d080421403198028000501f001400c2c0c950751148040d0350544003000521110206030f1102844649240aa18680c0310310340141c0542035074406c003d600001425114808020300c502c0c03c24060208440c0d901030305032000c003070721502da41d02d42c40400e40703191100c0307039001e0380c1080341d4403c00611301007002c100d009908040240d044a0501c181d481540c3c4e2500d8403440e0710180c42040241014880700001140c0a801248130890b140c2e03403900011100c0b4032080314a2024246408041c0b126800c059110590140c1c4034543c2c200100d00d9981c070900b680400b1050440017507510921401246002841c2d14010484070000308401c04d109c0d03454940204112a01100707205040203a03410450003031003224401d5003a0350007001303081c1c80f030b00d4000743d80041d40c00980d0 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 438677814 1250 438676564 438676571
    0xc01050a02091503040b06091b03040b04050610121101033b0a1e0302190c09050c04030f020f061c02180904030c1401090b0a0504030e0604050616082a01 67
    0x300e40744880f5045901441e0490300103800c550715101807003505080900b05410000740c103180c40c0880c4482102442c020b921407101001c0a0905d801c085161030406807419601203000c0c001004645944d40500700040d6010444000740c8a20000507001007800307803024101e010202c82503000c00b174030002041c0d08003543d10102c0810521103184195640e412600010716040c01c0704280c91000c44002400f40341e8034401d00c100c86149281b00400da07188102e00c40200d5a00c114880240f025840c00c0c011158003842699019040c1032454a0758801501242d41c043e00031041c080c3d45c90300e640c54003811100103455158000541c1c55841c41260003d40c011900e450728903030401889141c07031410300c2e5510301540c1c050b55805080141912130b070030703007042c544001d0300203660791003800000410b040d5510344a04802540000d641c42d09007400381c0056a840c0341944604420002844181e84510580f9459420341910f81502151482e0446142c0f0813519845002d1050140c8080b44040564031000800720900003407 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 438679064 1250 438677814 438677839
    0x280314040b07031106100b1b0102130602070b070804090c09090e070e060f1008090a0f030e030f010c0f03020a050c070b22050f010c020607170c1506060412080c01050a0209 75
    0x250b100d600c207503011b2020755030b000e00c20800c0b0039441000d01402038107451665400550b0800301400caa004100d020f203050040c000030410310341c041c0807001c01481c040118510700ba001e40da6203040d911480c05071040440c1d07101015420700e44140e43d03400103030120307100030011202014031995490402d03114604000e40500000f0700d00303082001002e0580c0380050001c0b21000f40c3c2800c01e40c0c90420090075040f641c411160528041039509402e1803070540244c8840c65204400020326007803003410039150516a040c000c0f010503080c0d0040c101e020040c00c2c3d01d4016218020000112a43c1c890003407004994451881c0108103000d80c08001d0016621445083e030341d410321a81e0741000a54540318080e03000c00c0441d40580d155000b502d06200c2584000d11141c50800c0f180d5580100104050304070307880c05030108002e2035240f001c115040091080d48154091441d10b00001000c52045000305000e02c0143c00e04031081204d1101595a50010070000348020701e414107290f0000d4200b254050720428811012 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 438680314 1250 438679064 438679097
    0x50301020405030d0c2402030103030e1c030f0507140709060501090602030d0213050310050106030506011803080c01090b0c09011707020d0e220914280314040b0703 72
    0x2194102e5002602809032508080d5060b51044021501a220501e100c1510500c11116900c1c3c144405608040140c495040d4107004058080007042d1900a81c2c00000000e62516040c50041d2601d905180910072003001d02422140c41c050f000d40240744441c80d000d10404440d01080340e0080d038061540400000f5980e0004680064680c8514000358104008030070210302e85030010410b440c00024039101c05640c8001282c58820b81c00d1500c6050b0341e6840060100b00e07814003816402100910b0882380e034040c03060300312005000c02d200003029050700041d1005811000e40001803030507048155008145410481100f00d5131181c00603d00040c6606007134031070f194030048014020010307640144440c10481d103041d00d05000c42700500d603000300d01c40540e9058101c40d100010f1402c500100108100c400c45c40d02176a60418800454826008a80300410780b184030b54814800ea54000e00c0c2d10041308181c2026035140c050382100313a0110708002404107504428100500546102c2c0e07590f07130171304482c0c03110 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 438681564 1250 438680314 438680317
    0x80603011107020607080c030910030c0f0e060f0343030203010608010e0411040e0a061b1e0302210105030d080105100302130f0306090b0106020607050712030e06090f0705030102 78
    0x1307501c40c405200c58408914418040e00e8001e044204803840d00d9000000a44441e21450181000030f84400210b018a940250441c1280c1403e00b041003400402c00f0001d0322030f00170812690000d02c0702000080c507081e20407101001080b80c0d00d40c4110782d29807406082d420400e041c000a600032084c0c0c40104401c9103e8400c6034102d4007143e840014a07402c041c9084404500944262b990050343c151080c960380c0d8a221303014281050000602d000072541c0f0303000050321100350010503001c010740050029250030403244200f1b0300703840c0c149000d0f50924020643c02402420080ca201070b5182052050301c0e0f84910780340d8185c3d40200c0407a10b40090410040302c00603230034091203800041c00e00b04a40c4047c00b03500501501c2e103c8461800d11507448158083e40d99191358415551580ca445c2e0020a00c4074036240680500224806450103144c06107001e0407520440800401d440b40c0e42200b001424800e03440340410600f00700c207030761890901600d61551800c4941c1058150301804400042c545414070 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 438682814 1250 438681564 438681577
    0x1707080613020d030203090306010b04091107020901060309031e23131511012c0304210206040302090a15050a0f09052203050a0e01031406130b060a0806030111 70
    0x50756442501c86503424029840b854410444c2544018080910141d40c1401440c0c083c00c00048079940701d502d80301900302a29105910707c0b4000300200048030150b181c1a1105042d2440340c203001c50b00d560a442c00f2542d041546100042049038240c1c8a44041d6100c07128400015003803205141c2e079154410716110b140724103c8500c0c0c0c0301c10030381d0301003280f25400700d07011100040c5420100c510f00d95070409035094850b0901e00021061000040e51515110030100c840d0310b200c1c4d500114241400c02c0300c28414450024401c1c0c011108c4190340c4004c6603154011a400786502a000c0c01f02801d000440c1009031032241c000c2901d0130b4025001141d181895800300d42150084d80c40d400c2d84510b0604000020074024040c0090708442e090019181014000f09040041c820743d40d00359151503152005001c251010400350405080c80030142080141c808180d130401e20894013001c2e103c415082c070100070000c50a0750740d00014003203a81d4a059820008051144ca010f81c0240000c081580741d50361240b1840 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 438684064 1250 438682814 438682831
    0x109050c0306010f02010e030c0a05060109091509170c0c0109080613030806060409090309080f0619230a061a1e0d0608060408041403010e0c0d080f0417070806 70
    0xe000042d580e40c46990b20500440d40750000003806c0b0b400505030341c2107030300840b9100c1603035102405010030444100b1585004000da4502040340491030b41c0c40b1506032101308000f2801c682c4030840f9600303000e4240c007600c041c3b4040d003840d1551480a00841905d6006400a060110302c0011002903550400b040480c440e0044a00c83c0c2e603024481d40e015140c0441c0984000d800c14024440481c5d80c089a101da05083ca00030345074645058900030050b8900f03184030207040a6500003409011150311510407450500001e07200100c1d1038003925481c07141203440c1c020700d030fa1242c1c4084148035906540b0f50051050703801d00e110006030040310245221507481025440380c0728081c40c10300340c940c0e00e8009002d400720308042c02d00820000da64000407443d20341c055400b50340c2070320001400c01a00d081558501c6017241c06038024003a014440d4684c03134861100303030081c038000e005410150003002010b90441711071114850f04180c4903901c400340e1005013917240b0103074401403080a001003511280020603901c1038403007 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 438685314 1250 438684064 438684067
    0xf022424060a0f050405090f041506030b011401020a050d0918060b04030206160807152702090a0b030307050d02070803121603020708030403080402040b1002100e0705060c0d080109050c 81
    0x21250b044800039007941d210010840240004105551040c144d80d000303201c01d02113191141031030300740358041c0035401042504451411404100003000c0e519105d0444111000306404039240000503414100760120051a034010400280303c8140c00505540581e601c1e1100c3c9541218000b18000c00c4800901940b20101401d0004100620745100241050290940c0b109030002255036440000c3e0444070007124484100014321000d01414810442d40805240c801c0450350004003a588902a003450044d005108880010300d608145805c10000f40074040e040780e5689840f402d01d1903c601d600402c150060040303401c0000e4035407001040d50a04244441d4001454440c1e104080090500d0348448050580a01503c004280100091031140d40240c9071940c01d86054410481119240344c04284202041d03584811019800140f03503020a0007007500049081c03030303101e41c54a0000d00342d2010b540100c00050140da804c501050b405d20040c500d0f1a8038010381d89446440c02551400c40c2e440300304060 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 438686564 1250 438685314 438685327
    0x60e0604031703040201093b0f070807020f07060c05161a07050109060204140901050a06020a02040b030a050a0302030a12020304030509040504240e07090212070f02242406 75
    0x444402144c00c1032050400d83e0740d4540e94100d030f18900d41b41c7c0090ba004002040200c8001034980307140040550041c40100c07543d49000c11000040100280002042019100009100324001c00c00c00c02c0f4195000200c421a503a1031200500c1c44a02c908101c9680c003400040e03416001003288807c007590709502105001d03003041c4900084a410108090368150340310226040031444510041018151001416850090442c280a41c000040c1d221034001e8181c03101c02c200c2da035408a4112181a81120049152120000024038100d0110000303491409034901c40e404058001004041100c1b50782c0742c0004041c5c80ba081c890032400100c070b014010442c10854417945e0700e003d0f0300059002b80b049a08481521640d03c03100b44080f41810380a0300540e80f0107540d108403208000003401031981c80c07001c0d8508050401c2c00060503d02038406024000c480100e102c00c60f00030f014080c07001e00e1040d2000080c2c03080780c00303144102e9400e550014002d041c200c1e00d041c0c0c141080c034401d050f241d030103803440d4500301c07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 438687814 1250 438686564 438686603
    0x9010e090c070c180b2b1104020a051c05010305030313051c03060f0504051b1e0c030a11030901140a0309080d0603050601120f0b060105070209040606060e060403 71
    0x3030008001038851602041100b00007035071180c1903c060000d40034100c14818400742100704445c02510810b00ca540f2408520491000c3c2ca9885500c000c211001404295081c5c5841e840c40d4101c0869a41d02c18004550007075030b00d6015000d0500c0c0c0040e244001041c108401c882c4084400a01010340f45401c00c100041c10311080c42c50b8507254034401d90451700428a4060f5003116101140d07241c000094503520b080180d00780415000d0040c1004940400442c20008000c403d50020400c44080c1018045050900782c02e241c070b1613640702c0482c4840c0d155601c9a1003a001c3d02c030b500103e0381d10701042d0480b01b02031030b005001081d61065030040e180d51480303001c0701240110301e8000b40c0710300041507214003030400000e00000c0030382002999450086007150075823604c1814013005800140b201c1c2c45d00103a03000031682620100041a070030412030f0703609840c0c0000495261007000c0e00a0b4015508405000803c02c0c103070300110860704983d403811940304000b070030880c1034880ca110281c0804c211000284070355 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 438689064 1250 438687814 438687829
    0x20411040e1f030b15030d030e0c040b01030207020901180f020c0607110715091a07050d050a0c020901030516080d0207270905060a06090204030803161205240609010e 73
    0x42c40c0715948911039540d030358000d01200101d4a0444114a240c89940c481c01c003000904400005810103001d91540502d02c65960034050035090300c03982d26030500c103505034002d9044802240e000b070b0221980e0f60312000d007400d40c5071b454421817400300e1800d421a88214590300c00c5e240c1142070075000d8001911082000c440c0d018400036850700c94018058002020034502089914400d255111384100364a0040000b42d1600400c850115540c020400e007000907001040d0306440f04081e04180749c489031400000c0781d40071002c0c20002d410100d20000403042c46400109010000050303c0c210140c00e845400d0f160300c0b82810340311000580d0191000b48141e0150080d000842d01803018080112600c2c1006503050341e60103030341555240c10030018016800b0700c500421000d031001c04401e614052455807038110300d10009000342c1182004900d00e90305580305000c00000100036980034052800d14071a41c900d004a041c4e44880c0c0746e1080c9074071312445d0600d81c094034003400e0161034186081c1c404a0512160 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 438690314 1250 438689064 438689101
    0xa0210110709050a0c0e040504230304050306130b071d040b030f010f0b180714030705072018010b0703050a020a050601060e2e050d0b04090609020411040e 68
    0x94010941d012800849510500b44035603480c0d0400304028440884c06040b0300d801c00d0401c0d015034109010800415043d090a040300760300d600d181540621807900040c01d5000f250072484c0e141c007810041c800000700d00d019a00c130940c000c0c0c0a207030f8207442e0148203498509512100c60381050345000045800c0ca00303980803140c4142d01905a8050100841d425421240140002d007035240d40c40381010100d003800701c04112600e107420240300c181c5c20415000b50406098403038542e00582c00000054050348501c0030348103120f51188a0800700a00c0f0540c9144a4881d03a0869006a200e9180d40320040794013503501d4121180c0503812480c1c1411600e044500d42d122071410030661180126010015004002050003003000e60346501050107008200f000710000ca0050803402c0c083c480702e5070310074100021864248801800c1996a841d1100f9600001d400d0342d001113580b240c600000d00041c4406600045007030303403003114200140d0414444541d59801980101c8202052a10004100744082802e0091 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 438691564 1250 438690314 438690347
    0x309280302031509060105011103071e1505180d0e0d02012003030106021c08060118080d05040f08010212010b0906040f08010b01020c0a0825030b0f04030e030a0210 72
    0x186440390042450540c4070503100a01204010810005100c24841107000d0304007440c15034061000304070705c1a03483c0a031410182c4000925505040010f141c03000790910385131300903100e88155002000080c010a02101c0d9004141201c11009603100c0c2c000c5109c06500440f40c0f41c1c82d40d41c0d40b00406120307042c0d00c0544100d051121006203040300e003008082e030319090074600000b1541e0390305050001341031900142c41c000b40846105442541d064000203500e0740180b00780303050391888805c1060b00310b1704c0388654058007850042c4152406d440c0da11070b008006a0341c040090311480341d543e4003424200d118120701026001c1d402d0006102c42d407840b400908a02e803000340705c141055220030032001d0b0710307217103520498841c5e554400c03004c850350301071010740942d0f441100c042c0011440d0140d416103030603182076132510003000010030015040d2400b000300042c581000340b41d01c95260440c80f10f82011410741d03042d00070441508007c425850300042c0504410b5005c0d02d10181200c1c00b51059071020400b02c0d4502 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 438692814 1250 438691564 438691639
    0x102030f0c030909240a03081209120a03060e0108160303080a060906091a0f030d03090203150708100e10120515090303150406050607080702060705010603080306120309 74
    0x102c4a584412a1501070703d14160b0100d017180c421006200644119034489025a13041c90041001c51086030558030741d000401d210036043e5941e4102d003070a00100d43c50009030030f0004624250000c1d1b0650050b020356a51032898000da90300e80c0e40840d41d403c038045a0146011000704140006842104c00e580c00441540c4040742c8544c035215540d040e904c041c0c0141c41d1069482c2c040d083c200d0f00c0081e1001d8400010341d92000b14140b8140401c0d101e02074015440c007850b468048140464600f08240d400306c0c0106501100c040c02d0810005090040030783e1700114000c17030720f00e010410443c02d070328143c0a400d503500e12a40702454481c5d000c0700c600700e40c241640c4a015500c1841e1078508000e51062140380e106020310759900c0c120205c1e14010844580090003689400c00500150311403d0803501d966801c1a103085d20f42d069440010464440c410b0001d040c0e50030014000100401d441c091170045100700c034003620a034070780d00d2582d940b07028002440f50b000300c2c104800211254507481c8a041641c400203102c = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 438694064 1250 438692814 438692827
    0x112062a020a060c050901020703030f0e0603040b07030e280c0509090c0406170a06181401020c060a05060d02241606060f0608070503061906030e010b09060102030f0c03 74
    0x10804011403445080960070054003481040b0607489000e0896800742051070070810306800007903485085000003018807405100e00000c1318094120058840002007000d82d59160038a8511543c50003568542d010034103201c644100c2c003002143c030442c3c0281d26208901040c0032680001e245c0b000d407040035039043e8549a0301203403a850f001000343c8600d90300d4009040d2941900c4c1404200d80c0f00340e00401141072110034903070040f1800306400c00c03207a07080704001c544541d426000030f230340240e1584020400d8900451440100c2010b401070605c12088d24140c1d480c84d901c4039440000d40350211062640300800400840040c9840140e209895141000750082569440c0da510700582c02001c048130f404400030f203680b082107918000c0c800903050b01003030b4404144c900000540784400242810b0140600440046c0c0c16840e00118501141c242c0d0b0000c070340c256901c21014004044103000c582d425428203201c2c02070f07801d0030380f0b049000d41d406a0095184c10144000c070032040d002448000e080d80000c1144 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 438695314 1250 438694064 438694121
    0x2190c150b010c14060603150c0a1d06040f03051902221118330c03090a09020417010b0603061003020405040c050a12060b0301030807030c02030a03091508011206 71
    0x44015110303001d0040c0524100300c0300700b5281c40c040424100e88c2644c510100130082d0f2a0500307542d1018003a0800d01d024100400e500c50360b291100d0100d40e004400400c00040d1a400080c0000c102c03070041055601c00e401031452000400d02c0040b000c2e4010030700492005c0c03001d90174a480300740003c000708001400708441680c1e008543c007058000440da184004460901c0c50240845000f980e260349400d0500403407070600080c61214840440d021040101754819130701414412542c00b040002c04a10200d92600c0b0715000a400c140100802200d0300c0c0603054040c1070500c101c00d043c960003040070341940e403001d08201c0c840c410f03648158105a028032000926440e6406801300e00091900c1d22600d640c0810b10042191000ea8201320038242841c608000004845086905494000241c07950355250b9007000d9899500e407050003034052043c2010102071560000c00403060710f148621a040e0b180d04d1020847d07804200303002c0c210301c09071407243c004c0003e00715a100c2c2000e020341d1310000181007030410f034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 438696564 1250 438695314 438695333
    0x118030e06090901030b010819050606010305040c2d06030b090408090a0810020301210c060c06060b160c050d150f0605060d02030601020d03060303021c0908070902190c150b010c 78
    0x1ca90511551b40140b14200c0103101c20300d98032070407400c40c04c0a445162101d40c1d4664020b09014141940d40c008541400b50fa00c4145001c0c4c203414a410202c0712300b52054512020000007400402c014a4030080f40c018801e014440403110004c18440ca01d86503900c1300c1c00c5070f911100c28581d0140700803600044441090248010f50b80840d800180c59600d45014841c0c00d08440c1380c81c094444120840e82c000900a03441102652820314124805040924001009004039004103840308004240d810300b142c0300c0b52401034010301c030700c54820040d40c3c0c41d42030015039640c0d0b0320000e04000c02d042c050607010742e059100d0300d401c0c6c2e610140401c13074a603070300040350251740700030400b01c003640d000410440e00c0d50301005070b0a600b000600c0d00304001480c1da24000c1d00c9981e2040c07107030700c0c8012100c0e01c00b260520800220010702881002d41c2c0405030f81c5e0750024002d501c48540d03818000d0003200d01e590078501031813108948680100884401e41e8184852100800c501c4492a0610421188040100e004000d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 438697814 1250 438696564 438696569
    0xd1109040c02210c0d0c08120108010504050709050919020414010e040b061e01050d0f0608210a0903030c170318011a060d0f18050d110118030e06090901 67
    0x2000b40c41004540f695102022401900d81c040550b0100050b030301103c00040c2880c140c07440f901c0c050b02001034510f41401c851050760700842c80004250000f0400c80410360000307020741d115004556032079585581038001d407642102c18a0b40c94010f051008401428424002c4001f0b20007071000409614806000c4001002038003c4500c01c688101080f0030000404007882c0c21001c111619185a080e68011042c840c820f102c000741003180105881d4203448541d00844a103184a510500a194940e40c13403036036030f0358408001e07003606900c8195202406920011510074001a548a42000d400e40d24103440090091000701c4e800041d103500510060640c030302450140c07102131034518001d50015101400c0d03541d28203541b4140010160410b100e40d44070381c00c803580d000c02480c01141c55103404070200002c02c6001200c00051940c161154200040850380344591042502c400008603400f9012600301e4031640350904219120f030030040c001c02e00540f4005070400c40141624588a1254040358032050203a = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 438699064 1250 438697814 438697817
    0x912150103380115120501060809010f05010503061b0d05090a171206042c011b020706051606020903010f0614030c0a1e030b090a110d080d1109040c 65
    0x882c031656031004140c142c842e4907110140c1035529078000d8030200d10a04040c86860386444840f1130501c2e04034003c240f43d0b10348105405c020413503980c0d104e00107814200210b0350840194a450714a0000881070300c6180d05868028000f4020355946006184002500541003520b020090115020204840c043c1e54498140b0fa8045c040b5030040340340500d20f42c44441742d1780e000c200051002145c142c0d0a424200e5100c04211340104031002544206010050f10b0f0b80301c407401100c0016115180c2c80150000441d01c0003195026500f03089034007013244c8642c40707030040800060b810081e44010799401003603c440c2c540a01c0700145031040d00390000342164129284900e2440d01d0300000c12020f40603009841c030321041903014004074064400001e013110614059004200d40040c5890404030842e14030702c000d142e01203004000342c00d11840542e525210700788200c0f594a090741c600ea1306420a000300c9450301d036204440740e0402403c13200140c0034184d0503000f850400c4042c080c05526580314015a00d40c00c01c0d6 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 438700314 1250 438699064 438699083
    0x90109050d0e0f0405010612051005041a180108150604021308060a15052809021210210212160b0408010605040501051005030403050702041103090609120912150103 72
    0xa40040c810f8000340102400d200d1171900c0010000940c1260400700c9441d02000005103076500c01071490280d85041c1c00c02604a460240130a4000c280403a04003000750742103586100c03201c1d883c0041c002e80002406090722980180c1c40140300408044d1900d03411240003440581000c2c012a0819031501c2541c0c00072002c2c4e4004410300c0056221f0f48151180c0c207403000c070000001030501001c54000ca103c00d1908480c4a0702c0c001c400700c0f541d14203001a0280c41c1501c825551400701c2c0880ca08100d4094503500f00c2403407080301c00a000a481280490b400010006100d000200da408000215880301c803c190140910f040d5685c0b071007407a411318030140007041086a00ca5040944182c2102c40540103030340180d140c40014402aa501e400400c0509040d25045039240d485140480e00d500500300c0081d0000d0a0041e052041c2c40c3c2400610f100310351407030450300c1607a40c4002541c1e4a1850002001001038200f1100f481402d20001c1011250914400c070740c4003041c0500074200f401e909900c2964a4446c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 438701564 1250 438700314 438700337
    0x1c0801142b02090f0708100302220e030a02031b0106080a110f121c11030f0f130605041701050403120f0b0904060b04051312030203150409121407080f03090109050d 72
    0x400c21078140d08800540d41010f4890300319030200e0440c045c04180ac045100c2203443c03420403100715800066240103903500f6030351981f0707510501940c0c0b50003624200c00780790903074403c2c042880d005104040c22604c0d504000c2103d40c80c44e0b00c0b407503100705644003283c4e041046014482d409449075050303580000c0302d010003000c01e0040c6180760441c80d101d5950001c10000c0810400a0550000003a01c005e11915490a55a5403500c0b19590070783c461400001d0f400d03100d0840000389a5003000250003124120f021205104522942141c200c0c0c0003158010041405084881490043c5500141c800c680c9010006581c01c80c1c14009408004212000c81d011a100ca2281500381410300956800c80380d0500180004145680c81800c95035003009020201540480020080480a460121440c0c005841088202194202507030300c1002c1c4c07600400490010700ba18241c0025400480d005590040f040300e00f00362144070301c00c1040c1d102a001030310b150348800003100414400e001000c828451034548051215 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 438702814 1250 438701564 438701567
    0x203100608010b09030303060f01090302120a2102030313030318080711030a17071b030f120203030105030c06071a100906090b06030103110d051c0801142b02090f07 72
    0x7403058011245681041c0035841c250780b13000069a40043c0b045515542444600004036034203e0320b030388040d40c00001d80151481d00300000c21010100f600903034640c070030104188a1a0b03034011040590400690040001030741010040c104403032000d11034600032a502005a00300783c0c0c0d6000601080d075245600243e11410050840e01c6500410340540c00b0300640b00564072101740c190090225160001c100044d001c0410041e09840c0780003204800c051002c0d2500c034181114209212103089480d412140b0240114500000035a4102c0b00300a0040c44001c08080912400e900000c4003211800141418640c81d0017004101c1441040c070109106407c1c0d24041c0003e054681d207a000101e0b00d803070284d0040003904d840b403c0b01c0c190ba40018070303d003014003008042003d0404c0883c01801a014142864078400d0518440785031946941e07443c610385981340d640c0318252140c40c079002a4041601302400c15058141c04003240103040880c800390952070390303401040c886002101c0034200050480100001075 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 438704064 1250 438702814 438702827
    0x204110c03040617061005070807080a080613140c0a2024060d060e0a020d060609060501021c32040e0a0b090c0915040e010e160207091e02031006 64
    0x4d00c0c000c007800c007908040000c98500c00703c0d0300e0400104030000800344240700d444002c58000381c2e4054001544c2e003c1003140140807440030f480780c610616811140200c02403050080360002003007040b400c000d607224a80030751100d50160102c8400d00032850715540003850a2002d044075a641780018104043c1c91403025502e000c41046940e032048070035070501800d6180c00700c0d001c0703d0a034860170020b207020741c00000d0341c900340034403200039442101c809250342006801e40000c0700301e445880b0103200b42500c0d0070069031500b000590900d5070403201242050701034031410300d01000080046851092049000040d02d4007001e03030341d28107581d950018007045081c028400c0030f5400b544542c0104811141c401c00180340040182890300d11040100399a03c0c0f56803121441c454561400038810340d181c1ea100400703006040f003449072100846090b80020660f2000030034200140c8060703800707040d0b083e080c050118014402e0b058107c1140000480100705030107207100a502917059421214085880c040d001040e0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 438705314 1250 438704064 438704087
    0x20a0e09010e070b19170a0906150b0f0a090308030109060810050c07110102070b070b1602150109090503040f0603052a0703080a110a050304030e0f18040204110c030406 74
    0x994005034040140c801000165418098250090021010f0342c280864001c003c01e0075906d001c401e0902400141083c3d41e02c100b21261140b8030074003080c8101100e6840c000c10301e06c54034461440400c000400c00400100500891150341080c1c0b46960f12500c52440340c3d04240c11825000342d48500900452008010070380b15000d0b48441440146441d00541c03c003805401e50041c82e440b60140724a503660300910000c80682404005541c4070342160800795134060307090f03803070a01d81626105003903842440443c0800c1c900e803902802050a900e070004040c0140070720306040e02e00d80800e010102d051760708050321000402140d0380208a82c14004407400c1481000c41118417000711803001500d03d0007140701a02c6901d134041c01c04811035540d04c03a030b800190030098407200003044005040b0031242e402c0740c060360151f0b0080d030f40c1c219502ca1750003d00040f41d04004115034043e00251495400d0700070762a0075a44a031010704049420480000f540300f43e900004008078580c0c101090602c00b581d030182c0107401 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 438706564 1250 438705314 438705341
    0x50103050f160510111507050d050903030106170403110d051902150a0f0603051e12030609011a12070914030714211c08090303190b0a03020a0e0901 65
    0x40c5180200041218044d401c103441400200d00b85018114820b02c1a1281d0826090788001d5078030b02807000620a0b8848600ca4a04d00d152801264440c000041aa0705030350442d02c94000500b120207170032900510082c400c404024595200658035081440b036140c0003020740e25016144c00c032942900d000c1a02c000342c50b008647c40481207204011006071140c0d04406045000141c0058541292021340883d0308003030500e00c02c40503180c0c03035040c65006d03a10b410780c85841503d02c09076120b4103000183c4400c0d0381c200d50029611005024146800c2c200b007003071426214070103140008a10580e02d4500d0b04482150110718001c0e41004900c1904840c030001d024100d005d429081e081c60010102c46515032001400341c03030180c0d03490b80085c0324a01e5a00700c42000340111035543d04e0441d42d180c0d149110070f20010008030742001203426181c0000699000c0c480c0c0825609070150b0071804000200400016241d10440c02030f00000940c0b140d00b41c4c00050141519221001c2c946071101d1400d44203c89808035 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 438707814 1250 438706564 438706603
    0x903061404031403070c2312180415030618060506010c03120b06090a080c130903020a030c061b0309060c020c030a1101170a020910110a02060d060306050103050f 71
    0x800a82d03c110784003a03025410706155203d4880460840310110000c600500018400e150b00b031000340c061900c0f0503800c0c01e410440d40312340f454490010081c0180805441103c01680311109289400c0c1c1120907035042c080f02501c5050780e42d0f03e401060710102c0716409500250700395428240141805019800359080c00d08039210b0183d5500204108240810f0140309641d90044011a5460008444003070000510321044207450340101c1e51204400d0048901c00c001c0103544441e1480c04d40a030307150301740e0150040e204444030394400340c54a444080003220b5080c3c2d02d107140c00403c40202c111040d410038a5900013071a2800b8501501107035002c124080565011078070090960340e00049100055030310050f4008070841850058032480780c2e8140c6080c0101055040000c100100d6001d030050400803508000d07021603200042ea9095400030b10802e441e04812140c1c00981000001441921009000040c0c1350782d594440e602150740a80013101c076500401c01444500d00204001c5082469481211 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 438709064 1250 438707814 438707821
    0x209131b050f1c0905010c18142206090c030903021009080301030212120406031b090e070e01090b040e071d010f030e0c04050c0c011415010c02030313030309030614 72
    0x1d0b04030b000f600e0f48045224941602581d500301e0036088011340d43c3c2e105009000a032521800030380b00b60741c142c84010b03071104000b1001614049500703030b0b02e4480d40080c0095911098641047c4c80e82148000e0100702140c8980b03000401e14110702c035610220040c2d03070780012418054a0002c2c1000c81d0021980782e03140c100443c01f070204145804813811294100d4042101d0003004100b5801c05e050b0f620b607040f500e907002c9000500ca5405030440030b01c3c1501c401d08080d400d080d00b4401c7d1603542c0305004213641c0c00e181000051a09000c2d50314000314480504004500c43d549503c1c4016552140e041481c0c40660306050003407d98004681c4040715045803040c00c0712a80b207100003070038441080418010141c070340c921301110040501104c45201c038040d00c20f1006240024003901c40ea03000b6440c0d00c50359072030500d1032a03664002249003405581c0444c11480490018401125000b00051090740c0c0340c001080b0174412101c107580c01c1c0004520a4881e0900141b650804d030086610401c141c4007100e40f4036041 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 438710314 1250 438709064 438709087
    0xc080105070e0d02060a1112040306051918110a03050a0c150207030816060902060a1d041a0d1a010602010b03010c0c150e120408100615020a030c060209131b05 70
    0x15282000d500d1f28003401481034184840d450008040410b0441990000300403040c091140c00c50f503c1188181a403e02032102090001c041310901c1c1c410701107200d250390300200010002c3c1003079900d400005200a00ea56103e455090400d10307000d004480381c070411001002456071626151650759100d001500070340e451601c1d420003900c21819080e02c0718211a80120801203541d02210203a0f0300074004545456a80c02c01524104c8015620380140984240142c86880d050145101180544544e5101e00140c0303014484825086142150b09800700c00c881310fa40080541031500800322980007003002da02d1403080c9801c5480c071900c0e10040102d10324201d00458000c10b140c0200c0c41ca80d00c80065091035000c981410002c1d4040080100080001c1c001034070301001408a0b20400c1d801810010382d556848080650701408020101507040a400100803d0042d41820f91203030164130003500e000e41e41000a03284100e10030319084d12a1382d40041d890303210500d04045207840ca540c180746180c580c56052 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 438711564 1250 438710314 438710317
    0x90c05150c010507020d321903060506040503070303051e21010b0a08010501200d17010e0f040b041a0f16080108210d02031e0a0b1003020c01090c080105070e0d0206 72
    0x50801c03987c0c80c4011000b011800400605a401e40b1004840d40700c00746400100340c1001c5c00c3c002c8070006800d10300b002c04c5600d428030071101201c00040040450514680d010b03034094118600340500d092041e000d50224469000090444518403012100d04140030307503c50b07801c000182c020b6560500c0900001560b2508030300c0c1c0c541900c0c02405e00a649036000c8030409040c04411042808600409000c40303181c54003c0400c003074418182403203424136038a0f840002e071850021580c1c40381c80101100880e011800c01013851350424080c000001c0f00f03140308003401600740025210a000c425030b0034104824120341083d0341482c50007601d82940154500a0000d80c1c91883c44500f900b8080d03018041030b40901224204c80c07120501c00303400c0d5100e18020354038a01e8440020400a03040102000054014090303214080240f1001460410007a6240c8002ca0081d0800d111244542d0b5942c06541c01190450000500400c0d074800017044524040d840102284000b10005001d18410403405005036074400 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 438712814 1250 438711564 438711587
    0x60901021602090c09030f011e0b030715050d290130020705060a0606030b060f040e060f0d11010e0a0501020712030215160206150d06090c05150c010507020d 69
    0x141c0c511480c1d1110300b0881306038802c0403038065040c460071080500c90103040d08240703030055001000e5680201d10100305d0090f180807100c62585900400707001d0048a00d03e0000c0400245c052074a0f0303003003c2c10030107403404941029016103542c22038003010108048101c2407640f1213520038a041c2c0061007462684c0400150450742d60a10001c14a40f0004010403070790680c1c0b04160400d00303c03000c40c241089058020040d41c080c3c1b00019060201007111810004100c0310b0981690f441d49192600c0d00d500a40051000350950f68094403010150300207640c0c01070288141e5000d034140500e81c265030000900842c05c12084240902c51440f0100300300d03038002c24110300711039008030307504100c8009180c224203240455003101c201d031114405100050300c06001d41ca0743c2a10503021559140c48000002e80c5105128000e25800041e140c4881d001822503080000300521507a08131340381e40d885400040f20341c0f000341c192100008000c59440081c0e40240a425006011800580f0b440e04441c10010a80000c04 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 438714064 1250 438712814 438712819
    0x3030402090a060509042a0f030209060d08040e07020a08030403080a1b02071802130609080f01021303020d05070308030a14130503030c0703141917092107020d0803040203060901021602 81
    0x10f0b1a00c0b07901c1304551f400c0e00700f02540c040d01820003c2d00c8400400c400f030403500050303010b220082c0c0060b40c0e0b401d05015040c0165005455941003a1401d06044241040204a002140903281861000500240141d4061442529035041c01c0c41c0c2501042d084420543c1504000403100281310641900490443c061780c406028100c400c983c0c418004010b8400d603940903022982802000801d154440c0d025015500703014160340074909425030341c5080c0d0007507072880725030070300340ca6400c04c01481d0010010300d0a6205100740c445441e500c1c0c4620210b60001c4a00e40fa0343d41d140c100c2e003294409410585c3e640844015100b40c1d00d0000e61721072950b207000c003c00a800c2500c0004003a0203150050782c90843c400b102c80f21a558a101107407403003104031885048140818260032400d0391003600c611200307100b441d449004140d4040001e1403032035600303d0b0305490b0302d001030200080405601d543e241080840d0098030000d036a07080a01c1810301c1e009005002a40591040c8a800010381500061000c074030f404 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 438715314 1250 438714064 438714083
    0x10f06020c041116020f03030307030501170a020a060f11060903030114090405060604021c0504081209150a1109040609060f05060f1218011b080709050a17031b03030402090a06050904 80
    0x451000c41e8401c6c5030341c640c071a031510000c010446100e034190800b034142c8520341401100d1142030903089070788486005009610201c41141440800d01c500c13403000e940c903418681031940164507104641410030949540c0d850342c00010040c444001d800d1604200c0110988060806103041c0c1c86807922640043d00c1c00c0d1189400240b40c0d15903a2010140301d1003c125070a040145e800c0c207240ca122564414a21180e00c0680000001e0340c0500100300600840002e030b58410083d541d03810182d0041640e00c50840d81d00105101e544280c3d1240d03c1180f015041e001e200040082c2454041042c130781003584030512688041000400d280039000a446141d901d00e2541ca1168484000220b80401c0b085034642c01c0b580b900030b040208103507440014407012038a0315090099115182e0480303c81d080d07401070640140407100100541b4014100096280e207501041d01e080942001e07041d54030f49941400c3d2072a90b400801400290f1030300885090308070201100820210b032401000c651120401403000d80729518 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 438716564 1250 438715314 438715357
    0xf03040e100506030f010303090e04020102030d1104080a0b010314010507050708090f060d02031f270e0f10060e04020a0314070b04091e0b03190f0b010f06020c0411 72
    0x2404811005800014403c545916140703a889464030005d100c140c00095886500040340402104070601803501a8080c51070407e002c0403071005080340103c3d00c4140d002c2080002003070481403121560715403040404d400d842d451410020740250f040c201d1009140d00d05024050300c160403100f01c400d900d40c00003101d92101c0741000003491170380d0131424164000a000554004050140c0e0003148030340c591341204c0440c401256100d0181d51018011720b80801404100031074800078400c41c10b040701c9050480450515456003405050410141a04900d5030001c0d110712900d00c01c902601c1c0242c80d090110407101c1c90a0b4000640201062002816448840b86e450b00e0b9810144121070240172101051580d81e03030380301400c00080c401c00c0700760343c03400070024000c0d842541907000780c50300c92a00400500c00340d84480413450f020020310711b08494100004659200203002004000c0c001d200340300c0c040039024902000a03050a44120010348140c2c640407488800c0455141941c204030383c55543c1d0100c2c02c5 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 438717814 1250 438716564 438716581
    0x1150c0f0b131e03200a050d020a020102060109110f0309150c0408010b0103140c0a020a06090b0601083607080102040e0a38010e0d0308180f03040e 65
    0x3040860050314194100041060015040d0641c0038480e01c6000561000c420680c24400b04200c8400004e0025800224100344911402481c46070b2030360610989069003260b5613500c0c607020b034008400d030150f000702002c11705542e01444030900411160300c0910052811507848405880351b18030a0405802c040003054016a0030400c0301104003010741e003c40981440c0242c04000d0b0001c0c4100c0038550301300390903595513500c6070250726811180d1030088056501d914010b91048d4000b0008007045202d14442e010110701c1e903021b80d00c0c02078015000001d0b141403240004040c054005c104440e03090007035245415400e220480b84d1075044002000c840b4010720240a60b00f00b1040741e001e8941c2c1c2d030005ca40492451485219a402241c1d81c44003080041c5008404d036913001600c83c01141180310400c0e4550000c0c2601e51101c0c0203040501d4045100030283c0001185a6409401600051581000c000c58101d0244612292824480041c145604604a01c55481c4070380c1c0616115a1190804614401c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 438719064 1250 438717814 438717833
    0xd0f060f05030f070614090d050c100f050910030b0307030321051603241d070216091815020a0e09060a05040e0a02100f0e0d0c0b13050a12030e03030301150c 69
    0x1448002d1402388140c17031500b0055502c103090480d1906c2440c100050502090091401810070f600544595050562400405c00e0181c48110b0310710a140e143e150110341e659081c00317080d02a52281d110250841505200c1c540c6e0400104842e0385c0c2c1d02c0c0703041c040c400903079a00f994007000341655141c0031444141603a01c80100c2c0c20b00029064034103100900109036641c201e00000340501000520b5501070b0703100081280e0360003a02111001c81d07140440140444540d981083c40c0500742c4035505500003415607218160300440750b1241584540c04070b83d0f80c410680c0628410016034080380d04407014241080015400c09042c41554480c03546c401d01c1d01361410040c072002510b150024801208140014400b80091412002e007000040c580b407120340d454907200013a1011290421001c410040c107050030941d099006a83e00c160301405000c0c00201965200d011101034000300f81c041c05c03a00c686180c0074121144103241c85220b600103000502c04800d60b001d031564006610729043e0240b0b00542401042d0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 438720314 1250 438719064 438719077
    0x50301090b04110415021c1b17070804090c0f080c130308191403070207170f012a111b0d05030a0804300e01050d0f060f05030f070614 59
    0x10700074085000160382e2a158017a8440c1c0700981c003543ca210312009007001e0700e68000800400400e1a40302d041c0a04482c0b6445400d885120300d0092050040c2e00380f40c60030581000008490500000070284607000340c60041110080d414242103c802c04400d03005400703a1340040c80110411000f0560860703020450a4903c01950094509581c03141155544012445201039620114804815900100121070206c0384540c00c00d40c040c0c45c206003000c6202a009807002000b206070700c00c0c14114407a014083c80303203c001c0308504100c40300d04160742d180444600100d204610a0090074001502c41c040042840302c0c90020b15400c01c00818101030000301d010b404c1e481d02504602c4007003581040c1c01e8100000d9030281e805505a8062203d5101110320b80c09410000fa10041000c1c840c0b40c640305004441101010314141009424107403d40c03400300172902540002422103454510802001d1943c3e0304202c040d00781035000d0003441c08007402c07050340c03018031b4480c580401001c415004520184981a95807 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 438721564 1250 438720314 438720341
    0x30a0e040e031e03010503010507080c030606090a1e06081005030307110d0807050a03020c0405070f110c0d0c18020a02031801030f0c0f02060708060a0b0c0a0b131a0601050301090b04 80
    0x4443c06884051078054109000300c60180d0300e080040b03041640105c065910648150941c40d28540c2e0740c0d0180103580e084811043d8000c9500440400c100756501900c0c45e0060303025604c10101c910f0a80b0040082c1409000c0381c03180400c0a1043c00603440c080221541c05800241803880c4800c004080307012070700d03071040140c0704080c040303078900401c0804210228814069400c0740c110442490802c4101c3c3c20a0b0380d21008034a2005562a5140c00748504030740007403e80c0241e5480e89270420215241005844d022034403222240424407481041c0580800007005203603086003442004503010b50740f8400d440b0003900c818400f0195202e02ea01c290818080c840c10b80805001144804002800b04549031052001601903080060b1801d48101c0e50305218500007000720b14918903100072000705900c90003003c150f9000d4107208002281035083c60a00030a0010072441c0c4000071030810702c0540e6004843c1d882c491040d03106004060380c0c00340580c0d05540141c0030000b0700565107000540102000c3e402c2c0380 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 438722814 1250 438721564 438721597
    0x1c050702070303180501050403060c03060803192706180f09270c06051c02070c08060f150402030a181101030b030105040210031d01060323030a0e040e03 67
    0x15850380441c201048910903102c140030880d9608128410742068080c4500249040c4010000304009401140691400e03080011343c8940b1140282c3c00c6501001515200b01d40c0d0407000400103038040c0820605012900614101d0390b29201801c0720002c0a1055008006070341e5007907a000040207500340020150320001c010034030343e202c01c0c580142250401e00d101d050084409010b51003580005546580d520845001c8001e0411a003034400d600300072401002003840c005801b4070103600d84002c0540078000d1406403045458007407060319000300204150050550034040c00400c1c04454026006100c0c01c440160701c990390350800390001c0c00003880382d4030b100041d1804c3c14188101417407411103000c400e9805000707010b01e0400f40f50a0354425640250000796000000c1c03421407296000c2c3c480e28040c1003607210048a0f0004550a4a13125003040e5908401d051845c02880741d0340c44001e003001d400720f024500701041107101510fa050b11070500c500964450303003002c0185601348201c0f41e418900c0319a50 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 438724064 1250 438722814 438722821
    0x1a010f17040f03031a0f0907050409291008222405010510021b1207031a06090103050615060d0f0e120427140a1509050c0702061c05 58
    0x1102c4945881005601203490316441c0102d40001c1403580122500240a015803000800c0a009a0490091254080090038003022490b500b0038003401c03c0c50460b0300803000303218040003078128003414440c00e050f10980b014580b000b503803074000c1c4485511400c480d401d01c0c64074640074000350f11004034100052084843c00d1981046e00c00105103140303824220340007008203a032500103000c0703a524034018803000b603072000c170f2800380f21403152003400c07000c4d8000740214000c224800c0c04c00b890700c41950030483d0340e00c00c0040303248161840003980d140d00c404211005c0007294517584842d500c54030003070b001480600352041500700c079403039038801c03501c0b10b1400c1c0c42d040021160002c03040009202110700c01c030302c9002e40d900c903103419451542a82d054420004000703600441140e4284640f6580f041d111588903200c82d26640586143e11100c1e1092345c0402c0045500400500d030344941340d2490300312440940c582018000401a06000d0fa002c00342d0603611140d0302c4810740e010801c40d010303005503d03041504040c01c1 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 438725314 1250 438724064 438724073
    0x70501110c01091a010b12130c030f060c0804081621020c0a121a0703061508070e040e070b0f310605040e0406020d14040c050a0602011a010f1704 64
    0x750b00c03d401802565010320900c045013103441020b01c192100d08206019203408410b0b503102180d040001d0120004000c40f43e55142d01c5466440d80c8180c8006401c402d030181400020b0090007071003541803070a40c030940750954a811150162121414071300034403408040402903010101198814080c801000380c80c2400710007035070b5030410317014540520011800000c000d40d142061541e8150701c0701d400040c94280c40341d81b44041c94002d080c101007580f00d100000d107158101e224100c1d06803a941d1180b501c0c0c0740003000035000c0e282124a83e8000d41c680861400314000114524003500e10104c1d50b00c0d61444202d1041038203000380541801009003000703800c44000768180d81000392100365448492496aa01c809803842d0107184918000d2004040000b4006509540241501c2c0c204c03000014510f8071854204c844a242254200c0d207103000f000e001d01142c0391210142004100c00c0c030080c818240c5d20700748100501306043d0414107100100c4000040f0350300030300300007460340c0081c1c04200307051405081 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 438726564 1250 438725314 438725321
    0x30f09111201020c0c0405060102150405010b0a050303131505070515150d03140904060b1911030403020d0f050f0a060525020606010f03020903030d0b091003020a0b070501110c01 78
    0x340e601c100c0c15078440900c40c80d018000c1c0d6100b5001d1201508840f005001444050100109440d04502900820b00841040400c20328000d0307005500004042d00440140024244950001442940180700500c2040d02c03409490096990304150720a6420150500355103500818034010f0a900400311440780041445045920400d80c03c900c0489444030f020501109042c0040041e0009403130504100a11400740024400180d010700700080d01e9036120940703515030b080344042d4108001021200c0d448103038800c424103180e03815000510314140c5544c2c0050403120700000000c02d0b0300754044010040c401e00744502011282e8410582c0c5510410b80341000007007100f1910045a44d08084107e40000340074007945024200c641c00420054480a00650740303c01001440001c00d80c0811002225460620151060050000012458100301d001300129460700900008211655840801c003503650340c00710004554015245545e2520241440c034098502c6032021b032004200040d20b540800c40540c07 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 438727814 1250 438726564 438726593
    0x607320a03170708041a190c020d020d080123060c070b13090204030201092303120706111e0c010b220b040b0f01181701050f0901060312030507030f09 66
    0x100b504000d5507070740c2002c3d00c0000c415540503054081c200c85c01c03441020720000d01c580141d0402424000c00e40d144904034140ea041c00d03685401030b040106243c550640401c221110b4244c541046046503060100c4c1c5050300c8880905c0c10b106002a007003a20468543c0d4080f1200c0c65a918140c03045140c503140e010b4a0b6030303c040e030101d0031902c030040c0c0001c01c5145442a2800d682d070594a860390b1030319000d0007544111101c40c0184040c08101c86070116540c0411a02d10b187ea0044541521100942080b504803140d0f0380d0042645d203800c01644000803020b0300c00e04c105060520301540c44420001e2420300511205151a801c5264172080c6880988600c8011410180c000001c0c00000c0070703501440b09035480654080d40012170045407a800e507018003030424a0420481c03c2011a0b540c0c2c410004100d001c1c2417031000246d54034010f000f9001c4015128580c0f107010720000303010081c5903988901d030307000141502904140e512400301740500e201e03811110030040b0801c0d0901164029081100c3c2c7c501d20b44 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 438729064 1250 438727814 438727847
    0x20606420405091f140f0301060806090d11070611030d0507200c0a060809120d140105010f080601051b06150a060329030a080c0f07050607320a03 64
    0x100103110205038040e8500a0703944c1000c251401450082d1881030b0814011010794091044109a1304d1500c3c03d00c201001091090000c200c5070405040080c240003110100104001c014007030511001e0002801c1c408807110380c40c040503e0048011b0907800c50141d07031f500001d440c1c00e10007403086c02c560110400124098280410390741040d42d039000c0e5600c40141e0a5960450b212000c1002954000c00159621080c0c0b5003d5031381e4024803505d91039150740700440c040f1205030703981c060083c040140c07004640074281c2824104030b100c59031413019040944c02001103040000004643e28a0ac0240e024609805c481004450150421380106144c1c6c0703e00d084e02c41c4c000c03590080e0015041e8800d008004041022480098050440c100c18207100b11510820542502c1868481000100b000008144030b001510142a07809200ca0186080074141e502580c03140c0d100b0700109007c6081c0240300010302000d400700400600c4c44000c1c686100c112901003240d135010701c0c080c0b00305141d08900400c0d251441d0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 438730314 1250 438729064 438729079
    0x50d0216050d03081902040b130e100b04120602070f05240601050a1202160b0411061e07140304060504030b1014013006031101020606420405 62
    0x140c009202c9207845403280640010140700c040380c211101480c00300195600d0000251a107529000700001c03030740c860034a40c611410800c00c10050014058082a0000d500842c0349070f07010f2500640c0860b50240c1c2c01a642d03803401c181c5203403082007115030403603800590112140c1c0403400141070a03500d80b4040040300c081e07000b07804404806081e00050303051184005855590900042500485000c0c00d05c40100d030700c2545c2000764110401040b4038540007580315080b8001145000c1c81c0400340c4024000301540503400512582c642d0644ca802110801c0400b200025203510036801c00708100c682d40550858036010018004c80c2c1d150b805001001528000c41e1800c810740c0300c866580c59159424810702600011054005020790300c615000440a010300c98484003151581250102039440c0c110300c1e60390301c0c0d0341e100108200440124000b21509090000c0c002c11301c0c110380400c0f0200309158542014400d4058420800840c0b02ca400c011000314503081801e50000c80c0341849554814018644166032 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 438731564 1250 438730314 438730319
    0x40c050c010b01090e13060906060b0c07060923030c040c020d030e06040c1a13091e0b01081f08010e0f06162c030a0b22020915040207050d0216 63
    0x1602c0294101d17007000341741d10029500d5840240c840030741c820080301e501361140c0722000410340700d01074440604810001d00740d86902c42480702d880c100003640107005014080d0800c00880100d0401c0a6410442c201381c18400d03424078000134140341004d9041680645800300d9112a540c2c00941408481002c0e101007010100c1140555502c1d482260010000d54901d08240188005045c490903001c580121340750804071000580700440705241c0100703107800d0f65202d404005c10390021000da40010800000c0003002ca100e40000e00c040c000401c10002c8090f00c40c5070700d000d0319a1201800c004e0000e14000c2014000b0721007680d45074841507021840a100340d202044483c0ba0b00100541e40d81d4550b2504850441248500032651711610605d8a055020b85241c00c031548050080f003200503c81d000402185ca0220f0405101100114988142d1000e801d05980140c481c07950480e04103c2180641e4050304040300083c01a21410758000c207036028180017013080a400042d0750b0301a075480244610f00c1078 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 438732814 1250 438731564 438731567
    0x601050a140f040c030212161719090302070f0603090515010828020a060206070f0f020a03030207111503010603050112030e0405090f010501262407090302040c050c010b01 75
    0x10004a16540e0000d00b0032501c64961419a001032140d912500f009030410b100c10609461f0b88008907101290041c80c0b80e0708004841e0701804c400302d680c440c05480d0b140c84c2029028000d01a800350300b47d8000e903988080c0d120600d40200035400044c02c010342c80100300d51b21000010701801c041c030f00440d82846a210702c408110f6880e0b80e913505070f68122005108aa0000d02d0121092240ca001e1806a485080d0f031000541c0b9042070319400780200c0c0c0c000300a581003001d0001c1200e4801030b4440b003000241054540155030201e05100850703050710703003d40c6800f0700d4142104040010300d4803d82c03118800f02c660381490318042c0594100c4819407000c21080e07036654966203440e02c00141c018001707101c0042c140550701d020b500031130b0810400c004880858900d4200c440c2100d100303800c0f0041805c0c8000120036031000380c9840f40110780240002d09212401d44070700710000381000285580040c0d0303580001d0a00c0344222803c00080d034000304140240007084802420582c0f00c80c0800b0001d5007889445041c55 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 438734064 1250 438732814 438732839
    0x100305010f06170d0e01051e04170c0102010b100f121803140f070b09031b160b040f032a06210e060601050a0e270f010b0a0c02011407050601050a 64
    0x205281c5c0c88001c40c4510a400450b1a075002d10b000702c80c0d0450307003500b011200c081f400141c8040d20701d1030508a450702521035020701c0d24010643c0c0a046a042c0081c0e0111a1660500c1d0b481c200c000d0305000240e0110800c0a45010b004100440b0081c1d2a102c0d03441e60081ca100c18050b09280a07480d003192a200c25078000000c0e1042c0120001c0142d03041100200241d05a0a6545c0c400001c01c00d170b9040c020030800d5002400d1801101111990001e0281003120280c03865003401010310781c8070503140c2858440302912201c1e4601c0040c004d2104c040d01c180d074001810402000341c3c03d001007102d901c15203500340640310070424100030302110103050a41400100c1c511807d050700340c1c4e03140113001c9030769640c00445480d402040c0c00c204100001048030b00c40d481d83e200d2241c3c01200700d81220420355a038124098070507001811900d81d201240b004200070101c52086070110203052910003000c003601c0c0010790f404c03908042080c09200000441d03105004001c40c08070306a520490307001d90b40b140d66020b4120f01 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 438735314 1250 438734064 438734083
    0x30708070f0207031112030a030e011b02100903030b091e070c020105090d020a1805061002010c12150b2805190c060f06060804110102030301060e09100305010f0617 72
    0x503074048481400450024140b501154000401a00c1003480d0b1980c031b603085070442c00306480400d4480a114084110a0290a400b290304007040300e4001da030341c84002c1d501c01160b41f500005a82d6019120245031007604500d06003000034042101509000e003240d4120080b02c62034000f0301c0c40020128000910600000302d80b250160b448504102c2c0c1e0000304107580ca003040e8200e0f401122501d000030711035284c0034514030b80101000300040c2e80c07510300107001c803006d111b02c44c602c11a40f400d00cc1c1030300030f6046060491904424900052068007041007903000c5055604014108100130a03400c000b04c0e41e4041c0f0307002090b941185404010031712102901c2c117000759074500c00140095141c8448503882000006001801040c003c03503801c03c1024080119881f07038008000260300031041200b48200440b0f18481342d5000c0c4000c0d032440d1b00d0b000c001007a05405141c80d51145411202042200e410303624003002a40d0010300800c000d840039540302e40205003510400c023039115294079102805d40d02140c00d840 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 438736564 1250 438735314 438735317
    0x16031802011d0405010603090308010e060a0b030903070f0605180c210703080d0c080c19030b06190e0111010e030414030304170601061b15020f0705060c030708070f 72
    0x800400a80c01903a20341150107004a088200511040c9140d07102d0081d00c2c001c4c84030b41c800242c000400c0c05d0082201c4e038140c224550a08015050080d142c55403800441255019501b482c2c41c1c1d02c2d2040700604500c80d01c1000341c4003640040e036100c24000164009402108103100ca00d0181074410281c42d240d014656889170300c640311010281c282c1c00e608003104a01c040c108141c0e540c1c5034896844490f203800034000300681e9513031910180078103030f0440d02c0141c100e203440c6011418000100c0c080c101d0710041d20000301c00c1648503412000c898960000b6034000201ca0f01d154800e0b021a00740041608a00b0240180050358044210a5040d01881440f00c142d9101e4060352030700c2d00300004134040c01104152150148020080094040200f402080310550108040c080a502d002001040d410121000c09491a02c441120000034004a001e0310400d010800c0941c40d40f400211107060340c05402c40141290003440200b0400300b000d030780254854929078a5100c070395118824111a1540391007040390 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 438737814 1250 438736564 438736601
    0x6062d080f07021e01020a090b07080409020a031e0c1b08030a05040201020a170409061d06040b060f1c1b09140301060314011a0303160204150b121603 66
    0x94541800607600c5030b220b15580100c03148004d90300d800d0080c40e2190303c0d4004030f81c6d41c04038440c2002980681204028082c0c1c08510f414580541c80e880881c0c030440c450041d00550000c1c20350301c0f06000317402c03a00410100c64035842001500c44840e01c00340100000c100e00203000002d0b04160030540e4030102c0c6089800c1a000c0c2d09507540c8051000007010060300503419440355a038900000b5128001100c4804c2603c0e191a0b102d46c0780c07514010581d2207036080303482041900c9502d0080c00d0040303401d00354000011036000c6180c40100740071038100c0c41000b85030508802c0c001200803c3ca141034100812000c5040800c00198003c80020b1041108800e85480011848001080512003850340c4c0000034400800005d01ca90b52682d580001203501a5440780b286d440300441003040d45152840480c2d00d5040e0301441ca010840c074103843c0c41030303003d0100a1065940f50301b2025480e0b035404110000d040c1c00b000c0644d44400040c00620100004c542150000341c1300c1100c4800d80b4484e004411624032031704c004c00b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 438739064 1250 438737814 438737821
    0x1e010b0901030b10230f070c030506150d061d010e030702090a0b06030402090403140d0e1603051f0902040c2001020f07080703030906050c1905030114041104080106062d08 75
    0x70305841031040404810309005000806d00e540c90400107000041c460000075255902d146001e5080441c0100744072162034040388181c070b00d91911850711f10b6840c1c1c440b00000b6415200d0f41403103a007203030244000d244c9602e0700c0482e545a40d0b000008042881c000c4900d01550f40c4c9807040182951000303481d50f0b400810034004980182440446690014408e0510541801180014204c80e420580c03140c00c0080c0c8505a04ca8120310a0107030744c9007030030b0600c0164a81d50a6440c2c40341d0301d0425141e90b08405000c2a005079101d100d42e800a4100c1340d0041c4140000d10a002d4001c1004440c0b030074000c060311002e0200104c2c0d0030140b08442c40d114020414034200200342d01e41101e550001c0205070103040c1c594041c1c9000502510400d813080c04d015400d140c640004849501242d564582c5003014402e082006005150300e03040b4401c02da40c011100071404a041c9a00340600b07002d240c2c08050340f0740c00d1001c046001500240350740c40304c142402034107208011031200c44051300d4a0f546100301141400010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 438740314 1250 438739064 438739097
    0x1150e0a06080606150f040b0d020714161403070e040b0703050705161707050a050607030f1808031b0408030c1002181e0d08030f09060606121e010b0901030b10 70
    0x40c2c40c4186c00310b041b850900b42c0d1a110418580d200a081c030a80c16400600403042000211120140c1c00e5000000c1c01e10000d40039400c4008102d80c00f450012020392212103642d0341d000c1003000042d00d1568828146802c2c42d2070120700381c060030369024001c40e0901000814044c0320b28251120100070107001c03500d010007611603035414207000b03000301042c00c0c0070408078021606c100070001703040e4400c1008269501e48200c1c01000c1b1018040004686800d220b01c0301c11401c2e45908209602d508000403560383d0321000d0500c4201c025100e2000d55a44011900150810780800500b103901c1680341529400b9543c606044101c1c442d090750515941c0bc45038001d1498100002c1111000200ca20f40c008200d04403000034124802c4c006048903c401c00104120090500c118110340040900c00100380905000300003e08a008001c041c8640c4150480041c6400055a80c00c4510300b100ea070f4452043c0d611480c8040f9240d00c9000c0300c50109084c51080e46003400e000d001481001c03072555a041c8103040c0c0710700 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 438741564 1250 438740314 438740317
    0x9090c030c090604030339110607050f0a1a010e0703020a020a0c0b1c060f0e070306030209250206060f100302090a06091701050606070b040501150e0a0608060615 71
    0x1c40e00500c40c2402003080a44a003c028006140281c4580c40e02100d95040c0130340903154400107075209241c11182c00d850300b0a00340d03410000e9070301190100000c0c0740310b004120140a60a005070044c40bc2030300010314142c0200c2c0900d4401e014400d8150048a1400c00100e0042c0a20402501014840001d440b1030711a5001c0c020202e0340d44190307081c00c422030f203900701c0c0e102d0203400045070070b140021000a604840300c1c00204686159109000085c9000965500c00c04c0510039100701d102a01c0008902074030070351100000c1c590051490200342031500b6400f440303015074040d81019070b68036010f100005d4000200c0714400c9a00500014100b03e007403040c000f03010714914807030042c03680a0068a01a0740d4a140e01e9024101030343d07484030300303600c3c3c541001181d10340380c212407680f64902814820540c6a540455540c0c6801103012561034035146046401040883c0c0b005c0d401d1a1003100c0840c25109030000c144c012403030380741d041c0071f01900c44107442e072540700c20344409a1108507289800c40440c101070 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 438742814 1250 438741564 438741571
    0xd020712080909070203041e0308030c0901090801090b010311010309170a1709100b150405060708040801050a0c120c020613060b060703030209090c0403030806090406110c0606120309090c03 83
    0x281e00d0b03081c00ba82c0700200d900d10100ba145000980c0001c1414000001c10591104203299401c80401081d403540c3c803040b01521001d4404041c1d01000203020440b07074001d40c00103000301a520020132600403030f403c260420010030b0008480320a0801d00c1c1c480d4640c8a0300402c00f8040d00314110500703c400c3e8008001d400d5001240b100c091100203495940840f00480c0907138401c01484018040d240003062a01c002c561002040c2031180c1000145601d0f00041c0b4010f40c4c00340c0e0010f030f808a541e0105400c04001900640d03001c014150700341402c1041040c040d4204c004010113589410300720060740c082c10400d4a40002d101001a4006800903014115161410300c101e80030385400a070402101e03011502d594810801503000c2500002c4800c5242803009880764080c20038a045c03401c05007140d40080c218a0040e081c00c0c4144403200114090050390307840500e00d80406004155607243c0c60141c680c89a0b03080340e08130311840d901004c0340d200c0c540c007108075250114001d041603070590722200d02200340d40014 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 438744064 1250 438742814 438742823
    0x615040b030318090c030403050a08040201022e0f0c0c2301060611160f06050705010e06010609031505040803040f0309050a03030c05100c0212090105091801170d020712 74
    0x4920090320380d181480184201c1c46480d0005003540030301030a02060302005000411040d03c104104000b00e544a410740d2001209071800201e15251800104e241282c2015082704030b40044200d140000150310312031225820701a0300703000c409680d51078002210004500030021a55468020000030305005240c0342c4007040d000c510103840c820018880c02c480e12500441e000c10301c0c2141c0341d0781008041000001c0c0e51102003414105608114090415501d80e106035410710402150000c02c1000c01c1d081801d07019415002c940d003079a5241c80040c1280e64038031096039281c00ca80210382c0300208034040d080c45150410360803480d50b216603864920140040c1010743c1001411800030402e50b50301081c1c00d0055010760b4450f2848000ea0402a040200144c8048041c500c0d088076240305a801055003542c4400700704840762100940303001615103100d9000820f42c80408040c1d4881c0345201707211990f06a50301100428801242000d03940e603212210080140582d100400810a4002a85284d032045105 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 438745314 1250 438744064 438744071
    0x60a05030c04020f0d0c0c0516031101142809060c0b0606070c081002030f010909242a020606031b040b010e130501292514030702010e0a08061504 64
    0x1410340c0f174004c03100240303c500005a50030b41c03031009010040000920340c001d41c4036801002899603640d42d914901c2401e080e418424240c001003005d0b0000c00903a840e9a14118040d0b00840254031007021038040842810b0200348400808220a0700c95070032080401d034082070740510340d110700082000030782040100b192410280e000c007150700881071110b0505032400160160301c03414000e4501e88002d4058104a1056240004030300116280d440029407409038000b6950714030b00150910400303402400b18400e88295820030a980b540b006030200c05101941d03034203480094540d80100342d210565100e021440c0c40e155110b10784035280590008000140504110325201a1000410380b400076020020342d4203952040108401c65034a000d01c1c4094140c3c503500c1d0000c04440d50442152b000e204440c400488100c50400c004004074216200031581150740111800100c1c1c2c1181e42d02da000d090101d000030300351841c0708400d04000c000c0720241da00060180c1400c2d07455000d01d4640085021002d0342c416207 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 438746564 1250 438745314 438745327
    0x909020d05190201080a0c08060d020402040f060c02130b131509090803061008130b040215031812070305070212151f0e06030705210706030b09060a05030c04020f 71
    0x80c100702181d40c509030382c402c480b14040d85000250006600070104003406080507007007040254010030903640714008903000000e00505001180090050340c0181c0140c10b4011808070710f0307a401041603400355100b19803174031400b010b07041c0c3e070802e48440304000c940090409456000199558006409004116070b040c0591555050410103540c401d04042d0760142c400070038800e40e420058583d050400213400c1c80c442505200410645600415002804076000ca0010804642d00d008614007190380d400121501c905007d0701404d02d1681d4241b804580348511035013582001603580039270300c240b13070151540c0d420103881c0e40070b004a89400c1c4243c1d2105001c0c16020000810310610900d014142d41200903045010b01c0c500441445010b800029030004400c04100c120342c0d000441009864041c0d81204c040410202d00c1010110694060500d40c000e118010078460740c13551140300904011102c1290b903031070703000600c200049580076040d0990824108030b0b107141070503001820280a54101d8034030300700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 438747814 1250 438746564 438746573
    0x30703121101062c06060d020702060c03121006080403020606060d0e060115030c022b02150405010203060108130f200a0e010905061f0e0609120a1202070f0909020d 72
    0x84403601301c9484c00441070f00c00040b05008404d909407a00a00d0b14201c0d45042c0100065014000c1740c2d0303032844041c0c001580343d0854441c242903903c491185000c590b2111840048100b1000e4202e8580c48840102003000a01c0c034400c00ea401d0080340c02d43c010300000c1d245d030300c1444a1541b010b034503600c00c2503d6820b100300c0b485080100038000c0100019101e000d040c43c040c014107071542c600c00d680842d8070068040c1000c6164140e200c2c551036a480300800096078120059003071000007a421500f0f40e42d4001008184070040d00110300c69034099a44041e0f642d0b42741d2000301100484040030f0007280e0303500c0d0030400040e140050708040f00c0d401c0204039043c95007040011040051038100c0d0540014170b1780100300c160502d0051540281045500070b0001c1e1801e003181d003940070814100c00030412903005290b4291244000c0755480140500949540030380301d03604039543c04117800c0c00c56200d858490a02c1000f032000c20841300f41e0b0740410418107058a032610721000f81071416800d81e400126540d0080014 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 438749064 1250 438747814 438747821
    0x20103090f1a010801060602060c1305100302090f0604061707020106050a030f12030501080d05030402040f02040e070e090c041205121c150e0402090411030609010e1209030703121101 80
    0x1c03071084048500100da20140481d0007201a400344069a0509105000e9944c001c40c4003623002d00b0112425803610a8111000b820f070364a43d0182c2c1d04141e140f0a07045419506800030703c28141d065070345202c05580c9070188080ca1245104190000340c20416111041c002c010301d803030700140244000315442d521140080c1c0842300301d034000c481150300d4104c000100a001005102070034140c1c00c003000305614284445441d04c494a0010b400c10600000107400c660f61031307001890a4003200411900c039038071202c0300b90310b00a06503142c00100b44001d070407281030300c3c0c203580b5248505801c41d08941800c3c42d02019211440032002c0071905c0d4010703038541c404003929a1016001c05c03014601f2018408503202490822034110480607281d5140d6500103007c1102c07000002600154103551600a90355142482d507058140003811079818041d03a000d20880300030541010000800340f40c1525405030300240c55070700b1849103ca01d9500344e0040e00003080030403000d0040d009000c0d188d00788010502c181081d040e085 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 438750314 1250 438749064 438749093
    0x60a05120d0908070614070302100f0204031110050f0f04090203090d0f0e030d0e190303030606091707091d10051504050907050f0d08192d0c02010309 66
    0x5a40c441c1025541059021907034000508059001d0304015080c4280241501700404001200d8000021000b040510801000341038410300b0b0320804c000c410004048019510510041da55004c0040c445003262800c0c0e4049801c01003152652441c2c00720039482c001c96900701aa441c844800c2c03c0c04001641426400254811202c450203030904600d810409803851070f04800840810400c20361881c841d49001900d85810891030a02e0035407400c0c0000011100c0c81d2052400750480c6246030000201501a042041078171401c0d01c4410085071100c910f000c040c8106501c60620358400181003040c00030a5118410201e44100140841d40c0c03028211858a40406252034099550704104400c0709001800c001c00124102c4040c0641e0410103069650762045008a611400c0c0d841d689241e02c0d0f0711102454401070317018960903101d1006100c0310050807510090320010548440c8842c807820002101e090114038981800a0481a006022560f12600034400c0703061641d40c4600d0408905540b100c01c81 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 438751564 1250 438750314 438750349
    0x60203010509070c2a080d030e07080313230604030c050f2e02070906090209090c0c0d050a1803050105040215030601141608160c0807030b0a05060a05 66
    0xa80354544028022804001805141001a000341490004401600d004491000513941d480004034411070b4680c0011a94054117440c0702d400300c040986505904019100407001090300d200781d644000c2c5a8032441407040c801814440300d1024011402e6442c0f4000c00800000d40343c400c00c00040d40414041e0303000e0f82066500441c550710801491800c40d0301c200366000255040702ca000c01c10003461480d01d038030041042e40185501020403645e40b08102d00c800070b09042034240411a91065000020340c04101c846001d940c1003000102050340760412100c48029040c020f010004a00300c04603910f80202502c541003015445280b00702c110030a05d880080e502030310001481b07040c00d1041041c0822281038030390503600c0c00d004224690303802c12800c0b24002c014482c859583d0031005800a0005110600180600d01c04a031601e03040a00804501840b8461145866083c1d00e03805125998542c0f48070003000b01c00b008001488000b196040540c000d00040c00380c160302502d03440003948004001d460080d = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 438752814 1250 438751564 438751567
    0xf05071509150207051509040e0d030e0c19180603060c09061d090601050f0c010e0708150f06040c020f12090a090203041101050a0203070b010609030303050c0a0c140a02030a0602 78
    0x15040b00c42e200c0c0c0d1402001c0c00109000c0e8a030001003010b0510840380c0808040010451410540784c68200040024031041503840d0a0300c00700c8040c000700305600f804100380c443c0d0f180345035440c01c0c01d04c200003c0f49840003001e4001450404000c1080200c00440e02d01a61182c10000c00105c16026003141004161100742203030703080400080052140e4013070407865020000246016407681c0804503042082172030001d075501d84180030624948200100c800c041e40c0ba194100c08450004640a4207440050041e540b40c1c1c0b07190110444180c0f07041da541340851003084003207095880c1a0780042e1811002d801a030790705801c80c005031810f09030484001c0300074140c00100c10304c5500e080c00e110405401004011421810035840d0b003c18003a8140d01c050511000003101c1c580d107030007001902c1080340c0c404459403640d80c44410003400c0c03201d07038402200481e0500000ca003e90180c2001d40da84845980d44d0302d280401d00d5210b48900c0c1006e41e8169070240202c480400143e1010720546125034010080035 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 438754064 1250 438752814 438752819
    0x11040b0d1202060f240405060a050a0b070204050105030a0b0a1d01091101030b0111030706090f0b091f061203080703020c030c010506030d0c0512030405010209182e030f05071509 78
    0x100c54804c0001e1808401d5000b030f000c004445803500780000030001e4140d400040300e40d540004120300c50140e07000340d035115150040005803070344600010050030344281c40900c010b90f6079a0034144da40c1c1042c0340041ca01c40010000803010101a031061003070f1419004884015842d201110b03086515956098805041c8210710940c5560540074101480e4409c1c68045896481812003039203900904200600341902c41d02e100c410701100b0380720360801c1d81d04a41040c94500b00f03055a2070395003100a02281031104100149401060b407442400201c4a01d00e41003080c0c64803940c0c04442c030328402046901410f9080c04619440300082024041c80e064642c00084c150910900b09481d0810300a1100d041100d005000c8002480c0824082420a1071603030a0342c9a4682d441d2040c0079000c2d0040c2181c0011002000d45c0c0b8000c4000307062809100820702c1002401070f9409041d031101c1e208890000c1209029600300700242050545c00c1c01107009005503454140c640b00d0808007143c24100120005080300020b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 438755314 1250 438754064 438754081
    0x706020a0c05011d0a031d03150106090e0c0706022a0a052137080105090916060c02010203070b0412020607030b030d0f1211030a1811040b0d120206 65
    0x40a150000d111024040141365211056445c0d0700c00740010304004409420078606601ca100400c1b006034018180c60b81d03002e0510000302c116400f4400da03000a0100440003d40b6000250100c1c010049090580d141034115101e600180d401003000b85400798028007860f210f40ca001d04d1142c403080700107026100c00002400d006260481440513161004495011032500c15a00d10032115034000005c0342c90f55110a041189020000341c05095030b8034400c500d00042441d600144641c141d440407200c0303c1840d2600c9100540d40e12515031003640b203010b4080240302c5075028201e800249481403046a10300790040d1703a4410380203001d0364112400704440d604200d400350140240c6502c03c54500e0104621203011000030750360080e45584009000d640d240700c2100f00d118480b4030ba4480c022103000c0c0b1842940322060070240c0e10441d440f001042c41c241c19002d032506540580c0d0f010a400644140710038030701004220081c508444402d83c000070001d80c40c1d0010300480c00690310040c02d50094202458007080f03 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 438756564 1250 438755314 438755321
    0x1107140f010b010e030d1809020a0f033815070b040501140708040f0204110a0903031803030203030a0e0114090309190501170403030f0e0102090a090605130902060706020a0c0501 78
    0x2501c2d0b041c005004001c44441d100054403600d090390034076010000c0b080c1c41c0300b090340a0307a0a070413000c1070500024084a00c01d40200461044480c280d80412562150031242501c034070601800c8e21001841605108240c00341c000c200003480e80050a00b80084014070b0351180550000d981200d1045101d01000f007800004c1c8521020000301200521841c0fa101c00003d00140c0001c1008008401011b007400564845901001c400303130010803a01c2d6655030091002d4102002071000300c00084029844116582040301e24108803581a0000d50541d11524619005800c071030006241540d038070804100601110040345010b40b58010185560b0100c420a10401030401c4990b001d040004110411140c0d03440800d11244103044a24024591203d14080380608440740804006a044c038040c40f914000650040403810303411117a04440a580b444108240c0742144129907100310903002e4a070003d400340d00224190303880101403925025450f81e400c4100d07004003010900182c1d08022400c2080424130 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 438757814 1250 438756564 438756581
    0xd0e01060e01030f031209020a0914060a26010b030d091404020f0d090f0b28060e0403050d02090402040b04030203010c0903200102011d0609070e0c09041107140f01 72
    0x1c800340520341c10758030b500d8150507980c00b0040c200300e04040b100e540d9689a0b4005098a0f41c01801c00747c01039552403a44010304000c92121108209101c0400c903286081680c51085034843c80324803514a00c030782c00e070403014517070756090103095500c3e015003143d955818810f1266002e803e807541200b140c20525100c0c031616040004c5030140f0b10400151250306611007d0b00d03c1524144d2000c600c62159152103442c480e90038500404004001040c03014010b492140700140c0b18860315880981e015403c1c0c0002a41c8580c843c0c0c402c1108000007280200f88208010020011000750151900000102140403a405030b448221000400305040c021841c080c0180d141a24045c0f40003801a411034403080c881030700b0344501c03005011642e22580001e9001b0f400440c040c10000448191141803040502d46500c001c440110b900e000c0c0300404540e5034280f40082d0f001310107089506042901030380500c80104050180c10a40701000d116190000e400703034204400c0100910b000c1c1c01030280521003030f400d481515 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 438759064 1250 438757814 438757829
    0x60408011e0c05040504020f19020616081501141e03010f090509070e06030f0f0307020906011806050a0e0d030c1401020702090a0c030605061b060c0309030a1409060d0e0106 76
    0x50b450a005501405840541c1d030122001030380e6a061350f0b08583d151003a2800d8449107143c0a016022072500030807114850802450b0343d00c1c1710707140c00b0380c21140b4501c112908080000b41c0000804154403401100300d61182c0c54400500d4260b409440c1003066030003036001040104008018007500707440e41c0c1141c000301480d440c203010504000201e6515210306004d0360b5001003a0600045650354204100c40c0048002c070700340c1c0c2801901d46103440d1070f644903c1041c0d0182c0111000305050b5481000710140c659407036078035044002d040c41c00c122190b074803580c28041004001c0320710100e0b6650f03020300f00c4540c3c0d1003602d80c04241d4520380703010322218014003c3c01240d0b23481032002102584801d0525540601e01a20018202c50610f2043d03008140e00d801203600840b012030341003801c3c010180f000d907940350240300700c480903a40c00710112813a10048600134140e0b041400141e02446c0204540c0d8018961503c0d8103080c040c5150110b4801c4d000050039030b500d07e4613180e500e000c0b4182841084040c0c0b121 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 438760314 1250 438759064 438759071
    0x141201060f0c120c08090d08070c0b130312030b120d09090c140c0a0501020f070605090309060f096a0210180201030b011110090503040302060408011e 66
    0x107840e0088103008a00e50b0b0403d101345901c2a0013081100000c50722060300040150301d9000e1a81410511070300700e0070f030403140034001c2e6801095007000401030301c0c0d180030004036003d841d50a40e42c803000d0610548203a0420325880d800d85420640e594408102602c11a9004158051050f07030f00518041203030707200302d581910f020260404903070b11404041d44bd00c4101c1d42c0c00d40d58905000013610f003800c0e511000d082540301281c642007808110b4012300e0058081d079005d104645505d03502c6922803041c412650761000c8104141d102100c020710140a0280380248841c200c0315403995514610303c44d0b1071445007088460a991222681020540f9000d00c030a43c4e01c2c601c00d4180f080880c1c414036140e4000f40012100350401c200307224402c000c42c00c81d64600d500240211091300801d078800e0003030704030100d0101c1d09020250040f13501c240907500c0800d07039400c010080800300455650041c000c940d01074a00c1e010401c40030015844a00041004000300c0700001404102c1c208a541c02283d9107440780411807d = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 438761564 1250 438760314 438760337
    0x18050d1409090c071a0103120c1a090c0102281104020712020f1513020607082203020a050315010b03070207080610080f0f0304030b0c0409090605160903080301090c141201060f 77
    0x41c091082341e0701c403203035041240b02e1180341c0c10010184c0414845001060388a142007003200c00021900d00e0b5104020f07001c981800940c2c400d42000040f418291780f51a92001031648003042c2c0440c0460420394010301300514010f6142c40f00000502c0110441c80580d0043c2c0e45180384080801c400010035103c3c2d4441191802d00c028080000030788998044c0c85203402003080d034203101e810801c640103444070070484070340e810645541c40188801880141e10032031500e4400101414041740110036205545c034039400350382c24441405190741000e044d80301180300d0200045101d1204002e80340c000c0616a912103c2e152500a1007441c060220681c3da41680240c040c0c140a00300000c10740e400e032030b07100d9841320302c42e40c84028002070341c0a694000407400f818120000305000042c3c0c043d90144450f13405400410b0028202581c0e00c010501c802440d105042004004d040c041e6440b0b04a41302044c9000c40c1951121118000301b42c010101d01c0c400e11b8020801017100580221242640366131a0400701034070394 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 438762814 1250 438761564 438761573
    0xb0901080408090109050d050a020a0609270b060f0310050307060f0c020117040f1a0c2d1b06071803030e030a02091005030118050d1409090c071a0103 66
    0x15409030006182c440c01150001d2542c0c01000c00e84043c4c00041d14408584455007407165440440c040700340d021f80700c0541c02243d02480b038808102500d40305640c03601c910048030410040b182501d003070000c03150b981c0d09404025a447c3c0008014400300701440d0782d140d083c02c0300c40d082690a9640070314880d900200d41001203541000f141960b045960038600d80701d181c50b00050f40c18450b10000450000128420081008054108651054098800c0200c2d803006d0260650b40d00300180c4209259040a00044443c5441c51100e0321081000340c9040341e65101000380d000c025001480c4c590700e0344024040c6401625030801072958860ba180c648507119200104c0f1940c0d1000c080e000c0942000a10912102151020001c00d04c509030b0103006030609191120864005140c18003a507403180d4280a00c0c030701069144507049507029000805020026948802079401d2903a41032400054901032140040c2a59400d91891040d40f030b4240307582d0755030150300e4030203559101001045d4a540c1d0380d40050001c01c = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 438764064 1250 438762814 438762827
    0xe18010b19030803180114070806092a16081e0913050403051b01050702010c0c0209150118090203100617011a120109091406010b0306011d0612010f0b0901 68
    0x100d411103c8241c0e83d40b2106181c5400d0155a03c109240d9800c1c04445460010500c6c1f02c548200c00c1d55683c85101e4541004120705043c09561041c40006000ca038509034100d00d651031a807040d0028081490142d80c0e003800c40ca8504a04003d6841c210b0226a4144081104441884840200c0d241c03a00c1c00c2030150001e0702500d2800890b45000d503540c00004c04050040303040307899010415114400355000503401074060501120350f40010350030104000e4046c0d010f2200030009941c0108005202d5070355003032083c0e104803082c00507070400a40548000c2c8084c0d28020840c0a482c8440c00961342e842c0c501200d044441d81036106074204090380d010f80708a42c0c0091005030648440b0841c6103251070b003c00a401060040d1060203104081140c00040d0862241e40b002c0301141c450500c2403900b68600300da035070301c0301d809100d8140d5981040001803980d41c450840111203612141114819200d400049005034001d0318118100c0700310300005015040342440381c91700502c0d410310840d107000496000208038 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 438765314 1250 438764064 438764069
    0x10e03190c0606090213140d020612040501140a090b010506030115121e0906050916090513120e0f19090b060405180403030c1d01080604060e18010b19 66
    0x1001400368000c0c00300400c43c0c0041001300343d002015901c40060030744110418149204981356070040c80d669030094103100205501c03150700100901d007081c029401140380080c00410464085d50f0300c882080c0044514042c4502440c0090b400062420440c0390142c3c11800682049104540900040241410b0094441e00c041000d2410190085807420240e026003245000e9251000f081d01660403643e40742d030b100f9068140100c00901140d01c500c0b02203a01d81e00e0560100b81010403840d4144810703c11900801d40242e14024000722100a5882d0003640b2000e0310000000589032009021183c505420444510710048481c3d081c0d0b54004400c081000d00300780f2440403c0d40c0c496041100303a981c0c2005943c01000060719890307050740791180302e4421000c102c4044011901e03044000420074400c500208203ca070581c0d140406508010054a1007007004243d158006c0c0c0351040441d1003a042c0302c01601031510822034004029404060500791014400200d0046042802c01040300d00b071540407808 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 438766564 1250 438765314 438765317
    0x3041202070b0d0c110105240607020f10230a11120d0c02010b06161703040203031602060c0d0e0109050103020f031513020f07060506040203070c0803090f06041103010e0319 76
    0x400e03881c2d544080da8081d81c0b403000905903502e0b01c02008030700205c8c07043d9000100c582c503034400d21032084441041400d014941e0040c2d0044408048070b0010305018540071130450700350410254903200b0020b03032f401c112032010b6840780107070000c5140f03400743e80c0040d641c50380152a040a000c2010300c004a5410a02a221881102c16246c84140000a000b0351214184050103031501c0d6039556425034070003588041c58406c488031000701c64210404020401a2402158010059071515040c540400002140c2c0d40099a110800300402c01c5c44d4102044412042c181702c7d00c2d6442d1118140d07001608803140e5034403c6050500412400c5030501c0e0324011281e02640350206201d034602120049560118010804080e8602c0001c04150b4611088040c0c5461031184800740520f94914041c003003680030903150342c03020600b444011400a140b5401440e07000041100303e50b04040002031039403900c00c01b500c0c15903072884245082d0f8074900b007e0042c4a00d5040c802d00540c5800146024820b034004044071000 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 438767814 1250 438766564 438766571
    0x4020f0f1c0c1415040315110d0b0102070503150a0c090509042105070201020604170c0a0605010915050a030f150507020d020d0f1b020d0204060b03041202070b0d 71
    0x421981d4811807162150440358008080c0203403841c2820140c0c120340240c11a0000050440409143c114101e007100f401001e201ca0506143da51240000d41e0501403000340c0744d4a884141e100300c8460400b074000038260741004640703074444c20006820034106401090090700300c00c0c02d01341030080000c286504a6440d04001580400b210800c0b242462541c010399480901c0c1400d000502c444081070342202d01d0f03d4500407100d110130b1001514144640d54009000d60440000140410340a03414060681e4107014046c3c44d240c500c010850070160548021500c0c10f903590018010b007012441240e00402c03448211700035042c00c0ca000038020311036511004200340300031000e1004201415024840d85031080e0010710007410500700103510303545450700e510014442c4401c404400780c400d12101c12a900240c4075032a4030b100300503916805944000099800000303151300440144c40fa44641802411520301d0151242801e00c0c0007078003800c941c10040115403103000c0074041d0105c10022a13180505199000 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 438769064 1250 438767814 438767839
    0x40e01050601051633050c19050a140f12010504022a0f0106090c02060907060e060a0c050a08130b03070f030903030b100504151403060103021c1503150504020f 70
    0x1217410b0505c0e8800d000b5444001c180031040700c039540002d0f426049050a2000d07503103200100556004401c0c1041891151001d8103184074004c400402d0809060f16000000c20703c101001c40c8558411081c06411a40005482c0c40c0c4050244005025020440f42980303854a04001400e685c0301c0c0c003c4c4c1e003011044002c42100c26240c1013203228890358003e8020b20441d5a6415000002c240d0066200094022800015682800031039003809440c41c03030307c844201015140901200350051032480c400e0180450140340860010419042c40c14420140b2654503c1c2100d5a18400f8646c3c0d40501d210000c28001d10074041d8001d0245080402c281c81c00207400c0b80389040072400340052140150304511207030411184103901a009000b0f440407105240034501000d41c1c1140c8540040c10f05c29030090050021500070342c440c0c0c0082141d01c0c2c54082a00300c145400b0340c104221541d02c0001d05501400640410030131090084040b082c1c01107060070001403074180c001c00c005004c2001414403442c41c01c0d074030 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 438770314 1250 438769064 438769073
    0x1e030405030a0c050c18090f070302130b0d060501080307060605010f23040e091c0f020604030e04180c05120c0f210601090f06050a06050306040e1903022a06220902031302040e010506010516 83
    0x3b44656150003180c180903c3d43c3d10010b55480754000032040d1a240c6c1011400701c0d581d4080c0f0284d201c09004c1e5911154440080410b4511a42da000e402114941e41000b001a0080350044007034000c5001802500080c184000c030500c1c0340b0401107102e01444291034a0405807600400c3c62030744030340c050404810040e04180010018010124001c0007800d84400c0340c0180180d498404003500c0c0160b80300580c0302c0075115029501e00c00140c110340e002c0800805800d140c10402c10180040d4076810556508445001c0d01030308200098100c000311a503100d480540c41199070040d0700080c034050b25090140c50519a00400620004041a00542e01c0314400c2e0b035419010400b4180101e000340402d400c6030b00500d8000d450718420300b001040b04924140b2409012003464100010102c0140001d151080c44610ba90000c8581ca001c081b180d07058450010b6035020600045200f512140f884030094050b9104010890b0a80e4111b084147e142504000450b600301c81240d00b50705502055460b0810365282 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 438771564 1250 438770314 438770329
    0x503040602130f030501020909070e0d08091c1218030b0f090a1b030c080708061b04080618010c0e130f020904090303021e030405030a0c050c18090f070302130b 70
    0x41240f07940c0424000040c80010350190610300c100700c400f8001d40d107810030103c0c0c02000c2c54107481c0e0310213031002e46180024810002002ca02c00040c1010315910112420500130809008046e508044403900251006500160305a500702c0941034220343d140c1581c40700901c1036030080c81c1040c1c0c66a59030104440f03134401c000200751140d002c1c403200700500305107030702c800c121556110446a0400c080800300b81490082800300a541c4010002c0c00344e42d0710a0203140d046d55071000150b80c4150200001316990b5018481d42c1d2140c00001042040b86c800d11100d58216044400c070700081005002380800d5564030003d030001c0400001c00c000c2501d0f10f180382c43d04024494141103903802032404003031904042d0140c000d0001d407079000b8903001103a090419144590f2008a40042041d00200b0032014140c0c05a038406c403030345010f24104c845102c1c88402143c02030010010700c80900382c000c400c00040140400052418500c0c8001a000399469507020415603040c0c282060385264694040200b543c481c8003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 438772814 1250 438771564 438771569
    0x507020a06090f06020c0d0803100b030f06010f03020705060601080901060f0e1f0f030305030a0609090302010e0d0f080f0403170a0c02010605061c090c27060f06050304060213 77
    0x506800c500c540d51480a0400e40d280e2050b500c484445201c002011800810b4000f410030300582829003848203030796400126400200a0500c0329800c150129408089101542c403a00506009038a68102500098081ca543c8141d90040500411294000500100d4101d800c03000a091a030310544400840c1c6015142c01e402940e084c0340d060100051440840030094004c10b5082e00000415041c03030455100320070180948800080b8903402040003070305c15001940d004440090000c4c040b6240c8902c941070351013907441540140e44801d240e2011110a20084003940440d042c141c0c0d0704040e418006d800124000c107840301c403440070000101454007a184140b02d5504452031481d29262110441004285494200300150310700000403826040890454420f40101201040e59282c140845d0000d03140f000c3c421141d15100c5040054a124030303402e144950803900e0440641100010b903580103c40345a4401d5845081c1844c3c20404141c020301280d8016401c80c00243c0c0c0c0b003405d42502c981d4007600b03a = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 438774064 1250 438772814 438772819
    0x7170321040f201201140702030a02150606041205010902130203090c041e0908031b0f1603090308040b0409050603070509060112060e0a050a1821020a140114010803071110050702 78
    0x1e15910300d41484c10f501c55050311940c94200e80b01911081002c0780e80340503120f20503002d0380c071400b464003900024070070b15940204005c1543e03281079180d40540d400f040b0305c03940454a60b0b4441d40c907182140790070303910381c84d15140d040e00841c00e600e07040c1042c50780c482c001504140240c0d51400c0e440c0301403680440b080d040d100542c0c0103201e009003501d043e02c641d40c1b080342c10042c4550451103c5440d104100e0854940e034881250160034245000305800303804240000407014071400403800030008100101a10060141000d40c0e0b842d0780c60001741c031082c0e94008182034420b800100c02441035a40700310a9940004080c6450740052003001c681030010162070300444828031003007003004810b149640241d84110540c0d0014400c9900c0810141542541d82e00c00420a000714070351081404000c2640804541a030710440780185d290b500d03401e4503800c0340050890f580e5191510300000f5481e4402c1b050050000c500150b2402056441d9030803000c0c4079040403442240b04421010704c180c81002134a0031540c00 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 438775314 1250 438774064 438774079
    0xd1b03121b0f0c0302060f0711010f02090123030403111011090a091e0f060b0301030503040f060f080c0f0c19060c05270307170321040f20 61
    0x8008a400e400200104010300180c032401c0c21070855840343c003102c0d002e0360341900141016107545802101182000740410100603210100c28140c600c2405a604085a8000c0040c3e850a00358001054901200103494610003044c0700b00d140d0440040031250302607050b03d4140c010000d914900da040c00c06004440d501c40d0b00700b00d5070910348900c80005007901c07901103451080c0c260740c5048003425241c071055103c0b0078000e800c070410100e110740c2e040300c402e005820790005020390702c3d13064011300707500283c10a4465500100b02441800c0440140c900680600d080c81500030b090500c0040880800400540d640300c40070802103400c1e00c284040d00c1c4002e8601c0185e52118070130120541640041c08001ea42280c10400300d40310340c0b4050012160704840c1c2d0110507240a01c0b010074541068445c001452305807091100000e0040880b40c1010249641007020315550001107404001003000e00304100c11503080c3c48203100000d0290420041d010b60700540c11001030354280901d5101c100a01c0509800503030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 438776564 1250 438775314 438775331
    0x36080607081f05090703050402030313080f0105011409010902070f020d030804051b0102151b07240b010e09060a0902130302091509010e0c07080d1406030d1b0312 71
    0x400008680c03145000400002c0180d4000c0c8072099900914030902c0d400c110607401160041e40719400040d801130025080700d1038802100c10307620fa00e54455100c1c1140f50400b2009410f8007101380a000d004140c1c10007050603840031140003480390304040c440d0a9441b0386c000360a030104030b0f55800d200344554000b03141c1a071070f0181d401c001d080c210007190204c505014001485e15140840443c5900039a0180c2c02403100f0440c4482e402d0720080040d0000440440030b013502075030002100001c15a0070b12800140305101c4480901e40744906400700f00108541c14a02c0c0c075055030740d000f043c1c5026032508440e80d030016210003001c10481c0e40c41d90040c100403800080d000c04880e02020b66031003120300c00d6a20a82079030700e40c1d4040708a0a00b5140c0b40d07901044038401000003070300303450805400c0104c850000346800e038260b56107400740c0d00041420074003644962502c91b081300240da401c1d61081064000d80409144c600c402009650304843c02d082c00c0d941c420700441070506c2004807076124458014100040342 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 438777814 1250 438776564 438776567
    0xa1b03022d0318010e07030f021201050c0904051806010b0414040603020a0905040804080d080403110a050604030305100911120c1305010f030e0102031806010636080607 74
    0x1440880d4a409890211048140314519545440719440200c6515070031a281c1001240c0114001a0960142d41d01c840d0a0702c6102814001800214802c9070a020401014414000750210420304121140d141c0002c001040814404881900004031b80024080c1d81d0800703d1400d4460f900ca2601c002e204e0000089000344050703000300b081e2100b07000742d003507240c2459080100b41c1e40c80340402500130101d070f0010801c0025940100703400500c0307800081d0415407a030301685e1a140c8003030748400c00280c0b0706040c44140358214900c045025401405801000d440343c0342c2551340c05018000400301507036000058a9912041d0402e00500034140092000030034805030100307103802085200d6000189000442c104141c030701d08440e00b60b0b40d480d0754110780620784001907071200f00c2c84a1070700c01c1c503413204242c0e0540710f0284000c61280b920641e0110b0b148510440301864020143c003c0400d00000c08292205d607072500e03030b806000041c03a591444403190f007200310214181c49035010502d140704950511130705070f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 438779064 1250 438777814 438777817
    0x308161209030c02011101020f0f09151606050c03090606010807091707090507020106060c03050f0904090503120c09030322030501060b0c0c030705010509010f0c0209010b0403110d1a0a1b0302 84
    0x54001d99031b1540007009944018200e06c0380040f41c0c01161020461030541000c900003910300c0740001022080d030f000e904040c0340c000d984a0301c1e454444440504c9030b82c003041254410150044040c200d00c60451814402440e55010060f01c410f040c002c2450020304058400d04898000e0318580003003003034541000202c00c1d52500d0500a01301c000341000c0014020610502c01d001c21a0000d42c2e602ea40c0d0320094400380d65943c0715222520300c01d0010041c80d000743c7c90724051003820a02c02c500441c0c0c0c94a508080000b582409410b00e504070204100c0710801d940c00000750381d400fa100c4014405000c040c4032420841201303941c80180303154244100000c0902c0c0079005000407505001c1602e2a104c0a003040503110a02c0b401100e0105000384000703407865110f000e00004050079414501401d2846400007460301500340d00c561507401000905000700600400d0840000340291a00c0b01d2072003030b50303449171a110040c0c4018245101c00d000003a601c14940e401c180c07002c0b40320f102500c915454809001b4040e = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 438780314 1250 438779064 438779087
    0x90d12020d110607090302130225260301150c02030a0302151501020615060c1b01120209060d020702060706150e01060513050105030c0904050f06040e0a030816120903 73
    0x3081c00c40c01e0b036500e4031a020030040d10620340c0d5038032001c12500750783c204482c00c440c0740f085405460342800380380d400e91941903010302d40e41c0038142c002201c5595860300243d142c031200f0700c000125100c10361000c2402d4291003030740c2c1900c020580f010444c4841c0c0342c0840342c0d05886800a0f500d8806c18001d8002e05401184a0300740c4100320341c004802c1d5a5041c4807138203a0080f0700390b0301d005a01c4000040d02c0c020f001560003411000c000c1c201407810040140b014a0b00440400e800001d0b4001c002e00000d640c0c02c2501c081d0b0140c9100320650403c5412400150203000b020407101d50182c0028000301190350b0041240d02140d800036040010f8000c021a94503060703c1c50180c000460901030020900358041c000b40d401140c000c540000846003008011606a00050800b000c011380c188001f8038035564601403580306009600d4648d00d01e18203c010041a141d0340c41c109102c60b04950703401e00200742d0040b146503101c100442103000a85113624110349810010360841d60031072801a41c00f007050f40c006c041407403 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 438781564 1250 438780314 438780317
    0x1140f040b070c081c09051608010c0c110d1a01090f0513050309220f020c010b0a150507032006090c03240901020708040f031401020a08070302090d12020d 68
    0x1ca540c49190607078190009250240420a0070f01c86031404c40c03161a80a020750201550100d82c041c555a50245850403807400006d068846500c24080d9100911401200d010305140000c0340c1481900c42503076001c1c04143c510b000b1074100541005218840c0038501d515590b00c0e0b00b008141d03a40b0401400203080402c611071009052102044c005255422030740000358000740034500c3c1960000c00c0090011612034990003510b610360b40c00102e06028414070311140c8a0203400360307075015844ca0301401c5580000c5034510030321600000b4014881030b41481150888141455582d0740c099040a40381c0c440d94003001e00400d81441c02e00003d0060100f0118019032080c011034054810319403c141c0c680c940c0034030f038080301629410402203a843d6640b440303030002a80c1c000113150039001d84482034140e025800800319501802c104008204c00d104100b01460380c454001c5041070055800145040009404203082540104450b0155501c0b01d22144130a54803550141140f6002e52001e912580000c1c0c0d01d50 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 438782814 1250 438781564 438781583
    0x9090a05010606020610050f010e10090806101208180607080705010f1a0f13090f2603340207050f040614091e042f0a030201030b0301140f04 62
    0xa83c031400094014060303101c0000c4040303143e0526090245092101c0c0c280d50400050f14201794a90b1203125443c0e078540d480d42d0b5582005410911014585800a442201503d442200810900241c00600414181c2c005c04031695040b8648505101904035844d40703034001000145101000601002060311511440080c881140c091451004441003101282d621188d0a1020001440c0518070400081030003042290040404540c0c40100c0d944080300b25642d080c9016120b0500000d0070203414101044e80480c00300c1e4851510310007060102900c191005082d141c98051030b0f126640036840c9201b0f900a01d801c40810702c443c000e660308039234444c16009a03100080c0201c0c2d400c06000740d20544294906e074011400380d5505000e90b03000000c0040ca40a59541d203c5146030640e1018240200c0c01003c001c482051240000c144103885040c08103050420005e40c0c48040d110703c14140b0842e82c0900300010f007103144401290140080032500c01907003166008100310004c05451060149d4000c540d101c = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 438784064 1250 438782814 438782819
    0x316050f060c21091f11030c0a03110310090b0d06090308160e06070803040201030b1521130b0711030a0309060c03090c031e020915010210050606040603020d020909090a050106 77
    0x40c500e00e002a188580b03150005c8090354504400ca204540c0b0f801d480300c0c00000e0520007034003582c2450f0020b0301d401d4441e000018101c800182e041c0140c62043c400031031039038034504200540301d81e61885c40c07003050388164030b601d4804074607038840c85c9030030980d50807500500840542c0c0c60024100d09088507502c01216452000c5c3ca0b01501c50400302c460380c9000f0300060310f0b108080e2112003450b000108124100358031050034501546400310416805414401029100c505070f5043c03038140610704040506541540c410802146650700c02c81000580010b90b140c1c0644034680112888a0340800c1480365200c001940310107180d040d4003070383c000b038002c1c02c0030410184207150440c25a0500200900300c1500004241301003001420043e511182002c0c0000c01c0b025241c3c0820014642254403000e4240b0140c1c040000d541c0520042d400c02ca28040108130a02c0e05d500002d2190149026000401d03901080100c1801d1781941100d80040000385542ca0b145841c000e020394410000f00f0486d4a5420314a00 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 438785314 1250 438784064 438784117
    0x3070e06030d120e0d0909050f060d14011103010807050118030b070f030603020a0924030302030423030604051c020102090919020d15090b0a080316050f060c 69
    0x65806818000c02815407500818030864090081c0440150420383d100701c00d003451841003240c2105c104c010307182e0400701c920306030240048880003448400300d100d038002017103890341d9441107102c4000d902c0510003c103040317146905401095800480300500744000004200248002900d204551003641e40300c4215428a03004044151540300c02064010010040390380107008524138020b8400358603000032000d83c0d0f500026016604c0d40e0003901201e550f001c0000100b090803030150200c1b4840d1007551105403440d50000d6892241d41b0404240314a043d12652044012000001c00f00c80024100c50703082c01c081c14819195074091311151081103041d568a4036440c01030090740c1c800740340240041c04d999610782010b00001644440204102e40c2007119040304641881081c2c0041040d0030407640990410120008032803202900910400d40c1c0602007010380b42c00801c4420b154403540d0101012400d511b002460129000007000040c00380804006880c0f021101074203408862207202404101044070 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 438786564 1250 438785314 438785339
    0x30318060f0c18031112030414120a03020601060e040e01060902120921030408071a10060201090b06280b0d051003021c1104020705070f0902090105030406050903070b13020307 77
    0x3500051503210800c002182005d000c44182c200003900c0500e1401e050402c8504641c071542204001410001040c40342e82840c2c0503c0501c0c800804c01070483e0080d03502e000e0350391081485890f040001b40f0b000c480e502d03184d64004201c5070307a10034000d2250303585800401010790801c00440140b107803441c0c0082e00b1250001184135410341c4280700c01220038505840314046a00044c02179658040c204640c40014241c84003d10380c2582c40c06051801381811032251006c51103651086045a0503c0400c002281107020810f80010301120360303082d2105449242035052003150712020500038011000910792001200901080c0b0007843c0c2009190346100c40301c01e55400da03000103034015400c402644141c00e481d180401c02c07540110070030104010f60a0000e400d990101204075000c1c0c0240f0301c10441c0c1c5110052080213410501c500390f0900600d10b00007015400020006031020391108003064030b0301c030140122140e50b40c00202374941490420f4500306019101d0000b20301034400c044000612101c541d8 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 438787814 1250 438786564 438786587
    0x1050a050f071202130e0f010504020423041d1f02120103030c030306081e0115151404030215041412100c020106051f090e06030316030318060f0c 64
    0x40c1d416151106802151000b007200c0d281c0020550800100d400c02c4601c80403040100345419001d60320740f0b0b02c00d40300c42492206030300c030300c1c0203d00501080c0420311315030b1002401080c05e20607030485440100c3c0054003511102000e8080d40d030489850b0403800d01c010910200c042c1c04545400340190b080c0709410120f1007111441041c2d801454018000240714103e04642c0324000e24010500d03d407038408183c1020f6060100c0319074082030003d420003445003030040e0f60540010f00c08080926290070b119601c034080b001018006c0054594883c4110031200007620040c1d50042c0001100c0d400d071403500500d81d40b0034000c0c072070007400c0e100e900c103900e01e844503e203402e0350b5201000d000300580300a03118002d01040341d01175040d55200c0341301160710344550010b0003042440720f01e007071000381d103c0802918013122504130915085440e001c000d0162800000c581c02202e8000071082c1044440c01c0c100c0c02044100380b8801c0a4904640000038004140c1100e4000104084200500c0c1001c1030140d50102515 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 438789064 1250 438787814 438787831
    0x1712071d09072106150f020105090a021207030506070302030a0b04150e06030a0f112d01050315040e0114070203070f0204020a0e090f0702010b010e06190306170f01050a05 75
    0x950028802d0303441a81044005061420422030850494001105807071301a08603041443c1945111a601e550202818400c0922400200024240548200d03114605c0c60b0019014141441441201c000304024074401140c200d020b503451420300d0311004010354000d640030618541030922460480ca4140306090040b003480100c1c0003907500e00701400c0d141c8000104426410300807070078400f021541081c0b48403000c500c10002d4249840300030041150b03c107010098011140c4a14402480c036180002107144824000d090560722540ea440a51184508004140340c000381800d03034080c02e14030150030402641d103110080d1060380d82c40310800c0340d4a015480021307022680502ca1100541450780c02000038130540d1816103883c5402001003400c40e5001c0c0c595110354600c0c003007004092035082c41950748144003440c151081101d5040010403502902440c0402031100d484d21700500e5000c1d41c890f100500c84a544203040e0b1202118064031200440200c08140d424134000401868051213441d201d81800c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 438790314 1250 438789064 438789079
    0x103061a0618010c1407030323090a0902030907091107030207061b030c0203010b030a140c030109030c02041a0a09091401110406080705070b1311040b0901050d1712071d 74
    0x20070b0044030300340311049040e98003255144034001035084c148948400307140240c940300608414114880760081005000e80c40c0c9034030900102c401c50791160800300c110b912040300540c8035124558120305140b40d952003201603510b0159908003206004003e804854000c2d0203850380b180c1c0d598019a2a900020342c03000c4200c11401a03400042d02078410302c981e490018000188008001000c40d10b0034034400720950340d28641c01000d0401d00300c200300f08401c1d00f205800a1001c0700c1181c0e4084c0003024405002071180d5213a461070014080d01018000150754000d04c1038042036541c28400e03005110042d0166580513040c0d030301c81c01c14130050091207018103281c40700c130386800e15013642104c000070060098010001d040241c0e602054103942c14502030840300f0b0036a000c00740da03807078080d83c80440000403500441c101502d40f400c966580a406044070b03410344601416a019280a0803200c0842d400b0443c0d51101203502802010042c000e28443d117002c1d154800244018440400e4505440395000d610600 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 438791564 1250 438790314 438790357
    0x170a0e030c1008011503110f04150201020a080403080a0f06091a090105033003090312011e090c020111070602040602060601051e090105090d12080106171506120103061a06 75
    0x300300480d50742c021102d02d000206681e40c8000d0481c82d5010036403007032311514045018800030340103211540d80c1000c140000c51030301040620107050024010700107005d001105001070341007515500710742511a8420350070840e094032000ba01d030041116414a050820003400078440c0d5040015007581691401001802070004d90721545001618494503a0340101140d002a121190048043e50190203c5e102071034442c08001d11341c481034001680150b04251082c0c0070f05080da103030050f40c481662000000441c1c00701c0b02c40020707400b502425a03106510080010000140034155024000341c400399401d650503902e0b00d20045840380a0014083c0885204040c00300c1c3d413640440040400d120b060402d0b90803c40c03038100055181c5404001550f0100220030200350a6500c50101409059142030002c00c13203401030780095031030702c00a0084901e9020080310b90180d40d1a80190b41c0315913500e81e40143c59607140c1c42d0500c080c0040c000d25034800e1114481e1303407407a0300c0c0100aa8050003825104800ca0300c0d03 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 438792814 1250 438791564 438791579
    0xc040b03131e0803011e3c06032301030201020607050a0318030314180307062403082106010e0f120f0f061303051204170a0e030c100801 60
    0x6040380480d01400b400c04609100400d02030380c12551801400c409407258540342e00180030306a00b01c1040c400030098041802800c0040307407854480012aa01c82104a403240e001800c002c4088601a04042c4246ca0000305207525400c110100002034901000008100d401d40c640301d2000e000090160f0400c40016521510440241c980803c0c28030b000f04101585481141c0a000115010340000e42c40c1c64082560142c0490010380098460191164010342c40514907101e0250341c1000b0200c40c4c03602a41100c0e00298481d080d503401c8013044210805580f45054082c03580112115a05c0b04195004a9070000f826008240302d808103031204441c6502c0c0100b0008040080c0d4a0380c0d621103801800d4241e0821b0400518101c1c00c490030042011284840c045e520b41140101088102000c808490300080e900500381e030921502d07005501c8103600e941ca0803440800010007200038a001c0400d001e01c0065111407540803046054058510034030704ca00c14424203200400c44040400c3c1094010050300303 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 438794064 1250 438792814 438792841
    0x80726190312060f090b01020c010e0306010501180504020f1c020a05070605330111030c07030602250c061202070c0303051b0f010e0c0a0303020c0103091109090d080c040b03 76
    0x2038010b10000603015440b440c800016958507000400707580d07900d4403540000c0d40c04102e4800c6c404000d0900a00721030005002a94030b407014044d140c1001407825042c52004080580c65004d0000248155112006011a0740890300000c1c00440f200c080c480150121074414401c480e4800065558503180c41c80a44914024080103002010417a1544100d003a03065500108005031102c074145154040102500050099075006046056038000308918a24900005640350071241c1c0010050307110f00a68201c1c2003054201624841755808000410003040107182a040c03c0e11559140c092000c40c3c90282401203003e500310092554002c40020f00104e03000d000a4200c80710205041c482c1d058106010345c1c200303058484502c0e550382d15429140ba46000600010007200e10565200f44291f01e180c0f0001c2d070b80c0d01c804131864141651101c104042c4000c2804010580d880076100e01c9050500c400003640d40c9619107030040002d41e8070000b00b41d400d10380d0011034045500035200b041c11601d50454403560f2 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 438795314 1250 438794064 438794087
    0xb030708150604030602030a091202010b010219030903051204030b01170d0309050106120f0c170607031a150307020d030c0518040b03011e0e010902090c03100807261903 74
    0x86542031000000017109400118480c628525000c01d107150700f854603080d43e000103040e080030745e41440407411035642d0000d0804240c032603501908040d020182800d60b8007448541000e4081c0c0943c030b00e10300a0040c0030000b04122446102d03440c0d01c0d0383e6102400d2003010121600407070f09400c486c6c508000d035440b80d0481e41c0000e00031400060801ea030b5501c03107600a00303045c404407862098824050140460203d8500042035100029020746c03000c00c00300c5807500002003204050550300c51100703d1030303070300026041003641026054094800040c58180515081210101d0051040c294094405072007402061000030f0640c640c0d90a000e680c10411008002c49104940c0003540e0300d0714100740da5400d0149101c0040c01b25003802d4002003003600d441c01d50310946500704043c1c0c10004000016200e021100e139114010740d80158694032100c0008444551070350102e84140700345c80c400300d103040343e80c035902200b5502400a5000120700518503603e41c1c00c100c006402450190000101180c00f400f451300c10f = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 438796564 1250 438795314 438795319
    0x812040506180a060207090e0309310203040b09010506030a08031801020706060609051306050904140a12030605101412090f01090804050103060e04390312090b03070815 74
    0xc5104560080340382d81503d03900500060f4001c0b242041100700c540326030114190b608010714030f000d00c0d403c00309104090700814110851340c0c5500c00f002c04495100c08483d51810000c017559203040030b050800c99001c0541c0c482107154038060211342075180000d0030000041e40086d106055030340e0510900c4403843c2280305082c00d55002c001d480e00003449841090040c20003602e510544600303040502c00c080012150000303170381e49024014030013595030028850344540c1c0122140e041800034204135043c48010708009158400c003c008141460700768010b941600d1041e101c1c5001040010002c80b090121210b5404910a040144480b461441318400f5409040c220440d040031203130340d5000d03003101e2a030030055403913a602040502080da807501450300201740602c508005401d154481113400c14038041c0c81029949181c5550914484802400c1d80202c144c0c2010380743e240d83e90800c04500d103d170501c0030b0001201e10101080400031181a01c2c0034051507070341e10075259110703010071070160000da1190360f = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 438797814 1250 438796564 438796597
    0x13120b191104031202010606050c07140f13050103060c1b0219050a140a06030209060a0c230606030c180f0901020d0c0309110603010b0f070602070507031b0812040506 73
    0x1c1c07222010800400007148104030ba89180c40161070002e08480242c0c001c502041020014080d03402ea0005011094036601e0450100000c1e0303d000007560f0501011110340c2140e403444c8841901c54003944403078102c90003081c0900c01d01141c41d8049503400e041080001c030301011800c03030300003600303103140803040070710080711001d0b44507454a00160440600307500000c0110046558407006083c000c000d10000c000301e040640c104107954000600900416130817a0420801222113000e110403401851003503c01e50340188114000e19101c11384401d800c483c0c19000c0e21850a42c00e4090401c02041e030401e2411016018040d1114000341c1c881280103417460006640a100d180d00301c200901c00c10101400e81c1c1c600041e030300c0052400001c40d0010300c031154410101407004000507000d000444a2203454243c3c21070340d038410391604400a0103044000740071403083c040041b041204018404a410300b420a56020140d41c65180c00c0c1c0c1d8401c0c501e004041d04000744820450b40c1031942c0030301740440e1002c0008 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 438799064 1250 438797814 438797831
    0xa030614011421043507060b0a05060d061d090304050d080729070201050126010e07080d1e0203161415070f18150c0b07030213120b19 59
    0x540c0f00e14401c1d00d00303840405445000c000180f014110881d000c2c62802c60004039034441c0200100d042c01a86009845940c07282e031280303030b20350303614004c1e001408000380301c1038449a510f102400203011a008041882c241392a544c200c815460500d20710a107015401503252508010501418000010048401481c14040c2000240c403403200900007540885c51446020800a903814000308050146415a40340c03030010300506004465803a0740b20a5861600c44503004884030703d004000342602a2042d000b0202c000c61812400b0540d0864100710340d0301d00c80600fa90642e034540c1c84000b40b83d9240541e000300010141c0720070101c0d030060b403903010310300f51481030381d403c3c600ca070920f07000444010180d9488070802c02910b80140c40801101d0080c035060320f0103104000340d40b02400b0300b40079800c1d00390140c0d0a000551840760025006142d484801e2110070300b8003007030160107500180c010492100911202040001002e101420b060303420000b10b04041d2603c41080c4100200181903c86142e00c42c0307001c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 438800314 1250 438799064 438799117
    0x18020429040f080610060503040b061005090a0b0405031c050702040f0617010e160302150309010207140a020333150301061805070f17070912080a0306140114 69
    0xb00001d03c00c0b1000fa0006240c0030302042d4140c2041e400a00130f00006100b4440498a5000b00383c6d8025401d5a840000c14008002500d00c3d00540030b14aa202c0034854000c2002280c060141c400c80ea816000c86400221510040c8840c0c11403085460005100388152009460f1a810105807001c1c40100004e240791940b0000441009040081090384c3d100c1e03400e9840e0f0f450030000f0340880f000300750724401c2007400c0da070020306140010108800f2015000c8046048214294100c0701101d90003488800340700d04041c3c005855071400401640b103406910303204400320804181d081403c0c4c1e550309202a82e02e1b881120f1115441c0c000d0040318520400402414039603c1c00d101c1c010140c54003c4007551007003e00018502580c6004040e541000700c607001c40324403a0f030004c80d0007001d0101d01d103003100542c1c1c400d1021034414115511008031500720251041c2030280f003200400c40c0100d103640c184083c0f40c80d840c0700324004090b0b0079054001341203001005c12004440c1c01600103c0e884005140d810340c503203101c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 438801564 1250 438800314 438800339
    0x1060320100806150705010902090a050c0406030203040501110406020a030e0103021c0e2a0f0f091311090708040b070306060f111005010b040509070915050306031509071802042904 79
    0x141246d00e40c4d540d032401d1055142040c588c0341c2c0030f928400300b4001f61410012042c014061440345038140750700400441c04003c42900b16540c00b042180d8900c1d292503a0303000c001d698000390318003500801c03081c0000c502194840d008403000034403400c41c0d43e080d005050150720001e01610320019444d0080d030105444481c001060f859008105130003544070381c0c1340207040004001c141c40c03a5a205000d4803550308080d4586140c1e860b800900f4080b500d07602d0925040195001d2008503949034480d0302441040340880c3c100c405180158003405d03004e0203a0786e41c00030a60803100c0c1405104046005240030404052140a603080804040d800340d0f0107402440b0b01c00c0003a07450070307044038195940c0498140101d0030120f00381a030042c280c2ca84070303094a1910212804940c3c0d400090410401300000180c0302d03131000c0014400502d002c000041003860710001181d19520540aa40c030408484010300d1484442d80c0292001c0d03502051107101c1c150503030340c0c0c910741d00c0d2500d40e52201c08420034000011440d10b00769 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 438802814 1250 438801564 438801577
    0x9010902090904202107060302070203062d010e0412020609060c0a0903061404260f071a0403020607090f050f0d14060411010e0433090e0106032010080615 68
    0x189098110464517203490f0a0a80e01d82110741018410310010001d030394005a025003181103c1d00301191045440b406c00c10f0182c40b6083c001e02d2912030400000c44c5407181803584d00c01c074018040c01d140328036841801c0b601c80d80299845000f030f83c40640810301070080d000c0100b4004c9218140740e884c403603480e0f0760b00080d00e00d40325003400c20014010400003071040d1000d0a0920004090f051500700f40314040303807a95401115008440064003240900c100001c6985c1543c44c0826551245050315091034025940c080481d03031007000034019400054140400c8080074296400280800301d040004004d0108680d82050280c40c1e0b4041c010400b003030880c092291a0050780101201000f01410000152030340340320001e00d9024900d0060300034070704030854040c405030810101c171440d0380e108280c21055640b10282c00800c5550b2801780207480c54501580300c44100e134810030103100000c01c009007070102c0c04022030034513402400c0321070406a10380c840d43c0f040364040c40003408071900d01d200741d0b1504800d40200307 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 438804064 1250 438802814 438802849
    0xe0a0602011e15090b040908070602181e04090f0f0803090d090e0a0b0f060a03060801060807081c0212030a02030403020f0c030d05072306060901090209090420 70
    0x65810114010100308a992401d040b4503040c0581d003841d0b001010000203030320a1503825541d54051803126034a41c0c10070403001e81c20080040d116041c83c18008004d5200f900c124000000c0c590000c1c0c01c0b4200403030502d44014103c41c40f078100c20b00300c8042c80060100ca8801325003107031000d01440b0000306201900d0140c01c0c058210340b51070786440c15800c1e140c200401112401e00255240801911048199003540100000d00110300703e848440465200801071030488c1e031261022810181282d819403120040741e072032000a00106a9659490381c4a0b032803801409143d8020310303199401e1140480a031020303807099104582028182d8500400b603500151107841840e0780010910040c141d041140d08400706803000945041500c80c0e00196491820845900038040d0204c2c0352800c4c41510b011046034001681d9810074070321021160b040e100c007812140c01d03105503a50400402d001016200381e07001010040d0034000301d5112600c0d82030907400c41c8020650914501074a8801540750410b102e00180c000 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 438805314 1250 438804064 438804071
    0x5011d0a0b0c0d0201020301030f020f01120c02160f0b071407030c080109060605030d081803090303130e0718030204021803011505010e030a021311041706090c0a0305100b010e0a060201 81
    0x51201c281e003000f10030021803085a006000620101e0f02c00d8456203e0b0990481d0481c1c000700e180340040c0e82d2009080808400c45150201e05881240c010802000c0041104c040580315a2180c0401d000c0351054011164418400d0010100017201d40643c0b15000e5050021900515600d1342d48801203c0d00e42c00020190351604141e1040008074000c44d00500421409424a81c0340d80600504141c4000c0284080070705d140d0050075a80400e200310b504000780a030540c1c6e940c6209214134001202a03215541000901c440011a000c0c810030200d0081088107001c15080c901d03580800001e500150f40d54091074000c410000c02c1540c00740f20324070160b1542182440410718220014001d449005031031802034101d4100800140c0d560504480c210591400c005000b07005411120b81c1c4d030080e0f80118401c0c1140e06844441d0345000039141e031041183c88101c0d074840c0e0011007884a1145203101c0100140d010300d030440076080302901302107011501850b010000668441c0040c482d10031030381c80310001d81d65 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 438806564 1250 438805314 438805327
    0x190c0c080307060f050c030f06120124080d050a0f12050406050f0702010203070c0b040c030c0b1c02130e15061b100e15041505040605010510090303020705011d0a0b 72
    0x903005001c1300080200d400c0009281403941320300700b031000400a540340d85400e00080c4c2256035905200d03013811600e400800c11010b04924464001c211014910916014490b001032580b40c0010101030600c5a03903a22424449651001d9455906840b0b298041c8081a03029600c03c3c1040d2180d18815801400c000c40c8900b844403200c101000d0241c404011a4010000c21441580117441c00d0241503110503061f65980e114101a1640f01040d040200a40414000014a0001c5c0e0707000e00420058991032700306a00250001d84103d201d0301214400032030440e2810801200d094040e030b50b00c991038501d8146019a00400101160b1021008105c80a941c2c0301c1240b07000b0080000e4425450780103020421503041605096440340c141800b81c05420f09400081d00700700400e01c611061a1000c0418001e6007172915000016007424060107000d82182e9400d04101445034001404680c0c2540241640c036050100444040c07480e03d591102c1e442141c0709009058840101520003000725480700d640b00e58 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 438807814 1250 438806564 438806573
    0x40b0315071412150a03031b17070f0b09070f090207050118030201020c0d0305040c090e0f06040b040210050304150b1c112e3605030705011103190c0c080307 69
    0x142c0314013540075440076542440085c0d0001e40e41c002c01c80c08228440e2100b5100c1c42d2140c02542c80340a0b040c0103a90228400302002060511a1007841c424056040e003a52400d0b05180c1c1c910700341c400c40c481c01d05810010010381405600806000d4000c60021807210204088003040385960030341180181c1d400a80d0312020310007406082d80e030000c54641840942010346038941d050b040d90248000c9141c0c0c0d0020b81310245402c20054807441d001c401903400c00d01d4181817540100608607826030040010700b6051090358440c0045900c219407240300c8800310001100340800030514081c00f141c101c3c80748100e402c250341101c030b040c440a900c41d45101941445110600441c081c6640224164011544181c41c0710107000c50242c4001c01d42c1d1601c18004415115100404541c15907000e0780945008003034072120300d0140c1d901c0700b540c00c16021240d5040d82d6400440703140c16040c80161490f0000c2c44600343ca4503a100400080381564980b0100807803840e12190201e8580344e0041d0a903500003d43c0b10f0820 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 438809064 1250 438807814 438807841
    0x2040606022a03070e070c11010306260f0f0307050d090b04030b131e0512030c070b040212071d01060e090a05130501020f0711040b0315071412 63
    0x800345803020385580384404064011025006002e41d85040b080c1d10414915101000100000c1c41025040c240600301110054240035030f14009480c40140301842486550080c0241b00407504a4000b9140d104c4810540da801d00c400c04580d201c0c680140091140e039144104185c0f51035040c1d90300915036854103481d0032454800007441e000700f40000f10104103c0d501c891401d44080340c1d0030004841059031076003440c8841c507643d550300074900c4c800c000c008040c021106203030602c002c3c410000c0b14042441c510760500c0314002214060448001004500005101c118134281c209102428009100510b005410704100b16600704903059980b062240c2a800d2003800840c2c01462a810484020090f40d000b01d009088028095615107844501088240003601c0b07000001580000c000c544079694450354030701a6000d420282c0d183c2d83d11401000e0180340511507036400c51801001003404000a1071400c00c2c00500402140c180500c010f5800ca8800801000300b2951142c49042d071507514103008102242b = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 438810314 1250 438809064 438809069
    0x60a090501090b130c05090d0c080109080d0f0506061605070e0705030702070f0803030708150301090615140303030a11070b04050a0312020a200304050d0b0402040e0604080d1107051603020406 84
    0x2a83c1402c0e6811217040d080021155801810749840d440700d0910706040110a56aa2007041c03250328080c003138003c0c407030040040c0c080c5250b491024052640d0002440040d60000e5500740d502000030000c08444515041c1d2140c05903100d0b40503a80070390b07543d07540c0a00924080b10741401081c400030410081c15410f000c510003400034661080b000900303080c1d44540d2400024100810701c90382d90046003c01c01d4226854a082c14010002c2c802c100407450710704080c00f0412010384900b071205002142c414a01c4003100400d240c0900194119034030755030741c3d001a0115446401440104001c40c1c0045010003013140c0c825800b0313a0050200003500d2600030134107140000150035691050102d03200241d404204045c09032008241031000e114210030340e500f140b14540c031956002e00b141c0b02d500104800c9041003841a0700888041040130003181c1d0081e1101001c880c0104400010443c1c020940d0a5511061b070400010780c0c003508140a0f99102c62600c0d0340240c0d4401140e1842c0d00030801c518150013000003 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 438811564 1250 438810314 438810349
    0x1050c0414030d050708030a110a021e0309030a08030a2301061403040b070311040f0e09010506060406020601031218270c09030f020d120f03061508060603060a090501090b 75
    0x503902c103c10700100f0b0b41c042c1660081480b20000049800d1914a8210142c00e40c4040441982c44550100295072000c07ca0000030380c044280400642d07501021041d100d5502c0e01502405a481c21031340c1307080c415440205000c00303150341d403600d040d0f40c0c00c034000c1c103c3c3c0072000c108400b02442d4145800903103404240d035100100102c0400400000501d07100849070041c155080120f001107081b102045980186e4018907500e03010321170b0019003611000c20b124061142c86000304602e403205818400030f4440c9000c0c62000d0307800000100001243c8004201101405103041480b07c3c0100240880304c8450780e0010704005401c0310890a002d13a41d0034071049208400604104446511002400d220a244400f030010b0464030b52007030542d00c40c821144211a07119030461140002408042c8c041310000d654600000e1074514041010a007040220301800f80e076850792540b40e51088108807071903000030409074100d00d038a00001084270703150080e0b6010b4140d4900104d041e0444900340443d0101d980c11012 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 438812814 1250 438811564 438811573
    0x5010308130b0f1602010207030b0907031a160f09030203010c0908060f010311011b1515081b0904050a0b04120e061204080a021905060621120901030e01050c041403 72
    0x443c02068080754020726030040009224521800180e007044e20310361014184107090b60401020540c0440e0320700c25030344260741c20700404045aa1128414500303e9003100d8024940041c4007015004000350a04c1c40d51a18103044496102c1c1c0c04030b07081d02c40c00f20a8102282c1800c009010828003402620b07408803644603183c00e42d6166448a0814448031003200d410300010b204d07505032040841170000742c250f4001450381d00d55040106414000e01c1790710315001414844030b101040107800441d000c0c80c1c11444440030301090340004108400ca5601a0040300c8a102c0e1100e41000a030725400b2041c803031030041c1e5000408403069240130f0403404a098660744250401c10440c8061644801d100c0d070003541154807940c4800807000e00340c1c0b038003140ca03485540000030384c01100700b0003c0c005010b0380708100640322030f0019802e80340d00c0c00010142d0084100b0316040820510314400041307000c1c0c00e0b10041403402280321a44c6d440c0982c2103807c01d9540c621080000502400345441060344000441c205038000c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 438814064 1250 438812814 438812827
    0x10030b03071d0a0b1e0103020a03060308031005120a050a0b180d02071503090308011a070215040501140a0f1206150302031b070510020d0902060a030e0106082d1005010308130b 77
    0x30ba0000e03201210745d410b05a0100d00d060599200b0b5101e0809181e02c04906692420100d200702e01c1c072100c1348501441031448a141840040c0085020380c0402d03405030040942031510f0b034032072485090050036001c0c4650408a482c5203241c04000c804000007158000e0403c1509101c4441c408030600d134030010525007000414000030740d001130041d04644100c41800014162190300c1500c074072945001070f5111014490701100881e00740c000300100c81e4262541120900a40c20030450340c0140725504000c14050341e8042042c5015013140c8500d1000c035070700024034a840e08180e101c41c04803000040c00003680030003007240310040c021100d80e00b000004446400c141d242c0d5215590f80d0a140c4d600b910458010034400e2400c5016000b00604580c000c0000b607c849a02c1d07401401460b4580b01d0707681130b600308500020409004180080d015100c0b08c4008100c07507490003d81084410800c3c458940d00c20144c400d02c1d5000503110f5140618132807040350359200154050713188440100d4102519294040001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 438815314 1250 438814064 438814099
    0xb04060608101703071b060206070305061309150c020d0207081c050f0f0703121b05030106050901050c0a0c0302090f0c03060d0206070609080c0d0e10030b03071d0a0b 73
    0x1d0b40100c440b03039500740364610181201181540102c40c8000d1540c5580d490701030080b10f1400d039042c03c1d04d9055080f1600755440c1401203058410a40f0841e40044100b00b14454044281e0041140d86004e0240c000f0b00c2c541140c03d1a04441c00310f41150010f82060110f40310890341800441c008000410007040c1c4a01020640c21500d0403c504550034040001804009481c003181560480f020100815880320703203604000c0c020f030b0401c800c0e08503040d1a00e501004d203001c02d00d020040c0b022032507560604680c20034a043e520f961090f81050305011040c040030390b00c0c6034200200b6031160700c200d000030303e040d00e0340c4180080020003400c408481081c040c100a6014100c5e410b483c0e10000c00c54035075a8000050010402a115645c4090324403810a240d401c1130052610003050844231a5007124070b00311400b4000c07219460301059117079103c2450000503100700e100b0b40000f91100401000c0e200160382d206800704402c5074503000c02001c0d049860800080441c548a024000746050b103401ea10711144e2a40c = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 438816564 1250 438815314 438815341
    0x1f030807020409021e03011107120305190e0d14070b0601080604020f0d0f0b0901060206040f140609160b0406080105190e0901090c1a0901080414032d0f120c16060b04060608 76
    0x103414ac20160b03a840013031200040001c03144070002c40040e080204941013552252660b00150881c1c011440f0354001403580000442210746030358112204902d80e4031114011078071740c00041c010541c490340031b1102c404010f9040000344100c1000000c00034075481c5111060b402d50304800803091080c5454030040080b01d030045440c41d8455481003030074410304c175a03141c80d0000203010000311400b44503610030400490000640f0f0380300030903500401901c565079220003030064416400f402d800200031030010461810b000e240711108000c014403510440f6101d070f00031800740c0780894a101c40c50303445110b4030051010402028028118404480f40014904544221244500c1a245041203602c00004060000310a180301c00c0c048801c040e03076a42d000c590080070182003102a1103180e1100c03a24078100102041e000c55041c0c0000040c0d030390070700007510081c4240100c000c012608900d0204007400e00c1e50400141c00240510a42c00001c8050760541030104031303012034000b5424003080e4402d00c207404c0d04040 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 438817814 1250 438816564 438816593
    0x12090302060d0e0111040602010b1203130501030f1d060114030a0f02060c010605090c040305060f01080c0607050708030a0504091506140702040b06030a0e061f030807020409021e03011107 82
    0x50300880e0703061010070f0140c01408007181c540444038021401007040340d81134110b0007a500040343e61014a100004400d5201c1c416103100c0410314484c3c3c44100185d5000c3c1c2c110b502c190b01c000c00c0004808841744030318104e28079001100c0380c264024100501014604409403040030300140c2c000c03d0f9040b407695850841a8075010064810580892150500403003500a50b0107444043c1030030801d8281314020580d00c2c1c01600040700d00b405a00c00080d84442c1c12070031300c0e040303070510340040143d00350340d4041c000507502c0301c002542c09000b02100803585240800003804921803a654490b80c807440c0c10b03200c400325020440a50065115031f1020480580c3c4801d1000d001c80c09814129035400103840007a00400f141d280443d00810088204141d244669005800c0c08041109680e03c07036440500c0700b034000b04041ca10009aa4000c1014004110014040e10041d40b015200113014455038001079905807900c1d0020546211040d03001e29141028098981c1d04480901c08600303100c21941c80700750800c00300 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 438819064 1250 438817814 438817837
    0x5040303061a0918180a0b070e060304200312030f1602061527130209070f0f030c0516051e07060801350105040c05010503010b12060f040e0106031209030206 69
    0x2000400d20080b10031100000d80c0b206002103501100051801c0c540302c1200b08d4442d00420648041d0020034100700003180d01c179030303403080d07011060402c80e40900c11801c10800550303402d44110011002500480c0b0001c600500030f8102c01465171810200b4070000301e81e40c81c21642150424418820180d1903a228018071703c0040b038144000b030310185400007940e44044000301c602600d01040c050034449a00c03003441a07034001e17560385119a0304d400c010380304680703004a100d000428121820b02c045100790302c4a004580686460380c5400040040c00310303128070380341040d101500b0030341074140b44011034007a14400244103400b40000702d240c641c0203000d07080c0500c9244038032000302020b81400030040c04807615590075042c2215601452080c140c0c02014101c50465001c0020000451035600440a50b03040300c04620000345440c7c0103a42105c03625202034009030b0405101c0c950014942e0300c0d402906c031143c80d03c05c00001c100d0315508ac482030b61103529135003100380040c4041c20301c00340c4c4404003200d01d05040e9 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 438820314 1250 438819064 438819109
    0x91002040e0f0402010509151803030708041701061d090d110a0212070b0304081306090b0702061308030a0f030b0906010207050d26030105030d0e1003180605040303061a09 75
    0x1513000507a0030388110750300141e00c4218911002c44488000029050710340407440307007102d9000001d050540c1e0388907d043c040d01800c0280410008145480352158800e2405000440d103690707604860704e8410346100003805803a5040080088050041220710808281403a0806900110207040c98440e40e00080203030040342401c1203940c000e0070400c034150040580340c141c0b5541c0d103410704092149400c0410340240c508001000002c205121300b4881d82520046a882c0389031100d581e00708407d59011229886210180e04c100041440d000d00290201071015100d80a14183c8810024200c5000d40c1e1214403070510001413184a9a00180d2101a50030503585c0c510760b203025003098282c031441094803010510201541442142d4003d010714100d070000d4084840c0700c8109042900c0180c43c0c00e41607a04510910130101246100790051041520040120360301c5041076150b04098a500310f40c02e41c0030903100d84081210b91800111a8003505080e21164200840d210000f99007406000c0e0007840f03c041c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 438821564 1250 438820314 438820321
    0x90f0213291801060807170105030c0105031f15020f12040b0c100c0e0a1217030a020f07050a0b0c03040b0f06130c080604050c09030a1202120d05091002040e0f 70
    0x3101108284070b40070565a81d0081e680d00d500051030b09100b1030b2180001411005c0b001c64502880d8984c906030f4500801500352504680c00460b1a038000500403200320303013200e41800c034207290b05503810041c2542c51405029241022800f84c50300e10102440031699000d0000d000510394250250740541d0941128240d0724034040000614142615080d1040d06241403083d8170b00a8100040174184002503d40c514129502d0281c1c017000f04e40610007400507192400e906070482d0b003042c0296071041c080f50300103040c20340c1700d0f102e90040d800a04080b030b081d0307001d0349101d010f020394518280c1d4003082c00010249507152643c2d81e00c0d00900040d000703550924030f01010413246d5481601c902c4913003040c503000f044110765a500003410144180d80103400340e454031012400003c00d130f4048800202011300107100c885800c1c2d40b458102445070b841c180850090b402d03001794411000000304001602d0380404039881c288407104034149001001c003c5e041c1841004204400b04650000c00e17441910740304c0d040d50507503 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 438822814 1250 438821564 438821569
    0x6020703020c0a06052d07110621040b01210305130b030a0c030f0608072705160306060e010f08041505100609080307021507080c01090f021329 63
    0x1045007103641e012403c03010110301c096001020b08501d8180341c0c0c80d00c0c40402e2015172000400708803003090322512000c00407a000f081001c0032104006802400c0141b034014210f0301d0003270402e03104815100c04880c9100340014004203010550141a0104040614916224900c0d9001c507040200505000020510b4141d0211440c240d1000705011510749907a442c4c4005600000d01890817804042417400480c081c000000707104030310980d0109402000081d007011084603010000c3c0310542c800b80d44c465a002032001d8503005d001d008203840e80421020085040001d02a62001d8002c2010030018020000b981eaa11844200c1c0d40001030808042c0c644941c00d1450303066901d444000c9045040205009806c1b8184a5a178200d94250340c500c0071280d11010f0711502c0303108807500030707601010400c0c10072403500c654001080d1240c422000d0b1071500e840000d009082d14520482a00c0300c100c9144c0120550418003042c41520441d22007c00c4000b102c000c07191150842441c0c007070f08a50f825405040c1d00d4 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 438824064 1250 438822814 438822823
    0xf01051905090a0b0102010c020c03060105210109120f03020f031b1b0d030608150c0c100e010204140d12110a1b210c12080403150c031a09040602070302 67
    0x40001408001161520500702d401404e20180485d0042d8a44031307010303600d20b10120b11050561030090282c5140d0f460a020400d80320540d8007031915100e6280c0742205005001d210b80f0f03101320f204c0c80c2220b00031002104080e25860440c10a2801d01d40100300c0f010702da01030101100d034001000358007050f4400b0101c60490341c50149000c1d6401c0c0345075041c03190b5034040d000100600c2c0c00e0a140d82c2448503c0c0c5400e003154580714140d1000c00300000e0000810201440003024040d5510310300101e604c19010b00d608a415560f034650392080304c0e540010107200c403140c0380c2402a442c5109540070040384c03000f80d54121140b900070203030104012030142d40181d00c0c581030250504080d005490f0141603005820300c46140e0905105040040741400c2c0451021001c88041069464200c8003441e840c510740002c05070300b00d409441c201d429040400001c0000f903000d889030f24058800c510002000e001841c0041c0848000c9404080d824000712103030805a079968a9655006038050710142e150310305450240c2c9032 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 438825314 1250 438824064 438824069
    0xe0d0509010309140d0c0507170c060901020c0a0609060f0e010c020103050903090d061d0d3207030e191a210106020f060f0421120615020f060f010519 66
    0xe0060584482c1001c4e84101c08004850147c015102080e54428084003200c668100c40b1049802001c10702007d40f80c0800940402c04c01070050320350030400600019487d040c0c0d90000360100d660824148083c0b5445681c020015250341400500c3e9182d450010301a021b01000c024105600e400010754070300340610070b5440124015004050110f003c2c903090024202d031124000310315220b0704030354403d05000220110038035081c2d26060b18034400045215002d0304016001d4000c1c0e10307003800001c3c102407024010102d160090b510800610824410001c80c071000400008141c0d102c5541400f003000c188110691650407407078042c1e03444401782c403002c00843c0903c00c0058040815400000d0700780c1c0200d03c2880d844c4620065825650794400442e5400c2e80035107024100d41c5e980100c00b92000f000102081c1d90305001c0c106801220340114040d01aa911074001e50384000c0c000036005030894040095000080f003c402030607661a000c000314501600504c40e103881070030f0048030f9500d51168207103501c01 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 438826564 1250 438825314 438825353
    0x10504090822152705090118090213060806060a050619020118030e03250902091c0309051003020315062101030c3213020c071401030e0d0509010309 65
    0x80700144100c003818810070056401d640c1300342548810300c142082c10142c001d9510081107910247d00388100d42e0106140c2e0481c40d00d1040c1c1c1e40c103c0d02c000d40d48144214102da403000e4008102c441c1890300b80350401801904480c0118400b07502801280d4070302060701c40d0346904251110b032404050001b24003406003c0c2d980202075181c039003048240b50340722a5079620301c00142d040301c0f10880b00d030305010704001c940b002404100768400d9090040041c290000d00d0f9030f02c401003621481d00c0641c07403069440300f02ca0b60218049522008108014100f0b04070381c900000351401c046095140c0b0001c2680e01c0030325a04043c2c8200c800080d40e8140b41d200c00754400510203480108020b039a182c0c504100000c403940509888200700040c200e242c101c0a050b600307400e411200150300c40c50321100a0200f241004d590f5010a69003e201c2c42243c400200240c0380204402c0141e031514014890015003140d1501e12107411540003022807141060b08881252415802880d0000d84620302d41011070381024135075000079 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 438827814 1250 438826564 438826589
    0xc1d010c080d05071716180b03130507051203030a090f1703010f050f0f01030c030b060a05030609060102010612080703120f051b0406020a030c02190b0c06010504090822 74
    0x11203440c05500c1188240215101e11502d100041103601217120b084441d0001c2106e044003485a061094440c0102c10100c5603191200a443d28a82c05186d04115081e500b042280d034503070002e210007007020600916007640c00380700301c1603015801c580305d10006101d0864240c6030315180080091400100241e9030700041045201d10302062100c940780d00a2090059110384040040703030303515118488003440c0d00c0c010540810a6501d90054000d0090401440181569151548910348a003002040c40320000c0e075500d641c91602008020b0104005011241160314042c018068403000404681442d60812205031f02d0b95020710f0104c505d40c0010880804840c20300a54140305a0710741c01030303801404100b003512040c0c140510342000501030f078803411005070f20200e140401309000e0300e64024054000b81c621112043c40304d8131620141d0455000e031180040010301b150f5141c100380020f41c05010b0845003404418002d0312a555107010744d00c840c00313200c2803000305040c030f400160003d178004120400440b07 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 438829064 1250 438827814 438827827
    0x60904110403050106082e09060f020a03110f0412081c0b10030c21020405040207050a0b130c030b09150c031f0b0304031809090609060f0c1d010c08 65
    0x80d0241d00305100803200c0f0340c02c101c00410760312001328250b10301d00d02d0555400c0d80c000424a00c00100521143c18001a0f50384020b41c01c0411030b64012000b00004103070b000340c0e4030b80080c40e004040303800030411802c0011060240d4140482c890302102d04881e030080c090800c21001d41041c0000d48100351040610864526a004c03182505070031016513200111256000050707500070540982c0c005007604030024040c9185226a20503002021005480c4408018142502c44000c50100e80c020740041d50b00f94000e2000004100c913946100e507101c040100c42c5012410140c2c0c030141480c60134000141503800b140009820508100311000508a190360b01a44605100403020001d034415180c82512107028280708025407001a8544110b4001480052440e500e58400701d510a0141c0040c280c9100344040000f0041c00c24041ca500850080000103820401882c007442210468000404114100381640b00c246401010361040c100c001004411500c00350001200c0040098000514030100406d21 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 438830314 1250 438829064 438829091
    0x30e12130311030114060111030c06042a030f02060706110a030e060a14150402040f080714040e060621030706050a0e060103050304060c050102090901030305070203060f01180506060904 81
    0x500c0031a801407900d2210500000c05041c00e8407032117001c104818000d400032a07001c0d4894240490780d605c685c1c094a003411a5207481e9420000c041c0e9082d500b15158405030038032002c01c188255802050101c0c1d802056295a646000000003800f01030721441c400718405080c000c1c5900011160405c6411840e42d6980003040030303001b0056200e40341010301c60b560010305002074502c00c0e811036841068641080d0b85e510b00348091001c00c601010358000b902407000051603510440d4040103010303200068103201b800c02c1c4242004468500110b0722071760500d00d440300100c0010031b4031a0458010398504400b0320200b025000302c03644104088000b8840082c03003605104a0341d2040d800744d02401c5081c0082c400280e40e035a5140828000500650010002045564012100b10a01c98030a1001604241034800003c822180c240d10a402180000601c14110700e414800d03d50304c092000701512181d4108107a51410152903020b000101c0d540344040344c0c070383e51a00203035891b40340000c1007840408040000f = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 438831564 1250 438830314 438830347
    0x210d0204060804060f051315020d1d1606090b0c0c0303030c0d06050d1703041506060804060e06250516031e020a02010c03081e01080106060f020703020d0201030e12 72
    0x2400e0f10130600d0054560110300b00d9006990040d15880213030408000c1c16183c8451701e0001d003074840d0000341d00700301d6070000108500510f844154030700b0549250f46d03404454a81011008400394860980c255001d00625400c9066442510050722001c0c0e02d4410390711800f40740a00c1c0300351195040c071010080121100c1d02500524481c4850401488126030f554107100d400c1170f0089000304000000071010380001c3e0307140050342c1e005000304045d0480c43c80c001c10101c2203902d290070a9001071901e8040000744881070103107a24656180004001c02c1c5400c00c524503090310f81078450b094651020100707504c21842131003600c0c950042481c844076041c10a01e400f41129514984903040340030385401005c00e0301e0000c11301c42c0f80240c040c4c58508020507a550304903050000200f1760703425204540810442070796401107160180c80d13000b0001404c01d040003005404115641d000004540c0302000520068440b0b60807841119420f090114036000039481150404800201942807144003064405000840e0b07a07 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 438832814 1250 438831564 438831571
    0xd14121f0f050103291014072f01090302010e03010207060e1e0d023a080405010b030a1a040c0b0307090f050609011718031201030c050d05210d02040608 67
    0xc130208800786a0240ca41d0300403d550740f00a58903800300d10b0b07501040c00c0284011940e8031117071038004201c443c103401100030740e000f08005032940b90903401d0b05404a1a0307141c20740e0b01003415080070307022410114002440741e41a40802410089043c1032000662401d40545010aa00c00420b0100d80c4402e40815030303a400070b027811039030440800d580103881d00e400b01c0d4000c880340055000d003026000c1101008401c03148494407107401d50518000c501311008446145501904590f295811403d0030304105007520040d42205100c1e0704083e4542e40002c0d40c10f03107101c00b440d448109203085030307445041086480301c403a072248002c2c41c800400c22060079400803150040d98031805001515580300d40030f00540780554900c3c10702040c00c070284154101e4426000662007505808991b01e5132251011031800c542100c5019182c1d103c40c03400500030044103569640c0600020303100c00c0c010814a844d066070b181c0034006400d0425a041b0460700c0c00d003a12804507040010070350015561039035200002170001a085 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 438834064 1250 438832814 438832817
    0x2090414100b120c0c0a0b010e150a06050a0810270f020405100c0f02060f072006030c0705070b162604170106180504050d14121f0f0501 60
    0x440d002c9684207054054a0040650010003a09556040103244096000008034030240c480d45600380c000804590009000c1d003044940071106041c4001c2245504c012400c806209103104642400401d5004058a00448451030084180c1d1074a07407111216903041d8002d00c0c411112404030b4818000c04150300d800e040e08450041243c40025103444049010b01d0140c6903024044450085140348150200c440c903a018001201420000d030340014000e5103d40c0700801440700204a510601c14108002e1007081c080840802c84882c0310000a80700303200c0144115581c0802250380821300004001242c090099012074594541080704800340000480d80111420071840029003e9a0180b840b18912140c05101c00740c1854200380e000113000072600510030180d0750307503680040e40912414000502041040303000546040a080c06400c0c0600440f0343d00511108603511213100b035a8074100e0701c460700004003010054a600541c1c20504820941d44258000a41d00125144820001c2c81c41181d03400d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 438835314 1250 438834064 438834091
    0x106090516020607020616120f06050406120203070905090f0105070327030c03270b12070819020a050c01150915030302150703020405030312190218100302090414 71
    0x1c000d0200e940d0201102d9000050b04040041020100007810f000150b0100e0305240342c0c0e004014146400720340d0324101500d10507450f0304081105081510907e0f010f002481c4401c1030640e02c980120740c0e100c01034402c2c5246103079500000742920380140300c54040300e08290000e01c031300d06109000401610b582c6142400c1c100c400300340001d90310840c05000307484a6154482c50301d0749c825520107681d600010049030742c12a04810358280d00e03110514102020b4264403400790784840320714904a80d9032100500d850240603c440038003c65000c1000c1c0c3d5407504e0a1440056a90319805904460394000d5000804944d03003055441d03078603c41d58410030020395110b41d0003001040090381400200b070b20303103210240c056048842c6024084469030341c01c3c0d901549505015141950310408203103103a0010740600440d00c504020302c9011a10300741c45d80202c0c0d0401c1015801e00014541048840f0780707042500b445020122040c00455000b50151802244002d0080214590480c01400303040340803142946109032 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 438836564 1250 438835314 438835351
    0x1d06030901140a200307201006030302060412020d08130302240a110a0509040207050c060403050a03020c09250c380906071116030c0819081c0e01060905 67
    0x1400507030b44100346503542c0742c402943c904140c102c6c12501f10740034060707409510516252040d0b207014160042d44070b64000c0850349040d05090000100803140300007190043d504161520307034003c9840380c0240001b030109070410420328059180010311511805407a12034a45124005002081b4030f1094005c1c8205014180030310315240c0082c0710348444000858024800c0c5015418a0380c090b1072202e00c2641101c440e0791030710300010f070590400c0d4800c139a0303035100341c555908040d41440742070309031079043d42e50700d501d17040041d08850800440c80400c038400300d041182c0d00f82203215001d580d11040d0041080d02c8000c450f50349550784000404a00139000448a40e03058181c0844080a07120310000d5001d0200c0c0e40b10400103ea205520a1001c80d09100710f000d8803816511142d60103004500c182907101c40395140c20203080c01d05401c10854501c070340c944007501e804070300c4070340c2203c29040c0d00e0072041d049000400e64010003800c0e85684aa030542c60b21002050a040c03079440b503405101c10180c1d0011021 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 438837814 1250 438836564 438836621
    0x5031608030313050307060203010b31030f21120c180905270c0906090402090103080a0309061e0501240f030b090405010b010e011d06030901140a 64
    0x246a118800c040ea00420000740051660300700c0500700c0b4420350540b0b00e8010140c84004c141d80003a000208480400076008082d6410007220401a4540301b0360b180d9806d000901800c81220076100203460002c008540204211828039050320002d8001c0400c40d4a00c5007110003040e45c01c40d0048001c20a103030032400d4280034011010410503160b1440e035584c5450a050170703035026005c00fa2100c44548005201c5c0d07140b06d407080004400c41da03a40d000500d0f0360011a01002074040300a85158040c030785000502002da21500781460649802c240000c0c0c0e101c150240481c024034200202828061810425020341280c46541104082c240b50341440207981304c6003402000001c00d0300c000c1150502c0441566918040c01000619484600b00010807402d40c0021a4072a4002c403802c030303217903552914220102e60b000200e96000d41e5080c40c188500d883d900c001d04400408200c41e10f4032a01e40840060108402508400c0004035003c507442c1c01c0c1c1c00e0240c0000e001c0d14803043c0030213000700a00598132401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 438839064 1250 438837814 438837853
    0x405070e12031314010516080306090109050606160302070f0305060114010311070b0c04030c0e0601030f020c190f05030705030d0b0324070c120c021816080901020d0c05040503 77
    0xf000c1101000080e54a48242160003601d0029443d0512070b090000c0500c90f2003002c04014407501420505981746400701c2046100101600810b000b5031a0100340300003a29043c082d18111302240e602001d0141c070a0a040c2e16245a981c01348104000b20785021080000c0841d80d98102c9401c0c102c18030790a00782c0030054081d00e88401c402030300c0716420700221020401c001520398101d100d0140d06454952281c481181140d4142c0180789481480402e00645581c907100382079807501008002c40c04e0050140400791103042c1c05c070b11407802c40c000c446031074103101e2903051510384107a1000031070350f89031601d02d491520791f0008041907100620f09540c12000d8200801c0c0c41c62a14030b11094a005d440781090501e109520140408041042116655000610101c1c00c0c02c1075010507100c18824500c9441081000c2c0c3d000440c10303101101407410302c406e89200898414003000d07a03050030f010b10b62b03417625100d00a001d0b107c901d100003400c1c4020511007907001001002510b1040d4142c81c0d25603801108600d05 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 438840314 1250 438839064 438839077
    0x12010e06060904030503040b1e040836040f02090d060608070f050a03030f02010b0d060f270201080c0d0c1806030e060c0f072f18011802090405070e1203 67
    0x2c01e404000080008100400c03981c1d00800000c0001440070000c258449d040004075811141e400c00000c0342040240c0900340008100095500c0320400b03d44030006024040800700704900464888440d40050017442e01a43c00c0340b203024020710320300101d50030007101510700c51040105901821030085031001200b6110415a01d001d050035154030300e5564216100c956007072803a0219580c0340c285076016500c61000c440e085002e030101203100b800c0c40c400f10046450800d4228584c44500001504041404400c0c105007902421700c0c048681e0350000790341c424400c001003214006d20b0094180d01c0c4581110b450741c03100e01c012627441b0b111030f115032081e4210380c2030180a010f5039104500084e0851204002030461054404509061415603550072341e028202c00050660002c034031942c03000c5040b041c100401c04980031100c0b64503013540340c000c40300b01782018001c404140144c201c0d6072085801980440e600f41c4000b4104001034a01540d005040d54243d196442c0320b6031344640541d4075000004141d03140f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 438841564 1250 438840314 438840317
    0xf060507081903090f0c03060b0a18050403050f0f03010f1a03131119150c0305070618120c020907080108070b03060a090213091103100e060f12010e0606090403 70
    0x90070440414903802c01d0000710000c002c040d116904200001d02d0320a02405031841208241c1145042d480e042095030707021101240144803103401004a803c619003040c0b140c10303d24200003801c1d03e407820121100c2c42059410030b401c80300050603180c1540395100139412a01c400c0d000c7c0300f0a58035000c2050700b040e007220003523000d2a003d2000c51418220ac0c1c0171491054400d02441d8103240388003020415800c0303102c2e038001c0071954640041082005118a90a030034005243c0f03a0307050702441d98044d00c103000f010400b80959940d4920300864821060414000742e400c400c201200d4000280700401c003444800d0200d0080c1c1007a004200301030f024540c4181038406103006050900e04001e907101540e040242865440b43c804040000c60a50701d100500800011041e250042130501c0015801d45241854038540c46c1300400030000101c040c14540400c0c0c80d00c40c6030142e06030711254005103000c00030f985060340c003600112140c1d01d1031031b0540c8007019244040041e500d5603170740d0700c081100212041394040e0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 438842814 1250 438841564 438841567
    0xf1101020403030c3302090306012c072703050d03090206090f041104090e070b070b01090905010209221103040c060c0519110a080624040609020f040f06050708 70
    0x400180c5c1c1800003c1030034804002684801150b150b0380383ca0035912409040050350003d515078160501b404003901514030b0018140b2009289039242c94044000b56005803900c07010404118601c1c400e004d00d11064582002909801c649240940c2441c08180300c00c8500e84103030900000154040c0c040c3c0503030726800400e0b417410107000c101480303e50500300100c02c0e449590f8040c0c0e8220058240058406000c0c0000000740d00d0400f600c080d0315000207600035401d08042842404009400060303121305444d01c020001c01c4140091070702c640680540074809901c07001110405810a80c01d00881c50380c003058110070b0001c146001c00702d411910003520050801401c11030113100c4d180c080d0020015030ba100e00100c900e034566801546140c0d041310310048490207010408202d451030003000c6c0e000038040d240040c210a0074034130100440c00c40300c100302142c1d030101504960750680d16540040018900c045c020340d643c0f580e81e802d02d00907034003a00407540404042100450111700c9441514002684258810b = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 438844064 1250 438842814 438842837
    0x1210303110f120a060b1c09030c050a0b090c0f0303090f1804030e0415120f14070f08010f05010e07030905070f1214060907060305100906060f110102040303 69
    0x21030181841da9190500c00c8410003005810a070910001d010070052207681d45510704140300c1544c02c0e15016032285982d220244064290f036094001c0041091604500000d52a583d61800381d40301c20500b42d000d00a8007540c1e4880c010b0041d607070007141c840c5d101e40007980c44695401003002607404c5900130280e0558014048008035061409401200c04001008034501c25800c11002d51b07900c80c201c1c1d0840014081c1d2200451909244c050764042103d41040031035451304041081e00e82c0e100100e00600240c00f0300456005001040e42d05a01c2c00c0c240d0b5040d5820140c582d0289a2800024071410300c80d50b10303000341441d00c504039204480c140c0d11616404a89a1100c1c04120042c0500340303026100740c002c4001c001041026800c550005001190b424070030003c650030105a86126404442d1158201c01c00700103c0750804100082516168100020b403500c410310608441c0591b6048200ea0511f85800454225003200600c4540c402135503a44031464044082c042c01d0b4000d611008001c02c2008605 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 438845314 1250 438844064 438844067
    0x40605040c0f06091806031e0c0b030105130c0e1f080a09050c10020102360a080705150705070e160e01120e010e0a210207080312040203071206020d05012103 69
    0x85c4078140324034000c04550207450f912a07001e103811200003c4050520b02d06a107007086041e40088e030003000301c0d0103003504561410002c240c900d082e84940988456481c1504405c29000d50164610041c0141c4100d0a8442d82c2c0300102002400100045c0869540350010380300340fa00307000e084512a4008060309e580c040000c1800008540c1d0240c00c004c0d5502030201c5c4c08103c0d0500c440c0d001d0703100c2e80554070802c020b0307212201d10020044078905016070541e00341803152000c0010b000d012502c1c140e0f004e1040d00143c00c44072a640c051040000c5c030300e0040790700004072400c6015000b070040d10000a005200c000248050356100c5561400502203944401e10707140602c0168040c0ca0014501030011841060340c0e4000c5041646c4d2941c02c60300642c1820f40d203071003444031281c40d481550360f80c00109419810000090369034014500460704c00e901000000e01191001e0162000504404107000520b4119203401c00c061b400004c0000401c03407900300002115610071218110700d00d0300c1250300500c45031a460 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 438846564 1250 438845314 438845339
    0x6070807030c0206040801050705040510030b031b1309050c011407030906081e0f042d14011503061e050c030619050a080309030708030325030b0405040605040c0f0609 73
    0x1030341d1101e005c0c8000600b58400707004141c4111843c0c0d5400c0e54441c02c10040004100807090560201854262543c0f10740e00c000400d01c02100c8060600c403c0002d01c01c00060608010304003181e0841d0a0920030000c104000409556400d0300340c0310103031704105581c003003102c078014010044c0010300c10032010440b140c080c91600d50040040000c00341c0d0950902405401341500b5900c191010001c001000300303220700c1000c20a44c258458000085450703109104040d1069003004c081c000541c1280d00ca190b500d000d601c40d00c0c144007010090038480d552818140c00404402c00f00703075084845100003402ca01506e00c00c0a2007403014200709410340e120202441b001041807520701001200502020036241c0c0c0e003407000e000815490340156501c280003414076041c070159611a00880d0300034006c1c410420b4841400c0d24070f9501c178040070a41c903800042e08030094508406040d400a2801080c4006c2c00102c1c1c1082e8030550040f01908005079030340704a2524070380346201e04d10004400f51000d2125028001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 438847814 1250 438846564 438846587
    0x60a0b07020d12020c0901050a1d10080d08180a0803040b0402030f0111091201020c0c1201020f030c0c061810020a230a0216061e200106080c0607080703 67
    0x500381c284942c0d80740e840c08203143c4040d07101c1c005a4040242d41e4407074a000d02c0c0c4036014140603640001410b240603440070b45082842d51081132041140e0004141501101403c03000f03140705400c54092904e1034001916140080c1d441440010a00b0702400d294540061140041584107458619559aa480302141d11202400072a4980a41500c031408170009020342002c8209450301c1c0c507a140403843c10044d2840541403000503503401400800303034088002c640743e80000000d50b20012034918506900d4028896014206c01840012080c0840c40101002400300300d1240f20031540242c880044101c0e6080c6007040380c00c40307076001030203064000b280398011340352600c0141018540380091018002520b00f08038040c02810390040340d221140c550400c01c403003c4481d40b4244280840c00c10348001d040700d070350800c02200300b10602030004010b403140c02307050620025400c040e0040c00090798010b001e412a442791101c58440c1e00d1145840e840d2030310448141540c0511002d2070300d8025035050700ca0400c400d = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 438848920 1106 438847814 438847819
    0x50c0307030f0e06130206130e100608040c051216120203060f0103032c031912170a1505060a0201051b0a0c110402090402070501050405010c08060a0b0702 68
    0x4c5690340d01702c0c1450b090007020040350f0011980a124541e40c20100350b407580c10015082208106180c09062000c4658044075540d1500b00c030456400e49020b001c1c41d000071800c0186241050910581c01290f40594004604500c40445e4891040d071245001881c880080011458140030607640300001d141c52002650640d10010011a1340c91b440d01400340100155000d10100c00b295220300600040440e4200d002c01c1d041c000c40c1055481c022615107050080d200c02990103094130021081d028080607031150f40c3c012648019241c0003c884980d1002400081099100c0400516240801d6000410b083c10300707520f1621601e441050b481c0207a64207004031400680c0c44503c110b001c540004c1402c143e502e54200180003485a000c400c1c0e4030520002e5441c0401c04190009841a4041e01c020010803c05000c26103c0710300c12122194840e081c60801d000e004608009000f105001 = true := by decide +kernel

theorem cover : BRFrame.Cov 438669064 438848920 := by
  have h0 := BRFrame.cov_init 438669064
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 438669064 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 438669064 ≤ n) (h2 : n < 438848920) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
