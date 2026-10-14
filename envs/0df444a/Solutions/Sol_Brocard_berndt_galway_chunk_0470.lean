-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0470
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:58:34.162639+00:00
-- url     : https://prove2.me/submissions/1da078d0-5842-463b-80ae-f8898db462ed

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 84352519 ≤ n < 84532375 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 84353769 1250 84352519 84352553
    0x30b120c031f09080301030c0f0503060c0a03051506030f040c210b0402030c0a0e010504060501170f0a0b0d050304080606032d011d1b010311040501030b030a02120a140703 75
    0x5240d101500300002c0000300743c10f84000c1c0c036200e000302c004030070051524541812200a0203c24114a480c2c0d004c150f1902030a03240d02c0c450100800c42603903160b0080d041903510000c008560b140e00f10300e017008203807254800c0312580e6130a0001300030002000104c407440006080180161014082c54017810500411201c0c00a440d0054080000d411554104080c01c0d60800240c820074a040d5602200c3c1005a420301620344598102207001c40d40d0351081c007080396000b107110b2030707030256458190008200060207408002a5500c900e403514064603400680308141e03100c1c0c8000d541c1d6501c1c0402c41c2d0f0624501802d040d100c0d41201d0320302446034029012084c8054050002d1540c0c52041c00c006500500b07200124034034807034070701101c40f541010115104403500b00034010401025038103401101180d0403540035400a82042c08140155440307540302d03440c4060041c00f12481c603c2e043d0001402c0c0e0001002191480d44820070800400044005011a5050602c000c0c50540e0641e910100d0201d1040c0c80 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 84355019 1250 84353769 84353803
    0xa0c14030415021303051506060f13080708030711062b0902030123060306040803010b0d02070204060b13080c01020706080402061207020d031103060904061d0d030b120c03 75
    0x109062100c1203114900c084030340c030b01c215620040d4020944140c0c40074031050359580512800715400c0c0d034030504018803980c00140618504180c4e0b07500e941240d04a10001c450891b0808400b0411450410040010b006481c0045d03880e040c1c1c41c81c01006114a122045000e441d051001038104040d151460050f081400c10a44203e11410241e00c024031840c80040c2d85907086c0b078203000183d90f0040340b198006418196205103a5203070000d05554100944004140302c0003000100201c1d9504405442500d40320000989000603a40004041d20051740182500c400001134a13080607072611401401000440050200010180c0010303441354054420300044c1700000d03002408550b070750400c940e80800d0040d00421142042040256100500409580468603068100e501078100005580c4141030003494040155107550750395001c6d000c607a140a80041004080c8083c480c0c0910007124050040c3e40c00180b443c1a0008101d00c0d0f0712103e5900c681034100801003100c5481c04610040582c0307081c00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 84356269 1250 84355019 84355021
    0x8030a060816060302031e0c070204050f040b04030e0a09091506050102120403060b010c060903020706020d030603170c1501090203100902040b03070e121b0306090c09240a090902090a0c1403 83
    0x241e031f8469040212852090000c460402142026030000f414419000b550104859616440c01110b4904142c40161005460f0070018000900c100b4407410a0b84001e080c607100c4641d21050401a035001810032141000c800d0816142031000d88030b00d6008013000d10003000480c40703c9041011a101d076004c042e003203e84808030490642d015500e140111a4460342c1041010150b06000351601094000c010050180c6450003024034441c0c05a070050381d400003001c5442d010782c000eaa03065940140c0c00b00119001d0307001450320005c1100c44a40c02080780407005641c0340b030725204102d036003500c98002000700380c0305100c10b214200e4980144c82d406495030a0100e04802d1500014003081683d20002d044d034822075141d031074004a07101050305856003d070700f100c80903140c2441d05511202450a210740100e014000a05030800380003042d0000c4100d100c001c40c074401102c0104000c1511030b04130300b02c0395840301d80301c03403c40c20683c1c0420761001a01e1300800810020307600080c14a8094a070602c0c00c1c4030040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 84357519 1250 84356269 84356281
    0x112030518060a020c0406090b1309050c060703020a0507080111040b070c09050705040306050c0313150204090c0c0201180608060f011101051806011a090d0303090f08030a06081606030203 82
    0x2540500016500401d40da843e000b0040009540700351001d03000d0700441c01c05000044521840c0a41104071900a002c034203038100407003100006110fa124180d030184a070b080603510548856006098282c0aa800b42050f0002d0b8101035143c980c5a43c080c2d4403582c5800c100c1e85ca00048101509e003a12181008903650308010f0921076144481c80d0010ba01d40381c68407040c0810703903422900800842c1d224000078041d0b66a181c0702041c5600040b20480c83c00c00519000c600061951010b100c40c81c802c000c3c0050415443d41201e40403a0300801500e0041485000e4500566800850b601545054201c403220101d0810782e009224031030281929000d0356092184030b00310382c00742c11005508503a80008204900d8202110780c40e103a01604904160b00035040086000100103000c0d4100701480030740c440c81c000209050001d00c03034150006800b0140c1d00e6003440c002801602c50891071a00071034104c4e444c0e04104074600121145a48604054bd002d440c2c03000448441600141c1210741d20309006850703903905 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 84358769 1250 84357519 84357547
    0x16050a05030708070c020306090606040f090c0b030709090603030201020a030b0306060f060c0a08030c18010203120f0c0c0109050a0303060f05010c20090a0207110d0f060c0905030a03020609011401120305 89
    0x1641000f907044c01230f9020007418103400070f20140b25186c1210b00380060204103a040080ba1029000500841d4400c0b805001c1a48800002c5804c0006841c0000380c503070355090404225403a603041100183d40008414541c1a4580204805980124090300711420200001003015061a0805010318804580300c980590709100055400d9000b440080c0d03a4540f05401004507403002401210040c00362090207400d510000c151003124910a11012013500c4038a02400d02c40002050314910070410045210080002e000e0603428910420090031850070a15019041d11400d40043d14020380c041c1040280c3c1c0e9108401c0e8400c180c0001100b614901e42c8407420ba5101460345050760000031900c01c0c030600851076802071141c05c2c01121224401040307041080000146440302030480040d019800000c14160751140c001c2030b109042203100e1694603404a4145100c0003826809600881c080002c411028000e400c03218038620000d2800c1d60600010860386094103002a0400001040440e0324000e2 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 84360019 1250 84358769 84358787
    0x308060a0b16140f1e01090503180604090f140906070e0402030a14180f03040e010308091201180c080c010c03051806040f15030506030d1b0b04060516050a0503070807 73
    0x3141c4195003465080070784d0b0555401103440c01c94542c00644c000f0302c400b20818860364015a074000065480e0110700d0712003511411540740705d1907000310100030014002c0c80328407802810f2100000c007ca82c8102110340c0005207100100360f8940358001c5010854156402180c0c075800078800c440058a90300c3e02031143c40280910000fa00b4903a06800501c08400d400140411864940c00201e030304076140c6440c0c4644a024910800241c0d08140005000182d02c540240120074000741441c555601c8040d402c42c2556503080401d9075241082049806001005203200042c00d1228020160a81c690000034540c0c3e40002c000b030b040040204100b16404034920f0a0140d00c6001486d698403261511400d004a4030705100340d4100c07034000e01c6451017183c003c0c0030b018440c4000030042d122041e882d1102342c0c0c000304c03c151703200d2001d4141e0341003500113560400c01e00e010724051100055503203080c0d080c0640100d4400c4200c2e050010511200090681c80400c8a40c40019481c1c500d18079100d0180030f44100310 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 84361269 1250 84360019 84360053
    0x3080901030c0e040c0504150903050d0c0302100614030c09010503071e2304050601020609060a0e030903030f0403030f08131104020c01020304150b12120313120c0308060a0b16 77
    0x10034480f517461011b03806009003040c0e03a24101c0101d04219400026243c1828a02c0300034804e070481034031240e01078008c4c101d90303103400d000380140c03042a1a411034080c2143c00a0304241020280300041d564541800c00c0507000d0300000307036841d410325410710000943d03904180c400c0300304410b02104111100c07083d808010008083c600c20090380002e00c00d001e0241c1c8001c0c0004140158a04000140150700c0011503a0003100240058002d0791500b01856000d084201e084098501c001c2116a4440e24204000c014480011444503221420752400500c0b06a00c0d0201e00e003040500c800b4020901c0d89641e0003501c02c1d0b80a00004104040b8a0100703010f801440c0c14039030755510200422044c8060000d241c0711403407414404110440b84202000800c520f401c01c030a005500c4070020385401017080b0001c54001c518040c80403684130b4581c0e0354428084e0504401400144210050020140c010b0b0015801202c111901402d4078140141100303d4001c03581c0f0300000d4086202e0035000e00c6403c607c2e40c54411 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 84362519 1250 84361269 84361271
    0x8120a180308031f0e04030e0109080703080309070602070506270a0909120306081f090c06020304060f030506010e040c14040f170a0525080607080702010c030603080901030c0e04 78
    0x241e60380c00d0000d45a001110708009103909042d0301c180707410340c0c505014281d0309030300400311503901c541d101101c1600390511400e05200e408280030400e018100108401140305201c0310b0fa41b031500007059424001e440d4031076403d55001c10000c1c403080da51041500d802084400425079038044030001c03c0443c0d030b10007a50580008020501080c1d403003680d0070035280c02d03005801c40e07030090460710f100f201100c02c2441420010f42001c80c0010305960302d101c4c020405441c0070b8000c0794170002d54956900f9984154880d001580c03000404021664002d81c8503007445109046c200864a0f2840001e040c06e12031141d09445990341d03c80c90840540107030100c45900d042c0c0720381e40e600c0b5500c0d401c3c0300910f0780380c40c01644400d01c0c01180000c1018400121040ca0341d81c014090312000c21290450b0400301e04034804820040d10440c8007185188040100910811066440e05018203012001900b1550500d541a042500b8038030300b80042000d48089520a54081c43c001441691884084450541085141da401 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 84363769 1250 84362519 84362567
    0x1140d1b09080c030d08071803081204150c0c030c140d020d02010b0901050a0504020c10050403020312010506090102060705090a09090605040b0723070204090605090f1608120a 77
    0x2940d0300048440545480e40b0844408002c0c07003040640d10403580c41e00000084522002501092182c612408a4103080315071002050302c03070f0340303180380c9070415011601d11000703440c100028480000d60f0714200d8074010a0030460342d000c1c441c0003851000303004d03000f40500c003d0f1300399407041044d000488100202207000307807114070303100200094850100295810040d0300307000c1d00706454a01107481038101c0790010031001c4101e24003410712020390400c0010072141c0c00b4040c4902c00301c8455010343e501c1a032080d4040c0d550341b508140c5000c280c07001038205074000c000c240300d00640c1c1e90f00014565001800ca04003507841e00444400600040c016402070f052040c1840150350400034941c0025005910030106c9405c59607903040c00321412482400c01c2c0a1040380149140113200440e4010a080d500180c8045024005611000c09444043d941c91146500c101029040e02d80305204021400c26910203c0c000c2c1e5203420f00c503030381c2d074114918032180d002000900e0b03d209901a466081c1e250340a2108107150b = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 84365019 1250 84363769 84363821
    0xe0103032609100e0c01020a020f0411160b0c0903031204050c03030f04080105060603070c030e03070b1204030e030309030304050f0d0609030503010608010f0501050a120f0203091e070501140d 84
    0x40702090243c0841840c1801d2a41109001c040350050602c101a801400f204d605902080026aa11407040780c00581c1c0e00c160161030f6035003000401c0350401a03115021050210f1404102c0110001c0a0004000c2d0604c118099641d0100441c0c80d460b07014100c021047c0c40703a081c914100045138615035031600c00002c800d06004c0545000d04120f650b61402040151b40d407105002c0b40f4401100c40000040d0f01089480000c6e001c2e00558200c0c90700603007210212a150a61010310b0351000092802c0b50001c2400c0004142d40451401620784090740a182000641c0011036070f00c0c015030044522800d019a2605000c0e25855882490b283e004070041c03101046905010700f01f40c3c001e00541300090110000401d010340c3c0d00c8a0402180d1040c5d4410340740c48143c80341220b104000a03642000e0b252140b8240b84100c910380081d5004803040c0c0041c00a0001c1091342c1241c04071052070070003003074004030b008102036a00102404130f000c14480805176101039107140c603001030a6080100400500001e0300000e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 84366269 1250 84365019 84365023
    0x40501060906062d0203030c0d0e0a0c05120111031303020c0607080a11070303021507030b19050103060f03080d050705070602190f02061b0c19120305010f0e0103032609 74
    0x500702c01d04141300808040a452084459841c1c2c3c552801507442000428090340c605c1c40200101b903c07245d0000b0307061000401440c00d01080d84000c1d50341c00800b407424095441d03c0a16050700c081d0b040c008000d00c2031558100c0c503a50100410000b202201c4807001000c2c1402441070303504000004094550b01d00c401c0c0790981c241e0b00100000d000140b18005102d41203000003443c0c0d4160380d0980c0042c112036030b08160100511600402060825031500f00343d0030b1035103e86050b400c03603c6428900c540c140e03080100041c1202c215034000030080c1c004100410204815004684184440c50b8001c941c40d82c910600340c400380300d02100280007a00c00100c0642c00301c1c0006440410f82110b6076118580b1000040882e81d5002c00c7e90015104210f62450990900c807050041100007603900c1a07452401203040184000c003843c1c4e8054410070051843d9140c242c1d410f120312409424076894030030100742030903441c00020005000040030300c80071043c0341d82e101d0000071007985034001d01d0303620084919109406c19 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 84367519 1250 84366269 84366287
    0x9090b010f0e01060c1e081303030e0303091302070c12050a06050105120c040914150108100e0601060507021504120b0a2f0d05010b1305030109020d0201050304050106090606 76
    0x800c401c1c8110001007900007103206603a040381c1960303980740202555500e5240303032906801c01c400d0b1107101c055603100000d10440d019041c00090b49220040461440c00c0c0940a070307041c401030600c640c00c20030424146a45800c101c4666800c800001030311035140303180400ca008482c0c5c11000f01690200002800c02400180c10346009200e000240101c4e6622000c2c0001d00c3c940c2c1551000070303041103240b42d01030b0800b50f100c0b001c40303408ac41700c0040d0110070a039854209800e10403003a180920200061220260401121402c000c0a5400b0408400900c00490700c500c818001c04040080004030740c01550303a01d02c6480d0132001c8000d000c60b91155141c812040407404828101c551403600400183d001509205020f441a80e058100802e10000b2403204941c03450000c1054000d4010720203025003d00303600c80e243c060811381440310341da2041c071020070251204a512991107617051003074110050b01c0391001d96003800e5080c280b1544a455034602207001d005250007605545103003110000f240355024480c4 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 84368769 1250 84367519 84367529
    0xb0301021306030c0504031106070201020c060c01062c010e0c2710030614061e0316080f07020304090e030c0d09050f030a0209010b160501110301050111010e070303030c020709090b01 80
    0x800034044013480c10349160040e880050440300c20303015492820300301040100011803051043c1c0d1201d140307010010750780b40c10480c0030741003582d9210303014008040d200306407400c41084055035006004880d5a00b610520b014043d40d81c00f0024280400c14032a080402e903402c40f0841d6019000d0203e080b1002a180408030040610490f682d00480e88043e0291040c2d1080d5080c03070403041d02181903c2c05102466000d40800e001818110b0141078842c951100614003d8034480c80c80807803070040e4400202415009409204034900ca0410b004c07100d0b40000480f4116520502c0124003514024042411406a028284054050701d4404a04594072042c010103550003103038450038884001050541e904045030b0003d400c4412880184408103080000d003a0b601404241e42110300100d54500d0700f0355500c0e2001c2404100080010700103580c01040150355001058001c1044450480310103035036003d0341c1310142c1419030340c103400300d6618400e01500c1c01401203042c0a0100c2521480c1070a0003450034824 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 84370019 1250 84368769 84368771
    0x61802090a0f08010227030c0906130203010305030403020901210201081008060a1401090207080301120c0b04060509030105240904210801030203010b010c032118110906100f120b030102130603 84
    0x911b01640400031100307901e8910103001844018070940500c00c1c440d002614640d030120346075580021940c060b000844c003a501c00e00185848030324510601030054410381003040d214403200d20808408100c0a1010701041d02443c110106480d170382c4c0d17040078011031a0484101401003004005401c034458129158448800320300180c146c2c0d94400b404100d003e1003200800800e0b04000400c540320a07203a0b4103420074041c182e5000e2440c1e4400c000500d55115074011800300c0d8000c0390b428168502031050355440310030ba40300c4000c02d8801003117000354a0b4050307020502c07615514004c035040c031040e030302c1446014200f500c4485d0207204600000d0a1b011003488201c1c40f940c00c0075540a010351003413192a041036850349403070588051101c0c120300c5400814102c81c000c0c80d0f0351449051981450005101e50034092901c06518007001003d11243e80401400e441c010450b1710000094141d116401c1d20240000340352410881c154000f48802824041e07000951541c00031800c00070405105141d0000c1380c9441d14 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 84371269 1250 84370019 84370057
    0x504050c03030c030706020f0c07150306050603040b060105030a110c010e061003080f0a140403060902010813030203040605090607170901020d0206060d020609040f060303031d01061802090a0f080102 87
    0x410542d0741d116414100025803c14000f0300c0c0090034039000f1b0702c212003001e0b903240d00340794a02d1122032402d0000e03440000c1c0b44e039200f143c4521868140c4a658060700302a100c603491407400d80c80710b03a080e01e0060081810801c0010004640202e01d6110140109010074171303e03910252950309074081c1c654a0385440c014050b20f0301281100b4080c454401c2201c0e409640390742005129001007060780c0084070032905120340e00c1c640640c0e02d140c19000b4005544030b00000074900445000041c100c4030001c01080305442039035050000b0230340000986085444620701199101080c0d03001c1602d41c0a0964000c0c4030391522a1106030b500e114078003911507000207a08891007554032400481e0340c0e1006131242c6402140c814481c1d00541062401014203040242000c0780811034405000d0485000d83e10560000c2e51342c00542182001602c481d10000e0198002480741501740040c009240060401c1c142d852580011000a15141c64160100030808014070354120360703541d032400d030103988031400559014080300 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 84372519 1250 84371269 84371293
    0x15030b010203091e03030d050a02032401021f0603140a05060610170a02040e09071a0f030a1d120c07050a083403030903050d1403130c120303050405 65
    0x402d07141e5555004110b00d00c4c2d07900348030500210303992400c2c040d50940400c101440360320055000d02401101480e2006940b46403540314603002c1c035040d000c041000411800f80512586c0c0c0010040e0b401d00c0300e44c610203400500541c4800086c8001e61004020740703408107500886c0040407070810382e90f50040c016680742d903480908010800300d121000360080307000c0707610800b01c031611088450350200d20408010318041d100c0180c40044032003180d900c140ca52101e5400d108810440c0860b40c000c81400001c103080c01800502c020060000a19100c101541c0d003401d445426101e010700440e541c04501503403a00e541d98440441c5030762040361528101d21807041c1c0090035013400700380f28040f1104800684420744000300303a201220000000040d412000b800c0c1039100103c3d00000600440c440d031101c000307080c0f0318a40a030918943c91a10b90a0146502c0368100182490013229072103144064039604a090a24000d04a641560088044044400020001c1507010780c01a4010340c0506c0442d10500c02c61 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 84373769 1250 84372519 84372523
    0x3080c1b06100632130e06120f0c041503060c02070905011d040b0a060302040c11150f06060703091203050706050a2009010c02030d031d06041e031815030b0102 70
    0x2010302408078040305900300c02001d5100d85040e0300c4c22511070502e071401c211110b0508a503e141c1d04081c07404007491090003800d2070b007040b500c042908140d01404040c0b040d003d8042c0c9a000e0b0000c242d001d10345894610090b28103d456130b0001e590302000811070b0325485c40300250345d81d03694011002c01600c0d210001c142104001481a1703034612030980c007084d07a5259940d1011102010748500707081500c0f5003004c030060b030351405001c0a10390780756102e1014240592031140b42401400410000941c100d083c4540070300d41c20403150307000070280d44040d40c68135036140840305411594007024120360710325141c2c01015031001c010418240607140a100c80d850b910200421909403004084085252141c00c1f408080b14201811030050141082c400440301ea0300407904142c04c0d2040c490000e0354034800824089043c1c21240c500a200100409007071170156034000c1902e080c28865141510718076442010184150185c421042e00314215240340755035907403c08065049c005050010a082005001c115480 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 84375019 1250 84373769 84373787
    0x71b050c040f0209041a01140c071202060c0106090c0f050913050a0207140609061b030c0706020f07050109120f050304060e0307021e0906010509090403080c1b061006 73
    0x12501414110620350204002481c40d2901501c249409000004071540e952040400780018981c030f1020444d45c11000500d01c1000055a41c00c4201c24070001144450004480e020380305d174103018404903011307400020441d005001c018071066003010004149502d1541040118042035200d00c29080f5182c6020707542401120302d00740c0c0041c00911520085440c40e0425030700546104001403905410703454003240501c50000d54000355101c8014017081c01420400c0c164000407811802a10580d050124981444043e01d041c004000200d0410144403080d412683c2030700603000c00e1503445840e880c2c614080c1603502d01c15943c104211351480c50711802020900c41a084903075131741d4956030300c1c1e503242d8005045030200d1211500c01405201d00503128040002402410710564180c400081c4042100c02100108110304118080c8100492a21407203140758015070715040191440c2d813010341103c07040c000d41e080b80c50703030142080c040084c9600c049000d5000e500703034060142d2090b03102d140a0302d043725 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 84376269 1250 84375019 84375023
    0x30f05040b121b0705150a020c0d0f020102120915090115030609050703081210060309030c06090f1b080c03010203040203070e100b040b090f090907060e03120a08071b 73
    0xc04000302800e0b010540d44840e4031041c0d2440c2c41c00da0000242800d00180c00c420300890f0158010003000c4a890f9001006c00d074480f01000c03003946000341406405444806035010a018000a1140e211245000307406650714005c00c3d5989685900d401c04506585110349a01c041d100b41c1d4110100714580410301a030711181c030350b0f203078410342261550f6217443c01030050620a076298084d4207004400600750344001e00d03442d90800e0344d9440c54200a1128103982016a1014092514008400c00041c1c5c00601080314290001c20008001d11141044c2c06c210044d903074020081100a0301d4002910100300c1d80300240c1d60b50388101c505005081c070500d4200d210696001e0b5050f400b4560400020310f00d15442640700f45c003910310a004650341c01c40c80c5207642003034028030464100800e080e0b802e420078510006222108850300003081c00c100075031030b4542c2000d000b070303004008a9000c0fa81176910200580f00000300c0d04849190b4628800a0047c8240025144040014645520b040222005400100400e5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 84377519 1250 84376269 84376289
    0x30e0a020f0d020307031406010501090609030210110a1203020a0f091a2104061a04020a09090e07170705010f02070e01140a150305070212040f0302060a05070b13030f0504 75
    0x1070020000c101060401020481e0b0502c241c5030040002070070400d0002c00011240300a2009504003000545559100d411490400c503c1040800c0541e603110b8905c880001c80d41007020a4240c000105400c00114400c05001c44c000d50035105210340e455402056482060741e280485400380e001c4c2201c03200c0e464400d40c001030540f06000c45001100030009c160b1080750005051400d9000c1612521a80007243c09035400c550b900690320810340b42d4109441442000c5a08500e80620107002600700e12550007030356940c523a120780e8510036000420010001e014003006480c0320008100b041035880f0510b0248600207514141d0540e2414000152802034914076244400c807a030908803040101e01066041c9644010300520005402045000c0030346c2440041e900483e17645416180645855408103651401300000c000800425010401e00c000b6281e0461350680d49401d0b0403000c6825000c1c1000107408c032488503052000380d140c0c4100342500c043c82a110101c42651826054895000300d100704d103525 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 84378769 1250 84377519 84377539
    0x30c030f03060414190606050f03190e0a061b02010507050f03040c0e0106180806010f061101021201081f0203070503040f0201020a060e0706090503072405091003090201030e0a02 78
    0x4003100002031940054068000102048002c0390001181c9040e034084c02a1840001070381c3c1400e41a00a01010b4805420520716160041604140503c0010a40200318a00e040116913401e03607900410400808a4111801030246040c8000141031900125840000d4030110012207801030149034803a5007940c64250a203800114400d02e03651000b44119152101ca01c000304070141e807600c032940680380c3c41d601c002c1403a1802d86200d038980c24030b0f00030310700d903920000c010001100a01400019240e607407034114800d11640c42c4181c00f90160400001e000750a4000201d0101c80001e40e68819070440c0350009015502d40044100300e100075500440054020000034001c500582c440d8500c00d0701c184111904903c0c0c40e2070310000c803144020142055003103940c003008841d500c07440e01c0e40541401c401a1002510f0b00e0400c0c0038802c3c0201c4d024611020955001940300d000f9401e460150f140a0300250700e814450800400810080034101d003c60f141034000004d10300d0003d0004100c50b800303003501181c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 84380019 1250 84378769 84378787
    0x33012a0215070501021602120c06030612030f0406020f070f050f090622020a0906050316030b0109031203061d060a17010f0f090b0106020a0506060607030c050607020a020a08030c03 79
    0x110715800039010180c03808001c2036000440034030040144190303103003900d501d005a602c104a0150b211062844031a440300015a80d6555403500706d0303030000004c99400184082070004c85084d400303205c1e00e06480120100e4002509900803544181e045809000e85441ca40c0780c00c1600c1c100310440c00b5803a00607900d52000005810040c0c805a00680c0040c81c40d610100300301c00c104001105070000e10000342c0c000c80e4018225401104190280155050039404c43c0707000424558010070240081e41010b4031510020340d2070f40500c411801843d049a41e90007427140d04240940500060701c0313a86040900d100c02c0d107003c404640b5005020305c2e002810055500c0c42e04084a54040c00141d020965558030340040e00d00720030600c2180582c3e0700b841300c085001c000605001c1c4001c0c20503405101503410902280700021000b240f00b50740202c04880480c0c60703843e1410200d0780c0181c0700000a01070b00c28281400042500014000c03000ed00c201c0d1421b012a860381001c41d264043d20f00409010f40c0240a0300d50 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 84381269 1250 84380019 84380029
    0x80c03040f030e2d03010903020606090604091202070e0c040602030a030509070f0906080c0405100e0c1204051b0a060203120408070203060c0a02010f020a0903030833012a02 76
    0x40d00c00e000345071100b0110140c50000d070030860054000300701c040e006181c2d04144c0e6424a45400412802c030020001c001094a000e500c41000a00080c403441030b100000f5250380e02c5070b000c1070805400400129048003080300180d6070b000280520310801c00b48100040c00300800108440c2598441d038061820000100701c1680900b1010349200214066010040360500203d10000000c01c02c080c00868454a40700362141014421540c240c0203904040030001103102c84448501220031031940a899540c4507200b0031001c1c080c00070400700f6a140301c424041885000100138a0104c2622282000c1d0101c010821900078201e1141b003025810070b210300580c0c00c55030030303440354014061200d0501d42626030b40020700f800e008a520b050074120101d0314031042c603424800d4622000c0d504104620307051031040c024107090701600c401410024000002202000540c42501d840c072600d50542c1d43c5401c5594050f50000307030030340d8502c3c0001c00504000000c50741f41d9000c400078140b400340c02c110b540040e4007400303 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 84382519 1250 84381269 84381293
    0x20f04020703091503090204060510051209071508060f010806010207210203070308072303070f0219030605070e0901210503070b090705150915030603070305070b03010510080c0304 79
    0x140612940c514006001001c4c19410400c0421654001500e40c6d22481000125025600014064044c0e40070320614150054112100c3d024600a1748009981d5017612528206403a00490000c62442603000c540940281d9518010001200c403880c0d008816401100d0f0520100c40943c0164071501041001c00701811900320704003d02554040e42031007a0300030900e0826182e00c120398201002400c4020301c40000181344034810340c0c0c000e1106c0481280421640d9000c2e03000c000d40201c50a900c02000c660f90740300c0c80c03444178036003041148065569080c540000c0c002183d00c50081070501906003500d00d40a54400c0c1600d80c2004e9000304500c8282e0400368443c01c2d940101d40511081103c03001282044108034403881542c13005012040c02d050500c18400c0f50b40c019002140400c0c000490541d40312000d0b03903d41d05440030000c0d00c0e55580c0c000603182481c00e0740043c12a0040d004c000c14000300260048d416140155a2002e256201c03803070440c0c10050440740c01452880620111380007075030040100b = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 84383769 1250 84382519 84382523
    0x506060609010e030304030b07020d081302130b040515010e01020309060415021212010f050406080a06090204020f04120b070f0207060e13020c100f0203130308060604090207080d0513020f040207 85
    0x110320f01c1c00100340400c0c990303441904184c50220444040100d101d504104022580a0b14600420b9030b0919040581c0c1000110b0402031051001011560488130b885e486107480210081080c000e5060542400315400180031025001506641116000e94000011a502504040e0805140601c0c2540036180d5141501c00d4000318001c6100031307070344d208444000e01907592003510b600159500d0111501c10811440d40564003650811000300300404003c14440d0006400c000c0100d0038010506c000f5000740300380c0002002c0715001140c0070440c009042841115548031b8170b6009190b0b141c4003001c3d034612040f07446e02c90060740203003000c2c064030788140f04000e41640d010f8220001400040c0b941c0701642c000040d1041c442e44020840800300d9114021520b1490429104501c1c1d41400c3c85900340e42e9a002d0009000d10580e0000324806840300c0046400a0101110864a451461030f099a1950000c43c190404c41d040402240e002c0b6103d12000013160f40c006c000040075400b40b0207000103500000c0d02 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 84385019 1250 84383769 84383777
    0xb04020310020a02060a050718030b13020a080703150e060402010518090a0c0e0109182007030305040221030301060305131202060118050f0103111c210c050606060901 73
    0x11441108000d00280054181c3c0313070003070452864081e480e1070841c0e400908000800c80300304410005034080c03400c00707010740380c20001e1802c096030f8446240f485600c007a03030300a40080c41c080303000401c45008200c220589100e007a108620341c50a007010b60a0326442c0120710180d4000c2004500190301400c002c000764100f250501c810b1072032130341c0040c40e0407001319044240a81c031040002d00840e40250b12840705642403c20208190070909291180d12000500b85c1189603100c4520040c0d0301455401503c050050290310766840c200e00d03000703001e0002500d0481c0501c040008022031403071030841d40c0020480c460011410343c0e00c3c1007012000340c04007802d030b05101200c0300d1000c808501e4201940b201c01c281500140095490130a814100d141c4c4d1507040214185040e080c4000c0036404411541141c0d080a0003042050700e0200042e290302032200403c5900201140c0d40d030400c001044001d8000481c030190052040c444002a18407d04840000340b4135005040082d00926014029040411044c50 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 84386269 1250 84385019 84385033
    0xa02302a0a0c030c08030a0203040209070201050f010e060a0302060304060f0606020319080c0f130608060d0512031f060e030d0504080c040e0c0a120203160503191104050a0f05010b03010605070b040203 88
    0x41d0300d105ea40c010750340f14100b190000100015400c16402e0740d42c00000503c000c00c91450700e0f060b011035072101802030428094404000c560540c1d02c10345254042d44d001040d01e5500e08003454000004c1c201c48400e000303420b05000c00060102e0010054450210003607181a50120103210202d500100c0248010840041845108100041c190180c071441068503981c03900390381040c402801d801e0f00104200c0c03007000c1c0240c2c0400020400300d100041c903000d41c02d400f40c0f80d40f145442400c40d00d001c0c0036411416000d80314000780f050b0707000d00301400440e01a02541c020740c40005049900d44a14014031040d5030094611201700c3c00d10303074004012036005005450540300c40d0341c00220400d0700ea40c000240d01084200b854198035040c064a50b00c002015440410b81d4a03000c042600e406661405130b51400300d02c41c1000602c8042d80c411a5a010001d00410103490190503200c010f155520341c4560061030a0004a004401c3c1c0044034107860050715020704004507a82c0e04418080010b00890701401012 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 84387519 1250 84386269 84386273
    0x10c06060e060102100506030d0c0f0203010e0d17042004060b030c041a030610051326010c0801320a0e0402120102120a02302a0a0c030c 60
    0x121402010700a5648004101e04080000900d460482200d4074171003440c11092004960b00010303105401c482500b090900000d071410a0b07203156079006030180d003550078000809030003c2c020890002c0a41e454448000400c00743d074100340900c2003114010900c548100501480103900c1807000c4113000700034004519907031504032042041d0000c0c0c2e28144028000b040500801201182c0540500c0781c0ca09038a01f189440000543c105c6440c05030041400000500440d0000305500610043d082c1c83c4007005000351120051042003800c039940c840c1d01d52070f00384507065141c07154024038100c44c0407a0103140842095032003080011000c1e410006c030141405203a01d0240c43d40c40f24000140900341c0c0c0c1000e030785014014000801c00c08102c1082c3d40c3d00c104443d60b504600d040c10386d03401504030300c00140c079004201904030300564008826200c00c0c2007000c46401415100c50500c1c81090000394118051101800c0301c15454160840c000789800c0600050f10124403d0662010150183c84c0c11041419a9 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 84388769 1250 84387519 84387521
    0x2071406071a0603010f02120112020604030609121403070804030807050c0f010c0e01050a0504060302030a1d0606010905010e0a1505041203180e27030c01020f1201121709010c06 78
    0x1802c03181d400d800310004002c541e160a00c203541c540080e0700e90543c50200c010300c00240003041405510115000078049005540742c0d601a40d011710340c0624100003c110500b0144201203002030000002030f00d10100e500c00c21600f0342524012059038030368860030f85955400b5a1101d20041074041080700034010307520050810400404c0854030840001050307441c04d24020011000b600b141c506001082040c1ca040913270240032903046071003900c0c0040c3c403529039031a20806042002c42422034445500480702d861000032480c0341c05110244ca5100c0c1442d07a0780015203012901c001290380c0004040010046420004029200c0300c64610f4406d00c1e00d91101d188001070000e80e84c084d07000170900410440403051000101010384001c4c405d103c11351a02400f02880c03d6000800412074108100e11a0843c0c90308006984090500c0c00081d034603100701d0b1032414510b80043d08400d48840070b0100001e040c000001180d950160466460312041142610080e4142d101d0410340781040b95052200000c40c1e09 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 84390019 1250 84388769 84388793
    0xb030f01180c08030a020601090507030b040906050708250c111203040e010603021e070309030209190b150304020607050a0c120605071125090e0a0b070804030207140607 74
    0x1c0c4070640d01108020704014407000c0c0315400000c002d620070042c00200c0da4002500340d0440c0c41d1000086103550f14030b01c04074040c2c4181c41d085500503041c40d20100030080340e0703003102d44199030950305da4001e690b458038015002d40c0320010101098401625903079000d1710412449003030324003400f05140c01008460106025108111201065410106081c02030b6041808070030f0041101e0f140650400031017010b1816441d461041070b5030000350000e0b038181054000c040c441c004540080280009107010b540460390010141c56001c40785103060b801060618000c400f00303c0e05d04004030702d1420b641d00c6a00340a010b9000c80c50948161003607504582c0003c411903240006000071201007108180c20703250901c00d560020b0b2000342405480100081401800100342d24480e401230342010490881e00c1603c901c1c1042078000034406410b04035000c1f0032100010351590b1440c0b050381e110805582e41c107802ca4a40f130050320002c0051700000c104011400802400c1140f112000b40000e26040c0260380314036204a07 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 84391269 1250 84390019 84390041
    0x19021c1a10030b10030b0105010f12050a05070917030a0e1807180e19022b020714030403031428020a0506060303070201050715180803101403100b030f01 67
    0x149400d00803c81c02100e81504000400081803690b42155244406c46c1014000e4030304100705140700300c94981c81025060004014000c04103c1400d000f61140060001201e6180c045120b0080016000c51b00c41e0001409103501005541808e080e118101ca91200c8509103e81c000e501e2840c0045161000e130b09940100455100c140b50488100108030780c20565038081c9090014003420051446100c1d22000d5001d0036121005a82c4c6c0703420910102d004031746989103281038108485000320761081b0703402016018042c80c4c00e100071484815000f0380c2c0f48542e000040010f000f41c80000001421180a0020005402c404040b001121000201c0c10f1014040c10030040e4404c50104090001c14040d4036005a8160044c5140ca103d540000c0c0042c818283c1c01040080b4002030f440a0428a500100041e03100b10002203d0305440d017088001500203a48410fa49003c101e000a442445a8001d2a07070000240180118543d020540c8004119156400382c140c02021042d40e120b9800b0720541034110 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 84392519 1250 84391269 84391291
    0x8093007030611040e0402010c031107030809030f0601150e01020c040f0207020405010e090d110f0601030f2a09021602060f0a20061612050c040819021c1a 68
    0x91031824008141c45070107020f025008420030040c0305407010081602e81c01602030900d9000e0600b40d26045806003100c00047c1818003c900004c001c001e8072200800011b6001c038100d8a440424800b100e444200c02e2103a4002025840c0001c1c80460040988500ca148140181c0c0c030010340100220b4141c426485074983d240e44d00042d0075045191a1143c6400740c10940c4400509241c100b800130b41d038074102c1c040c002c00e000c02d20030203400d850402c0012072507141e01030064402e656034030f1403d031f00b84004500085a100341c61580051300f0801108201e5405c5070716028801c061071612038800025406030184503005c031480040c90f80541c45641c018540c0b07201d1400c00c00c1c0d907020142001400344d4043e080c1045d0042801d054291500400030364207400c150041c0805440c04a404420381e40c40c10003440300302503181017808000c02d61030060050000c0710040b1701541d407481010048403203441c03070103c8002c0d84201c0101540010152000b02130030080e11440d462042010305554402c21290b0444030140c0c1c0e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 84393769 1250 84392519 84392533
    0xf090f0313090f05010b0a11010b060a0f021009050607032c03090f040b210304030b04030203040e06060a1d010c050a0506010f0b0c030904020306150a09030519080930 73
    0x8000b4910400700341103400c1d0030820055040042c031040921a41c070b0300a0030050802c858028540d029400300c0c0b04450300922203580d41d01c0000c0d0103030020100c2c00310320380036004048220210080c14042d540860358000c0241000c2d60b44d208040e00280700c4002c4404001c0d5003003400003000d0032034141c0f80340c0c2c1030f0405c0d00446d11070180d5003c12005100c21000e841c0034a0410407030000580350072060288582c41000228100401c91200f940f460085e5070020303020504400502060540100050050314800c034403040c05503030713550103100691043c0301c000c40c0022521246085050652092045c1116052410b480030408945400e4a083d032028070681e0240c2110004200994035802040c000700400c111350307401c110783c4607000350703c074010705494a00a64000002403141c0d52020b00c440e460844c8905001d88903000d003507000344000614041203035540310380300403043e1111a4040741c070701c400e6000c0c043d10324060312141440001c2003440b4007075030142003840200002441319a400d0b840b98064100404030 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 84395019 1250 84393769 84393779
    0x110a11030609011401030f020607080f0408070605030c090d02031e01050f0106030e070e0703090204061d1f03020d0c0305010608160617070518090114040e01140f090f0313 75
    0x140700c405460b0003441da141008034226070b8003c1032001d04694000c0c041c1d10f0200014000305802d03210745180200302c5540010300340c1d80218000d000c0c4c41038418030b500300c90305291a40810340e410302c4180c903003010b0784c5801c3c007035003005103070480f079841c007c51000c1d040d11840a02c0e00d05e09002881040d982048a945417020441c0c0111f4110303205006220500d01071080301080d86215495908a0060030a914480c0d00000d4030103000743c20074018950f01a008212996582031051140e5a400c0f0441d5561003040f4081582280a40d030300206800100d410002d0b82444c66080102482d808601101c01207829a40000450030030f01c1040018060355014240b1214521088005c2000940294091141568000720800c580c50386e9240c0c04142d0b070900c41e070ba52000300303082c515420306802c1c1554800400800403c05401c029021401c02c0d406030383c2800b00400c403031a49401d845a0f0b41100100d010f00d0b00000340741014107502d05030814142c0080c1d946040740c00b0340940c1142e0002e003100e01c1c0c80c000c801741009 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 84396269 1250 84395019 84395023
    0x8060a0c030f05010b0f1e03040303020406020c0a2102030a1202060601080c0f040e06030c04110d1103040b070c1a1302100c05120903030d05010e040606080f0601030210110a1103 78
    0x1440210071103080050b136051840398101c902440850b40c8400f880480d001540010150700d02034466840e203080f98803480e107442c1c0200a03500601400700140511052120b190900301c241405841868201c0c00907440c6000c95100984506881030340e1510440104002041402503550f05c080c1c0d10785d024014500d002c000150000e24050194400d501082140001c001b021000361426500740c03614002c00703a01e03010006881e00107800101544a46041044032649868000a24401044074024002400c0e00321140360140021a0007400c40d24040b00080c81d207620883c20b00c400144582d1206051300100d03100180d030501d0860f10311460300011144101907103002803034400d03d03010ba807074405451a141d1342c1e550b8840c1c180b02c0d0580401300012506010a0f80d00344142c90030118101c07010031045d0381d50358460f40305600960342554031a292401c0401c07240d40c00706070101c440742940c0080a0b44e03403031a030a110302031441e50f40a000300b009600700000d600c0801e021714804140903c2244030420500304c1014 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 84397519 1250 84396269 84396281
    0xd060f0b0d2702010503060a0512060f01051012020901030207150f0f0908160819090f080708120307121a0405070329040207050f16050603060604140a08060a0c03 71
    0x2409441544007400303008042d000000140d90f4286045601c0b030311944040340044640b500450340c8048000d0408074500c400003a41c5105603503d03958007419903a500c0c28400c504048000301000204144500320310034203181c004013458181850b006180500075251090020128646c54010303070f80b82c00034107440c042c06000c2c410000f02146002c20042c1d070141d6a10b5401d1080c0740c101140014426420020b008a0105450a804040c4007070f103401c12110100030301450141c010020303002c000c82c0000ca440d0f074000a03000309840c801c1004009070818844217020507080189540c04002c6000150a50901c4a01030420703411003500c3d0b03048203030b8021001c110599000a080d6000c042c40c00403d024068081401207844179020302e002e00850a10001007006885200b201500d6481a031907050451071780010313152000130510701078450300c940310002c100641c072040d40c420341e10000500051121600b200640a000ca800a00400116a82d030018504108003100d5860001395144100246039030140a11 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 84398769 1250 84397519 84397541
    0x20a09080105070f0e0f04090510060303021b03060f09010b0a030602070203060a051b09010507021f0206130818130509030d0b030102090d1101050c01091506060e0102060a020d060f0b0d 81
    0x10341d40796400204020b091886002171188a40288407603152140c69582c02003154a801000369024a007580741c840740588514031040340180300350840000710640d4492610b0358005e008010300141e8035a240940074480c0094400e802655903001030030700c2941c5e481048001540f003080e000da2074000c035004160908a0048c610703071402e030902d805c0085606403c4420050512080052912500300000491b2603000d00a4000e40000c3c80c2c0da60303021541415030601c0e2042103c0d90803100d4583d18000900c60f0060b0f038810050040c84207005031103102078510f1280c0c006007000380810f40c110b1441540c50301680c41c2980c80c046182c2000510026480942c01145070019003500203501d0080160041254952a003038050314410085591041a80c8640b0032501c058a914000748007074076260030040060580b28042c41001481c00000050702d90051242e0102c804d41600900454ad8482c504a006035100b0085114144d913a5480480c19260000c0c1d500d015181a840186d11801140c8624088030324a008e4 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 84400019 1250 84398769 84398777
    0x501060809070315060b120105042d05060111100b040506190306090809030d05040503160312180b040e04020414010b03011e050a060f0e0906030d051309020a0908010507 74
    0x4222560100080c02d5046a0740b00c68104c45012070701c502c0708024080743c0c001017040f16000030060428003003202c80314140d540c210740030007940d00c503142c03150450403078003801c80b03480d1540134038480100010b94012948610181841c1d640c41c0c404407141800c02c0000b400300610380f07662300c05a050394100791048960001003543c20784c601c1340000c240e5501d103d03207900c40100001e8441c102d20342004a0341c0141c0d042d007100502102c145401c0c03400d0142a6801500405000780b144a804480d0540d201c1101c1e41241e802110044005030703442c10440748160080e001614259940c48002008502c44c0001c1004100703900103c03a8500345841004203540004003c400c260070003000501a01420404490444030b00840e0105a0a07100758440c11000083d400950f02101a400002c4d00d140c01822181d040902f41e40c41c4420b00f10020200019900e007507500300d416600103020150202d00a2004200d440fa950810344001542c2d0011306041c5e0340540c40c81030014100c00020880c2c03880900800303401c000c007410 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 84401269 1250 84400019 84400021
    0x9050901021b1f020f070807031d040908030609060d0c090b1306060e060d1413060b09010b04050d030302160c030b1012020105070f0501062402070b0f09031903020d0305010608 77
    0x80d600c4140c3d40600020300100d076000a01d20459800359045681c0c283e17020240b942c9403110f609015045060480181c1c104a00f203030040c0545150511a00d0022544416081e003140c50340018060780240013441160000c0c41094044003140011a081d001031a1540c07002c22501540c0e014031203800840040f941515080c01c000b40445030300034100301d981c00c10564100382c42d24040c61020018024845c4200750035a00c02c800d00806407580b60703200102a001e44818440039591506101e0316000034410b20401400a1006104e02d20f41000e46000440c06440d0250800e001411032019a2911920890300a4038005041080002c11040350b41d105504c1103010300c44524101d00c5610700d0758880e200030b0410000088000402040d40d816a04d0b8680000081007050f40b2482d400b00d448280c82084100e10000708035000b19148005043d5040d00c3c51040d00310300745094a1041b00d01038001c00c54240e07250080200343c0c0c1000568501c0704540318040e900500c0c229000e11806800c451040e0403450070005440 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 84402519 1250 84401269 84401293
    0xd050f100b090f09070f030302031e0703120f0f0e072103080f06150c01061e0b090f03010219050d0507030908070b100b040311090601032304080409050901021b 70
    0xd910154400c0c901d00010b00940d4604d00e00505000c41a000b0521b40b48030020040241a400006480c060310400d5480960121000045d06503021314940103001801e048207131540004903820148a00d8005103010524a50900800c01990700c0f0009a0040340d200c1c00d42086074400f00d4581071462620103540c400c6076601618002d041450013804030412019000109105444951824071030020350310300c090b1505c0354200e07018040e0102d4401d40b4070b03042c80f5a41c04480c240d28a800482110300040d0798626100c6142d06000c248044009520b9055500307010844100c01d5a800d03030028003000b5641c0c4c80d0758a00c400341000860784041d01304420185071181c2900066030754400c540c071082c1c0010104c46c031540c070f51806101d25400c0d500180e41815000c0b50000070088102c90407451030f102143c1c0b12075166200c000440841e01221003881000d40c00248461244802e502c5007a0428010301c80c030303031801e901d0b08419420f940094034984041d80d4001081d400a01903903450400c428a16000740003940c0c040 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 84403769 1250 84402519 84402529
    0x1090608190201021c08060a080303090d0305040c050415030b010806040c062f030c060c0909060d080c1902040b0405070806210d030c12020a0903080f090d050f100b 72
    0x55120100024403210107909580c02000b0110881182c120760071682c00000e074000f4000c00d010340b8554003540d10700d080400c03400808010b0301e10030070707010004044015580c4001c41c0038000242055402078460940441c039507c0343d0041094400d22484800307a264510b21340303811007410503404007001e60055005d0100103888061103e01b110903e1402e049003100c0410300c418996541c40c0046400b0240f803a026014a202001400c000b00b610811344105a4a0045032101b6100301103240741d000007008005040d500e0107072a054615800703454000d081843d8910004d10340241c0c00c5000342079020b06080a8118505030290500110081d00c0901190034401c0d805807040f54050601d40c0b00d41106846020040d00d0403100742c03205140c0a04480d03844503000400340041c042d4020241c00036040d0f041c01414018203000b2941d90707103515503507280721918546801607590042e001c0f1100c9400100245480ea58403d1100103000340540054244000f420088a01d001c9490110301c0100342468403c01c00d9a8171 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 84405019 1250 84403769 84403783
    0x2419030207240e070311100302030402031c052203150b030618030705060a15120b0a021c020c010c020f0d08010311010e0d030201020d060608040210030c140408031201090608 76
    0x2003400d841008060071003059024140c1500a1083d0340b05a40000041c448200705020b243c2e03006940006881800d020100c06030320003110b01035056403044d51080344030315400c2c40400c0310305158508282000c2d900030850f10442600f0034004001c01510700c06109100100062761f80018840904020440d40303500885c7d201c401c0104411405000b01404003641d540c00d100703c5650b55400010f543c00c0d4a41036203000d00074080080e000c40c01042c5441d0115a24060441d5030403410342001c501c0b165903450240030f00103980807104681c0083d03403d800045a801c1d00b40003600e007040c012000801c4820700c0c604024a0422451a00341d15a8042440d8600d003c3d04281c03c6415607811081c0907400c500840010f0342c00c022450700340390308028100445001d2560640c040c0c21405500706040c806d00f5035a2070201c0d00136600355400395100c4188080c03944414002e501000a165460908500c00c03c0400c8104945801c1a404040d66420029020340348078580d40c02e07640904802740341000001d040066241d80e5690f = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 84406269 1250 84405019 84405053
    0x14061f080c1620030c0109030609020a05040e0c120309010f12020c0303010608040b07020607050306130b030601060306030c050613030f03021203010b0c0114040305182419030207 78
    0x400e80204064009000031505188011086158024041c0c945541002d11400039078481c0148800001c1c0d80d0325020130400c40d201c005a5070580842d08641b180d074010000418101d03400255641c00040580f1036024041007920303a00050502c032902d030000c0c4003440740ba0150301d44003031f08100410302c901da03080701d41803201e01428601160a00d4502c8401d400901c03c0d40701c640716510010000264407644480d05503c5103100380340c40015511480e40c1607945940685068001ca07200f440011110704010b8940414180c0c1c0ca540450060202008281402000e0304481c0c000b0761544020300c18000f16081c220300802c401e40342d491800301c00c01d240400381c1403140001050300e0800185141418800c00c000522202d880000c41d0b92943d40d034009051541c001c49011507135500f48031040c0021a90740d400c840c855500340d1030702e81c0382204826030042101c0d0518211940071200c40494003010240f000340001e80d0303c503100701c0c1d41d9408820651100954070a280142050700400800b4005078040c0101c503c521 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 84407519 1250 84406269 84406277
    0x601060e030708060c09030d02010606023d0506040b030a0c0302060f0f0301090609140712021c23090d0c060b040f0e060105041a060f0a180914061f 65
    0x4030803002905001e1140e200c18143d10408040c050203540c0907000b04200b0b4011812501c03114034156060f03080c1c072114456030000d03030058020581c1b000c1210003c8407180c1c10b0701482a00c0e80002840440f041c01e007816508290654030410401e1504140c45450b440b01c0080300100100d80103a46c518055086a0200a02650001c184458004205400d880240a0000106444c1d685030760084000307082922601d10880e0a120360004403c62107400c0d10f01965031603032840c10b0b0080341d0540c200a503104040a000039007043d42d0704840403026110b001e0303043d020b51000d5098075260014a40c078400000d8400007482d08156807103041940c2000e85458015400b040105080d028038000a00a00644204450341b0b400e02c1c4403140c0d40340021925505032241100c0401c10100303914801ca1042822001681d0801c0701000943c9811f00c0d444050800c641c0c0c1460320240c2034451842c803850216a81d4056008c0a4444890083c038060301002e4a0303010034240d47c1685d19554802600140100702c8008100788 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 84408769 1250 84407519 84407537
    0x1512020609100306081b090c0a050315011101020403031206150f0309051207050a05011b05090d060603021210140c070f0c0308030c04080f0714150d0903030204090e0f060106 76
    0x5010f60000c5000708068400c2c2c8800185a004a46080d03c80c03141b81d80c8201d403107e00081c0041030080540d070190129646460459840d82010414692044400e038140700c00031a1000001c1d2090004002451107035072003254016184140c0401c1e42c41c3c54114104104981c20710b46103059010522003c0c1c91074901d004940103609003403050400d410400206240b103400982c0c10b00744000018210f00c9503200700003c109000c034814051001540c11001c0350300042003000351046510f00302d10040212401000000b0794a90307a07900007000e5030040d10ba8007499403c03007060f0f800c48109038480c0d807405204501e0401d034289440f512450300d0344180c80008109401d20454201404800c0520001559009110660380d04100101d9012034101d8403900d6036034840c01c0c480c0f82c610000420000308581c040314952419008035000c100e5a9810001f6003080a04144031078004070b092409248040b80c001d44005a40c1c90030042c00605484150901980540c0000c10881c111200052041d04481d02c0e440d1564130f07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 84410019 1250 84408769 84408799
    0x90402060304240c170708071115010306060501140901080c0f070f030509040e0312010b0a12020d0207031b17090d020901080f160b030f06040204030501050403031512020609 76
    0x30030200b850850f103111081d820036115108030f591040101c07140325114100948041c1c1200c1c1495a0202c958100250030b890109440c0d9010340c08001c0c00d80844000d40791841701209402c004000264020384030140c5079401008903503086042060ba1007140070a9520b4481800c002070641f83c406000d609080034005015448074041e81c0070b40344060340c044101694050700b820010078a4001600302480b46103800310f00246120008111412f440c0c0f00c460000140e0b01e09505207690f50070283c0144103104010b00d84160603a0244002c1001c8c610300280145c841340c160400509400940e5030b1441c05041450030703134000c1000d150050b085810105001680d030742d00900884c0c03141d180c6c004001c2d080034166001081d25403000c10420320503039010048868040d450001031010419510885151000400200e8030325001080025800340005d40090314260303a0b82d5507142150000c8074154006a5129282c1509204001c00c440080040d41c2a05202411640009110303200341c10300140f1805070a814410 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 84411269 1250 84410019 84410033
    0x70810031704150305040b01090204030b1503120d0c020601050108190c0e0d05060405010c02010902090a0b010c0f080c0c0f010509090a061a03090d02060f01050609040e010213050a0b0306090402060304 88
    0x1000c0c000e03903d46a4502c1c084100003501801081e034044032442e000e140003146500c3d561003a902281d41012800843c5e40b9020b078020100d4000b280e0030740c0c150049140c0c1e442000c0c0050010007854001600004904084000090820348103800142c1044040d5060000c5502455514958081c400c01c00250355521860f080c1c507494218002e903500301da5240102e00910201181c0c1e20301c128003440c001c0c0304644c2940c500703e00301c0320b03403400095101440c90081040c01d10075a11624444078103051880400c165619040c41030001204200d82200000410303c1000070103000d201c616403001e64000000b40c10b02d4001800710b02440c1c94842c0908254400581e007800f80d904800c00508840c40c078080d10261190368014958001c440040f0544103000030000600d00c0001c4075440790328005010311680e4203000401030580e1040384950b0b4466110080120103107001e10083c0b016030000c0c0042081c441c036007010301a050119600c0720310010020f208001042c5c1340e014210354440d50498510303950382d1b904d00e407402e = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 84412519 1250 84411269 84411277
    0x302040c1106010b0a03050129070c0b030a020a030b1002070b090a0306020706020406020d05030907090903110d080711030f030a0c050c120909010509060f010e0a05270708100317 78
    0x12526220360303000000e16130048802030981da00760b40e80c14000b90303880b11a121000f00046e400c0c84011642e20b0b904541c001e203400090302c4142c1c45080c60010f0b560b80c030041c0c2c0c24250001e0310a602050340c0014a0030718150907128292082c072382514240c1c102821124041e450711845d1043c241459030004401c0384540c0d4419500b0043c680c030850441d02d0f41d5003030801a00075040740c011030000d8860340d000e160f6010300403c03c1c0ca10070216000142201c40c10100b080001d800800da049003444045110307404001d40c113000b106079480b442d075a2110940781c0780e00c00421130561001420000c1e04104005a044104503045030b60082403240301040d104c1046c07800b2141d81c418143d03c3c0c03c5500030b005120444820000040c128804111910640e0340d80315001c100c8000700c00e1b05c005900001b0304260300d0441d4064420743d042c1d6480104280c0c0d80a94450210b8030042e482d040c2402d40140d01901c031403000300000c402c0b0780c0241507403401880c3c40c903090105150904103408050b002003240b5004e045640d100c0812030b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 84413769 1250 84412519 84412547
    0x30b0604120c050904120f03060b120708011a030402040515030d03050106030507030b01050909150d031110180b13060e0307020f01030b030d030b0414090f0c040b01090302040c 77
    0x966031156120403221816035040c40440704002c42d22800940740c0740084d01540100e030890b007a281da0031000c40e030580d032500e0324a2116040c162545000140003110301e014282c50b940709031140c40c25240c1803034014044c910507007200340d118038100640e11008001405a943c03040d170545001800341c4440007080d03c200e603460f0000350f00d4403c944040c05180d130f0540205040320b1140d05c05202548075030000f41c0a5548818860b80001d03400e00004d01c0c146403803092150010540b5500b078507480000b2000c501c0c03180c6103840983c041440022104181c06042103001c1d0b0003200003004000040a26804d00d01c00540303103002030403400c10f0f000481e40710308800c0b40c0101500e6100c042004a00088880c1c80d80303d40003404260310805050a80e041030354042d001e00f1a030440c00401403c00100c814000740e005108402656400542c1e4100c101d81d481c04604155004200e00c030010b01d041103403d4400d03480e041c90361100314040d07418440c01e01e40990300409044147ca5040700d0120711803030140b8084407008031032014 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 84415019 1250 84413769 84413779
    0x60f0d0c020307060c020604030c1203090501021305031216030f030b061b0c04060806070c050a02100206181c030b0102030909101d0c04030201140f030c04210203100c030b 75
    0x80c41680000082070598070651007031142101540059031643c00460307016020910380e800d52000566050b54640e01c02005080005e24410540c0f5620301b242c0095005101400d1110000d01c42841c04020528200c202c0d446034a2405480014894145200080082c140401010740b4500c0c180680c0000c010520007510080d10340c0d18803400000310b100720740b40c18019405640d030041c841341802d01940044c2c0b0306080040000f80c48070b4008440c440425407060f50300303000d60f0300c02c0401030b0303a4091081316016240c0d0007441c43e400c1c0802c80880740d00c401c1046c0c484960208441940b80c8203016049400d14400d410001151013400300140e007540700c1c132a03225a004130400300700a50030044038420010b42d2000001c0100c504480040c40002e41c900f07590048110b101400b04000540c0b08000740b00da01c412082d10302d4103190700c212014103160000e64400c10346600200341448001c0300c102d00f0300e0302d44007895104804c10f101ca0b004261141500000b0354041b49d00d6411102007203020350404030500c20302074a = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 84416269 1250 84415019 84415031
    0x3080307120f1a0108090a030e01020f010f060503010c090807030219080d1d0a0806010302062805030610030501030b0f1812030901050601020705100503042409150c0c02060f0d 77
    0xd42c1e001001c01000f545000002e103112020503500c240c40c2c151041d00c0013402000705480548096512106408445045206151010303408500a010303482d01d0300345090001c2040c504100805082d10401c894440030000141001c02c03070040c000410208032501a0390314220008a070000b0705000c072498104034014411440401070140d481001c1030450450b0b882000600b00c00241080183c841503c22083d00303500200040c405468074100402d8680350300c400311710784010b843d90068a544070074961040416004010080c085c2007900c1c031034079007401c240360412066040d65a11031941074050007204c070360721115001821205c4c03104680b10403800c1c1c43e000c5614580b06080f800c86a070344219a0702d186035003440003040b440d50000a031030055403c010301120b901c2c42d143e101211541c20080050300d81039680d4401b60340700030f0702d01101200c0c00300800c03012400d4070039800c000540c2c00c0300078110f05c0c1c1c881c581040200003c1e400501a0304582d4103c07062542c82c0d07140e02c46c80909000d072001e144e0503185001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 84417519 1250 84416269 84416291
    0x160303030c091d0405010506011e110f19050613030f1803060f020a11060903160f020415150207060f0e060405060d050613020403080a05160b16090e040206040308030712 74
    0x20f121845580720350001d020a80e1104011110351001042505a03da10f0000204055005d090723803d0003900c1d200300b00c64018840800f081d140220318602c0e41c4030485061803400030300006002c59680003d12041c0f02003140f420b590028009103c003000042000b00071600f85d450391700020524001075820100c24042c0303540d000c04003c001c0d800f000c0c0794800b0506540000c0c4801d1000b0407204c2c40b91035640055810005000000c84440c0c58080d0b0031141c2541c0140d0043c0141d6a03807080c50020300c00c4580f0440c1440c240003002055007101a08001503600103d010401281c2c0300014400f0103100b0700c0d001c009090242c0100d403080c040d50300306590007013002c00d0040d00c1c080c0d190b0100e4490502151203503c0c17003480b0050700049110f40e0201402e03c00317080010b0321103940110700504070743d800302c0054a00c80489498140c4881d03c2655804540100208440181507000601001030080e06050745100e0a0039400940f5601c01ca10004140810100029099500481c0441e4038400f540d17800341700102c0c40c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 84418769 1250 84417519 84417569
    0x20d02030106080705011107030804050d170309030d0c030902092d0f04020109050d080405010c0804030b090c0a0602010c090e180706020c031519090204020d0c050702090702160303030c09 82
    0x140c085c00303000a0a106031101d2003140058800126078000d09410300d002e041c101403207402052010300351908000c40c2c6840854042d25802940302c0c039a5103002d1501d503000c2908542c05d0356080100e460405040024100260751801030a07600030030102c0700c1000700b40729142c0040d00100106400120044a0402c000c6142500320329144280d200f40d807541a10b0781c4440401456141c07010000c0c0403028180403d01c000d5020b0140d00c040035000d20070580c00c05030303030741d4840780e0a440443e0164519000185100036606100a5400240400c0c2c0000e10100107107042c014920b0440e403140c98854544000030a40c00014140301c00c0900c40c81c4800c1c2c40741c0c1905c409001e513446440240e01d40c068441d65032480050103406210b41e00a580c021180031305c1c07085c4240d14402505403004140e03030082d800c004080030780075a031041e02d9501300399488503600c5115a00400201070707401003120003990030148413601c0c45440d004404043d030341e05040005a016041c0000c480c258a030742c2061300081c49420b21a6126289 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 84420019 1250 84418769 84418783
    0x30c030227040f1a1306031a0a02071202030702130203070e0d0f02040c08090708011b120f0614040b0328171b100e070b1c05130302070b0a05070609020d0203010608 72
    0x100361038404101106031170b15400c40700b0f68030002d4032111a06000d0a00505104595070304000c0891000d0300f05940f80d02d07141e03012071000c078490340943c0c0001611002c5080c4200724408290005008508500d0441800341054031170010b150310030502c1000714001c0148194400204580141c810880a154a000500b02d88015a140695486040000101c0c110140a10815244440580341c507800d03e900060b0348280b004080400c80c03603220300280c1d90b940c5192040c140209101c07240c0d040f0f204000c009010032100307001c00450298000c1103020003551440128001c1c0b0308814400c14a14bc3c91504140d0211090380310800c0000c20001454280110240ca98110102c4e203034040d142c00c2096032402c081100c00050b80e8039099000b51204028005040029088044958465210042e00201c0600450342d04903031100d0840e10803100d000c28140e0421200003c0c20301684030038945040e41c44081c01c039020701c2c44000d2425803103280080440d11952882d01c115640500280806a01c400324141c40d860 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 84421269 1250 84420019 84420071
    0x170a020913061401050307031b120c05030907141207030f06050f04150509010f0e0d0320030f060109120b01091503261b01090201030c030227040f 64
    0x40041c600a11040d0184152001c807214034180c0c541c000428001541d0b1031300300610890a040d075071003d50b1491707113080000303004121035070360307080b8a41c48840903540c202c6509080a0302084414410068080000207052050380e2003414000e031104403280024030442c002010794541030146a0002040090503074001c0030182c07042809001960fa00a101c0402c1c01e002c8801500b03007405004401e20300f02095000e10381102c3c5540c0017007a510450f0701c03040b055440201055201d80c0c02400300310021989403065a21079101c0440c0c61071000c052384140582800041c00d202c3c0410004404100c09038080c8000000a0040d105850303150262420803402140d024426144000c0c10008466500c111800342101500d501044018002045070b00c551212a01841c0041807800b0402c540b07100c07105500c4503003d00a00d00400071071152100d1000609175820400350105040c010f00c0301c0c14560070045e2a1903038a0306408140d99079905440005405000e0060865034083d18007581100612414100000c103e0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 84422519 1250 84421269 84421279
    0x316050a1203020c040f060504060b12010905070504031407090f1b08011512110c0304080d090b0a030e0114090304030b09031303031803020a060e030f0a08030c0901170a0209 76
    0x19544031810340100000a8000340144c1094108903403d14280c0e000441070f03450048000741e003540b2200030604541c0d480c1c00100e240030000c40e0045001d010800e00b940909200d800c28025400d020700064024040c2d804020a01802100c0c481040101000305100820340d1000911215202c13441d490020b24001203a4070581c080c40d441d015845000c3d85015040711001401401d620011410403a0f003522024a818a409d407555007059480c2c003090007a01540507110b01442e45c81f45800ca110385440303180303100d47d0240700e584a006c2120003040d409890f900989801c000c62180007804103a4010070003051408800008581030000000001000d082541e00c19440f229082d25034000f51541ca019540d106000e0503c2c5580034000a03225444444031100a00c8a400c503c944035400140d0071260740c0c10110014000741007245451604110505000c0ad00074060701c0e608010752203a42841c8002007403582040740015404403964400c401074a200048104011141d040404429000e5030050603034601c28 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 84423769 1250 84422519 84422539
    0xf010302120a0b150301020708040605030907170c060a020c0a030309090b0103181202030409020708030604050f0912090a050d050c0906150d09020f04050403030501050307080106141e031605 83
    0xa01c1c0009641d60700c0768002071880c403a65100080ca0030303c500f01622443d019502880400c0009103008003520242c030045c0c850340d0f182d02d4550340d031620700300e0079510141e21400b807656104a9144040780144624034152182644d03504402026498242c0e000b05241e08a44060000000d055003e25120165a003c1005005451241c00110140d40c03011100d141c854410030039200014800401ca07400050850040d642019610f18101040340c02c040410b8400c0c0c3c500108008052410344502703035122400e211194201d06001041d10740d5006041080343c032480c0c1c005100c40c2240d603a15080d40051130010207030035038100146412a240e140c0c07035000710b001d42901c6021030b09070301d010381c07016000c01460b4a02501385043c040706d0b83e01404130f20340e003aa0040070f008200c00b00c5440b2070103001e12880c02078401103a00e5140c142414a0034845911680099150013802d1102c600002e000f000c6540c0b0449a040030892541001440b851002e84138503898400c1401c002e0401d0010317a001c4044403402c071906100 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 84425019 1250 84423769 84423799
    0x4031a01030623010b0702010201110403260301083a020708060f0403140a03090b040615050609010909050603030910080702010b0a060f05031302090702030408010b190501050708070b0f010302 84
    0x44030002c074040705920043d400180700240010001d012054014400490300c81a00c000301c1d0400d6100c1c1c0c005550070f0325114180941d03604003007041103400510280381480e66250000407916609504500025040b5000d2481c682042512101040c44881c840842c1117108030307800a03540b140284104060341c012040091a0040070400c441d00c07942d010380380c049051030301f45c5080820740e100003104401c1c15074407003a02010903059440c1a05c200c1c810b010003d103034000201091450310041d0301c44d40c4602c00400c0705643d40d0743c0c040903003001c440300014013040e80d4603090700203403e6002308100640c000c81080c100080896000e0082c0340a030001d90000c1005005200602008040a020f1000440c805d0f607500c40e1564440c800960780711140b004010301c12100c030b5000406102c010703a030000c010382c00414144220003081c82a8650316504840024400407950f43c1030221069131320490341400350104000040c040d0741002c980c01c0c03030751003610541d1514009084903840e04c4280000d0780100c011800001d5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 84426269 1250 84425019 84425051
    0x80a1109010b190512010303050a08060906060f0c01060e09150108060103210c05101506090f092705280c05100207030501110901030b09280204031a010306 68
    0xc1a2007015240c41d25000440780e500118214030f180300e0007000004c01c491200750042c1e1010501030b5220b66512595100c3c0b000c030080003201c020b04280d11601d03954091240c3e41ea13808088440f507000130708040f0784030454581e4050041406502c402c900001da0000c120000c0000f10300c50020411082c0130354a50b90700c85c0c4485036202401d02000345041140d04044c8074045899545810080700391401e0b22002c0d409540b428108842c201580b40d030180c8458561000b4101d000d400c101802e00d134a03120075214603083e4000100911841800451a5a468000c60b040009038040300c4007410900da035010090780e03145c090b030340f8902c94501d04d0580c90b9503610310140d000b44002e00302c2c0e45074201006c0c2d0790303490a041c200030003044584211029482007800000c005070083c020b0742e9400d0f01100800d0b8031000580009000d580850414520a510060070404400d01c903001d55140f0f5025845900b440d08200c203070800091207503410140640e07542d66001000b84240c02c8506050720321500c3c041c0301c141400d5143ea0 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 84427519 1250 84426269 84426271
    0x3305120604051b1f0c1202010902181f03050f060105040e0d200a030201020903190201050301030803060409020402030115110105010f060806033c07050906130f06080a1109 75
    0x1049508080072003040540140708925181c00e0040c4822680f85408440034483c044d01d129060109200c440c180060010400201040d12064002440800810790005092141c1030b440c04081212400100e035a02030705c000c014205501c01110740d00800c0e124104103948255824030001d06105400000c216400c0074010001d0b0304000b03000802c1c0898050b64242c804003080b0603400803000c5001e188010034542042407886642c00f0303400060f41d504030341c000d1505240380e41a50761001242c0f0381e100d8006036402400c0764110b0b0740140e095512600c4400000d0040d18051401942c420b00100000c03d48401c1c04030843c220107420f0b03e03080e01601e4040f0110742642c0d824411a0145c0203008010080640240805a8880b20003820b0f04c201d51000711098440e500c8203c0340000b501c0301000d1001000c1c4c1180d144042c2c040c0103100410845103018001800084d0081c10640280740d451000b00b000d00c01d0382c210070b401003405103050100035165407950380d4607001e040c4190307080001456104118240010f5003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 84428769 1250 84427519 84427523
    0x5060603120403140f16031a0601020d050307020708030a031413021e0301020d0f060303090b030f0105120f011a0411030411040e03041208030117010c020703063305120604 75
    0x92400d00b40b5649514111800740040c104c82405003241c03000012005202ca00c0c09a000034241c01681800c41c00c00881e070354042603c07498117451080c2403000581c0c0005030304071440e0032850416a01d41e100c01c0200c2c10044982c0c2f10141038800800c605001d10b8040c0c00c0b884a407088802c0d03644140c1d44800540c81440b00c074403130103904240e01d0180381624028a00c40310120101c09000546040040011a02160305004040b1085c6a8171042402090742c880030ac50010b21742c11780c100303056003409024408000010301c561131042d10102c4880481000510419008a2511b0000c01032030001c0a0304404d801a644462071260303141061030f031006400381d0191b03805680c00c02d4040d04904640c40501009207903c4100c6010342c4070a00000500f2184681c030110030603c6028426120b52400810503882c0d86003010241c210703414040c012001503070000d101000c883d0402c801041c0144182501941d454803d030000d00c03201240c00141105880201011045407010b81e500c01078002c6c000303506900d6034416030740 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 84430019 1250 84428769 84428803
    0x10804111c0b090706110d0207092a0e0a09060e06060307090302060c031c02190e040f06060201050103110f01050706090c0b0a030c0306080708030406120b040608070305060603 77
    0x180159500301072005044000c00c0d0010900d00c288261941220b07070b0742c111500340310b40c3d1040c44107000c2c5950100c84019100e403150000e184240151001940381c15a13070282c240c00d42c0d84d8034440040c405403c1002c4070300841c006074119007901d074020001d10729807114910502452000300000f0340d0500034400c0404480f565800c0707041544901003040b07a1a070000c1c0040c01000440403010016986060007030a00410200c0150741e01e0203111200400b51056505c00c2100313500c18000800f020428a00c481c0d20f40b5414a01941407000d0180001c008003c0d0346480c0000c00e1074200c0104009030158002e0381604e00910315a14001f1000e0100101510351003540d81c0000c501340010700010300300d6040035402c0e52003949001312903510340952412a801040c03845001944030f00444685039050700c1550054000140503000550074803109960f01c0c0f180f442104100800c03050f4200e90101954000410268000c00903c003256603504aa07035a00c2a030f01054855010341c4000c10706c1c5150000303c800d0f03004401e00c2 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 84431269 1250 84430019 84430043
    0x21e120901060e0910151a04060e04020301050d0809040f1a01020c100203120c04150305010501170903160f0b0f01030b01140907110c030601031415062b0b0103031d010804 75
    0x20b00381c003e41800e40c0048046c856001000c6900294599842d2100494001d400e40b42c42c0f410300000e2030140741c0100f107405544104014013150300c40700800c0c5071031030300700040300d0b69005ca42c408240185000038003104000d1412012014220000003800c0f1008026802c64055094030020482103924a00c10f50025a204102485080d170091040c1c96101c2c2c50015081d052030303075401100700a28001c842010000742c0e6280180a90b613000030080c2e000c2c46003243d20340414913100b50345540e684641003401c242200019048000c01074450f6841d5640356008080c803406051488100940300828002102c401c3d0302c510000c02c000c4444850070381005001440c0e200207031a48802038130038425001d07444126014081c4d2107840d0b5102044030034029881103141020001c3c0382d0301a5428002c1c200304400c1001020b00900c00156038544c100181d003002d045c00f0a031407108101a1441c0318580d02001403441380c0840000040c150014507080000c1c0702c2c81012180c0410200045071003100884c1c0003843d03129112 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 84432519 1250 84431269 84431293
    0x2a050c06070809030c062a0a02070308030a06051206090d05031501050703090305060711010b0a0803040b0c070e0f0a051006020613080c0115090e011806021e120901060e09 75
    0x505a42d4103c1d8045083d280b501361200185400d116084407060390b0310385048003410401035103401054244040c1e502c0da5040120a0b00001e440740154400600400703070201c00b00b14881656403050008000c000c1c040510900d0407100d4a0311040c08550281d818094411032a801900071801c6074814070038012540700070303800840151100d4000346801e80420100080220002c0c0c0104161070017540c103078440340c100190b151103040c2515402c40f845030103440c0c6040304010300000003043ea401d8901030725800351103034041c0a44500d4140c0039801041d0b04410242403215040790070030b005000d82c010079014062aa5208840a00e206d001e109207401a885840040c0410b12010740608110340305a504500e80f0416104540c25150a403190117803040c10b022080240481c10710955000c4028a00280a101c11111000505404400740940125000681d40081612207500035080461000040c0e03140c500c0d002100c0d0031a1340441d0300b48032035880d08201190715161b40b040309110340d0841b802003894007114 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 84433769 1250 84432519 84432527
    0xe010807150309060608010b120106060905062d0715051509070c050115060801080f030304022412040b09070317070f12080f0a0908070b0c09042a050c0607 68
    0x1440c4a41c01c0540d91000038000580c0740c06140000c003c2d030000820400541803c00c42c0610030104c10b00c2c5980e140c0581049071350b40000c1c2500458008a803029142e800102c2c0701095514035517111a001182201d840c90404000c0b00071700041c9008184500c01c00e6180010f540440703200380c0b00d900186c9000b42018001c2c0c030344100d0455220003140303005814107520f0740c1d03014250b540c801c45910400740301070424041603900050300c500400030300b0000c14a01007850700300b80e140d100207030002c5c0c0121540c2d40c150703007002c502c0f00c0d0443e940c01a842e090380d40c903400074450304800360b0183c50448148032110003042079004002503c20542c0d4000780c03a605200d14480c046c881a03404248103c4021100b40e8441c0041040000400103030241615103080070700d000d207004840007000504030310a41d4a031400540c045a160426155a1075202c41c0c01000790301c68803c510468003803030700c0c007d0f4810b003018511400700305a00d41079072400261140c1c0d00111404e108058071640541e44003548107901c041d0000b0002842 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 84435019 1250 84433769 84433799
    0x70f020f040f0c02030a1103180613170309040f02090306010608090c060304051e0a08040e07050d2408070605031306090b0702070302100806010f0e04020c0102071401060e010807 78
    0x10041c800540e0042c2402c000040e1050b032407410015804c0480c201c000b03a0703080b095040030a942c1c0001345150002504004004d001d240150500680021805c0c80d441c1030325401040141181000241ca0071007045112a50f0394415024940202e0800154440b034503020700070b480c90810001c0180a0503800c142003268006c00080c4854654480c80341c0101c00c80c0ca641d0001c0d07005601601c040c0880070350403c21014150209100802c07903a100c1824000420300d094256802e841c142d4090300100e442c2c00314115654014100000d625a1800440700c2c140304021117401c0c4680314038400304d65611fa55540c0552100050310602000c81d000300000703002c004100301d141100d0b501c14400040c07200e07000e841d0104060000c03541e210162b4030541003801980350541d0802200c0c03c00c0d03d03015056142c044002014142241c0051050101c081043c1805a03620703016509030500d074030001c548410060410210182070b03803000c081c05520700b600c00b140344101e051425041e210210000e10b80d592400003800744880b2 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 84436269 1250 84435019 84435049
    0xd03050a0204050402070302011a030c0d0609050109060c18090501080a0f1a010f0e13021309020a0503030d020a080f01030f0b0c04050604090902010305070f120e101506090b070f02 79
    0x241c02c00002c07550303544c0c501c0030700280d500035400065088032800503c520b161058502c0d61182d440400b00c4003865640b01d5000038000d40c800008229454140381c01400351088032001004181410032110295a2107000c2d003d1100d001c0d60000e8929070355010740c3d0211142070050081c2178008034035580200758142c16503a006840b420003085003290318050941c9240c42a000b0380941c01c605d00040100c2d91106003103d42107604d0007038994400b4903560005015080543d40308001c1a11907556105664a04403c14018000a01a00d9650b07000c3e005440003075000f11100d8000c503e101c000708491550145030130781621341c89000c10500004503120314200e000000c00c0705e9680401004007017060303207420000d08014030042501041c0c0d0009480050250740c4010315110410140d920407000843c0c1c1300b1040e10342a4481e0000203406145108001e007400d40020a801c040c17800c20318540070070010201d6400841d0500d0b81c5016680c0e45403c00c3c0880d40c4590351002e131a0380d9250718110054a822a88094081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 84437519 1250 84436269 84436271
    0x8010b160503040b03060109080102040803040e091005071e080603030d0203100b04030305040911032707030203030c07050f010c080d11070203150601180e151207080106030314030106020d03050a 85
    0xc901551850301d0340d03000b44c00400d03020401005006e031558110030048040c0c11107034001d50170103041580d60b503071380e0080e0f02ca040d044012513070106003444003e10442545140c208010700c410701c0e00c680041e203401e862135000125200e20441e1204281d116021060140714024091b5107020320614000d40a5000540450b66070714407940d00244a00c8820000e000070b51094403810740700c0b031800030300303008489203010001c03170500c6c0c10000c0181200e51500c40060220010f035254000159907400c01c0d02e081980d0700300941520000604e00c14001c40021040f084440807540d42c0d11400150004440540c031000e001407600c181480351121901d92a0081e607071134805c0c40c08040c180002038001920f044c1a103c11484800c483c1801d01c106541c4c010f0149207948031898070022400e02c1c0001c00241c1000052441000b0115140b02c3d10260790385020301c201d103a031803004540103180c6920125008103190710007200860b1030041000340007000390060300d040710943e401078101410403c2080c0c01400c402001c503604070b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 84438769 1250 84437519 84437557
    0x2030711060907050a090c080402040c031e0e07061106070509010c0b071709010204140d0c09060305070602101401091e02030c0a0905030a0807030f031b121401050108010b 75
    0x10440410500380b1581e52240103040c80c5207001c0c207001e400451504003a4015040a040c1504260400461030b08540c0c127440000e01c40c480190101c00403d4008a0880500a411034100c00e07084070b03800000042c407050041c0e030304441d0795203401e4030090304021034942250840c2c0005003c050083d03001e4000f214042c104003450102550307503140105000c0f070b40c45012484280c42800c0305040c0c0301030316a03c004000000c615103400c043c5a03241d141c8090014600c01e486842d040020441c1039800803000380701c00d41c400d0041da81c90345010342d243e101e5400f49a005105100e4000b24464142c010f0500f2a580600315070100d03402d0400110290400a0902d051180540441113503110507100275032051521300060354490500100040c150319895122606c41d600000c906408148034000b01d505807945070509580e581d0b401d0400b0f0f0081c04640c00360071002d440000901000700d800c10a1500c0459031290100415584900801003244080c060107001a06c400d0040c07203c440018000c02c010600051000a1 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 84440019 1250 84438769 84438797
    0x6100320030d031b140301120305040b0c150f06090f04030e030a26030108061f08100606030506120601030b060d05030301140a05060403120c06020412110f0303070f0204020307 77
    0x103029030000801d00029504c000314070248203004540c0b0240141c0d85002c030b4131428030710031461050206000e111083c0d198000d103c800c2500550171030b0000c01f010044140c6a64a4407c2c003074440a900c01e03103005645600000a03e0000401d81c1240300300c200420040f1b4580740c05e000c280c06241d0003801107050180c2c0500340381450f5401c1000841c030364411221400003507500315124001219250061119010a10052205003008107041e507009003131090402001100030300f241e00039002d562205a16001e142d0244402d041c0f5504400c041e07500039101842980c85030814850383c2480c1018861003a0440030043c0000303141509101e8000300000c0545a0746c00f80740e2600c030704562080e0b011040d10800302d0006151403c1c4082044001d100880e99030f410245036444060307400758003461700c00421041c0d0000800300402c5030b0595000d4800c0e504007419451040c5002150300c0108144c3c1ea100d0b02115400021919001007100c40d0342c2e0344080d0314590040d07aa030030302001c0c0d080640800c00340004c1680d0f13144 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 84441269 1250 84440019 84440023
    0xe04050d1707050d060b0d0b0406050d1e0516030302010e0607090b070308100f170105010e09071a040b0406110f0319080411121b030c0d0f0f050105091006080610032003 74
    0x8031580c00303480d000603080c5044027004121203480c1d10480c002c41c80c00113120702040d141c0711100c03c3c01220666070100d120710303071810a0500344000c1d101d42c946802c0b210301001b450750540c45030a01c40400e004983c8a9145e4640998000d001441401c3d20450104140400288203002c0c41c1e400900c004018001c00d5101e02001c080e2050701d030081700004c04044031002c201c00007405800e0042640340b5190f406400c0910045860b449980030300344038125400051420000c0040c1180c0050aa202c07000e92103644800c0000d1182d000a0156801c92040034054201d0480204c22505032800942e844490485608000c3c4c2c0c42e0a0010810340b00320300f00245990b0180ca4a4080c90580c24410003d043c50300e071002880700e0b03038000c0b10030b440740298009020ba5245441d04503024480c0c0303800c00034900c0041124540340e61420905400100036509041c1401040000059281c804030341000c0c05120300ca0302c820406e603685400701c0700b03078104985507441000400c0441c440119035105540b00b048150480c032010038 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 84442519 1250 84441269 84441277
    0x513060e070906080d0e0607021c0f0209190b1f0e0a030204110c060106080115030207081303030e031212012903070f0806040207030801060503090f06010e04050d1707050d060b 77
    0x31340c245c000c5c11141d06140c0c2d001548503100a0110346513420301e00d4a40200f0070300b4842c0001e0f44a4401044100401d018503242c03241d030140c0d8010035029481c078140300e03481103410070001405107031803c100041d0f840d4a400754ad020702d1030b0b8045c901e95182445044003201c0d4002c203021001d40001b040d180100240c0c49034051503020760b1035a40c80c1c07651442d00006442c5031000507030041c4c1c20000000c0061040501c210300840b10071599141c00f580340c00103801c0c00c070724600c1446110000e80c100c0705c00000803da003220700c1414480040303043c1c8058100c0741005161500c1070140035840729400000521800d81902920705a0707000d641c03a440c01902021402c0b01d03255005032003040209031840d400d02002580305036400d601c0142a44d066080c002c3c3d95602034210b050602511050090210014012600420580b200354910000715020b55940300000c509070002078406440b6400b07001c0e44440300d45d0141d0310b5154504a041400c0c01155108102199680c10600092444c29245d1400050502c429400380c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 84443769 1250 84442519 84442529
    0x601030e0303010b0a090b070c03110f06120a060603021804090f0b0a021206010905030a0b071e0903021201020c0d0c0201050f030703150602060c0406030203150d080703120513060e070906 82
    0x4181c1c1e40a400717a010300460312030750100c0d0700c0c0001005140300281d000e00da0380d81200e89c408200314144040d035000508015106400c50382091000c2001040150036103030041c014444a07408000d0070f034940004409a210b280c000c40002c0210801e008801d040603444491941d0192031a9280d048450382d40500307401e4145c40100070796801207071031030b882d4005442039900b01d9024280303115000c1c6004082601c460f01040054007407010000015009805600201085801c1c1d840c01c40c9560052400640320f403200e40403c0e0701034024080302c4c07600000c0500c21180741c8401e80c0b008044860300758408955006184001720304000c424070003d03e11801540185000d06180d80f03012441041010540d8600480340c1e01c200210350041c010b200107400320001f260140c070050303d00503036240d0f949040108003040b102a05d64120568820701000c0c4190307200904039a520990b152000a001d10701441c0a41b08144c40c4055010100f991180008030a07500030b094407654141999402c03503840d80203004030380140e486 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 84445019 1250 84443769 84443789
    0x26010603141c021501140102010f0f06080c040203040809090702010209030304030320011b0e01020c180f0c0301050a0e04060f0603110103140c0301060f02100c051e07021302030601030e030301 84
    0x1102c1d100114008440d20070701d00c81c8000c00b43e030035a1071103900c8900818030841c5605030034000900c3d030031392003908000c4220368196000d2049148440260009000c0c5200d524224000d00b480900c19103014021207000d15003001d0014245210308040040c0d04030080c10000940d03500700f1810840307450a2001d04019030094840b0084031900d280d180707411040190b101c4405034580300d4800c1044034103403244885c200300307031804401c03007504140143e00c0d0141805080741c4c8480d170200303024000c0b000d042d5520b03c40d40c81c9400c2c10403e512007139800210790100307008003607101ba1a950700f804080e5004035016807042c0182c802042c44100741da000403ca418642007079403600c20404c00d951007960103009802000c801a00e03032094526004002000d14041800b4000c100803903580c1d00b0403043d01c00c006116045025503401c20604000100181290303200108403041c034040c12501d0003400c0403d00c1a10852600a0816082c02e01000030110081d40000c0040d418142e95140d40004001c08001a50103004e14030a = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 84446269 1250 84445019 84445033
    0x20918040615080303070f0305060a08150114010504080703060f020d0f09052404140a1202070f0608040f0303090c0f03080c160b04060302030a020f030a0c0e03072601060314 76
    0x115004200b079860f00300d40600d600c20018881e1842e408040c0800351401850300144503101c80000031204a03996206200d00c3c8a40c00e5604c1c2600c0140b160103040325400044000b180b40602c00558117030080d03104030700d025009a041000490070b15007041c561002c104c0e40c0140303460b102030036010496400d0781c0b41c10301c01070351003101204100c400c100040c2c80c03104010584101d403941c1c0f418181d0380000180f005001c11181080c400795042d0401074044041d0f4008e0340f0700314510703d61000070f540304500d105410f08104880c00c0020242d004481d07250150340c008142c030301c40f01d4207620158042c25444404642d0a80301040001d20b81030300400c44406107110340701055480d60707042c440c2c41ca40561070300325150009000504201c11801007084408071001800c026842b5a80c2c00b4440d0000e0082610340020350384000b041003e0607040e5404801c01c04a0340d12400d20002da00e0090540d143c0c0140100304c3e04010804103003002d008903010b8801408580000441c2c2d180d12990b800200000124440825a0041b1 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 84447519 1250 84446269 84446291
    0xb0a080312010b0412080d020d090f0b0a020a052502030304060f1206050906010c05010209031609050f101802130f03050706020c0102100c02010e0f070f081f0209180406 74
    0x40e0420b00500c003ea00041c2001d0404c00007991112610300000d20b1280b0000700540e405030306405440c800c210401d02049241440c1c100b111004600705012074071940320000103214082c152003528103090f07003950f4241c18090316402500034840400001d8a804c0e0b40320b00b5450040c1c1e0104020300107001c5598400300d8040c14044007404964422000030405c500b0840c00380b00f2510340c0401c4c194000c000740303410704148421703041049c0244240e001c101c0e0540180c2541c142e6030a04003802c0f000311042c0200420555581680341c01d51100c0581d04044c0001c10801c0c100b2407194046a1032a00c81c4407a40010310f804070700c201000c030382120340e80002059070b00c0d500c0400503c441030041c1401000940050074074030556100003500c80c801e1441c00d41c41c00e55501051403d11b413007580010800078001e0b04440e060380140c802144e6910349442104682d520901c0c0102e10380002046528002c080103211524541036200e80b0350294000a6040c3c1e0485074900c041206090900c50340b0b4022800f44500181c292001 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 84448769 1250 84447519 84447547
    0x11d090108100f0209030d030209060c01050f0132010f0203040906121205030f011206090204051f06030b090f04060b0603040807061401030209040b040c090908190804030519030b0a0803 81
    0x150540f942c1030384184400802910045124030581c015850700603920010940003034090701070304001102640c03810003003180d1040d038001e0b0382c3c0c1a140024030718030b08644d0300c802204071081c1c0090840ca0105d03030a01c10f42660350103075108000144446c01500d041a444861103c1140e02c0c0398000070200e0710200768101071080841410107210314610740607103503240c8a40a121100c01c180705024640503503055034070512000d984408951540240203110fa400c041d0340c0061381b5030316076282e0041908022400251580203204604036120080c0416441380d68480440944440041054801c103455024842c42ea41e582ca00443c41244100384d071944440850900004036202d0b07405200b0316510391401400941c5d03600c541641d2156000741d000d4800d90300ca20317100005405651005801a0410b46003108010542000d00051284070305a130b60071048500f000c031040c10302900c024021440030019450b0713034440c481c5114804400c40c02c01191191028000c50844489944a00080e03007010610301444694 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 84450019 1250 84448769 84448781
    0x30f0606090105030d08010e090703020405010909020a050a050f2106010e0103060608030405011b03031b0309021206060609010c0302210705100504031d0a030c090903021504080306011d09010810 85
    0xa81c000c0403c41c0100d43c001d0b1031b0290601650751045251800035180c25001c0003003902450780604140920b5030f40721030440c05881c905030700724030036040e0034004689070820940050485e0303401402c030303030000741100c0c24030640b204c015140c4101241d4108050350540d6042007480d009007014081c0080947c59424848220b038116042000c0c1a0000c000070403441e80d0104180d04141d41c10440c109029090380740503802855811140304d09072105e4049084501d8240d440410f03410300076651002c3c0a14100034882d00c2d46400c0f2141c960010f07003441603c445504c509448001d0504c640101c42da454030320f1054111817100e030351617494000000501d00702001000d20100c4d0011180070000e00190505a501802d4510928501c00030b9800010075107025a603048480c41c000d5030080f00040700c440c1c0b104c1c20180905521241a0b0151150f00850020390184401440c8102d41003d40b49046440d080b00454600348007807621011a0452600b0101e2503803a004424000c1c142040207101d643d4642888500b0b40d82 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 84451269 1250 84450019 84450029
    0x302040308181e0901060f110d021f110f0c150c07061a0d03030213050a0f03050d02030301030803011406070602160605010503030c0709020c01021903020d0b1507060b030309030f06060901 82
    0xfa042003d00038944a44080c5415280315080c80e00d0072003e1154101c4d100c020b40c444010b00e42c400c405400700348a8021032019140c80101d043c80440820500d13501f000d0310344062003c05150004c02c481c003001110301d0080c0c407010a0000996400e07220344070909600c00f60965900c0700c50301c0001854420080a80b0031881c0d6a55101c0105014551890008111400d803010180a06030006402d500b248050441440a03000040c245111103496a01a0000d0142400102ca1030300c41c0c0801c2c980f01500000c21b13641240c1d0b000403581d14582c02c2900301102600e1142d0b14a403c00707412302a000c0081c1d4107001030680c02e988811b214807421900e0032b205058900c10780c01240250000c0005480c1c100b07000c240c03542a9100c188015aa400281d89214020310600d4a0644000f500c0018030406170b41c1600144005a50345905202c0c500c84030041180111105100e1640000c00300b005e00001a2950172010050400a05aa00300564600400d0030078071032940c80752842c1c00c09410000c0134600030b00f85170701420b = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 84452519 1250 84451269 84451309
    0xc1202060712060501020a030c02030712080c010c092303010f020d0b13060b0a030203040c081f05060108060609090403141c0e030304020d14160902030712090309050d03030204030818 80
    0x3a1130200043d4807800c0d40040542001211118801035442c00c000c0e441c01010040c40c9403540c4100d074105103006400002c1074030829420100c202c0542c9118523200002d94981007100400302e6151351742c0700c400d80008100103415540f105440407000200d0300c068a0080604030340803c0b42103c00d41007002682e00d08058504051074034205110400d0348905991104201d4140143d60751201d041101c0d604400d6404090b41d44620a01c2c0d124400c1d041c20008d8049152440a00894540760010350b1030314011038043d82c015405006c900d0785440c04803040c640084c040c3c200b07051100591400811260706c038030741d040c0c07030110240010403184110788240900000c10b000076505500303083c0c5c0000c000e21300140e805411410070710801444004207100780092505a00c09186d8526a907500300c9020f500101d80480105200c0711304140f00c156240900400d4943c103584da10300302401d1004102c0307450b4031010180c0401d039090101000256040c030090020a032640c90000350300c4100340800450117001e603003414a403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 84453769 1250 84452519 84452531
    0x1107080118060c020706091a0702120d0906030b03030702041a0d030519020105010b09090711010c090e06010f0c03030e0a020409060203041e0803010506030a1b09030b1008030f0a0c1202060712 84
    0x951024032001581d107010903070503003c420623980110314021401d008c1e5110b80c080d440d030217413064005414585040310341c031070705c2580b0390312103069040303421084c155034154208210383c600500c0c00350b00c10140d03803e490000070040c40c00080441c8008400e01c1e0114081200081c4480220001041c0018000f00c107100038089581050100c000c54098a1030700b500503079aa20118200500602d90040c0300c030740e00d40081040035500c8400a0810100d4410f003007071100034078080f42c0154030074000d800303140300186c4401c1d1a5807800e507070031001409404040072190007800c02181c01640c0d180130f17648025010f50790140e22420142402145911940ca4480e032140c0c400982000003003015007030341d044071002c5407810349a81e101440d44024000801100142c005004050207042c2c0e000000c00c01500d0242d00078915650700c002180c01c111215000d0504158000e1182c08030104800c0d000309107902c0e840c54002000c028998440b003080000c1031100f0013507084001044080c640c060030138444031900b10428806 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 84455019 1250 84453769 84453779
    0x9011709060415200d0605180115050c0c01120b060a020307050607030c0f050903070506030109020304030f02030c0705040b0619050a030507020d0804030f090503030c0c030c0a0302101107080118060c0207 89
    0x31490a40c16841031000d03010681700c1301e245456005200078640500026604000f040030380344040424014480711501d11954040d90301c2c8104141c8070309140003802010811000001500c01d1b60003d940c40079055295423a1848a80360f65000e230460f02c00702d030011902c8446524149080103c020040c130304143c90701d201d07100c0c951f81c0b15204400d007007405d0820700c5d65910100013107400c1c85950307048260044400400005c00c91199070007184140d000c1d07a40ca1000e4080208126200e12502c0e10740083c0e07a02101040c070282ca010340c000e1951041c0181481c0c0b0303054400100056248a0032248808624082411903400c0d4142c0600f6a001e0b4807840030f00030707000c03152102901030f03240580007804100e040c502e694402802403c80300d02809005080741d8440403070322110b681d511f50b1410100d0280c004e0950107241c85c1051715054051ba580144103601c0078100100c1101d1480001c5400303c05445007000010b0800070a108202c60000c0c03801e56800d550301c45041200554540c450490b007194030401d02002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 84456269 1250 84455019 84455051
    0x703031b08060d051903050910020c0918010b090901020c06010f05060a080603030c01060f060e0411030604020306031009050715050315011107050604090b012304030809011709060415 80
    0x180c0142e084550380700309661810105e01e070000c5218140c48294428001030b0503d504007000d0082d0007000c0300e407130300c03c0345146200702e0726090010110341d00074111401003691000400012401c6080307440002034040c94900005950600646a0040c1039500282c07088011000380700050140c1441000c3c3c100c02864140800c01602c030b04000d43d4100301e908000300d0b006076424800c9601c170a51000082c403190751201110386076208c06205003400301c0c60540e8241c0642c2040e000302c00ba0301e051f0030462411030351288144030180d84010001c0350b150042130901c013688012441680c011500450060003250b05081d002c0581a080c07032801c100744039061007044004020302e142c011a00c80c00b843c0c8041d5002c0850308842c40c00c0100c0e0415030380a40c001c54045450f91503a804808400026654540103c02d8989408004084c074807402c00c0c00740e001c120900c003013035214005085c006010b1500b198030b58070780550000c4003641500c04000c241c03c10b00500c403e00020680084403c550b55400300410601c20688030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 84457519 1250 84456269 84456271
    0x515070605040c0b03040309170c0303070803040219080606130b09070f0e22060603020403050a03050703051308151807031401020d0c0c140105060603070507140f030703031b08 77
    0x424268a034000079003082903103d0160000c04543d0724241e140d003090306c0c024217840e4450180242c030308040c0c50002c014041c005890403400e01c01401540c50884d061302c40340d2941c2e000030030591304030130345c5a5070556051783c0104100051800e0409440f135824020100300c031140260309c840358580e08181d0403845c5503031100e6280790410383c00d0030000e5441e0310101003aa01100707a90102a88440d8102c405420280544038510340c2c0c03000040204441c1da00ca09055080380110300014020398403900030040002e004030b0007010821300a0400b0390814859600c480800c0c1d21613004006203030000d042403c070b01003e0041081d0003e8a903070b031041c0b00700c0e0302c04012640c0d03240710310001e0a4220304201c1c100440a081d8101c62070140050f00038400f2080062014025420ba0b100403925140054460030700c40006100d0039010307060080c00c0b00d155403124441224260003104013a41c140c0b040c080c012010031f001b08103ca500c2052a0007a43e01c880740b03424080c1c100c0e00d044851030102c0c04c1461301442000d501c45011 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 84458769 1250 84457519 84457523
    0x200105270607031715010e060306131b02010509031e1803030d0905160e06100c0b01030b0402031207240e0609010506010905060f030a09050a0606080a06051602211e03040b01051507 79
    0x100342c0f01d44d18440021040e003200080b100c203c41c40d20045000c4120340721200c0050333100030780081c8001e40f90f480070342d07507240b20300900c80070300d05c10104c2c981e0800142c01d0700901d00d14610744003e0000106540010741161702001c0d08a51040c1d940c00c00c0010864103110345c034020900c507024100e55620340000400e041c20001c0005d4030036540d80c0b91000c80c04d406914504042c075003040404a1540c3c4910b0715842020069030203070320a00c51401c281080700641c4046a8032507600000390061440e039801c844501c165024030944055842d00380031036000604128840c032426100e00003103424200540050a0300816401190007400d08109803012428100101c0303410012a14000071000300c03170304159040a003024002031030349050440020300082c0004815040e075003c0c01c4104402d4450170082c100103001ca90000c000358010441000e18100c0c0c40e5031042c43c0080c0380b455103203090140c00244049804080f42c0e0060341d000401800184a0040342190141005494140c4000c844003101c9840c0d01900e200 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 84460019 1250 84458769 84458779
    0x1180b04021c0e010915050901050f090309010f050c061014010903050a260c0607031503030206060906010201020409020a0302070c05150f09031e010504200105270607031715010e 78
    0x50303514443d4254040d00c61144c21102c0f20701a85154401d07038020f04000d640c812510760070304001c2801000c00074051402004020021480c0004010054404100000752700040c041c003440101c00b62042401042d10420844507440c1c2081d003055a00b1841540c000e24003410012610000d000241002a860401507009010840d0006000002d0414905184200801c802c40402d410f8000b1200240d400d01600840d101032012502c82500292512010701c40500140e10100102c2c0360f60070102043c40d0018018800589040c1d210b44007a0b040e648400b40c83d20000c0d0340000c2030020b0048644010000d8003003102c80e81c0800d03a010740c0b021520300440510b5004241c0008841c4410b03a020032031032800e00010611b4903900c680e10003a09008000031602594414201c900c4410140312081c0c400000e440143c48450602e001180d00c081d40c501c03403c207003024440c0700c0d2030503002e581c2c5d131100500250f034403968800c04480e074150010408584041c0030b020400171682c00922060b81c00036202d00c2c6410042d01c0e = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 84461269 1250 84460019 84460031
    0xc040e09010e01020a021507080610050a020c10020d0908010509060705131e05180402060a05090414040f1203020a020304050d0302011e021308060103050a02010503130b01180b04021c 80
    0x10940180884040b1418035880020b80c81c00c00d80d00441c0c400d102c0300380303000071180c1540c80c1310081d548000120754040d40a13403505001e12046000304e014046054407881155014040480400d1100d10b03001c451f071001da0700083c440400c0580c4803506101400051009002c0390405100c1e50350f482340d001e0300403401d001010804400c0050708031000c80041c184212084120310304400c600142c7c45950140b9401003181c40d0b4038070740362401042c01500481d0701030999032812240c0c040846a40d040700103440e90203038444d903031010003100d680c50303d0307010b280680c21040e065241c5242c84150480744619840c10b00d401403001c1ca48140d008020b0742e08480c0180c80c41d14121400703180480c018000483c1341003001d652310b1030344801780685501034540803615100710341d0072548412026a80740402d110080c01507020025490055100d04041c58002d041000c800c40449440e03643c036810040b003600451070300b0341d040100c00a4a0424003c440d01c03040182d03021032800b030801c200007044807000d240c0044080d450700 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 84462519 1250 84461269 84461281
    0x902060a081b040b0a2007050906012d11150c030604060e070309050705010905131a0924040e0c04110c01150e010501020303010b0313060209090a0219080c040e 70
    0x34120b003000d40c0078000c105603119100c1c100c00da00b58101300004000600b205c45000c543c402001d01035084900c405008041035440d1008124600c0070082c016410004140c44c4030500c9915104149121705c80e88031030311560884410001c0c5504080400708900e5803004d8202a500543d012040c1d811402c10440c0071390b284d92300c1000c00c4c058403841c2d004c3e508003500102040351095044d8850400c40f0721840035205001e0341c4100440d409107403400360340d500080791031110a0240403540081c07141088203908403168500e000000300002012610055808200f540d001d014418907403c2610401040300c1c1004807201010b042c80e030b210409048980250380d1802c842243c0211301003a180b40c4170500c002400904c07a0741c2500c901d200d2442c820703100d1a10303c0c0400881c0960012058a040e1000c54119038210344e1541d80c038245040601900740c403d25400c000238940c0340c461002030707403050004400150b40c880c0141d52850350400342803d1541000142000c0c030401e4241c1e4400c903011030b882e1124400140e1509 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 84463769 1250 84462519 84462541
    0x1e150317030615070302031207020d02060901021309091106040815060901031703070c0512040815160c080403020405070c020f03070302300d020109050d030c09060804150f05010510030902060a08 85
    0x850020000c0444804024827070341c1c00200c80a01c1901c59007540d85036121069440e080c0d0154030700d40c20352902004000d1019401640c40748a119024034014625010320303002065030341c0c0c002e400a5072a40c101d0782600e5042c013507072030f15a600250141c8503400150b256442d0030620742c1c100c4e00340c1c0c05078250010210f4411441350804d000c0711904030b030541d001c03c001a01a5100da40c064409c003000c0380141465101d200740c8408905204003510710410b0003a600da1a8103c1e100382129000b1240304009100c00700260700e031841024821055621440010301a90040041c046484244540300c0e0703200d00c1d811300060311074030040951180c0381c00380681041420115414450081c0c0d0040002d44602c40584000ca0790540110752a24021010399421858641044080c0c4d010f001c0d107031000c0f4490840400400e03100311951544a40500904130004000341d0908040d51961101c000a250b15074006110502d441004082e102e041e0707040400030b2115a9003c26080c0c0210b25895050040500c001491041a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 84465019 1250 84463769 84463777
    0x20307080f090a0b1801020109050a0b091e0604020406211506210209100e0403050d0e0d021b1806090403030207050d05210108101e15031703061507030203 68
    0x18030303880c0f4050f192040360581d0b0300202d8046a0309103002c034081010b075006104000489420101a089096040e00c490060100c05004507035644a136400c0744540c845140ea91104034034000700509018140f500421069840c2030300140b540c0f00440d400248034000351740240c421385500441403098455042d031554010b12050b4400180641110344c0c07103c1c44000201031121461084a004020303071103032290050103000d1401800e001c84060303030105011900800241a194048a40c08200d5038180110035051201c41040400503a02124100d420380c01c0701440b40044480944c2d40700e40c058018180110602c00c0070f40304030f005143d00c0c40843c3c00e04d4481d0301100c54042e040011180b0000d44400000c00340da000d405105080c00782c0c910800304d5521075450160403a01010b00520100864003071320750042408000c614140381e41a01c0c0c03000442034601071a200f108081107110821491810081d41800c6032035218201e000b4108100541561401101400845c9403816103440c0c080f9858160b140d40310f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 84466269 1250 84465019 84465037
    0x5070e0d05030306090a06050a0303123306030203060303091311030103230607050d05060d0c08010f0b2b0303091b05010e0405190b06040f0e0105100c0201020307080f 73
    0x103000030400140580003004601501043c2c50300d0050769210b80d0807130122200790146641c0240d0800d4104040b80c414440407034504d4002e400010000750300b03c0c0118403040c4800000c4801d9043c4801c200070b103808901b0032001030175141010b500c0e600d09a070000303449228810100d03100310303c2031407040040d410691210840401099101c2c0d603e50f16414100d2441c0100741d600d04e01d60007a43c401c0e040019010a80b58004c08168944c20f00b0040604160800303454001c00c003580110080e6400004660404104d03001080910300000f9220b81002400c005d462260b42c0c01401000f800c1041002c1031020005c2080d5120300b040c290301c07564090f01e800c40150a01c460044c080304c1c00114840103014404410740d0840d48240c9a00c0a00d008820620040d01c1c02100c065081038020720300d8403500040360b044804102c03401000645420789620042c2c5464081c1e8010303140c00b5091600500c80743c00c10500d07814926100b820b080c107214007290300007556407113401d02c01851081c0105403141803035a68011340320020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 84467519 1250 84466269 84466279
    0x6030c060d0e100e16140d080904050c090f031207060207050304080f07090f09030c140f060c030906090a17090d1a0a230406110f070f030e01110d0305070e 68
    0x540f50900103c05030407014000105030083d8841d980d40510121148030840c0d009035058041081b980d42001141500c2c0401607401080801441506075142d10416119466450906443e100e0003414030441c40c000414082c080d91149c16440150404001500c1c0110741c81500540d46100904e881401e6008941c4603511030300c6681c040080040012070315030107032100f0103420448203102c2d01c2100d0650700c0705400035020031403080504012507849807100e609150791400700c1e81102c9c404020303a0f140040480304603200460120500004040a004981c0c0140301c90b0000e00c01030080b40c842070761001c0c5181c140d0076071110016201c00c103512880d01c40e840ca1034200301c045c2c005010301030142c3e03210307882240d40011807850800d41019200302e49502000441c00580d0701080c0f41e85607501c01005000f401021085104140290f041707044d840402056114851582003821005915000d03124441041c80d80741030101203131030002c24400010700c107030251145e484c021800e0740f14031400b610592036007030400e0b800c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 84468769 1250 84467519 84467533
    0x507020f04060e090705041a0d0312020f0d061508010602031803070b1b161202060c010b060f04030606080c06070b06010e060a0306050102070524071e0b010303020607030506030c060d0e 81
    0x9900c04170b0341808480041d5010b205100010f0001201300c420601541d51140042c201000440d1040d60f0010318603048107001460000e845600901503000b448400352555142c02c4103112850180700e007291041ca060400b00381d82e5061041c065141d005c1c143c00f204803a0340f600c00010704c1d40d42c2042200000c100009017103540703070030390f048041c00800300d0b01c207803a80c511902c1c0400c10b03500a664203d07412603414100ca2a0b00700b003a81e080203442d42c07004441404079901d40f0107a01036503683da00201001c0c0c80c440034250f075561075854a0019604c599000c034005070040030080005458840469080c0d0b50320417005005c941e0f9100c0180e0340c0b40d1200d21300750f400540210b0110151790305540702c48142c48098003144c400603aa0f01c01c203c03010102c010b040e0203484401035495000c15401011b0300d001440b9001d4482c00c09480c03001000403441c00310f0280c88175204000100145a01030060a03000112450140241d242c10342c0804e96a000070030040e40074150010f800d201510701a407000c01d02003160016542c0d8 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 84470019 1250 84468769 84468781
    0x203040f03021b010905041d0708030702090f0403080109180b090120041203050a020f1b010f0806030604120302090310051005030f0d080403030902040e1b04020a0507020f04060e 78
    0x64800d220508801610a60300305624010f030514000d285540160748404100e400c003010303c000b0b42040c252508000119080c0d40c100800b06000d680b002c1c003d403100954540040f070040040b20344010340481c0e10f0b144074400344000700f84d00c5034005044d40c0d000700e4045007a420010001c0701040ea42800500340c210703004180311802c0b0041d00140400240c0e10710704080d4602e45090a0001d21442c8100d0b005079017820b04140000e0f0103031000d46000c0a403401580c490741800703000c0e241010042d25a800d003100c0c610700f10146540c1c00500701e44c5012030300c0c9001141841d210b404250303a010050800f6203e6202107034a804224070940455103c1d05001e0305444056100c02c0d001c4000e00b200792070070410b0f010503a4010815003800119a00d82c5071b9028007e0501d2032410406071141b400145c1705404150722249040c025884501907451260740e0940240010140205082601e50340d000d4140d10a50040042100441d8450150340405404442c00340c82070600500040c0200308076402011448109420000 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 84471269 1250 84470019 84470033
    0x50f2a01030209060903060f0108070b04210201021203010305070306110403050d030902040b120601080606030c090f0415060605030906100f0b0310030209010e04060b01050403031713151e0603080306060309010f020304 95
    0x4100d4200c1011107100b29200d684089141c0070301d00680c1c0e13000ec5540104400039821841c807051490040c01910500c2ea2640d040c0006079109030400c3c1e80d550700c221803c00800c0b400384601354000801002050425045903030340d544480c4100110010036403500c80380303000d43d07507035501a070b10420380102000044400c040f941a1502001d2080701d6090140e2000142030341004a03030f076080100700a1142c249aa900103841004d29005002504d244200c0f81e06c1d00411000ea204200190566481d43c80c0c0f41d150503c585442c294000b011140202d0f06280100107009a8a0138502620280182540c503a90790420001044030315a00182d4402340031000021140002e583e007901079801480c09110070849000191120708c02e52000030002400030640b65034240da001c5206d6003142075401504031202103030304e65080f88094080140482c958034101c50450820314410002d41c1c038102c4105010003880c0d500d4881c414040100032a009910010000d89100001e41c009a900320301c1060842d182c2c109818001 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 84472519 1250 84471269 84471271
    0x90412180503160e2409040c0803280e03060a0b030a0501140103030906030b090a05070c02030a060506010219080f03220305090109170601090c05070f050f2a01030209060903060f 78
    0x80d0390980544e000c10b9120480140846a43c071110101d01c0d202c000440c14000107031001001910858681c0c41c02043c25082440108205450300442e100c80c4400541c0344003a07800c20341c90b65004d002140301d80c00403544000c00c54543c07140e940500020081c82500200b4207210140000500c036529250a039202980821300c11410f8900994070b00c80c8040d110780064044450407410746601800c4031000072241d8100e03801887e031015551034540c00740a4150301291070030b6050501141d0140d11002042400e503810400c00a8054402d46103d420a4042d2181c5000b4840d07070b07440e01e00e40c0a0010000b8640c48000102c500d0014404042c21044501414020107a8110648040c0011001c5c1400a08840c5031401c1020611550300901026481d0840c10001030020b07444038070078020700b8059903002c42d1101d0003039024540903601a009125208204030704003c40d03805099038854000c4100100302415401c1d031440c00b603083c240145c2d00c4c00240001844d0b0f01a601c4c5c019818420381041000d0030844401c55 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 84473769 1250 84472519 84472529
    0x201211104082b0215060112090c05010806042304030507050604050705090105010309020907030c110304061e030501030b040f060906020301120203010f02031515070203010914070509041218050316 86
    0x460a00f00e800f201a14680781480210010381c01041550091803210541079000a8141041c268070541c0030892401da88401500341e8108070b8030402040a035070044000342d0b10100032541005428030b8200010404d202d010311080810b03030080001000c0602590865003415007101c1100d820745490314100d682c43c0c086001d43d42c010810340c000001c6550180c00b0794081d4a030300516030362069540b01c10880003400324502a808000001d0398030740f0500030510007800036010583d00c0c2c15086244202d03d41850354140d60f01d03420540b62000402c0072507224004150019400b1455903584052030622002a08200b140600042c1c0700000014070b0414001340b40105600c01da00920041010204c28070403404121180d42c8401d19920700c501407440e09005048020008000d00c5e404e040464000c00d084030350010044a103800900c0c6010000041040004002c02c011074601c0b0480c07415607600d280254699480205000c081c4064400105c1c0c0394901070041e082c0070301207540c0c99040300c0e540183c01d0424810 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 84475019 1250 84473769 84473803
    0x21040b0103031403070c03120b040606050904060506070f0807080904020a0c050618060604090302010f0204141f0e060903030706090b06180f1512160e07020307020121110408 76
    0x84407441c25009001c1c0c0b44240c80d10345426100e40c03000d440035141d0340c0e890044e034128560f0311540b40c4840d6652f445102e01030001603a03102c0d1604128070600003202c10035005a84103d40500c08500000d102c603c9000700c59901022464481c805031030151020301484c2c01d415445800800d00170003465200344041000c6015404030b07080c03520b481850104203002c1030380000950700403000013449030070280c00104070288a44000504002000e0901f4100d030055082041e228640c0c1c824104103103003603019034a041c07100d0a1901c0000c424004e0140001041e144414018a008955042d00b65000d20913164901e410807014040c031120343c50040ea101000f100c0d00c5e4071070400f131780c100c000055110b00510300c101d0040d02000782903261020181142001080265407050000141405502040c005040c0319007000c1004194035042c0038040c0d0b00754600501c101c1c21903005200000c0940e0740095204170ad01b0038843c0311005205540084800362800180c103044103500001c00040c880c100281c0c0700c0034140250b030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 84476269 1250 84475019 84475037
    0xb01080303041a0f161403100503010c050a0507110d050a050c091e1b07050d080108010b0409240b0315060a090e07060513150e0118061421040b010303 66
    0xf241c008981001d44414501d801e00400280d40b0b100c0c010460800940541000d20503000b0b0300000403899401103072120650072800d1020000382c00d00340941030240e40a0f080290901d070126030000c005020340400500700c0303403c0d241007441540314504041c4901d6041415600114070034281165141d54060640b80502031442c0010200108419980084607190102404545420510050301e003e085080c903902d0340c0410030000050802c11118558081c07940390642158546403080d42142c0f0180c0d40103015508080c0f00e42c0000d00743e1500031086401c0885d221300c60341c03001742003c1e000300305100a0540510510700081c0c0b0984480d100540701e80c0084034295641c40e25104c00d18155842c0070340d840100e5006240602c9545d0044010f031000001d403492034401c6954078506140c51004900100001c00d0040f03ca040d92940d00001200041400804032200070303107481e0700103120303d002d04900301c403818010030f02805031320500302d0380034014041240d5400c15041c03d0802034150a020b200850114803400 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 84477519 1250 84476269 84476303
    0xa080a240608151012020d06020909090601030c0f0b03060103021c05090a0b0108070506090d060f06030803060301051b0a2001050109060f08070302010f0516050d021c02070305070915030b0108030304 87
    0x3a104c50503501c84607491905060950b091100300c0f91001000c44409401f4012146143c071400c260900c12007400f002040654954100707030723803010013a41040e41d21185440c028440b008915003101c4d0480c40a02c1e0043e0340c1d600320480d0010b42050904135209150800d024880300500001e003800a0600400400700c5603603984c40d030f2990302c100324030440da00188140421825407400c0c6042c69001401000701049450401c0d11200c01c40b181c135001102c4040001c024013485048c02d204040c0d028002000c0c0740354a03083c0781920078090140021010404c84041c41041d040c1d50311001d0740d01030b1f0700014000d1041d56190351001014000301c5c040c40600c228647e42c0043d404400040101c101d80d01a190745003c918615401c844903806034446106c2d1614a14070b12001403020000c6025044007513001e0284500b0304101e80d440c0080041c503d108560044c60140301142010032007904070380b0219000286160141c3d100c1122280075400540b0302c000c24400014201c2011000f14440c0c3e00c0b031b030b8419290200c0e030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 84478769 1250 84477519 84477541
    0x6090801022701110601060f031107020a1505040306110901021c0f0804060209030d0809072312010e060103080a090b030408030612010b1e030601050a080a24060815 72
    0x10032030003002da91158a61030020b8010b0307203081e10803400600d4069444d0903518582031400100382d010350002194040414000b50b030512640d141c860f0603022061800c00c9980000e20b01d030324907000c1d514040c1c00381056807529034029001c5400640c0d1118062200360054018000c4a42040080c00c0c00b5020b0990146c00300103080791040c1d00c280d91358443c001d110102c520100c0c0d2100e001042101c0d159400c01ca500050340d030801444031040c8442d921a545864a008101d0400d800f9511010b80e600066541c025841c0d02400f07010b0303004006994000c0c00b124030b540a240900180d8510707c1e0940105000071060003070400c010b01d5103c00c280c0395403a00310340c0d9188004691208071009000d0700070900101d5490f15013960034a01c41c940420020a50741a500000b91b0010030289a007054800220502f03c00d0381070900c0200d004003002c641060810346060002610341c1e80e81c0c0ca0090010100001e0043d400318400c1784107000c03804200c801c02074541c513200860b5139101c4105038054203168120002c2c0d01c840b10 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 84480019 1250 84478769 84478777
    0x7121506060203030a0b04060e0408030604061a16060906060f03050f06250c050106090f050609161b050d090306050a060807090b03070306020d05010f0b090303090f01021e03040609080102 82
    0x7407503004624559880081324010040945000d40c466142c000c0025200040b50781240543c1c05412078983d40c3c00d01c1c0c1d08100885134181d02c624a140f08220103640d070030216400742c1e42142c1c110310381d00c403a40000e450700d80014100d400008142901d042e001060191400c0064400c2d0303407107502104e6084880b03400441c1d032010100d40325008807944217a1010420380307030f0040344111101c9040c0345804100c0c556405007599001d401000e00683d40b48a0110006443c1c021f85030020015104061141480c5c0d4002e4418503000d43c4400900402c8101c01e48182100746070010303a00d80020554010b83c241c0700001381440c001e44002d45c2c0c003c0c10407001c203440c00020300c50306003226901d100601580740382ca42d6520191080368180381e81402820790020100e80e00b40010b0070000b04002001406605248410f9405604c541110440450501450342d4646001080b254005400c550010301c0511850040b0300d0049208200d11039090115404c201401000028100f0b90300c1503210310f101c0c0c0d5111a00d0350f00300d0213 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 84481269 1250 84480019 84480029
    0x30f020609060103030c02010c050f061905010302061204020a0906080c0901080115030b1803040807050a12031409040f0e01050402030606100801090b03010b190801110c030316020f07121506 83
    0x300c2c00410000340504071405202d44103042000070460340362999821300255081d011403d0300a141004850a914401c07120041240c0c40d040002d0350540c0c0100d425405181d44103001c1d11201008507007076558080e0010014020f0103004d07c003294a038603000751a10001d410950080590b00b00210b480401801140c40010f039031010714621b94510344661401c010050007000d00703500040010f80d1002c0b030030710060010b840400001c0100d9450b2005210746a2840d5001280403410340d6015800240e00101103000341c1d83c0300041c0d039203c0414a0001f801090014000b0b150310b2b28008295400a070190099403049000b101a1940c594441c418401c03d51500c804150000c2c1045006110001041c0d10115805001800005502000601140f422184484440031140c001501004140e0b000d00030360640569100d1901e04100b81800c1503a520301002d008541c2c006808088800014400c000000504c031944007107406a5035035240042007507a8501003038545850b04061440466a103008030401c0350 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 84482519 1250 84481269 84481273
    0x60f02030703271208070c0f030816020a0807080f160605030a090305090a03060902030c011425050a0b010807060504061d0f090c071103030304020901030308040f0605010303080718030c06050d110f07030f020609 92
    0x440b82d4070080bc2e441c0100d440032a0b100c40500b50106000c402041000050b15a22002b4011403040d4450b182c5040741d00f14032035500b0b42c2880000e02210303a102090303a401c02121130002c5403503180e03440c1c290746034041c01200d0f68120383c019000206000c916040003000d24000d501792004c406403640110b850000340b040d404802c1030b00b0403160314181a060403400803001006401e82e0803061b01d44c0c17420700707042d00c0800590b003540c0d00c10010b11030710390240710540003850386040140c42c091900d031000d40009280001c44030184c3c640b0300088001d44600c0249070510300001e02e052214980010032000c181c20082098828410b4184504164100001164050350b001022410a6840c66074201d503074000c010b10880d580840101117400140c16401564041c611a0722680d016142c103440040200251042c0720003e00c0d1034600030004600982c0c048000d445480c6490740e500c5541505600c040c008101040700607480010710064031100d03010103001c280748a03590390440d40020600c202c0eaa15025a016a115 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 84483769 1250 84482519 84482527
    0xf0c0804290408060f010e010513020703030b04092d0b06090c0c01090309050f031504060507050c070305010b0a050d05060106030902040b04020c0601060f02030703271208070c0f0308 80
    0x40362601c0000404001001c06001101c1075921505070304564020f50342640403c050100c070569000d08140500595000e00702c0317a6250400103003090702c1101716001c01581c001095000e161080d04004068074000d08103102e405158507092301d0381c0480c00c1c410311400524846020f004110b11100070304540e00100040d8403502c90104201000d03501070040c1400380d004000d4464a10b10030f000d046c80c81d9009407560f8a200d40b401d010701c0904580312201500c0f0b0707040b0031110760400d0075151006030009d07003000c00001c07183d4510b08291000c0c40303950800700c8144110100042080341c150407002c0a084265011006181d455061254422013010002c01d00e0b0014001846818482ea008544490000388041040016180410102e07442203030059020380041c0c006201c02ca401060300c64000c202c0344001c5103051281d44004100105400180c03400d05d10326640c0251201c1811107100c003078000d00c01401201c107000e1038038010302ea00480f0f00716002c03046003200251280c00206000308513500a58858030f8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 84485019 1250 84483769 84483779
    0x10b06031807180506030c01050f03131113020d0c0201060312030f02070b010810051503071712040605030f1303120b010309140c030c10020a030c030309080307030204060f0c0804 78
    0x1041040301d031100280d1045620001e000c0f0000c1c0c2c80e02e1031209018800050300e0820b0002c0c5410804000c041700c0c1481020800001400d8806080700d034014041c81d00d0724884402032030300340081a8100c503410b92008020410f03280700c29441d40100307001000a0010030800141d00b80503800e98a10780f0002d008681030428444032180203400545481d4a425001407802c12190f030b03503500d00d0300203030022040783d440410320101880c154441e00b6040f00b19061031940c0c80c00f159002a0f900e54080c010342102441d2014429a0340c2001c0107000305515012400f981c50f1516400000c1041d0400c507800c29440e850311002c582d0042165130021b00c0aa01030362402c071260740c0e0118140280c4036041d030b100d0400d5640c400380d9010030a5140c030b070200c6001c1c8101402703160010601301490321248005940c840d6241a005048c01500050108441c0da494100a155490307036007001d5005085142001c5c041c0c0a0000030000802d81c95401802507801c6a00c0c1d45061001c0d001088611020800004041501c20002400 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 84486269 1250 84485019 84485041
    0x1170708011b14090d1103060601080408180406150302070b0c0406050a080c071506050f011407020405060118090b010801080105090c1203040803040e04060b1914210a050f010b0603 79
    0x18810040700f81d45041c84a07000b04128102424080c1d0f150107444103908400d25050102e182c0116003482c0180b12800e041e102c00307800d403042001000b4101d0741c02159140503107440c2c004078003e290a090300c0e1404a00361101801139031080318115182d485010000e0003200100c1c00346c40c1074501d266180b50421480329010750f0b041c24094030500740e0310340034460307030000680c440744004480010007030203d0394030700c0d0405200c050940864002e05101015805080306172080d8180e4420341d40449000c0b842ea00c5001c010303104030084010944004a4444000c10f14441d00d410102c800602a613882000d41e0fa600300190807034005980d0750301c0701d8108007214480d92070003034500d404042201041d20316140e694071740e035455640907900075900c0148841c100000c0c001984500940309905480e44540c3c20a00c81c5844000c04242c041c62800c206500c0d1103240c5511568480001070030300c01c11900b046e42d01c1142c469a90180c1d00c2c01214944580c20100c901c804044c000c4514100001d80040d040d9142d03090811 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 84487519 1250 84486269 84486287
    0x80f0304020111030c010608011b0c110a050a140a05040504020d1709061b010b0301090209070513050604170105090f120904090605131203140c0714010501170708011b 73
    0x190410441400d10070243d030041c0011702000d85c0c10400002c0781850102900e080d181034902c051510b100e40310000b00d200c0d4006141d0f2001e2640f103400e401852100400050701d044041d0002d9400a03101d100102d04074008005544001508032544100b6542d510100300590740215002504901240c00c418005100714010f802d10f60700001516003442584008180c060700040c881c880701114003c801020320100380300d0000301003030039030081c800034507182c000c50301c080b101401c290200000050081c0603c0d01c5081c01c0340281100404065803980c1d2114240e841d4950b101c0742d043e13594a00008500d5001c8000342c55003614445a01a282840c141540354501d034200d40304481e00b040d12085040c0004446101e0a44502805400055286031a0410b00140c01c2643c000e81c09141c9411664415424821007250340a0704030701040e81c0d41d407414070304101d4103065116910070300c0d802c00d000030942c02c00000c00d03031500386070040441c1e00065036100220300783c616401c4646c03002d06c00c0c074042d00c618034803403030481d = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 84488769 1250 84487519 84487523
    0x506060a0f0e070c14010204030204060b07030f050f0c0318040b0405010f061b020a0602010c140301030302031204020d12091a04141908060f0403080f0f01140a0801140906070903080f0304 82
    0x8800000c4c01d1344a91060074945040c040403030b5400903044c01145031a20580780034041c44d104103030401e081654090320307400b280600d440510002052403c032110100d000c8403d5080460280c0782c44202c1c8510345183c803000310851510442c18049000303e50f08043c45080d0482e6107202c140c00c42e80785041e105942e450a01c000d5425030004070120640561140390885004116640c00014520710b0390030018604481e100c91060800f100700010004658000191101380c000034181e900c090700c4500c00203e0345000520300605540c07400c0280d044d01904880c48500f1182269010001d0380005001d0081610450040410751422800400c02900b0182b0000580c0b0151140c01e4141d10327264100ca0b440c2c6801190b815500e5a00901001308040d07004030101e030005220780f14881c542c10a04229008040c0501841040d0840c461480106d640d600c4a50401000c148000b0850505111124440c5e54012202d000152041001050216120360441403c982c2c10018450030074131a1034480c00564005442 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 84490019 1250 84488769 84488777
    0x90102010b04020f07120804080301060815030610060207090b130c140c010209150306010804032d09030203010605010203030402060f0702040624080a0c0f0c1a0c070506060a0f0e07 79
    0x301c001c03611544003d00c0c03400481502d15403a04224a08074484191000541080080000901c0002002501500d05403000c504242c0704aa03034100c072021400c1a151030700c2d80e1503c120024440d0b4241c40c402c904056800540c2540d503d180c40f41c01220903144040c140d0380c0c0000c20b0100e401d1140080740e0103c1a144d080740b4080c02401d80c288501b134482d41049010b202c00381d60015980030246821460040010300907a80c0d603045207029000a44103403002040030381480341c201c0d10b10142c1c4c0a4140c0f0851140e480021a0151180e1240e000304184818001240203601c1d1600224070f56000105580c802c50f801001b55142080003581c0000d00d42026204a070415203404000c154001c0c1c1100404600215140e02c44007000f0041c0010201c3c800a00010040e501e00b03c44040c0300ea900280320407000000b801d01364a02192460310803070006a2810152a41c0e08140c1400081400d010080c940c3e64003401c00c40e42d06840700001c2003a192094411100c66082454003000b00d545681603940c2d1104541c20 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 84491269 1250 84490019 84490031
    0x50903070302030d050c0d1403010909111e21030313030311030c03040b161d1807020a030906090b03061201020c12220513020306032803090806130809010201 69
    0x201092074640505448000f00d4004145a40707500001c07c00003070100c000f441c1190b14500d9450444140d0710043c0580c0820680b00c03941c1a0921107820084408600081c00c2c0307001141000503540d580c3c2c40c00140d010320540418007510840014000c1d0080036803600c80107545540c581030710346030201501030002c805040d181d6214000d46c44048018510030f00c07003501b42c1652850b251401c180141c200030251516819240078526550fa8054014402d48030044811003640704480c001030404460a001070352000c03245410002c00c0c40c0e01081035a0468841d03110f0090468032514280c480040c2806035420b14042403000070b84525105030710543c206004400146092000c1d507509041c11a20b02d214401d5030700c000741038001d658070200403001981da42003411010310305020004001e400c41844607007480f138011020900943d010b001c0f4640c00030340c90b2111100208149803010405e040481c06501203014440000703a1504d0101d80d440c85001c41003540e0301008120b03a9224080d0300440042e50441d941c1d44 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 84492519 1250 84491269 84491273
    0x6030b0307080f010b010305061903021011010501090207060e0a0b0c03270c010207080102040b0301050f0a150206070806010e03030901030e010f090302250b040e060102010207201e010207060509030703 88
    0x80f12034024003648034004070f100e0100c6000036007034400141004c1d0003481c80311030a09258180c00c2c1d204003a294120740b41008213040704001c690801e8281c01c0303888503520f04000020000403550003404c40d1846858180700080400300380d16210100400d014020701e04990000c5e142102200086600c9080d40c008000080390b014000c5c1c1c220700542182442550103240702d0912503070108031082c01441110000d6140c58144099401c80f4001840741600440440a0410f065500d00390f0301d001503d41d5203821000d0190308040203542c2c02c000e48160000c5070075400810b8007540b0600e40304410f0070000c1c00540c5000f0001004400038140001a8001556141085075824190340103849240d400380c0c4c010034400351244440c2d482100b1f40309042c45c0c000c130480b60030044450700805a40c11200c6411441d6034540e1003800503800782c407030f46030000c008044240c42601440c0c5111520b00025806507402018a0000928018422200018603001d80c2c008541000241e1007080100101c10002c0c0c10341d2321480d030704c0e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 84493769 1250 84492519 84492523
    0x5070501020d06141302250f050102030c030109110a0503010612061e0306050a051003080a0e06030703020d0c03061a1e03010f080f0111070b0a0b0d080d0b010201020702030706030b030708 82
    0x9030b08001040307400d43c0031404c0680703800c80b8008403a900e0000114900325240c611795808941c907503006004c1180c1e54600030184142250800c082ca608103000750f43d00c2c500703001181910fa009001d000d51030f618000b8100344040c52003040d10b890b1619625000d103503909000003601c03c802000b03a2001c040b903c0e10340120304c0d54080d490044400300d80080f88990581545000c1b010f983c0001c1084900c1032a00301001158502c042e4803204407074020042640d15001c5078011140962110907850304400c00200340081aa031560043c08450241582008400c020340811801e8031003d2041100e890017440380101354002500c010314201d503d6003030030500d45140d0840e103401908260712426903010912004c00900c881840304690b04100306008101c1d410440000280501a007440501150380c82c03000101b512410350320540c0d1418005003941c0c042d084c10714007500954412021000e4160420340c1d8008254014000c0d9400f207580203000d40340702130508104900616a0360324a90345849803840000d0b80c0302c02 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 84495019 1250 84493769 84493781
    0x207080a08160c03030806120c0913050709020a1d06161502070209090d08070903050604080a0e030303040f03020c0312190e090708090706050301060f080a02040503030c030301030c0f030803040305070501020d 91
    0x4c40e8417001551f00e01a170400418203426943e040340c1d82c10841160314140c0d519113620383c0c800ca07400000c4175a82c0090809901e420340c1a0803c0141c43d10014140c180786810403070094161448034030350207100298000340702540c000c014a452418045650714070014603044610349d00e01041030380041c2405e145400141a425065412460300d030405031012b47c20540c01014241cec040190b0902c5400c4508d15540c2a56034440180060031124003c15a40c4107103100d440301003805080101280d45a0034a400c1403058000a05011000340c4503ca0450302d1034180800c0a007815545103003642d003440700159900f00c8480c4180030072800c104046500000b00e1f501c01c10b80c14000c00403550341504030b00c0c0401200d490440302e41c04c5501070100a100420410f50710511103e480241484c4c103041c0c0362501d1285002074004c076040b40f035243c000490310485961002001d14120383c01180a80b01040d034800704102c6d0b4945501024045800c06c000180119010b900107000391803041c0001494181500c0441c0200e6207 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 84496269 1250 84495019 84495023
    0x160302190c14030403050d0c02060d0903050d06060206090c0409110303120f01121e050109330504030c08070309050411041401030b011209050703060903080105030d0207080a08160c03 80
    0x1c1c0c11240c0c8140301d20070301c40440b4000c11078011850a07040d521295514480018aa0300f040400710701c220442d2261070944400b940c111b0014460400c6c01c0c900035100384c02c086401d8400303d19003d000240346200144075401100402e0103049800c035000c06100142c030310b0310401c1d6801e40c0111040d00c05918100300170095083c11405404850420520030310320740704103a124040c0009840e48203008103403201d4003100c254815500c0c170442071a50f89415400341c00101000350a408030080001840001f44e0400700b40066141610078456910200803021140260390250029801c0c00d151350000311550020505140a41400e806050752000081d003070700c4d1000900551224042010091b160002a038059041006d080c1800500f040000091022800028211b012902c51707141b401407000a1003d0405550800e100340b001c45001d06000d400e540080c40340d44e01070b02c0b441131080c80181c4042080801e48602034040d00c49940140c071030b00391640090800c041002400700c4080009003140111200440c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 84497519 1250 84496269 84496277
    0xf0905361303140408060601031a0a0305010506010f1d0103020c100e0106141c11040207080f070201020d0503093c07080c01090506040e07020c03060f09210316030219 73
    0x40601c2c005208076018406004003038014071003031000e6403020039191392110303003880e000480d400d07038802c0c00c80d030320351019031103a04145c1c010342c084180081904101e216a81c2078a85210f030342c06050044880e8a4000c003100c81004064801d03c42e258400d0b001040c3c2c00310900e080314403e8a51150660445e11210130f0503400383c1d0b44d010b04202d040a400c01e911802d2400326003020b40d4640700783c810010002d507000001c080c6c8041680051007a511981030b60030607504a2896521140c0603000c1092940c8107079002e0303000d0700c50b41d40e14060a9210f10304407480384400c400a00401c01d1480c0300c1980964440742000c8610f52420721001403500c280030300c42c04803c01c400c0180003161401e5200d50400104200d0181040070071213080c40766460309400ca408503243c0c1c070a1200c8a55800c6030403424403000010840c0d141c007075682800301c00303c400700400340228451019079020040140441d81d41006880141808540503c00240074402e2480c41d40d90058041c180580342c03d648048061340d900d4981c40c030102003 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 84498769 1250 84497519 84497551
    0x6020d0b18060901140306040323040303051b01050106050d0b0d0b040b0406050114010203182e02010606020c0117070e13020a020f030408150c07050a0804060f090536 73
    0x140c980740c3c800340e004000c4040d4500384050180b021940f00c1d40010000b40601c1018000300c0f8046a41042c250b0300051840401c43c1c6860722441d004202d42c4c0814440002100d8040b512121050706102d424125440d13071b1600d1b481e00701481c61801c06020410042ea500203810115840841e420030380351403165115a00c44501e500c0c191400008481040c7c000d8003000b800c08149c02d2150f6000011100e281200310149410885540f002400205110140084e0001200c3c5502c410203902c2c44e42d48010056034000b0304c2426216007003265929003401d0814009418002079544c004458001e694000381945020901c80d1240c0012484512002c18002d810715400903480c0031403641488405100741008000d1440d20785041e0405507101c052400c104000c84c2044045001e0301881002c603081140d0020540700350303074030074203100419400c130b40715002c04180304a9030409802d10030202501555002020011040301000d03020600b1a030900201d0107102f10b0078100c0c0780445072202d003075214080541136041e02e = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 84500019 1250 84498769 84498781
    0x150405010f0506030303010b1b030d0c0207060503060d06090204180b01050a080304030f0b06010c0c030501050a1116080f091801080708161a0405040f14101206020d0b18 74
    0x311690034001c501514079000c2441055a00401281d044031111051140c031400300b03e1100303080681000c1e802440b40b0002030346440031001c41e00081392802c200c0d02641c103101d9070b4000591340d501c012180380754040350b0320148400044540d40000402800038000140c09030310b0081204486120a4003a00d00c103100c800104054500b025010014004030805582014030315541c80e0b642040c114401400080b0a0002428036403186100580d03698022403030750725080e981e0034010b00070700098601c0c2c2145810184400401c4048000311600da00030b0441902c051011500d0350360480d0011014800258410080e80d4034a80c0c4002622a00d03a62100c0c0510840d450514100c1c42c03d90164007180064000b21107940e001e440d100345d101d040f91030516950721003100e0202c8911541c420b542129a0040c82e20075550982080796000401003950a40289055190314012080000c10352013000401320002e030709000017070300700d4000d800345040580f000301d03d6010102c0003c0c0c001c14402010b02950444604001e2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 84501269 1250 84500019 84500021
    0x315050103290c03040501090803131101081504090303110f040e07080f070c02030717010e010b03010b0f27090d03050601081003020121050109090302120307170a06050315040501 78
    0x84104010300d40800d0007402a40a0816001c02800d00c0840d03c00800000c09100c0c0079040504c0c072682c4111301d25980d15090300c0840103d410300c01c1c151500ac1c1e0f0100008595401000164007886408045544050704881048003607c62941c00700e0405851301c00c0f4550780408c01d006408492000507440392640e041c0010501c880800901c4a010044c101d01030001c01000b0140658201c4114a00b1440b80c00c80c2d800468034040d03040c1d00111440d100245404041c00d4198442e24403041c13170b007000384283c00e03800e0101820b840c100a001507020900f1000f030815850810b03120800103034201201140180c456140000200080701c0714416508040f0042d500160b0522a09034000000d003889581400c08140d07000400183c0c6c04024184550b1b400c1c20310040050b42d8645440c2c00c0d00c094207000070360315004641c020f001c3c0304000310094842d14140440d941d46030b2003503e10400d506d641d0070131044c4c51034200018100018102080c1c003555204042001d0314140021110101c48000c070380824200703490a28 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 84502519 1250 84501269 84501293
    0x2030709050a09320606030a0b13060905060f03060703020c010e07081f150608040302030c0601230922020d140313090e06040209070e0405090d0f050408030d020f040315050103 77
    0x5031180300e0f001d134080581c040d04900c3c0e0000070a85520b5200c0e9120f100c13440007094164100303a4041d9243c20a810078102a412075020703294a01c5003800942c4842c0203004000c4130044c41c2d194141c0100d0000307513a56120798041c00a084110001003641075a0685484c00c1c440c10b5040400681c0108405034050200300060710002c8007210301c2080030150078042041401103e004000c00c000030761012805040c401c100b52850900c45606032496540c0d40c4941800003201d503e03248040b0017028404140b540f4050401c18403890030b0341a261044110240045071074003001900b03e9014405c9200c1c1c0c1c01180301c8404074104844940001d40d510200100c6c2800407406036030090034000e0604590700c1940302c1c0030901a40003941566402103503211003100ba01c1c0070911100c2c03560070500d400200890903000003014010103c0c0c903143c1c060b0000800c070040b076071442a401240f41a40c408c000b40994840154001c181441000709418205616a5610700c2c016403000b100350542a2200018024460300030548 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 84503769 1250 84502519 84502571
    0x703020729090406230418020105071103030c03040306050f10030201020d0309060204080d05042102030601120201020a12050d0b030d0c0602090301021306110709090f020402030709050a09 82
    0x66440e51803481c141d4041d240c550040c5200044081200180e0391510b8025802400c001d00020500c2000c07401c40352103c0c002d40468034070a81c100507900e03d40d5203240054000098060391580e241221a0f12103203001c00600f9882c0c7e805100410040702032410900290020358858800400c10b41482c800242c90600050414900c84d050541e00f0401071313030002000c11000c2d0306c5050101c0c08440c5810710000900072980f240c2c00782d002c2c10b012100103681c00340003002030700c14095505100c590441c1a030640314591010080d0135602040c014840d8803840b0018855861051046501c2c1518550b12001c6102000b000301d0301250340170a40b411405428010b641901400b503009103140c000e2543c0003010520080006041241d000034400125182034040f510702c0e9640d10007140011b59101001031034030000340d21034034040c0100040402c6900e8580241c0b48155000051030964001c1502044020350020781074006012000c20f0010306500e6403445080146000c240000c0c1d400580c0c21450f2550500c03c0c40 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 84505019 1250 84503769 84503789
    0x8040c0602060705030a24090f0f090809122401140102060403051e04050406030f02151201090f1b080a0c080910200f04091a03120d0603080c010207030207 68
    0xc1008080c2c0c003800780c039803080c8500030209030118010700c2070034221300101f0803105401da204001325a0407095004481904d0020500b0000100b05100c19000c541e01140000d1194004015018092811103c0119408004400d9604081560b031200b0003040011020545036105140100311030070190041010321182800904070038a4160340c014102c0c400d41c0c1091f1290f4041098184803d001082070b18041c04019008102d21520b03420048000c41c802103003203101e200703800803101c06e10f04d80f1416614500349030800390000781d08002d070200242290741050f0080c180d842900400081c000203d0041031110350f21003e11600b0413070b001754184d0301d08103200800e100440040c403d8001c5c0003d2020300c203440395000024001c1d006804d01d08801e00d62903c1c91040c803004107125000c80704c10781c000c00450f610035000304681449040c070048204076180d2030a034507811110701c44950042d110010080d02d07081c4100001d40c030b51641d40b03004c040e4000c04060f9520742c0d4041880b00400d0b4041080c0b078090845921 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 84506269 1250 84505019 84505021
    0xf06080702030d2d09111512040b06040506030304060f050306041112011a123603210103030c0204111c05040b06040603020a0312031103070302130605040b043308040c060206 76
    0x3907a5050306e0540c81d990303004000c40305104074050454015502c0020108411003a40e040c1420305600442040d0b4030103110b00c1c0792802061a601e0b00008070782c104d90854842280c0c4842140d81902d0075040280120f4005032a5501400e24070901c40003841030301201041d409407541008003031101c250b100d040e1640d4141d010046001e84490721501168040010000916810044004211842c030a44240200004000a606a4900f004c00901410660900c480202d22040f480c83c10b23a000080c800035002c030303d2041c09800541040d8200300c81e9109489901c0d842d003083c02d58014405955014a0002143d445080c042040340e1000d41c0d907049103046070240030080c110b400269074428140710080000d00c0d01d5613a408003074040d4000800b0440004c900c982c8078505403d003e8040c2d0b00c010030401900f1809440403900500580548040d246681c0c08141440e040ca2149403003100c82038449041c21f62030b03031820b90a41440c000038820201c155558000726040915044160010365040b04082d500090 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 84507519 1250 84506269 84506273
    0x302030a1713080706390203131401090302220b030307050706050703020705210105091b1201060503030310030b01151b030c0506090717070f06080702030d2d09 70
    0xa0016505400420f407036558289071074400300038011610000c2054140c00c651492442c4442400c04a6a000c10826002c407201c0040403078591007001d880200d09502c0400600c05585403480c051598134043c10010a819101e80010b014181d07200308146808000d41c155030742c0c0e22840c0c000c0341440002540114241000c0f0380d102a1280843d0040e90f081050224600d018188200600c40091001900700761b940e0507850900040700000031141d038401c1d0700b0000801d071030740000900011500e031144c0701c144110804000b04450a0f81142201d803c56480307007004105550244011f5000c4c001c160110401c507031a45c5001a034940d0142d002c0380b0100083d82c48003002c9500102c00000108402c076551081400c44d140030350303140c108494007810034822581040102c0c02c0014180c0d00780c44400e80c0c40c4d40f1520701d076500c1c0d5980b03004500500011002210003004000d00032000a90840100c1c0103803428180d100064800312044000190350754500c1e50700310602e208001c0c3d444001c0d503060359802c1c09034008075 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 84508769 1250 84507519 84507541
    0x1e07050a210305031b160b13030905060a090b031006020c0306010e0c030c0d0513030315050607060c030209060304061a060a08040f060b12030706060f08060414190302030a17 76
    0xc550180c20300000100064a0740c401d501007032100d8001ca43d84980322202c407550884000c1001408981460f110030100351501002c1000808c1d89605541d220040c6003051305005680e01b02c50501414031a03e0100881c8840795407020714401c52010031400c000e1840e0500003441c0c0044000107900a0700094014448100c0e41202c4542c04030a40c01d00310390b070343c80700840d403c458407a0a1058840302d241c602807003003c200c1807000d0011380e40642c0c2d06004440341d954050029160b14842d46504c40e804105450005403190011000fa1204e0300700181805080001306129034021a4210740c0d031562120b0404074039642c0e03103a1702e81c501429500c1030b003805107295020b04002000b03400600b45103d41d4900c20700700700ca0341e08038801c08107010342071580d90880700c51055500c2c0c1010404864481c109500450100d4500042508a5917a08014031181d00d4548072426481e00201e2003888500854040c000c403c0001032000f441140b080c7d00a50342ca20924000400d1011000e85c914405e410020034001c1c40c9202c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 84510019 1250 84508769 84508829
    0xc060a09090c05070c030803041103061905090a0b010b040306110f0306130f060b0d06050609030c0909012703021e100221150a06030504031707021e07050a 68
    0x49107800081004400310251920300030440e0040500700d0240c00401009500b001950146202c2c0b03281c0700c05024031404054880c901200c920030703c0c001980700c04070441025000942c110803d4802e940304050f09440301c044040d801d80050403c8940041d040080000a00c41c58070000e2459403000c1c105000c01c80100140e01c0068000c1d8402c2c04000400c48103900c040c1c0c08901c442042c00010052940e48119402c801d170030082104208a03d480b00018190800d4021248078120042c060803000e0b0700c941c100100c114000d85216025943c82d502890103812881c00c880302e900312100c10503402c020510740240b501c1ca00300c800008820315110f108030400c90011342c414441101d0300c6e0141e25007030450400317420042c48642c4480000742e03030401c0c0050032020000385070002d4401d03103000d00c915469810544c11343c0c3d01602c0c01000161822803490001040c200785d60340000240c030546056a44808000e2044c54010016110075004604208050f280c00400840105079184820292201c00508140c0d1540 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 84511269 1250 84510019 84510029
    0x90507030210020102120f06010e0909060403050313050f010b0405090d020607110111180901050603100504051b07060c0306060c0302120c01020c07080102070303050105010e030c04090305090a0909050c060a09 91
    0xd14208048071600030b4054a2850740707030b8001051b19240038500f001d00f0020586800b0301185a095090000d030900d0007105226803070f224000e28240c0c68540c3e0841c0c5562000f4034850034500d50300e01500c0000e2050010303089004512001240c020a05000c00040b40c1c0080c20b980103541c082c0954424450300426030640c801c1d043c3c28440b04419a0641590140c03c03003600d0204a45400100907802e0f40c04840c02c030400032400d81c6c3e5001903a89403400e1064070f10041d20703182c407200c8018004000da0f10342900309a40c00207138000c83c84648201c4880b00d2145401142c400c4034295200c00768001d50030303030510411b8003c01103880c00345220b02541d1006511001da03042010041000040d80190204017501181d0103260410304603011035640e8070013a4001d4001420490019041000022b950b41c445c0718071500c0002c0040241c8003407520368040000400d00030700f044044c0201801000b60940d20440d6200003000e600101051402080c40e00c00e05040c100c240e0a81300703c40922401070610362160300300782031b11 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 84512519 1250 84511269 84511279
    0x6090f0510020a021203130f0911090616020406091107050c060a1d0a1a04080d0906090b1c02130302240909071b12030507020a08031f0504060905010e0a0905070302 72
    0x205e0741e162542c114070420101410a0b201e0b9140010320000300e5180340c040751f0707204204000b100749403040c0004511804020300e03440001804000c0400d0017043e0348112051000b000021000d60f02d8011005803405c009080c0700c958408035514040c08030502c0b0301e141c8400c04072912490000d0310318019003000800410401d2410f100085035005484031031603e005860400060b0b09045d00c0d8644002e00c0c0c2d8850702031f80d40140104062030303080600607241d0070300b82c68198075941d120a0510098140a400075071200c804680131a010301c0b02e0303140b50320040171640010401c01924a040d4010721512950107004000c1c180d08401801481000e841c050300e01c8003c00300d82d000d0301c44d06c90007421115003000e5094507620000c034030091010400912070030100c3e583c04c1e480078002c6948910090340ca59618241c00382c214441000007541e181c9051044001c039030007141c4095a05078135a004034003114580d41126090300d1344d0340010300c8002d002c9000f182d400720880070140f006030040e555080e00c50103d40310090140e = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 84513769 1250 84512519 84512539
    0x1805010206070c0203010b0607060c0207120b19180c150203070b0103080c1509030403120c020907110106030c08030c0606120c0405310308010501171911030106090f0510020a02 77
    0x11741e020340000c0309403400140001c0d00d8403050308125008003958405031000d4424030400050b848100c0c00d00900d5107030032481c03440d4559280481d11030f002c0f0316450300d0030345159548214954a4450707030140c08000c1c010b94140c0c00385030801c0c3d1060911441e2051081c1954000d02c800000a05d0f44902c0c0b9040d203a1100b00a0344409180c400c0e58600405001e200d0f0f1108504030400013803800000c0a80201c0340500804a05071840110a039842103200402035001030300d000006548034000c441201e8140703541000020003665070f40f141c00b00285030390403502c0c654000080d102c0d50384404004040c0c00100445584000c445419800c80d92006d10300324690040340c49200181c00c22500f00350a503214001078031014000503400406c2403810151217000c07400b150084001003025482151820707610030143c80203940310380b9003440c00015025645d01052039140c0300c0c19000134a41e04840135600030011611180249801d08007c050358a8107a08464020340181c00c000000c1d55000840c00cae500c0e9010f407030714040 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 84515019 1250 84513769 84513773
    0x21e0a090f06050c01140601050304141c03021309050c192a0311010507120b1c050609010501080c060301151e0c020315130212100515011805010206070c 67
    0x20880640c00380e0362407526040001101600300009100e4070b1995802040682008503500d240d1500540348136001031030078400540040e0f41200282c0c04c880c0300d80129040c11100014100704000038070260350020350041103140004021101c110050314500070240244c2c60607001c4440e030350050443c5601d508070101c241c84801801545881840700612a040c1d8038201e03ca2080d881c007009031f02d0200c00154018203807121050040c400c99000e0301c440c1c0e40f0b020842019442c0200a000c900c1c0001e41c0c001d00d610003151440c43e840c951001080d1055001e81202e04d4000512800c403a4140d00415540d005805040a0350f60340c5412681076800e000c182c4849150b000d201220050454000e20050b0440902e40700c0d161074014690315901c0b0301c04c5044442c2d01040158244254000b078511007084540410f104005203480042c1d50340d102c2c0d02c0c0049500761042c00414900f42c0318283c858074a40510802c0410581d41c1c002d13101841b51101c90300480c041490100001d503541c100600301c0003007101441c80c00c02 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 84516269 1250 84515019 84515027
    0x6140a031404060219140912030d090b010611070806012114030d0f020f0d1d01052508040b0c13080f0c011e020a03030207030c0506100501090603021e0a 67
    0xa07081c060614440310600e00382c64424001d5010280c2028407403c082010100301e4410071070b29140307002120341181021181000c2c0701c2c0030700aa21852103d40014082007440d03248034828011441d00500310024654035000c0043d1139040346007400442038002c5502440900000110203044508071021000c42511200700d1400210700004010003501001d501d0007040d440000290003807030030004041014901c4080807200300c0c8285000d10303c1d50402030100404c01e40d00c0d0b030b10411000304802c07400251180060107443c21110b00b02c5a85405808403603511400c0030940010b02c0c4984c1490904400da4249a1580510010018800e28031000d0000350003034112102032241d402003044008403500090040c82003521040c0c00c0c000035002821403035440319454501603200045580c107401a1102c1c28040d1003c6010703501c884825020300050000e5500041c2d41088518810520403c40001c014146030004095044d01d034803030701c10540144a41001c1c036001118114805020380380140c0c0d0f07800148c409403 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 84517519 1250 84516269 84516281
    0x1030b0d0302060a0c110a020d0f080301170c06030609131407080102120601020106060f030203040c030b151315060507020a0e0705030405010608030a14130e0108012406140a03 77
    0x50300002082508420180c000941d41d020341d003804410322107010700e50030442d1070405112028006510081549015007000000e82e0103a0303000c1d992900c0ca0503529164003001e60b100382d1150907aa40c6080000c1101c61040c003203c41e100400301c2e18036196003807150003d00004400307480303c002c100341400c400b010000c0d402c5a05034000034680a8402c82c0d0f9031768020a000790003440028280b101100d0000d0780542c41031140c1d4003686c040b80c80d61044003d000c40210000c0d00300501c12507030341c501c2d100080301080c100f001c079901c1090300d20342408090005005001041c004882c0160006041050416450b111a5070038001c0d2806032030019290642c034000603000807141d50080341403140700003e0040742648031006610607802800241315542c0d603850441d650f449094903c80c00074803083c80e15454000880d00800e400e2040340c80300300025449030000091040b007a071003c07043d43e5540107000180c44c2418440384003000200743c1d42c0362252a141c4041e11134a0a20000459590000f65080700d442c0264088 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 84518769 1250 84517519 84517541
    0x70b090118081b011803140708041806081204091410060c02041806050103020a120b0118020c011e0e0102030c04090b180709030c080105060f040f0608061e010501050a0e0f0103 77
    0x2d0245d050b42c20050516a030f0180d0003139002507144001d003e0031080d000202c0322955409800c40303240514041031400315401c5080b44100083d1514030000e01d011041008841d442c007400748256840d490300f240b84040310088081d1103d40401e5408000005d107203030b15604112136842c10001c4c4007400600c0018020b203a044696035400030310322888814409164400c1c0d0590744203541c1c11014540300c1a002c2d810500e81c800043c02880c140006021a41c5114640707152000c02d002c0244c00c00c0f100f1009036082d10201c8841030742451110202c4ca58080050240c0d80202c107a000c002c514505042c81806414482c6000340350107a40c8803030010b95251190f002001c0e07010400c0c45540400e007010b10b0000c1041516100a8030a6103001501042580b81807080c1ca0007120000e000c42c40100e040010710025148019140d45100d5072290001501081801aa88500e2401034022401c02030680c01c0343c1310700c0068102504012080c00080c04243d000f00240d0000381044442c07510900b0240700480c003500e00780081c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 84520019 1250 84518769 84518771
    0x3030c031104030503040620030a031508030a03050a110a080c03180729042103140c010f0c0509030709090f020402070305030a0b04150909051501060203070b090118081b01 75
    0x800400c4c003a01001901c00d841c0965a100b5030b040f07100700710b02080240c80c4100e04880c0c0040141613020360081c0d010a01240401500180b0300356641702d04c0e800c40e000b4800200110361240200a08c100d4544607146c1d1200c000c801083c14191066002003024000400000000100201060b0f0310580012040141e5150030101c80c0302581340c1181c00300305c00d624100340c04043c2250303401e400381085640948080d242428030040c805103590f5034404c1d8501d6002416814842e120003801c844044080003400f80040320760000c5040803446000804440c03003c421001006418008071b03d40ba41d0100b250b00850300080004645801d036820200b10114891000944c082d00c0044ca0310101a0080c019600c600d40056003008001d049900780002e5880c0008050342d00300d05c401c41170020004a50246000c540650300b2036a10031402c08250f001d6081c281c0041001d6440030800004100080b12002c1d8025100002404075074210101d41000c000f201400801d0310502103082550705920550840c052010000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 84521269 1250 84520019 84520027
    0x71e2003070c06050c120403020d02100e100903020a0512060601050a0311040906090b0307030b06011107050a080a051c120b030a0606060915080402030a020f0d080f280c03030c0311 79
    0x50141880d80400440d611501446c1000d0f1040c6e10800151011280c000c1d01c80c10f8144495420020b1401d19a00980280701110841d94183e03160711034040086412034442e01c407850f04600420043e0581a404684117414030002c04003840c60100304150881d00a0900d152942880c54050b409460012640300703d180300450300086007041b0f60401e03030847ea0500c1d010410761030000c0501d512224240400b0303000e4031080002c2011940703d02503071201c1f4000c074000d07603428a84070800503505040540c45010250301070b40c0c5410501509000c0040700c0424081d10481e2741d0180d00000d0101080b50a000ea60b882e540c0c2e90003025900c060100740411540101c0401c0040c1d203070440600b402026000c1e461000c1c940050601e0154010665207016a40040040c15108071a5080089104880702003e802601c0442500000380c840409440742d002c1c45010103840700042d07100a06203406a0815281098030b10408031001030b00810003002e020b4040c5000704501c40486819009002c00704400d5a0b0058001 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 84522519 1250 84521269 84521279
    0x14120c101e170c0c060610030b0405040501020301030204150305070510050d0c020a0501060f05090604090503040806071e0804120309050106150509090a0c0512090a1a071e2003070c 79
    0xd1400b41001000309065161280c0507089218010010b05454903071040010880f0351a0030500c0d01c025100914010a809980704007007030541c1d106076000c8aa81c1c2d0080010f2045241c2030280401807009000c030103200302d2039a191680e44000501c02c860280b820002014121489442112a40240c4601c20301c07c51411481c02036030f6680c4400305450a510b0000082044e2080700968012100d00a02c51102a1601020000105071400045070381d0304c020080011001824045d2078030500d401c0c1c60720f81c0c1100182410101d200001c98a130000c1104500402002692114a0300c1c81c2031001c1c900003425000f14070300640180801d422058032a4034440c1d04258542e407040040200303840644003400b9549400020100b42e450080c00080868024440000d40c4844002603e078042160021a14841d2445d102e06c1d1001c6000e08042030034222600070804039a4200001244060a014144814805401c401880101e001c00c00d49500102c0150711000e02c1c40800907940055046414806595616 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 84523769 1250 84522519 84522527
    0x30a0210170106030606020c12031b070311030604020904061a1207080114010602120a0e09010902030f1806070509011806030e0f03090f0d08210114120c101e 69
    0x441c080c848011000d070004101c0b075101e4022a030499075036400404400c602c41e001c02c403a07229001441c0c141407009104040713086600c0d20848615840401c0504102c50170b508007012107060341c0703000d58020b5001c0c2d014800162070f00c1091540c03140d0081c3c000502e45100c60340000c1411404083c1c543d20003070003600c004221030041054403c90300148000c00130704450f08506171000e80c0900ca84070141c1c120208512203604901c00800302101d0a180000b048000800011032580c0e003078200d04440381c0e008c01045001486808503c0d04003c1011068a1140424105641d00d00005014804000c03011030f0403506640500168140d4485500f80b6490250712648001d000344503102030420b25204540d4041d40120004c0112800010042d20240c00c840380d6174184450008040c0007140c000c60100440c4809039200132401c403480c400c0c1c65000e02d065240c00d58200032079401d400309900c00e8100c2d11912000000001300f211410205a07210203000301689425190403046400580a20340311004882c041548 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 84525019 1250 84523769 84523787
    0xe01050c06010602070801180512090105120a020d0608031911030d050c0c15070e1e09070c020111010c08160905060c060a0c0c0305120c16060207021509030307060b030a0210 76
    0x220000800200080c070240481d00c0c5602d07100948290000e03900522b02c0d4030050000c0c0800001811b10b070349881c500002602c50203404560080c1156800314441045281034000c0c640188800c8006500341400940040588015809030700309000301d009072444812810700c280d85400040b048100300300e10304072042d01216030001c0d019803040d00800450428401040141c107015100c0355580104a40f140310500500d1080c1a0a12084590010240c0e1729a82c58041192144c076040c0d549001d1100d9a20025140301221000d00f14140d0400d01c550b05050b40c0310701d509910458014590302d51f03510052040c2e4000d449c50700002e400600c00031344203400b1040056051b0090141820402c0381c00c0e030b010384c110b503440035210005000a40410202d030000301e80c0e00c020303500030101c0c4880714a000144006a0600d101002c0110b0724903402241c03040652a06000408400c2d002e280078519013403800000036161321803c40000c0c134851b82d070003440d00320382c508101d01c120040e8040c01030491080c000340060034a80c6 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 84526269 1250 84525019 84525029
    0x130f060f05100f050d271202031602010c0204060806010b12010503010504020904150b1f080c070c06121e05060f030c06030a1d06010308041a0c06070e01050c0601060207 74
    0x8200d880010316800d00701003280030b1000580e1941012203030302e00100d4013584603000107041c003920742010424440d40000b42e0313121030b2a03880c00c2103d208118500700d50b0b86501c0c400b072002550428000003038210010b598159440b60309103420007021205200181c01001d042d00700745924410131b000030466007403410061400d0007000140400e20f81e40d510415007a80e40450f00290840145c82c0030600142001404900c031102500010a882c400c4c07402007440c10602c0110800d401c0d50750560881810341142010707402c0351150705094a400700a449601103101c56202d101c04100341d6503c0412a010994440c110b0481e01c2c10310700340c1e0300d000c1440a0002c0d000a0350744510407e4200d80304082481d0024120310301160203030500b811591022030001c014514403000508000740c0001981c0c0f40d403000d1107610301070b42c4144c16a5031236500781031101d00840c01100403100e5441c410040c0c0b10741d440e070014120343c1c80191850080e40800361500101d0392303405145140070440c4500c1002248154000c500d03141694 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 84527519 1250 84526269 84526289
    0x1b050d090602120a020709020924031f0509040201050310090203010308090f09060a0306150801110309010b0904080301030813091406030d03180f020117040302010902090a0203010b0d0b130f06 84
    0xd10fa0680801d524851209128050703440148200b041560f1a000352030301c40343c010300400c44603155292281c40151403410000e00c4442c00010822480ba441440f1401a5099040200d9003424100481c0d202c400251000e41884070200c0015421403011034142c001e450b15a205544a50f900e10300009a40c000c090910b03c5803070b1546459032242000006688a05001000b0300812031950f2034000c0140614110300c03072512180d02d07010030354800034010855011011468656203103400000107013100e10462005200700c01c4030f400d0101161954065905417500f0101503541e8030042d141b11044480c4590059202c0d41c01c2402107140c0f44004008103118200c00d13402d031075403400c0001c401c404550301c201400e20352500300c00c11100850001e0a055450074818103000002c41038510706114120b404640840042c0c0d145d500d4601107051400f032942d0001e0300f40d02e0940c01c43d4100081070410b40144111542c1482d0348050f1034143d41d540d82c0200d100244402030800c001c0c2000070706a000381085000300050740b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 84528769 1250 84527519 84527533
    0x10606030509061503070b070b0f0610020a060b360606030c0a0503060303090a03050307030314060109050d031e0203041707050105040b0313200102010b0a080d1b050d090602 76
    0x2190090145038480c11442018024035610030800e0301c0901855200d15405204e05040481d4184555000700800c0e8090120b101d03051410040d5044080001820b05000c2c021081d44a0401600040c01482c01c2d54000800f1604142e24000301e204183c81c6000055601d080021140f5402c0d58140891803001ca18582c5d110243e07103d01c1408042c1c4000d03502c486000000700008898140328802854104070014242c0c1e141c00382d84000a240001d407500f055440e41c1001600608142d058072a8444c0c900c0d2800f66800071340360020029025941d01e104190103115100303440810148a4040d41c81002614001903105080e031040c000d550341c0150003000c1030a009000f0380141c883c0300141c00030403544140e4555140c00c0c242620000903400140140001c041c24802c0c5000041e40c0010704540c01182c0b4180c0030100804600090948400041c4d00d406540c00420600c525070002c40d550700c10704601e0a105a040780700c101203071b040c0714802d41e015049000b441900309030355078445502800c03160f140d0308407011 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 84530019 1250 84528769 84528779
    0xa180f11090402010905151204030e011205062101020d0903020309040e0f031b0a050109060c1409030d1103070209010e070207060203310504020316180302060304020909030424020106 80
    0x1d40740107a40c0a03011a220744020080c40c44d005448940225941d981d0310304100c1c448820010701d04042e981140410034002d070400d06564003d620365030038102034400340503e0030300c00049010001055081100300c030309070551080c90720b4250111222541071240420180003607090081d1686c0240180781e215a0a11701c001d600301800084c0e50400130500d0014515007a4845d0140b20b039074041c04500e45450103112100c8001c68070a00c20000c13114020324010038100f14541000b4006565100c1080c400c1c1414041c603d0036480000d894861058a81400c911035003180002c54074500403650000e52096004002098650345486914082c0072140c0888070700e82d4a814044e61203014040101e00d444204106041002c1c0d08078003018814a920b81c1d5030240c4a0301c2e640810181d90007202c501078111440100201d4181e031020450000d40419030991704070b103003140c0c0098a5444003070130192094a090b4081140800b0900c00c803001005100d066242c01c0e0f5081c0c5410820070110540f00025510b40b10b80011 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 84531269 1250 84530019 84530029
    0x7051b09060301020a020606091e07080403080c040617060310020408070e160503161701060216090b010e06250506011e05090712150f09060f08060105090a180f11 71
    0x170054110760040c1007159210b5050142400000f40144499140f4803065007000d82c074034854601440d201c0d84c95900d240f506003409810707058013410001c1c40c0c02003000104001544004466690035404243c00601c4d21001c000034a440c02e42c070104d82c01c3c1403002800182c0300a0000d05081280c5520b03c0c901c503181d03926200584192004422000450010000a4161900820001611240741c1012000c0840840d00c030142a03500360400b2016034080d0202c05801d000c81801c4400400c00f600c0d050100c1a030800000381101c84450313825004d0440440c1000708020351607500c548400640403200e10400392803d006075548020b2140d46c64228040688204030401c00d00c0100a03100d0240440545440d800310032901400300c0481c0c880b1070313540c4415008000d00e8510101004220151400c182942001600780445803243e00c0000340341c003e1003003045541004944941102e508880c2448107540701c01ea0780e009451891180f5070401048000c0b02c08110410802242e058000c0001d4800754084a09100f = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 84532375 1106 84531269 84531277
    0xb13050306061f030e010204120609030801060e0306010b0708130f050a0602160501050304021212030109110c152724070e0f01030207051b0906030102 66
    0x112034601007003040d4001a08941c02241c1e0f01001115000c21a000b0415605060701c9004400700700310203505890007030a80012800540c0b07000d1074448018088544100d0103e92500300200b80382c0d224900340000c0380e00180c01402c00364281115a40303541c11403101117460703603c100540b5103030041c003255100003000814840c2c0d4081c3d0400d070130029607515a130041c00856002c100103d6030240b1124444003111f5003820802c1d90b944860011401c5105a001e15550750700c204c40d2800003182c030101c0194100c420210040200007000310400c815403050404030304480d400040f8400c0103a50300d43c040c6410000f42c80c0062110031403594055a0403040c05032a8000f900f02c508007007582c0441d0030004500e000c2078602090549008600a070928100d4400c0b980a0400ca084003c01e5901035812201201d0300001101e00c584e40741102422a0724036603071094001e0003060b02081a40c101402a1 = true := by decide +kernel

theorem cover : BRFrame.Cov 84352519 84532375 := by
  have h0 := BRFrame.cov_init 84352519
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 84352519 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 84352519 ≤ n) (h2 : n < 84532375) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
