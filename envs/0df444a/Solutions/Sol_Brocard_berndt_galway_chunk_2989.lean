-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2989
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T08:19:59.953989+00:00
-- url     : https://prove2.me/submissions/bc9767b4-0d04-4e20-a6fc-f10014c76dbb

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 537410071 ≤ n < 537589928 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 537411321 1250 537410071 537410123
    0x703200405190e0907060f0527040b0307030311010b04050105010f0e010c0c1217160201080c1614061f0909050c060408150903070f0312110d0b091003 66
    0x2c0b18400035140c9000a4111020305624010252800504905402c01501810b03082c00c111552007044800c01c2841820300300032503140880b07802103090b00b01c9407203520000b6010b00740c0c188c2c2c80c983c18003801800004140d0070187d4002d1200b0310780c0c02032240107180010131089902c2482010302251000c240d60600300e1003607245100800c0c0c1418078925540e85d5031144c0d00310b1240760f0004801d000710450faa00c140104035429212400341000c2c41807800400c1c10b0019040e0341201802414480c4d420080381d404226a419600d090801222850040c0e101d410404130f05020b00001c134043d4003c00317001c2050100c610300020b1070a81350309005030010f07250074800002800201d1080c0c455003d164120003c56948800034401884603038010458051150300d410a40c0138080c3c0384034290fa0080010200280160400029550300341c14080700703610031124548043e0202000f000501a0000f66a051043c0b1a922842229505403007040d919500c142202c14138820302c1c040901641c501288501e0180401c4a403 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 537412571 1250 537411321 537411349
    0x50f0d080d18020f03010e0c220e150f0f0103140f060708100503030405030703030806150d0c090509090a060c051606090b1e1303090b030f0703200405 66
    0x1000d15010620381907508a9551800200c42086030500d0302042d464030903140018240c0c02c5000708207292603205d14070b41e41d80c00500d0a80c01100341c600b09585040b00308052a0701c00d0b07404035040c84080004070840b500c83d403c11019514000c068000300c3c0c0a1081c402c0034030700c07840003028200c00d241d0030354492480c840c400c4041c10304c0714856080030346d500100600405014140c10b440f401554100b4600309608038025030003e81c000e03481408200b26558002030244102c0e901824076404a85070700740407900b00c0910032600c0422800010b1f102c0715011030b5900c0307105803920903035802031025269030403c0340a1400781c0b10244541d103d0143c010206010394401101a03c4a050203864103d82820300c0d1030360520610141d0300c82d070f51fa2241d4001c0c03162840c41c0d140c2c82000900b800f5158680c1141401200c080038024100c2c0f10707070f07244600040501410410024006810317040c0d8032841c200b842595580c01c11124000041c1c02c00c408050071801d00c210440410740b15084003400c0604080c14009400ca05042c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 537413821 1250 537412571 537412583
    0x160e060f190e0a060f020303180a0c030f05010f0e0c011409040e060603240412171f05031207020f0a0510080717160827100f0204050f0d 60
    0xd01100380c841480c440506641e039200d40b254401c81c802041075140e900d5001d2002e10103441c1034045ca175a404400c8903449211843e0300c0801064803208103203484940e0600a11b5442c00107000f005001003980b582242030721910003401280591802d10043d940268512041a408007425204642c01000800004540d6421060038054042c0010b020f4400081d80403080e90800014020a400e0900081902144c1d440c01203481d13401102c110111084c0003007016042c09005850040054850829400302000c9030440784007a080c04940011031140c03000000c1c0382c4181c0d020700001d0a0070003103601c002d440160000c031400c0158a4081c4082002d596004940c411856500400e0750355445046941d6030302542e42e222203500c3d000d1009010180511800ca0400c0a20700801c00c1086010107601040c00007490100c40d99240c11390000210041c603200d1401d2402d81d80d0a0301141c00e8001070654498101d2074080c002c00c440619400102d1149001e15500500980f07069941800c1c22001e00c294144218 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 537415071 1250 537413821 537413827
    0x70f051c20210a170c040312051c05011716210609080c071e090b040e0a060b210d0521040605040b0915060108060d0b010e01030b160e060f 61
    0x5000e545910042840c110711140000c40c4240425130b00034000b0201c0b0b0071012900c0402d0800f012505100e014510000b010750030303100700c1e20b44658070841c19200c200d03501c41c0c800302e0a03039a9500d800000c0d01e401d02a20a0039491007101000c15600040c2440751090f0b000c8000540604100c0070401d6144004010351044008040d0900000ca6034071402603814025402c403500c1d07401000e041400c1038101e60009005000542007200701d880345c05000d10864540341c0000401a003144003040113003a030101410024010840030100f805095003007004400070807950908081c200904403101079000c0001c600569124100e801421070181009244800c0741c0500c2007904c02031b00300410103039030046a0031034540303848406100800400f1000b242d040044a0003501c002109008110807841c2c00a00c6035040000d854003003001c1d615002a06030a0a07004001c100c2250303101c40240001c80304c2880b00b1034074400400c00064000c64601c18066403003895590300c0041000300c80070030900c0d401440701034034506130030 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 537416321 1250 537415071 537415093
    0x31e04030816021e10050105060301060f030b0a0e13020f180115020a080a020d02071d070e0a0504020a0207080c030a050d050d060e0115030c0201020307050a080406020f070f051c20 79
    0x4050104d01c20301c200010f10f911148000d109041e1030060f448140900300070f00040c441981c0001000500c9111803034005660311900303000410014055201440061079a011702c110310106401080403240240d4a1008100d164018051305042200620900703503070310b03c0107004414101c0481514416548100d0b81d009a182c0c651502d154032060300c400c05039000d0b9030501c0d19039070180f01c0b6000802c01c184d1500382d80d45c107004135294260320061105041003012615040c2c3c990355418104090200504110340700e060707891010f03588100300c0c001e1000178825408400c0d568900007a02c0c100381a03029002e0103409826910990322500701444150300252524004038103402d410358003030700805522801182780c6100d01c0c4050f04036800740d4072020840e4010010091640d400204442411046140001d2181d80c5d5060000c001c0c000c1c010311910307a54002819005103d04280d111404c14080d00035690208101a01c5580741c107071404800d4003080103c01c2e482c0c8030500c01403d510581179184207407440d8802c4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 537417571 1250 537416321 537416353
    0x3140307170a3801020c010909020313050706020a02420c0a0f110a06140702040605030d020610090203090714131d01060e010f1e0f0605031e0403081602 67
    0xf290510350300301c031501d5000b0010303060b4520541d5450700070f0000e05458a95000020821691400344d200380c10b40000105060040b10f00340440d0b081d4012094400d50ba1711144000c2d103420617658141e10410820080e008103482c0c0e50403a401d004200102002504441d545140e0a0310101184d0703801c030181440804a503540c14480344a01507c10402c0781c0c001ea115150200e40c1c0b0710f17980b82f1b044c011403681c54148401030300041200c00032600c0401c0035031521050706c0000e000d000c054002c146c26008043e100342c1d1541e00007403030a009440c00f441c5202a07946501070042203010455800390346034041030082050402d021040c05501d60b015141200d0040800403000a942044d140c000342160820021904480b0a100320303006082c4416180049501d49241d924002200d40607041c8068070110380c0780b43d89501c90005400405080350131100081e0750f280301900e40d4000b10f541c80c4064a026041d140143d004d035140350f1046070b15480b28a0503840341a85600401c04000c02802940b04003e54223451442c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 537418821 1250 537417571 537417611
    0xb1603111203010816081b1507020d080d0606051303022101020307020a021504030b010b0307022a1c080a03050907090f021903050c070b0907051c03140307170a 70
    0x4414011700d5051400c442e42081c6000c144d00c1801da581207566804d44818500024003000b4204030351002100086656010040c40351020095014465521903410007030303810301800010309204010040c40381c0e139403419206032050000198404040d50001d10041c548010022449002c102c8009241c00ba00051075007281d2080d6815800341c2c0c0a03203c1e00c4110710300090380f40c0c204180301c03610b02c7c18180785649090750000c060080000d0304030044000ba01702842006485c945817200688040b81044100c4280d40494aa06445000c0c4460039043c00300b03030801c0560546081d0340145003524260b19900704030000c0401400e4030060303000309400028481c4c024003a810f182e03030a0038030050f03880380c00d1280007030203405c100031007018141003c040088011b40394003030340c0784030b0b4001c1c1d1000700c580c1e2035101050030b01c8400d0708080e0f07101810624151269458000662009100b42c840456000c201d1445030700a0008441c9080054020b030000000748080038184c81c0c000c40c8403500869103a02d40118201144 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 537420071 1250 537418821 537418829
    0xb0f0910030f0606030209031908070203060115020c041e020c010f1e1a030309011809060605040e0a14071808030d1512020f0405070c020306040305130b160311120301 73
    0x703031a107950003840b6040b8030072480204003505003146490303c6000820b84407254801d1181c2c1c0c1d01400040301303081c0aa4101111605640101940d920307603119080c54811203640d400c1000144510202d069440c03c2512944c04e44070007030851014051120305c0000042e5022100e1082e05540790039915001d80c065000f030401241c44000b0404c03020780040003100490b014a4844041a07000a134101c465807004811a02c0641003071801904041c0008071480ba1842e0f03691007171226501d08036002607200e52080291082d541c0d60484c0f086039840300303140c00c425201032144c000b0105a071007011130402809007522002540c001e602c81c2403401d9a80780040d0451300b1200c0c10386083c0f520340c00e0314070300008000071501c0a80907945a080240c0116004101c8850f58002007900850340d480104600318019101202030310342c02412581d45242c40c0c50000c3c0315030003102040d0100341001d000450348441e1001a258040340c846500b03451050152000c59403000343d48031681c800d00598a00484040042008501034 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 537421321 1250 537420071 537420077
    0x10e070e070c24050a0c0f140a05070c0e0103051c02030909011403152e1208030402120f1f1a0423040c05090f0c0304110102100e0105060306010b03100b0f0910 70
    0x1b201400402521500307401c41d01e802000500302a241620344880280c0314104a03519045496007403d10388582d8a0800b90488010010183c0002042140c006100000d02208642e4000010b018100a80e500c0c040e40c044142c0c08800303800140000c50407800d40301d1894200504030b03044405032071404020f079482640c8140080c140710401c6d8044c802d1440d480c400040c00881c0b5642e0651908036029048050120010604e41e400804242599a035001d03107200c580208050320395049005a016a581e4070a104190030303d03214201c0c410300c2d011544620494a900e803900d020707442a44204100081291480d882e501e040000c82c00070400925100c3d56205070b00c280a5a044281000c0420411020040c031030808089000100800d50640c1016203800c0340c3e000c03000345600c01c0c4140050342002464a140540030385041000202ea030720540221b8019042641a24420f0340c036000003400340c0c8000c603000c2108507100c00d42044450030f0f4000410302c1180b5011a107042511500008841e08230803c1c0c44000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 537422571 1250 537421321 537421331
    0x3061e22140106050f16110901060807090905070f05210712140112030f03140c0403061505010e0603130206030c030103150515011101110c010e070e070c24050a 70
    0x4591000c1c2003a5014007041e0508506028840010903201d00c00c4206035000c40349114140f10400062008164090350001c082d010361f0f6854080c010510103045501d00f002864000340001c038048548185801003503103565040f0720a00059003a24964070000482942d40120801e12902031014444a4050901c03039070f48150322010520328070285d482d0083c840f060076452000402c8400c1146540907401649030501111105032040160700405c11040c0c020803c042e000c003004003400c0c2c84002041580d21420040002542c3c007031a40d440107409004442c041441035007800001c0c90002c1c05903030b01008002040c071000c106540460405d030400da07a1a809004080014010091201000034450032840d0040080d0b161080e80072005a408c0c058182c14000340d42281714940c4800c0d0401916003010310001551160305407120381c020108007880b59860b02403a100899014540300210b0302951155039560346074102c54641c00305418100300c0b180c0d0340c6c0790000c505000e030210034015684605d07a10480059 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 537423821 1250 537422571 537422591
    0x106051323120313051005120901060501030f021824160311010e0c04020f04080102030c090f010c111003060302090f0a0e03270604080307050309030d0503061e22 71
    0x2510804182001c60b0741e0700b042c0054041c08040e8018502181c07000c50790500000036145003650944205480744207505260420441071040c15080f240444000307a0b0200129020b440850003207001d03e821030039070052100800c41642c5041c0d901d280d120200c2c603100d80c1c648010b6401501c0c103a88508403108544005890f94002c0c1500820326107a07040c42d0400a0003da9401100261103c281881c0170344100c2e0f0106002040303d0341e100c103445c090f2503204002c6590b802c285042a03515000300c01c0a511030f40c41250410443d500c11800c400c652544480e0390703901c8155802c05c009071030f284011200b0405a40741d46c004056661143e206008038007110305410303c0d04050130700d082510542280c013050b950040018020099503c81c09407841140c9034260180407580d040003070118401c5500c0805640b00204e181410710002100031310480d50704904a4002c54500d40703064405000460301e103944105400301d00090054402070300c408440c8000e105e18901c450103000002d0b92a6110307480c0189960325a5445 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 537425071 1250 537423821 537423829
    0x190303030b0604030f0605070519110d0314130f0f060b0301050601091503051e1e0604090c0306090606030204110d0609020711211209031905060106051323 68
    0x48607140649105182c5030031529242106140140d00811460741e0344005501d04e0720400c2070f04c82c0b007030850000074407070260110300a00415515429504601800c13040d510454024403a8140041150945c0c0341030b540c56003000402145400310070b803036184040e061400010007442010f42d00c140310751030004400b03107540c0600d404c45100400c0d5505100203410140a07500f58119050221030702c80c50081003036900c142680c008110103902400301105480180710071285070003d05600520042c0c0c8011940d07898000700002c0d81c0110902410311140303075809102040c1950007003141e4500070040860b02d942da980c0424115017001842100d2150b000c14080ba1100c058081c0e2401841d042c8001c0d0b0800c11a521955190600e00362864440e01c0c18072008501c10a902c1c084002505800741561007101d820309651000c0d50114400911900a0382189203205000c207241151598221300103184a0b070a003c3c007900e00e81c1c458100d50317894036800c1d0400500005200708100320700b0a4818039032541003966042c0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 537426321 1250 537425071 537425081
    0x140d02031e0108062e0902070203060703050c0706051e0709080c150d092a050108161e110a06022505210910020120070308060904020102030919030303 66
    0x850758111000004201c83d01000440d030b0b03000300c0012200944e034000d01816105000f291115500441450b242c00900340385694050081e9500a400783c854035940c0e40401c0b41103c404680c6450800002c1c008980400d445500c403962000614150380b540880c1c1814525032124101c41d40310000380180010300860b01d051081410800f025100b800c030b1320a1880c078945540c068080103001640d074134403444040c44051044046015001000c0c0e014000d948100002080c41c10300603280481d180c040824803d9102e5581c0c20100780142e5505100ba424546460014400fa90400801c01ca94a0b060f00d0710001c003400340a10084c0b05540c010717929100c01c02010700b144a41540c0400c42c80440c07003458007140001c26041022561219888800705040a0b284801d001e03c500554010030502501202684c0560104540e107244400c0c0200903401400c100d60036101d8804018001840b0a004c01c4860034040c14164000b84140107aa040c0807180c80403d41c80d000801d030b0074283c2080c0d10300c10014180c051240b = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 537427571 1250 537426321 537426361
    0xa0e011b0b0108010f021204260a08100b030c070b06011112040306060909030f0c051009050d1211160203070b12160c0201082701050a0f180c0510140d0203 68
    0xd5003401e41c100d110711003846e8001c2000c9c1414050382e11199500e40031641e079403c1d10b0240015a40c41d1080300c0c10081004208036400e140d07100000c0707000710b15502c110040d41d20502010f10351171318144040e5203102c0e110001808440c180318803a0040e4a88802c00d00c45204580c1d0f81604291300c80b4a142041000e41d8240e90210b14103624010000010036401842c2c071748031103014200500d940900d0300c4c105185c40e4103d60701003407107450043e00ba41002004101a00d0308040395031a21041c2d030030024003004540c400c60842503031100401403801286101ca1002d489680000c082c3d07515950340d40c0181c08580d100c543c20100182c0c15004000e881070510801c01c5140841c0c0c40c0003c0501e010740e00290599002400c5d0142e040308241c0d6040c0ca4504800c03e120b492150701000388294100522982c1c05081d07051001d0741c22500b4411240009420040700795401c1c0e030007144021215203490140690f4010000f80c0d0f01c10050309002a204140451004181109582c0d000603505d01e8058801003d48420042e = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 537428821 1250 537427571 537427601
    0x7050702010e0f010512090c060d0f36030504031202030a1106040317060607020d0b2403060c0306060f04030317010e040309090c0c060603050106030b0f0103080a0e011b0b010801 78
    0xa49400030307680807054a0414183c6e0813002025101c0d0f960542c44c10303202c049095480a80044c0010040f4810707040450100d001c10001d21032002d404001d15403461407a01580201002d80c020380c00c02018a210b46e006644c047d00f807036403516849440e03401222400d404040050381c800541c5d0395015030700940702a40c150300140035101c0c034201550000c1c054604001800400304150000c1186903031074030200c580d1103500822a0006900c941340c049103000c0304585000b6106003d544aa065105071800b4001032b850040250045039910000300c4000c1d000540741c240c01001c140041c03400b0081c00e40c01400a5406511109065204a00c28206c071240507000b000c0314100e01014440042d03000b004400a03141d271040042000c00328460112000d210400c0c0245c08941400c04c00400d0003010751010040e00d0140c00121619501d54141d10a2180f0030722000b4a0210f00300300b085031051143c459499061414500072402c490f203100d6215400c4001c0c0815100000210010403080d2024402c3d014402c444070 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 537430071 1250 537428821 537428839
    0x303030a1b0918051e1f05120a0807061113050a0501050a0f0f0e030709050105030d050f07060f020412140d08060102071a04080303010e07090b0310061b05030307050702010e 76
    0xf80c410606900c200741110103942c0ca803800710704041c0c014045140d503202060072603c00ca2800c01c0002c001918a09101c0d031310000903050100d030700d06180007680030301c0e51014010104040316540c0ca81441d80400000c1ea0301541da41145250041070800501301d40d03098551030403000b4100810072010b0060b5500aa050207010492403420a82203040e05022000781d04000c441c1d042400c40945070000b45038450745d4940100354020ada01042c40d441503041c0c42d010380444035440d00020301a2100d200d4080042c408600a000c072a0001b07080ea0098015030a9044016040030354507803c0d441c0f040d00710441225101120421607001c20303010028a000c0d520b0300d280000079428204d0010b903e0300e903140160400c84d41c140d41403c445404090884008081c0c1904413581d80d83c0da100031020204050741c107000003542c0c428001485075003203401d0740d01600d9642c0b0a447c40034908001581c0101c0911141102440008404c40204800b4401b031449a8555220f00c0d5880303401344001003d03000d1a58003940701d00000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 537431321 1250 537430071 537430079
    0xe01030c0f2106020702040609022a0d08160e0d0b090607080408190509060705010c120e0607051602031609060909050606040b0303451005180303030a1b09 68
    0x8410782e82540360404401643c4054a002150241c075058001e801098000110801034900304d901222210301080310860020444440352a100c1d880c0560100000b042e603030104a0803003451580d0340311550709003407004c451425000821a80700300101c0c1a214010003804005404d0400c1c00016400080c601c0c108105182503504c13140140259261612a001182030100c20716006000f255101d4400034409903c0e141d9500d4428040c08814034001d0006401351601d10304003002d80107041c05c0200001c05000303555294041220f45030440381d59110005503401c020030268406101c035840d180310038842c00d0103031400c03c12480c081d18010790044409520704402c1202241c1c02050040d0040001c48002c18000b01c1c3c100000c1c42c500030700407401e42c1c3c50070701c15000300c124014000d8000c5031120000b208169a01401035110181995203030a601312075146820700c0550311030070040580707900342da0180c1c21800c20707140803074916002154605040341e43c0e4440740f01041280e54078101c082c0b13003d28001500d070b410 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 537432571 1250 537431321 537431369
    0x3022406010f080a02070804120c0509040c0e06061902010c110a11040b06070210030209030c0a0e0f10090c03022a0318130203041101091e0e100e01030c0f 68
    0x58640c0181000807460200708442c1341d58044901e0b43c0d41144074152100c0d1240c01c41186050500d400b1a01d825003c0000510390401e000b003648925080814400c00301e02e40f40c02c40b849000b0041c003c07a8805000c002c1e44645083d0601c0036041e0b85000d070700016422501e0354000d0300c0f0070f800356000c00c01075120603140000034031840b80c5003401410588010501c0c52001010130f24a0041500080d40300181c94400c200b5181d060f030180c00511811012128920402d01c140007031000103014017070054002200050300345041c1150903030851006100c1d10704103039551001c5030846248040c0f2400291f000105d042003052580101144083c043c2c032601c042030500b02c041540ca2280c986181c84203c0c1c8450040500d964000102c0a030000010782550389241900d8001848110001158080f4603120004039a00c03032840159021401c80c2d5020a03415418140744415810001b0040a0300081200300030600707051102d640350095204205030f250045c2408140c511003019900440c003219a554030a44103c00 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 537433821 1250 537432571 537432587
    0x90d11071505090f0a0e040605071d09040f05010f060509012c07030204032103150503100b033c0d0e12010e1e070905010503030f09120a0302240601 65
    0x280e9414800c0c0e5910f15800465207050750001c010707901041c840c000041031520206000d1081c2e109110401059448000560310a0000420140c0d5001e0f80d900b540c000d030500060762500a0b0180f01d5001e03000c9070300d41d94542540c0300580001103a81d03d40d4000c02290401055403405400c0031420100140c803601e405440805c2e0309041031450004180102c0c0505020f981200c0145420601c03e0111103904c07a4504048a5a07a601c4000039241c2025a400d00020b86030400903118002d02821880d0b4290541101804a600b0040d905010708003800c0120440030000c202c1458210580c04004049012408000c40011159140f10303003010024820442d8090a00302c0c100c0c20442d8028030781e2181080142c0180b090b49030b10700103403140221302d0015142018100c0442c449803001c80c4e04d0740342c55005071401c0c0e46083c455141c25a206021400d450343c000d8014055451000c3d003e501f00034108204545051680b00c0b0640c0941c00a012002503080500480c0e5004241300068440600704900020410300b = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 537435071 1250 537433821 537433859
    0x914062b02041517150d050d02011e090b06060912070311012c1c050d0c1407080a0213110f09190e06091807061205010501020a02090a1104050405090d1107 68
    0xd004403a0400b6240e45046e00d1160168100007100c04d08042c62001034000c00c0e400341d4085103071070851101024110705008030842d03641e11280d10f18042d100c6206024003030300080500c5511940102c02840c9100040120200450054800e110300c10032040c00944a1076200d0b2484a4440d0f1001c3e03826155484c0312929842c104d804da40140344200303403003d18803040747c1040d8028400d0248400c0c0b50f401687c82410f070641c95000d8140207910342c4401115a55529080c400d0811541050403100c1c05880c0c402c0804030501c03002c0001040400c084002c01041d588040f50140442c50702241c01401401c00d46c1c100290701005980241e1854104541030190b400d005290b6441840c00c1c4001800c0300203c0049400b150348140100c520003034560b1005003425882451800e44180382000009440d8130001e034441c4101d4010700100015119000c0f44005080e200c04442c0542c28208400583c0e504d4902c91244240512405480500c40701c56004203102034285401495520119080c403c40d07000c82c0f90800c0c41 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 537436321 1250 537435071 537435091
    0xf0c120c260c16120e0306100608130609030903170f07060b0a1535180718060302031c020d05090a170d020d0914062b02041517 56
    0xe0742d100745035444584103001500000036264000c2004000c00f0301c90300b200c1010035850700c5a84084890901d503841004803420314a00148520407c29180201c081d10f4009200807950100c0c0700031038070381e0b00694800e41802c50006140b11010002d00141c40d41c05115940044445480e045904c0c00102da540a90b02002d09a107694101c4a010ba50711564010014a5800c2105400020b2110064800414107400442c90f000000000d54040303a1712200001c00c0c0e0811140443e5a1100d86c80e00d0400442480201c6841c890070030b02084203105034a400c054002c01c0c00c8041030f82070075031040c10f09100e401e401d001c03030305c5e20100c00000800741c001ca11241154010f10f042a180d421440c009110f100c2160701601d208034800380c0e004600c41001c00d40f40840c040766008c580317680c114080200d41a52007032041e081a00116120000c0f2880e003e0b000340b00d141c0b07620344a01000c0c0c0d040107a500c01c99010400000700b03180c0c000303810031903445810607542c50303090241032035903903004813803804002614010514809 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 537437571 1250 537436321 537436397
    0x3050f0f011b140d0e03310303052a010501180203071220120901051008060606181903020a050f090a0c030608030a0905010e060702061803010f0c120c 66
    0x242071034401d0f100000c0c1360800500099400107003070b5449901100480e038a441032000c031045691020070030051000418100c84041600d503490884281d08241e141c0301c47e906d650100074250442a642e140c801c3c1001c40d0000a265151450070018a000b5100e01c000d100e0040c020088000c0c2c10407041208104001404200d85042c0d0300c55000b0781240c83d40848030380c070000c2502c00320b0102a06805100301ca40c00003c1041d6210800f0722040303243c1070f01c18484035030b01180004126003004c0000d420b901e009088265001d000c1c0900155070040c80e06c6010341030054454040040d843d120043c02d0040c5402c0d0ac0d00d520091801001c0b843c6600021b100f2001d00751988047c0100a219034480e00013410b51a00b580c0d15110b5501d001094034030320b44a49400555a07100100072441d010080710b031034903402843c00d407030b0110f0041d1171030f20822040c1d042030740355686030716210b0110614065550051005c0c0c3e41c114507020201003e41c211a407004601c001c00103506804e03040000c0310076800030880c000000000c2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 537438821 1250 537437571 537437597
    0x409031d0102010e030a02030304020a17030d09050307020406031401053303030f121902040b091215130303270b0408090a090f1d1903051303050f0f011b 67
    0x40501120316004140b4800006d07a8001c990b030210146008500c00c95410b103407160381c1c02e49520f400205001481150f08200b2241030180055485040018800c00c1542d0408016800003030071686264010b6a805900360f07014040e001c400c0c0b280300c0e40100c0440f5a503000050811120010b43e0304403580e0f500d0040c0001150005030340c02c1040e01c400182c0f035408140d480380d01e800200036041d03007038a072322410658403105140203801c68000c1e6001d03030b400801da441c01c025281c4100500d812545d907110815018a9104011400d19130110394401d41d49100420711a0075a898010220340420b000c0e0a0a4208680342c040b82c403100400d000d102581016020b4007507250b5003040340c1107104440010344d004070313161800903600429800c40c808980c5180820002c100740d042c04c0e19010344030b05d81013809035004510943c481901000d81850102c1c06440e1003401c0c840810389140680e0f1043c0c000b600c1590110442c1c240d00d40040050340300e1f01000748003d0060051806c101034820b1880c0008500380202c94281c3d171 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 537440071 1250 537438821 537438823
    0x170c030a05060612030c0601092a020307111309081b0604020d1713031a0105030a0201120c110a0c03020a060f0519121503060b01030204051503060d0c1d01050409031d0102 75
    0x9000e40c08520243d1f1361659480b15004000c09580504e06000c0221943e080ca100034541400b490a202c0c640145281894540c1e6450655082e40080f0341d0012a840070446088018842daa5400d48140070141c1e5401c00c031205a003140764840140d0a581d4004000c100058440e06955141290321030000c0301000700324940c0702801c0c003810414510044418000005100c0c4500452607403441c007115100f1184d88030310505445908400000c3d02040c506104803d1012081d40701c50528402d03031400a43c0529491085400c003c039111003900d04424095080c007d6180050940e002003842c2e04100c01c14480d080740103412070141ea0900a240c0210411214101d40200f50080c4482e64085040001401c1d01d0300c0c211a400e01c0d40001e0b0390881c40c0800003000355019200316001d94000030000c4d58013440d47d4290658a42c4018030498001c0c03020007407500000e80811039103010f400501c0d803821019078800b1403203030745190581c0700510540c10881d0385004244c10941003859490006000103055806200517 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 537441321 1250 537440071 537440077
    0x503010b0609060c03091801030204051e041104060504020d02031e220c1502030307110102030c2205120604050105070c0b060d0f0b090c01140a02070e100f170c030a0506061203 77
    0x4640140a4030150501f50701c2034111141a40d1080301d007080540c5608140000c8040c40001e030900c0781402c0d50100d000700301c3c14019414417000c02440810007035252000f00c2d0036a003204071b1a600380c1d40c0200501c4089001e01c60309001078600341e44801d000b8070385400c0071306c3c0407841c2c00001e045003040040c1060501c0300c2d00c4c0301039020301203400041620203c1801c0c0290340e40d008542d80400202c0780c82017000f00c070006000b228000c3c2d040310f00e102c2c180100171024280e45074280c030300c10701b10300320a5000040c035440e041c0c4652210390024010f8200c600e0300341030050949074001c0001d03040001d00d000120008a00580c05d1f50040340690b40344210303188624108030100183d40010b8081400201002149400051942e4030b1110a03038031000147c0d602030144c203860041d00d06c28405604120002c1c0800c00d0450b0002e40d10824060b1b00c0410242d45450403042da096075000342100c40c104c2c02042c0304a0900f00114401100258000e00d0102c4054036040d483e641d002c1c00d85031065840c5110f001c1080c0703003042a = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 537442571 1250 537441321 537441337
    0x30309060d09201002010603030207090c021603060c0f030c05030414150f0604180b0a111b011b0e0904080913022802060103110f12060702070306060503010b0609060c03 74
    0xd00c0640001c1c801140040d007210030f10443c0b145801d803100b01c035260f20600075001142c1e0326400a00072942000080005028400386500c2184202052040d500c0719030a0050b0003540258800900328034050310080c4050180165141814188061b951010b039000e82125881900102003612108911515905048a05d655907010b0202c101c02d0120464242d082240030752800c031002c1003400080304040c04900000c03940500300084840000303044003010b0b00000c0b424940030f071aa52911000318203810152540700b1814500781e6481c0410b00c5054400030b002090005039045c101400e01201c00010301e080700042008105110102d002502503c3d284001e1f604868034103000e54603888103c0b9410b0380c64111401000041082940c802101400420103906a9070030520169107038102009001d0700741320202c820754209404c0321809400c2401400060700411407035029017003051550a1648c00d541c49904018400c3c4d14020003458544e40c0c04040710340c010015a01e03070361150b0f2030754065805c40c0030f4581 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 537443821 1250 537442571 537442583
    0x720100206190230010e060d0f150b03030d050a050c1603030911061209190c030b060f0d26040f050d0f140f011401140904050f0118110609030309060d09 67
    0x1040c00b035200034400880d043c0c131442134107004a5a1950208805031142d10005001d480911074640c000c1108003170030700f8112084ae0300c0828903c1140010074515401700d0b5002032940c0d1380d0014811811158001c46070856841c210a9041c081c05000d005c9107000c1e0340e0002014140d40c1d0a45208024602103070f03501201c0d0052074251144c003014031221850900b1034210410b0700402d024114a0301000080d80702c256003200039009101d04564445001c0d4102809881d40b040f510741030b1920320740c2d03041420010325216107040021441444441c1c1c0158180010307400403c2400e1104bc440300c03110000c6401100e40803115911800301a0a15420051100303030b0181191482d841c3c0e24031145070000e0514142c08029000300300280c0310a003004d04a6400780a100d01843d46c45071924520f2038010320340b580280c0640e054a03204080710442500b103c901d04200080231700c1400045061106408070103040c500e003603031404d1904032100300003500c9105d03a00700d00d445a030000c03c0794504007845a1041c3e401c164425 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 537445071 1250 537443821 537443887
    0x606190e0310060317210910020304080a110601081c0e06120609010e090309040903180f060f020a080412051015050f03010b03070504020903010207201002061902 71
    0x1100850140125000a0b907180c0110805c3c6545022980d0844400d06003440e10203c45405031056032058001c05464010b141c46611400e80103044c640c07006500840c41030701b94950f5280405c03400340c1569200b21002e20b85400c51001080040004260140111640c0105860b00b1002900035540380c0b4500c110300d90400d0000c00e11380085079020500b01c3c025201102c1d60002a0707a00c00300f003200030070f00700d07001070300ca400510510030315041a8001d030300e038a8480c0c1064440c514054070902c0035540c0030740c400d1180b8200200b04019843c0c120101c1c1941100501c080c02482c210f548a4001a108921400424501d890318550600c1014400301c585c030202d0000c00c0c000310401b0701541040191034010309210345a624807070041d0f460144511000d00350054082c101e60361034502000003d4005080300c68145d5000c00c40c00f00004d0706c40741c208c082440702c3e031502e9103842c44020610202c0c0441c10495010340d400b20301400119030712042e10340b0031031180b6900581c1c2c0e043c030b28002400c3d07010b5400d240741c00700d9021 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 537446321 1250 537445071 537445093
    0x631060204031704060504051c0f060c0813080723070e09060105040b100e1512150603041e0c0306111c0612020915120f0609060606190e03 61
    0x203400400499000d441007a2030b858240d0035603140383c803071841070340c000c04c0c400c00003013280d4246070b20080422440c80008100070304041c0c8400703075204401c0e8010ac520960f5900c001c1c107100d8100b505250043c282d0100c14a0001c1242c1d1442c03194460000050401c070000d00018010042d05140d080200c01a1070941e07000a545035130b4002400d03800d40f0403110364090b2000105060809114824080100a0403440401c54400c41500c1e071400413070b0403e812180e90001c07141155a00f00062600c02c40c080700300d1130145020203000305841034403900d15200c1d4074100700388008a503500117401d88004894030200140d082d680f030031407221841a400100214280500e85203000d8901c00500001845594032203900380d600d4800108548a40c000c00000440c00e0b050300025050054260ba84110a00c181d41c0482c90304200084a0354000c5e1000e0301103500c0b4001c4410f00b11f90a2040540000e801d00003002507051150000b541d0b402080e880000c01383d03140d000104d1207442150000300c03108016095800c54104 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 537447571 1250 537446321 537446333
    0x209030124080708120301140a05102f0c060318061302121c050c0312130c2102060705010209040c11070f1208070507080102130f0b0c0631 61
    0x2a200340c00b40c03400340d4034000440e00d50118400729042e54603000b680c0b550382000e580380c40e09105c580000750406048031021507552101000849a142c40741c43c1d0050306080340c05a40f141c555400d400c04440d901c0540170300510b080010703907803102c840102c0e0030359141d40d1908529002c00300f101501c60342034440d4200344480e07058807071803400c450303030094403840960200f5110b010307510f50800d441d80c0c0d90300c1212551b0714500d42c820701c06042560500000daa19203c842d8920b00301d4224103036903003041c052000d20070504000e0140d100310001c001c281d40100c00b0000e54002d800441440501c003034001c890008030441000001c4d411200e1481008008200000303a80400410900d000e070400016840f946401140b0265164010b0b421641e401d502d9010310201e0f55140b94950b00048812119880307842c02c04541d00c2028000b512019071114284070754545000414600307d0000da0216024117420000120000d0010800d160700c00d40c000510300440100f0086007450071122a0081040d92441c0c3c041d80422407 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 537448821 1250 537447571 537447641
    0x12060e1008010213050f121209031915020f04120309050415030b04120c0c090b18130f080c030a0c060c02011b11100515010206090102090d0602090301 66
    0x1030500050000c55844040340e40c200d03c500c00c00076055014442d010840c0d894240014064190040d184c1c903c8210154510340ca0941481e8440e5126034000ca0003054070b08040041503c203034200089640030030069110315421007904881040d03001d4001641040e00400038045500904000300d09002d03012044c14014128030f981d0007010721581c02d150711150940405891502641c1e0001c0c0400d090741c545694403070b2181c6070800c00c0d1050114210110f0085424504080010800214082a8186400e081000303140c07494145111007a01e504c02d0001c5111948080703030303200307500190042072104503003440c604600a0414000c400d200000d14070384101e91040054003964800d0f9003d000c45004400e06a00745c4071a050001c86242c41521403803a020f1113818410031030040070043e5001c00711491005400d03a0700031079200d0702c000c0e50815001e4055032304105003644807149000071824180082c0002c4e58440c03107510081d14a98001c512110340e66400c0d440f215015040114040032400502c00d80b03c20303d4 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 537450071 1250 537448821 537448831
    0xa03030210050c03090709022109150a0c05120604150b040e060607050d200610171f0209041b03050906180c100c0b0403020303240607080a12060e 64
    0xb4201400f10745a801908280c901603001ca00203090114100b140000094100030340e4115404021080c000d42c800800400310f000e4140d182c050302c41080e05e10030103800600f0140407007150390726140c0550945a84601540c001500700490107a07240ca030300b8006000360141a400300303442d91601030001401801d01d401403045500c0c80700c200e102c0e5070314802040900d0246a41c0500107401c11110399030810300c50305400108030303801d15190299030824102985060021294880044035084090007400851070740c2d40c4158092078001c4c188824040c0c83c0c845038000c0150b12018150300410006c8050740c1b0368108a020409000e0720802405400800038040c040550b05000d42c1c0c051080800e0781c054994450421600858005052a00710f060034030003643c566045d0036041100c5591100d001800f0030802e140114025801180c407410500580f00d0001c45030002c580140141c004404296140c1c401074603006a00643c00783d840b001501801e6401d950421b9070364010b18030b0290003081a0b00c00d681c134a4050 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 537451321 1250 537450071 537450103
    0x60307080106080a0605130c0306060303030b030d0f1115091023010e06040207060f0b0910033207090f0c080105011b03050d020f0d0e030301030c03120309020a030302 73
    0x119035258426400c850540c0681d041e107400582150000c00d800340c0206802803024102c11840101d20703199900c400302190400c07101c407a140c02e000c2041c0759140c0904e410b80f040403006000c051140500240c02c5040d40c1504409103d88180b107039803041c0c4107004c0d0342c01818100a850300c41d881e02c4142252540003990501001915144075204050143c0403c81d00a80300203002c59016400c00d0002186104001c01041d0b03c80d800f044200d0025405000e600a25000800301198001a55041214281c0001c0449002c0f4907244c004102080414440214210201805250500080c1000c0344820414a0a42824400d2003c00202c3d0740c1140d014070100c0c42c02601c00c001914400350100c1d0481805e10400e80060803203141c4030410340c0e590002d4030075144030f41409403510100c507c98000344d810140052901e41400b00701840c0c2c40e4030a0040f98a64803a9802551856041d552141c1d01c10215000c0505100d480090b688030180c00782c0d00201340541c004124160655036131800035500e0800109250380 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 537452571 1250 537451321 537451333
    0xd0201140c070524040b07061503080706050c0c03040b16140313060203030106081f03050619060806010b190e031207030e030a0309060e0f04060905090616020a02090c0912060603 78
    0x210b40c0280340b00700304400c20131a0300e4680707401130b1841c540c4c106910541c1d001396a06c26002c1103400c13900c00e201c029445482d0325074842d0791a0a0500403520020107280080740200721918281b0b00c00b00072a02a2076040b034070503031907000020002a8000e40001c000700301050401fa40c2050b40c40005c003401002003002c110903030359074460900300e2f1030740428481c000108540c0f0000c03543c02c000c900c4030f4280d805407490030703c040b1603540d071202c80c9404800e60305c042c000d101c2035003581d10b007001a0158001500e014002030007254940301c1030f0015403050a6400d5085208644d920600d42e03c1520303900117034400241220550a1000000c4070300d50710550088001c43c03c0d000a0918904000c203100035501e405885e8410540c0c6064400e58080601e500001da01141c10354600761103940da4401e00b00500941a0005402e140c10328400786480740241c03042103020040450b0140301507000a03030000e0716034103850524850306d0303900703607240140600410380d9840b14002c0e88020a188000a03101c1c4242001c4046402c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 537453821 1250 537452571 537452599
    0x20904020a17101a0702041b0306050307120b1305070e09061512100e12071202010c021618110703021c0c05070b0a0c02030a030206010f0b180d0201140c0705 69
    0x24201181c89044008000c0d50b42440c26404100c016207174240c00600b0109a0311503d05040064004062a00011958604040c8207500b010080c10014007403540040c5000360726501c6550011000910002140f07916a13040d000708401401840005d0071f040385516001d04009418903180c2c4022120004c0002070064440c80c1031425003d2200b40305400310141c0b6140c0b25005100e4080d040000c0c1081d19807103052104149615118001c110b602d0050000b806200c2d100746000b800e58000155440455100c0c410700d032420301021a0010031102180c0428a20800740307041c84002e084c4103c000e5010480c08a2180c041c5070300071500c540800d0700b68800004c1410600c805840c660300c0d000002e0440c0d070181e00c080c860f2106060003482904028200507400400c2d07540001d190130021402140181c000c1001040314610683e8143e010340309000d101820509089644180d10f1008086140b107800c02014010030369003d03040140b051060b030628159a84c0c030303100942e40e491945209040c05002c145244138 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 537455071 1250 537453821 537453841
    0x7060b0d0816050123041401020306060409180b0c1201060219060b0414040c06020d02061e07180b04061106060303190203040e0106081f0f18020904020a17 68
    0x545558801c08207418003401e04900100301803200800c880e15035883d0141040344142da40c22901382c0c0b24240015a240c0742074030305100d12851250380c01c0881c0c0c1c01031007800303d2591ba00054400783c460302c400c005a0400561020303a0325200015001d0040080c210500c0a004060b90040008801d82012052070381d07a1350320100e0b40d86c00316020038174110100050040005900d034002003c2c0c0311000b031000c1a0f402d003030020b544480c030301994129915040998100080c1780c040c041504020f9160010b000340e4600825241d2850070500c030542800342d505000030f24014026002c0c5101e0039a4224039544035a243d020100071940306014407008150303166480240c20100144292040e400034000d9801c110b0b64031038646100c4030001d2031005601080c4004545103601c1943c0500030543d86d90356a09030f04288040d109100342c020601070003503032003038428010b1000c0c04111b503048905204900c2004158810020001e000c0e05c2ea40c0380d07005000003501c0849561080604980010400c401211919100b4a171 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 537456321 1250 537455071 537455089
    0x60b0f030606040f02040503070b1c05010503070501050d18060e0c0609061207140a05041d07020607211103010501020c06071e030e0405040506040b010b0c03030c0a0905120307060b 79
    0x80d0305030720010000c0d01608158120404080103868003508158407100028141540c0d500402c000c070b00d0208919400d2040d644654580c00100882001a0b504010119441d6001d82c000c0a040c0b2000042040f002c2c402c80d4008d048035544887c0441e0a8180e42c0341040103414441d240b0b9046104183c49a105850004101c0320341d62030042c2100d103000041c01c03e804d071102005002d4418045c403100030044411001c801070201c041c0a540301035a8a00303100c103e4200110303003144451401098010803601d85d800044640d001107c3e41049001c060100c083da01041d2035a2005640d06403c0c4484900240c58010185050301d00c00d80a642d0113034420018040036000b500f002130b1018096124014a02d014002c0110000e4000e203440242602c400e004078050350402c0e03904444941c0042e040006010501e00d506003d44810b083d89864080c01c134003403560300d000150900004d1400014941401401851141d004080141200116030002d0400039140e4000c0e0700240c600a0030401d4040481c40d1800740 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 537457571 1250 537456321 537456349
    0xd0b0a0c1b120201020f0a110114060607020405270709050a020708070b090a06050906090c0f060d0e0304030b01030c090c0f09090b150f07200307030308040303090618060b 75
    0x1140702440c0d00e80324902d81d4802c6800900540d507003002101d190340085402800071030941d8403aa9214240c8540075821145030300203541c40f410b02c40052105690303491040b250020f804032001306480d2a079401550100c00301d10f6202c02c603507004100c1800700000c00b090500031586c540d030040290366281d01d1140142e10942c0002060400204010000030f41319840643d0801c92030b0b001c4482d0201d8aa4481044840076501948194807640400206440412240703003400703020b58001c2c09080060001c50014003501076800307145503e445521200071810003d4800441d04008000c00e5035030340b8280180085c0c0280100c401e1141081d20024905016450504240c150340e600c070746001e80782140340c20081160240349503201c000c03880c032000340748142070192003111104100f0583c0d82174140707002981c403090a05104004405c4402c40000c0e0390780840c10740c04490b018103141ca150703a22460210300500c950784000f030421b842c081c8028031041c004412001024450b0004101c2003110303074200540c0601d9041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 537458821 1250 537457571 537457607
    0x60306060901030807051507270f051318030c0c080303090604150b1315090506101413080d0e090906061203040513150e04200f0d0b0a0c 60
    0x1c0100002801310700103204030b0b40501c003911412141c1c1c0d0703020b105070241640c52070002400b4144250340300500002904c00000c040024041c100d2074003825106040d4944140f5204d4240c0c03404004038003110303803c0b00708009071400710450402514034001d040c03c1c4d00940700343c54400c0c5110307012074a00c400100f102e0190000000500865a561b0703500380400e850161003100d016144c4500000d5a1118404000007030880c1901003000f60700010b901451051580c0002d0081e03050009008072034590310304c00c2c2a100c10a2510310342c131442080c4e103510301d881851081c0c8405016024001600c0c0c01c041040380d14400203598410700c2c41414010410317a99801e81c0d09a41c16080359012407d1841c101c9030308961082444152070030250ba500005000c4000b11000345001a1201000d8644140075141c0381d01919032200d82d00c5650401d9210b88000c2106102003824801440c5000941503940c111071442200004188540100e018506500602d0080d22501021401c2001c8180154096103a40480900c615 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 537460071 1250 537458821 537458839
    0x1d0a030812090c011b0f0c0e04200f370b13090c0509011d1003150b0703021917070305070201030c050a1704060213081b0f0906061323010806030606 65
    0x5107910300082034000d000c0302d00b1519000c0015209209501c9548918040d1a2b1a251884207a00d0000c007501038800031071107070b5444004015181e4500b451010303828040e08410020407114505a4010314518090002c00550742d400041d140102e88000c1c44603040e1034a0f0200c486944100c50000c2e29902c5a0a8005ca00f013032140f200075521071070400e6001000c604141c14003200440118843d000c81c1190b05000a8031407441d20300c80b25010102c40001c1009010442c03401040352802905c4103801c0d00f441491464034507198052003844000440210b10360310006540307851518000d009a8080f070030490110f4240b03161400c842d8029415901021410b460b80c151b000301048031100080002001154030319420710600c4005040d80f041d50001d010010300800d1a03105c20024003000810401aa510981c510701c3d607480702e5180d1000a64000c0000e492041d2584070403844038201480070740210301d03191845a0031404880300b003043c403010b6241c203807a400810b4441a061584404089500035000103c0c0 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 537461321 1250 537460071 537460073
    0x3210306050109051207090c03090615080706080a0b04110c15010e07050a110307060b01020f030c0d080402030c0d0c061706090106081e10060807030c1d0a030812090c011b 75
    0x141041c0070002c0c401d8800d60316041c7d1110303001c800f111014141407001a5440c1446810482a44201c03281c4010308620085514908010281d941405010381c074100240704000c25400f6609812401103120000c005004110b01c080810740c03207411103002549580702c0c0740b070205240da40703090099060740e04012103080c07250390b4540241e60f26409005d9030410090094411030150500340301400070b26200784000b1440d04001c400084c41d04002e4075641c4203942081000290785880011040302064803800c095110740c0d1280000303400c1104c5840865007003070b07101002c03004102941201707006070382d01511000000c0b221000c40700f144007000c40310f1903084582200140409400340018680c00f000b1964042c030300481341c018014002405455800d08442854010f00c100760700109810391100051900704030304c4038160b400070b1141802c52a05030026039030700406009074407465041e0000c0c40d001001c030740d983d00d0030b10054591700a0440313031a03409002d011620007107503100d002c41080cac1804107805070010800c0307 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 537462571 1250 537461321 537461329
    0x512060607030e010324030602040e011a0a1d040c080a0c0504060503010504180210020d260f040201051306120605010f050a05090f100c020307061e0c17040321030605010905 76
    0x240f46504282141b03040c06c4200265049030a040140d4411040983c59504c1d082d02c0300c0704410183c02034001c4c54968079143d4101900d83c0300f030303803c00746891074032400c100d04211762000380144a84000d80c000381082d4684500c1a0010341c098043d88100d14100b1402029100484150056020fa0000104100010021480c00d0b400074411000f4010b031500a130802030b4002110441882198005070b00610003d1144a4200000d00c1030403d0b9038207012401d1081210740d041003500108841c01428415020405691141023a00d0a00040c00503449030070b511050f0162000c800386070760503681c0d0300f44a000300d501d52094043c03450020750747d2138003801c0560001082c2c42540080280e41d13040958400f42586603a40d8001400e034070245503c42041900e054014542025a0b0360403050600c10f40d5010006214a42134880c0c40d464a40d181c00c83d60028246880d00480081d031507030981600d004500802400300700100401c44450b0a003011344800c40095055058be16140703d814080340120104000c00d0070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 537463821 1250 537462571 537462581
    0x8071b140a090b060408071229060112150f050f15032707090b180c1c0e0f0f0d090f140d0203010603060b0a0b190c0507150512060607030e0103 63
    0x43c005080505181e00c80c100986030101e0303503215908000d91402e4590501184040412110540982d2441079a15402d22815680304c0a04040d0401c0341a24021503d805694000b00d081c45060898844c11692412400ca10802c0350207014405d050403000f17841c9600c0c248540f502e10044405005056903680c09140fa10030303e507804019520030b42c400c2105800882407094802600e0401f0001907401444010701c60b035814001c010b162586060130a001d42c1000880980e200c221010700d41c81000004c603a4510701400101f041643c0078803c1030308803081d014020031400801104070040b036105a10060040b548801307584114451014001024044c8400c030034540300c4c14400c05040c0581d02920b550200f030031945181c2c07003501c26690784c2c0540c00310b07132074251044002002850328850902d03004038140000510034013002400d00c803501c00b01c01c0400c42c040c0940b200605e141d9501042400758844080c04a41c07091040314041400800011703020301e44001580c234295015035400a01140002c0154014a = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 537465071 1250 537463821 537463841
    0x60f090f04030f090e0f070311070222200309010b010503360d09060306050d080318011107030e090a09110d030203040906080106090f18150908071b140a09 68
    0xd82030001090700e1005c8900345000c4c01c21506851390501e0201001000c480215102c02d503100c0741048018056641c14200c2100803031140c4414403440102030321100105023040c50124044a04c0340220708140b03806000d14854510a0024001590b01100454082c8000c03201518510218404403508618030003000714601c144014040c03100c9204c3c0100c80c50615028464400900a40300030f10000b9410300031640200002e841007a0544403035503990b0b2480c04000d00101074521400442e08160700250410103a440e00307552125a550500d040040080101c0340301c89001c1d241c1c100200703070000076074843e0b1440e080e00000d280c2e9004440ca0100441c08580c00c1080e000c40c4418000865007114501c1900014001400001007441c40c0020940643d1050603200100c20b01e021844001c45001044242c0c0150b0f1018920b4414842440c00c007008001088024104980118010041040c00c400399003c0703103a02014502c03065032310000501d80300d0200400c550071035a640c0c0200f0000b1200d070003960600b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 537466321 1250 537465071 537465077
    0x2403161d0f0f0c13080c0f0103050919062a031103010302060901210e0a0302100501050616080f0d0207060f20160203160f06022a0102160e060f090f04030f 68
    0x1107078600c4d800c112000f102c0d0f04645070940003004d0007003042c40c2180c0d040811400c203007010300440c64411822511061510400710299800d501c5007001c100481d80030180180c0e40c010b00c40c10807101c035203c00c40340d007450b00740302d50110340752030100c69510352000d09883c102d9600601b414507120088004443d000c100c116012100072109056420061150041c0e00107400c1e440002c120045e140c1c10024900032488482d5035001d468280184441d0302c900d41201c040c121182581c3c0900f43d1303a0b00c1c0c042894481d50300c406049201c0031800c0048005030741c004220b86030107220140480d90507254a04201c9030f1901510700c118505044440d030801d1311401400341c00184483c076181030781c01c43d0046030078000c1c440800d1411000000060080d9010b420305080903120510040541400e61008501c9000042c0c0480306101c600031500e05140e80300700720b03034030207150440408501c3c02da5840e48248101800c1d203c0d01d201c1e0103241104036107410090110b510542c210040000b00742c441e910166040c034a61410b007420 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 537467571 1250 537466321 537466327
    0xa020105180901080f0c060c0a111f030209100e09040213060306050103050f0613080a05033c010b070f0206030417030f040b130305032403161d0f0f0c 66
    0x90707a0349081c2c141c0c0c000c0400340301401000c0c1004100500700242c1c0a0001c0c0f2800c003d20520950100000329241055846000755100c5000180000e241401000a005a2110f2000ba08903e250b140d005003803161420b58508401c00c1d0840740a03240d018102d10815013010400c40010054074140d880c6407070b0300801c0c0390000380590f101e0311404c09a980981050341c01d03070303c001c100510000e0b0405c5030b203030301100a07051200c050059654540140c410051b03030004001c1c021010402c01030f02c22280203030300c40d10948a20304c0e41915083d40c14580035611081140c0d42114000003030441d1484044500b8182d102046c4650444540d007001190382002c0c2042d14100c1101d00c00d40a01c0c0c04580056000c2c01103900c2c03d4060303151038502170398251001041401070f4010020650b000a4008003681e0308064610351403a0258141e0064400540418440175850307c903401075500d80e445110700080c00e4a5100e020304000d40010b03005122030f040c041e19903501080c54200000c40103180440040d41095101c070311285 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 537468821 1250 537467571 537467617
    0x305060111030406030506120f0706030b1f0c03030c05030c0714150f18030403110607030c0203160906050405010f171002040b090f0405041509030203040302040507020f1b030a020105 80
    0x120b15000b68110202107035032181800b0030707481c4c0050440040303031921004040505072004481e88a03082c2d071003024149074550500d20130f6580d9151000d00d1146040d00428003000000c0c0e0000c0000484c0d1009502180c64400919000381c460070450784921000c41c9520b20b408405d43c4c03201143c0380c07031003200001d9001e060014501c068171024001e02890000604000310b04000481d28040003402c2401e02141d0701c108002c0002620407290302000c0281240d4954a079122410180c07004444e02c10002e506024030100491f0a8046c5051001901c0b80d9880410507240c444007404102c510038051039001c0a00c41100b08034903003001c5402d00e02500c0c2002644c0c11801d50302504420782c1c000c1d070490f480843c004a0010401d04011803200700f0510122000c2c449820a6114008003c80704110124840d03100c510800905000700115030046901400410540c40c0c8940c00a4039546002102c0d03496025050001407142c81c0c0d200301112400b0000c01400c81c064159006640c503500050985250b40309a0410036 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 537470071 1250 537468821 537468823
    0x7180e0d0f020d02060f06011d150a030617060615040b0408010b10021605060c120d020304060c050f190912030201050402040513110f030307050a0507081e06070305060111 75
    0x3840152a516803464158607050064104003d20074003c085600c01c904200b0f400300d0401e00690080001c0c20100c03419602c1c4803424501003510031500f80c2140801c08130b00200482040200035490107035404100d281e80b510065541220300046c404c0b2282d1001000c2003144c90001118245d044158103030783e10b8140c0e1039441c403615400a42c00521180d55a440459041c1007070401213031145038510151000310070110728420f4a0010f401000d00820010540308402c07401002130249914851030f502d911149409407410280d44200c8040307030700c1410041240c02d00c900a0f400d45103001c5180682906100f0343c403403490a030300d0300d59000390308011160340c0c0002c403000480b051f818010301950001c215032406005003c1903680240c1251040c412181441020a072005104621140304803101c0304003040110010385540184030303002d8118050900d100041000c0081e5110448440409640c3c103400c000700030340c07003d2404450442441d0411307000030303054502c2907000552114050602e0100c41d00300c4080311b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 537471321 1250 537470071 537470083
    0x50709080a030c12050f1b031608190905031005060118030b04030f1b06051302040e0601030b0c270307030c150201060b2115130c0806030a0507180e 65
    0xc2d00854000f00da0741051103404208403482c2907050400e10b10705105454002010300c511649285c40d03210b041c00740700c40400c050080380c292003806c151038165500c441c2032500040c3c1c0003012041031248514513001c041c074028106007045840c001d000d03150322000800c084010780402040701e410010812600142d456004c51610b003c1c0d070142c1d05c440c0319450301e89406440310702042c00d0319090101d880c0e00d40c5080344548180d12115a0b0010002c10540c0b201400c40c414810400d40082d4024102510304101a000140340c6048900400c0c004ca25525080340c503000c00d00c51924802800244040c01045588210701417400d4000301030100c0303003401e5681d02d54078010364103500303d0000003840c030601e90b015650901850001e1700816080502e0b02e040c1e082801c210b55000f510130141e5054020002e00005215400c2c90443c1e08040c01c20013a4030405000381c0001c013140310600000c10798450110700142800503044900c598440028440c0a0811040350840416401210307038240c0c5541c0010f41014042c001f03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 537472571 1250 537471321 537471323
    0x18180c0327061303120b0a1502160303020d02070902030705040308091309060c0f0513090e0f01060b121305060a023004020906030307080f090f041a010813030210050709080a 76
    0x24505030f0400c0e03240040c2a916090050181c0a05080e00d5a40e660b6031040c6400807112030010404088000807004c0c0e08181451901c0441302e141da503c00414035401291010380d100399076003620b50341500c6480d020708900003a01c81c1030008005100610018116030006c20034440010b04d02d502c00c3c100204c10500780c13401404100d030b0090325040d018a0450b042141d00326101018141035091100182030140d0b031181302d10030300f4040c130303100c120011842c03a00b0b00c5078140c0199054024000035455012104065004601030010300745010001003003894010301c61007810354020080c0c040342d11080b1540010390481c0380c5460721040c080c1004103450901d00000c055807000c40f1a0b105203032401e80108003204074014070301c034040d8101304118000940640101c03840f0b100203c110503240d180450105500380b01480c80d140c1c00c10300d80915400155401ca0a04800910036681c0c0d081c43c1c0d40742c10903014000d02964000380942d214001c140792402d00d580049611182504d041c008056170788a205143c500701042c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 537473821 1250 537472571 537472591
    0x40519061401080604020304061104060f0219030e090901110705060412020a2a030f05010f05070f0903061e050c070516060e0d1718180c032706 63
    0x120001140506020300e80080611040e61001d8907094070010f0201000141a507210320741c000005003c220942d4000d0054001c220b51031078940fa1180000b808175040300380000090300c20001e0506500c00030102c040b215030f91654031340281c1d650709424084a404081c205c03003803079500c40e00507004c00080d8078040d28600d806600100740306c0c28241004070711a9000c00c030304011500446018070101d00c3c0d042e060349a520803208c0f950000c4694a07a0541e40c829160070003009100300380e0030002800015000400481e2005000300b0035030300c0c3d0390340665903c9070390310241d0003180c030703060042003c00c52070740c09035071080d06060b2500245001c08010404030b0b01c0886a800001e04013041800c18408208601c4102c80202c0f0725007500d07541130400c0a040078110100072440f40c18060409810403040080701c1ca0300301c04000380142c66801c00c0e40100f62000054402a0148416100160324010700242071030243d001d80303490030b245843c0c032441c51603021203441c8a1200400725400b200351a1804000c03036403040b9000b803 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 537475071 1250 537473821 537473851
    0x5040e280b09100b1b0c130b030114060a060e0d120504060909200f0d050108013206010c17070309051f0f05030a060806010b0306010f020615130b0405 66
    0x40100700005001074400200501018000d12013141030504480c01511304c88800d107817084503014900d02e045060031209400200901c0d000c034030031000c2c0d0096048240220024080700320304008001900008070b4000c0d0740403080e0207041112902403030b9102e1000c000a41035480694882d12450030010540303c0400c0043d038001402c200c2c80b64400080d201400c60341c0c0d010301200b501c906104456103454007032401e03d5800000d100800b04400c000300c80c0c44058015051000c3e6a58036440340c028204440c4900c0311075900d001e9004540d001484046854000314031603220b54454800440d0300019075403040756405008405040c0303050408001d80304051080c0e440300350403801c08042c04000c501c540301c01c520310b0740302d02c0010b25960b4000060191a40c0340d0f1620b0740c0c4903510f00408001030704941d800311546004100010403881004001144901c1c1d0a8032051068529183d04076a01d40c0e044a54a803c444000120055442e040d0012802c031624039001050305264200040c0485400fa00e03031148128900d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 537476321 1250 537475071 537475091
    0x11010e15040302070807030c05131d07080f0115140303040506030f07020120030417041e0e0c04060f180f0602010207060b0f030c06090d08120a06080703020105040e28 73
    0x1044000e018188174000b0b0f0002901d19552820124042d00a842c420884044000a081c04a0b4002c01c81c0d80c0c448040d40c0c505008800c0044c1c1c88107031038011440d081c014249050b0b41208140a240c80841c04c05482201700e52400c040001c3c00200342e1116907050204000000d01da980d098003030340c02003a0032651020355041c965006400c44202d000c1400c4162a01050702d82661450415640d01542148550850704103401030100c60b80319039045a250b001c07000c66401d01c48901c0000080c00c0e196040b1704070300da90300c600300e406071180100d00c01c520000e9071380108254454070558041401000501c07081d001141c540d007001c8908801900310200503940422318106102c1180180d400b021800e075210010840c00302c1c0841c0e180e520702c1d114180100d80c001030269260700d0301b01800050981120700c854848281443d40031001c102962020512410070380c1c0440d84140c08075400007126416110145410301d4107007501800da0004194002d590300c1940c501d140207101000c107104020255000003001140 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 537477571 1250 537476321 537476323
    0xa0f0c0801090e06040819020106030215130b0f1c0b03010f05060f010903050601090e0f010504050607091401200c0411030126060103081315090e0105120d11010e15040302 75
    0x60841d0f0a000d5911040900000c20301d501e0032980503024140029948002454081e801f6060079030000b5007000d070031407411201444584c0034022001007545000c0c003080c0e848851002c0c074016441c0801403d5802c129044100c4000c44901d0890b0505c42e102050301054400060708442482c6040d00f16036403283c04006c46440c144506070215102400c1001055007542c80780c0b903032400140140c00240f503403500c00400e8010200503016540d1a064000c0c000d40c40c01e440d007140c95810584000c17003c50302484000c6010801038084006822040c1d6503000d00c1e4807040224880700c4400603443d03506025000b481c5c01070343c03218026030700645501407601d80e0742e5141c02c045075200180d842c035039010003002c521446604c40d4042035030350449402003a00b41d19003503a00312071841010b042d4815446002c0303411080741c00d03a030003c210300700301c82818003198070680c2c0e50001e0020341044100c0030308190700304401150aa5009034070740449210303103000001d044101d4015041c82d0801c440c0803083e00130409010001007682c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 537478821 1250 537477571 537477581
    0x402031f1505030d08010302040b01111002090108090a0b0a05040213090c03020f010f090531050a0f020708070312060b07050c2403072601090f150b0904050a0f0c080109 74
    0x400e800a01450301c01d984018059417042c0002072050383c403618200d0a503071207030a021003694440c00c03d45104540c0c840c6200001c2d405152a94003003203034000010700610001c101648000c4c0c000c10380c0580d5aa03883c1017403008081c01001240c0c000c0058809080070060307881580301192007500704045490a500411142d408010085410007600c014500c00541d44000402c0c1116810780d40c43c00c044003044c24001c10788070400d0f501442c01402da414480392501d01d4100f207008001540040085501404804044e44100b1001502c000010401800000c4c400d0000044c90114600006621a240c54242c00c1aa003e800c0c1075a140d8440361040f41140f0300700c001001c050300d68402002162107000054006030200604040030302405140c091980211581c550b001c886806041440300d60311000c10000610301000804d440034600322140803030036040c1c03c0740c4003592015441181441540d504000c040e22004240e100703010b448010642480680c0d00031107060309013a4a45406070f42c10070003441c00f214 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 537480071 1250 537478821 537478829
    0x1203020403060c03021e03160c05030904090c0f090203010e0f1503030d0b0a090c0f050a02070e1305060708060a0504020d060f120b0f1909050c13020d0c0905030c090402031f15 77
    0x11b201041401034401491601003002245410206002c06c01418411300314024203025036001800e000c092010002d03488524821340e58240403100225403074002d110308a000034086d0500890406010400b0305824104130703544041d440314000900d003080d501103425a001086d14000264541101034094035104c5140030103808200001c0041000550004003076400d200b44120520000246080c0c40c40c0c800d02401000e080341c040401041d051070f00700040625204182510b0f0360080c00c0104400034428014039010f10001442140d000f4100803c010003540a2030401116030390f10000026050501c0c0392440051005800c401002440343c24581407401c1700421000000d02120f0411100f0015000c0d8035001400c00d42001842c4002d61800c0b40c035100d510a01c86a000c44400003c40d00041c8a8005121000c1c68581c00e200816080c0702c25038280b42140a00b50340340c2c000c00c0f480f030654245a5581c0b640540003c04490005101c440824481600c8001008409440d04000032000303c41d414114010 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 537481321 1250 537480071 537480127
    0x20d03030b100c2001110106140907050309060f09010f05010b0307030605100504290304060e010b0a0b0301090903090e04050715050405010c0b0a0e0f030403140c0d1203020403060c0302 81
    0x4449956611980c00052413085401c95818003500d40103900c2440c0041052201c60020880ca41d241c60111549100084e5664030804420300040ca446e8403032025203002d0002c80006008a0315a00e80c0d44092100003442d11409640c2c0b83c90882d04080701d4000c15000740441c01d80c40d682ca0034078400050503034206030045402554241c40412240b6030141c112000c81b89449540f80c101c0f1700f91f80c840f88100702c180c14115603030340002c028401070080503404165900c803101e000f00f01c41c114950a04c0b06c1204640710365240760380b0071f2004004480d0f103504000601803003444d147c12095116201e42c200c1c100152400d80700d90303001c0141448841200140340800000d2803c000341014030b0301000800e1302911800c002c00ba00d100d0f00c003060102c5200c2c3c0081400e202828240d81029000c0b2034100d540e50003500c41035070040c02031040c00c004141c000c60146240d18018029940a45240d110003100702040208001015401c01001010544c248607048500840b581c025030768409450403031a4500042c0084000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 537482571 1250 537481321 537481337
    0x3050c060705061306020d09030f03050907050109140d0203070e0f09010213060f1107321c1b060f0201152409030c261b0d02030a020d03030b10 63
    0x40b035800207096910148140300d07411501c000b494001c0c068000c410f0781112541c246141c04c2d0403d41c1111105a190840d17a508005036540c40c40c0c440d81e00c2c2c020b48038590200b6840c1005018481e801250394405500c060814a0f034001242c0c0482e1804d0015803010511880300d000f40b0070300100009045801c405100020f500f0201c610b80e080c01c042c84903200d090248051620b03a104620302441d40f600d0311503000c0c000d40740740c199146c206100c01c40c960000c000b26154a40703d00d0141e401c00b100490f13900b410184c4008411044828001c0d450442d5400607140120704410f1140000030240b40c08018100d255590b5030200d90414000e4259410720001140003c10b50344280b01042c400c0d1110705011300c000300580c1c1000e0020310300307490510a0b42c1010701217210540e404034280c241c1d5078042d4422031070000030842c500304045481c0c0d10355510180300c88143c4800d802240061800c2e0b6080c40c0050300041c20b40c0d0b4046034544c0080c85403040c042044001c01c1e00c0e03010014413403800d0700401808400e13600344244 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 537483821 1250 537482571 537482573
    0x2010c021b3c0306010b0301260102030a230402150a0e0409110306160c0f03091706010603060b130b16050a0812010b2106011b0b0103050c0607 63
    0x5140d40000034070350411007101805050300d40c0c8445a0702908140281401c1e08030048500e510309101c080d05405802c02c2c40c00d9100c0c901801e0020303d07103040b18040310180d41141d0801c814420611044140441d0303a940c03065420072901403e10045001c1c0a007843c00003400440c42d03500d10051281c1d84940701c3c81100c2d000400c80582c81b03032520083c003024074036200c03030384c070020b000c01078640549426440f43c101c2e1070084a5400c01c44080400d0350580000c4040324003566902a400b55102d40020103c07000580e0f020555001a0a00801065141c401d0038071143d4540c039647e15019200891240074030fa80c3c0440010000c81340c0601ca03c201608100c501a07140c11200c4240300d629800070302c00e040107420001307486105c2c002c80c8801ca820095025050b1035405071a802c00202d02d0b0810003103203405010715400000c800d1003e00450302c11148070500590341e102000e401e0300b503881c030081c8820705100e004504450140c0d0b545c00007900d803d208141c0349405505606200e403406104d1802c203401880200030b090 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 537485071 1250 537483821 537483823
    0xd11180915030a0209040602190203030406060b0c0712080403120806040e0102090d02060d060b03070203070c0527100b0313060b0607020117250f0f02011407030209060f042402010c02 80
    0x401c43d98040e60030310381030380b039903c1c4c03600080c030521003441404040710302c2c0b4010b44c44e4080700542c01180105800d01c04952240f20b09026031044110404580e80200c40401005020b403001101081c000e624803800c00307a0ba42c95080c03201c0701c108034040020300044d007003103041e1809110b0103410501c182d0003141010168804100d24483d003038006031140401148249400f00c95420501c040d0402d074072416201d0400500103903490700800c0003203c1c01050840d0105043c2040c40c644040f03402d100900510365810034124030b540385006403101c01a020440340c0400d61a0641c80254052488441c2c02c0340c2c045074600b040c03021103001c0580c04d486454100048000350303a20410401c6405aa00f00700c00c425160304140c0f46426402d17107a0400d2602c400142040b02d1500030802d1145a8500c1d01e5014200000c490103e003201c107208440310242c520400403400c0700c1e1283d03014000406020700b1241c90009000d0106c0700d281c0090344460b81c800320030760b0b00030350140e0f501002840d9202d05000070f0018040c007450203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 537486321 1250 537485071 537485083
    0x605071a061e1302070501050f0906060102060601030e0c0d030e03010f021201050603190c030b0406171e03041205060717010308040e0408091903260f0d1118091503 72
    0x2148000c415042401955501c485100f600b54400b420110355402d440e1030301e240608000c0314510400c82904000664007000414120b2090030164043d2007582e40e0744006400812024141c41c51034030840d500c441c043d4450b8828400b03c1d500070344070415911410400c01d800d440b40703410062074160041c031030003084044800c07205064442c00c842d500e0701c0380c0e240205a0142141e008241265604040302c00c0c03962078040d44001c0e100d83c403d40d0240722543d2120512803044841c540811030035032000028400090034240c0f5500c4a04246040e686055030b1007003000700301040301c20160303020341120052043c0c4940020041c44a40341000c2216100e601d141c90791030075402948500b026814890780010104607540f0102d81184800514480100c908105950400c8800f07010803100d070b803d01c00500c003820100e0302c41c2c000c3d4080310702109490300100b00809031441d04158541656141c0f902e241400300100c00380a403151100004c80a428010030b0810890000c80240c00c06655440954a800341a140410341d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 537487571 1250 537486321 537486349
    0x203030414010b03030f03160f05030406090c0807080f10050c040e06010c06020d0e07050f0f0111030c010501082505011205310302060f1006080c0706060605071a06 72
    0x38091441d59100c40300e80c0948a0b5500050b8140000111003444102c04400745010f2381007454414610460350b401a5085548294a000440d50a1000400048250f00540d0b200c51140204c4100107035070354a090700d048110303040000d00e83c0204070001500c44040012040300154110f0912003030034200040b1038507200c1d6000340e0002c40380203400181c003039005440070300c015503200c40c0446d0383d0400450141c00a1407078a540020900444200068a140240b10715403101001080c4c060405034100c015110001074800741c1803e4001408003201000082c8030b518000d011f014090110079646907000c0023a000b03250400100d00d40307001800e000303c0c0d9002244200e00c0ca040d400020305520707503044a60444126011403c4618503030080000030b152403109205042c1d10940817104d0a40310080007401e00a81144c4032403a000c03a040c0104a00d911651520b500301303201c400c1d042c0c5010740750f0312054265800f5410010204a00044d0342e0100101c0d00181849a40741c020705816504103140051545074804003 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 537488821 1250 537487571 537487583
    0x609190201180f0f05010e150d020a020a0b0f100b030108100e0a050d090602070614070803041b0e100e0709150e03010612030306170316080904230a0c02030304 70
    0x242481c2550352500e140580f41c0032580c04050b50b600d0082212a100b2406100d0025280c1048408103040008902c40020b113a10074440c1020b401c07000b0b03400250004401e41085102d04441c0e8408039410780c101074040c042c030f8400d000300b80c078144c22800c050003075640c403100842130100010001389001054801440b900110b011820801c06081035290843d4040041c180340140d40741c803407007036420620714003c5840036000d4607100c541c1c0302c00c02e40b031462481d09000c00b03c0d03404206500000300303070000a40c0d10611518079968114a4580700c00041603040d0004020300d0825000c2c4065480702410240050881201c4000c2915103408020b210440318820203201c08440c9410003a6035001d40d01e01c60407000050000c02829a5800c0e205445072016041900032a140040c08184161a85070070803042d40c80701c0081d880c10000d182c25403c007040c4440142c0d02420144086881907071180100c01e40e0340d0a41e01c01889130883d040c0310310040c110140c42054a9890304904050894020040d01da100d13030024 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 537490071 1250 537488821 537488837
    0x50907020c09100b0a18080f070506092b0b060f131a060723030717070c0f090f0e0303011202060912070602060123150711060301170609190201 63
    0x3581c0541c0b002d01980013140e500a020591040d020341c0a030400c41d080b91380d140e000810b20381c0e901501d501c58140882c03990f02500124810310013824540010000744074080d0110b90082d001c0800c80184e02600d90328405000707580421041800b0340200d400d034201e20110b601a0440500500162400140700c01000241e43c5849400b000189607640e64a040c010140038503035107405501e410903580d2600712883c0300701b45500840c1110b1810010645140e5544006030300750b162a071081140e081c0d000319008a03840010540042040c241c802c060900808140741d0120303540e4103000c0c44200740c940d40700381c8041b150b0040c00100442d0840102400880e41c0544440b0360350241140851740115084000b490301744200880000c09a03030008110341210719003040c80740c0301c00420880000d02603d440c02d07240d21004040c0e0440c0d942c0040d0000301261380c842c01c800125a05003401058a541099000c092068501c10400c0c1e24000244000d6038002130f5003002c0c20881e407460550380040d58406e800641080248 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 537491321 1250 537490071 537490081
    0x2011104090c0c05190501110c0604030518030a0b0f280b01111e060a060308040e070203120405250b0a0503100e090d030c0503091c18030b060a050907020c09 69
    0x246a003e903003035400c401070b18010b030f42a218000c0d02e42414102200d082d032800001c0d6180c980c0020a46190b8020b07000508000e89540d01c0032a469085035441ca00e42c1c071b450a00c8120705503410051009004e20414001e8241c0c5480c40e03800d400b452005211840c00c40c94440b2141ca01000100c5110440b00980c1700002c4c03890348840120385500c6502040c442d98880c80601d029400141103280c008140480102c5596a0318428202c1c107669036031100500d01807003840248855955002d4980d4005064030490b07040c0004201e02c2180c1200680c3c060b58150010480382111030200d01c64603c00840f20640b1105692600b94010f0191140c400c01400704100400460302d41c6850f070301ca480040c03000c0c034200c05190800c141c2d9140c5920030302050030f004c80d25055003410320354020025a485042500c0240c054500303078509140c5881c4016903003008001010f40084420788000c807600b00a1801811400068a014018010785240701d41203140715040341820458490360000f64241e0104d4180c954103c04c0d212 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 537492571 1250 537491321 537491327
    0x5100302220f060e06150706050c120403180618050904060b1206060f0a05031f15090b040f06050901030305090f06040303030207050705091009090c090c020d030b0102011104090c 78
    0x3036000c1e18a5242e081181c0542d000c88550004001e90b40301c000e107071807180c0f20001001808a05e01a0fa805080402d11030840490410b070301a9038490f1014540c14502030403181c6403115070700119011000701d22404d150f40b4286080c25020f60250016040c152154010a50101c003243c2092040c02e114254500004040181e50b810084c1601c2000d844900702c43d100c0c120381902d511040341c0c0d960240340300907a0194540351a00700c84c000c03250b0280c040d080c0300c071810220030005608085103030f00440e222031300c0f041ca00111030020b0300103281494000501c42101c0041000f030351020705040140d1405d00f0f2003803003e9900d0114480c1100c0d494201f155076003110602040d44e5614503458954400c0e0003003000001d0503050b070010900d047c4240c0560702001c0c0c0381c07010015072408c01d65640105030043c110a010141a0742c0c0401c014501640142c400d244d44c0c0c12441d0203540f40b042e0548016001208642d03149600350080160581013400244079000c80f04c000003030b59020728400d044a03030f41c4510118001c240 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 537493821 1250 537492571 537492619
    0xc03070515040303050a0b0f0603061914030c030a1a090c090a0624090b09043b0106050609040f1b09080c06071707051504030306090f05100302 63
    0x6800001d41d40000c0d940e403824070800800b2201540400d0505000409600e494130a0402c842002000b24070748104140074417050340c0000700b407640c02440050480070241c80401101c40200740103003004403054191400e06080c01d0082541d54029409520b07800001101d841c41003035107500400a0000540d1130b50541480c001d841c54503103821444902c28409200981d1f0004c1d001da5406028143c49041c890f45141c4c03004000e5a490350024145410920042c0207580c000c00c4c042d01e004001080001198544102d80310b0b100d0b20f144030402000c84e042c203094180380d01c200a070f2607140d8000c01c09149050085003c40c03040750f0015100e00d954800081c500080c81d030242514020180e09405040c11a01c40541000410700861401c0c0c81442c0b0740c0180da240c004201c4400d6035000701e000e010500984418902604458811900c0d40110820141446200b000040c4514000e51b40801d04030b181c1a1580205c40341c0c5065210900c1c20b202c100400c40440d1030b00c54088950590741e44440308174103d800c0207800 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 537495071 1250 537493821 537493823
    0x80c1e1e01090308071209050d020a050613030203070b07030f05041203080601090e090c130e100905032503120504030e10030e1002070c0e011a1305060c030d05010e010b0d020c0307 79
    0x780c40800c1017014806030004000865100740c89002030151104c0070049480750460317000b94442c2e1400781c14016800c0c880e002c0e01d8813409201c0e140100b40e460354002802c00c0c00607000180d81540100d01d90051592040860003440100c5c1485840e103130a0002c00103d00014030000b90a000340f074408942c031a441035610f000100800a2490a20304240014030388450551100b1340c401c04072442203003240c085610401c0c0100c0800710003041244d002070780035406042481c034103030b0b5140400d0008103a5900125450880e800542007001103105145c0b40203071407504002e4003907000900d0042000300280d081205031001c85011610035030103c840503011400341c0f4044603909550300407030b00000c208003120340107440041e1281c40440e11b11921140100d100c0343c0d01f449050314020f9000320b61210520b446005011181109920711541510b03080441c42580c0718040703d0005a02c00902107070010617502c140c601400002040081c0c030751501031252001e024401d20b0108990380080c3e00c100300c0303004100301c80c221 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 537496321 1250 537495071 537495083
    0x30602090d0c06080603101a1e060c0d080903160305031f0f03030207080d0f050c03041e08150615091c050616020307031d0118080c1e1e010903 63
    0x140f6180d5400401d60082a04c2940c0640304800240341c010070b6034000d080881051010f80466a105c03007041201074051004002c1805608000e01c449546801000b441800350404c000c2440c1c1d07100540050080c4001000d030282c40d00306000c4054540d544000c220b000d65054582141c0320307140e41c00203e96100c0c0340380b2100c2c20311000b41c03000200c03210305845220031240243c090359a00d40c0d40e43c0c460f603241c2c03e4104256001a02e5124010314090041001c1c05104080300f00b00c80c14075446d2454100c0c3c02c5181e030303e001d5161090090812091500708480e10700329030a211381d1a105d04010011851100f803071718850041e0100410011070944a03090104500024100c01070000300c4a41413242d21003401340e405002c16201e05182d08032480c000070480c0d0755107034107694a00713120400702d1168015280d0300c24194104602804c0d001d1040f8415510700019216030320103054000b40708420003d504042d0181c00030002030200e0b003c0515658401080000258686003400c0740b440f030401254003054176080103090f = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 537497571 1250 537496321 537496343
    0x30509040914010e03040e0708070504031a100501050c0a20090109051f15050a110a03030c11070e0f13050a03080105011716030c030f1404021315030602090d 69
    0xd110072002c00744411024000200880d0320321000d26074072072145020762000c004603a0f0200314214424510766a02c01e50501d041c45c1026100e079182c400c8046c180c60004445001d090900c105014080c0c03c0030010202428058544200030340b41c41e0b20750304030350310281480b80b094503450b01b4124020030a1075401c20007489080c00c0d43c0c40b8070300036006200664003001c0403042500f01026041131042d5840607200d860780c01a0107032030303518000c607507641c8120000c00410041e00d680c060005810400740714410700c01c0d00c0204d81c505040a0041c104000051441c0b0640c0c0414010050780d0043c2d4100c9402506030a0000c2941c2d40700b0b40c038000c8102034614000c0051180a4503d02030690289516069510981c5c40f1140c41200070300b1051402019076822031070303120240b640c10f94103003c0d500c010686034041c2800b1401d0410f9103056000c9801000314081144844020002185480150b5484020249c503042080455045a00c00ca0801e280030040500303900243c00384155642d5010303a401d0075404a03003080d07 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 537498821 1250 537497571 537497573
    0x4081504061b05070c050402070807060510090c051c020f1b03070f1a0106050a05120405120316030e010921020705061b0f060c03070c020a093e03040b040305090409 72
    0x403c41e0b10002d42910a41c2004c0c0001c2851710b468001c0b1051030b0741080941c1c1c142780045d252440107000140006550080d03450707001680300585c0c0914a80a0415160705444c0c0103480c50104452120003041c1104900c10454018850011800d0303c050fa1503101900c8601d140f1420700f503255100d221006802c142d121140181080064161040c40f41d074982d0b0f010441d40d90321103050718240161940000400c4050100900e118100c07500301b82d2240c01501142c0c003a021219444040360300035506440c46d1503120300c00c01040b94240c00b80705402207038000200010300940d2504600700c603a80c0300c2d0b544c00115105581505900c01c00090303002e404000c04860399010542c14030160441c1d1080340e10b031a40100440038882d404003244442c46070761008442d526541c0e6a0748110307200245e1043c101d0f804040d410f408944c0d14481d2280403811a5000d4206002c2c00140c0303241003500c4d08960b140034903e46c0b41c000d4290040e41d0f64040ea80c204c0d61044a0505903200da00d01940c0798081d820445400615013407440c4 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 537500071 1250 537498821 537498827
    0x18261c0b010f09080d080903070609080a0f02060f0403210c020c01030614090c0c0322051c080415030b0310090b1003170705010b060c010c1404081504061b 68
    0x59100242c0300d072001e800c00030205071a0341c000c5104646042d0082e00000d48180d028205069102514001360303890101c40c0c0c1d880e4422070380c030110242c3c2d8406010904101841d000701481a80304031a000404c42c1d440d00405a01400d0340041c4010100515a9941104803591710701003c0d6102c0402c600b888640b895540c02036a40c119400a06d00180c1411000216110380891359130001380054415400741c4d07601e400086055000310310180207444100003440f000c03100150410303035881c25050b090a01c2442e000c100141b102c4617040c00d0703106017450804140003a0030f204c01c4400311104030288215204204209500401149110503054092036051403050100c0b54400c072001c2f0300c02c160707442403500d402e002a90000c540c0d0100814400f21644076285103108040580200d92103440040b406100c00c00108030300e90003000c05800c00369114480110303117a0b080300c402c144c038611a1020317909040c50043c103075681ea260100da41e0b0748400107801003018009150003980300c0c030a0b90f0741c0b00c860303180070b20f1001 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 537501321 1250 537500071 537500081
    0x2070c151106251b110105040810060312090608160306030b090d02062401120f2409050c041203020c060c030405091501090e071803080d18261c 63
    0x3c015500c0c14603490040354000c0c2d0070351030350408028440e00220701c9a6200c0800044c4100d00307505200007440002446030082003404418000c44e41c0101c0c4491139880c1c2000c03190344240d82041440701200052010030740c0b1003080d030761108140d0090788480000000a80040409400c007a103101c400e1000c01201c08070010f40d059203000b031942140c1035580c0c0c070040002103182020b080d0070000c01c00010805958401c0b840c80c0200503450500040a0440182e034404440480143c24012054010106843d40d02407000c480104681c400c203000e0b600c0c0000040c05140701c1c60041960180e000450a01458800c10100b481d070300c00504500e640e0000481c00d250f03039800621986104160242c0080c688044540004030007a0041e15600303070450230300b0200c40c002d08005040000f0040010414250040c030400b031100210f00500003942d903500c40011982c10303241300384801c0408001c80c030b01d2100010f03040b01c04500c240c45040c0403103e141e10b405400d00858801c005110f0300d410446004803034004250350003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 537502571 1250 537501321 537501361
    0xd020904080903060c030f15010912110301050406090c0e01030b01090507170a0f0c09051813050a0f170702090a0b040b06120f1b03060103020906070605130b06030102070c151106 78
    0xd031f040c081d076942191040350101c01c0746280c0019410035042121421442080d84540d10038040108214110400b090860b0012282900e43c03c0e110216201032005c4400e03d40042c01680580c442150b0450300d40030052101841581e004545c1c170340000d117543d44244c103484004600f080011903507050554021000d460140c0242c0180352805a0b0010800c2c00341c03400c4c00449070042d014444041e00c240646840d514000d003c40030007124820240b0010f03c6c01d0043c1001240304035500d41c01c0d002c1030704003101c0101d06d041400701d814004105804c0035907101c2000940c440c0c240304011811103034000126003c2c04c1c85d56070309070b04100e000c00e41c212030b012200c110358854540d4101901066444501d610312100e000c00280c00061001c00204005500c02d0300101582200900201d10b00407e9607a050100d4100300c3c0d1006510300406c2e5150f0810201011140c0c01ca0421002036041001c547c4807142d02210904c14040714919408200002038050041d07109600c0503882510b155203013084a40054040c0520 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 537503821 1250 537502571 537502591
    0x260103050115030f3005030106031b050d0b010207171e030702090a09260310060302091315030b100303120917130819020316050d020904080903060c03 66
    0x800a00600c400d01012040341d4100c40c04864101003174a0b400c044190040042c0500c50078200001d90b182500c0c941c4200c80c5020340e803000e40e03a61410b1401400c42c0c2d015400d104041e0002020760031056071082c251890000d404a0018030854040300503480c1c449281c0c05010000100381c20310f105140c011030341012028038805000b25115110b6921500c034070803180025070000d03640003c22440740155211f8018a807242d01c0200611112041140f080b94489507980702c034442c0041040742c00c101c5007400030003c04040c281581041c0c010340005030041c0c188440f01c003116640352201c003490268650b000c4000c54002d0006003550502c0d1120340701c00001400107401080d5082c4d10000040b81520407070008541161345181c1600c0c040d10700c800594400c21300c0207295402c00c040030030184028880980e45400c800c40402074030a01d881454140454a001401048962002042503032550700041c08081c0d41200d1443c01c42d926460a80628012180d942c0d400d88200020041c0300d4072001c000314010040d6030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 537505071 1250 537503821 537503831
    0x6010602070612111209010f0f061511030a050d020403020d030c02011427010e030d03061505190c0212030a080103151a0609060c1c0807021506010f2601030501 70
    0x10619200350b6000080c04d500c40030041107003c40c0b000c42012074a401072403441c0007140610025060300155100580040003072681c40c0c2e03040060130701c0596814210036003404e0003142a0200e407140e0346c990081c100c0c0d81c4240000018540c00042c004e504403005541c0c003c1c29120b11f000a0300b0300406d45001648106c4c04601c50f40300282000c040c1005903000303410702c5090004400341e07602d58190840d03000f042581c123000d81c440421485076420f0081d1b8211540b2660f002413020328200c1010000c4900704464028003a04011a010ba556020401031000000e41420000841c5a1000c504400741c2285a03040314000403401c2035000e940103202030704907401003610048100c4940c2c05c1000301c0d0b29040b00d4160f03150200a4a00550a041000d07102c4c030710008100c0340c244100700340c00a06041d604506900001210590780041a42000b0100d030064154802002c0601546110b45010f20b00908801e0612800d0702c61103a88070722032400e811482161080102e60300c28207112050200f60f084c081103030f05509003 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 537506321 1250 537505071 537505097
    0x280803120c03090307032a0501050f0a11030f100f030506090c0109050607060b130f0504050f0c011413170a051507051209010204050307080604111005040303120b03060106020706 78
    0x860190b034010912000910315064156800740c0d9a035545e41c0d000070854003a82c4140d6000c9070a503146900c4039004400204041c50300c807865038142080180340651070380c50480b00100c40c240d5001981d501c0070b0400c481c22001c1d2103009d200d6180190f1607000454159041ca00401044008031307001e030080178800212a4007640510041d106404540509034120000740620320105010350810040100041c002600c80c005401488083d503045038002c00c4140c0c1c484007480100a001c00041078401003010140c0007501d45c85c00000c000d000450401e80104001203110804103402078000d030300804095011100c00340c814000c03035032101c585030810b440381d000309880078880b5031107005003e10514050347e40514100c06003051507144034001e4a448402d40d401d10002c10729072420001b010223824103400a0056160a180405440e40b900c40c1443c05100c0c0170407031003803441c1c05c2810344080c0e0f64075042c803040740c4169040050040280301c1c441a85882020000a802500415040155002c55035910000548 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 537507571 1250 537506321 537506341
    0x2060105060415032a0f020c041109010c24091406010605030a1505040f140903040e0a020c1501030b090d030b3109061a01020606010e28080312 63
    0x2d500c1000c02c441040d04410f52028070a620490003117049280384012210302c1640f40685000340c05120010890180ca0040113540402c1207181c40c0c1004c40e0140583c0900180e61039050280c0d40e40c0a05101c0c0703a00c094410045c0100384407180d03240a031070b58044207801009004c0904082803080e907146402401c9088080008104581607070742a841d02d42c50740d20b0794100117000340a030030030b1500c0045405d00c0104070350780d550050f0030010b0250b100205007002d141030407411030100905416102d910411040084000f544c3c4002d5019420f032500684900d050322000d407c100900c0386141808402d4800441041000007400f401011144211828405500015021160200e0200358003104801035155800111220180c0c0680c04184402a00d1070307a201c01c0080c1d851114040718802c1d01c0301c46002c1c00005003900031000c4c8101b48020100e40c140100003030004102043e003280100390745203000d100c000c0001e030b2003084440b00300c1c44006055640e081980e00c81d0030132161407102440d4140829002c240c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 537508821 1250 537507571 537507577
    0x8160c0e1906080d021e0a051509011d0c1003180f060507031401030809030f030f040306230a09050705060a020105150102160605030a1e0212010605031308181207060206010506 77
    0x1a4517002880280d98040c140b04003010544c3c1182903601ca210075680004100b80001c220b42c3e55011020b400d582040b8140c1800e4400c55004003c03411110818100711020020b0022040d44040d50140009111100120040d0082034103242c40040601084020090b807031030003100032800750004001a8a4292048007a603528580f0b0741c0c0c02802980041c408a82c3c0f88000f8502c02c60300508640032407081d284440e04680014000e041e4140b400700b020410700919004e24021044003d04524908100403030344400d04101615908209645080c0a41009800c10808002d050020032194a03100e146070000d000e00003c5078181c803025003040103940503500020785a502110500d8848240c20300301507085925400061000081544a5001885035992049000c401c529440b00161b520425031010000c03180042c1c1c007070320401030100b041140e003c4102481c050859401842c141d0340c0c505600d441c0d40380c00c1410b20f00a038000001420700c41001c1c40007070010b04481242c3c0941d05260303a103208000d4140 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 537510071 1250 537508821 537508843
    0xa020f0f0307030213090f0c0e07050301031716151d010b01020d050a030902041802041506080105060a030207080f09100c0201050f031f17010b04020708160c0e190608 73
    0x82e211210500040c0360480e005c1c035080400c140c00289a4985407603c60720344001c50001d9072400704807981031102c041c440781e986a00511500708245907503d10350b505020601e010301ea11410010202d00c0f40c15000740401c184500d107410030354041d03080807040c00000c000c02d00f13070704911010040e1000b030418001041c001e41d050700788140c010744240603080348281d80c554803031070b10101015615610140180c0c5c5603c9804815200689900d20b17607062441848100d034245400d0031003080c1528000c201007039019801030705582090300c1c1c41d0384481054a0a4000c0e010b4807030011301030100411044080e1174008050000341e04120b07180c1c25280e200d08800c0e03500342600c4d90041d002545c00c01004401c407d40304002d680080303102424242d0010030f1428410001e4a42d080b130300401c0301e0014903840c003d000f40550b03d2150400c640840c60f0001036a1503a045101381c000b80d690407030000e5030050502103050f800070000e040c01c0c60303401d29500e4240b0100d14140101d4000d40c0740b461030940017052075040003503150215 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 537511321 1250 537510071 537510073
    0x51201090f030507081e0a080f040b04080a050c0106080c1c12031508010c031d150f0403110714010210020301051c0c090e010225020a18090f050a020f0f03 68
    0x40c0e0300b038504480642c007441003134499000401400b50341940340005090300352800b9001036103074100b0b010000d0400c10007030107540002105e14103000c003240101e800c46801a0744081802ea075018192010b0700c09010306440980c4551900000041a500100f64107150600c1120f601a415214800340d004110400c032000e0402d004245c1c0003d0114042d500004112022010070501c040e40c8030012400c0d140402ca94000094031a41301d02080c01c1880280c1c0b81d00c8c4d40b60310141c968440f60340440750714480014401c070542050b45002c02c050502403203c0b24041044003090380c4240ba01d80e000d40c1d800240c200d400500607c81c0c1f0140210080640c070030343e8143e03000103103200440b520407105545548803603242600c0e014240400050503144030300c22081c1c1002084009600c400f180d0880d13041404400c52649070250042c0c50a80050b80c46280c0301d000d50b00c403605021444000d4420b080000c040d030003002420710f05a03210303550a00c0707400254071849078804c41d25a4000030544041c0440c41c503820303d1460b01 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 537512571 1250 537511321 537511343
    0x2a0f050a1805041106180a0b0c0a1112070e100b030124020c04020a1205090604050d20060103030504090b0a06050a0c110d0b010815070c1101121505120109 68
    0x1c0e0700e549401c500d0f0024003480c9021000c0e4001c80000d40b140e8010100d030301c603210302070511805e1810030103900e600034000e001c030141c20410100510b6803a180003680051405d107600c5400c0495580341e01007c1e0300d030b02c2d00303804441c4903d460382d1101d102c044068600c40d5a41d403046400041e403580d5103080300e0590310040e07031700112040190b100c00700c0d004c040180482907002d6880d0000b101e4503188058a4808010b603510448403495000d5101101e00250600303c4617004401004041000010340418104091910481c0340d50002032104a00309032120f001c3d813500406c0c00000074994400f018000340c90040104102d482e00031001c214446605100c8c036004501c091010b41686801500e4041007a806100d0344084039510301e0000e500ca480a440032581c1180e00c1c0d00601c42d5800800c80c00036081c02240000c01d081c1400100600b040061150050000c0d2181766200c519034072500c105480c54001a03803d02c034501c90b99540064101c024024140604005980044510170501400e2211608a002210 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 537513821 1250 537512571 537512609
    0x40b0a0b0d12021c021b0d1a040813031118040f02010f0509090a0e060108060420011412060f181605040503100204060906090e060d2a0f050a 62
    0x501824107070b400000754043d0325906080407242d8100c040450400da80901440007400310205042c2e28107803029801441c45181c02c1001484096a1490907010304481c405540d0300d91800c03031050f105005020b1004071584c440002004a0340c0380e441d4543c0f804a406601c003654541000c0b10f003800c101c502a001d210154200340255004801e0340400d000c80d45012441c04104a01240701442d003602c1201b60b00e907403009203064001007409480d0140c00034038054405801c158036403580c008078502c27080c0c0701241501140a51a8000d846d0340c0505501141195101c0c003c51214480141c02111070600965005040c1c080514003400c00c24504001c0c4510002c11341c0b0340c4555031041450686030300042c01000c01002c500c66800708030781c0800014410026903101c0c00c105000b00002040da10060030301c100b0403030500050f0b602c04412a403094040c1d4001c12003040c83c0c01c011103040a0148050028902900f80d10610004000b20f001621419007024004039668414410210080e1141d1104020f00d40d510f90 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 537515071 1250 537513821 537513833
    0xb0304291b12060f0604080703110a080c01120b060d0c0e04050709270b180103031d06091e0a0b0409050c070302072102090114040b240f070c030506040b0a0b0d 70
    0x13100c0321000f8203850300f09500d501e415843c005544d041902c504001d4083ea6040c0d14101d05000040c05000c00036014218242c03001a18450305490800112500d031098812203807518010b99608001c000710a100d01640404003501d480102a400c81c047c506101c0001c0e100c5008040364000ca840300b481044000d42d100302e030308111418644022101c03549800080ca8039545042c05080541007071031201500354074500c0e0280461940054a48988000e129642030640c2c1e0390065603071a40c0c05841c121450140103022555100c041c1d92042d0b8010f0500e00c0104500391a400503006aa5a585007042291102022116180958080280164801301042c81820f060034200c007807420005041c2240010135030300003205101d00f41c00c1a20800c01d01030540c80c25180c9405180140c6000351510044005104080010084241e012491030280040c80300c0703042c800030044500e501d8000c07041804460b10380c03030415100e0005540545002e465a17004c2201c0b45500d10031107613a8803008180c41600d090903070b943c0c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 537516321 1250 537515071 537515089
    0x3100b060409110c071518030503030c03190e2103040b01051c1509030e0f03060103061509020705060f0105061207031a0306040f050f160b0304291b1206 67
    0x144403254001e11402c10302500c100164000742a0f07880f2181c5046d0444a0028108203041c0300c641100c1168040c1040400c1c070106c12a500480d400440b95520f80c0c48000060360307005903da40e000342c1c0d4a85181085c1403180420820034801c5030304100046100c403000d00791000c0c003095030f01508a10744400100400d00e00903080e038407542c00a010440308442c03291610000e0304007c40ca4000340d036445001007410594842400a084141102d112144d0352003003021950700c3d40c0c1400300802e8039517515103082e90320740d40040070002040c100784150b58903070561400540f100d10a85000d0b402c442030000100b26481c050b401c0d241007240e110f500303c0855a801504502500d000c1031401080d06813180c1c4000c05032000c0c4845841180a552010f65140c2a0b00d40a40740071030020795200c81d038003d961005c44150f508800c0308201d800300480399440c0e84581c00c0c000034034030310492081c020382d240040f40650800712503440c5124a20850181405865940e0022854170030440210703040c140036000030b28507190007100 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 537517571 1250 537516321 537516341
    0x20306090d1d0415060314070c0b0402100212160b070801060f0311070f110f010e0307060c020f030307050f120405150703030f0507032c0601030209310203100b060409 73
    0x40422802114502c3c4c001e41d12030b940011001a0f2540d640c003110801d81d0401a4010190b440d000e1298041c5842d008510203001c0d10003481808402240410700c0d1080010035417040442c90300c40e42e92014035440084172120400100c0710302e241600001c4640d400b44088034106c5500351200307030741001a820228020045116014100001409441c01003010121406006403040069480b001203401c100b0482e60000000c0604005020503584410786001c508501159601e08120044d8682d074070000f220003084000031a014800841e8010034804000f030014980100003080c0c0b1000c904d44030040060344210300556802c2007406209103040d245840061908501170316000400d0091002c0300400d0342c0044c0c0748600001d0311002c190700350140660001407011040f507910038449804021071a114601444007070711908000d000600540400070b0021041081c07005440c10003084045000c500d0140d8102c1a4043e11880015000c800075510500c926024000d0000b8201890000484007825001d10 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 537518821 1250 537517571 537517579
    0x11403060727090b120109210201021e04051f05070b09030904060b0405040b0108010e01061b08160b01050d0c1e050a0f090e0303040c0506070c030b13020306090d1d 72
    0x1000e00d80001055021501800322903e0110b00e20b104401000072030100c40440320380c240d14040f141c500080d0107280b01d583c46485040080b2000105032016402406a02101c0e04c43c03004651060251881c010000c1c41030b9101220700d0f4213482072800f44501c40701c403450800c5010500802205000c45c4541c0307003841d0700c001ca51003128a00b00f0002c02040998001341d002280040f030101c1c09202c9441d090117580480482031034510110361400c0881d48210070103201d210144070750340d8203013400c0d194003007840b0b484c07150020130203a0b84890b2201c03003680054605a054031202e400c5000480e6516282001620550300001000e001c141810000c15401c07000c2c0002d1001014941e40004003a00d614071520018419220300c0321406241c51841001d48400540e0759616406c10020400002d40b2961003006852003500c0d419100d25403032400152084031034002800c014004010030000d071965003000e1074101d02c00d80580c0c0040d210402d50b290b903412204c801c1ea01055102c4106098001c5805070701804c410028 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 537520071 1250 537518821 537518867
    0x18030a05030f0406061203120c050702011e051201030f0302062511190813090204060203030406090312020327030a090e060d0b0903030a1802100c0c0302041a090114030607 75
    0x4002c84d446e0000359408501140312640da02548444d68460980f2840803410900e00e45085640001e00c00c028000d00882c0340360301f06800240075807148043c0d82460120000700401561207003807a05078444070040480041c131a0000007287c4501914000d0284451203404400640d510542034074609250359402c0c038180301d0076423075200951460581c80c40c49405011103603941c0c442c68131400b040c0e003610f0300a8095140100703c101300e00c503800030407254059000140020021b5003454106e481c100d000c100421454004800c3c0700201286040c140b610a00b10325540c9062410030075141d44a026212202000c5400b03d0810000c146918190703e40c800c000034800b2040482e1580c500c1c00d142c2d01550200115440030003008201c120610804a1644a1500c14800320140c2d9001888c2a40f40c00d0b50702c001c02c007042c01080e00700001d079104400074550080c0706020380424040d012054002c03c040300d51003286100c00001e4280c00c81c040c603074100e0f41c0160127008a940c40c802e06881c40d0030007040184900c2010 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 537521321 1250 537520071 537520079
    0x5040b09030f0111040905090303060a0b0c010207290a110405040209040906090303090b071e0f020f07030302101a060301050904020d0f0305030a0c030e1f2318030a05030f040606 78
    0x81c13085084c0720b0100344100d5103844c144114034084810080c50782d04550b00810910810ba501c5555240031500c01d0f40c401540d5487c13591040d800b81c000e0300002040182e1200012110011117502e840c1001440c450720440b070303035501a807001951500b006466a10b4402c03c41400103082a80090620718000341c0003040c008030a9807030508550b40c074482030740005d0f5509100f0b0200010f400509801841d02e28000500345c00c130000c403804031180c0800c1c04042c804c12a4101c84214001c1c4201e07130000d1780740420358211a5590801a4944507041c5024500505d801c01107148080c40000d240005400030f86003600f0f5a08040a00001c00406403040e80e000000d121001c001920401298100700d11a640d40b58a03410070783d09070000e8070207011440b400e050800c650242100c40c0040d00c40b4101d1901c500c02000300c0f21041502e8010484030f00d04004402594201c1c040b1a400904210300402c01d018001000301e2525100580301d00441ea10312001440030800b04840454515025401a0050400003111aa6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 537522571 1250 537521321 537521323
    0xc0501030c0e12010902100809060703091403340c050907030b0618010806040504021012110d2702030d2304080105040318060e0103020706060b0403080715060605040b09030f 76
    0x2801500c9202617440c0c420a6045003010603558664402d80e06046a10741040080c00d51250030003001c540c105665942224107200001d4407401c0d4046601050700c0c1c4c1d81c2003080114901d880c0c101503081c43da804100d5071080203402e0902c0242c07400e03013041154001a090208003c2274000251840c0101619040b9040c055500c00e0001c0810594402840600c80308100026290030402004a4429440c080400015071948900303580c200189141c1715040b8880006244000d11301042d80074800000401c03022400000b9502c91001803001110940345044607901c000580044100000d4050f0003516203206018041c002803940420b0001c03240508022001d040c40d10340d007140e409201107a44440038841410b42040414003c602144e03400c00f1aa03042c20380291442c80880f10490400d03600265031000c0c0100c0d1361085025289014400d07640e240d51f8101041150444d10702035904c1c10109081d08401a04c5106176030440d1381d0380e00d54500302451710710031940c1600b103081c10365014000c291151020300c0c0 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 537523821 1250 537522571 537522589
    0x151308010212040b010609030c1217030108070f0801060609180b0306150f03012904021b0c10020706020a0206090f0301060b1b070302031b030a0b0a020d050c070c0501030c0e 76
    0xc620000007003180f5090030034140c003100c1a400b0700148441194140041855801d900c03040e0348102c0340c031100301c4803589401c120710314203e1407a5034a010702000110714003102066140490344188050f04645481c1c40c030b139074200c50780c512981f00800d40104003044900001c2001c48c82007400100d000130420242c0c004242482011540100c12001d0001015100d14281d02e980134002360540081000c0500c40141440c9137070301c0e001c00e2060781d100c2c22005d4200d907160340444d40b8403404200c2460011100c07028490ba152036052425114003020001d001c55684002004003c680c410340c02800c0400c42902403081c164413144413130f17403c03252450408601d51024090003009000040c07a55507500c99680301c041d8800c0694142c103680c0c0d041001c0c03c10250b6400655a5500d4840310136051602d04400f001920340010608002d248290100400841c2c5400c0d034050422101c2c1d040c0d050210707030340700c0c050f14055204400c0010221440407070180402e500c203a00541c4031004504221805c00c01d08000205010 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 537525071 1250 537523821 537523837
    0x70807030e101707140c01090803070e0108070f0804060207061a13020c070b03061807030203070f0806030a030c15060f080705010e0a15021c0e01030e0c1513080102 72
    0x40c041c1c4000c0116420010512000b0180c549000300c09203410944807200580c000d400d8604100d035009003a0794500e2408103c6a9024440d8005c003c036445501d00040c0f0b90b0001c4403460301042d42e041031150a940200c1c1058401c010f02d0351000e012002c403d0b810b0321602406042950040c0d03080c059040020366912035202c00012240c80d2001070424881000354500c0a0140010f805005200000c026980098480b042d5988048500d0b120359800010699103ea11000b028050f80654148050342c0c0d01980110300910041d5601c0c0c98009a188040d14000010341d103860b0154000c1d110400802c0c4510001025184500d4104040000900d1064207030340c030540000403c9851198104800315007084400003c01e4282000c0b501c0c043c5110000c0c8070705626101d82d2101c00501280c040d0407a100740040c076080d17030a01c03030000115003100c4d0f0001c00c3d02c0520743d5440e002c039140178030303116180b10001000e40000754000e0400c030b50b5a20817581c1e600703990040b0b014028021069440484c0c4680d003070018000c0c0c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 537526321 1250 537525071 537525077
    0x312070309020f0a08030a030b041503031805030c100309030903050d0e12010e0604022107060c05150937030305160504060c0b06030c0a08010b0a1a09041107080703 72
    0x1c94040c0100841803d00c1e0f88001e10505810800f08a642c40210590302111014100010419480d07804078002d400c0c0450f0f2800e004074904004800c06030410250b0301400c600c3c000900809032100c060540c1c1d0740300030200030381c80443c0d4007080001c940707c0d8100040305480382c80d10420300761340c940d625450710040380e410001260342da0500402c80c0c100004d075141c03603503850f0009020400c69101107584030342c4090300290140700e060000d02e400200e99402c0c2c03142c111144040b50340c6c01d6500c00b802824601d442c01c3c02c0b01c5500a4444000911881074034113070044480b00098a2584100c451201042c52045d40b0700462038031640d88216a90105510520300303038069100401c031854460400c841c0d8107108400b01040c45014082401107039880786403000c025030300040405179a00c5d03070000217143c50100550181d0113a0854000709031070301c040d00310030031040013918085150394071100901c41800340388149e03007104502408019103901e400d821144801c802204528580741103500d60070804c1c2d000040507004 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 537527571 1250 537526321 537526331
    0x305030a031401050a050609120303070507110910050f0d170304050706140a03050408090409200d1109060a08061608060904080a031a12240103022103120703 69
    0x8480d4060082e0070b100072a07003904102640c1044002044210b0900130039004a50202e1281c0302901c4020409688003500800c407a12854a01c400034007592060382d085640c680042050240c2e801c0103c00c540c0103403441c800c5a0395290803c4c080c00f1001e01e07484c20ac47e44c0f00070b0500d030842c0481c070103a140c40e1281c0140042c0c0f5035a8503003410030926003070075036010004000e2803c14802c03900d02c07940103448142c2410700d000700e030766142c50030f00c0005406810310456200f45051070620030001030203d0010345501d60010a45c552090000f00400440d0300030001d880c18000c602000e07240d14007808216400a0018800044030340c848080a00d0705004413408400095007040c40d5040d0394000c5200e41c2d1101c0c003203509545926066403108074a0081e0003100c1d0505885a4056450100c0c451341c00041c842c002d402e0a8200c5a55603030251340700d0315810001445140b66000f9001039081d170514505a9401500c2c4040c140a41401044540700300c06224095000074480010780501400d003041c0030300362554001c03807 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 537528821 1250 537527571 537527587
    0x2604090510030206030c07080409140a06090203070905040905070918210c03080a140903120123060c010635010903080a0b030708120c070605090102100903050702040501030503 77
    0x100e8001901891260184150800059840c00304070f95010040007807454541d60301e45410b4016009940044030540d00b011981440040c0700002a031103091034245c1441090703600c0c0801c44c101e104c29103c800008032800c0c1c0510890809070400b40e5041e1003101211140e079600c100788001c403161402e50121158070b216111050154540440300c0505512010110700420180d0182a40e24040001001c0c0b01084000a145d40c4650f40216140c0382030700459007a40c40c18080194896000014008080032120008603d481480c1c008020001414040c1c8081c0c1560404000d1590400c1c5a0a64950f4070303000e0100b00c8a4490a100a058640b08501c032411000d065403245091041c1c3c0800c1c9950f0700d081318800229502c078120603040701d601600090003050b08000309050071500c2d00f001d10603201c1c03141c50b0b90103640f10200400384079441100341d801d03403610340e50100c440748240074010340168008030445800d90030b15484910a940300342030003880c11445a0100b025103200340e00c26205034001154003c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 537530071 1250 537528821 537528839
    0x180b0307090b030601080109050406020c0d0315060219030305181204180c1202030c070f0507170d08160519080417270f0d060e0c06120f042604 63
    0x980500440b820881c114900500000c00d500b105124242c0c000b61280c01113424001e00da81191122a4204151000b80e5102980038000c0e00d1114103101440010354030001d00d0a2002c120505808801e0540381f005a40d191000c50203400701400c81c031a00001e95050180e0041c0c01c01c02c0c0f021324140d843c1404d0321140b50442003110185040c0d0480543c60600132840b40302544071203d03e03031108091a0068491316010506050f034025071800611920502142c82c0a004c4009441e00454564014180c9070720403100180e0380b1041d0003400071001c907000c00c1c08109400406070b0503112034151850700c18280060103203902804c0040307070102400300e0b02c640144000d12820340e003c080101a40c10000b460841d0041c80500140388010034600c520900b01086a80741c0c0d41d00a5491000c0401810b0340021301003030a12600418000c401001c05220748815450703c1c0c1411000d40b201d188450361a03c10320740e15042503c0101000410481d9081194100810031400c00c0004402420f8080b00654441d03041001c00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 537531321 1250 537530071 537530087
    0x611010516080402012a060b0a0923042d0506010920070c090603051006081209010c05070510050406110102070206070807060f0906091104060806010510180b0307 71
    0x141c0031200d0120900580075800c41d10301c0ea00164280b81c0303004880160030401c2400a402001c0c600607890210031a03060158607003010488401c1203504d00b070020b540741c903604100c03400360910400014214980c40144c2400c4032600e1790050080301c64489801441200b114608410707885d4011003e00c0307181b82401e0040420000c3d014100560040114040140041044240e004069201030748005882d1041000b80c018020041c000410103100240e1039142c207a80328590107407941001e0b4a854130000301c9820001d03d1141030310301078002a20f0000071000448010821b40c40c00e0740c0307900c104030b000125511070001c921f0607595141d5071240c139281003050041060b02c0017000118145c2c010b20684e401f682d221750468101e207500005107030b6204e86170718011010b0181c460306034024500c1e1803082c0050280941200190710b202c1e030441103480310540100320403161a801004c0c116130021005122608040c85006880042c50800c1c080d8442d0100b2903400842c01900300700b45600c0007005200d0030030b03001401 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 537532571 1250 537531321 537531331
    0x7060e1516111e120304050c01020615150307020a124d100608010b0907050c060105010302092b030e0a151812050105150d0201091a09090106110105 65
    0x205640010002002d566544542c41001c4180000c0c0d03d40b0b015088000c02c16440140c00345007805440785001e040468450701d00520050160040c1d40000e584020b584118010521f0020503021501d20300c40d03800826501f0050185096202d41c42801c00460a0341a103c00010300594a44c52040d4412076841a4040200e000c2107411400d0a01e05aa0240d01e4031203aa07034082d680444002040c00d40c01d544d10b400d0421030b50510407846c000e80403a0010040d0410500c1410a8852051548450388100c450f403241448001d109d40060300103014a40c420b8006141b0603600a060744181000d0305581c407000c90301a0798000c92038600c11095000c050304883c101084a500f11885440c245c540110000120002d002010800a40b481d4a421075854a03480b90044c1c000020a9404030b903a600d0854000c000035161020b8510b410100d0b000c452800b880800400b540c181c0d42c1407091454108180c4100e05008240c1c81c24520034007000c84248c0f00e010015000f0f00c95a6207602c16111080821821110003510b = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 537533821 1250 537532571 537532577
    0x602091c02041d100b220203220302031905091c0209061507120207270f0b100503250207090b060703090b09030708010204090603060e0d0903030507060e1516 69
    0x80107290b0010200c0c2c1c000390140c0456010034038101e40c00014809941990203c50080c03030a64130421b0860103540603520900201141641c00c408000c40743d40c2d9548282002001079004002181c50700302c200220000742c0c41c05040c82c1b0b042c0b052050010300c3c2880c11501441c05060038141d0344e405e614001039029008501526050458140c5d0000b17061584640c01c80a05001d296480c5d40ca481c40c07007085204028003031f5008901c2d480c0711850301c6034500b00112000518050402c45a000c1c072410f00d1050b40c00002c0e0081411034000e0f81690143c6032504000c1068004524001c0c0071030554510b06d80a98181005034050070b80e090501709100212000c0c814038501070b50b07061011100081d00010410140e4041c920070f25181c0e804440007900d01821360304180c00340e500101d000505110130360040802e5a01c07881c41440b0203803480001591300c1c030b690706008000420b0300c40d0400c0172a020390020300c0b000313006a00205805401c002868680040e00044c030600e41110340402c0044040e01503444001c5946c1d20b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 537535071 1250 537533821 537533861
    0x2070e01030819050c01020720100801090b01020a12080910021908180f0c030706020114131505010303050403060f2c010f0612030305011a160602091c0204 68
    0x285903402c19000d01408404902c002c0c22400e42030a000d001504c04840b204802507540d0112441e2803501c000c07a41c039042c2d20002071558442100e140a0b207010f07203071807410303500c480ca282e01c1c00d8846800b0300a00590141540515000c0c04003140d600e500c808030041550f103a000c0d190402031040c601c2c000e99110078400303103403060281c05544031b2108080d800460341d0f40b400c0b00315034561070b00082c40030303891081418440c4140c1305401c0c80302c43c0105480c0b1004030220706482500b1b03a1800182e003611804551501d214020800040d010701b442d414500c5414001e01d11240d00c1031902d0b943c501200c40a8000790301159022a08104001c994011419030010003a81800f42980252440c06041140c000400741c0c4400a590000100c00940c000340386c2c440103940c1404401da0b110503588807180c0804042c1e00180c10070001080c02140004544d112100500c1031625121020044110904205a0440d40240c00700301e806c0c2243c1e50790080500903408a4000758601c01c4030320412080f146241d950390620b5901c1 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 537536321 1250 537535071 537535073
    0x241d0106020c040b0423010305011d1507050702030a03021f020a080f06011101020a030207060c02030421030c0b01151206080c040e010b0d080a020c0f0928020a02030a02070e0103 78
    0x10403920001c04059402184c1c0c1043d00000502030640d45c2014071085c044e0040303006801580c50105e50480303002e80002c104d1804a400c41d0707040504c052240c05080e50006010803e0701800c1818203a00204c0e6142c05030070803046a0029003042455541034005911100700768011420a040d600c0907a40d900104501d00300180c04094245000103105032000c503622400610701e070f406805503c0e5043d04050003103550b140500e801400a4005241c1558410728100c000041076000001b00e40a0300d954803800c111031700c1401040005548903020803020020703c0d5501c03100082550111501030640400c8500d000030400320000d107440c00e4a081c81c2c1419041080410400f600850541200706d02518080381e0b44061502560150060b0606c650b0000d411164003020310034400e001d0706a4010641c26101000318001c10440b40740d090042c0158491106800700364234440328038080c50071251444101440c0c0001130401030417604060b80002c0580c20010b0389950f460f038107004020107400e40841e9980e080d411 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 537537571 1250 537536321 537536323
    0xf0705070f06080f131514010906260a050304271a10140d050f100b040b0c1905210c0303010303050703050f04060e0a08010209010819241d010602 64
    0x503140380c00084052005c10940c6501d00800301741541c002d18280c4000403600700c1071000305122080824022050f0001260b60f200d0350103101c040304c004504811400125440b8001c101030100d01300c40302c912031501c0904c0003400c24006400149582c60301c1c10b007551f00b0448039a07031520321000200d89082c50f00110783c6e80d40703003083c1e005203a0b43d40a0b90203111404501006a031456040484075070800c0c1c011030034072110742007508000c0c071482c494480c08200d078039150f411441c3c00c0b11a00940083c003005100600c40055000c010f000300740644421154041003030580c107903004034001800d4803150016488102d2081a0034180c441443c1c0b900f201d103140c00302032040c19443c0d01040c000141040000505001814480d10944040d80009c2d0091690741d5500d045c09428502c0200110740551300c01140000e40c41018400d40700c4656041e100c1c4880c0c1c1e079640c001b04010909014403c480159180213800e43c034981c840720418402c142c8107a800d8a039081c280805010100c9a00402c042c44080d0018000103034 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 537538821 1250 537537571 537537587
    0x60109060824070203070c260a0308010308070218070822020108010e13050706050d06060e01020a140f010f050609011e090f0212042405102601020f0705070f06 70
    0x51200d5100b003550700d492104038258403402d040503054050600b00410a82844000246040b840a044014022054944070b8807051039a0000d00400d008400400204e540c41c001413058901c003c041a0254240010b000d114080a580203000a0888400c000340700007490101e00c01802c0080a03403480700d0f6036a0000380b81c00c5050140d204c05056120200e40340e44005504514495400025070788025180c8a004241d50065031889032540e080880002e0704034058210441e0250040c1c0c064600903003035898081d5001040c00104c142d03446205640081c0c20404c0c0b298910150204101080c035040c104104807441e541a00a24032800456450b40c002000c10800f18040b1058090b012601880031007415000740608045030329000f10700002c0008200300d035200c142111213042c911004844800c0317031440480348102c0d186650050850b00c00c1c080c0d1100c11102505007e0400c0050320004d003130721601401c0e41c105507421031954501160300c404008040c000000602001108061168a0041d0050001c8 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 537540071 1250 537538821 537538873
    0x100b130b04020d2306011e05091210140c040f120812070503040302061605031503030f0f0c071d0601050304110a0f2105122a0601090608 60
    0x659844041910340c807650142e40408200d45020040b690b0201c401d080d040300107441d107650f40c01c0b2000005407a507010341300540d07914910600340342d500700c181c210030303103941d44404502c580c84035218504000000702006000240101c8081c00b19200301c0804c1039120710040a014014200c8003840309014002404401c2e80844001215404142c107181c01d07d00072074801e4410391440720b40d400c81000000c90b000001103005510907030850f44940c1d10400f11071801c01c00c100004000500400110340e20900c40e025955240000506480c98a48502007040a81e8480015009012408500e100d503c0ca001d01c0355200510766451482429811021210302840009204606002021000c6020700100030311000300010b010340051041d40c1c450a24040404481c41061382094580c0050b003080384444c0c040f0341ca13190348680105210700020364a4110f40e045400c107042c070700807040e07a001c00402980c01f600b5010400390740a450254146065102a950f25400102c0309601900c0850000c00c21481d00c502e0365 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 537541321 1250 537540071 537540109
    0x70806070810080f06060f0301090f030e01020304090608010c0f02070303140d020c060708090f0a1a090309030d09032009061912110f1c0b0c04031211100b 68
    0x5a60350148845600c00580080b0f40501c107a6181480e50b400009500c3d00855046840080c5125074104160980d1041c41000b400002490311000009008105013030244e00140152424070fa03d1701c02c400c0c21135103254130800d400d0f91a0031300a114107420100d1000208030a00c0070f007006ea4203507200641583d181c41c00e026030383c00000800c040c401121781e041e40d180203c00c4c8155142c901b000384005110900035a200007240c0a4031448c034004000004040f05041c1c0d10801b651601c51a02d10b03c400280c10003000310400c0d00040014a0703040d034003400004820441519070300411030a41c02c14550382c00c40003016100f00452200e40c10031656400b46880e0380008103c0b66010054540307041c040c06480c0e1503010700320348000c4040150070000159103020305a10301382d1b00f12042000c1001000a010802c010590059080390003081c0402c052003402540f0140c01c03600b081c46c3c80d58a94503041c0c66005400b550b03001580c03d02d0144050003080c49001000c0011400030f01c290301110340003a41c17841c02e64408580c6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 537542571 1250 537541321 537541337
    0x80402100306060f120902100302090a0b0405030c092703120702070b04150e13061e0308030402100c02220c03050603070501120f1b020d140304022b111207080607 71
    0x40b0783c107607007189420640c0a401103100c0002340e0300207006034003c001190f00c1042d000c0700c042041090301e800d450450308000d0041c81e00900c4c41f41442100c01c00503002c0341c05004181141503180c45003850b8841c484010800843d9075921aa0242c0200e40b005840c3e802150080703031082203d0940d280a171019240d032900301c01418040e080040c0d4074100701858054111500050460032600340340e0105003103501c01d6106140c0480109450020b941081c000100450710601c08a005403c000fa005819198141002d50096105800154104050b00d4000c580d0080d00101c07540040340c6805240307a80310090600b40854245040001d4848003140a500e04101c2c10310705100b4031143c55003002066010b8820b0801689410801c038903000d556031611394006d4402c1038241c0102610070b00215442140400006055481e1703a8200100104100318800d28084900441c800022040040111003072183d5900311054841105000f41d4001c56070401c2c025400c07190f030801c401c0c080030800030340c440e00c24900a40 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 537543821 1250 537542571 537542597
    0x3061e16030912030c0e0d0825050a0827012015040c03020a061d0d03050f0a0c0b132001030207050a0c080105010909050327030d080402100306060f 65
    0xc02400307541c0000e0461840c0f1283c00345041d0300b50b40401d140400a40c5c07441d0302c80310910b041c040d086c000c0240c010962103003089011002c0b00701043c50603200078030408034203500b48240c80309854040841020b440c1c070f1000296491203015055030300c2106e0307040b545450312900301500001e8000c003035941319403881d5144903051206031002440060304047d0005900e42c1103081a003010410201240001c90054907440b4000c6041e47c02810780030b6060280c80c041c072007410781307290a221544040107012018004181b2020000d1740c0000e002e084200c1555540310700c8136590781440d2840260252440b03403c10f902c2c81c503d00108024002040c080380c1d03d2626203203c5400c00c0c3c0120000d11854a000d4001d00544164604004401172194121410b4900902c402e0741c0f00c1e458003040740d02c0494002d10545c810414480784d8002980c11880d000f810301d006000c4248080080303400c1500881c03842c0b0001c1ea02c18208400c40c078246c0344039080078006140c01c106007400c7c4600940480d2041c00041c2c24001c490300044 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 537545071 1250 537543821 537543827
    0x50f012406021b0f0a03050616030b031e070b1216080903180a120813081c0e03010f110406020601230d0c08030712030c030b0a0b09041b0e03061e16 65
    0x1310100501500304480c40e42e0301e08085454510503554410802c04040c0c0921141b4031a00a0b2155140014090000364800580300410040803441c01c00d0740f13000d00c54002900c0d100040c007800388038605802c2252145040d61841c5040d24980c400781c414081c0032002d20245c01c10010076110090450b0800320803424000001038020026544081b12009455001004000d0041c0281048110400d915070130740d0348452019803144080c0c0c20040d0403500c074840c14041c95200b40000c1441d40c402400021314492000742010940381c0d0f0889040017890001410069141c1c100081801080702d2900040c0d424078002e0350703003000504043d1043c45001070403c258184418960100004d01030a0101c035520001031620034108a003100500011a20700041c140300d45000380154046600e000349414081401c1c03261858070382d00a0110550081e03603030000340150b00e030310075007404014101d40c40d6103000741c402a080520b03240c40108440060b0b00f82e08407080490712000400c1e070f00180c040819201c00642d2408c12 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 537546321 1250 537545071 537545089
    0x201063203060c1b190b041b06020c0a060201060302091b0c19020f010816030c0509060d06090c11060609070c0f06051b0a0e09040201020a050f012406021b 68
    0x100758035005802c28420240b2800b0014403414120000040c00301030804a56030f16440d403030302c07030a14581110710740200048104a58560113882082c03114440d20b00d1a13144001d002080d00440056802000e001c5410301c0c110407a20b000f0f040071720081c45142d0031540811031800c0040c00e601d481a88400310818000f4112007520f0002d402101100e61005540380321141c0d0341c0030311344180e008041101c003100d4103520440790340741b00300850800c0f18401000c0c02c9003207009200503c0c6620811105010300041643c8840051007100ca03180d4001c11042d0616a500f03003140c8902000a061280480741150940800328516500a0044848941d150f90780b01050303900c0404090018803c0e00c8850300b1400b003000940c0100d0042040c0c80301c81440510404042016109903003221001c41d202e180340d1078040c5400041c1c280e0292061050300d00729a10313035503028917007809400c601c0030594656510540c91032002d5100395841742440c60a46a161170a0340c041d44590030444240d00c0d243c00a940a40385403280412 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 537547571 1250 537546321 537546419
    0x1a16031d100c1e0903060b1002030a0c03090510080a0b0f01090608041a0a020d050a020c070909082206140403110d1a011202030c030303040c060c0507030804061e020106 74
    0x102a01d0100c3c949002000140c190104491052030240c018205091107607900d0707410911a001140340c24000d41c415208401241011010000d4009003c076903911498050041c20595813100000d5040070820700042d02c0407aa0024010841070b0203282c0243c0c1e2010f0164200ea0490a1a040c286c03039904041c00314424085109101401c0d002c2880852800355008100100e060030b410403683c0c03a003402c404242c1c0314050007403240d40e2045201f40f0410a950b4800580107120755405482c245201500c1034103030004e00d007410656a2491420050030f40c000220651401100d503c262800b070031592109050840c1851480c0500456000b140030002c0c1c201d200f81500000a042091540c1c3d1441c1c0d0718510315240100b24042d02170005900750742c6c01c0000c2645e0143d980300300b4810a00e0b040c12030032901c9200b030f110b054034240704a001c0080458500d0008001400c0c5517543c0c440740c81390076802d005400c0003820b501c81c21a0301d0a0002c118449905450310391400e84144082c1400c000541903840788012001c0c = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 537548821 1250 537547571 537547607
    0x30306080601060c03080603060708150604091503020a0602060c0a0318060e0616170f0402010c0c14120d09051302070203101a03030c10091a16031d100c 67
    0x45043e94020307100700400c0744281e0b01d14101d690350605154403401c00303481c85404124540c0c0424000c0b140c410102501c000081d007060f040c00d07511401042131310000c0324020f802e0411800f0900035800c207410100301602c2c0c01d000829082c2040b055507626481900b1443c01010760386d842d801503407c081140100c0d483c0d08081c0510000a010342d205d40c944806852146030207818104c2c0700b60780740c080c4200110030780340300380307028080d54501c400030301040d60040081381045802d00c500c60000e19260020300280c00c032860380400344c41d80c1009000c000e80c04d0b40740b01c40d403507803141c00010401c0342d00032610020f4a42c161540f203105c03100407142401a00176100025454011030000c03038400e04540e0f0094014101030050804610b01000a146c0c0324810541b0b40003240c0c00205c0a5543c2030016041a259a0b216010f0180385131030300c800c0f50320110341c19122550380c4044e5139a408003859040c011094000d00b0b40b10440f00d422a1407400c107946030022043c40728540d8a034801188000c0c0124260381100c82c06075 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 537550071 1250 537548821 537548833
    0xd030c110d050f100501060903050a0602130e01030b09010b0915041a06040b22030203060a110f0307020303090c01111f020c15040c0b0a0c20030714030105130f020d03030608 76
    0x5802c003034a1300032048540f515607161000006281d44140c40f4501200d4202025000c0e1146546920b4041d5010b50344200310518100000112003501c030342e815008601603c1c40c1f0300d090801e0b01030a400d40d240b1050282c401c402490920100742c841c500207000c25032003101c000a0841c11100041c1008031019881e81d84000d000c100003030100a03910040420b11800f600e00d180920589107240c800344000d010207500340d4412000111003200a0b032100c01202002e01e8158100580600d9486a55104848503030040e0000710501000b00000c0000c03100c044024200210b0500c0311402ea996250031040d65510902440e003120500102c1641c100e91712600540140d03030902c0c841e0740100d208030f401036600702c80207400e110000039002111002d03100c1c113810b25682d1601c00340030350701d039400da0480401d2036400c035031001030185c1c1955034200000d900610021001145524440d03040600315003004200c00813144a25040c6400121f608031003495055045990400421281c20110300a042941000450307200e08 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 537551321 1250 537550071 537550093
    0x30601080a0f0e01181103031e0d0605060d06180b1e01031103010906051c080406050f0c011b090509010b04061404080714151911012c0106050d030c110d05 68
    0x140c11840354413405900070840500c207010030305640e445902ca92111103d03e0928126200d00c6d20340003800d0482b850900821002d03110703000107810b81d100d082485d00c007698855003000304000041c09111540c00209040000656400100d0058074815078401d0706204014a490b90316030007680265112514001d01d9a00d03581c5404000d40280014040d40d4480c891a0000090480f169a5440861036000440c0ca00b000c1c074094054410390404081c402841c0003e0207840c0c0c2e46103003440760410313544011460300b104550340040a007010724290011800740303020300014885074540c0b50440e000c03929149001e028a0a0a0b40c1c04070b2940125003002c070380c034043c4040003c3c800c8030302490048000300488107134816112001c00f1180a1148081c1c006a03185409440c00e08240030304e042c40e940032081c900100d07441700c40b819400d04a2a00380c2c224801c0c43c000085031144440c00348590009860250346000110300c90f5140685221912140200f050492034135411444e11050301e480c00c013640c0002140c2a0000d0 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 537552571 1250 537551321 537551351
    0x9140f150d0216060b181003020907110a0308060a050409030905060714060405100f060311090903040b121006170f090a060203040b07080603010507050f071a1e0606030601080a0f0e01 80
    0x205008a4400d60054408450784c40c00c0c10180f1f8010440030004807803c520f55824482840c100408090a02c8480d60020701c02280612612581c14402c2e07a43d8400d5241070130030070001d1110740e000725001d81d2078500c0b408000783d040300f90201998421907040343c0352080c03442d0a030031404d199070b60203007240611402e01040050028265405aa00c00014890042c41c42c0d40c01d01103802c0c61201a0811101d5413030302405041040c07140360081084030681e450203488844140c0c903948049403520202c40414200003604c0c040b4030300100640303e2407411440300e50541e00045000b150103030031010511884804203508032401c1107102c440e298411003d5440c0e2a042c1000c1100a004480c00c0740072642c610300060312850306101d07180c42141d05458080c10040c080c0c02d0801e840c1c10400741103402100868a42c6541d440101519105003443d0044145c8000c0c414500c0625003800340815020305411720501889a81022003582c0c0001082d4001032100c400380c4403130000d4010464001e2455117001d4514008101c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 537553821 1250 537552571 537552581
    0x20706050d0e1c1b020901090b030109120f08060a031119090908120f1b0c070e090610081b060c01090b0a1a03120a051b030a09140f150d021606 63
    0x303050b0319100c0644d50440311081c560030b44140001d51142c0040300600c80008150310020a540d4003600005100c1c1150303641c602c0d45216803030960080361000003201c04860740f121301241d200030f09071f07644403200c0c2c6541c1e07a50700c03015103045401d031185030305004942c0000c9510ba0200c000780158482440207200c41d041000a980c00305828582c141c04690004041100d85068980100030582402903000e0301506021a1500601c05644241c01011000503a281113a001140603280c1c00c1c000e880941000424010414902d40c400401074101c007010040458602010211440c0300303030b900c4c40d96400581728040c0145a5120010580000b04007884424401548040c4d03111552a002060600a030020140e442405140c0605605020004041d000b4030600182c842c141607144140014955052041e0540d0030066042c0005509044200400705807800c02c4003a980c808c0e2044500c1d96403c4010540d008009601d1801c071260000d01205a854503504461020a40b038451540d128030520740440586 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 537555071 1250 537553821 537553873
    0xc15050118020909060919020c0601081e12030a0f0c0e0a0b0906160611070f02101d01030e0309060f071208010f03111f0503040b070f020706050d0e 65
    0x800740c60054484648030b01c2194484040148071581c07507075034002080402c1200802800c1040c00549400b036001d4030500140c041d07000040081c01c0d2030b44c1008030440c070300180d0724542040412007000c5521021001308800c0708a183c2c191420340d0380d6585454072400342002c00c9100e00c3c06450100074191150340403205813018802100e1350b4000b2580e0713a2200c600381c081d00007103650140c8100300f410503010606000d901e080b4480d80001c00c2c05c0c14200100394040c3c01400342554241841c07090682107241586540101160b07606220660740c048803a1000712990b500559414599101c03403c050018082095680e140e0340100300564a500164460300c854000000481c2c103043c4449980b4060f5005540090503030350110311a1043d00d20b15214070841c0002a415a60043c5000e01075004880d407400c0090b1104210f6183c0310740e0b9007400c0c5801629108000e10b550100000039031107c04289d800300d02902191100c1c40c0064603642c01314900301c0105500213034588544580c6401d05006140d01c500c800d034074 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 537556321 1250 537555071 537555089
    0x3052107030e070603051e1906030b0a050c0315100e040c0512010803090f1309020d06020403020f04060503100e071203020717030418090305160602090a08031305100c150501 76
    0xf242d601c403400c0c0c0546009640412040381040f10030018a00f80074003580d030010710b95000080300341074204150100c3e079a6400031748070841c5200c10030810740f0103401816004210a00091b14600d410f0710401040da401c2030302c2610403850700c040c50240c03920075415516052002001040300551a5002a01c5c1d507024286284500c01c0800001130018408419200100e2001e80344d1241c10700744104121040c41c0000741c0d102410303a80d911132409a15081d0340b00806510460340180d841d070a6004210565140c0c01c1024412400c0060520032918085059000140012000300321502c0b00c8058a040511a1b0400d403040d000e80050a010b040e400585041160702e451560b0100c6e08210414503101d104034000c20707400e440c0030100e2000f000c009500c0010003500130f00d02903081c51a5510400105070078894155861038010403c04c1086c40c0880c00c110007001d161000754034111400100002410151044904c500303c5001c00002c1d941c016581c20058940c000c45a982c0c541c0d4440e100001020280540708038 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 537557571 1250 537556321 537556333
    0x40f090207032037032d03060302040b061801050d0207140307020405181c0e1f030b0105070b0408090d02150403060c170f06031608010905151303052107030e 69
    0x60b02d44c089000f40d40e034a07881c4070203202c4800ca44043d01c3c0f10203c8240c50301000c01d0503841c1510710340340c43ca202c5c6843e01c003980c02107096443d500411007600e8920b000c061003100104114502c106004911002031042030a0445d221005000c0401c0207000c2c0b1103006d8507410f088622925480302c044010b0000314807c40c0c00b00010f481c1c8140d0049074019001700010310b544502c2c1e07241c2001c0080c0008050641e00b074a0028160340507200461003a01f05048400c0e48007107012075543c884c1e0b4040c050601815001c2ca051401c242c0d0035280d24886490240c0b000e031800e84e001070b4501e80b07500c440000d001c0741074001d00304100502080707103000c0e10340c0e202c1e100c00e688591519880d0701d0f0b1240304141d5110681504c42030f0156603201c41400311000b01000d80b05643c9486012101e0000d149040000c0d0010541c103000001d140c1c295003009030505035144500c4d4079401d0007904200000104020403003d803500b505d8215250210f5040441401d100070319000b84424002d001c0118940d4560801a0044061025682 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 537558821 1250 537557571 537557623
    0xa060807061407050c180403171612021e07050f010501150315030507090f0609020f04030f0813030c15020109031b1106030f100803040f0902070320 65
    0x28a4561034001c40000440c000445400d030030090001d4440c6a000b0801d485400e4404c100081c0c00000e030a11040d00b80b24180300f08024980c10001403060000100d4040440d40340a0325a071014881070f03000300003070204816244140050b540d050b10500070742e114800c82442a00c82d210038080e0032209007254107206100c00d40500394818050715040f50030340d05171000358015008081d0058684c201d580d0b002c0268081e070002c04142c041020704010007100310b0000f41020040c000f20203035011608031414560040100000c0c558840040780d040365001201d880041c0201d00d07000c0103512074441810003002c98000c000c0107104059074005c04560118080c043c141c001031034164240d42c4081030141c045004c4c00c04403000c0c012409119a5801c2c07081a501d500202d03d5000240f842d042034400b00040d1000c20100003203071182c0c001074006400240015814140f80c2252150619000e0081b681402e8010441c202003500034034039404100c0c401ca170341c4c804d820042501260382d003000382d41c041c015103070700d1041c44 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 537560071 1250 537558821 537558823
    0xe01180516030203070504050a0b030d0509030114010f030605040302030c01060941062403091501030f06020d0209040c0e0109121505130b040b040c0b12060906060f0c060a0608 77
    0x602102d5014018001079482d0030100030040c03000500f0b1103274994440c45c01c3c0c02650350510113210b2204e001c1e2600303034075102028181801c50700c011301d51002512a5600500c1010035020640044992020002c2441c0c0c0d25850120b0842c05540d018088c15030800c0004216442d0b1030704201e81122103800060038118480b60b04040c80e00559603008904c2c00c00501c0719100c4d000443c640c84d840200903242d45038521440b02c449684000f07669111007040804005e0040081c8140841c1201401a10194015505540b16900280d003001d41c0145110390001321228242400e4066801c0c0700c00080081101c00b440c0c00f80900749107a069031442c005000c4400100d0000c0c1d200207201042500304811000800380884200010040509101074000031100744500290100001c144981d2190034002054189031620035003414a5411152a011090102c0010304110038200c0e948981d0890b00c1d47c699494150100d180c5208100d0700800d0f402c00010131000300340000030031034015025101c1c204402652a00f02c0c0e = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 537561321 1250 537560071 537560113
    0xd030c17040b1608041a0d05090607170a15080607020c030d090512070f08030a111504031b05060108030a270b0d1b0c11010c0c05130e011805 62
    0x4505004401c0c00854440c00d490b81da401c060300d04c215152841c040d265200c1d078403101101c180c1c400c0d407045e00241164900956004413608000741034004c001e9418012400b4202d140c2985a411242060500003210145c0c0b940206200c2c803504143c000070a920340d0510358a40d034003181c0b800007611a9002984a50800141c54282c0b107000d6601e2121072420042000b208090386500c2c14228495902c001ca0340610310309080d0000c2500b200107694500f0007640103429102403d0180d4000c1d00601c0010000c0c01d52030420b0b0b41e00503418544000b5207000310351009856803140310041e1241c81800004601124000014120200d0341d88406140d0411058051480d01131014144858800060200700020244014010240441401040b51003060b12440c400e007100140f8640014240780700481130150340b003a86c42c122542841c009140c07003c241c0301c504000d4518403505015540000a8181c0055039a0100340b4080b1000b0082c02080042019042182c41d4a141a240380c0148904d491041c1c1050f409 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 537562571 1250 537561321 537561329
    0x10507081504090c050a0b1e1615020d050c0c010b06040b0d1d1207061103100312020c1306060801050303030f1303030603021003050106031b0e0906010c020d030c1704 73
    0x340d200d12039820000e11020f006081c40880d80e03e0044800494590b0300c00409034080d081428105407102003581c814600d41d40c49108000d4401400c0020340301e02840340e050884050b8110000c01d081100d42c542c1ca4009104d95042c0305002c616001c2440b1000103440010304000000d00c00a00c00d5400e01d10070492a481288107000a841c02005080c401400c550815448031442d006400d100e00d0503040d001d41000304c0e9403011a400903000072040b04008135841840742090182c1441421032070000f00791140368200d400050b00d940c0810a04041c2140300300001c0800142c090b10040c1e42041c20044400901482d0260300b0104130240004661030900009903480b13600c2c0301d40211440c1d240d10030300d01405085140180c08140d25103d0100143c0c551a031072070401a059030300080ca9615001c0018201d900d810001d01c5809041d101d840c652a5001c14541c400d0642190110a207496030001078800e6900854000e40001000420009164200c801640c16034002d10b0706280081341410f04044911841c05 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 537563821 1250 537562571 537562591
    0x7050a120b0301060f060f1706032113030524190e120a050a020d1b0b06040603020307080d030510060801120c080610030611040617040602090d0305070501050708 71
    0x42060555003907400488580c40301500010b6016168005040e100500c0c0d004000800c3c0341802c410070031075225200d00c02100440c03001e0251820f0900c000b9890b03088000903807444014a0a00d00550f50341c0004840300100040300e221509592480d010392a052118038201e4040740320208034084006403204140f103004420000e908211900c035061009140a011001c402c0c4035458402e086215014001c10b40011139456881e183d840e0b14200915202c0242d0100b410070540b20300001c661922042c02d881d10591181c07202a06a444102140050080c0d62000c2d603d44964072000490a45c0440c0141a01c0e005a60500c00ca5803035644000ca1615944209000155000d0040010441d00080c400180d4420100001c03955618080c0034074000c0c0a8811030454a806082081040100e1107100d0010251407880c40c03d0a1926074040d1403a20641c10480103000103000207001c00616034112051058000c1804603a2500b5040060103900211001c407007540c6080c001c148002d028900c2648180a418 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 537565071 1250 537563821 537563837
    0x705031209011e090305031810020c100f030b0402042c1005010825020105060f03011a010c02150708070303110c0a021002150f0901051e130c1e05040507050a 69
    0x1440c000064010f82900c2d004001c060040840040d40a01c0100100f0b940b82c40c207800c20201c0b400c200824000381c04850300075540018600d071026294804115007089190500440d00551038000303501410040002c0c42e030041c400100072071b00400b1039140c00c40380c074544403c0d1689207441c0c4051010104068620507030421184004101030361103075005503800b13480145584049055607848a032442d401d10052001741c2d441c0c0c010412641021820104982800c0f00240014506008242ca04881c0344080c1810410b5003003d00007035468007120004802c410070703152a50b54100703048c006c9558001140450000b41000311307101d0117084040581380e007021a00c2c0a410680d2081c0c1c200007035140c8034185c48040d4002e61880804903c0d80701800d44c4280042e1550704014a0507130406800c55000600c01c505149008665074060240883d090b544602c0c0c03d0200103d0140608000201d4038166100e030b80c0e070f510300d4012401c1c408203200d0004105c90041d1002e112035100e9180a4940b401902c0041d000a525a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 537566321 1250 537565071 537565097
    0x2006040b041401020604151a041514030c01080a0504050f0609010b01090b390d09030b06040510211e031101180308100b21072607021e070503120901 65
    0x1b80c1d000c4078230812140c00c2030b0609581200072505031550440c5103203409015200c2006001c140513400041010f046016103c00340d021b50010741241e2000d0107440ca81035071000010104001040019100c03803641049440d40c2ca01070303030345a02800110100c0f03400a602c84900007500000034095415447e031a580c09500c08112030741d04000180e0580c92040d980da61f08129a505020900250301680c000f552100c840604500b4106081b110203400c960155140c00c00f00101030600001d0201654035409000c2c84036201906102c8610452000107881d66103a1500d003801000c0c1d40f2745a0544030b2103500e80c072040781c10b14851682211810744000b0010708091010300d001078498074240d40d10403d08242c14940c50307220f03141e0f508ca40c1c01c10a1041d10f82090114101c84900d410009950b21503080e14144599501500b180b0a003110002c0e40030b89400035001c0400d070094001d0104664401e032000448000c0001450003d80c1c620541c0b09050103030003500b6808031507683c54001c07110740780010b0712455041c2c100 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 537567571 1250 537566321 537566363
    0x101a0301050607240f0603020901050f0604031403121302090a09050d031e060303080402130204050117040807020415062c0f0118060c1406040f2006040b041401020604 73
    0x1301c0e20031025038107090604141100d4a2203040c840b01c0e140800050080c0c01d51051004041d0107800983c0704000e0303070080c41c1ca1990717130804842c180c9910090008000880d10400791541c06081c40c208094a00002081a070600304010400894022585d480807a01e44503064002c640d9141400f5105c0d030000344003c8040d50013034011041d2000c1d9200200e10341062070181504039912900110001a80310041c402546045400003017003141b1028110725203403500002a02009034130901412070780c044000502405011400c0c0c17080e07150050814014440400d48100030741c29a4060b400100b680134584030001c0405801d456480e01101514001d054618010000030320000c0d035030b5504110b880c5044002c251040c0500c54002e00c82d40e2118551240c0518200301101075150407000c407580800308000c08620001c05480704d498211580044051080400348000101c10f00c2e09a00050300040000d060300b0603a0050080324070034039081c50941c1c102401241c5400d4203076170181c1799040034007030b91080c450 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 537568821 1250 537567571 537567593
    0x70305190e0309061b01110c060a0f0b040c0305160315050f0a080f070609050d0201020a060b060d020c0a0605100302150a03060513020d0e030a0c0f050312101a0301050607 75
    0xc41c60201c030b00b400300100006050754055002c10122000a03001403181c3c10090080340a02920000c2c8a414100e4010806c0d07501c00c0002c203055840758451200311b20f007422581c003141c1c070b49001400501603800800c00240c050035090b40c4080c9a44a042036088156200b0321410b80204040c51008850a1414040145022580d031410354040c104031000201404c0410000032040b80c0800600350303e91811901a104615603803100340201c4802c000e07800180e90204060103115405030001441142c5500811085d000b203031910a1000d10009485d08403450010380000c800740b0400c1c041c4001d95406144540b102407a01c0001d400000e06a540c0c241003c9000140001503003500c2c00140b11580e61000407403100b601c1400d5443c150f4006802c440c0d00c6024001d40b0481c1c2000001980b8180c2a201c00415003500d119015105060034581d000030404140122000600c01c240f107501141414200c011411550b440350018079400c0e8070383c05014084840685e41210402072800781019880c2e203407841c41d04 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 537570071 1250 537568821 537568841
    0x7141804020f2d090106050405040207030915020a20030a020105030702010b04050f06011d01050906090604030b0a020c0f01050c0a08042910061b140a0b0a090b07030519 74
    0x7840034482100d0a8488038000400c61030114211070011007030f0203c031604801d0701c11042d400b81503c18018001e240d008003c40d0101c5005a900607a20100ea06007110026540d0300003010441c11145a50001c1c0e50000341d089a4600a90aa016a40000922801c024001c2030902e41540220340c0c484059030003003020355486030250001003541170030900041d04030303a0101c402c00002102c0c101801a0395902008001c14030030740b07803821182c0d40c0b45400003034024041e0b1001036104500028403c0e461741c0300c1783c06940c01558009801c0c1c400e0b080090010f1b000c1c3d040050351304c20504c00c003007032102e03808814003505004440420400c3d1030300c4560f500450340b1040042050300e0102c0c821400e000c9030b291592400b1013154151882190500780b134004582a080243c0c8100108070074000c1001c02d205030441103081160703000c8528650135500702441810700e082c0362405411056020300304800021185c100d00700f403502c00c900d410400d42c0c0c0c1c0d4030181d0841d001555106649a503400481301900300c01d40c0103081c05 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 537571321 1250 537570071 537570079
    0xc0a0201052107020106031a041709040f1803110d1403060d0f06050702100603050c060a090e07020102070614130210050405030d0e0a0b0c1f1509090201020714180402 73
    0x142080c8200c2030b2000d0020344071030300181e668140400900a61803581800010420440f040d1030401d5102c103520701d0b070b90070000c40c200000041d00044581d15030340290303071112a0403810b003c011018600103004100e001420740c04a0718945000c4240032011a01408810760ba0f03c0300501e100b0812903244054000410307060b04003501c51407080219240010030300003503205d000003050794070701480000e0804000c91100e081e8541009824000034101065100c04080103480c1c040c0c69003800881210005460307440b05009000140911801681c190001d0072564000c14003801111211025a41c045508480c0540244106231004005150041c402181200c10341740403401c1513100e100090401d035607031081034003040859001000f2800c0002a0314007c1400001d400d0030001c00308030040e241c00e0b0b00b1203821280c0900d48403915056011394007074610041000c0d130b2000d001351601149402003482d403038168003507c00c92000040d112210f00c10380c03180c8840945282400703071212483c00c43d403a5000c0d00c200d80c0 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 537572571 1250 537571321 537571357
    0xb07030306050d20040203010609090504060b0910080105070503070c230d05040e10120206030403110703030306060201050907050a05060f0d020f0702011706010c030e1207030b0703060b0c0a020105 86
    0x1964482c0f41200c2040d00400900305859412850001c1c030f0710440802d0380c000c1d8014401005002c6c0c014101e00103c4a0f8502c0200c2e0382d41d40d5203429002010308000099100e10440140003104900c18501000c0d603d00c8802000582c90340c1d02e0542e050300044514100113019000d20310000b9112150301100c10751401640680b40303440344505800c0c03001d90008400010320214080280e50f01303600d05182c0001c00f80e500d4103e0a42096403500c0310030b80ca5840a07004810000200f4200351254000354000080d100c2554201c40e102d1030010041c002c5449840c4c010741c240000700e000c030180031440c40c084810040c08411420f1403c0c06000040d00810842d0001002c14040c42403420b01d10300044c481f0b2b0a07009a02682c4200501c005000000800c0c0c421002c0c0701c10f0002c103d00c0c0e0340c20034815240e00e134242c14012a021355030000100e04c203080c52240300190041c94000000c200b18040e0981c001d0800703032420b11400fa1500c80d0500325010311005410b41d58425a032090165000e00010121801c1f80036011301 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 537573821 1250 537572571 537572579
    0xd0c050a05060a0b0f010504030c030b181207150c0f2a050a0203060903040303050f071401230105033007081209010b01080405060423150417070b010b07030306 70
    0x81030110840c3d14000c0c158440b0140403103032030a40707200c20400b0000d080c95800d281c01c64991600d4108640401440401c031030300410f17042d6011041c4011807a01c2c0700101c0301c20b1103a00310400c80b903402c081d1040701d06051444064052140c1030080c0101181e8940c1d40c15180d8151040482d0340d4401d0034802c4401d640410700e603075a070500401ca04044c02c0e006d4402080100310500c14146041002061590503800501c000d000007a405800c9400040c004070259444070030b83d0900302200680c0a101403000d40c600960300c0c048a0000c0f5503184c4da8500d800c8481d0702c0b0381c0c2c0c501c00d042d110400020004ca801d50301042c3c140035a02c20074000e04060b40846c14090601c141747c0d441d0006544481c2500b031840e0b08200c01c00043e11002d01551007680820b107000c010300e08280d92900e0b580c03200075100620203c07440c0040c110f85280090704040054000003124560010200b02000d03405c0c00f41e030b00755060012856403844150750b00d01101c040035440020052140e10b40002501c25801c0201c046040503100c0394001 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 537575071 1250 537573821 537573823
    0x417040503010905030712170a0207024c120e15090f1b0a091e0216030219020603060114220905060d02131a06040b0a08070804050d0c050a05 62
    0xe20180c89071004641c0d92801f42070540348070786010342e12800c00c100b001b1035800f0468a082c10903040a003281016886401d1031000400130701822080d084940b0440850002c03400300031030240d03003558050b02003030b058110000614041c02e07668403641020603030841403203180040341e6000c4101001100c080e6085610f520000750360031310041d02d400c125540540308849030003500b8410156114002e500304616407403080041502240c0318440c04580390390325031a1a08030703541d0101071020319500410866403410380e0040005030f10055201580180300740da10202c2e066903007461901e24107800918190856641400440d42c028107c100351401c8a024443c400c4103034400b400b0540030b003140074051100a4103116040003110700007003042d4402d26241040c038001d43c0340c407100300841c407941050100756042c00c0610b0305031454000301c5a640258001a0008403281c0b14005030098400c15503c1c038031b4607201c0c241704850709503007540c003d03005400c0861400c241070300583c5d500e0816407050050310502031540e103c0ca = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 537576321 1250 537575071 537575081
    0x130c0305061f060e03060403050a12090c06020705090609040b09033f1003060b0a08070b030402010201110f1912021306111f020708090901080a0b06090609041704050301 74
    0x103502e040e090910251504034400e44290040c125519011200900340000607589140c05807019044c0240000c7c004003007403080780c140c1c3c10300c01560170074805840540b810841c180e1861203014010f0060110204513898007190031800303000014804802c40d12240c070b6411302c445000c1c001126030320041200034507901e4021b00da4101c0c020b942c5100c082602e4180c0e0540603a103e1040c0c0c0c0c040c1c20a12a0821104859002c030010680703400c4030002410054150100e41200c0c5680c2255100307201e1810001000314003880150b1083e4800e1b4002c1c420610841d04850b5580240079448900072003c0c003600c140c1c6441c0500240340529a4580b10f140c1c000341c40d000b48201c1e4010035841a0740221100f05000c05031300520010340a05d0384400500019141150004c401d00300c42c41c406c403c650300061124188180c6005440813858014150303512542d442c29116034914503910708803659044800003641d00c1c44c252035550320802010344000074035030b22076640595544444101d001c00c501c0520000c07415840074450 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 537577571 1250 537576321 537576331
    0x204120615230306070f020d0e0a0b0d051f030f0f02010c020d060504020301140c040e2706312303040f0905060901151b06050703020d0e07080303130c030506 69
    0x54401d103000982e09150404c41c00501c08402e0102031100103c2071680003820800e40303070082c5400d01c00c00840a000840110f0349521507160080049060030054180340d0003607000344040301048004503000e5030b800321000c20900c0040c0502045400440100700d01040007184140305151411641c5402d500240070300d587d22a083d251141e5a00802046040c01d21a480744c100544d5001c5840380b8085001c0c50042c403950240b000e072102e4807408182504c1078100350b042184003008400f480c14094280041d5a007504543c45000100c494a040031042c070004121840600d42a103c075091001c0c1d502e40c032560091030360140c03200303000d81089801042405c0c00a0b0003d40313401e42e110300c40c05d0300c0e140002041d00c1003d41103d00c038607500c83c0100042c400070b006d0103800e4070035814001403003590340a503400703d2805000702810301410f1008120308244c0c140d0040c51540141c91307080183d003060311702565603070413140030707102e025842003021881c5400230a0000c04018400c40c0003444d1a51240e488d40d0038201d003a14 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 537578821 1250 537577571 537577619
    0x50a2f010e0c0a150e030d05030609010e0106120506031e1c0e0604141302040603540501111315020d0302031005180402090a0204120615 60
    0x40421102142030050116680146004040c0e000d5100001070303000d2a07501c00c501d1541c0c04140c010400c07601690080003c600000c041e902e9031781c4840e001904a51045481da40f0900d000c0c000881c242e51425190741c141e60041e80e42500c5103074001c0180c00104406002030307901d441007144054a04c2e0178000c4030340c44c0406040140c02c15858400c4001803003040000d0b02028014104102d0000e51a50030569003110400544020900d001c0e0300814503072440400000921070000501007061901500a428020740280b510801c91a445022001c48981e000d15942c045040141c0341d5482d03080f00d0060700d6400594007900c680d10307103195107160840e41c0d241c440c800d00e4031001c10051401102000010014014200032007071a200400300251183d280d005414289540440401e8224001190744009040003074101d58510800300c550500b4000100d034205d00ca080c502c00061300221060003510f0843c0e00240103200869200e6030b41da80a04100351445656040003180010589a00c0a0100602445003 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 537580071 1250 537578821 537578897
    0x9011103210105010e1c0c03080d05100501030921020309030d1d0f0a03060203070905090f0603010e0d0905060702120111040305070503010908180a050307150201150509040201050a 79
    0x1440e141007001059000301d042c003041c1040c281c65a2112420b201003000100c11200304151315150402c9548010341015255410114000d01540f0341c6034452801255041c0783c1501181d50760300114180e07014510002d22201900145507948c6581100101c0b20060f01d00659080440c00c0010902c1c0010f00182c0b10002003e0a9042c0703041841c8501d5003054007010b40c1c04204001d5000b0204140c14503d1100800c11640000014041031003048100003505008000a05a09028003038000700b0005590300e5200c0d51034215800701018000902e01c08001264032801103440c600b804100c40c580140006a070410296496035a41810a10618040000f000702890f203803811410241e140004070723000b00d4001c1e0314244003400031a9400c01900e140111020b10010101c00030008136051510342d034401a018130640c2e00205071030608404002445075103500800440114032000444801d06100b05500541c0440204004d07500c288020481103c0c5c506055031f504008120b00900d2200c62040c800d22500d0380 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 537581321 1250 537580071 537580117
    0x150c0b1e071718210405100e100801052101150602010905061303020319030902030d020106090b18010501080c070c080307030f0305060f190305061f0608040506070509011103 76
    0xc0302e8031541200020681242c02c4120401655035000c000c0300e6090020190780400514882a40840d4060600900025a0300c7c030882c4001d0551501d0707801c814030079011440141c403241e120f406443c0c1280c800400c2c2c9000f60448000c2da0400640707507540d404440d500e454020064800c9405100c0042034141e0001841c4c02031400d210b810100041e0484a44000780c00d103601c040b070340c00415030b07004030070340380070600a8035003aa82135004100501000b17405010b08480c4009a0340c041d8011012520300c65800d000d0080054100301c00010008200203607114098014042c9512031090180d1290155010f14030304109602c1d0800c2c54041540152525400082c00104140c2e02c82e0400c1c88054103400e091002d801c3c034070005403a04480b416818040c8001d51080050b940221000350010740c0c2050031747e50175040c4010a8099a9515003215040440020700005d0092165000501c120b030050050416521101c000700c84d5981329921450410130740d0810f90b04100c5c4207100410340350350340541a01c4c0c99044 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 537582571 1250 537581321 537581357
    0x40f020f01051215010507050a0506060f0402040f0b07110a0b09030d03050f15270103140705130e01110a02030a030e010b130e100204120309150c0b1e07 67
    0xc05206040003010311180c1040c003002c1c00318581081a07048560b085041d500012030f0030340509203000c1c00b54881d41c0c09840501c140820543e000c0c01d07081d0768031030801c10b106c014081640710303500c00c1c150344840e0034104004203109040644141c9100c0c40e070a00c5000d45c50400550707180749903040121745440c00144d1849901c0d0820544150a0700c03030400b800756141482a8151400340203001800d85214403042450a41d2074000054005103800c0c54071080c20807421840c00c090109010032100403104000d00140440000f03103030b004541c001440c0501c1ea21011082d10060100c2c080362020039901c851030803a044144002130000100d450780103685511925000a099070302d01f6445101c0369151a010913056150841c040d943c0c10352f0704078007042000d0892006071602c0d40c1d1903000c20000d880410b000c1400c001e02d03014002181d000380d032801c0f050303600e680030003040d80c4400300c0400116001e82c004d000010f1568500581c03141c0100e00703807200f000070f03d900244070400403a02500025402e010801c0d450003 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 537583821 1250 537582571 537582589
    0x80f030a080604091e030e04050a06060e06030103050601060c210305040204140408030a020c07080607020d09090506060414010e0a0603061502030f12131707110f0a05130212040f02 79
    0x403c0320140000e0003641c4510210380d40c800e0070524114420402c0e807044c103008400c0b0040b8090054020007880c6810b41c03003070700208500d005400c002908004002220724040b011b59041e02e800c600589200d900c0e1140c250f0744810104000c80748041d04149842070080d4520884490704925140803e03545400c0c4100001c9500380403440d0302481c50b60f424000410b80b2401aa40d1020305d40308010303034071821000c0442c03500119501c501e601e441200c04201d0100e90102c0e01d10303200034071511a18955511141c0d000709441045070101d8010000380420040100c980038403070200703031041c1070508501070040701003481c00072030b900020046900c50004100d841e080100c40340c0b074810303203102450401e0503924410081703206101d011080c0c0744158000c103800540f0f101c0020324240c0c0c804050700f0985d01c15083d107030b415003180758107403100e010320280c6018a0900d800b0090303880c4401010400c40c1030400c0e0130483c00400b480001003200703038203214907225000da04200c98055801161282000402c5204000c101c0c0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 537585071 1250 537583821 537583831
    0x803060f010f09060f0908031b060612061315020d1b0516081308030c0c180105012c0d0501020c10020708160302240601090b03091015080f030a08 64
    0x12050140241e0340f40d0080e400c0c030a44100d07152500f03080f4001c1a0032951100750b0b4000704081d02002503444800c0c800000c0d080600b100324400e03078020f991031000f00003800c080f00c0400036068000d03400195900d10005000c02c501c5200780d00840c0c802c000e500a031030803a04101c8500c1404e41d9150b0341e80300c0804200348203d012031100c1c034106182030070304600d103007100d104c04100604180000c18405104102054103402608100d022070303840c0c240c030050b81551540e80646490207012102c050340f60910319202c0e9a03050310810f854461148070178000041801404002c014040c0e0410b200000f12995603920140c000e6019000150b15010348561a03410b0948d0f80005c483c8003841007215030700145012007030704c00c1001050091211100a03042c05c2e030400010b1054903514544814920450b245080f01c80c44c00b49000f81ea03880c900c141c42b10000f424511050f144c41045900c811445260024203400044001002d0803112407442c3d6242090b0b45004840d03803c074034540c2c00104003031501030f601c00c2041c1c0c0d0003 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 537586321 1250 537585071 537585077
    0x3070c0c080d0e01030e0f010c0203271806281a0322030507120309050f01110d091a09060405060a0c0f3005220b0f0603070b070803060f01 61
    0x15902d1aa8060940440328903002d05242e121b8a440041c0c040510030b80110030340201c002e00420b0b03d1554001c3d03d0b41d00000d041030310552104413104509092640074000e041c00036103806290449400c00c0694007038000d0401e40c1c07108030420180d184602c4031950000701202800302403c0c050420b00882d18001081c0700d902d0543c03400b032040141150b000030301c1c0b6682c011401c541a021281d5810704954a00c20700c607002d8038080602c81c2d140d080b90340c59070001544e0390096040d0f0b007142980c0d155643c00d9515076041010144002d02a500f03035048194400b4a80302d11403245241e5004160620f01599001200d80701c480360820300070802408010311515601c080f80a40801c00e5144405028103050b80e15901803041010300b54a0340c3d0003080b070484100301c200812090078501c0d010340462802400007120910366a2000c0c840008009800313a5030f1218849d4045965042951450b0305851408001080d26606104820340081c081e0101d00040409a00580c02d4655a01e4074105002c0707007200c40201c3c5810 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 537587571 1250 537586321 537586333
    0x7060e0a0b0a180f0f0302070f12110907081b0418020a030518070608100915050a081504020d06060302150a08100513050702030c0d020f0c0402120a090204020d0203070c0c08 76
    0x1503030a01c1c040c140c1e91344022403140c1c500c17550404a1170012190040000925028008200c45d9028290740c01c01030320030a000c0d0b0903030070f034101808800c020540344000031481c0c82020811001220391a40d80b4030308030b101e5150a0554800b00c000c40e9040400c3d0b2000807039030025007504266814040d0700c0e841007a00086a0044150462043c1e4401c1184101030400c42e025012601480c4c240c003440c0f0080c01300c10800e0050101c1a24917041c041c0140c8510342c0326844070880011100d1b000324401d103480a2000c0c10582070340c0c4503002e1050b424101041129007980d2208080010b0391209558801481e41002050b20340308107540140000401500940d49401881002c12107075441d20f5105840d04000003010600b500d030341c0e8040e803441c05007803a02082c0703014515001c1d030003da000602c01000310f41002219509403419061100324452801d21680449540000600280c50340d0012541d140c40504014500080844001d0403a001510014001107044082d07400b84648c41c40a503024240c2c01c4013a0038 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 537588821 1250 537587571 537587573
    0xb01051201020424051303050f06010f05032802091305070e1501050c0a02220f02070c03081e0412060e0c09060d080405030304032f03070501030207060e0a0b0a18 71
    0x20304a0f84102e0a9070f5070079003213400101078401c0003502c0b010f1a91800c945030703884d103030701d070031a26400d00c00b10300000d82c07280b01c00000d080c50441300007a00305c031000342c050940040e910a0b424403840048452aa00c801c0f1000101c00688070402c805104111020002c80e00c03600da40b6055050403a0360b071214031420380882c20320110031a10201c0e01003401007401c4c1141d8071f2040031441400c024078600042c0d03100465034034000c0e80c114502c010f021b003000c0c2e143d020400003940920304c400300c0c060613101034402003026009000090707003200181080003408520f01d01400342e50300056625817041e008400419103d0740c2c0a410402d003070094980d01c00c490741c0a490b1030820171001c690054070052209100ea20030485590a00018100300c81c007800018042c0d0390b0703c9846e8148060074408401e8515080441c44101000d951805061040000300c01001350022514144c01180650049141a12080ea452002542100d810000f0000340c0344140d2211007907140200c03c8104643e62004500295500c00314188 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 537589928 1107 537588821 537588839
    0xd0513052e1218050d030228031406010c020d11060f0c03031522200c010605090705180904030519030506030c0607080d0f1104030b010512010204 64
    0x348045a00703100c8160500f402043d01900e160800c0c0415090301d8440d0700204032900042c089454201c410b480c00150340d0281d10522008603941d0b0181000d400c40f0078003040d91004017400c160800d40340c02d801081d400c00144100030070b02c0c80c5c03004030140b031030ba40c01055400120019401ca81c40d401240c00203680d9038000c2d54829820580003030b00901500d811080e108903122222111814250a0106407015041100c1d1655000030301e58000d0004500d04000f0344042c210010000c41d01514040502802c410003801403420002c1c2000b00b8242e0406000c0e2009681b80244c0c0c1001003550303182001c4801d80610040b18a1032103c2c440c1042c441c9a05030040c500641044003038410180c0341078104a018401d2500090000d0414000d03815007408a51218240140c100c6010a2488050804114a81c069001112034000c0500144024285000032842001e1840000c62405080a1441c = true := by decide +kernel

theorem cover : BRFrame.Cov 537410071 537589928 := by
  have h0 := BRFrame.cov_init 537410071
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 537410071 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 537410071 ≤ n) (h2 : n < 537589928) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
