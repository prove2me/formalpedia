-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5367
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T15:38:25.252166+00:00
-- url     : https://prove2.me/submissions/14dccb8c-2db0-4fa9-8b92-6e6a9b05b0d8

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 965107913 ≤ n < 965287769 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 965109163 1250 965107913 965107919
    0x2061c0501050a080a1b030803010e1f0501020d0c0204060b0d0204030b0c030f1314010e0309010e0a05030613030c2f010503060915041e0b18010b07030e120a0f0203010501 75
    0x50007000350784c3c80401074040c549413600e885034440c4001824019000c61108000040f801000c0914068010344900c85010306011500700013180c135031070701401c03241c012a900300301c142e800240c00c0500d00e40c10300303001e10039030440d0000030010a01ca40c0f01001074400003030f054103801d19503401041a82d110b61a18401c0707444162800d01c1c580021202c42e40015030460100f00603c1c0c5a080c00c4034028419040c0084c1103012103062801c4d039051062245a607880403c18020542e0050300c16118290b0a94250001c1032a00c400660342d5400a080705452640c0c14640005141c0720302402040710390020780c045a500304090106c0105d000000e8031140401001c2014181503100e03000310b03801104001c1024025455065004a030000d10035034060780b041e5100c004030011041542e490750212102c0c03c0003e0312410390b00502030450046000c0c08a11100c010050000c414502d0643e20016014035001f5215401180032921036030091405108a1003000032084c10003d00d5009540350910036030003030280f82d903 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 965110413 1250 965109163 965109169
    0x101e1b080a0f0f09050922050604060c1b11010302090618030115030807150b10030504020306090604030503010b090105040302040203090303040c17031c06050925050a050d09020a0302061c050105 85
    0x2c010706480002070441d83e000c00a52808190058100c030302c6e00450404814410500341f8102201c40e01210550001030410081c0181c40c4201c0d034401c2c403079041502c00b0400a81c030f0741d001c07003070340b100e005106a06070710035860164820350548410070800303419a9070310103880c1f07c0380c1004001440014030030360034115400c109003009102603044a600071112400d02c1026901c3d1560074a500e903c000c48280d4425501d01540d803400c80c1121040c4440d1800141420b05c0d0042c941803950042c1200850792084041c000061f500100300d0b0704603000d0130703022a00ca0201d100101e0702032084d076001075401400031040c00400300000c4001d600540c0f06012142440c1d980d03c02c1d15200c1d405241d2070f54a00d8001340510798208003030202c0503042c0398500c40002282c58840740042c502800c10b8400e0062444a00e4140c07800544100e41000602041d050145c2403018005000309280700d14802e00c004a600c6d200c1c840700b19161001c1c80d5002e144d00800d100d4a4040518103070b51300c01401414110450306220000403941 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 965111663 1250 965110413 965110427
    0x30e0c03063310030b011716030e0f0c091801021305090603010618020f0705010908070317100b160b07020609100207020a06030b06072f101e1b080a0f 66
    0xb5010300b81880240d4080d0040c0c3c01407043c41c400505001c0100e2040c600520b10f60f01051003041c60603c01da00b500302d00c1e01e0003011120201c0210326203500c8000c0e40e0541d404001a10385500100301e071001e0701542c0d921071022011f900c40c01515400c3d0700101343c03079003408000c4071130009840069400b03c2c01541c0d058101130917134425209000281c10808000d03040070312140c00421041081d90303010b51601f01c80e40c0d030345800c40e04c2c4440182c85032000441c00c00c08140d0301c000d24070003460300c14400e01540d081c042903400c03807901c69110b4500e0300c10001441d803183c03840d28020100b1164001c8802c0c02c5038601050041c0d11600d04584603200da0040c2c410208161180d40700b81c41c035041d0094243c00d516803d105041d0018107904088607403200b8107102e0100080c21031141a115020004009541c500d1501040401c00c501c0ba001d8a2150002100000881c1e5018100900701c104540341d84451484840c42a01c00c0d1480030804d04c5603001040901c1c2c02d1040c620b004000f208016581c0311610743e01117800301c07014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 965112913 1250 965111663 965111761
    0x501030c05031312020703140d03180b0c0a030905010c02150a0227030715030c200613030306080106121b0b0d022101090e0c04020a0e01030e0c0306 65
    0x2558000080b4400b05400340584c002c9252240110b03021140c032a140d002c0300e0b0040c1c0c000385416500403201c581100b81d0502a5100f00c0804241c01c188103412030b51603005280006000d1401c6100129070503242e01d109410580c0d2003500300b4020032030320480c200300a482d001c410180210b00a000404560254a2842160346a4080000d602c00001c80c0e00b02d401a0381c400d2461180d81445030010216007071040800304d0408101c00d850001d40101c0c0d40350041c00302c0101c0440540075660345001c2020703100d800301d1031550000c0c800e5100c1d41500314515080d0014000c54208801c0c0350310b000c0c808a41900512404c0032050701070320500058050500e02161400320501450000400c00d000040c075500742900070b483e00301c182441c0005451091010310600003800d90220300402c1d2036428201e9250410700080c1c400c4501690154a00a4a9800584a885e6003032003541015520050030808582c11f115032050200001c044d502c090030413042c1307540901d02c4800804c42c1343c04103400ea0180081d00c0880f0301d106c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 965114163 1250 965112913 965112931
    0x708091204051504080106260c01080f06150307030608300c0a053717090a1214100b0108190b12010c0207050a030c050d140105040308010501030c0503 66
    0x9041c2c140302c2400000418581c004400740024000465102020300808000c5c140c440c1460302e21828541d00b13001c50700c54189080c00c20f078006003210105139900460003a0301c4411074002520f075440382004610121b80f401c4454202d207201206005120fa403540001d4102c03984003003203c0c07a8079110b0320ba419000803149070010459511409031500b07214a80007a1100225a409660f9440150b456035400c002070b000c0480c1012514801001d10260300d0404c0c565001403646409071890041c0d50b450515075003080403a4900000072824405654070340390401d01a003050300080501070030500c1c2050740400101d16056003401240c14000241e40c0324416a40c001d08160340c2d44a8503100d520f1640c0c01000716815542007140c171800d03103002c0d40e1200d040008062010000025200c040114020700300321040c1c000740d100d80001102040455446407010040d40e0302202c20200768a51864540c0c103c1d420040c0f0b404483d401c2800b00b0041c1608180b0841c1242c101fa2030501c66141143c41c02c0351140300854031604 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 965115413 1250 965114163 965114167
    0x911040e06030a060f0606140a022505031f0e0a11040c0c02030607081009061a090402091309110a03050d1d030a0f0618080a050d0b090c0307080912 65
    0x24400e00c200d5081c1e000503014003541c20011160701e950702650b001407003a01c1da56880e9042007003280c2d40310198111030799100450030700302180303000c0003500c46035030265003c14152002031000024030080c1c5414001c200c020125000221040818170b19400c8200004180b82d10704001200c41c020b02180142d1105c4d0702c620200d0401c1c44c0002000b005008604210302048074400c070680050710208400b0317014185075181c0c54803e14154000c40c01000c3ca03900840d5045080102c00c0000b2092844900569003640542e01c1c6c42d80030f00c0c004107009014100f25164024005100c1103801c0f00d45a00180000f8090408003090b007240707109102c0f42c40501d20004000d0b0703001320701c040c80d8284620540036940300000c8905210103844000a4580142000c017503804046031714807001003001e40c0c402d00d40d4141d4106c0e40c04a50701080d49504444d030164030341100c24070600044840c0c0d01c0c003e65000d4901400700504010140c02d010380d140c1c8054208582c16804500303044086070500000083c1c20b12808000c004040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 965116663 1250 965115413 965115419
    0x110f031f09020a11010f0606021e031e1c06050f0607140d0f1106060a120507180605011107030809120114130c0605030702150c090d031206091104 64
    0x39100d84124108104414031035100403506861a00040401c40029902d51401a0700403460350b084620704c1311050780071854048200034403600070500c440e050450002c3e0708881012006e00505501c141046410068828041d400d0300c00d6840018103080303003202c1031541841102e02c2c1c0c880c0407079481740542e0307901403c6441e40d02c2040c98200000c0c01e180b07114010313024444c0356030780c10680707441c1101c202c220200340403909c020142580300c038000001d035107540c008061074140a00400c0c5100300d0fa000c0e64448145618030b030810700908000180082461a00c4803c001c2c0e2001200b00c001d020902070180012808400c41682410002d003d1090b640c10aa005280060100400802d8258806010215500c519085804203480081188101d41400301254603507460b190103882840250000400d1003c10b10034020703204e034001601c10010040f00c0d4000d07640d480b480301c406214040e18840b80d40c8000340c0c000303c20400d40d1022000004800c40f260a00c0680e03203441102d02582d11211030b0000b5450103100030 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 965117913 1250 965116663 965116681
    0x30f0c1a0604020d0c0206060118030c060509190803070c171e0a0602030f011401050315010c030c0203161a07020d1b0e090604030207090e0a020405060a080a03080604110f03 76
    0x359003184004000526000381003000c0300965a00d1102040980c1003102003000c9541c201520988048460070007c1e00c460841d60784d0b10021105010703000400902103104d940300d8846038000d40841880005640c1d000307a50341081c07a0f40340e11450080312907801d0780500298420b03c1042510081c4540005401c40304402032100103901c00802410b8200c0c03103a01000c801190282c8015800741d403041149807181d41c104200031146464850b101810000c2c1017040143c10700039480740d84544142460510880b00150408450170a02c5a4029515024034281d00c90b0f100c20554205007255003d541c0d0b080c8200110300711102600401c00041c0d001100d002000340020711b69400804506512440568400d8580520104100044908910036444101840141501004014005c1c0b1f0052410300c164044104a642c0701c0080300c030300034065506c80780800c0803a075400e50b004000e803a5076400c9964401123810014150401610168015460110103503689a1064100d038a11030402c910f1303d203980c40c3e80c042 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 965119163 1250 965117913 965117963
    0x40e0f04031e120e0604080d0902040b1008061e010504052206060f0206160905240f04141c0b09030f1201060201050604060e060409050a1a0103030f0c 66
    0x401c40030440103a4150b8900405000c503012002120f580b4507070f180400203a020112420800b84040c1680140104000160130b5821601c42c0769101c400469a8403c40c070200e4040e026000c50240d000b03230584011840030f0303400081c84c0d201d0340c2c003102d00040306007545401012010090b08064001a4200700c280300605003000c2e4480b181082e5144422080b449000b030f4811203d1907046040094181c009032450a641006980d80244120b80c01000d040c0c1603400c0503000c000580300c1c00d40582c0d107058401d903840030307082003c005038200ca1250b6582d0704469082407409074040c0c0038010041c1442c4d0f51081c09820003000c0d00e1006590b42c1d99130304501e46d280e03c80c002d0090008040100b0b6120801c118180019480090510620031688641d8554101700780642900c00c0240245d000f103103080c4042042450300c0341c02903004503003510002020821810700500300040703401c01811179141740081100100410300d02c14120b038007070f07511610012114601120387c104000d20140c40c2485848800d0149020024 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 965120413 1250 965119163 965119171
    0x211b03261026070608010f06020f0733111002040b030a0b1215010906050301050709050f040b060f04031a090d1d0907020607020d05090306040b07031d070911040e0f 72
    0x54520882510703010b8034030709281a0040c10004940310010080c001040c00f02c100500740c0c0340090482d4550003105d0b01d81c1c030f652601c9020312031030148046040c030700ca903840752023041803828001080c0a000840c010302811140e011140040c464100d030104071011510a44080c0d40d4040b000d1407464440c1c10541c00074106014481c0e5018030091780854021000b00203c42940c0082180d201136585450100710486060741d1003580240d06000400038291340c00000f00c0141e072821109070a10108100c042001090f41d1001076030031460003e40300c0d049056102c0503208980c03040c0b445079072a0703c14241030441040c0c2940c09070107987c0483c3c0c694420700c2c090001001444103104d20360407101285400112100410780c0c05002580001c014441c909a048c809605100440d0070003500c0c2140640100e603441c80010009000c0c0207040000c601c0e82c0d81319030004110309070341048240c1250520300c034031500c604141c42903400b098545000282d50140180584040781c034143c120402d19650803070790070030f02c140041c = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 965121663 1250 965120413 965120459
    0xa030806190e040501050603012901141605100b240a14030412080f070203040308090f0a0b0d29060307140c1513211b032610 55
    0x4802044032940b000600d8480c9018400104807820424141800c403004d4280507020300b07260200b16841c071076156180311484c00003840c0c07034003544008041038095401040402d2009851605501c01407000000310b4200001c0080d10401600414078100845030701141807914509401061f00082084034a003d4084c4034160300f04081170703003811729180c4d80d81d030b2044074100c80b031401d1b4000d4054125072210b901580804000700d6000c5a00300b14202170340d02e01440c80010015400050030011680300d0b60020030321020054001201c0e1910341c5601074040d0090480302040038a000155900b0281d25442c80c241c003c10417200818080600f0140943d90b03000034420007c0c008800d0200740c03001d03d031400030308214a0034005491321400c0d030144190700800c050801e403100c2d40c0003030059002c00c6072060600000c43c0e81800c4e04001044402064400409441821300510a4400103c0a158000c42030480000710102030000c115213011100720101c8003a101d80900850020040c00394440508012000c110a1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 965122913 1250 965121663 965121709
    0x9032a0307020d030915080105060d0b0a0e01270506060712021f02091c150905070b04030b060103050105030f0703023304050108090601031e0606090f050907080a030806 74
    0xd8000c684543e0155804a0006041450030001c1c000c0f444040c041d00c2c00d1502e0540c00c01e5241c180043d80c0c034040e8001c5c500c031065a6403201c0660703942e1200f4ad10010000021389244c150b948100450340c2c90b018200e1030103c00b4000000107032250141c880c2d680b041000500c107500300055034072007260b824281c0090505500c1145a84620b2050b5841c0e00d003002e042241000da80c90360540e0500690008140c0140600c560700c03800340e40000c418203117200b180f205010000444509a050040c500b4a1550007422200c000090100500c0000c068640c400c240030380741071006907078507000c2c540d0310503803110300348187c1d04010820700c010719110000784110032045410954120462881703407400c82010500002201d4001f0b010416540c00406080d8021640c030003820031907145803a81000c20318240219420250400301080421071117501045c06400d080d0010012240038a02e10f4004100c207950320300492140e000d0010700c50000003484207100358103549000f05620f4900601c0780f242004203002404440b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 965124163 1250 965122913 965122927
    0x5030403030e030304141917090105091801091409030307030e01060b120f011208070b0606250b01090c0504050f0301060b19111c0c0c170a0b09032a03 66
    0xb04101440c096809136072200002c1c44010103591401c6040381100c620707904141d4068012a808505084540741e01c00c41c1035560f101c003100100c81d280300311010781d0b45c403080c03e401001e5800d90503d066070503240402000c0203a05510080340c45118021500a40c1e0ba0788100700050366148250030880034004464004181140c40e0132483c0255048403442803501d60034041001152041e80240d43c1c01851040030103080d0b4065911070403c5489120070107040c1d0303502440810a20340303031001140c40107585000551507900c0302c030603038052240500701c1c192885d1741c0345400414020b80d02c0c8144070401d103064072010f2610b45030100740542902070039001541550b951000241482660000f00030281440b2030344414486500f001401a108051b11002180d000010440e8814850307010540001180d0801d100e00c0c0c005450300420a98141c0c000b00600c0540b03502014009400141441c11688518001c01e0345944150242e42c0d24007810210341c5410510038204010b0704d10400035020010701e0801520b2170861 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 965125413 1250 965124163 965124191
    0x90d03050a0c140a061d0706050703052817060303090f030307080d02130605041d272a09010e060111030f07020a050103020c0703060203060307170c120d0c030503040303 74
    0x8005002c048254001d104c5030800c010151081c002e0b0100903481c040102108940c1907540c8180c0c9004641c248080082d0040506000700195061890741c0f0b4400c01e4103800d941c0d20340c170710030f8000c01007400403d201000c595150f10302141e40070b100d00b10290041d070030540b00b80200403402001544040d0103000800071140480c82c160010000c100b002000560f54644011a0b10006e500300c2d407151040000902c0305201e002c600100c5071603419580c4103480402d44410b40526066450750403840401011603041c034800003000305100d8002c00402034821300b045070600e540c82030030001d14140380d403240c0030000500600b03288041458200d0410304d071003c481c0414078440e516552001c5c440042225012403014114904a151000940f00c203180a50614001e129080d0fa070352002e000003090741d0b8000c00002d8040d182040707080001c02c814410207075508090300400c0e485d105040b0403107001d00d1040f002c2014000340096807482e2040c080e510410525441e450858071a00042c1c4214109900c2d00030f4001150 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 965126663 1250 965125413 965125433
    0x712020303043503101401050301181a31061d04030302070b010306063321060e0114090615030c0405090403050a030c0206010f030f140109031d0303090d03050a0c 71
    0x1404441004041701d06244050390300c0c095031440700381007000c100700511014103a0510080c243d8003800000c5151520f0101880301d1039a0540800d401c103869402d0010f00510070b01d40c500ca58444100da40031106038040703070b150a0314164000c181e904041c150103c3c0d405464161a01d80c414000e14006051110b1691400302d0110300380c0c03040d82c02503240c2c03000f80081d18080e12005aa071201d06c8040c2c1038502c10b0200000c0943c3d140034103205200c000d60003508007a400e503a9900366801803940401241d51200440b103d044003e00682c4644d401c4851001c2050400908143c01280c00820740e070449107400d406094154801071a00903c40c009010000d03441d2240c031034850003613100381c4400391202c8041d51700a0450f055521050b0442d406013004004030b0703031001c0240058a0308800c41d40c101c0951400e044d503209660401c400c2656280200c45014594442000d106074201000c0301050100c02100301980d034014542401e902404440c907410000f80500001c0443e07182d00c0c1040500100d1340d0326288420f03 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 965127913 1250 965126663 965126671
    0x50a0c080d0207050304080609150601180f090c021c0503061306090903030903030f141906240216060206060904020d02030f031305010c0c1a0d0203070201020712020303043503 77
    0x1c0e440484e051000c1841480030591200907100248ac042480002c6c0c101e00000c040c1505040c41142001c8070800d82003502e01e07401400e01c0c500c484840701d941d0650000105120805c0030018002e60b08001c4546800c203107241d4800300c0e10340e1101e04646440c010081d851310310003005260a40d56080000c0c2114081c055a21464003d440c00140d110302d904014095440381035000e07190924129010002e811140001a00042c1000c61000c0410305041c14100030080342d004520b4a005001c21100707122282154001e40e90003560236516640015628040c441d04280902c8015070840030009449003081c59007243c0c418001800041c20b500e142e00801d00b071000912a103807560304001550892180d854080350f000b00004c0c40c216150340d04603122004240c943d030055003089200c41803421031582c49a000e44d1506006100c0455582c100b40101a000b50320002044412034a07010181034154004021b40707104540080400d0070380100d1907001240e54500f003540c80350ba403144481d00180044004051441 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 965129163 1250 965127913 965127923
    0x21606050406030b0d0b01090203060d06020c070f0501080903030a0c0e1306091109091f0317030a0f06080a141f02041809030c1b2c0f0106050a0c080d0207 68
    0x91a0b04200c401410386018402080c010f01e008058080000c0295100368119002d8a20058590b1600000140301103094540a003103a8004141c58400d501d01058000072138039141f6184a5182c0d03120015928440200d035040815001400050382c441942e42200c20501c01c0c520304111410708d40000240c2d08078140c1c40300e214040e964002441a18114403c0d194015103001c01075040202c0c0e400001c5c0385402c001d0074080f1139110a0003441d145202202900040c513808426140205880f80061009030000c03204203401341c0c2030000d90341884007148650300c00c1d92040c0e405098038260380c0c2c1341e5001041c44c8201c1100b19200c0d84080904003084802e008002c215902c0f8051f0761149440190800307250b060300c0c001d050602e0408000000b94115140b911001c0cac4c0003142200c160583c88003005602440d038001849010f4515181c0300c0000a0302c203051039038540203c030b010991a549040d444200d024011a00811800c1040441190217032a080c5219440390b14854901101d10180c0002c0c0c3cbc00200c0101c0da = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 965130413 1250 965129163 965129167
    0x130b0607060f0c09050319201f0f0504030f030f0216090603061a06031807030807060b09070f0206070c1b09062103090e15031605040c02161502160605 66
    0x10f086135001d550400105000c90003401c2070180383e034490000b5401a50001c01c642c00c40340380c84036201e0342c5408031615550028041b0351124810700c025005100c0181003c00007800103160448040d005406982c103580d00701c1000407001074070b681d064072070b00740e00c2e0080001d620a4145090884032001a10400b03003110f2840441c90f01c3c61440d1100584882c4001c002e82664804a41c5000d80c0307411003680d070711691502c02c12480305c080b51112820056290409440c030400081e01000340070803504a40040c04050704d00e45002d50380d1001c01c032580c11902c0320744c00041e00418086013209110b0101078040a014040301c5403041090102c0d481c030943d80e5440f11043c0c58650384200850356029160020664603225440c1541030250307401403030403007140250b0b0761038011140891411100480100300f0107002030100e4540240034080071100300690b1050714811824030260b80705d11071001c260103101400c500c0c1e100c640b50b800c03d00041c40ba00c030758010100441c42207543c010b01d15540400c0000c000e001a0700c480f5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 965131663 1250 965130413 965130431
    0x506181207182003061503070512090c0a030b0a06080a0f03031d07090f0204050d0311070503030715020304032304030c0b0f0d0519020409021215130b0607060f 70
    0x500707624141d16000103283e14012800200d030aa000152004034101d04915a403966000001804940c5030310f084002403201000700801039400c80d0013004080c0102c0307072101950340c6040d41f040da00c00c0c442d81d00c9078001d1016801040050620114543c21814400020441d9a12080c4003850041c01d0038094440151030082c100c145501441194908250203c2221651011603c201d030755910610030714002980c0c90300b4038200703030240b40d042c0e5002d02401440440c188010341002400d4800d07000000d021400f41342c40001b09c600d0000202e503591548005225881420600060003d40005109905105180708008125145030301862030394283d481c0541d40b43da040d81049a1264001e80000b41c0f800c5040000c00d0b421402da0041d11202c14038140c000ca040c8e90f4006240900110403e00e80114a00100300415101c0703454002d082002c484c502c0c000c1c5540ea801c200c100d4800414010160444a440101f40c0d5480c100d4000310026400541060f00d132500c02c0d85c401c1e00300d4003410400500950303a02c25007 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 965132913 1250 965131663 965131679
    0x20d0e03040510090501020a030c06090602220e060d060506061b030a0e01020a080904381c030801030b10050607060f0506150d0b120a030c0c120c0506181207 69
    0x10504001c501d404c42c03c4074140301c0042c0d07441c0340c4217401409000c403400f415400c1040c1c41c1c0110012a5220b9820754030340140301d2100799000c2c0045000d51400c1d103200d101080140c2c8502e003041c8190001031445000c0d2120340c5034100180703000341400e504075000f00084440c0d0022118a00000e84104001359034640c14404d000f0f00c02940d141000381150424480722000c1900001603a0140368100c034000380d0103904d50000301c03104907909015143c1c10502da2b4560110b01524420340b81000003520703440b03944404c0026400030310aa11398010042000c0000600c003150118208070742c40500801e00b4101962203500040050304441000c503012910f810b40407040750482c0c0580e9070071500a860044002d4132500f100b134490302030340c1c10080c42203541d11000e007a2541e5401039070783c0c10310f601d03401d6881c11f03540c0741801801c01030340301d40503501006116000601c1d4001041c142101581000c0d03110402400c040030080350740d01c40c421003481d406103010b0000c555035500240d240c0c6807102c4001001c031580f070204c039 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 965134163 1250 965132913 965132929
    0x2041208120a0501030b0a11090a0b040f0e0c071403210103060c0309050a030f0e15040e0601020d1409012006090c030d170615030408040905010b04060c060b04020d0e030405 76
    0x1403440b91424540100f00284095041d0b0350042c0d0b6a8a0108a074604245c298503e4015041956803180c00e0003000141d1101e03005c002d1050311b6103901c010300742c07503245d40f0011003009056880503ca00c0c001c1182c84c0c08100070110003030344040842c040d20715003182074a00000d0b0f21702501804280e00b8403000100108402446040302c04003032400c00b4004101c6948a0030b03107841420ad005000c0c441c556001d5050340c0d02c140088011004010481801d00012002c511059000780c0180c0300c250603103a0101d9910341c00012142100c038001d548500c3d848030310b504900144d4102d015a0341c14045025115000f40480070035a406141130100201950700c0e024000501d00107410201c58001e1300054003800541c0d82c0b000c400840030300034450400458a811005c41c1c070201e0009010f182c01803021040c08100020b10005000310740d0040702c140526600c652004089202c3c9109400200c0d501804410014003103400030001200300400c0141411180d001c50001c2c2d64020210070756581000600f40315529243c00 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 965135413 1250 965134163 965134171
    0x240f1909150e060319080d090809040c114b0601140a0512150c0c0f030f0715090203010e160f15140d02070f1104110306130204120812 59
    0x8100042d5003056004240c5030001c02035618000e00c0701e07402d000240a040000c56500340f0f070300d08080141c2001820140999084000d6071840f8509010f9003801d624821800107050039180c0c80500301e0420291690b040c0001c016880700140200c452201401c003c40301803900351442c091102c803002120013a40a802d20105801080c20505450403040060325007842e0101a00e009640d0308400d06007041c142e1b49000038604011800d150001e04201000708240c000d4500b039030007201191034402d5259503031510380c005d1046034010500288422000b040c001e8042c0c101c000710403400002e0402c61900031a007900d083d0f086641d51648120015590a881d600ca1080100901c4108007003981c01c1445884100749290301d401c0030080070000390429108400115084030400079030465031203605150100f140000100141c45d0818100085012400c050298074000900512140d1441e41e40004020301140f00c0c070500d03000300d03500f44008260b03500d004044440150146a50350303180c81024007400000d9400030 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 965136663 1250 965135413 965135429
    0x3020d0b090114071209020a0801061412031c0504031808010c0e0f1e0a1d06040c020d170c070b010b03012d051e0607060b0108240f190915 61
    0x8000c00c05400c1d400510401030100884006c1400348103800094045106904059160b520308200040c5a0310f40010359481540305903600f250030042d1112071612401689500a140b10124034203402c20100d692040c0c0d480fa109044c4042c40c0710100010600c0742085801030301882c1c1d507448803030342c035950400b2014604480072101c5d03a401032004008912088030742a459103000350703038403c0003950b940c0d03800c1c920000c0c0c40810800d0320005220808951f4040c1e065032860f00651034100e80c003240a1011944032450b0700291107000031810b00821002400a0050080607504000e00503240040d120303100c9113000b0409500641d8070395040448403c0c0a00c014440228500c0d41200d804d08404078149030b1004803101240c14251281c4104542c44000c3d00080156601c00710018a15003040081e61000c44000400e0742c0c1d28a15076202c60359960812103080d400c84410141400600c40b40c40c00c4212207660a10140c1460700700420340d804001d4002c03803a00084c02c41c1f42c0f0740c144400c1c19100d0607510401000c0341 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 965137913 1250 965136663 965136701
    0x2040b120a060f1a0d060e1603060501050724060b0d0204090506120d3f051f1a0c030406110d0906081906030c091514090606070c03020d0b0901 63
    0x407503881d040d244000184007224140101704070f4511a015030282008041d078075441040c42c5414840b86000301c199900d00c0c00032038508030000c00c1c40d522070001d44080c580d0000120240050410b48c4241042c030f45070b075075002d103610f452001c02c000006201500d00c514581602507191410710110505449000b08030bc0d020301d08415030000340f20303400030303252142c41c0e070b242004004503544c0c2c412110507510401090030354042c411070207452907485940c43d803c8000e10801c200f145440d0980410741401c0b40001c0080140d002650500c4500aa1583c03042400001a1140d2601107400743c82411604280c1c407101c04501141d4036200c0030107051004110707109403490100841d6052030b1002d0052100500620400c0641e4080180030852591012010390780114110800f15583c810910103080b0100c86045400d1082400080c404030341003503a804a40c1c005c01c807421a94640040c864950803070074080c1c40c40b0f900340b04000b0250b2503406048108502480840c1c1743d515042a1a500b5103000c10040c2c4483e00b40 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 965139163 1250 965137913 965137919
    0xf0f081e12212701110a03020a05091e03060a05040521070506091c020304030c060e0d06020313030809030304030915030e070b0c010c05210a02040b120a060f 69
    0x11a4001c07800300d60900d259101c409640001c1411002851105200b25030070040c404074503203801c4030180214030b45601d00b280c018418109802e980041400d03105001040c010807404a000e034003d0124017826180960030010950b00254011000d0b440c0740e8402040c60308120f07040c1c1010300509511101901c0c003404030f4201613540039030720150001c01d400000400c049c01c004a40040044504440e0860111502420840d82e0240c0f102c2d42c2003040d14459030041c250000d01400802034404503500b02c240b60081c0b5207020303815aa04050582c55a81c0543c444c40301c3c0c4000b07640752001c0e6020780850b018000340c8244c80d00c2c0c0a07109030000741022640345d10030300820000a5110b00510256400d000c0d17006500c111120f020780c0500300d100c1c1602d20360f0088171400300d00c0380070f00c0029180390303c4410002d020235100b81b4000e5400384a5400041422648120000003012098100a41200e0060001403a01d5a41c0d001c1d49016004840301228a809140074440d840d80760703000f01c001601412120703100d2249 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 965140413 1250 965139163 965139223
    0xf16030201061d04170c0114060109080a03120f0209130e060f0423030c03040602010504110406030b1f0b0a0c020a05040c020309010e0a0905100602010e03030c030106180f0f08 77
    0x103c010001805510b26010141a00c000841501c1d084130b000002402140f0707104180320580704049410340d0004d014008001841130000a080080a4050303c590454250114500001c2c140701d046101d0203a80800030400c180d1160f20740312250080703000300020743c0c48541458038100030303000d4041c40f0258007482c01d20000c81c100a40c1c071842031018074050624902420001400c60140d17030100c0989010126000404580640045119512820001e0000b41d280800c10040b106140030113000c40d0007440004204400540304c00c2c2c03144104202c605210342e610740c1010320a500001607540000d00e200c00510441c103182e681d01010744812207050102150b02c5070001e540740174030018203041211b450705441c0d003510f034820840044c040c03021091041c0d1801e03800002d200d2101c1c1c410803006600e014031403044040c001c000c0c2e9008030b00300060f0a2440c1d00e0701c0c00440d00d02000c4205810b8007180010001095095084610b00400f20741c40702c1450680b401c043d060070a80140c44040211205481100d0140 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 965141663 1250 965140413 965140469
    0x4030207051e10020709021c0e03070809100c020a1d1003030e13110a05040303180f05010e01020319030618111b0708060403051206042f0f1603020106 66
    0x710341910649181c0f041450202e01e0000e030f0760f00c00181c3c0ea00c00504401d40b402e100d00c4140555440440a11a00c05038800c0d04e80d82c1d1241400140c049001400130011710326102600f603820150071b2a21503050083c0750000b0340502c170582d002600b1681149114183d50550444d119400940010362558062441c3c901500b0607520300d071154415461030151006079405940012001000e911800361561180b01c0090304c1544107000c10f801250b101d0103004070119141d1341c9641034640d01304405c8a114540070042d50042004446681503000c140280d100c1000501e549190540305c50b0307002b16685107462007214404004981000085043c40c20804113004c440e0129001c20f00480000782d40000a100200d0034202290000f80b440c0c025502400705240e400405425001c003204e00a00d02d41d10741d90304100446200410b140005005000c910200100d842d90a800d10181c508010b0310b08166500714201c00d03401340408c2040412444c803040180742e824800c42c005840c00444000041201d452515852 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 965142913 1250 965141663 965141719
    0xd0e0309181e0c0f07060c14040b0409051305011802010e1008180a1208010306050f0403120c18060527030a0807050109080d02030a140c0906071a010602060403020705 73
    0x100d180580032400108000c3c1c12900c0316541446800d0322140685048809807068040130000903040b0010340c000b981300d0310708580407075800590640c505031429401302d0252000900b51100154400c0070900071a500303000c0c1c5c02c80c820b61600807481d010740f140f00141400806802c0f25000d0705501a001d260150004a001e4110100c0ca001e405403010244007185400d040c400001e040161208001c8241a0442240c1381680d11603002400155600c5004040d6030b03e08440140008001c0c0015100c070314901d038480003840c030302860301480c0c6e0754040ba8500c1c0e941409a102c072001507800240004ca0b07862550072040c0d031026500800002d070304003400080c1d650b8480c090240643c180081c00504020b4250b1000046942c05454161107121940b19000203400454601003c01e080520305225038541e030034442e129400642c0c0c8542040022000c0c88551b4006550403103001180c81d291324a010110691103000785120341c01046e581c546440c000781864516400f150003040703041d40f031640101504c413584040f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 965144163 1250 965142913 965142961
    0x6010906110a02310b0a1203141b12040311130204090c0815030604170d0902040e010c11060408030106140d09110406080a0b0a020903030d0e030918 65
    0x5405408216050000c0036400a51060300e05582d03070110b000c42d16246401c13a81103081d100d000d900c2d040401c803c0d2007009017410f030712002010041c04012080c041304010103010b460105500e03104e04100790340075031005a03600204c581a8200c01c14140041001c3c0c2c0215850301e046038102480c540d07a2b042e40c4221440780e00d00c1042d20071003640d502645030b810394004060104c0c00740190116050003034042403094411101c0f41d10020030b500054200000c0c83c500456001c02646c0e980628140328007000d410602d21003075000c1e01c610303a071070140ea601d0107007004149080000141e0040032410151071b180c9500015111900041c0130000443c08240c241e80c111411402c1c43c500086159107040b00900c10702e50703802d4030a841d25240b042800034100c44810f45042c1a02c08012940c3c03100c0c4210b680d00c803071136001001d40740d46100180e03003582140c001d84411040541100c1c28282c403c101d0f842034070460500840b06500115440c907032480d00c40e45a16141040d002e1440b036600b40503803ca4034507d0300500700a0 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 965145413 1250 965144163 965144177
    0xa06051e04181d1b100f12180506011e0f12080a03020909090a06200306040b01110d081902182e0503090705040501051f09030204020d020c010608010506010906 70
    0x1401c0780c00d11081c0321184140c070040d804c540201c0c4812061600075600602d420140f068611340217610100800142e0740701d440d94546075020650140c4540032808800d100c0601d0201d00284041020b00c0c0038156414805441d15103075a44200c90030b10710783c41000d00400900c0204580240914110840c5801c0415150390b2961560194060b10034a000d40303030443c0700402040000c90b0081140c8000728420801800303034191405d806801d140c0e10087c0b81903e82c04c1003010031a24545540130910303005060404840c00d202144034982411240520040410f030000b0800c240d682d03906840a02c1000010310440c24204e0701203866074803c112f61902409441e14100190071201641265080e608000099400011103208014240e4105aa5440451207411000b0030149014040c582c1aa003000c0c04102c00c84510038001c0d006481c0000c2000f043c030510390004005600c42c0e00052000212044026035071386900e038802e500315902640311a0a81c7d24000511070260783c4008031008072105450240 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 965146663 1250 965145413 965145431
    0xe13020a08040602250807020102010c0305091902040f060f15020706140c01060b0408031b010e121803060106110607030507050306150d0f0e070b0a0228020a06051e0418 74
    0x104049102d4412171548504101c2000400407048000d01d0114803e1b8024404030740700400070303010b560040d03032440070b10b4102042d20b00c100341d074102203e82528002400407904143d0102081c0403039009400c07001009902d04024001710048050044070f0f0081d610040c00514545a40103000a0442d0080c41c00848001030b441c9420100b504007001038117a0780d241594841d91000e03065541e80c0409030202031102d840301c5000035498184241c001c07404250015229180c440b604181d41e5601038201c408840c034421500040c10303141001568080e0074151555061007070542402460a08000e100d10101400e0100700700303226a006058a0b00507200750303048801160400c030000400d006028000705011318051240098003041c0e00217411042100703003502c1c07072039480e4510403c4510420042d9809032b4480a02c00280e06040901340001c4a40d5401d28442e91141e070340040c00b002030503402580041e60100d6103c1a170a28000380c90481e8412008080c82d01d13250000d25100c8500f00c030388903004256540c1d028 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 965147913 1250 965146663 965146687
    0x1030c060804110901080d1d090a0c17070210050901020c1c0c0f06050406061203020c0f01030e2406102c0d0f1118040b0705090a060e13020a08040602 66
    0x41038041c0b8004100008070340e140c4600340c7d66138021380840e10020300583c071036281d84d0104000d00c40643d00e015100c0d11055498444c07144c054501810404100242036040c00b0100310101c0c0201c0c050fa016501030200b610b21441c2c0401541c401400407501a44100219115480005075500c7c3e52211029124000b0311000b4043d55810b00160b8090491118070314401c0402c00c407a404544903138810740c0c040040c56112142410300e0380d6041e00080159103c5011b416051a040c1030064005005141c0030642d00782c403840140c10b11118491104522400038040c070715921240c01090b07440201610302c0c805442c030001c0010b1044c01502c1000000d00c070800e15000c0d00340400b44c00d08a1507580584107444425040c46c10500c13068092034151140711811740185014580945442803404ca40c1a1076800d60300d50703880c0d84944520240941080c010100306001180c0c42e140c02c100d004180c15191144494107000074480402499200107841500c10080d0941050704000c025405c180c1020300184c03180c00d18081 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 965149163 1250 965147913 965147933
    0x108040c081207050111120406020f07151b18051210151e060c12090305011a0f09070c1203060807090e011d062a030411011701030c060804 61
    0xc141d1801000c9901203002408001000c000c0c1c802e20003001401d10700c4580d039425008160b580e0242e45510004034000c560319801030300008241842c02458a0384950b620302400c4140d0000c0071120340c5801800d400b110702242034940008941c2850b10742800308000649901340303240160303841120450420302c030000c1e040000c5c01803180e074040200301a14900d001303a110207405109003444551024080040c503d64452803030103c4100b61101c8042c0ca4a656030022940b0a01444000704150003034000b01041c0c0902070240074036205844c3c0d2a08058400512295806014100b4016100c402c103201c60603070302c043c00075412a00520a10210024594101d0140104d0780c0310b89003d21030350030081116946503000c2c81d01c601c9900002c00107181c002c02184907110390072070302d0000c0c0c2d00140300003840800c0031501030310307041c00c50081c604030207000e1002001650010340d02560001d44000610644c0e50f0460400c82000070b40b200c50681a6146070385081d804d00b194024002005007010100d81040349520b9 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 965150413 1250 965149163 965149169
    0x30606012109060c05130b0a050a111504060506040f1a040216082212201503040605040302061f0312050405120f01060f03050304090c05120403030f27020108040c 71
    0x3060120b09056032005100350000b14180f56406d07050000044e0090b8801c00315195940c450f01d459090102418056991001a00045109000b5100b00e000c1c0040d0243c501d520440c42540002080c2c2049014441159002e8440030318003440c018091340791164582030640045802c5401503075070340e100d180b01503c200c1e058000800700040810602d0312111f00d07600b02d40b10702a080405104044ea80d801d45464800d240b00090500d100110300048180ca1060f40600c42c100050065001d0b0f004221725030505600c201c60a9600540d1f0b402480304040d070502100c0d8001c01c503010013050300035510089a411b901d0502c0002c0400c84d91200c2d400030180a54103880042034020001d0000c6030001640903101c106560869406500e004404a0b1000502801c442503d03000030007181040c4c20301780703490020b003880c02001d8242b120600901050341ca0855146104500ca550082a034840c0c0080540a54503a2140c0e00300c460703221060001350584102c0c04080c403030780910b0701083d2610b450038284100401d41d0 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 965151663 1250 965150413 965150423
    0x70b16020f0d1a06181317071a01081216020a03021c11150d0522031d0405010b070201080a0b040608010b0901080303010602070506030a180c0302010e030606012109 72
    0x10342d01081c00b0428030035821014040710640d14a5450900304080b80000d01c0e0110b0200301a4004a466101d8042c00e030042103220704400549415400100e03207a1360070001044612600b00020101c1152140309094010281031000707011040e001034640c40c07940105c1c2d44200703985222442c0f041c00d654030101844000c0d500036090f40031000c20031a004110341d003400010f4404202181001c05681803240c0320302c1a0894464005041c005c01e2413404025042c090500c02c00c08070b10364039034400c50010003220407501c0e00c240c4035542c01c4c041c140c422150207910300c40082d108034030b4100100701c00c424900840340d0b00c1d542403078a0052555076649880c020005940419003143c07a00a001c1941e00056111202c008070894103d2083ea0380c6444480e66131209020702c0c40160800e81c0104803900744400650740003002090302182490b210502260031032450700050740c440700003072010000e40d40c010b003442031880019800341c0028509034002800f41944121920280e0196654034442c0c210305074481d008982e444 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 965152913 1250 965151663 965151679
    0x103150b061b1b15071a09060f0c0a02030d111612020705090c0904050417070b0601030f1a06180307030c0302090705070f03051b0f0a03020f070b16020f 67
    0x601c06900110510701889001d40b1802c058069200b10201c11083c114800070141c4034841c100104001c0c103a00300c0da404880385c50455100d40200302e0200d40c500d01c20341d25240100924540901140c00920000d0172803403c8503810007601c0310040d0b010046986c089880e000204000303002c100c4c00d00d40b40c895284040342d401c405164000801645009202c6044101d5007110302143d1078000b0805540c0e401d03144602d40820800c03182010381400d030031240c4d00c180102c554580c1c0e084c6249060740c0c0c0c3d0340551411185242d0f020104141036070184606000040a5401080081d00350902c141f00c00d1761740b1402c02e01ca1580402d464241503880d9036414100400942681d01c442c1e644d20b4500003034449804120301c00e10800c030000d020544030b4400d5605403230700000ca800f4081d5481c0c6007aa802d9006111007041c41000c05600781e5440020011601071002d00c0c401841c5031009420000e040c006007828080b1103400c00402048444248010b54000c44054648a2451134040c80000c44980030700e051650400c8034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 965154163 1250 965152913 965152927
    0x709030f230d031a0f06030103061104031e05150c0307031a040608010207020427030509060f030106081f080c0f061b0d18050a03030c02030c041d1c080103150b06 71
    0x31640140340da0b034203841d400c690307a10740c00b2041040414040c405c0641000c0b05100410201d80645c00084441c074001807064a015101e0700c4505a1654446107920142c101e04601c1c03007045003c10401a5603144040d0040031030401d41c20213100740c0720152207182019212840043c0842c44840c0c2c140d0031400003401000156620058031380030303401c400300c280d00ca5880d150181f0b4501c12200c601209560b01800314800201684d40d00759001d801494507680c0210702804140b182c075400d90003c6020f0a065152100185049040044da40e488814140ea080d00498401c0080f4100014207041e96401200c1a603521481c2e400850103c0c06000c040782e810446089504007030320f0340850401c403204520758a00c03418030340181108403158a40e21176103130031001c0030703070108040303885130b0a0100c5c0c40b0320040a41e5801175071200000d05440030f1200e44100310034502e542911138002006080f503080710304a204505201c0b0100b0240c4022070500c0003420141c020f8103202e00480032a803050911040c02041c09859030b035 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 965155413 1250 965154163 965154167
    0xf0c0322050d380a1d07031e080d051302090601030e0d14090d033f1820030c030615010c020a15030603062a0e04020f0c150709030f230d 60
    0x280608007131203107080314021700800040030441c80c0540ea001070381a90b00c0900000b10b209600e180e448155108039080c001c865040d00240540f0380200231100740c01c0c80070001d40c01040450400038080364103152401c250048000408202b090800e809030925500010700d021100102c4e1003406000e5900c08000702d104020540c104403444100544a06103c41c0016841390700d0036070040880f0503403a0170b2400e4000c07100394882500105030311303468071141d01c42101c01640c07041644a0b40c20344155150281c1d000507100b5003010802004c81c2042200204070314100030804609201800c0304030384c10844214030020642d2a603041c02030007086041d2088a40300241400100145510b01040b204a4200b0382a849000000b405a03151420b041081001030391080c1c1c0141c6440310a40e900baa04581c007400140641114407028007800328124015007021080c4840c01c440b228401003518080c844442002e10101d2410140c15060721342c000f207200100180100070600c040385044201d000c600c60452000b0b80c045e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 965156663 1250 965155413 965155421
    0xd061d15010801201806070807030915051e07110d0b07090501050403051b120d0c02040b04050103120503070e04050412091a0706020f0c0322050d380a 66
    0xa401c01c030082010140c000c24508000a640500503c1c00c2010300624130b0748280e007515001c105d90000c002c51303c0c0c0034441d52900304d035412490080d40132a4018004000055608100c01c4103c2003034504546064600581000740542500d95410600d8000ca9a80204440e00c601d0083d2028002c0c441140c800d010b00d8a240c080e0002c80381038000409840000429500640560707050301d6221018000c1102c010425202e41c880351650030760b100c24042d03525080c1a50620400134180380903a6400030682c52401880140c602d038000c0d090246180c50300400210b2080051400340c40f01c2450043c0e41d03600c422504032041d4501503c0700e07905c10f00e0b20003800100001618480c0320100ca80c4c40310b080543d51509e0649024140b20652074050b40e04000359800100385034020048001100d101d00d0030a04030488807031a40d0441070300031480500d2000d88581a607881035003180180412203141a100350319035140c1000b8030ba0580a4401440500405503005a0805414001602c01020600c5511341040000060 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 965157913 1250 965156663 965156669
    0x31b13030c120209060d11060d0c0e030304060503060d0303110f0316020a1101050c03070b27070b04050105030604090b040302010c0e010e0a0e090708010e0a030f0e0d061d1501 77
    0xd4007249000180469a064610016a4001301010440ea4841c018426011001e00c400c543c0c80d064a0f90144540c1e9984001d800000403049001409414010b000780c910400700c62414800c0e841480100011603000003102d90051083d2441640107447e85800c0d4083c011404c420040e903c404200d0225580b4240d010751f114094a242e110b95011058105070307125060000f001e0900d000d1040c1000c0d540d4040c05c01840220031510440e490130b00c0a45400840350800d40b000454a0341c000d44003070031508440707001810002c0407405010580e01c0e00c8100c104c80d10403441071700d06102003c00001e2159031030303500c207002854008281c81580c2c0f41c9172800900178428148200045401410903250350352040c01c03003075030072400540b41141c0c85d030a24201c410305880042c80e0140e07610401c4800b140c160001c1c0600d11072461024002e2500f10386902c0c8c00346c01440c145400c0c2c0204500c48442c0c103a40d0b030316010806c102c640c204c100000c00c42d0310318141b1350503801090748454592094503280802100a40c0d1a05d0407 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 965159163 1250 965157913 965157923
    0x4060e0d05130e010803190c06092f0906040209010509090115020d02030a080f0c07050307030309020924041d07060c02010212191d030712020a08150c0d1506030203040b1503030f031b1303 82
    0x20090107032f080c8404414000259603001307244c0c0400a001c90402d6401003151850504000d400e19001c0310001c0e00b5208260070502e05a1407600810400c10340400c07004d042a20140044c1d03041900c108002004180000c146228001600d03001c940d00c8410328007162910b540103c2901d030340d83c4050030003401412031071004034001d82045000078861449200d4400b07101d4600c2d0254040c2c0c1e4004e00800c009020583c0c81c20110300001003209030070400c20482d01300185041d441c7e40801c0c40050001904010141d20342c150085010042c000c0d44988980807105c14643c907003460700c43c200c02c001016a603c200c16003001d4051140c80300c049903a01c820400030b020540700f00c41c10100143c5588007261640f48004030441580c03805008600c207000420060a1550062040000e81d00603100792584001155481000880d07070000c140014422240f8071181d11042000340300c09c8040103500400c0d07036442640303503980780c0c8040880400c030b80c04a1880b1000c0007001d010710350307612620070a1084055005600c4102e44d = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 965160413 1250 965159163 965159213
    0x4121a0106020f0c04021b0706120f021e0d060b030a06050a0f030302030307050711090406050402011b0b060d06020d020c010b01091512020304060e0d05130e010803190c0609 76
    0x1d4414070000380290000d0707401020b4004a00e40c1000d1101a41001608004400e0005818000d600003040180000c040c0740c0d4401441100304050007044035043c811508031035004009241007a031180380c8102d0a00788400d64203659280d042a040020241500301411088001050219900344c542129094490460302005215a102e03041c9040518901c4000c02582080c00003456150140f00503140c06805039495041110401c400109058001c40742110450b66500c14403042d0b50388402203442003082501c18080c1172405807140803401c2801000c140c030880d040ca00c90740c00c00101c2c0d015942c2540d0303071000564a40c041c0c0900c0a01078130391894181d00080030f041002032889000c41418440d0401038860041d1100c180001101a500046c420b646a0345ca846008411610402180c40780c90b02c19038500d0b4480c00c0032041419400302e140e120f08040101d07407005200d0660044201c407a00c00751011b40c07581086800c001555050992003014042ca80b42500641c140040d0928030308075240d014014007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 965161663 1250 965160413 965160419
    0x1905030705030115050d020102190b040c08030a1706011106040c030303150b04030602070305210a0b150f070515040308070e092707090207240207032304121a01 70
    0x15003251000d1881c2c68132289200b2040010707003446100141d40c2e600602c1075801b840c03141c0016100420b1013081c00c8610300c2c20441000107010b02000408054400c070000340d031a00d49240c000030700d4a2010b24400c0c90042040c004580103a00401088040920f00cc0540d2210720703141c2031541801c041444150046410a000c0f000034038215a0004107550751000381a007002e0841d110380b0020b400c5103200b00e080c09020090000303480c9100c008013110030710401850282d03150081c1c4440c161210284c0f142d00840800c010408000d041c00c0030303280003c10440c1c1903901c07034246040051400200c800350508075030701a4180400d05d80e100010f98880d40d115100c54030034a2900007404482002280d50258040f0001142804102a4400b80c41d107001d8030300448500a03240e030300341d0049a2055408659080756051016030450114224424111140c8021030420380e45403800b400407a04c00c00c0c0025003525800d41100c0401c1c150703003550042c0c419191a000310b140c4500c0c0c1a03041c1c8440041705079500c07100070000 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 965162913 1250 965161663 965161669
    0x1d0405060a020301120b040c210320120c15071e020c06030604051b030a020706060504200c0f030a03060602060f061e010302091008040c0617060d030203091905030705 73
    0x104d040b910070b14199022040152152100244090000c40703800702030010001b030110700150720960b15903210702e140b0b0308104140b81c00b40c0820308180c0b6201369000700c0e045c00e03440318002181082164046008040d51003110145190030702c6c0f0341c14480c10500c241d90091007401640441414084400d520125020009180d402ea03039503d041c2502c00da1100003000003a005007495000f96030011400c84404090181014a000c0c1c0d98008031900c410696010600c0c1c810301c41c05000d03903c0200f000713960400500141280f000302d01060a071021194080019007034409103420010b400c2440005020340381c5030100782000a01800803440f40768014030459010030308200204540c0c07800f581c80201680768400d1002d002c48884103120040310b05059007400009066260102140c02103c0b4598400b141450b00c3e02e080500307081d15070808010000466030701a0650320900d081900724070202e68040342600310b072904a14501c83c4120013600440100007580d451115445040250303117042341903504150303c803024 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 965164163 1250 965162913 965162917
    0xc06080903040e0a1107170903160807090c0c0b0112021f0807030b030c03060108030c06010602060717060f120a0209161704140601030809040f02070203031905041d0405060a02 77
    0x8080e51001200c011681c200841e905c02400900c07070060580c00c04050380c41d501149102c0c2041c0002c4d40c800000c407094130785020302500007140740250110110707d003060070382581c40701d40b4003036255480c0d91041c54061407030188180007802ca07408a02181d42f0340c1c503814881a440800c01c812401174142d10545074000300010883e1444040310343d43c03815140d407440001c4000e840b00e8180d80d07415000320152417103545c13030038400741d806080620000c5551b000c03183d0b991850090140d021404640103482030129280c1c0c40b040d10700a2982da40b103060110380724440002d44c000000e006c260750095040000c1001e45001003184070007079000700c1d059921540e40480007504074801c03c011100050f4007030b0750014140c0e0780c5194250403a00446d45070009050703a80b410703442d04c2000c1e0030540300e042010800c0b180a00d414024806001d642150035070605010360f0100c0d6480c044c003c04000b01c1110b0103590050188603000b83c0c1c0061150f6404820450704505085c0002038040d1401c0d115801800c000510742c03280c2d802 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 965165413 1250 965164163 965164169
    0x1080c03010c1115190204030b1f03020102070b030a1107030309051b131a060c030c2104031214190801090911060c0a32010501080c04270c0608090304 66
    0x50086150040346081d40807000400b0304c0355070100714511003607403445880a07102030743c4500100c04050070400c140c2b98040090b60078891043c800c124007840140d902241440446a070201c2c210303180d49404030f00e90054040c111035805000c4000c10f49a080c5a496080012464000c40940d44910301039003e000e0b15104141c0c000c1d40003240303400103440e04000e590011f1407441304001011003200740c0d030002a0455000c0107901845da4000700d803a40c6640814041c0000143c00d0703404400003001200c110410500071484080e00d2441078854203000c16024040d01955107001000d40c694400e150005000c401003000ea1070400a20301d03a00114403550503104100c4410780114003d1803071651041005141e074000c0d440140940580d210080003c0c03400144890010075811700c0d100c0081020640944c808a202040c40040e0304110041100000120f070140d070400043c0c40201d400e040f4041e404986240c8074071003101895404500c0c41c148040601c0c0501914400d0f61100c1c2e0704d403103500740d060b0b4a0084e80 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 965166663 1250 965165413 965165447
    0x312030c0e12010207020402160c090c0804031b140607030c02030c3003131a1501111f0506040c020f0c0d2307051302041a0a030e0601080c03010c 64
    0x207804241600d025400c51003500c002c90000344c5818a50790104069800003001e400320251516110320411101c100740c90003400303c08a04215992003000006c0c64248064070250a01102150b440c1c45213118042c011070036034104030440086802c04000d20340d036990444010b00021f1400c2d040d560490710101c201c80105075200002e26842241d0b05418001d0703030f214002070038060400004814541d0b11900554480d20921a200e041020715007800305050841003100080440c0305020080e11149410030026170960a00c0c040c0705c1e500382c0c02c0c8800d262495141026032000d10b040d008038040c200ea508180d1080c130702540c06100d240421503080e6601c40248820a0711a007120b111507085041080350010094050041c01d410091203400c020f460301454405144e664000e1078084c4a0f5080442031482c505405a02c114a020715141c2440c0f12105c0441101a92480005842c044c962003504401c00500e1000142c501380d59581200c1d99682c0341407000c0780d010307500f08044030b400c8600030480e000d5404098 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 965167913 1250 965166663 965166677
    0x30e030f07031a0c090910030308062e14070605250503071206031e0209010608011206180203070e0f010803040303051803010f0c0215010e0721061d010312030c 70
    0x1403294100e030f02100505100384148140300604407550382d00704075030003060011100040a811410001d0548a00504041c003804c0100c03040b00d10519109941ea02d511000c00300c0301c0103c1c2c085201191011b012149082507440085a001c0c00d20500c0d078001c60080c0149614070b2050381c603c00154444481d00b28492011440a000040d02c00e4081c0380503211305030020600280c40c1e17841c1c0c4d9900c405c030031090801e10955070610746404210700b0054601d9001d03040605000009600d00054203c160143d100002d00440d19035036650a20b60020450036a441c0d03000b400d80c0c0029844142c002c444900840e030310354009403040300000d80303068044101c6040c0e98060b0b85180ca030080003c1aa0940310400c1c0300160559a10200b80d00a08841e00c208040d84c8200c4d4082d108145411340c03130034080e00c4182c02100e4101c0202080c0100d00e904608a41c03010303c0c1170000003000c25079a403c2e0f54002e004551000b42d40024811000c0c46914140d6a1603060342d01c10721180001424a02c01242150015408080400d10b0 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 965169163 1250 965167913 965167943
    0x1f05100b1c1803091d04080f09060906030a05060112020c030a0e030f010509070602123408030c030106120c080105220e010e0706080709060e0a03020d030e030f0703 72
    0x14200c1d403645111604502240d4210080c03040c401e03203101c0d40000c0c0d0005488800c14450380c81088101c40954603200c0001040c1e003010346840703c43d071055884903000342e180000c4564041e16080107490b00350138000c19442e2030340b802c80e9a0780f02609084560f0303070018180740ca001c014640d4900c2920310310f40c0800d0040d800c01968550039078520300504030b030700c1e0f0500c90040c0452500f00300b401078612034020000608826450040068176100308610024001d090612105804522a0010780034007005508040082d0001307428100c4104102040a0484600001040f0b51550500011412150140d5416180a107084003040813a02511281c000050301d0000400c000c0c900036900d9194100036044007450703122561140000c0310708030481c203207099440e410121004c000134804a4002c0a643c18802c405180000005100d00102e0203418148440c018020b1061745440b1065006998050a0344000d148a401e02801c406090500d040c403e105e09404030002606c04a4182c0442e03500021800300e15030 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 965170413 1250 965169163 965169187
    0x303070806090a0b03011b030b060702011e0e0604030c0824070e01020c0604120b0721150b0339120405010905190606062c030a051f05100b 61
    0x2402074010300243d1380718080e200301a6401e00c00c201c88503268000626006a60850190645410010765445003500b40040e4003d030760441d42008540312080341565400c050800c0a940b4070718054910358002202080110401442000000548a8030011100300c0078030304c3d1004804d001040d9415400c1410b5001090905014400d1400c1249050041c1c0713030440d6150022034210740140c0c2c85900701304003840343d034418010088805904800c0b54a008481100340c0360013040f0b10014007414002d013941e00c01c501942010458031200141c2400b207020f44c1e507420150403403005841008104941d90380701403d5400340c0c140002070700351a1084501845e0405012801d1040c015400038001d90b002e540b100c03005000030340c041c0150003a40040e02d00800d80d88005045c481c044540d2034000b00240141540c0100c040801d210001d0780c00441c0c6c9036a08043e00d01003010a05055041000900520444494040d203851700c0818003499a0700c10010819945c500d86014041d414610440c4690f1008120100c6261 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 965171663 1250 965170413 965170429
    0x806060a030c06361802030405032502060a050406021603020a0902091c080319090b0609090a0b07020c030c0103060e0109050c04080f010c1205041a09010612050c0406080303070806 79
    0x1410040d1000ea054800210f10010020340f1300d0900403019881c003080c401a29007040320080080024011401c40c0f40540d06c407650782c0b04030060402c501002e000c0044036141c03519011400540d0143c10386454a00343d140140c2a50414059840940501c150900100d107120300c8040880780c00600c116541d600d065071120003540501c00064119403610181c0c05680081d080700d5100030b20540e403d659a1420011100c504400c40342d56081e00ca04042024006c181203100e90758100b50b04440b41c41064035070204447c0751040000c0000c10400610081040344c50f0041000040c40d40194151280c02101e0401142154940c0c02645a03c80d8604010b1150250682c0566888a030400740c152410b43c4480c1c02d24a052003031110700001c1d079114996840410351051252000c0d4403882c90500c141c0c1800d070744e8075290140d581d20036880c10b40c6240c0047e603010400d402c500c004100b000a425410002401c1198581c034450700103500035801c003c0009a030100000880c0e21440555031081e0031a110542004201 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 965172913 1250 965171663 965171687
    0x310060503100b09130e0304092004031514090109052112042f0f09040f060905100903050c0615030d0e0f0402030c1201080c1e0a08070303090806060a030c06 69
    0x100c1e6042c1019a00117544205a0405410b1004545940ca00202402990000300509160902d481203c0c1545500e2909076015030780e02008042000c10000b010b400100715070001081c403000d1400034481d240806511846000d030054055400d9086403c400d402d019020503100900d00c0010000344c03811000740101c15410a06c10041404da541c0d11510424000c0c42c040c040001d106800d030341e0782030780b0b18110f6507076595100b0a55507564a85441d840d21151340e152050085c1c00d49840741c84c0c081c10000e06016200341e903006100100001c000c103040042c4207030880180c6610b41c1c03248002180e0004c4100002c152030010040050440303418911003240c0000b503a0032200d80240b1440914240c036500e034006148034420005079a0b40300c2c54154928414040180d1084070b007600044130b80c8001d0b8032280540c07101c0d5110041085105280d60004c240724001031380c04000c1900801c280031042681c4008410211980441281c0d40d5840c0e900400c04084100d00c0005c010308403602c420865607005071208201 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 965174163 1250 965172913 965172919
    0x14070512040c0b0403050609010608010b0d080304060603152c060619030c060507020f10050a210509030306090108010501062f071701180f0f020604030f080310060503100b09 76
    0x1206940300b080b03007120b0b013103070700100d40c40c0c1c210304d00b0820944d4003442840002c04122000740705010140c0003180c06042d5009000d044800008005414008181c005000860b4801501b003461a10041d0a90040040c6194240414a194640c0040f40e100701d035900716180f4581c001d0304491300c402c400c01c01840c0c120038840904260180d0000089003a0040034001441903488066940304644100441c8000b000301c0711340710344048240c0041e00780e40030080d50708608250401c10520003241d5801100c000790b0a030340c1c41c00941404100300b00b032003010014501403401070703510381101d0340c07141c403282e00340c600034052500000c11510440d40c0051300a400c105081c0e0600901d40c8185491248c0d29041121075080015046011100054007010900c0380c5038815000151008480a40759108a4840c0c0c0400d0301420000c5100c6031007003596156000c0f41c00550340840c00c405505121702d081d00c49a0421034400303078041511000000d02c54000d004403481a0f10322180d00c5202c9050a1401c0041d1b004545a035030 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 965175413 1250 965174163 965174183
    0x20906030106032c0d090b070c05100215310b07052a15011e03080a0527090a0605091801061703180a0501020d030e032b1407051204 58
    0x22403404980560300300202c004003400810304c44005c007800c40161684030341d5110500b00209030110301d13003076071010a981c6c0445285104401c0714608038038289807070309014102981c1c4021700c04072521450310400100c0000200c0d0810402019403100381c0480054080c01800c0c10344001a50345214100401445071203102e90f015806c58902024a9006031000c982040e0780710b00c059100d0302003158207980c01020903206000380c61030a0dc0c0c0c6121402c00d14130000380610400b00d5070480312070081c82540c046403281c01c1c1450030411840c4116040700f1480d450f45009d180640086141125940964400d9483c080d01c6111140c440b08201040d0354240d81080700d0079580d590012a051004000004031002e00078011038840282d4002190406100106644514003030541002141d802003444107184003170b402c0005044034a06101811442a03070324807104402e04401501c100e0601c0608040100a50081000364400c552031060703d85e40305848040103e10140030121284240c901e83d80d521601c5640840d03 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 965176663 1250 965175413 965175461
    0x2508330403090e090619020c07050105030c190f110d05070b043e10090e0907090c0c060b0a210201052101051c170a0302190201020c1002090603010603 66
    0x140000c3c406580b0101260449000d0200301e42070b400c40b550314036005000031850080001b0f04580c0c0c1d001907104550600c2000300014030131400b00c9013928440460a0000403104408020092900e881004d610300415140504c013407600b800020043c20604054444904d4034005486007410142d00030b20440d8070030040c00c0c0181d0702150415410a03624041404264078a0402c1c2c00300800110143c104c3c1d0051150040d605030091340070240d002100c40e28100c40317030729480d001440c07400d1080c40e801c0545000d007801880801c0a0344a152030f00682d0040700b080007441c6401e0b007003050740c0c0030a1040300c0000304030782d0050310110b0299990031451441410001c0c43c1440e5114010855240d008501580b2007904004010303504261220b1407510800904800d0f01c03940a9a0340480540c0400510303444400200f2840d401501950488040c2c5100a01c090310710030401c00005d02075880240c52003414060000341c2c580d40043c0d4000c0d1810042c00134000c6095a00f01201280140081d400d515403c2f0b0b544444d10b = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 965177913 1250 965176663 965176679
    0x60f0f16030209040e010f0b130b030a140703060e0c012006041101030b0901030605011707031a1003081603031d1002070206070b360618250833040309 66
    0x600040c3c2c2207c40b001c1540c4440b50304001846031540c4402c595941081d40b09501036034003143c0d80e0b6815070702050031030031525520045450300c207458000510040c03802c000840e41003000103000c2c5d222042607071408040c0b1500110202d600306105041901a84106c0c00b00d0b00240d0480110112900e0614001410200b9900000c1d540d10302a1701c25144565258010b2145880c2c482d171404103e19400000c2061707514540e699a101c10101c00d001040070890000700f403400b0003003c400001144c20155094503400032a58007200040c041100710086840c09a40720040c102e01c842c80c070000d40708400139107854800012880042e5100348030485c2e00400411119000441c40c60125001d8076802c1c0da44c045444e1100f046100000904443c55030301421142101e003100e40c0010301d00d502c11041c480503440c107185060583d1a00b208201c40b9401591038040004000d90807008410803070300a20304440f0343c0da11141c1864102854583c1108080c1040316a1201d140700d04904550880c1c441c0c9040c00c0090740d1f0f0b840d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 965179163 1250 965177913 965177921
    0xf2d0402060d1d0705060a080708150a06170604050c220801060617062209020a3c0503030a0809030d0f0204062007090c11030c060f0f16030209040e01 66
    0x54451070441c0f01054020301101005180050402aa2098505800c0d50000382003e50000e101004001d001c9000500d5544115001c11090340060301d02000d4070748500c0042c001c0071858190105010301030001581c140b4003401598010341c00c1076000d510744400d141d1400114003c407443d11300c0704c04503850f0004c3c00d40001d100c4d01e401481c2540d07442028450388001d210074058040c003028450108401c04101000d031a03c019140c1d041d901d640040c140710305102040c0c061380541c1c000c66100728913400d01a01681800050800d42000351144c803070350a001c440c03004025034035009d05501a4400d000c46071909005040294000f40090210303406d003460003c1d41d0301a906010a20256181c02040070402d240d003001d100f008120100311241080d00980302c4035961881148510304030b498840c407141151500840400681c84981c0c4107a03a84c40c2d84101101d0355984e0192120316000321004000744402440e4003402e03014145080f0011000c0c0c81030b102c114042e402c41c83e2a154400e54420071310791025000d01c2 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 965180413 1250 965179163 965179181
    0x1d0c0d0b0103061d01030b1b0415230c070506070f0320030f1c0b010c06050705090a0815010b0f0a140412060b0a0603021303120e090106080f2d0402060d 67
    0x2880b04ca103605516024071180805401c880c00300c81c000d4484c480d04c4540c031095034150342c0b0005000002e00032180d411141100790034604d60840c41da00f4070b0038860886e003030014024000030004854540d903445042c040c142c801c2c110f01410108042030f036900002c3c030402d41225207100c00c0e80b01810201566907aa070569000314480020454001518160031ba64444034990701d044810382000b400c180440007910340114104018900c5503a5000a040c06004009494100d01e025240c1c0c50303001c1d142d0318210303512658406c40c800b24111300e100000700b110203001100d0603500d420541c203060000c000015242c0a80080c083c00f5009418400424012480c54070140c816000d03040201d0781030082014441101e44d00d402c042c04141c01040328070404403100500904495100c1e98541300380096039400c03943c14450b580c0f01c0750300807003183c00000d05a5011007107030f0040300c00d544402c0c002c0c0c6442030a0744408114544440344001d41c5507005050031003038003000342c0c820300140481f403519481d008200700310f4142c1d82c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 965181663 1250 965180413 965180459
    0x903090a080105150103060602060423120903070e04081909050405070e0405070801050114090a0512030a0e22051f062001062403090602070c1d0c0d0b010306 69
    0x1e810442103c25450700001380110a0030100240390034440c0003511954010710142c0803400c541841c5a881c0c045600c00f48442c4441416940c00091300b01844100f40e215012442c8a48111003021a80f11207548040f402990301400892501390480c1269488980c65580c12060140c8480002840e40765070003840e2240f09203941d02c0440314030384130822040720302c080d10210401090360014403969800c81a004424043c000c04182c941d100b00000032104452508581d80041c1480140015010b000000c2e0038564401e440b1000204c502074144007051b103044036100d20603805036811244000d0990300c01c0c3d401c00a038607815010034a500d0307170b22240035005900282c001980e1117020400d0000c01d41003003040d1100070b402448010714107015039000074010032000c010106820242401a80a80c0c0610034040c1d10003000d5440d0442c80c107240005a03a80d11411a08180d86804d005154641c003103c217110319a600701860402c061802180300500d100103100d4140359030703103002203001c480441c2e4000503c0b130f6034 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 965182913 1250 965181663 965181671
    0x2c0f010606080f1302090601050723071a0304021c05010b040e1606050c0a380117030c0d27030605010603110711090a02070803180c030a0302030708030903090a0801 72
    0x51210020010001000454034a0807400b0034001a42c0d80d4451b941c014a0901c0c116403030300b9180c18a01e10551000c0c1c1c192940701040344008070051008101031088900c0c01a0045150111030b03213482580c401103c000354003007629a07200b030321813907a801c002c400340d0701420000828404980c00b00b03044640f64a0b130560320b81d100909001000040b003610070701620161070103a08000005024036039030403804600410010251400141000464a01c51146280894000c4212603c11070440d030305a03080c001d050200b0001b03900791a603407070b0000444200c01900401043c07448614034089a01900d0a59400c0c82e060394103c1100904000124410203503015800000d015450001d025040b81e81994984400c10380c00e00080010a2000300490b0444009030383c42041c1e5076070821040024420030300010710100000c02808100304a8103915005514001c2c06c1300c01c1c8007413034810540c1d190300780304001303006074010803100c000900688042c1d0b8001e4201022242400c051764002240d21486404c51801c5a42d6 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 965184163 1250 965182913 965182921
    0x32609030a051c03140604020d020903150907060903050a03030c020705040c090519080d030209300607080c1e1b0a0c090207080304060c2304030c092c0f01060608 71
    0x74840885014200c0d03003800c00c00c0c1c5124002c0b240d5010170040010f48071300d07030203d4040d04031030168045901c41740740101940e04640c40c84049014803034041c2d07044250b82c03140c2d0801040842c0039104171001d0700d8000004081604490b5401c8000c0d01521404000310700601300009001d8549009550010302c0726110b030391246080c20305014030800c19028140314070b000079004000501001c03480b0710344589103203005652040003c0110720031035480d1074aaa410b010703240c0100400e0706103c4c000824800c824050b108a515802001c60b800300302500c120305850810400c814000034840044041c1c2030450300f07818101100701204403541c403140403d10a46400c54031004003002140c1072614060302c241e1100f14200607a640300c018807404001d02c0104026074030071195051900884c045d15284c01c4544020b10480503408114070150040e202c1121895602607000c100d0a400e401030105010000020f0030455413204020880144000e649000d280944030f9000c0c40c1e501c2c00c0c01000d01900d042d031552561420 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 965185413 1250 965184163 965184193
    0x1140702091b0f180306100e090102070c030c360b0d0204020a020d14180d21030e0d020c0d020f0d0b090a0309140306010513151502070807032609030a05 67
    0xa213000141c0f00b81c014070108a401f90351040020181d40d1030113440701c010b81c0c403111441c1c0284213a083c09001590300e50000010028600d0021041d94508890420f83c00c0074080740820344420310711120001068100b40c40b14501d4030ba4442c0c80d80200051142000194130b030017060803a031042d02040e00582040b0203200751150414800c0c441c0c016112402403070072070684001c05500c9032501d0540d1182d9242d021180a021800d0740c5100b80c015542c00400540c2c52410001c0c004003080c22010f507150040c81c0207000064000300b2070307400c1148007820451b02c0c200309500b00320607400c0304101c42d58012100f20740c0802081c1c80d04061849040048000c054542c19424050000101e960210146054181440402e82c0340480d402e1304450050317510341002d038205100784014108000f8038460440341c42c280002c1400071014000701020340354007034905150319503449541395034040c003000d00490540303103419018200040c81d805110000102d064100744074100000d0a010707000c4002c0e01ca603030151260050b824 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 965186663 1250 965185413 965185447
    0x206030c0c0f0601060f050d0b040c020705030601060e1e011403040303051005150a0c05071502070504060b0c0a0314040504050106020309042d09051006060c06060501140702091b0f 79
    0x1080302c0c03004101c15850418010140c002c8610b507030041100c0420150100e200581241e40203040c000c0c17003449002407050000350b8903903040c4107841c801d00c5540300000300c250249901c00002c86c0050660303801c0c00980d80541603000041d250041c108448540003130080700c407440142d406a0310a82e004a000e00b8013440240428007160060742c031071214002e141c1c241040340c07422a10b40180d14104141c0c41c107850b003030860910105038407540055109103458071400e9404207541d02170718411a803c0048c6525182400114050404c03061150fa02c41106000400d011b40c030104240078140c00381910306625680481d0644000303a10040c0541d0001c15086c00b1407505010b804001d0351101c40080d1040400321002040e202100340c9034200ca85d4600400007071000501510f4046034070701409005150b60740f40010120208084251001b030314025011074150300ca20f01007811403c1100341c40f41421a180c00f0800d03441c03c0505a0540c1094281c02c0d003030090101c00c05001042e055a40042d00c7d40500f4040d68411 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 965187913 1250 965186663 965186683
    0x903070b0f1510120513020405190501091a0607080f1b0c01080420060403050105091606030b06070605150a0810061a120916080d1202070b0402100c0206030c0c 70
    0xe0340d0162403602c043c0ea00c0340784204085015400807902c1c2d113030484041a4005050b901035001707400d000820641d541002c40070450390020301000c200310703079840c042101220300e2403070071405460494210010614120000d80711442c00b4042207841c124108c01000005d910400c00301034108034542c0100c1d441e10341070000141c0ba05003824852240d190507031701c07403844155905150402c500000016140c03612a5020380d00139541c0035000700003900f420050240c1ea90250040e0300c04000c485840818424464062001e4000002d0300c0f01d404c0c14000d0b501e90380985801400755a98644848051805645905a120040c0494806800389040086002d0103588460b00808884030482030000b215400e5a42140c446515000d105c54080e128840841d05159041d69503141824070104003080ba0038001c9042503a0305000d41303c61030f02207503110701102030740a41d801c0508071488078400240503003802e01101082501e1031038044921241540011100d030016145051803002c042003040408000304a22508 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 965189163 1250 965187913 965187919
    0x616051c0302090a06030c17040b101a0307031a031f060b0f030c0304060615050a0f03110316093501090503030411040914100c180e0903070b0f15 64
    0x103002c01c54008030710380184c01e200d140205555840b06c2039509108214100344d0030318901c0012510b091a0500d00e2141e4030075124000c4841d07255500184440c000c10407041310410303a100d50760a5a8a41d07000390001c10721400400c5005881814010040e9406c0c82040d449a5041e905d80300c144030b901c0d403283c080b542180c00c0350200d882d00f0040c2500b1000340c01c080d02d500c01040b00d01c413940c0e961a0b16184004d450300f84c0c004442c00304c1c072009240446030044080c10058115640c0d11042c00e01500040302076680c0c014550270340310410408a4940d88803490140c03100215130411040c580c0e5070b1102200140c0300400a0120201049110307080c4141d20502034800d008190000d2054110366140d1546910020340000d2582070190b98010443e21030360401c1010a40217039036a864611111141a101c8105085001c0c0a92510350100f030154003542190141400c41b81103006180e09185c6882e41c5020003402c0b4041c54031042c80500c00040115807118410401074104400034209258400803e4268490040c4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 965190413 1250 965189163 965189167
    0xa0515100f0f1d04110d091a13020d140111040f06020c09270a02031207060f0c082a04060918050f040206030c19020c0f2d0616051c0302 60
    0x3450000c60010304454404441c00141c5c0c2e08800355041c8148582c40404ca4001e04010b0007006000d444161141c0301c21000f15500030b90b940701504150307005071441c030080d44442901541c002042a81c3d189810150500000040500e41c0311680003180d0081d80c448081c03048800c105000d0280c0c14013076200c0111090b140311085090600016025100100101600c0da03100700c0030f84244107003044204d07a881e4000e400e964081c1020b4000c02c42d25401508107549040c00c0c11100350409425100305554405c05a43d0b004290715080c042e0820a200c8039504080c11480b0480c10802481c42d10040004001d2030b10f84c01c03010382ca094210390300402c0307a1811215040c685001c0002d10f210002c981e661250b411a0541d03603076a9a00c0b0301d5400382c000c202c82500b907019080e16042c1d645400186080e907602044840581105030081006295000c2c2406460b000c45000c0703d6443e030303081507000200d0510000f00903904041904d0050400b01906400a0b5202e0384441c105a505042c40159050031061a00e0700758 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 965191663 1250 965190413 965190437
    0x150801020705060c130f030b0103060b100e090604061e090c021605210618060903040303021c020705120325081605030f04031a0117060a0515100f0f 65
    0xb82c1c5450300182241c0c1800000207a0407042011041c000c0081c04100030400d00302610390030300c0e940410090204454480c984111904030740351488000d8000c4002d40e451098184e40300f0309001286070302400007a04070352104404200d01c160b01d8842c40b0914a0062010006c1d40f03013015003420340e04c240c20468259004074050700c01d100c10710000c4001303941040c0c40c490030940000d00100346880c072100c40103001d80180003c0c0195242c102801030210b2403c0c0c0215900c94a9035001c6944070f201e03038407008026078008400c55840c410442c242ca9004c5010b401940e101c50754a01c0420003905100610202e9a00005041c007042d14003149641440b64420a20607005541c0d503459000c1440303900008425149040124410013200704102c42d020311000501c0703621030369603203015040700c0e1000c411900f12001d810000709444840d02051002500c103040282215118015031400400c0d001c4e01014194840051031039150711520680003141c82140d4072001407044242d0020903681c0c00d04048010450f00403500 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 965192913 1250 965191663 965191673
    0xa0b09100308070213020c0a060c050406051c090618030207120809121e0307060609050c040b1305040908490906060303030b030d05120f04150f1508010207 68
    0x100064a520900c290364503403660000401c11785d61001005665800091040425a4085000d1444038807c600a0021441102087e5494000c500511000070b000340958242c45000c80070300c0801c0030301082d000800441903102c1409031038500100c1c0041a0316058280200740d4100560401010710100c803a42c02c0006964018191141082003485582129007450709444280704986041c1d00306610021050420b0610300d481c1d030030002e03041e1005403170060b001815034018041c01d40300b0b504d000992480c5c030742000001c1110350014407500c80014170562020526480302d116031079515000e00c0702a40c550084030021b0001e1800d03082c0080350b0a8802032607803a1000408103e00c0400801043c7c041011201342e00c1c0802018010f0f00039100c54248500001455015071251484400c26000e80742c080312a4041035900f40308d060707903000c030260301c40c4002120030150b4030b0255003003031065408180d01c00e1080103036003d4415009600c0c403500e0742c2e4414840308181d80d14104000309420002035041a6482d222 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 965194163 1250 965192913 965192941
    0x307140c01140a021c021c030509030307050c160e0609180d030b012109061b0905090402011710050306090c06181f090521030d090c080a06050a0b09 65
    0x51091140003041c1c0c2c80d40f90b4000d001c480194118007110300c401c1602143d0080d5a1680c02007054510740c0406265508a8840e0050700c0c410001400110300e16250207000b01c0b1543d002480d48001409058020382500358511846801481d00c2e4413400c44034107101003080200c49018004101104580c0c0d55100341034400f0401000000c028240000c0207a440030042c1c801c0d103070f00d06114901220f041d181c49000740a550112a55030300403030041146407039660281003000c1d10400104041009080100040c0c58908001a80180306260481591212090540400c0b50030369040812110811003441241001c00c81540e10185d40d000030a042109078002c100a0f02c2011451072050114429015079038550808101d031820240d07080710007a0040c040c006200801c03900503107114070305821000c0100481150f0100c19240008051442c011040801c50001d050511040707480090703c000000e1a928240f01c0c00070624011000858146030030400c110495000c11007240c0700300181d0782480106603004807 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 965195413 1250 965194163 965194187
    0x904050a0b0a0b0607060906150612050408040f0b0712021f09080c1219020a0b0711010e120c070512150a180311060a050c03070323090307140c01 64
    0x141c0104152a80c082c2c0c0c00160100c00402038010030700203030400811086034400c0f50f40c180242400c100c00c565100200f854040c0c18440c0000040a680c0f01c1e50baa84c6066001d6034000b480f58500d14601a41d4461104200b1159413012020982c0484c66100b44042020605c840c00251310161050701c04162491440141690016040d00c0d541c012003070400122004031050000b112085034000b01c2e811a011485a100702c0041c0501f0115183c00c001d058000101e880520744d0014240c4219503400408440400c440c550402040d920703900400ca245505000c104414024a03002517501c640d0281040c4c513040304e541c0114016807003e20303024100c65000c80c03051228101d80006227425294450203a02400302a4065241c0b64035140140c010950442294444448800b05841c050360321440c405088820417110712460030b40800000703110501c258000c074000e04034000405640021403a5003c03034040304803011901d40c0d000140b40410b00900094030081156150000d007240100c080c002882c00303032800 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 965196663 1250 965195413 965195423
    0x30c020106180e0709051015080601020316050a0b16090b18060f070c0e010f091a040b030316140613030c081e12010e0a0212010b09120312150904050a 66
    0xc440762084030300a0119a00500644105000505041180c0070b21f44182e803090503c00203071441c0e9900124014020180300b440141c004d1400c04003091590382d100409030900315094022803044400003850703410994015102c4510008503c0004213010748400390540019502d10428000c07801301c0c2e2040c108103030b0b83c3d820039078960307844e43c13080704880a46010318400104004001c40001c40ca040030311035028100c5404000c40040d5594a5214400305d42440e08000040500c2c2080b400041c100b5070807240b945080035003241d1408140c0c1c01e240c10304c0301a40304112003d5182001020310031070b00b04090780d001840f045504000c5004c95601030550ac03001480242070701000300f0344100c2002c1840c0c51404c64007103c000590340f035040c0980b0000c142c03400d010300c90702e165012002c503455440c1d5100740d546031880c0f440410600c0c0d09118120b2140c1e00b040f0009a030005602d01441c0300d90b081070014007107800c2841042170712030401800c01c3c043c0b40c0d8140e0398540901961020400401c40010b40030001039004 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 965197913 1250 965196663 965196671
    0x301090c020c150c0105150d0b0411060a03060503010e030f03190207061815051e060f0a080607111b040b0102010b0a2606060a052e080403030c02010618 67
    0x54001da0501c00c035010859401004400501801040c1500818600c03205400070032650340d540c4650384e080480f074100c0d280c1202c604210030001508203110b180e01b0078000d1807030341036008000c800504a40c0c4a29403940010782c0383d8504018500b000d000318421010504095810144034192000c03ca0000410b041c01c010412941c5101c0a9000d504032600b49802510034851041d03074011820035800507440031200c4400c003000c1c0c040174030018440c1ea03003d0604c801410100d0361010008088045000d001140d02981040918100f0f680d140c4440c03005120388006886185040c91015040e40b00001d244481a00404c200f140401481140c4410300e4204030780000d100f0340480c00403401810800b0070380f070300704040d02000b086c101769100e03d6111010303407101822209083e4116883d2910070544003140c1146c0100000d00080c0f82c20300d007801c01d400440c54080c02074000001c00511400301c0d001d4041c04211070105010038503034580101d207244e484500003403200503d003027008004074081d011441c4a940d59 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 965199163 1250 965197913 965197931
    0x1061407060605031c02060a09031b02061b0607020709090213110c25090b03030f07080f03010f06081e040212011401080313080a051f02090603090a030909060308030109 74
    0x2640600043c08000c0e045813030162446011100c1c030160440880b015105810008104500078007a44040940c5540d83d490310745c850030441107020800c0501241e1140e4240b201202d03910240303d44540e0440c50000802d154249442c0180c00d00c80240c000440e80c84c00c01c4224009038443c05802c0e810f00e00d20f000d001401c0c0990101c0d10030f16004a14035224507010307154a51000d0703210107181440b08010345e04032140c0c0039070354800314044551602c107241c1c240d0130030301c1071040c1c504070b000141a0040c0034040452400741b4000145040380d100342c10038414012459002e11109a00c060392940c803642004955610824440c880000300c0001040203120f00c440000300554960b0a402c00007145d0820080c60a26585520042d900c0b500120390b050450003481d5400608180c000507448080c1d50414081c0120500345148201c1c3d009941c0c040306d040342e40030001e803a00c0340c4500000358402c4c0030b54800751200e90300034900100408201d51040e0070b620704290050010071007a01c03c07a070440e910b8440008042007 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 965200413 1250 965199163 965199173
    0x1e06011209030206010614040e0103080f091003061e030b0604050c0d0c080921030129031509010906062114040b1e070807051308030f0408070b0301061407 68
    0x1102640ca80101410100c1e04002c243c0c0004155040c1c550985032100319800010380c0d6805030003548620030101802c000100041240600100190342d081c0030114980422907012a009103c51046080000d0740c0e00340800c1404403607a85066078081100d4641c17030280c0b554844541c41200944002e1040340d560000c00c081d01300682c100d0b1100030400070280300a481448000d8085030b400c0fa80010780740140240070481000b449034204020050445c900d065901f0280080c5200d03070f20031201c000100306c1c41d02107a00e8085c6080510310959906868000003011041807000901040e031102c14007505180707091168980102481040c0341030b10014035805c40d060300141c000360030f2041c2a00d90b080c410005120611040d038006c075105200000390250083d0004c41040d41017003086900c0b9001410708000724102e01d104a0050981504001c0342d500c03015210303580070303003140e00c5031682c84560b800000703041100900c1130240c0801440803c10340e0303007150f140040241c86804d0216407000c14503000140002008 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 965201663 1250 965200413 965200427
    0x714060711040902090a060812211305010f0219090605180d0803010e01210b0103140a050105010f1502030f0a03090c080d0c0c050306160f030e03070818091e0601 71
    0x135001001061982080d01030480240194040d101341c1e8000d10b071400d0700320205d0400b16041480d51141c0019101d141e01a21001310038080d21040380d2001420441000c2802402400190380e079041c40107aa80c5060b401d511062112008424203124804404000ca581c004040d01e030701e003200b07000b050200c2020400081d414842d00c48001c02c004004000230480d0901d2204080c183c0d8211100c407038818404502d20710700c902c08200000c00786843d040050002402e49d4035510840680c68007121145004c076070722142900c90913042400341b15042c2e0010025400d140042120707a0015001031450100680c203800540d2154200034010325494419010410521050900007031000c032003540c010301c141d004010854202420255030072040001c01040c6882d011850078000d17070034001106002c1030000020b072681c2c00c00300d5420042c5170391078643c10410542070008190691040f41065aa000e00700c10241c5424080030a490140300300345c08100303099007018440800001601c00d940760541e61880125404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 965202913 1250 965201663 965201681
    0x50d06030f061b141606090206030f0906100602060f0414070f42030f09080d050a141909020d1b0504110a2003030106080405071406071104 61
    0x301c414140308400b801090b40c401000c1010f004400354240c128000121000004201d2a2694001c1007103d0040031070340004d0800c0d040e2044102141c9904540c0008140d0340003110f281d03040d2140b86040052040c024408903074440c06445d42800d0050500e90020340d00c1500800003000540404081002d10082d804404413030041c02c0202d0380c41c01c0d1904070380141141e052103900a01540c001c000c002d052144262062003880e8400c401c00310b034540005940d81101d407018548203040c1d88100c010303800200d5000c1c0e0403003107000d120081e544840140d504030454900400504a03540b0300b0b08000080503034114001d07009074413504049943c0581a110000030101881c0003540701582016000800c8280099803283e4420408500b120580d00d20034042500c0c0704200c810031400042040c0d040d00381c001d610265102c0c116450b03809505003c2841c0a245070b00c280c00010110f88a002003000704402000a42e01030504d581001d55034080743e1005c03034000d0290290050808002040d07030030700c0d03446551001c114 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 965204163 1250 965202913 965202923
    0x18120c041b02011b0f0f030b040204090e0f06010303140c03040e1005010e030109050709090c0f03030c02030d140a0f23041d0c090d02060c010509070f1205060106050d0603 75
    0x100c0302410301c0394a51a51480c040c200903509050300090030702007103054480c40382c00039111070038a1505010202d82c03907008a034044003815519102e41501e5226031018002a1403030b620005402c1050100051400504000038922640907400510000c2c0e40092101003d8844084094946282ca2610784c154040c0d60011944035003190304210017a8040740981044400a0700c590b013500c010380742414241c03100d1010241047c0d021180400c03005a4591103510315501a480d8480426103480215458a0890303100740c00180c15906140254582444070360b25643d620705000904200b004054280da00411000509000324007064680c094010b6035840d03241e08040c403105002d9400e04003a4641a0064059142c0d010900c034500c55284a803102418014542910060300b802c10110812100b481d0505e002c0340c00c82818008440400f00c24010b40340904005000b6041442c140090404a11610b900070300b0078240b0b6002d12004507001103096815112103141280d070303074141c450030a00074158a1380020a = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 965205413 1250 965204163 965204171
    0x17130f0f06020c1b041b120e03031608180c0108060402040915030311030405030a110102030c150411060909130303060506121504021c051009110315010518120c04 71
    0xc0010340129403c10203c244444c941410b444000c14071084608201d000003101d40800d40302491070707000d05d090385000c051902001c603c0c1c415441801d815500f00b5949040c00b5221000d0145066800101d0180c0c4403890003001c40c4070f403a080d06160b40e964104900141800142c07000302d00703180c035282c04450251145042c148000401540d4101c0c1162a603c426000521898000740708590702000b25401c440f0020028943d03840c0a4035080b0b030314090200b805040d4031040101c3c0007081011701544d04604242c5251103054900342c10704007030441d4040c02d03c512030401040003002650b14445605c2e00004514814582252180380507401081b50f038108560010021032180081100300210510030150506580344061820381400242d000388400310920810b429200f0328240802d920031680400d50702032040990ba51540e0400803a1000c02c01c3c41c1e00310030000200162201981160b40401c02d00303107025440c0820141056003041001a800c52042c0038041388983c40b03c104020b904054000204100 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 965206663 1250 965205413 965205427
    0x427031e031413020f0d1a15010e06160b090715081e040f050f2d06060618150a0201140c0d0e010b06030c07020a0806130303020c0102070c08010c17130f0f0602 70
    0xda01c40205001e0310511f2004000400d10a00b00391040020f030b8068407000c00b1140d1f0705041041e10742101002d801c0403015442028003040c01c1c165a203009002c42405000610b091000c11060301c400303c0c101e0014401b042c03041c080d240701d4240c0070003e000740327001014009444070724102c01c2d0354030440f0014206104003458280c80200c0410803442280d00c0040c0c580c2c6004d000c4010319645076034403a0342803998100800045481c240301c00141051083c24180042284083c00014040c8241c04401a582c3c400403a101540303e0302441101210754030362181303021618000500010901c991000d00001e59155441c0113000c580941142d4046400142013a03108e00c2c20003a01d01480e04001400d034440c8800c100000340c010350200d1007601a4552402c141c61005c003984064010b503110034255407166601300010030105100d012414050449500040b800c2d4080c2c10b80100090b4072440c2c40009850b03c1e03000d010344545030110031076000c0e0348800d224000030f54074103108401844103c03014004500005240d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 965207913 1250 965206663 965206673
    0x1e030203130618120b07030506131e0501080c0d080c07230906150d05060f0319030228062f0a09060507110427031e031413020f0d 57
    0x40c5444658401048030165614400003140c80c100d800503085c000384001149580c0d01c0781d04441e034882d102400304103000907420000811104e60103c00d8407992503041340c0f02c04d40301450003210700518000005110b1500f4910000b4000e40c1801c0c0300515100740014103446046c001d000034030003465009900324611021001507800b03034a40381c00c094170449188000540398581001d80ea8400307414103140c50300702940c03000b118006000203802c2d00e5011007804050250ba0703400700001000880c15149040c4102e44c82d01d0064a450345010480c0154402002c160318504e00000180700640c2d04110081208100c190a240c101c000c800072034410000c191000601054500e4014503c0003090303551121040d6072018115010f0003951801004c2c0340303008101604c103151030740007030344141c7c1c01c42904086070071000c2c080010581c090200f1804a01c02c600c84010f040790070307402c40145600034201400700038090340c4c0320310441c0f40003002c4000d500c0400308424299101e1800300d0030080c034090100300c0ba40d5068100 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 965209163 1250 965207913 965207927
    0x1c0201361410081b0d1e0c030605100c0b0a02040b0712141e030702010b1c061a0303030403180b120402040506010e091602010905010c0e0901090501031e0302031306 72
    0x540d018004060304240c0151051030f015114080c0700e14208039110115001c0c1c0f485911a0780c40d02c1e0310680740c0b42d0120358408122118011141403600008000261404c0a415075640c0c0e0300c1644105030300350001171507a0b0440b07100c41e035041d4010100d041aa803600880c1c8024006d90b0014a8404001b0850b1010440480f10102413001035403030345001c160300c12100d44a030703110703607003044000198071b07108420202c0000c0013445c2c110074140004202182c040d4040303041800c0c0d09404480c8001c8104011040c070106100380241700713501e140800171301074449022940e28440a04003d0401149101d03120300545246101d1000c1c0c92003260060b40c0322400c0811803580d0f2406e5400368442c42c90a40890555801850740c225440d0f400742192505070f8803800703c00e10381c503880400c0c2407d41d5220749056001900a0ec10003a072007006445040c26000d0302e01c24003807007a405804c074122051400c4014070100e410f04c0113400d01c080100c0c440c4000741503d07140481c2103002d10280000e012400c41c1300811400c1d008070f1 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 965210413 1250 965209163 965209199
    0x905070b0c0f1603020d0f0f150f18020d140607081006020c0a050603070210020d0509390d080c1e070b040b2101030b061c020136 57
    0x4440381c1c007142c05240c0c0c0c0c45002d484842e00102040000c1000103050580c06180102d020740b0300d00c14008201d4851034048400540c080302c00200741406100141c0340c41c4510b0b0300110104500700002104011010b01019190344064032030300e9504181410442e510311241c002c480040c0a031a803074100108007525108065800122010303015030082026440020b00300607036100141b200d6109071030103041c0081548081c1c01e44c030860003089201c21161660340003e103410703140d0080000b40b62130020949400c1200e5000030b0100c6c510200c0481c2c7c80405d502c1c5400340400c4414030100122030080c00014104070072044010640100440c40f02c1f421080411030b500e41c0f46800303001002007205441280d03191419402401c0d02c000d002e1100384481c040e0400a020494002c3c814919102d02c912004148100309900440b98503851004200450510389101078100c1e03203400c0c2e10450901103900181400445404c40005a41d82512602d03205881c0da5600e03885444030007001e500c49843d61000c03035605050070 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 965211663 1250 965210413 965210437
    0xa030f0809041803020a02130b0411090916080109020313060c030e011b05070303021b150115090f050f010c020901080f46060c0e0909011506120905070b 67
    0x200c440d03030f40c03901100c1c3da07242d80d41603000e8a07030a0b01d154204035000b18959019001d075035580c080d030615920359114030040c2010040160362540a440c0400220250040401d0044403000e04800da44981040b0b40350b041d620103100246c1c4031359500411180714912944080d105070b00308403907665996059130101910640380c0001340515002440c0f94034004007084000070004904110910102e4402e6000e00750051100124039507140042403120300c1e01034401b408200075446a001000241074103c640890340605003003000d002450044103860b1a001407040f01c1c041c03c480c4421b84580e80c40b413440c001d1407680c0249601e5640d40c559400c585d545114000042c000e110b2000466102c4081801c0c45003034400c0340b0112034004c55078480b165101070201c1c00014516400c0c0707101c0400591a80180400f90285641e0710342120203050400c40c01c43c001400200303180c2d1520306034a16802c09501103030f05071020b608100034590001503103000107041c0180d0190290090b010007082c0e1059060003003050600e29 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 965212913 1250 965211663 965211671
    0x121213080d09030504140a030308150a03080403061b0e0f01030b03011d060703180f060903020f0d05030a0501120506280608071a030f1611031902100207020105070f020a030f080904 79
    0x600c0901121f4891808050045202e5900041c0c5c242d110105130300030088094082a4050307602c0e0f8030106a6080740c1c104541076501c91446121019407402b031034508080f01d00d4040a0500e086010030042c140e804441070405403240310303241c1a80c41c2500560785481e0761400d0340e1003c1201c8241070782c032410306923040c000107030518403201c0a4403208041d04003000c0d0402d20004140c4a00e980e1000101052401203056024092000807075250501c01c0c000f540b69991a4a59a494081803031012075605030020384100300109500310200300c00240c0c1aa000c41303000c002d4620130050540ba491f01d0701b081400c8040044c10300b0030115004402003005800c5a01d2801c4101c42c9200241c12074442d40000c8845001d0000c5460008004d804d00d041c1000045071075040c8072040340e4010030103a0465014401c0455002286041c030302c03505030304001d0500b12540800045080c4095540001c1c501d108011014105001c2403071200195615210b08100441d407100007151003910916001d0703c41c0d04000800c510031450 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 965214163 1250 965212913 965212949
    0x1d120c0405100302090a0e070e100609050a1203030b010905061c14060603040f03141b1002030c16150c230310050603310203121213080d09030504 64
    0x62660720b098a500400302c81d44c1d582c1e424144002099045c5111009105541c80010103030b4a020196004440003c3c0c142e80043c1854000b070030304030362640528003401d00b0b030300100400100520f00e00c0c44a81d040c030300030450401440049420005a411140e448800080d0b441d420035103031054a5000220100240040b15030502d10800d26001120440c0d00001e0800010700020115074020340f0306031013820482d0708031100c0d81c480301250b0400066000c0305594051041740d40728040100d500002c02100c0154a0741c5002691405140a80c004103c0c0b42440440700e03904000a847d112610b81d08100801c002940e0f490900500c0c11400090200036444103200340807a89a200007280e1080e50f600f50000d1000b40ba003030500011350300c010703c0361041c11503e1000950180c41003000300c4002100078050301e000c1981d80100b60400030405280c0c4050b03c002c12041c00c903840c1d06100d003a03000360404a80c01d8201d8003410042550b200e00c49842c460b403441e240c402c40030550424060019030700784d13411000e080c0ca0 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 965215413 1250 965214163 965214181
    0x121a030601080a060b0d0804030b040602040b040f0503010e010c091a0909160818061306150303050a03110301140907050c070b0a1b0309230405090102070b070c0c061d120c0405 77
    0x41c1b502015250f52800c002c10700104200c14081038200d032054000510341503848008501c0390308250850f100e15002e11104016510b0240981100103543e08004c03c02c0100000f13001d8590259485042400b0302c61082c9144000d5000003a60010100504200c00724645128100a8041c812804801148511000c15041c2860062a88800c0001801040c0d161201c0044907003001d1801012202e6a45071042000c14503043c0b03001900461003078644984426851001400355072401010403c80c04040c80104040c01d1307122030b480c48440d0291600111500d81e004211024890940c20240602c981e03000040c420103c400100421140390b40c49400802c0f191800d200403640700c00c0082d002903080007040c8469030b45147c84451003070725200c49443c20034140300420f00351041112900866507010030308405110810000c50f0340124030307251480d082043c03941d03094020340080c010107080015800300556101e51401c0c032680502d400402200741c004100c08107640e1041d0700c4000c24003d50504021803100c203 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 965216663 1250 965215413 965215429
    0x2061303140312070503101205070305060703020906070602030604090c08330a0f02091203040905090a030f11031218070801020c0712260d05060a06121a030601080a060b 74
    0xb4000410f034980d02e0710760010480701900040e2055200d9030401c000021060740300310455122500c40e001400100d45141031403820088000c2c0700317400340341c010004c1208030340e0ba17282241e0b10117030304c0000144c681c1c441101080c002d0031030000062420541d998003088440c03001510912600000a00c1400d11414402c0054948162403502c100154801e001c1000910940c2224043c880c044200504210b24080041c0d544410b00046c43e03095000090181708a00b114041c3c2030340106c5220060a944141d940e004050004514241c01080508c41c8940c0082c1014022940ac4803194503180d0490b08003009088080e22089002140d50b00c20344000040010040c020384103c015158084c0141501d000c2c98001d1249040c0c0c0101c8442c4006881038a500d0f103101c2e00d070090840c24492003170b00c6407051820781003203c00180c812441142d100c1c50070000306500207501d5504845c0c80b080031800086414910241440011006515000303440c000304001c8070008034143d400e8043c041c1401101042800c0c42494 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 965217913 1250 965216663 965216677
    0xb0c0702132406050d0509011103040803070c0f0b01082401120318080c1c020618220507180e01030305130e09011d030313170403020613031403 63
    0x10007076010450354850915030241c4940550410100d00c81c04640c140524500525040400402c0c40810800440640d0344950381d40849110000c100000001c0b8203400c0da8000100000c1c0318200000000b82e01c148540001032100340e0200010004071101e03c0e00c1c020140c802d000d0310140b0720070b0f0712510000079040d000c100032240344206d2543c0d0030303400c102c06800f202400800c15014890741001408a05580d086000000c0250300090101e40100108100c4000404403081451402001a58016075240400c50701c42c901124101d6600401d07036400709200110150078000b140100c1d00c0c44410180786600910300c2001c07145d890800c440d84c214500d107103100d4a8010384013104092001403001900a81c010000981c80c102000e44503952812000140700c1e048540c018241d44038444060714a050440042d08900000c000d0350a51078000d030100a48600c00502510f260020340010030050038000448000e15005070100303a50780a10f141d00740002c0d0300c91004582d40a02c9010f41d02101001109031a60 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 965219163 1250 965217913 965217919
    0x81303050f0139050c0f0a06050106230f070201030b220b030102040b0403020909150c0901081006081302060c01020a211811010e13140a0c09060804050a1e0b0c0702 72
    0x705003d6a0f4215260b400c03400075019039200da5510449540801c01510391001c0c071420010403103605000c0003c00c507621143c02c120f54116540710300600d60b404803042c0c41c66800c2c03406055443e40c41d0381c00103c0140c00d9841480b0341008650110421f8004829908400d80c11494410b00410003a40141401c0703200360b10810b11804400c0c08240014030b02810920f8020700b40700b0480d440018112441c420701007042c0c0718500580c41c005011006541c1009007076038403100b1011044c0216107014405404c0d020010000542042881c040c0380441d916078040e01e100c500000b008541f20200040040e04a818204016200041d807181c450240e020301d029a5003100d05494202e680c0b840b4695030303501c01d031702035403840d5051003241c42461420f515422000710f5a04400034001c14000c1c0c0503803651303c1107100030f003507030324903900300440c1030030007500601d841e411106103161451003641e0b182042414200c40000040903200809100b0815250100c107402419006e8020401c0503180c6804c2c0c044144500318000b50 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 965220413 1250 965219163 965219261
    0xe010b0a050109031106040806070504031505070905061e04180b060a020c0603090f030d090615050102120f09100314010e01050a0311180906010f0819081303050f01 72
    0x40017a510440b5440440c1c0041e18050400351a9254203080a004540d08400500003107410014080c0c034035402c181155031104200304500302154020417400150040724021280050000c044d080c54208401665072181821a203030381d118412010300401542c01885540d0808040b524580340140c12a07500c0f83c49270f0001c08284040300c0a118540d080100382c9415802104102c0109001c14002881e80d20000580010494110301e001022500c19025100303030a15180d1083c071441e60001028003090b82c0d1107116a461300d48c964101c580038482c20b1106500880341030300125045030540c21020710030441d00c01010850781c9485095147d00e6017485550b0b4008a008010000b04801602003c64144040d18045200800798030080c424a8182c800380523350102004100000e1800c8580e4003611030f08014000d2084111500001c903100180d0140051500251300400070717081343e94074002103074000e050780c10503140219114001d202620100610800002c003091042e0050b0680c8a844001c289070b2032 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 965221663 1250 965220413 965220419
    0x203070c05100b03070e01140f030703060e0303070311032a0d1401082a1003021207080412030b010e0f0a120615050607150b01021e070503150f130f0b09010e010b0a050109 75
    0x882c589c00c00b555050f000310f50006c4082035031801402d4504111000550340c03400c1180c1c0040031202580443e50b40300500703105000080c448080c002050710740300c64410071a0351248029524900c201d6243c0c9042610300307940350640c6040798008504070744052045d82c46031301c1c407900c01484c801202ca044000e004524442c0c103c5500e070002e4805013800f05458010300300300701c0c400301c1d02c1c18820030350300240414028000c01c4100080555141d12050040c9030031300070f13003000c140064000707580031010600c1112403020b40c4a641e00c50380d415000400b0348103659549002c003810080b0013000c02041000d4061900311012466041c040102e4000545c03107440c1d5030001c0c0480a884d00204001c151150450044c11205030b0fa4a8851117010201c200e04d00c0039113070240c64041010f140245412584107000140e208111079812404411948214807000c109a08080f41c60146030700c89400000a203041900018045910750541c0100036402c0340070000c001860354801000000c000c9407003043d00040c8440428 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 965222913 1250 965221663 965221669
    0xa150b041512032c040e03130b1e0a08180a020a05010c050c0303030a020904150b04170c030d0e180f0109020c0c18040201081005060301090203070c05100b03070e0114 73
    0x1150182c1c082e182c9007040c0c50021340c001c0d40048021104410310303c40804a60700510703083c4100503401c00f84500852034011200000d03205440c60f44110800304001052070040075104d070303800c0270000c41401c101f0390b9541d0800c10f014000075030a580200741050001c420040071080044c0c80b510107078008044003034052804004483e0044001c004aa80307014425050710b894900304041c600070541640c000d030b1100c0c01e0034244002c680b030003180b40c07580f034008031801c0084114003000c840031b664000c2c4080310341280e40001c00d0700d007000c0000025013501c43c100014100590126000100f150101d50188101d0f003100c052038011002a1900841440c050004002642240d4014001ea00340b40090b94a04c0e5101000207205000308203031080d02d80c441c0c804000071981d001c801e00d503000c9520046140c50505110100f4045e0205015400350103a0002c040b031207090041400c542599880021150a41c039042e00740e030050040c800c5451300a109541c0c02080c103170840b00741305068940c12042d103040120440d00b0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 965224163 1250 965222913 965222939
    0x403020907030e010e0d030c02070e161701060816020a0302150717010e040320030f091305090d121413020607080d021e0c060403030b040e0a150b0415 66
    0x9960241940c9507111054050f081c01289484070504000e840c0e13006800310701905a4089409000c01c41d0012541030202034590a4501d410405a07400624500e03644001903613801e8a407425030a4804100000085156104c081b061142051150355403541c110010260303550b03281e0580090258210001d03800913400c40500e007551003030044c6007003a80100d5071201600000000e030014683e44a0bc03c01304402e1580001c00346004000404c001051805c011040c0c03a02c03070150030000341d120340300022842401e5540282c07a5030a0180070004200c281044a4860b94400741c65a401c00440c01c50741d00340c16450311070700c5028030b410302c400c11421030b0303aa40300010f141c4001ca918040b64041d80600200303020410100140850040b00f8600580d81c01e0031524803040380c3c00080f040ca4080a0402540c81d5844011402603001030703240c08c0101e03050000354005005419210541d400500ca01c600c4402808502e07000e400e0100c645482c10828141c500c400d20040c6c03500f03600501c1e01e00400c40402c202c58250415 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 965225413 1250 965224163 965224171
    0x90c0509120304123c030503100f1202010f050a09211202030309010510050d060b030f0f0102090120030f0c1009030c12030507120207020102030d02041d0109050c04030209 75
    0x4180e80c80c00b9181c1c80c0034601e5003132424094880c603940300d052440e0031405001100c20003841d068900020800c50000340d2030303108140001400c1000200100319241c5241010b0b01c0038142110041d08401d4480d1f1204d256000c41e280268009552079865510903401001121030101c55a071328030b4522420800e1208603564040d10030b0b5a10048030403038a01040b012a0000c8291200f54061030342d07401c140d172140b800d484e0050200074019030680010022075460200c00c0d40c0081c4c0c8854046140c0c05c0440000c0d00305207140e500c07003880307000e051305141c02c03d08103500501d8115030036264103280c80c814213843c6502214028504420f80d20800210000c0e0411030042d0508143d22422100c5640340c0b02400320548050751401c0f00030400b600a04420400a441000403054031881c04001901d4604001840309842c01482001c20b540010300070156403090084801d02d9400c441c2c00d542e903955450780020788500e007103400c0249a0f9440700220304008103005203030203800081c00507414181507800f044040c0320701030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 965226663 1250 965225413 965225449
    0xa0f051603090f0614041a010518130b04050f07060302040503030403062d050a05010b0a0c0201081e0f0105100207080a060506012606040c110619090b0a02030402010207090c0509 78
    0x1c10b90300003c40c0380c007902041700c0307115a41911a09191401002e1440c40a60319000001c000c00140402d1301c8a211542c110042440303445c031603031580817034031180100b16200a005104e040701000180a800213415001c03641c02400c692410365950000c0b0224003e40c09020f505410420003000403400580001c2e550320b0501900c4a2880440300030200001c900c1020350160030340b54010031014140b2407003454010001e51009038a1f11100500007400d040300340030003d062003590001f0802151114031035942450000d2160601c82c02d0501c480d041000d424452140f1a101119408049900c04980b500840d06104010161542c4581c0c41102400d0024001c2e07041210800c6c200c1010740302e03448228860656104608154201030083c4816624100e2902c030070702c5966004c40c0011900010055400700303911485500180420b02d07068060080c010340a0100000301041c040c0014245e401180150700c00d07021a80c405945225448c261081800082e01050040c0854071590070491a000c010764111 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 965227913 1250 965226663 965226683
    0x270b010e10081f1a0612101703031f06051c020d06060503060103060611070603020711060a081009050c1803010b06040807061b0c1208120c030a0f05160309 68
    0x403064149080ca1414409501d0030143c01d1001c8603030114419150342c114050680c403900c42e800c1c0b000c1825072244c0c8040c02681e03080300c000290101400b40b01000509044411002e6038609036100701d540c0d410a950201c4056a900c00210380c07801c03101030350b034200c8080351540c1e8100860101c60382c072104040f5041d01001038080013138640e0388109100342c901900181e1183c949a0070a40001070031119503402c030300103204022074107120301000003910b5003c480c298a00075a984042d8541010140e11b9009280d40010001c02d40007070f0690840182403040781c0e50059420200d940d0120303141500c1060301d02d141c5001c4200460420f0b41c4145130080e014243c068000701d000314000300854440d520a07070049400360005e040611090744d0005010a181105e600d5001c0c40c0102912000c0d144140780c4100941c1107031692501c0100000030f0b0680721500010251104149000c84102009a00417641c05144030714155488204207290310659000b1000080b183c0c1981800c0340d002d6006001200e0295210f1181c = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 965229163 1250 965227913 965227919
    0x34020d03050c16030b1503070506160503090a03050106030302060c0304080a0f05071406011403010209151c0905010b01030c030e1f060f140f0a18090f060f270b010e10 73
    0x11034003d01c0110701c034040c3c0d00303030514003201c54810a807429070302581309800400041016540c4e80050342c016500d10007805543d03e0281c501249540319a0490342d4101080300e0001051060640c8414101e901076020340e0003a988400e00f02e4060310003100c00902c241002d22000302480d03c01c101d038174800074450030901d190284988464507440070b101120388596104800501028003d00400c0e00c8040099000b03504102066000900c07072141320300e07102150320b030101c2c0703500000e4007040d141451601240c200300f1200c0b400e402e000d40070380400a00039000ca410420b41c040700c3c80c13080c45006c2100d86444090101d000c000d074100321803c80d00d01008080c0310749407440072075240d80b91070030740000f40030301501683c011075220244002903080300d186070311803054010704204050b89000c895040711a00b00000031801c2300c0c0d15140130b4941310524080c100510700000e0b60f5840540340e00c0810280c01c20f80b1010480c0c071a40d0003c40200e010301800400719460100100301c080c801a8106403c00070341070340114950b403 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 965230413 1250 965229163 965229193
    0x1031e060608010e100c02030418111c060e0f190f020c0d030b19081002070317090a0308090d2c090f0a050705190f11010234020d03050c 60
    0xd00101d9094075400c05c92000308060901c0c803460001c8807540c00914249407614410941c411041060410740c603444540741c5c800e80507444c00f1103035003e101c0d0b000c0c0900c1e9500800e00000a00c041d0081d1a8001c1040001c11407100c284a0124818144914008003500d10103a03c0b0707010706002c008200c00c0a0b02404801203184040c00305030f840003c01c1d500010284a07800800c482f03811003404114001038003d40910451001080005128044403400750783c4400310b240489014844052284030a04c200080c0a40c00c0c00100b4441c0e002402507a5400b031503114612601c3e16261840c211002107107204003101402450031803401400b024208642c2074052016000c5070300c0e65401c031844040f82c0010343c03c00080807800c3c4500c3c1c0d000b006920b030040c203050309140c120344209000850403090102d010319024001d441070390003c4d030308200c0074025529465101c0d2402000c11034542e4840b6580f035400b02040900744160140f4500d21b800a00d8a0701c05a011789054809500c1402035140c1c500440d400540e01030 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 965231663 1250 965230413 965230421
    0xa12020601081c0320041211060a09060c05030c07090b1e03330108030a140a0801050d0f1704060e010c0209070323190506091302100512090307020906060301031e06060801 75
    0xc6041218040c01f03001d03e4801240b0050140b000d02c205401d0080d96a0319a00818020680d038850400349140ca00b203050007480c41c0180c2828409900c1071031800f0901400f9074010001c144004e8424002c09103105070032091070800048a15095884000403c001403a0014030400f0010924140b84211110241d2a19514402d8004030b403164000191064000d61220055107400059403006090100c6124018151501071150364801d2200201680038010b00d0700300a205a50b112010032042c01040780300d03000c1c5402a102c1c0e88041580c1e1100b1719542c0d4040c480e90fa102650003052161180d0380c500065000348041c8450311604001c0302c80c1e11501c0805c11010f1030050700410400c0050451120440c0c05071440140700d03030f000328941000e001654001a00000309154121800031110791701c41801c507014041e0002d40305030160303080b0500c13400d0840070009041c2c1cae60080d06da099659841e80103002c090f02c82880b0082055044619640c051881c3c0c105507203900f4420240400c03026070f03c01d116820f507 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 965232913 1250 965231663 965231669
    0x110105070317100807030b090637020c0105040b0411030706080109020304060908070f02091303021c180b0409050708060102060a02090d0213020904050108010605100503090f0a12020601081c032004 86
    0x511500024840f440e5010813103580e100c0c001400b24240c403d0300122b40d070035100140c1134a004911580392101202c081c0703070f010346141880000003084246024200f00881c4c2805641c00e41c2d107085640140d000c03504010582000b83c0d100c0d5103403503440b6440e000300c483c000d42c0010000d0b15440d5899400d00d0010f181d40c001004600e0181541100044960040141003c00506041c0080307010300786540000340c000c100c000614000c1000031403001a4580300b40d40c41d000072000c018084114076008502c210030640030340156070620000f00f0565540360000c0d118400e055580b640541d000c1000940380c0900e0760010145039070080e00f007007050b46a40d0301048529010910031182c0c140c02154981300d82c141442840c0c01800190024840180382c200851516826940f8480400c500040098150041000043c0c101218007044030401d61303039403c0001d12805a8061140180112800020a00300001e40e604007100e49142500d1100d08a071020380003400c0a1040f82c070701645038503004446919002c090001 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 965234163 1250 965232913 965232923
    0x4060b03151c210e030c090c0706060803030c0a080c03010509011e150306060e010804150b060708040803070210170c222301020a080d050903070b04030c11010507031710080703 77
    0x48034803d40e41c054461a00365440602903489030782082d8181c1e4420104a40043c500f02096665070290704051002c3e003c290821041f86c0301c008103201400712508014040380a156544139880d441d4120003980c640b00038440d07103a2002019005224000702840c18641d1001e10703800b2460443d42d10750203000300707001004290000ca662180100651074210390b003680200c00902e010352482c0381c1503a448070908040090007107020740d1410443c10f01d80f5450100c45139035420600c000d44a0f507a40f1001030396903200410403402003640071400c0803894040c0c03114180c84002040388004994503114441003d8005640100007084c4003d414840000d99810504c0907001d4001c2084d800c040808428040c0e48d081502c00b811036200600c920081b070904001c0e1008415191004030b041d8540500442c51805481805004000c24400748001c1640005042c100a0b11031071117540902513040065489004001000c0d0200300071042c0413104400a640380c40d4407009004604003d01e0701c8070165840c01e8042c0d0000c6070 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 965235413 1250 965234163 965234213
    0x9150a0320191b06050627010e1509010824041a070302160507060207060e03031c060e01090b1305010b031314030a03090c05040618090510051504060b03151c 69
    0x10550806031085140021882004200d0003d1f580051001a00c1440380c2120407a11314040746054403060180001e420000f0007501d925612001c4903070b01c1e42c2c0c2c16103188400b140b0111031484003411154215101e00d8120406950440d03405540c56138401d0000d04540406900300a02009480c2e9200741c2503075180590700070070841c3d0809c60064a070444a8004e442400b000a480918a9030b0000440e44c2c100c10130030004181702b1038000800042c1080d0f4021317088030300ca14000458942c849511169003204101d0340e01c021a451003642c1c50455000703004551000724100000b60307a034404084120821442203040e010124907410b04282150001a14140026244d40c00d001c18002d01c64501005008100d504010503450000d507060b221009810050116868006060038460b0034003255030100d809902c1440986080041007804140c5c0c449078910491070a48003050301d10982c07090303a214070f14681e031888441422104101034a1400d62600e980880c88100e0032002902d21809094901d8848901407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 965236663 1250 965235413 965235421
    0xb090121050402280b09120f3d0207050f030406120b040b0105071203060f0611060f01060e0d0206070219081c120e0309150a0320191b0605 61
    0x4422080c00313003844000c1d035018112000f2040e07114250081220541084140c0d940744410208008140300408070703205000b5441c80c5149200301051126034202c0900e207000300e82c040720152040b0301101782c030100000d02d84c02959400ba4440d41d4010404036000d0800c03103015035140040c0340c2c9503500540251001511031000d000b1040c145018070340700400708403010f01880249900007802c3c0c0c043d0707031130180015044804002041e402940b10802800030919504071807034840f1005440903000580b00025441560b00180013130888a5020381650030075a59132001152481c00c00807903034030514059a0091082000a00603652020b0459446803001c16561944ac68012400c2c10001195030030b0310754414000320707080200e038042c00e02c0b05818034492000030b5081c00040d04d1031840c000c801c0855000300340840c04c3c00d0507041940286c580506a50b0302030140708002c041980703005e21450b42e07101002e0780074405c0c00d0405082d1a2182d115403042d00d890303c0c5907940300c030314526440603001095400917554010700c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 965237913 1250 965236663 965236669
    0x90501110102030402030a0b0c070605090d1d010e0f13020d0f110403030e0d0303270605060618040506010c21020105061203031f0b130e1602070b090121050402 70
    0xa800c0303051248000c40c114038041d0086621010701180c01040c0b421039170006100c421001c0c060741e000ba600706808001910302810f200d91f81c2d8000c99250404940e01200742040020f4580b01607907012010f81d2102e100318100800d1003400103884601551200000c000348414404074409004a40340100b00410b0038242e5500c5101101c00952410b034442500300002e001207030300a101054080415620f041d068221401c0440041c03003083e0780e1000d0a00e074024a592511125038071207103200d0040104000d952203a0007003040611803000c0c11b1071009040000c11046240c6a80000e0380300704181800c01180000d075495134021002d580c4500550044003144c10041c0e9824890700394003803425a000c1036400e10a000d07407540ea0100802d00d800e06804a20506442410b00b901c1d24010300c01e041140b522055106980b85410980340a1390307000000503000108000784140d140e078601300d0180c01501202c0d0400c14403a902d5400014201c1c180482c090b40d2800f51060a0000d140f5054400c4000405042c81e00c10 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 965239163 1250 965237913 965237927
    0x90c090f09020909011e0f0305010c0f0e030c011d0907021506010c0f15060b0315091f0303080a06051011010f0504050615041103090622240219090501 66
    0x1110041d284107000b01605616a107031440c2c1501d84007a02d42107403000c261514101c1a086030030100310300d0030a120001c05c101054200e240e50b1421620741c0030540294810440307501c03032030003c0c00754194011602054035501403814203003c0365a25550804000d80003000c01e4400c101510604010791100381c80c4130b140d02029038556009282441c01202001c5151a030150320002481d0182c00c0e00080c400c00c884d807280603441000102032407004503880c2e10703080003030000001909807014016600400061844c900000c41400b40711160f44400a0440c2142c60844034414002c0641c100039903503107004100c540e184004007010002e140c0e00d00fa0703042043d5002c1402e4030080ca001c0c2c9011802c0000780700c0000c6000c9482da03488030301302d82e04481500c0ca250004000e08600c000d42482904008180007904002082491003800c04098440301342e0088000c141e0005000100605841034540310f01003043d807007030491031024002007005400c0a00014140ca004400c0901e00c10200d154810104141d580001e8 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 965240413 1250 965239163 965239169
    0x20a05031e060109140615070c0e09010b01020601080a0605220605010f141503090c0a14180c0711010509030d030c0318050307060902061207080f250c0804090c090f 72
    0x390501074003240001c122440c0401500407480347d801004903003180301211055503840d036080044890960b81d1810480000354040e120f00d00382c2e501b03080711360485500000e2458125010800204001800b680b0741c0070080001a0a05542d43c41080c500510b88403603000b0044002d00030034000030117514081d42502e10440a030310008400030f400c40c19080ba46c0e52011242541d840c0420301d29500d58503100c190341400c100c510b40542c0809402c101060107051031000b180c00d000c0945041c58010307d121380b4640b440b50704968506911101300b10003000182a41021525014181481030a00254100203420401a0b84207040000e5a400d80d00852590600031240d094110560b40c9000b83d11a8481035161310400e08050681c4c0d4940c1c0401c0d0440d00c860b812034000c083e04500d07100550800960040002105840d102559201180803c1c80c401c1c005001c141c0a80c501001d410a0808418007640c030101340f040c054039400340c10701c03000408501d01e002d00300c620742c6140e4035519894240511503801941c150 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 965241663 1250 965240413 965240429
    0xc1b03070608040308190219020a0c0504021224060c060604050106320f1207030c05030c090108070c06020a03060305120c0c2101060306020a0e040c050a030207020a05031e0601 77
    0x1803e0101103074000003d160020009110340e55507044d940b1800002c2e11440140701c410342c4442c04040903082d40071854003820381c481c84d9002201d41e50384003040246e000d80d040070340c0101940000704201149400c0029450310684683d060008010360000b1060f0700180b06c800300075001b00081040f0780c5864420b543c09059282000406ca001d040b40c2c00c200d00900482441580c40c280c2134200d118420f2000399400c0e0040c0241161b81c03a019901e05184071a0141c440f03002282c00c004046041794013541c1030300e124000c0d00350b40c1420441294011139240d0800b0300140144021103c2d40000310742640020503154019030ac011401074654a40340d4500101290400b0300008213104c01d101e206004140500b610100312410303140c0404150040819107000d407000768056203410400000c2044c1c5070050401c044150312000300400c8124180404c7d99800241000017031001c2144010030b50180e400341c100e4a0002e04a42216501d1f1004245480030303203401e40510060a020700402014100902030142c0600 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 965242913 1250 965241663 965241677
    0x905130b031c020c0409060b1c1e120e180a0c09060206130609050f01020406030f0506190302040f020706090c150203040303020a0f141504030905040905030414060c1b030706 76
    0x2c00c10081d12920309481d0300c0c1c4603a45809002007070090036001606010802003030305031000540c0613880040300380d5400450b01400321040e00141480101c41c20380e2415084100d0b40f004540300d01e011101c1c03a1a0916140d0300c6009203141c0e004042400276410b100c0e03010345074000755030103c01c83c0c0900291010751040d411540540204a4245103200c4810021030b0701c40c0010034044810b18000d81020129100741071503604c0403d0000300710f580b40d000211750300e000c0002040395480300c80600c0360103d5000f000080e0001c2700d080400046c280f5901403045403070301c4040142030440c02c1c0c0e0f0352800d41c0c2c406002950b2022685405010b0344500d4540155a10154001145440c0c5182d80103500c800d20315000ae0f0000d0454103890060101c1c2612021005a0700c100799680c02da603603132a9416158003501c0650010b030001c0000704540c105442454840c3d60890001d504013841e0295086a26a110381d0700c54019409214090305481c00f00300d1346046c110900d03944008401d840f001d00d844c2c155254480c0c0104905 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 965244163 1250 965242913 965242963
    0x31517070503330709030503121005010c0f24020406030501031709151e03040b071701211505040804030311010b1806010c12200106060503160905130b03 67
    0x3851000b03d030060110a1444030395850010640f0580707000d92001c1c1c01400002a40580c00200e03145051040518500c60a82c598403400112780460000000a18000c0107207142408900400000d42e400b20140540c466101401c030110002d98005030300c0100442d0b1a000144100f00e002c05403068038281c840f00c1c2c3e504003803a2400045800101c1040c0c94400c90700050042c00c00c0480c03000c403280308030050100301d949003070a242c9110048000c45510300080d5030010507180c04807543c0c180c1c504851180110f07810503582149000000c2c40c0c0c01e541266501c82d4103000150030b508a01900c3c1c811401034000c41d41301e602d1800c02408071800b0040303840051349071101640c203039036802a079140302c50020b01408105984990042c0d8081c6c00c2140c0c003810700182c01c1c40390110300b9841002400006a10700f070440d15044121281c3d4241d501c14040c08000c5042400003850f66002ca403668483c41c3c48501e440c691180e640e501003040030080c1001c5084050312054100c481c0d0804100141801c0c1d002890040d584030 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 965245413 1250 965244163 965244223
    0x50402030411064801110901210504050d1b020105033106020406110f0d0c0203030d0203011509050f010903240509060a05060108090a03031517070503 66
    0x842c0c5141c841c4281d2001c00e101d076071844101c0100b0341e4090b01140301c000c2e0810014084051001201070000102c2c180d031a5400c03800c0781030003a04601c0d624a0001403c000c848401919001c1c40d0009120200b46c0c1900d110789424941c0c0200380c05680220080c18000c011040300030005035400d0884138500d1204802000140d038018200ea50219545404144040984851f0415190b4485009461208031060703501031140980c000c2c82140c00540742e580e01f084404034501e0721030f14040920f00250704000c00314407070180a800302c100450700c0101a03d140c10502c02d0048201d81007030300894034a800303860181c40304540080c0214050802102c3c01070040c03d481c4002407480c0764500006009644141000002c0b400d140140c600700c03405050280443d261640b0a2540d03070030b04540c060b01860401c0c0206089500a03644940503403d00350140c590702425440a40241410402c15041c038000000c00103507a2204442c01c918040c03250b170203882214605000c151906040c01d0316496400308100e0000307040340d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 965246663 1250 965245413 965245433
    0xe151c0e1c050409020901050715050619230f0d110307090603080912010f0c02010203060a05040b03060f0903040e0f160311040501110708030f040e010f032a05060c01150504020304 79
    0x140d0f44d0318016030b51703241d1800102d07454064401c00401580e26a5a008030001d800e4102c90f204901c140c07044180c01e6164803085c41c02ea42d5501c00c4190030340c0b2018000e4400300707a410021646803800b6001081250300c61010918030501d4003026580f030003102081e03284515041c02810020004004103001c030a0441d200d00250b407084052680c070904d4042c8615548000030f400119040a4907801008031901543c03010780170313500c200c407140d12540c04408042000c2c40d051042800d17145018000384884e0b82e0f0040c4000164002400e040c40c1c9100c180000245a00462030040c40342c004005401e00302e003010304440a0f44a050b101c848241400e103001c4601d0b2060f00303019203003215024038201d180346074040361060601c25240c0000081e804001900e85001d0304110060080381c45030794031035005a9955003002c10664183c04001d00c00e11400c0c180c6060142089004801e451444c000101c0d80c95650b00000c200c1c1d4020080700c0701603511244c194076251040312802d0014a0162000d51451400c1d640305440b813 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 965247913 1250 965246663 965246669
    0xb06130f1e12030c0c090213080d02030f03070e1903060b04050f060d0305040b13081905031602040b0a0602010c020115031e03121107210e151c0e1c0504 67
    0x340041c41460740030b252140b40c1041c0e08640210440758000d444401c964040d6208036880201c0c1c20010b0000500c1c000000ae202288048507805903041c620104954811540060000c40800202141800c860fa03100c01d500604440b2040c1d801c4040b40c558a84070042d564024000d40c41586000108007490720407040300c075441141226819012005840c040c0c41a0150713410000ba00031010031a00e840302ca0009078442500c0300c0c1d20440e0b10481d55801c2c40c0414910241000700181c100703110401f009d03a80c000c405d80f0b1040c8024404074520640c4404690182c0e510f6022800513916001d40c2d031b00094080c03003020165040c0d2980e44030a282507450304000742d4511034a05028040c0458000141445203081d06e10300701003120203001e030021869254015821500080d134411141c210302030f111740da40c58141e61005030f590302c900c00860f00c401c04000303481e880020031920b559010030001101c25032a43d001011003010900c001091505140e0346440d18007000226141c64403180c51801c01b55070010107032011 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 965249163 1250 965247913 965247929
    0xf060c11060a0c0609050a03080c040f09020d0609020706090611040e0c07050106030b180d0509010f210f150608010b03150a03120507060c020714090a0b06130f1e 71
    0xe50a16058201c80310300800c000038010f103180c40c017a030041003404a0580002c9029507160310464503070041c030000a10030381c0b14090b500c0040b000c0c100a944100d8000d8212109100c02c00101242d0390300e56071003aa40800811298103980e900c0a50401070070b4401d011201142801c00303402c050400d444820418009000b00c0e0b00b07000082190000c0044c00d40101010b10b07401264039009003003410301c040410605000305000c9004800c00048050b2144090f124074600580d80c681c0c00841002c401c1c0c620300c240c19166004444102d1101c0304070340c40d0740122303a50f00c0361102000900e59046041e20108441c42d810003010003071030b0001005004080700c181e94100900b600f00b25480346141c03002403e004001c0c2c0c001071580108040425000350024040c02032180540350a0025007141c40b001c03620340700c0314098107403171034002c22a00c1c13020704001680d01c3c0d109460720b40020719981319400060346908410482001c1400c01b42c01808101500f200040041c54084001203804d440f44404a00c0d5202e14018120 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 965250413 1250 965249163 965249167
    0x12020f16090216050a0c140402400602030406110a03200109020913030e04060f06051b03030a0905150f04080a1b0303150605030f0115020709020f03010f060c1106 71
    0x303070f00040c5410362005136020040725100005481e04240740c145900c104552540540010390160820380211200c55a0743c0c4c0000075000d0100c0310646030242c5280b100312600340c088108608010035008414060304a40e001541c469207441b100412600c4118281c0a031742c7c0010500e880040c1d000800e603649464050741402d1a4852000c0e140c2c018100c034000a0b40c411800010f200e500c041e0202da00803410301950768108198069400e00050756064804c01c42000040c603401c1005074440e00242403070030740364285800880c4080c100c6500c0c40e081510604906c45d500c94460301080300c10041144034000d05441585030345072201915440c4500108054507440300001d142d4001442402e04401d60f0b40c048d44948c0081d400f5060080040502e02d0b0841c9034a620000c000c15103038000c2e41901e12410307110a8000043c0e090100541440910f15030030340030361007240301c01328806c00c1500145c940303061070305009602d940c54411800c0408070140e20507800e105c440e11080d000318100c03800900c0140c00540d1019 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 965251663 1250 965250413 965250427
    0x91b170703110f070f200d021e04050103050f0d0809031806090d0c0e07140315010905091311220504031b1406220b06011b12020f160902 60
    0x1c4480d200e200011040200c3c0012008108203d8901120381745000d484203e020301c07403102003060354020242581798050400301c100d00051816000c09542c0203204080041e000309090085001e83d2001e07002152190000030955403240800c2141d20341451407840d0010240c20204c00c45926445509400042c2e1048410000303c01e0701c601d0304407549800094510a02c628003814100001d0200e8041c064200c1003c0012602e00351140c9400b9030050304080c91540765440c0e10000b214000300e001004d0341400300d003031000236072692225510b0b07204400c0e900c008000d5241614049009040381c0d0300282c030422b0300c62400c48001d166034041441c43c04901c0300004050b2960b02b4140d626280d1070711030100a003c0d4594140400c0f00106076944455480070443d483c640740c1c0c8510704038003801d41070956074802400c080d0902044c903040e0001c2e006403042c14590010f044072040901c400e51402e005a035414079407010400e58070341c100104c4000100b51005051801064224000c003c0c43e90f1050208058002c0f4581c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 965252913 1250 965251663 965251691
    0x1080112030813080f190905031f0f0603050f01060509011d040327060207050907080f2508010e0603060903030a110f0c01060501141305010f0201090606091b170703 72
    0x40042641c000340c8951715290041c10001e443c0c0e02580c0c280311041e00710400700460300e00a94501e01070720001000f6040c141d0700b089075007140030034001c03150070090f88a50700d0703131074816031446082d002e18050390140000141e403816490a4880b42e81c01a0b01902d884001000301e41402028984d40807035812203580580c40d2070500715290100f010006200f030800c000303400401c0b0301501e07001045802940907610b810303a4030001c0001c01402240c445000c01c030f0311400207500c201c9290b0040c3d4825100c003a040840390320780c080080b0100100801c030020409080040c812001c00d500390390307401001180288054a0720740e00c1180c40b4000035002403074654803900c0600c1480303903440540e0b696894110409846618803031703d40e0701070702847c0300ea1408150305403025004444001f0031258142441c41c10f00003240d1a00300111900000000f50300b08655948104c00001450b50103501d0060014030f0000c2400c034018905048441f0448502005000303100308007003000c94504038925885010b42c200001d03603014410107 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 965254163 1250 965252913 965252941
    0xf1d0c0d110d0e070b071b0305030d021e070f02060306220c030c0c050a0813210204050a0c1d010203040317040f050a051f03020903070f080606010801120308 69
    0x4260042800e22070500032121201c4003601221840000900044600c00e03450780d101c1c0743d13501809140240c00c10450f0301040c0e02044240d00140b07003800c08030071242d4030b444841c21600103075244220103400103400c010181c54070510342c2c0307901041c200c00c61030200da0f540e480a0601c07900c1002030084201000080c041d981d201707640e845041032840302013201c0c030201d402c0000503d41f40c100d51010905c3d04101d410420b114084988803154414010855840c1c107403980c9880707030000b02140100791460718000c03540e0b2183e0419031b10449201811000551860310410060320401403900a01500e041c0208850b1039000003814440300d80fa01c1038007004c580c1c4c040100d04600c100d0b00094401082c00d8518650844074800400881d2000d560701e8400070346031810000840362900c191580142005c141400c0e03006152168054880a400d0052030140b01c5400b19042034015440003442000c0003604000c901d60034410594402c81c240fa01480315814005403180f5502c50400180c200441c400000310403038240c0300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 965255413 1250 965254163 965254177
    0x2041d0c040b0f2205090109120c060b061b250b030a020702030f030d0608070609060e0a0f1701111303121715100315060c08040e0406090201090f1d0c 66
    0x8000400c1c00b404181c0e407030424410f28682d044c101c0c0340000040003c1018407405140c590f005011124440e08a41c0844d041c060801c4103840c4150780d17a030075000f5a42d0380f5008008814810780c03006422550149100c0c00c2020303140d154011107200040b0703425400d0100380d103241901c010b00141c07903ca4445a8000c0c00a01441000a406214174802054180b00020242100c900580c41c1481502e44480380c031034980d03c50384115070104101c0038080c4122070040601d8800110080c0402e8441503841801210b0403007a0f80c4001e0305510f000c81555a111402e004041c1d05041c1d007100e00d8584140c001100600000d58480505045049009084036901c90300007400000e000c034428014a08140030180b204140c5c0106da1440360010614a24882d4000c0c041d408030300400c00f01c0341c100c0d00e00e418010760b04981024002c964000e01040007181d1280d50144940c081c0740100000941280d051001400049447d0410102082048410004808003440b004001c20180079280056103034040000011b000e148 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 965256663 1250 965255413 965255419
    0x2821020709090303060e01120c0605090102030d1a210d09053601180f0c0c1b0807030501051b070c18060806161812080307090b031302041d0c040b0f 65
    0x4000560010300b10316680223140a40c11300740700b4a80d175000c19911807041d0390103036000d0b030000d010518051403d54000e130040d021070110300c2120032035000015090110954880c120840317005a45000c030900300060b004404403410030700344090504c80001c07030f6284070802c080c1c42c0302c0481e000c00180c035040340c4d1201da40c55804000003503196102c20085101e035100c22440002c0314540085645000c050b4000c2c00c02440c000e445404024600b501d8074540000300c2c100b0034080340750190002030303c0d12007040410000e500a10000410303042141d03006200c1c0f407a401d5031a02c0c460040c4980f0010031046040f210441e09888200c06440748000c59520180c032039070340701d0405802298100981042541606803da4505032b0312184480345c0720400002060803802010704440000180030300041c41c40004541100580c14000c0740c0c59604c40341000264001c03074482003c0001480c810007182800d00844400310081e20705807164806420016640d60b00c051002445251250100f45c3c1c16114080014143d036405 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 965257913 1250 965256663 965256689
    0x60403030e0c09190906020c0d020c180105011d130c030e0c091b09030312250507080a030f0f06080c011107030201090b0a02282102070909030306 64
    0x504000d001491076544401c40350007680b004507094900840564800c4180c403071004c000c82c28035581c250007070220308130482c1d109030b003001400d9505104000321040319030542c0c014005841c00900f84880201540801c114443c0d6880043c400c07a078100e04a800a41c0d9140c0d203440507408001d0020780560103201001008515042016005913810341141000104140444540f402c000d41440808401216178000d003513181040075044641c020010809404003c04690928034100030200c00301c0d90a5079484400e07001195030744105000801d2180144a00341812403c00d100790300c8900d650b01c0f0303401e088403c2540d02c80d440341016036164021080740006000400406407199140b0b552041c20b036800a0204048403409071070104000358180c15070f40e06a4664031454a820803525080d001419402c00790302400030040030400034800740010040d403100501c81d00c44140e08001421040400d4844025550121402452500000e10008071844041e00240441c07407810120000c1690303802c004511008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 965259163 1250 965257913 965257921
    0x5060d1e0c0308071b03030e0609040207020405090d091508150d05010507030b0a080102040b0f070c0312050406170912090d05192f040b060702040504120806040902010c020405100806 80
    0x203d6000b034102c045c41211801807181c0d1401d6081034030403607488024005002e14200404a091000c00350130032101c05003002d803c041d0164001401d80348201d40014650b4001d04101c01c01d1540b0400c51402002404035000c51107010040c01070000500622031000e07004031030000c82507501d8000d0030040e200c1d00203008210f503040a000040140c16040e0141303100b0882c91034041400c21041c0300315000ca414200c0c00c5843c2c00010000129076410100d000e98010b0724601000020581c1840102100c2d40380d40d0b5132990321070814001a01e02160070310f90320025200f103810440c0c1c0c403800113081c2c00d01080b28084030383c4410300c4000040b010300311828018407034080c50ba40e240c8400b101c50940440c0c180314642c250f19002140201840c80e2200c1010302800d154030642600c0c15040560050001400c0913000034078041c8640c001c1000d46000341ca0072181100440c001586095202a0300b40e046442150144040c0d249500005c0140c100000301910407a6120086052082a80e80280c010001002902c901e850 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 965260413 1250 965259163 965259173
    0x242105010507080603281713080601030c0b040302180c090604030b06181605070201032702010905190905130209010303021e0102030c03070c1104060f09060905060d1e0c03 75
    0x1000d8504a01900c5003488a815821040c440b0903803180f14407404c8950b103001a10380d04c00ea20b00b8020b800498800810030300e81e00c1d001100d64100030b0009c40d0001e143c4d55155180c801307651842c030351103001590380922050006a5801001800e480d603501e0103602140c407064030141c0e9074418080103e03400310001030000108058007840601c00c51085405194030f0352010207011481c001100d00c00c61340105244e225040b94001d801500394030b0700624002407400d4409100000c1201400d00c0401c40080d4401d00608540e800312048002d0542568100304030554041c081c00e01c4d244c1c1d4040c13041041e0b01c07180003416240313072388201164041e00100714041c5946d60f070501940300c1c2144028501c02c101c013080f00041d100c405000f140d0080351982101499950341010842d10990881c004403182e040c407190202c490b0b0307200d0042002600e0034510004079075252002c284100d0321036a10081000e400c100422420740d9844a010a0071600f240d2040061015000c0310035079a9280f020040010840e0300c00030007881 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 965261663 1250 965260413 965260427
    0x6030a0f1e05060d050a0b070207090212010801150305060105010f030e070609030b0c090f0111100c020609010b031203040303090f1502030a0c1107090e031209030706242105010507 79
    0x64107003045140c9440f82404810000701c5805085075000fa44420005035034101c00551202c40b070320590700d84d15142c1c0660800c5e03034803070070030301c04120340315801800041001e2090051514003011a4621180f55079100c0341c951105220311810702c10f4148403001018040d404c080c4540d0300c000140e640c090b85030100600f6442c52400180e035010308000000e030002c01450101d950380c40004103c1041d1101c20401159200c8402e170a8a000b4000c500954040303600e9801030201c01011500903126502d01281040c0c00c40311103a441911941c0031128821401280000700c0750401d8140c0740204810001d8103150301003040000000348031810b10301d8081011207459003d1401255180000e02420100310b0302195140610201c103019a001150304008042c069400034a0480f82082030301c3c1400a258000406000201d400e4541500001200e004101d00362180e42682c00501000180c42450282c29103140c441c1402000c0030724405951062400e111b1404400800c0c1e40314000380010702d0b00700070080001d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 965262913 1250 965261663 965261711
    0x5040503011d06010609081207060e1c2304150504050909060403120207020117250909060e09030d090204140a09020907030b0d060906181211060c0906030a0f 69
    0x240c05000004180d2600ca104000e04031f400340710003001462140f03c649041c90344040e40882e04103540da02d403540390304014040d1800d60724506980030742042e40f280000d8804071018510b83d94420007126822465860842038034103568143c0142c0449075103161066506100c0d91b04619404486642082802600010100d02c02c1b80300355980c50301d00031035000d01e0040c0d00600a000b404a00f40b1006066040680c0000300d501403c20303480120001400d645007039030016001408000500320711030a00c1400140d00452009046001c144070a601e0305202194407402140c3e42900d103503489002510030340d034030707a0084065030141034501030341400c10319010801040040c40807400780824100040d0b02d1402480342031b00212000e88180c0140400d07a84d50801400c0805003140c40554600d80820743c0080020b6804015204560007103010f5508007002c4c01000d440d0700303804200d61004041040545191042c4c6655000580d805920b03500d400f001e0801900344c1c0d00041511500c2e05000041c0c1072841038443d141 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 965264163 1250 965262913 965262971
    0x3191113080f100218060307182606040201020604080705030c0607320412021201050403180807030203030406053a0605010503060603040f021311040f120b0a0c0504050301 75
    0x8501c1c683c25503106074002c4024005209503160b55210007810b2a60007580d0080041c036104001115510900c80300344000d4016010f01c030b59589698070140561000c1144400f40b1500070021352400d03a0000b507640b1402031000b881480b01080c2901040f4040060300c10100410003a100c540c50b0086005040e0111055102c00d8074081040031a1001d90000d50a24404e10240c496841d00303040000e900302d090300c1c512080b80c2020049841c0215401d0030300c1400d0090744a82c0d00c07141c034108070241c0d1285110341500b0644c01500410000c01c0160f0f00002105c00315019424841d442d40c0c040020b1034a260030488201c440c2128a40c003040f0241e80d601c00071a481c90300410208901515080111000d0000b11800f5802807010070103d80030480f48080803110520040182107070030140309404095503548101504020f401040502c12030301e05440410180c100140328298016042e00c9554400c800074050036619a40c07065040c4055104104450241001600070311400180c0019982012090720202c40 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 965265413 1250 965264163 965264173
    0xc07052e05061c0f0b0405060412030219081503060a060e01170703120e04180210090503060105120111040605040e0f04030f0e120a0b180d0c08030601091a0d0f0203191113080f 77
    0x151440c024330954490b40c800c081500321904400c082901e600304068803a56034042c440101840680e02009a5803080000700404100301e4038128503801b14100c1a00142400030301d454001c402c403080040c050701100d400c00c5421500e10039005060303d80c0e11034200410380040c180030602144043d0f00d030a003407056100317a9035605004900c0c401114a44102d0241c41c1d80b42d0008070040041e49007031800d400c0f59001ea28000600b44040b40c810003c15030081c0d004502080001c41c041018450444860f07920484e1001c0b640024078090360000c01c89060001200180665907105200703544030103400c40c9400d802c0804503900001d4904003000e00003800c40355a0000728900041c80704210021440034111981e5444120940207107558800701500010a420f040000c40a00001e44103141c081c00302c03040d45440c0b590341da10301004101109841c000c07104550424010000d110040c075011101c5800c0307103001c00000443c0c40c405240348009120381e500c0e101d41c11505200104100d10045403002c112005407017140c1c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 965266663 1250 965265413 965265443
    0x30b0d05010b0f0603061008090f06131106090f0418020402210109090309060c140d1d0f060306150f0708030618010509040b0c07052e05061c0f0b04050604 68
    0x702e44c40c03004076020750f08294070600044000f0300450543c1c2d040200d01c0150313400d0000c0b800110f450b00320111465841500192000c20038400500204c04da05502610031501c0c1581501c00f042d0403100060085e40900d0b9200f180d40320380b901607228410f100d0790040080d5910b82c1040850780d10445c0c0720403000311070034030000000341e0300b1414450411003680c1500c4d14010faa292000a0362920016035082d0ba01c1c0e05c0740782c120749071014140200c40101c1103903154181e400e181441c2d50300d084a05d0300c8445004201240c3c0340d030550303551003040e01c0c2d2200046801a110881071000300c04a40035000b11584402c6001c6569010001550b000e140320720010344100c800d400380010751000c0b080b82032103101d40049151021401041c0d001c603505030b1003144c0003d010300d051055a41e951500a15051104404a031680c0c0340712042407500c0030001c8a0754040302407115060000025030558132545101e400513224a101000b0000e61030703902c602d078540160030f000c11440d003800c020342c0741e02c01103c00721900502e200c919 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 965267913 1250 965266663 965266669
    0x61407080705012f1231030503040b090c0102120901120617162103030e0604060f06060e03030906090a050a172a09040c050a1d280507030b0d05010b0f 66
    0xc1c410003014809038030f44907154803000c035000c810140c801040c18000e00d031b03214050010480800e10094860f41c1c60716601d02d03050030000d240000c080d0041d10f454001030604d4415a0f40041c8a16a021084124039923400d407503001030b40d40507907a035000d08a080c2007000c001105d0550103280000d040344207054a40054203584040c07100d103018042c140e00124494820030348401c8420300d00031190b219081c00545618100b880500d081c200310380845402da1205042d201c90060307401003200800041c00c00179152821240081d0710380c061081d90900540300801c0c0107603c0d981d803040440080038090030101145488503542c0c1c0112644021011103803140a100b0034001e1090300394164200043c0125a20340d06401e42080919000940240c1d94030b81004004561990b4601510004051144010000205007d0b003450103901c01804580c12500c0104846c103050081200e0301880050083d0018080d5a4031600345c0051960b41c43c2c0303940050315030b500d0300c04001055000b06071002c030860340c2c0703882d1035100010 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 965269163 1250 965267913 965267917
    0x613060309140c18060a0308070b06010f0f120203091504030906030b0105040302062b150303031b0206190f0c0f0e040603080a1101290109060201020301061407080705012f 75
    0x5401228564140c14181034450481c1c1d0025001461100d20b5503482d150102039411500c0107074ac10030b000500f40040ea40c0c100004085080060a00b841000b4034036130040d182004030500d160201780c0020004120b08003e010009224108001c000020708090400411840c00e500036000401e141061556003503000c2e0041d2000c80e980104224600441d0306c0c25205018001d10001a09103501324680c0350a0710340740124021101882d00d03088003c1d203942030041c02e030340c550030b10b0a02c4000b5602400da15680c1c00f01b01958001c5040da0362117080d01100802100404168480a01407881e0019029904d5803105468206002e10f9035900a5007010300e00300f00c100c2c0d241d84002056200c0400110a0460240d01c2070f120104818000040c83d02c241c04004404c0c00c030031604042002d44000050105680003840c05019013440d01c000c50039981840300191015002d14a02960303908013160310750402c000d600441c0e4400703074807000920005402d0ba00300c941c000b40010840c90a1300c03080b0342c2e2403985075230401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 965270413 1250 965269163 965269183
    0x406030606120b15030613020d120521090c0d0320030d2a03112106040c05160201141902060109060501111c14160303110313020f061306030914 63
    0x107401c03551a41d600040d1f2510340c0310400c80e00700120020321000300300c0441e42200042c0403034650f035a07196004070b0f0b41107843c800020051031910b00e02040c802c514100250000c4910703800c4d6101c5007501524103003501c1072212410420003221002d007201040010220181030103803400b03e42441004d98100c1500e030328960488503039481401c0e82c40102c030028403030b40082c03a607809410603180c900420380c1c0c05031a803501c40d4090300b0611890003040c0004e40c24a4440c3d0200e4550074940103003440304036954440040c0545801a04100d1911034040a20f04200b0840d05801c80d00d010f984100885142e0103512050240f003100c02c3d4600d01700d00081ca0b54004c0140d00b44601040c1d015000100c01c080901001074040d60002d020803002c1d03410700729910107484c02083c805404641110b990782561900809442140120a913010000d0082c481807606400503100d00320780c100d03080902c40c041c002c08a00c480c01038040d416800c4056520010b8566090b42c080e0703071440d0052075409107800c007403900140e441440007 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 965271663 1250 965270413 965270419
    0x40204050406020f190915020d08101a250209130507050909060703050c0a020a0303410a09080901080702150a0b0f1f05220b031905010e13020406030606120b15 70
    0x10b0149e2409200c0d01d00b055108d00c000744030304c410380d071034000e0b11084d04c103038400d0307007404c0d280c002405480751b20100d0f8000c1c030380c1c002081070a601d5912540419980c43d4082c00c615617880000c24100c00b0000c0600c465006000060b108150030b16001d800569030304816030f41c0302c0c0428900300c04910320403140002c44228030742a07002404d14107080d1750110020718101070301c80c80701c841203180a02204e030a0400322200300392140440b10050034403900c0700c1c48108068281000945807540010029001c1c2d01903801c0d0080c242800442507403120800e03424004c1c405005072207208007200304110000d070b0754009000410b0a403022002c00705200144510304400c4096503064a80411800521a10840003480c050310480d1017905807001c0c0408444020205401002817030601000b08003206640f40044540002d10740818001545403120709200100007800f078100e03a902800000c82591256000700c0d0065900035010480b05650740941f02c801319034601e007200e031041c414001c00e440d44020075680d400f10341d0003 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 965272913 1250 965271663 965271673
    0xe040b0a0506030c090301090c06021e0304060f03090501140906183403050109030503060405060d02100e060f0c030d0b0603010e0c070f050d0e0324040204050406020f19091502 77
    0x44a021074960005c80e0016070541d00c0d041c0050014195811075001000035400400c41c5003c260780c0c0a503001d5040c021303c4041e40c800e220801919500c80e69611148440d03080020b1600d4071402c00c1030260042c0c14500322010340d00d00501507501c20014280d4841c040801314007054a2140c400c1c5c1d511078201d803d1400103c103280380001c412000942d420090800c042c008081040d642c0e950b12404c3d640d1000c01034002c01c00210422809080c1400b509503c41c10464a003050f40c60182c2c0028a820107001082040254010b5a03100030b4840d42c0c210340002c01c10003861501c8030750b00c4114694a0348182c1d14004800d050101c910b030b4509298040c0c2c3d060701d02a0138042c1150f921706084800e0394000c114180e03442c0c04001644c0001ca07205024803400640a9940c9044a905020505140c1800702c00082c0c1400c00d001c002040b03100f1a8021103420a60440c0d0110706500c50303003002006409095608100c0c141c000840105903510034100324801d00d03a644079a40120f031b4842d07500c01c0410071240307030601603000 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 965274163 1250 965272913 965272921
    0x602010b0a050f0409050613120f2c06040e06040b0f18070201020706060824150409170f0706050c070b01060c050a0b01060903061407020c13020c0105070e040b0a050603 74
    0x414201c0703c01d664040d000160104458a0f00c91801d001034407a50741884080482d40140001901d80501ca40003a05150000500c107840003000d00c2c814a078940f0445c000c10022424100e04160302c0f18402c10010811b90701c590701c840110040120655100340700324544256420a824a81801c0d540d5040040100c212046640b0180405900040000046560030805000010400e12442000d440a1002408001c454402c288203e0900c03014001448142408101a2075044010300c0c005400c2a0b5011901d04014500059406c1003030907400c01328000403030928816844603000c3d1080c103001c1d941c103012076207424446509501c10110058112aa100d0050180318003854070b5101c060b00c1481241c1c0b080010761030340006508282c10a00010384040804c0003446418011034180d807041d44c00e100032509140e1030103036850051001080c0252501030702c94003180e0780c59050b513550b459514024046840c00d8003000b4036400304003003124810340c1341900c5d2420500344804103505a07a0094201343c43c40d21 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 965275413 1250 965274163 965274169
    0x51b04030f0501020f040308030403030f0e070618081b3109020d02120d020c03030c0c12030c070e0709080a0f08460c0f02090406060b030702070f0602010b0a05 70
    0x1185482521030f9034003041700800318030608005000841c0520300164032801d01d440d00809444d40080c440c1a82d9041404c840401c071004200a021a182410000100b00142c050244400c0040d072140c0c506000b00108189100134100c400305a040c0c044500317a0b03402c4d0034840042541c041079101920b2020505070750403807169407a031191200c5030006049403e00c251a030300049403124624135041e525003164a9844201c0d404000c0400304d03900440195081c0200b115a16945909800003588601200b001e0b05e0452803017031044515110b600815201c029407030340c0c00900e024070180d81c401c0004444010004001d940070403c0500d441c0c2c03008204002ca442515a502250016100300d00b01c6103030710b401806171001c82c0f88412040c0c892a040016811104d2808008100705c2d131800c201408a03441024001941b0005400d400c41c0e0704940f002c040344c5980c28840010030048d0026071880f8130020030b000d5001d400080341d5040795009800c1d41e5030030303442d460104d00380c8101107421070b00803107240402e200d189 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 965276663 1250 965275413 965275433
    0x20304030b070c140a06060603020c0604021329030c040c020d200f0c0406051c0b040501060f140a170a0609060f0207030c0c050604030314030702150702030c01051b0403 74
    0x44042d00e4a04000c120035181e090700741d0070811000219170312000802e010002c1601510008040e2400c0443c10710002c88c0503140c80e0760b0001d100030301c42c2d0700039080b6003034040f515804076809240c000c624030001619000c1d90200754200d180740c42d210380310750015003034940f5060040720b40ca031542c0c4e0b0103411b40080b01c9800f030314440d440344e21050a1030307094418140c1c1c2440401c103803000c00090000904c41c40c1035040c2030200b10707640742c0c015901425041e00c0c00b20044620010107001c2e42d174441e24161841c0d0b620b0030200c0c014011030b0000b210200441c180010030700307001d43c00344d00c413490111038030310b44036603203003400c0300c3c14460402c0c0c0c80c4098100c4100100400d20b42d61012040303501618000c1581c241e040c400d00100d9021380400c90110b4041c020800c00e20181c0814500a4001a07c100c0e142505580307000d862100d1119441c400c4000000004011f0b92003440400c50740c400724003000c00311382010700c40030f9101d40003001e1403400c1e0b40c0303094000f0b065480d41042041e82d01d24049000340c0b409040d610780305120 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 965277913 1250 965276663 965276671
    0x130816112e02070b03070e0109090e280605150405100311061309050108030301080d050708040b2a03090330032e05010e06070b0c1b160e010e0403020304030b 69
    0x5801811000a807084c4510001c5114160302c1ea207080c02e50780440b001505512554108014961500f0400207107580001881d000c0385c2c00312203070700280d42e00407040c2040080300310340010046802c14040c880745107010514001003803011501440956144200f1303582c04841440092b050310071240702c803121401c0520042401d682d40801250180b621003590030180e0300d0130ba00082095000100400490000b48160440039901d8600b80e0700d40301c1191035200c0c640c065400340c9203089100041c10b8601501200b14218981c0000e9200c4120072541c20455460b070308444e40c094040d000b4401e0b031802c00300000700845e1650380c401d04c030301c4080d50710301c401e50b400741d003000340050056140914102040360340e00f84e04500b41c02c0a1890070103014107000006103100842d814141c0501d105000c19400143c0d5100700580c0f08060107031103038417418501c5a0b00c0c6201c2e41d020a9000b64060440094684205ea01c80c1c40c0c01d0300c2000c140d000060b607032901c840d40b614004940150041c1c00c24001880014146950039800c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 965279163 1250 965277913 965277917
    0x715090323061923010e01080604031d0609032517030414060c0f030d11120a09020f0d03051e0903030a0302280302120f06010e09130816112e 62
    0x40c007405a07001c9103803169404103c04003814250040006091b16604076014203000301c040c0809041659010f03101140b000701140c40c82c6c0c00c5000c0c0310500e843e49000d5941680c0000c00315000f00721150450f40b82c0d81d0500128400072145845e0102d50380788080910140380d2075010007940303014500f050520b1510000388032103600c64010000c1004600c0c0c1080041040d0100a026507079921900c599442207420f007003540ca01e8101c0500003403211900000807a580013081e0400865035050300d2000aa159486078203007580a010a10404285a4002c001d00303011000418124400040644000c032a4059214890341c15801013211303068251181c1c0241016404000c81240c5456400010a14560341b0301e09910001e82c0c081001c4034501c50014126411510306d04140320941011030000b41450203081c0705a001e000c5650109a038640182d42e03c54020b03400004141e16000302652890904465090550740358107268032201080ca44440200c03009001c0e081c001c1b000d004065102d400d000707018429142 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 965280413 1250 965279163 965279171
    0x803180d06020a0518010305042a03060e161703160809030132090d1d030a0c0e09010b060403110d051203060315090a060e07150903230619 61
    0xc0020381c14009804040c00907111180c6900301710401e944003003928180c0a041604110600c00420009082501d41c4e004007648503a554603003030700f1740d0000c21259100805a500d40b07400965094030110316440e101c4003c009071140e01da59210701a112210740404004580c1080000240d110001071002c2d9289220b0200380d4204528280041d0840e4906016065240000c4901502a0b8840c103044e200e04100740304400700608044c0701c81541d8541a030120401e01016411002c5113103010604014180c05c01411500751010b2442c0c1081d00d2003d52081600880344003000c55000c42041c0104d01440c000a40794034203040c590303140c0791440c449600b40c10b0703004a82980c499002c40d006000c641e100204e01c801740c6683e42400024140350070380320b040b040700074540c0d101440507410000c07942421040e000b11012400c1d02c0803040e041d0070082140d0010060310042004482d8203604410104100c134014510040d1613003c203041d107040c5e41078002c00300c46150007950001e2882e404120386807600302c121900c005 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 965281663 1250 965280413 965280439
    0x80412050c16090501050f0409030c033209040c050408121e031503070b1c200c0a0302101e0c030209180406050106020c0d141203190b0604080318 64
    0x54240c02d140c22940f1101d442c1d10050005050032401c80c207600780305035000c12010301d40e500c00602d00080a0001130230044048008a1980c82190060f0013841040401c80070482303d050124113a81e10103a00c10f40524140421a980c0e18007500588040369910030103402c19603000884e14129600041d03d010b003403040e80d410305038a081d10388082c43c030489004580007195a450010545450415404400c421504002c1c00714040c1c52803036041110118020007044011b01c6500307600700304c038135281201d13441800801c0300c030070f82840011b0010401c3d00903001e45a5a4500c40c41c07201c145d400344111490881e09040e4183c0c1c80004c80d51182000c500140380c01410f0800c0c030000601340b00c1c100343d051008c00c0c00b60320a2000348031740c521401d40140031600042000e03001980100b441004101405401c2d002d600c0d41c0b84941c8602480000d030394204e5a4040d0366203240c03103100c08007121004402400850b03c3d04c01c401140d800c1c20700445044d070b20303400000c0d0f08080e4a00040c2c0301190398611450340010300d1001c00 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 965282913 1250 965281663 965281693
    0xf0c020a1103031c0203090f03040515070212240901061d070e040c020a051002030106231c0204140904022b0c03050105010510090b0909090a151b080412050c 69
    0x1070f1308541d0700d038640565a030603e501207500c2c1504180c1d4003d0782d50010071003003000f5550040060b1141030011000c80d03c4852a0001a2184c07500c1c58040b0300724012031041c204581c51400c030150820401070101c038401d44510fa48a03003240d513940240b2a008107030702040345040030780000499004003285459101500041c1c0400d040d94206944c0e0005603108480810030003500780000c4001d03800348001142998900f5030018644200302044c4600f004c5258407205903401461304503000e90801030300403110200d080c9007100c002c0d805071056a008840c1c207444c1030340364035289411900481e0010b09154540900c800c1039613408140b403200c035640001b61440c0300d00040d4890314400045010390000207080d0314240902c8500c1804404900420190720303c00d101041c010826581c140d80c0a584a600c15a1410b500a25082e00011f001d0140c2502c40c51024440250740c0002001d600b500000d0b0440141056041d42e82c41415a0b0003007040c1c405600c0410603611400c0031700321030f84400e0115030820074031070f2078 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 965284163 1250 965282913 965282947
    0x3020c10090c0f09020f0904021b1501090e030c1b0f0d0602120c0c121c09050109050c0301020a050714031209010f0b0d0f030c030513060806040f0c020a110303 70
    0x1c215945054524200144a10b0300300d50340c0281a21581586004002440158588100c1540a100e00d40c04501c08000d201c0f00c80c0700c3c40104040c1412600e0f1140c1602c544508040d0910920644070b09141c1d4480e43c1d21400b200390b0302c402140100901d1003c540c2203002091100440b07240e90011400d0b01e42c040950345105503551f26034000e483c01a590504001d2107611a0401031411050a40822840032800c9002a4500041006805441e11800d0f10003030808600c504004611146040008000a004042d4881800782d4421000c079501d03d40c0c4407003414240d000d074078004008550140a10740100307440c1510301d090b041001060b00d01d494a2605200f41c6040700303407010006695200c0c1c004c50740540310b105202d9031540464000c9070301c00c52950741d194600740922000302003203007032030402c81090b000704d0640e4404c890983c0003440442d101d290040803498101d036600e1182e03041080700041e103c1c8600c2801d4483c210740d4042c00c1c01c1105904d602e84140c00b4941c4440e01071000b009001600c41807004 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 965285413 1250 965284163 965284181
    0x30403111c1107050a06020304060507260c1c0c0b13060e0d030515100f0909180501061217030408090901090501032109090f0b04050708010e0109021903020c10 70
    0x107851070010359202c80b5500c1d20407030384c111501139400da08081c0406074001007a50b003115054503140790f5802d20b40c504524012007103004102d540440e100f0312905000088050040400e401c41103c0150842c001510249844861100081140710a00001103112925180c0d8000240100700084400c1992880221101c210030b101c0c460704030140a0700c04980c0b60007881d42201c03a55004903103800b04400007070020610a8007440c24070050b140c0350300140d800303010750314014104010200a00d9840350b4078040030000c0c90b0b4044500c1d510f0000b0104d40104500c0d410000180c22080603854800c1004810b5000d500141080d902c0a01c140510040c0345e69000c8160b010340f444c1480410035516600d002018008070310415a1f62a52060180c603c0c2c50307120007104e040382c110080c08141301340e0569515004040f10144d2640190424080040894010180760b048403034042400465a076103a4000c070417405000e519003444000b04c4140410203100e40c0140c0b042112600c141d509801100301c2304011924014 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 965286663 1250 965285413 965285417
    0x703020a09050d061b0509060a120b13020a270605030415050415060e06010e040507051c1a19050118180603020909071a13180203090c010f05030403111c 67
    0x21150b00c689600703410400c68001741c14400e04125101b00010298010003024508200c0c480d480c4030844000d40e0402c104c8400c0284c649000c0c1c012200c8041c01961089030181c001c100740c5188540500b03000400c000c0d05241c03e00f140079a0300d050103802c9031603600c054007da881e9a4540c03584c03c0a1030a901c945406a8840d000e8440404013a100030800e03100d40340c0c400c001c50f04031007041081a98000000102002040f58001001e035a0084295054003440e0001000c403030001880c441e1040c2075600c20f0f20803103880d141000706c403290741c4c0800c2600720085c1202c4040e029155001c1003d5402181d0031400c54400a40ca80e0103d503c801a04044203040c200c44c00c0303110f446040070419800c0100314141c0006081010301516424454004400c1081562004e1000b4002070048070098004070402c0151540310035549089902c000700340003079042a254070030140140e450203031007076002d0342c0400c80160981e103421b0f04603525928195011902c24901007240d0090b440980380c9440d2008007592410895 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 965287769 1106 965286663 965286671
    0xa0507050408030706020904060e06150a02031c0504060b1f1211031003290601080406060302032401080115210b0f0106021c080703020a09050d06 64
    0x90b4061141804003140b220100012034006007070310b8100321405e100305604c4182d5504460030985101c0e0340b04c500e601da02c03601e045984014021081e01d500641e414140900714003486281c1c000f0a41801656490800c401c00125104200031040262a850643c1001502080e0740c00710f1304e0859002d000c4c09088003186020395802c0b0052040c40c8148458580c104584076101502d0307540030445001071a001d03509403050017641d031643c40d0441d038000e4052907141d07003006603080706002d00140c404945800c008009a00d0401c0300407039190354503403a0003414580c00c01c20240305a060708211081e07410000031415080380482004141d503128010800c000c0804040f07601c14030803501d002011030514a04000d80380c0140074219040350120380030340c2e00c1d0781060880240102070000c0f0140211b0021404519043d00c6036015154484079414a44111902da400003505050440400c441203512 = true := by decide +kernel

theorem cover : BRFrame.Cov 965107913 965287769 := by
  have h0 := BRFrame.cov_init 965107913
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 965107913 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 965107913 ≤ n) (h2 : n < 965287769) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
