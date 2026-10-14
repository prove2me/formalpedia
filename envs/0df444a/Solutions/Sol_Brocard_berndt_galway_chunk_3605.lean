-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_3605
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T10:08:56.9252+00:00
-- url     : https://prove2.me/submissions/e741f923-9ca9-4578-a1c7-b6f8b1c60012

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 648201438 ≤ n < 648381294 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 648202688 1250 648201438 648201457
    0xc06090e22020a05060f04051921030201140408030a2d090305091c03021005070e0d1a0702060106020f1515180103060c030e1b10020102070b1003022e0302 68
    0xc3d040703403110301041c81c3d90885503054a5905002c6420302503854110590f503141030640e0340c40140185050000c40d0500c240800c0d4941c6a9900d00b41d403030615100390001c55038004120040d52090602d4504007034190720490344400e0051a080e041100c1800000c1c0120700c50315a220381800802c0102c442c64020301c0505001c5040c04410400751000391151100c0580310350b812550314203940a607040107400c0c0764402c1034482c3c14034030700000c00c070049070080800da1880c1420b03074030616426610f03d06002c8000a030440340c03031174a0004040016043d40000c0803410380d1020b07800d480c58621041800e0f551342201c03030182001c0201020005042d126102c0700020400030007081e44104000c2d0240c01c2d45445000c2e001582c24688504500080d1505806580545030010004200946070b800440d200e5213102d890307141c441c0700b4500303da0000910035010303612425004050700c0494180b041030003d10040d80c1c8070032400b55008418044282249107040104445000031040c0d0500c03101400324020360041d0400c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 648203938 1250 648202688 648202699
    0xd050a1401020d061404110a050d0b040f0f0623010203120903040308070302010e0705090c0711190f050a050103060b0313031407030e09160e0904021201090c06090e2202 74
    0x20040c0740c0f609002d81c07001403490180032500000d441045c001940c0450f070171480c1c0070341c00f084100003c039801070450b0900290810005061385144001030050203681908444440c1070440000424049520500807a1080c0c41440a111030090701c43c6c1311000a5003140c0d01503041400505225604000403e80c0200c5076000c2d00d2074103440341d4801401d5044007406800517076403043d0901c00201c1c10060380000d008100c80c070503060b02d48400b80511522980e2402010f69840c0c58a1682e0341d2102400c0c0e07442c089060701c603000340d10348415180b1101e251341c0c403d540c801c14002c000015554040c3c82080f056032019060145107035100c1c42e088060001c150300071400c108600d0007859012200002a200785071190743c6508000c07a80703208103c0c1c1040042c00000c201c840103030341d4803442d58102030714a01051041d5560900e690311800011000e030781c082d11210031542402c40380c00410070b68802c42400c2d10520f40300c0d0301d540e40e1030f40c032007010b4020111b89100f42d00480c0118080d000d11105604078040740300801c03 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 648205188 1250 648203938 648203947
    0xc0803090703120503010806130c03060f270618080901080414070e010501030e010b1c0c08060115080702010209090606030604021314040e06090d032a020303070305060d050a140102 79
    0x40310401c00c00f58502440c00148040014000724005101e056000680001c2000c15426203485e6541a0011440000c004542e81c49078000d4007101e80d00f00d4001c404204032006a094000e500744041201ca0240c2103c0c11490f01018104103c490100d0710311043c0c00080b443d003001e00500c015507038894044c01c03c4c0c480c1000700351594040041042054080c040c0c1c1075400486515020001d42560398210643d413051741807145206c0151218405c1d111102045444940103c01c1402c000a11085c02c1d00301007003038000e0030004164202607000007261825196200c00841d0b450980c100c6c201d000d0824442d030300c40c0310707031300403a0540c6400c1010f107402601c0244010700e0301c40320507802c2985c414558407005500482d0b10515206141c02d20a10b41241c0030b5001030403140c07501031b8180c0c1d1038520307241420003450798450408070f00340c1d6901080030005c03200e464403011001da00b0b60080d540740c0003107038a031000908140008040c3d06004502203040d6a002008140704001035940c001e1a026140f0310b404259401e02 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 648206438 1250 648205188 648205193
    0xa0503070305040302010e0d21050f070503040f050901080d1d1c0203120703050f070804050a060909061a0a03090212070314011a1c15060b030f160c0803090703 70
    0x61402a01c00d454080e5514a14800907060001c1030100c244600c0405040901148000c0800c600c6440c0810500035001d00b029070031b03200341c0101d46102100c044049121070400030000010025503207898034003035080790781c2c3c400c02a40401c01d00400d031194101c207107117800613030003503040c3c4c1c180a10f4030350103840118070031005c2607404504007080d0700303810008202c1e00305506090007e500b00344910044103103404c1c16902c003c1c0540c400e124540c41d0301a00003480c2400d014043d0203031406480014425020705684100040004400713000d250406490843d001502018007600c00071400c210744121800c00443d0030f010303001843c02601c140e8121b070b40c48401c8281441c0030f01c4940042d5214014010a07070090807509821141035030b860f030f0300c9851541421403066850030a1054401088420702c45c1c00b0419151603c21881401207001880d0708051000c9075000780540603500c10406420201d03400d40d03d00031069074194000704204081420f000241020400f0000156809003c180441d0f0f0071070350f2903 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 648207688 1250 648206438 648206443
    0x2703060118110d0207240203090a0b06031009150c050406080105130f11041a13050904050f0d120c080f0a020d090b0106020c03061806010e181b040b0405270a05 70
    0x300170889404e80c070300100e56a0074850180702e00450b50201c000f1421490040000c9540e5841060050403209520001a07025602007082010032000c5030350a2100d04024680107021017a1035400340300700e9080c000444003d03449a01910f0031196665140038840c1d10341018000c0d10325203241041d014640b5a0a9401c0c3d4489034050020028010500741e0390326481d19602714520110030a01e1407410b007041242a8181c155000e016064034411a0480d4140c0c5a51034402e10b404165044c41e01c0c14083c1e1442030032641d820154940d2a11071180c001c0c032001400c16001c491208089030348448481003c8007207104280e0366806030501c0181c502c80000c0003003040c0c40b03c8044100076400500141c1c4441c03800c520600302801000c1d00101a0917a800c0310745004600300f0380701c20050054580c2c8444c1107002800f80c0305007108054405048200351103544028510b04d5403454a4941507600075401c00c500105036041c01e103d110b01c00c807103802d01520250040c00903440c0d6641000f080300d0061040b60068400b05006 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 648208938 1250 648207688 648207697
    0x10b0a0605090f0a0b0307080c0712180e040b010902030703090215131e05100e10020d110c1507020a05090f0f060103020406020a262703060118110d02 66
    0xa45519031207601c42c0c020441c128030351042940c000c00b06014104280e07400700040d80c0d0851058184020a03a54660040289010b2030801a08000580c0f030003071440c40e0449500c0a400744441e82c0a5680c40c2c4030448a100346c00143c030000c1c0103540c008010010722140303034091500300d03060740741c042510681074000500030304c004054160444400201144003c00c0880610014000ba44041d209401c2100d0b10182c025450f2003070f607000b5401003852518152040c81e25441c00c0f000100314080b078041d0950009d641c0ca40c9114440c0100b40d00160007911607800088140d10a00c1c003c10340354100d400c450b41004a41c1201500b00d0b0002081d200c00f0074581d0350354100511504010700712030100c1c03410300700180c1d000310b001d0451814141b04100c20f000156001c074440700307005c2d04029540d400301c650308001c0f1040b034804c07005408160408104c801c2d40c42043e01481a19009141c81441659030000030162194400c2c86401021280d403001c00c40f0101040e0802c82c09818815023040c10001350103085420382e4003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 648210188 1250 648208938 648208949
    0x303040b0402010207120b0a0e01110304061109060a050309010b010e030c010509120106181503031b111e0f031c08040c090606030b040c030501030b01090e0a050d05071406040f14010b0a 81
    0xc604082040d18589845002c0a0202c95000bc2c0300708103601c00806c0d01848017034400b45c0b925490380c208c2c603101c06100701100d149003409840a0b90381c0141845c0100281c0060310082125424005515150741c07040081c40c611040040140c010703186007000641e281d40c03000300c181e500002c550085034241342080c4a60b01c0180300006160903e94000b0762030f9400c581603110700b00c921008900c01407000c0b991101000c21100700d1141c00c0800e0204e50304101030361410a84210f03074003013000b07a06105025510074111084c51070603100c00e1b00c0c01040808054844280b22054401c2c0303e030b040c0c943c1c624584521200340c0c0003409000c14031034040d16008442c061b107440c0d8009a0100c1e840f88104100da003418410300040d025245410071140d411a0f13550041d014040c800e00210503107541e28001800c1090050030b845c2c1d079000742296050803400b80041c0030394100131401c4c3c50601b0817900320301c0c0d04100410103a00c25540500c1c070710320320800c2c1d642e80701420000e20b004010703a6503140408900e0f41c0700d4441d114050070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 648211438 1250 648210188 648210203
    0xf141311030f160b0a0e090403020f0d050d060e1501050a0903200a06030c0e010311040e0f011d01140405070c080720010203090d0204020f0717130e07020303040b040201020712 77
    0x440d140780d200f401c000103034030201001d078040100c1c000300303644030040300e00130802100c03200340944031403e01b03e25040b40c800091040303008100c510300400d81c1100c0100a18604080c05111041d6030b04203078468180e0031034004030740038014440b0604c903600c11002402c5020716400c02400d526101e4907444914499030000e202642c0110003620403600c1c140261100410b03061800b80004201c40800403c1407984122903414107440320b0358198420900c906550141c5030b100796114152420720500c2003088003e1289015000d5542059852940401c3c851410b030303400703000250700c00c0002406100c028140205444200102140c014000400d5140208a11030043c5100e02407480ca4200c240d099142e10030392181994820880b1410544481021505c1b05030103c030f0060320b651542030320340000e2060240003011001d10392203c14081c00030b0400340200c4016a10980801511b40c4540340719031600f074640744003503401400020b00140071b00000c142c4c014410703c140c4a070f4507601c02c900c2e52602200c0c4800c45112 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 648212688 1250 648211438 648211453
    0x100203120403110d0201050717070c021504151e02071215140f0403080108011b0804060204050607150f020a050301050906040e030a0e120a080a050a020a05030403150f141311030f 78
    0x3d41d000600e001c5e050f2750ba14218074281030000c40544240e8041000a0146611440160740b154881007998000e01c4503034038440049000080c000e2441c014006142d080d0342c80e211074241ea880c40041d095080d241c0c82e4845c000122180d80f2500c12581d040c0d060500095200c102020380327030000054090040d81903200d41c2e4914105440e003d00a648160403030b40307407a132500000e005401003c45551140300c10341d060100407500d0b50305200001e1f02c599088603404c080001030510400c01c10015010703211601c040100b10b00c01604408500780c2c4100080b450000e07106100501076807030124030503074020800500029000c42c6502c40f850450300200d42060128165640000060402100c00d05030300080b24094181551503036990780d064001c0702c220a0401a0104904161900070800e600c0416000750459403540e640b890310000c009680c081c10320360340c3d083c03203020a4072110301d0203000040041000e6032200d83c0e40300010101411510b21050390b04003900c41c120307446601c4c1030007500b40c134840341005407056 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 648213938 1250 648212688 648212701
    0x1d090d120609022106030105060a0b07060603020a0f0302090901140103060c12050a050603010605030a02030d03230108011b0503060d0201030203060105130f0302010e06030c090415180614100203120403110d020105 93
    0x4d034100402040c06641008200120382d80c45012072019100c3d12078000b46c0341d44103402e0400c0103059135080207403c070100304408101300515800d024102da20885180c040c035510b4a01080c00d0700c0707102c00c0014a11890100503c000b40c80c1350080b10000805180400710002221015400c0d198141c2c1d054820641d41c400340722203424280154006020268010155490940e0201c0d0781c4e011241601c1041540d41c0798031101400b0016040d450040c0d080e0905003040d41c60b0541c090080840d9010700309008100424001084d0043d1705903481000014000280161140c0064000c0e61000f1320300b0b03040003401c1040a0b000348616002801601a0b12a81c201d11421407001404508080c0c0c00c0511540301402081030551202d0111003200070140c80114920b2981e2841e8100040f490f040003081a10340c040d8183c10101d01e0340450b04496480e0410084500c400c1c0501c014035108800c10710041e001006001c2c004144201c8490300144039103002c000c1d6039a202c1007581840500800000181d44403404e0119 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 648215188 1250 648213938 648213997
    0x6092d030709020405090a0504110904060e07060e03101e020a02030706230c070503040b0d0b09070e0d2414090c090f0f061809071d090d12060902 64
    0x585156002140f41034140400100d140200030030515001e616000017604014200c074072034ac2543c20140100d1102d04040c60000c0241101440c0b4240310300c120540012a5440351443c604400e8000d0044c0c159070502400010290540d185178142050a00409810030748052000f4500c0c0e422aa02031a110b0040d86021000d40e5040b0384e6203d4499100510171003a030340c040c4011a002902082001d03502c0e44246131090031406254040200c5030000310354801d804c06036410032a4103560807941001250356105041d10341c0c60f042c92950740c1050820200c2c000280c488043c000c0c511502c242c8a0080135280c0911000362000c005118080c991650284260a101001200021a42150301ca5800e103800c45c690f0020354001001e064070070410710301065040e254107455407104044030700304031828604214815641c01c2c80c5c0c401d000000b40802008180000c0b408150fa0243d940ca1000d00310060341c1080840e07106036160708161506503265000144418035100904002c1b8019043c0c4140000100c3c0700c54 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 648216438 1250 648215188 648215203
    0x13050f030c0717060720070b040e0f0919170a0c030206010f14060306130f021305150702040c1e09090f0e0c010f0306170102031b1806092d03 62
    0x1a03a000710343c40201d078100496840e82c07201c62807410900082c2c50360804189040b0390101c0c40c58501802c1c0c404100440020020002c0d140d64242401d029125102049144002110f90280719000724100203002480c82a02e0102c450045082e0f00982c00141090b544560040084001098286914400709501480460700410920903044000c92030082e041c000080d14140c014840c486c0040011502e54446400c5110090124020000310021002d0b00000358030540320f8100b4852007402c00200d42ca4a0030498401d001c48190070341c20002d0030703801c0c800a0688072324a1014007119429101d000b00c1c1140f000b22134484244d4440c513900e45424048000c40e1800320341c0b101c1e444d04246695299034800285805100c400f031910803030f85020700c2401c50043c425a0403802c190815511000301640054003c0d6000d8410100c010703804070070b0070540c4620343c415810340041c190741c440052100c41c075000c0c010700745c0b030140038040f1010244906426010f40300c041c40c441e0303036090b1103141c000000c0c2401c01041 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 648217688 1250 648216438 648216449
    0x209060d02121f0902030c0c01020c07030501060f0609120303020c06040f120c020603190204080d05120a020903150a1803031d1f050402040209040c08071107050a050913050f030c07 79
    0x12184a03083c540c43d0b404031a10701034051115000004a04408001c80496172010b80501c02152a40e84d1420842d46950031448103231465800c00e800464007100e000883c90440303004d501e80700a200c0c9041d0400f500302030160000e401b8954244001c48a0398010310ac072500c2030340300b00c0f00368a01c032159150102c80c6201040003003041011948251005860340c80c122500441040200d0003006031007101d8001900c5140c101641c1802501c0324a508203810034090301400e1100c0920105580c0c0300d01125080f8010340100341d41c1075106444466100348140c01458001d603000782c0101310700100c0c622000506001100880002f942c0e110040d8507000244441c3e0300e4281710b0009406030b400900541c56070210700c15165011160340d0f10118045556950440390000310190090000344811100580780240848424000c21007200840b00c4010300468070300f0a40394010000e0300c00358145010b001184070020b02034071180c1a5003100c400464000c0206042290300000119910070a00c0701c103a003044c2050307108 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 648218938 1250 648217688 648217711
    0xa1704090606080106080c090a0b0a020d030e060615030c040f0e01090b010e0906040c020c1f080a02160b0c0705070306050a0b060c06010b0f0f040b070c0501050c0a0201030f0209060d0212 82
    0x600415600c903807001c3e000381c1f1099845884602000004e05561515400b8110000001440044180e008a03600340000480c1d00c080105d200b100c00d03c540c80f904c1c01c84042d9481450043d00403003007003c1501030350b08400710030b18040c10142ca47e209040c800e01e498001d40340540710b000041007203400a0007400c0540d90f00780f030f01c0e0003a101418085114141301078403251080b51952807255041c0d1080094080c410300041842c1e41d94124000c111180501051450300000c50000014140641030700854181c4210311703820001038107aa490341030b0302560140020310305a40c00c12018000c200c04004100255000b178000054500b031080356501207840180c41c450003560f0900c8006010301c8081041811506400c002d00d03681ca21903a80311189101c0c42d00d44811054003c00e002c20f00c1403442001d003a034141b1443d144440c0f1a103903001960f840c0a880c07403510255000e07140c00780040d44681c108090040b0120350142c2449080c00000b00d490700111144105268081444010407201054042e003151403541e4 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 648220188 1250 648218938 648218941
    0x21216060b040b0906240d0f0b030f250314010b030118050a0605060609060301060c12031109100201180503071a0606040e07020316151a0a170a170409060608 69
    0x4280c101c2c00081c6198800c0140308041415022144951b0119035a20244640d0352044182814020728080b08000b200700e103007c80340302a60034009540d28403000c0580040500a601d0060030f1070803074030a201a10a408035a1700000060000701c003256100b520000046900e80040c2d041c142141d40c40040030040c0c0003405000c1c40411008a03011140c035801c1500401c0343e176100b1000c600b071481003c1c86d041d00142e000000140183d0302002c0401c1c40342c03103080c0001121000e51400ca0581c2d81d0081c180604d640304102c00c8140345094440d8681f403a916000104140d4041c1800b500361100213202510550400103000c801c1044e103440c102c4c5060400d0044808030304101c000b185043c0124040c032407210400e8808200f01a0080080d5070700c1402c1000e6605074003160385031600c0607044404100c075103181010803c1d98591410841c02d1082d4002401d290b81961905140702c4503812140c1030b08200780200201e000109501005461030080b0403035040d540d41e4680100c2000b2981c10f98016000c210b0801c0 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 648221438 1250 648220188 648220211
    0x606060a050a030504050a02090c07060501050405040c090b28050909120304080d06051c030840080a0807120b030309060d0e0f060703061212030c021216060b04 70
    0xc00b542ca030141980b80000b02580d4504c0c2462070179601d4000030f54422070000c1044a0a00840014a0340a11582060005903a54418071058986c00d590080184c43c4803a0300380140b205541c405102084000d00901c3d020102d691608461410505425001030101006102c6401d00481c00358000c0c000c20014401d40004601c001311134000074000428903030000a0080708801aa00700c940030344801020140c0c803152640080401c19140c400032404242c2031000102c01d0211580c0b14614000b80381c84a280f20442c00700c8221003207080904c0c5030080c1e401448040042202c0002400e441c426a80365401c4608264030094a51038444503456125130174240c10781490344005c0300b591410f5500761030150300c44140302000d90160000503100300c3c0501c10740c40341c03120161001411301d01612094138100003064503001c900030a0007800a0240400440b0040384003104c0c401c1e0700400c2d003012248140e80340b003403154040300c0080d407001282c50200e4024640640a100040c46800c04181049804014140030326 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 648222688 1250 648221438 648221447
    0x5040302030d0c1d010e0d060b0307170c04110738010e0601090e04030909090201111009030e04060b09060a0e100807021b01020c0d15180614090322050a08030a020606060a 75
    0x1f800281b00644644c070359002a04d0401201c00903000801912030b00b000000c0706030740e40d0200070a29a10590410070352500070311a100c103e4011755081200320b400c2000c2d0544907042c051440300b0035030340c0c65800080c03102803002e003554142c060b168108640307000d070a0080004007620141e070080312002c2040b20070701000a801203400c10032140ea8110118054003140016601c580001201c00410f0182c0c04d5080102c040a0f440f81c1400c91003501e40c511400c04643c18002256418000e45030001d00400c000c034400e00e0804060041030400745001d201034480301007c1481c0700303449010a000f0820390418018080c0c0c0502c48010074040c01c800d0300908032281d00000f951540080000c41c058406104800c00b8800c20805c031040740b00840c0e10600c00107c0f41260200b0411117200d066688901c3d044152300d200070943e40150003000d0300c00046041c455110b550503c0068000f0344080c081d4400e45001034a40c40d0f02d00e210008040b468043d64440b104c0900107820850010308240c03040000f0070607803075181e810 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 648223938 1250 648222688 648222709
    0x109060b0c0a2012031201080102042d090204031227060507261806040302090106050309070906090902120c031c111009050709060b0d05040302030d0c1d010e 69
    0x303007802003040584070b00310000700e107114943d03410900c241c1c400b843c0c2e800b0000042012207200c07003140320240e03a10b40025080340524010240410b80300284407004032400800141d407184a07002410070569a88006002ca80c86640101d0b00010804ca180a03400c0d01b0405800c0100c80c1d48000340708851042c40c1211044450340500c0c410703c0303c007007209400c0c0010141c1028044003078034402e070408440e03001045625000403101c05120010040100e0071170400f07000b0b03103080b00d9004c1c00c19001c690800c1010b8031550130003401108a4410600d0005000f030182c00f03400024010303a5400680451240144005401d1099054000b07501628800e55143c0f000916014808001201070781960044c1c0d00403980184545107040d6203100d103600348c540807160b0350320444080e07129200300c1d108169129811016154244100003840f042440070a121138001d42000d40e0180c072902c1540d1518103809025800c0b100b40114440015034494207c141d8080b54558030010402c00f401c0401980d1006030000d00302c00003 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 648225188 1250 648223938 648223943
    0x510b0403021003020c1515060c030d1d120d0e010902031506011716090614030a020a1b1b080c060306060705010b0306010b071a01050f22020409050109060b0c0a 70
    0x100c4002d0350900c0d11a505541220f072100c400d8401c40d00004410114604080e50b40c4205501c6090304002c0b50324090080700c0841c030900010f9802d2414034a0448018803410051a1500300a140c040c00c4c2e901d0140804181c4150185a09440700d10800409044400d00e154010380342e850061004090781d4001031526000300c2c001100032559a8980040304c0c0303959031120340300b010380a003028802070306141d0704901c558101e690740d000032495a40c1805c5a054400c0503071550811010004908004043d400030b2841f0051800c2280302c54a078400c1c2003200700002901591034051003400ea0010b81c0c60303580108010030fa041c00030f2000c2d0151000180841c4009400a8412000001c9400c1084001c0d0010741441c1c100900f514800e607034500c032108081c0e01c0010101c40c00c044801ea0580000c5007015a14180ea001400d041850101581070001e19a440440b1100766003910305000948030041c0000c0000c1c0130003000102d4103500d0210203c065480c0d40e00580102c000a0001185054001880049264 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 648226438 1250 648225188 648225199
    0x50f09040f020616030e040c08011217070803160207090605030c0d050114010e0f130312091103010612060608010209010816090803160506090718510b040302 69
    0x207510005003584035480140043e21400101c0505260f00318000b42940c0e48180e13010b02020b203000d80100c400750701c00d005180840c04400b254030049850003c1c0b000ba520182001d552902d60162640c1030560030031201c180c120040e20403035490781941442400c2c01030036002410300003a0304001c0000d48445002e00860b010703114600103541800001d4002d1219854000400081541c490355014200c0000300c0784500003c04020119000c4140340000308441da8040d07440c00e1444282c101004054844002d0030344580d46080744d02e2003690b800784604070051a075025000a0010b040c030303004040d20880e40c0703e5811648148035030701d8117982001c203144d442204025807030647c002940e0301b03441562882d08400c2c00b0344800300d25501017111603010000076500070400c40d0496620340c1e4072265205c400e8081c0c0d0085007480309409054141c0f9402c1030002c199a01c010089112841400d080d141d00e0544a101100b5a00701c0c1d0b003100d0f116600e001a6070610841400401d1034100038511030a445a84002400340c1d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 648227688 1250 648226438 648226463
    0x51509070605091503100302011d0f04050c090415090e19060b0303040807060c15180b06010e03060906012d0e040c0902071209080f100e0304031406010f050f0904 71
    0x242d1300c121200d01280d0552508a40b28142007418003c849003030702003207000c41c0401d1a81602c4c2640192640f1812400400c0e1514807400e160611014200181c18081007800500c1180320079034441c05248441c481c40100b80704200e18042405055405840404008c0e822250314000f405108020803100140c200201098180b40840403030b103513110b15884441c2030b0081d03e10109146030700400441180d4010700034001c0101a41c40380f48100c0e09001c43c07601001080d42c5d2444001040f11030000e610210504248460a10140100741401400c071540d030282e0b00403a0051049400c40b039150700b0094442c25282d402280b503070b0b01e00380381c0d02c0f9540581148039004000080030055817440f040080d004070001907440b04007a103000c0800740003001c408800b0441034280854034210015900d4006003684008103100d040b4000c1d0400100800200c20302203020400c0301101107001e55040c1d9007130b401c0010050025614200c041042000c2c1d68000750310440000b205c046503560340c001041d40140d0007490390200b0 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 648228938 1250 648227688 648227707
    0x2130c080f090a150b19050d1104021b031b0d02061311060712030507030b0a0e04050703061b0e0901051005090f12012f0712020f07030b04051509070605 67
    0x34907081e00070007441c8410404c0d160451650310313000689024003c0c0c4601d140100c03125042401c1442034001d6513040195a00d40d030010417401800041aa00b000c0e04c014504180360101346800070000c003a502c0582e00008058038100500250f8056803000e10b40982001c50300030300000d4580001610220203000c10403200f4040c00500c0000c241c00341c00040c1042e5840d031903440c11110300341d0f01039840c0010a04d0140050f0f03020b8040d000c0e501000c0c030300a101c0b505990030440c040b24840d10151040d141440780c02c80101c0020715510035070304c44030440c00d5081c942c4529030000a0000180440c42d40c003031161540104155241c202c0030040e04022410520f4a032200100400c0714140402c9802d40e10515500800c0c503641010340c0400d40c10b4426100052018060500d03c0d000e039025524541e40501c02040070501003201e00c1c4001c0d00541461040c0c5a214441078006443c20440b0b130402d5911a40c0841400100708007048060800c200c3e80200d2407051030035803a40f80e15030110781300384020b0090010b101400c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 648230188 1250 648228938 648228943
    0x915050a140c0105070908100b090a20040b0403050d0e0f061803060f01090c0302070c0b1c020f0a030c170105190503010e060a180b0c1c02120402130c080f09 69
    0x30346000090080013030f40341000c00100f801d550b61141c034070140601960070711503041c030340111244a0800351000a035070301c543c82c0c3d01c0c1c024001d000d850f20085503039148200480108400920051024030b400360b840d42e0450401d5820b04075036030268810701c090302d0603440240e02c3c0e0409548103800211156600c030150301c21003043c0741c46840700703969050280c0800c00c5a65400f40d92014142d906800c0c0410900310440f209034102e1040c0c4d00c01400a24a41c0010003c40c00c00c1c000070502e0783d001c101e00c95410440c000200059070401c0502c0780000310702064200821b9410b126000c260080361400e482082c003240e4a00c18652418011030f8040c0d481260f56403018002200800e008203806802000454400c042c1182c580b030b07058500c00304003803c10708005208403200c03904a5134031340c01246548441e04c8280314030450740d102080405001542c1c800350710303102070f1510151050352000c51620095280620400081056070003021100e03519000002c0c441c540c1c40b86505901c41c1c000c01700c4448580b11142c1f117a1 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 648231438 1250 648230188 648230197
    0x6010b03060a090912030c09060c0f03090b040314010b0a260f0a05061b0304020105040611010603080a111005090703170c07061d0d1a060a0302040606030c0915050a14 73
    0x3c0600f0040d40c00104094075440031500e1900342d07020003190f03038504401c956086282c4151800035006400940100e48003031380004600b031090425222460b0744000e0800c0c035402c02e910503662004040c80a91014100780640c1003035502c01c40d03410b103886050000d59070384100784c2c450704c01c008103100000c20419803082010703440088044080324441030041ca04039a440714101e45020303036144101660002031b05c5035400d40e4000ea90503183c890805090060032100890f10031811100c0d0340d00c5d407400202284030071000701b850408580d5841208001c860403985010410808180c080f4505410440a20800b190580075603034080e0700c0704412080c52041c1100b501580c0e54405e801d0041c1e04000500eaa0065080400d15051402c3d48405400c4041040040c803954040508800c01152140007628154004560b005074000c02c5443c1d82ca45980100d401c03614207400403008682d4a0300120001e5412a142c0c00c000c140440107011031645c029070080050060303407802c009125154150310341e4100c1481c20746 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 648232688 1250 648231438 648231449
    0x30903030e031c0608070b0304020108090a0b270a120509010c0b0c0304030f0809060a0507020307060f020417210906120a0f05060303090a060806010201110310080c0105030906010b03060a 82
    0x1039880380d00721a42450f840b0314080b44581e803d0b02e090790014a80b076020070b0100484641c1191241107645980066070032030002495038105010307542440b0005850403541c1809a607103130000210455001c0c202014190010f21301d01050384c4451a41800075000103281c0c4050b0135149081500c44881c0300050301c505855020041c0304074103035400c1101c0d040d074010285105034066954a204000740c40b5056505004c20f4070011600d400440000d82494807507041240c001c81d1910460b8038085440d00c4035400c441e500352460051303640002d0704100214a28005000380351503400589502003040d01403107010124415144400d51000c20a40401e41da401c055420b110462a00344c0d490313141c42c075415070040401408181c202d915090118030641400000d41d08524000f0380900e01d0b0b5400c001007139404200040c850ba044ad0b4039280b078445444096005103014180518040e401c01d400d0400590a110b145100d59041110a10403c03c88400000340c1c24115080c6290140d6a92250004a0411b00054010 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 648233938 1250 648232688 648232693
    0x60d0215131d061c02041e0510060206010f050901031e1502041a18040915060821030c0f090409020a121a0705040905060d061d1516030903030e 63
    0x5640400d00d151800102c0001844098956416007040341c2038004a500b03049260f190100c0100608184d406041404002401e522540302580349040c02d881040702c0f8106189559034080244540400045000d0314003044c8441086003030002048480700141301c00b400154850a25070220000072042006498001d15114181d40202c250100030750305c140b08075030054480021000002c400c0340242c9000c1e250740240e080d440c80010f010440501009641611207a2079070035219407049862280a008000700c5000d0015000c5040c01c15011610031070280f15080410420045c021500c1f0b02159407450034079004580700c5007103201241c0201840301000750446143da00c0494141c080c007081c044d41e83d10440b00c050340381e96200f841c001d8500080e2111000301d00c040c03006000c2c401d09078001560081028100c1110012541c85400944418500000e07a5412034162801040801d1001c06011801d200d580301c0c1c5810585011040c1040c2c114007641016500c614100401d071103500700b04c0202540004 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 648235188 1250 648233938 648233977
    0x50601030309180507050a030b01020114180c040b061209070b04350c0f0411070602040501080907051509010c1205090a09050906270105040305090414060d0215 70
    0x74050700d4412580601d803030a528103444000c11004034001c07280305451550300c150030401410010b0f0007805609074118155502e030031354007500384101c074842440342e03650322000f503082c11540c01e00324280f040300880381d0f0150f8207110070b040c500e48a90044800140f002034a5420540d9401119828040d0b580c10030301030726200044c000b580d0010205e4052140100845d28541c03803e842c15440c1a01c1c02d030100e221070580108101d5450b61809142c000422507010300f020401a1500d101c180c031a5119207012074081c0d901003400c0c005941e1103d0403640c02046a0010150035050000007403110094111111406000045c44046c1ea481810310000c101d9101440000510315200040e02e55041401564040d001511001460600d103016850280d00c241020f05070a4076000b0203a2012050002400d01000b0486249009a0424852184290b0113507450a40b2011036000300000e07100f8160300422913201031001e00a0b5550f40806409580c5e034111400c01c8100a03441c0e03012154040c0b21801020f9010301340 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 648236438 1250 648235188 648235193
    0x80f0402190b2206020321070201020714060106080f1302040209011b060b010813030905060705160605040f0b070203150601031b0c15051003080a0203040b03010b2106011403060d05060103 82
    0x1c0742c0f4903a83c40700980105110752210390881e964041c0d21281d20244441542100700c19009401054201010380f00140c506041d17501c580f80020712181900111382d21017401080302981c4022400d03003042c184550750600b81040e80c0c1011014000440180c4519800600600103030b0040c4207040d11200300307182d601141078807070804400502202c1c02c1c2c0345c003047d9054001058040050505103481d54580c0380c080070641003509028461b002410f00300c80611580b03049400110750203108000070075003036a42e00d030f5503400c004040682c00a80d0380304510b401e07000c0c00345a005a9000c5a1505102c00d0205c640550741e4540740102c1c0a031014101c595144548001c00404443e4040203d8200340d004407100e69103a02c1050518040b80c00c1240c03070512050034200140300003404d5000901200100348110390426880d5140781c5261303030084e0312012078820001422100c50441a00c40000344944181c41c4060340750000c000383c4888d0b4030822850862100200041150780c403140c40007646500003088950703542c0c4a2 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 648237688 1250 648236438 648236467
    0xa0b1009090629030d08101a04060e03070605040b280302070209060916120e03030c22060509190e010b0a02061006050a08090f0607030f0c080f0402190b 67
    0xe41d40c4a04000070440c1c0d01400100381ca99103c01404040d000b0102d4503880f0504803107408000d0095060f01085040004481d11114866282e030320b190750704583d51301c0c034000020740141b05102a950003504413100801c802508a81607408a484480c4100d40d290b0f8155020360f1180034481456001c2e101a0040a010b0303640f5030b001d03140c0c4d030348240c4002011b0740b00c01c0c0401c43da4400846034503c1e900801c003a80c140540c45040c40103106144000301051303110f00760380854255082140c08910300c0a000c11113460303014050003c2c0200640c0218000c518500301040248144a44210395000c0c0d045203403010780d00119030042d00f0007020405203881d00340d40c480e80c603004a07a00440b4403400511032400414917040709403c500b0120b4100b626038525000e0081425550460003c1c9121032902455012503d219000d000c49803060700150f030001401c0c00880308213001c44010100b00c0b0200409801041203100d104109140c004e60100c0c1d4401e004201d00011910782c844036000017100c5440841c0010521080307 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 648238938 1250 648237688 648237701
    0x6041e0204060e0402030c180607080307021f200f040306021903060e09190303180f0209090304080712050a0c090f0506041a040905010b060a2001020a020a0b10090906 73
    0x390f54819110b0301c0700081001341c1c0015030313021100d005d0400801c45212102d0a0300c2482d010b0103004141800321039207072103c00360011500040035800001c0301081c0905410491061994800800c02540942c11000000900403034603109080f200060519012120002074070001d50b4408820740d036500c10201100c0c3e0790803105c222100481d04101e8049020b10118600b688100580001804500141c94608541040300c000c242c0c03d01d80d440e54500c00e059443c00300c078030790940640340c20030b140d07030152041c00700d80c1100609101b086d400610041c420401c1c0401c04c0030458001c0c611050700340c3c00c41d0030280c0c10710796a40e100401501c01c6d5040011106038503000004041c1e040c4404002d01d94481c23060000b9102010300500f00da415218082505181640c881980c01e0301134000094440400c502244586c0e100d95510404a00c0f55422142e00c000150b0455800c1d681400c001e41c00d001450f08065512403260781c004100c107d284c0005240450003103120030041500d10014010f00c196418240000d104 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 648240188 1250 648238938 648238949
    0x31303081807060e10090605120717090c0f12151801020c07030501062103110a02040612140f120f0c071824140612090327090f06041e0204 61
    0x2c0405d04131030050040016108407881600c4040c503010101c04100c280c000018410028409440601c81e04910702d0420144141c402500a000084420007048080e15030300c40840c3c86800c00070100303003640b0004250000002d207200e446402548504a009030078000350821700009602c003003449524104001140c0c0304a03030181c0d000700031140d01c4400701840c1c0d0300400740905d1510080030401c0002845628000d0a800c1410161382e00340c1150341c0050280c0c0c1c1164000711900d06403100305070502c65512140b07108150b2140082041d5009460320544414400000d00c0d800c50700820b00d0700c060680f841c1128210340c1c000094502684c0c0751814141c2800e003500c031040c185031400c0c460f0f00400c540d90114820341845280c1c1d80b00e03554680b03040c0003880d00c40c40420b1500120700b4032071104040702900c0d0702402903110001464407400000c160180c008150444002003c0000d0610032580d100c02c49200d8015040000664517aa5103202080c080e1035032480c02c40b90142100ea04107051241030340030300b003506c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 648241438 1250 648240188 648240199
    0x1051008070e0708090a0209090102220509010603050c13120c060509150c2d0607170402010c060b0d0501090b0601030606020c0d0c0b0414090705031303081807060e 72
    0x98541a455070398020340c1c014941d5042808001c00c01c0c0500403590142c0c00314849048410314102a0b01150442d14160f03104c00b1603a401140d900b081e0715a0208280c1071480c00188022454640800146203410611510301410360b10b101080c4900c090002b200d850708408003c01120035510b08040c0704035255020103864003000d100c00402e40c28466011507550510081c0603402038101e181c0d91250a13071214600b41c690303102c1d840c80501e506840c0b080700781c4001300004505400411020b002818400020300c008108440003c14005041c10718a58541090302842c01c1c2e103410000340b41290060014410059206002c60f43e104100b00c07054000c107004500c51614403801c0d0321003800541c1070712001c0c012880581c1101d241244c45080c900301c1003403d5400b4008007075141c0c0e80c45503905030350b512903000a100c40c100100c40b0016428510340b2690812200e1614514520b400b1a9110800c028a0b82c014100001c2c8030102d050f00c0c43c02d580500d4030480d054117590f10b0541d05e4a02401e1040032101c0c0d2800351 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 648242688 1250 648241438 648241471
    0xa03050d0c060b121506120d0509180105150c0a0c1e14010507082104080a020106080c0d11030709020313020301050f06090103080a11100509011505060a050a020109050109050105 78
    0x908100c1111100840c104c1c008110b000410f2548000460000b0a0b007a0014410034810341e901c1d80801c5580284c014545809a0740c0550000303102074a07200e219160240301c0b90b030004201548400590314200d21411032240d0701c590064408174101050b42d84060064583c119001c00d00904446001414500c02491020f400740d880103020401529400e9641c00305202744109000301341c0c010000c0c808099550608000e107041c20004149041d0709a4044d0784441000c10f40ca40299024031070107014103500380c002c00ca080781200000d141c8400e81c4000030011a0090301d0320b507040c1c404120311409801107440c15074584c0b505288221441d400980c0981c425030030310000c10f1008080602d9280101c0c40944513180981c01c6031110015980030502400401c80444000311904105010400710071815400c049030b42d00b01032146c2c5080d00c11340c1014008185104008000560f00c1d40300b19001c1d0510b40c10302c1925030070b035031720240d0051a52040141055082c920214100310065204610a82251884071000d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 648243938 1250 648242688 648242711
    0x150504080a1b120c06150e0f0c04051e01120c080a0f020c0c04020318030406020706080c181003021621110309210d0f0e01110c09060a03050d0c06 64
    0x31808030350005008407280c0c40840071414420756801403001d0169002141c0e4400300c2c04200d00011070742c1d00141101c03008105018450222620b0940c001076182708090034503040c0700c0081c0e4924a80918030340100f2003c00c0601c0280d000d201504818071070b9203010048208903180190140340d0444000141a180c202e45048a141500c25a480c500c9240000c190402d2143c05110007548042c00428003a40d110000e66a420070400040000c0c004903030141000e82d1406402618030240038100114201c814000e030780903400018140680c0302000c89628240d0440003406400902c1089a18408900103da280061200d580010740d41070481041d4100c5200802c0802c440c240e03030f030450b000090f42041110041d149844895040082c1b036034655444040d100e8102d4510b00200c0400d00340229006107544c200b1940c003c0015021480f081c2000400c4050f02d0310b0b083d0300d0300f400000c4c541c410510803001c18019118010001c0243d5130000888c1c80c000f040c10f4006c0d006081d0010126103480c00d02c2c45c42d121 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 648245188 1250 648243938 648243977
    0x703140901091401140103060f0b0d03031e1e1d01090c051201060506490b010203040f060516120503010e07140403060207171809100e0c07150504080a 66
    0x380340246014151705a42580d50b68005002c01c006811005c0791a03924040c456560584840c45041c446d40340014500c2c1d0281454001007000001000440e140110b41c0340d0103100855080490f0f042d541000810513411b40880500721404120800b8942c40e1081c0d071801c1142840c1e000c41a0b0744c0072a030761540701030702803c0503007a01c08601949030010018001c200c1501146010400e4010700b9a100e42c4100744000380208001141340303800301800c4004004680c00c0100e5101d840708035071b02840954901030406012000781c030302c940302d61401c0050010300c0007a494503060b403c807402640000c240611008801006010b50000c0c09000e04406100022070013842c003e44500070100007902c03c041c1028915101c0e50000e403c060000e80d120036071403000b003c140300903200038140702c4451610341c0c1040000030248074209800400600c0108411903090280c213201440940d030240041e0b140a5441a040c5088002d0103000744c001c91825080c80c09000130001040040d00071104075645040501e84407021042 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 648246438 1250 648245188 648245201
    0xe0403090b2721070f143001050a020403022e1b05070602030c1c0f0e191712070b0103120c050303010b1b16150324060201050601020d14030703140901091401 69
    0x65207c00b103000301180610581081444414221041c0d089072544219140d003900d03011100305444990000f03040c4118503040408181114043e0032102000009010380450820035801d13800034020f0f202c0b2500c1542c01c81c0610040550750000070750340c4903999050041c0d901d810002170211303203014489800c1c4008448440c041a400c42079510340d507501d9013014090350443d40f5255541d0b0000492802038500e05001e5032030400412a840507007284503c03a003041d6090001110038101112820000c20003c80d40e40168241981d42048410750006003030346041d02c0036000903900400320301000c000003c581c1000c8001d00100b518800d0184038401c60010b1858a480c0307007450000225144030010b1191a251240c42503055006007030014902603140890030900256901c0c07945065000e04061050690a01900750058800c0c0000d0002c1e001071103020307000703103a10030454003402e0010000411161081d08400c0c1003000900100300f840c10700350f1916010344403460b001e0301c45130b40c160000454402e0500c140c0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 648247688 1250 648246438 648246479
    0x31a01120e0f0a2607020105030a02040905040c240c02120f06071106011203081b1b1f020f120405011103090a0b0117190602130e0403090b2721070f 65
    0xc0d898005170764019200d03504050b20703609000d0307402d00c804034044042d441403a007e240070350315103001c2c00d2405243c2521750b04003810311601012071001402c0321a8000c800009050340c102c0d01c0320852207030304400368513242040070304001920034242407150303c0307070030100c10440044a00242c0e8036aa885000d141c0101a0403c0000c000030100b0000071074404c240301c1c1040380d000c280c940340341c9001c05040000d2041042c00d548420160046403081c10f8400b0b0f003082919914800c10001c1d801c02c008580d000c442c3c0c2c012460b142021403846400502000429444040280d202c5107203242c581c180030807a16134568803110220740b071840820000c03502c00c4aa60340040208188401004469500c0c9007941440b10500c0082f15219002d000c0c58494480c848150405008800f0300c2003c80d1130181001007880003030fa8000f200c00c0360f042140d12040d426840804103c10802c09580340108880740108404040140c26002c00111880d61404010008038000d0308450841620300c0300c0e00c0d103550004806064000c2407 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 648248938 1250 648247688 648247763
    0x10e0f01140d0303090f12030c110c0d0b150d08030604140c0d0c1106010902120a09080304082208011b1b030809030d1104030c06031a01120e0f0a 64
    0x1440300184c8250890074009104949141071b10301c060341c401103800310b1451400007180e212000150708590083d842102404100002c0c904640c20703101146440103940341c040d05100c041c0340005c1c2b01d20100c000074180500060007504000c03a15080840d40da4005550b070611a504003001c4140c82252004128080c001e4030071501e18004101112600030600501808180007503008600c02c0644180310050092220040c00350742c820680c00341e1100c42e80001c01c8010383c80d24201c0303c070b000308a000c025203500c264170a01260362092800c10202c07010300007203024411103d9080300440c5004043d0090360303041400703520391016164042400e80310089610b03a10030089011000c81c0002c0382c42010121b8011041c202601d10309800110103c080d03e6142003895100240010200104004038036414010810b07890108541d14030300540d10303e0604042d800e2030403c1504201c000020510307a101602403071031841221541c40300b0390354050303d44c6001030082d158404e400d40c5080301b0080080c680390b4015581981c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 648250188 1250 648248938 648248959
    0x140313090b030c03120a0e032a0111010213090b01030218060a1b0309030b0708010b1b240f0105100203190903060911120c010909020d14010e0f0114 65
    0x904030062600c142038552500c128a4094031a80b41404019031050101c0c16841e030303400301c05c08041c08910b100740869010b80c5c07052101c2481341f0514182c00c0300880c208207a100c0c09075081d20040300c2c071400000181c1015440064540d4090304003da0440448121030001d2044644940040d022070158044000d079144150921191501c2c00d10000d1241704a2401c14031803031414000780b02070621058900318086641e61740c0600078840c124406562088035481c0c003d02d15810a8000c9800780611903200030f40c1c0c000740e40c510940701024402c00f081c0700c01c64044902a83c5502000c50348042c000d46001440ba100310f0004241410700312000400b0740245d4004615118014045008014500f100c0e0401c00c451601c0200c0002d00d075004a0f07110500030b0001d1041202044200000301c403a40c1000d00490b80b144d141842140d030010205812034112413801600c8106100401c0b020304502465486040e40c018004a00341c641c0103141406071346501e07601c00f1144c1c1c890b0305810280c0d10403602103a2003444800c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 648251438 1250 648250188 648250199
    0xa12020d0816091a4f3501060603060b13030219030501090b0403030b0a0509060f060403060507180b1206060c030d11090f030606180c130f03140313 65
    0x2501c0e00c1000d000b01101c1d841c1c40c2c55400018050303010b40000f05c3d081082190b5424a02001d400443c107664040e556403214400c1002c01082407021901c81e0700f07220030301100f4400c215010034240040c1d82003246d06030784030402110004ea008142501490f00441e00c1d2140c007140d10308030032080d6268a402202451901419902000200c01418503800c00d040125000840000e00a028003400c1c03d220b2044410309003400e15000d03043e03035802c601841c0684030b10401080566181603500d40c00c08003d80e5924421206000881c405206540025004500700300c04d000103507a02901080030348180000d10300c0007988400c04580d1178410710856074200c0351a400410400e10b071840042ca1085880c030100e03860f180c1002c84881c242c07040440000004903000c42c550640f8200f40184281c480b100310064166840c02c44005140000b074160111020348031003002601d88440902201d0f40010450105c10741c0580d5010b02c15200d00035030004031010f403040d00b000b1080c5040081595464090741205030501420031 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 648252688 1250 648251438 648251459
    0xb15090a1212030b131a040b09040f03081b031519150518040e06010e100b030f04020a03140307051e03090f040b190905060109060f0503090a12020d081609 68
    0x1480015400241c0054018011115202d034204070003000410a07003041c6da8104100441e0b8404101c540144a44410080080c00d5001c1c0c0400c441d505050001907516905079000300200c00108403401c0a40c000140702800022005031302c2c0740c50342210700207000200c443c04440c296105120b5040d50181c2c1c803420244c46030082000c0d01c43d0900b07844d4119940d101100018003618891040003089421020040c030500c102c03009490b03031040c0009e061212061820304c4c000c00620000f002051040c25480c0030034110b50361150307050019500b08100101c01c4a00c3c540b0180c03a5480144204d803075120700b190762007000b43d003400304180000e540750181d8180b464400c01d00c00f1000c1c010944030350195980c08484c1d01d5645003080a80051205140c09501034200510142151303805840d00b4148410124200003441d070201402c00c3d51849480d0a90312501c0d02c9445034640401d481009221004240396000c541d039001500c8580c0d442d043d91084a96200c8503240f008414402441a00281041505104441d001c = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 648253938 1250 648252688 648252701
    0xc0d05060f0124110c06030a1406010302161709031e060702010c0c0209040303110c031804020403050613050f06010303030b190e16050909090109050d14090d02040b15090a121203 78
    0x611301a50408121000007410652040703401c2e10b5241da0f602c03410743e0584600400700c0d5020740203013011440d04455640d0f102002c054900010040302424403441c10341012082914040d4001608903070100d03c041c03d041c1c1820300390310182d81c460300c9001c000403403041c414040c86d886085980c5032b00d000e170140783e000c2c4501500028401e8060503140c1014078074003441d9800600c050103082c0d01460f122a842080c002201d600d00b0116407250340140f0041c000b1071000b107842d9800101c00c2c4980a0910107610f0218149038171440d5440071406003400000505406800059089000f2280c904000750141c18040e4030601d40d00650020304000c800090350039039590140e212034a030a003001800c2200440c0080d13030080c01141c203010565107400000b002c1040801814003103801f2410454a40c070000d024000e258061016818414440701c1055020b540703541c1c0c8031219075000a0080d80c503c400101900d850f0f9030142984078000c0d0b881c1100000c0d0801801c030074070300d00766100e076048803a072107420b008034040c0c0407 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 648255188 1250 648253938 648253967
    0x7030f0201140a05060f0103150909020a030f030c06050f09060601030203090304080111040602070b0f1c09060c0e0a06030b0906060702011403070309031b02010f110c0d05060f0124 79
    0x69814900c90070503280c4102c1071007990740a4011481c0e241800c1801021403070101140d060500389040c50406400111410301969035818001500e4a241c2c00002c04501e1280e0003c1c1c080c0d505500004c0c2490350110240003400c2c090360050180d41c0742c40210303100054040b1215402d5801c400d021443c55840790300219080301004044078109a12080c40030b085944904880c0314148000400304000c0ba01801004020011444224107200205680007100d00c10010035845d00d106168050040301c0203540300e84800f41d08150100b1901d00f4802016024150300b60306144100d810803800200c5078440c0c010b881291101605440031501d4800502543e43c004003012414041006281100d0542e07000117944076900e40e5402082d07100359400c1c0906140305075030360034584603000151440585d8001d498681058418906081c509454042d0203042c26100d90281d50b02508126580e03003804130000b0381c640907420600301091540d1f65443c0d101e584607100e00035500000c0404500304200c90007241042d80094 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 648256438 1250 648255188 648255191
    0x80703020921010c08061e01090e190b0f030a11030a02040c0c0c0e0103082b06061106060307060e12030c010504140124140a030c090c022107030f0201 66
    0xc82240054032440481c6800c1c00200051508002c41e89404d0143e403a00741800c0c1021909400e001e00400c02c4000d10804800301202500c004130426441091680300030007048a00007003505000965441116611840c600014240b0080883c1407511b50008141008020002e110038009076840fa07580c0248a0002c1d9494014062648056251801a102c14072a6969009849038070f070b1030154041c2a141c1c200140343e80458006100141c80d040444140310322a41c440141282c00e000076098407400c12507106111401e01c0c10018040750800c00c0f1024800f4404c060315080e69640003815981c11052190b000000d20401006015050110641d5070841282c01900d01c0d00f00c00070f0030682954000d68003190300d490302d500940b0507040b080c1b00300085000410304504440034202c000d10843c0a072406420304030800004948800e030f440c000c240000790b5001c0b15100700d990381c0c1c4041c000140040301400016010b0b000300b00c60140c8400c5200c84004200504903404c069490f00d0403151a54121014020741d07 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 648257688 1250 648256438 648256447
    0x406091e0e07181404050a1707050d030504020f0d1511090901090207080c061906050402031e090c030a05010c09081216080f1801020d2d0509060a030615050708090108070302 76
    0x2068139400038030481c0100010030400c4128540044a24000300d2200c910505c240000400204007050000d41040c0074a000326903529540001803428124048650340f010728082c200042181d075041900c90102200c10400034141903c40c03001c800c3c41104162076003c00040c0c0140451a1143d01030720540b4042d80c081c07805e20f19011910362a184041c0d400400720141099450f59a001500810340138001c156415429814843c2070450111406c25840c080f541514000407000c080400030039412420040c11111b82c0c600a042440c0249940d0b4450300004500807004215a000014201034603100505c40a29042d003850a0b000040b0302042d0803504040200080c1d041f943e0707a030000d0907803003441c95009250940c4200000e460300d00c282603d002408800350300307010b10030303c40ea0385054803c1300b050403002d58a000d140200d5140c0710300706d21954802e0010540302c4806601d503004200703a44034200744025103104a0015181c0c0c0c09100e8004048101c200601e002951081000c543c10000ea4100076050 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 648258938 1250 648257688 648257711
    0x6031b03100302030106051c03080c0f040b07020f09040b0f0703060b0c030d0b0f0d0204020306040b031203090d02030423031608160b0c07150e0406091e0e0718 70
    0x20340c41a12048a0702001c01024010740ca803c0c400c500041c90202e610400a00c020340c1e5160b0860011003000e0180085100040d10314282c00f0108c829000c214203005684c0d40d107a01d0044150707003015409038001c140606900100d4201400501d01942c0c02015076040c9a450114590440500500c20030030107440303090000d840c1110402801d05110b18002954841d03000c501c00b2030488511100a520480724003150030042d856103110540140c1c2c05403005640c0ea41d03000b0100c1c02030301038414201d030180300700031014030344000c44000355000b000c805055904a4400341d00480e0390f402540220325440c042c0c1d00c3c0340720350302e00000c7c1c4014a0f48005000d0f01c0c8000000e0943c2859407036683e10018064100c1a118214140c440b4500e1002c1c11040308100d003003110207000c10f59181c0c864051b00e10351000388160385d555103004520a0010010041091090544401e0141c01030958403407100d4010300a940001401502c0e07020700800080358000070010a45040d403c942140280c01c0205585617862042c01a03 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 648260188 1250 648258938 648258991
    0x60906041502041508012301080a020a02120a03020408100603030e06030604150303081509390301090902010e0405040b0406050c0405030a050d110a030e04090309180516090806060603 80
    0x3444d08107610b91031060b6141400005441560319110b0751148182c3d9004041c13603170001c0051703400a1040000680b40d54400605a02c0c150031001c000f40400300100c0c071209090781c190000c100b40c41004090b21103562815040b803041e24000c0c000100410410358032603005003000d801441d170140000300302007131411860703406030906030181d0011350001f0030400070011a244807184103400d001c002c1e0707054440c80c54802800a8405241c4012040c3c3e11207811107203035041c99a40070440f0610b0308040b4242c1c0c030359407500c030403008090101c02240403e40e00c52460782d035803510b031141038403c030b410a01c000880e640e50361b00c0300300402d0300500300310240740f0a00001c2003070b40301000304400d030901c80d000404800c145040040d141c400c600010254941c00f056440c3d00003035001854004410b800d85010031815945d29003910303100c690fa000703005030b406580f411070541d0015421143c01480041070600902200c0d40c0100c1d030221f03181c042c5141355400709020440500781400117651000752003100c0100304141c041c2e61403 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 648261438 1250 648260188 648260219
    0x310030f050c01030c0906021507050c0601060e01030c0e1e0a08191a0106021e0307080c10050114030c0d0609060e0601061101021305010f090302090c130806090604150204 75
    0x4403150700156040b1010750309440f40d40964995410801c2d201490054002e5403901c204413800200c850380d0f0040348070240117400b9900c030380140d8000c1d95000c1d80c481c1c070002c0c01c2c03001d0003d00a00084c10403010031000707401415840d80c058005005007000b107110141942454a800c03621039000f103081c260002d0000d03004c0c401205602200d01203410b049942d81890044c000040501e02183c407001710040100d5500041c1d40c0c907038280c0c030700300081c0b1420650700300c2401d41c014054084d01049001881c641e071510041446800101e460348200500d0b600ca64401c0d030140300089502d60154880e004201c124902034160286c0e031031040030041010200759444005a501d1036107441903651010005020b0103400802c00340c0401c000ba402142844600000c118a0380b006104280c144901c43d2071594009101e0481c90010715005010020981052000c1900c01d50181029054054002030041005500858100d001c1c80000d0300070a103540f110348481b041c00101240800c0b226600708000111040da424041 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 648262688 1250 648261438 648261443
    0x10c02012a140105220c05100816020f070512010f18051e100507020c04090503130506091e12011a09070302031b3009011518020310030f 60
    0x24080c0300c40c924000e11201c01e090303242e1030640d04100400000504040080700f0854041d4a001d50442c414140b090011010f030b048290481da03205105045281c100341c49a00840fa0710707507a1400040801d8007240c07107685480e0940714030b070040c075420070007451305110f40b0700d4402c014000002e5204c1c0604810040341c007401318000900340c03441c1d00d61052140910403a55141c1e40800303d0030081904c0400140c9400607160b02031003081da03500204103014820001d030090550050002c010746545803c0650362034100034440c0c1d88036810034130046014180b03041528000d1001412070a50511000006544011007040e2540c020665402400948009000d559264520365110100c050100d00074002030580087c4521305141c01002480712480701106007401050f000341c02c498446040c41c3c05808060140200c403006012054020710944c07036080314643c050300111000304003000881c42940141000703403295500015003038805251009054000b19404070558984401c180d0300c03a5240d14080c00890000e = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 648263938 1250 648262688 648262757
    0x1c151104081014010e040f06020702100908070803070f0b0718030b0a0b090c0d050919030809060105091009110708030a0911030c150d090210120c0518010c0201 70
    0x1d0b0805070381510400c00340840114003a500c641c1880288072402c00b016100925070b0700304019040078403070a941501c0d650742d0b008100c44c14007403508000902d035004030b000783d01d181d02610800242c00800001140c040c240e1084242c0e18015242d156600211002440401031050305824084480500d101942c007031841103140b041203080400540c001c460046504900a10003407043c0001d0151040c10740c3c1800150304004a055940c55692500f000a440358180c130b51030403202244105a000401d4501c13501c4070708200c2c0d405a0340da104215084030155151511421410024081d20110703800c00020007021400346071410061303a550084640c005c540c40032540c1d9841443c0c80401c003078000c1c00142c0040803030045c5990560b20b4000340b10300b00880d070801088280040d881d0303607600c2c4d9a00300c003414980040c2450907801c3d807590060104224141a680074a03d0000c01115050154080d10410402c4c0304d9030384200609030740192106030040806a041c0300e22007080002d42c0740404000403030704088021 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 648265188 1250 648263938 648263953
    0xa030b070f02010b0f13110409060815071b08070203070b0d0c0f02060a1d0f0717060103030c12050705060703021803030f030a1104240801051c15110408 67
    0x1007141d944482008216414580c288046507200d80c0f03826440c00c0c00f180c00400103810030340d8003801403100741103042c580b1001007400950009254080003c80d1040700640d02d20b07030090112003401500440780c04003c10304070700c644034246400707141144075544981d061070324103c242d400103072401c4100e9224a05640c400070b0740d01e40891450150340c200e95039a0802e142000c01c1000041c1d15848010195558550740341041008801004207040c80c1822200a0f50940b041324900d0a0b20707030707209000701d410f544086806e04030b0f8900c000500034120f81c0c050396090301c550741036038070b5605030f00809508008111042c0720341400302d00180407840c0a1006600e005903222031203010340c40e00c2c0403d1048544a07800a002c5200711807a0310341203d50000f00c0304000a04862015032031302007402550030401d010f841030030144140c164030503491003030b010090720395a10710381c5e0311401c201c5103a010074140038000c40607042c01310000d50182c2d2414010034480c900495110600c9140440c00d41050f849802660f00c07008 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 648266438 1250 648265188 648265201
    0x207050304091a0a08031204030806060d110403021801080a0807081c0515030a03140901090b040311130506030c09060a0909050a2604140a09061d07021c1d0a030b 71
    0x100c088001e007505c20145003807070180e04051015000050000d824400d460f80000c8035a030759042117500d030580c2c01034104070310348a0310300ca00c8064004e4003042b0b00600001403a16030409881c1c0605048030980307001450f8029503035584494036003280b10100d400340300900045160311481050708032990f200440014451401c880c0c0e40c01ca451030300036070034001c1e080452610003299101031080760034521301c100c0c40c0d42d800c1402c00485405401c0d40c0306a02e051004240401000510425503c02d800101c450171113510004c4021803c441c010395215506512501c0941e10301e04002c0300301e551000c03004000074003060391007200c541665955502280c545d08031044100400c2980c864000101e519100c3c1c10318512644081d00300c05101c8e41c040c085843c14181c00c044065920000043c0240860400a1014940c0d80c0c4100a01c1d01092410030070b01d02c60300000800940c400507051207044800c1c5051201582e100b00181ca421001541a030040715404820190380e444014107040110321613010540c0b1440c102 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 648267688 1250 648266438 648266449
    0x18270e01051006030b0f0f061210060e040204050d0f030c0b0106090815040b070825090501122711040e030702030d0908070b0a1b0302101a060d0207050304091a 70
    0x83c0c024209044c0313090003901d51903c518814002c41ea00a1b9080c242d500182000515a802020408981e0f0001e170420030070207074900d00a0400305c6406484001001041204002c1640140c1c0541038100030706104007004a045c0541001d48a80282440c0c080ac10071501c0b00030b51480245c100a002c0f8130a001b08000194040002d420071070850394503a0301c68102035441c00816034018140408000a88001c45d58036904400e180380040c2c46842d032440120281c1c1e40c003400300c100700d03c00e0602007000026018080c014a000d2501924507649940f160071425003072503020407c0e030300700070780c2e040384117181c0200d05840b14405d088800000200441d00c5850510426103007010502022003003082e40a0108007040d0006006410303203508000450300d401900b007089414a01d590404031010f103914025409154000c42d032101c0c0b1403002601400800700b40c2101050801b10703246c03d560821400c000d40000c00a403503024180712449001a2840d1a5980c0e11460699050401c1c07119488002c840c2d030704d0b1505c1c10 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 648268938 1250 648267688 648267721
    0x211e150d29160507021906030b010905040203040507050405150909010203100812030a0f0219080a062106020c0f1204090f0915090302120d02040f0618270e0105 70
    0x103507801d0025600d46000003030240d0310202c1e0010148000428064210740d1807010102911070700c0ca01c4100e10729580da4009015080c111081e5010500141c00420523040c9402240e104070b030000000d21080e4a800300384401084001d0850031041d94050004c2000e41c0e4904000340183d1b417000000d40c903424545050b45c203a101a80c05012658400d07100c1c0c0c21201184419640d0100100c1c0703002618003103040400d0041d00c20082e981c81191440350340801141d0b000306800b80a150104020044161a456403940c841960098910300541100030a0b0025072036400825190b40d028080d58403910406003036510304403880f8828050207a01203014850324080b0b128101c480312404909000c20140750710741a240030860310006240684a1543c8400c1c503008006014801e500c2c0a11141c0e6240601281c9000350003502800b04081075003c0700080c034500c1021029682400d421030b506486d49003000c1800b0180784203089400110040c09400801c04042c031412629515240001c141450b2041000003c40007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 648270188 1250 648268938 648269003
    0x90b040204030213020f13090c0e0406140d02030319050a020d02010b0d03051612020109021306081c1206030602040e0714031b040306090602211e150d 66
    0xc14401000540c1e10041080c050404000006035108425511501c051191a1700403880c02100e000002e00083c081d800b4922403030403590745840c41341c00281004160781c50b901c9029411000000340c0c020078070f80441906449840282201d10780030008607039140d0340801190501c041000032410f082d40c0760301404400c8101c000c80c4000c00c50150b420000496444003480088c041100c0442c1035036611759540080c0141a0300008034210200701480000d000c0c00c0707440f400300d002d40700080c1c108581c8440380c02003906a8160002034050082e14404040c3c0345450460443c00708040c091080c15101164402c07100074500a9901583d16410410b84104412018040008000101c444940740c240400150b82c2c00814604d004007441081301c211340c07442e004681015000500c3c1607070003020881c07a980101614190640080403400039000c0140408000702c44c400c1d80d00700d0340c52402011010100000360700101080003101e071304c000080030a00003c0880002c450b50501c00d40d5001814181c0c01e000c02e001c25 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 648271438 1250 648270188 648270191
    0xe03060906040b090a032102070b090706110c0604030204020903031902030717120a0c031113150807020c01050702041122050d0c09020a020705190510111e0c1306090b04 74
    0x2030480e078008100040801c841091f418400008404c014095012560040e80182c400302c61400c2c1074031901c0e15002c0718400c010109220003c03c5901400100302862125002072043d81414559002c1c00702951148541c0d9a040c003007000303100149034407101005034031a2a40d00841c0c030341c40c0f14904005e821424130306008203014240808154107020112144d84140c0c104c00100c2c80c4030706050f09601400862000c020554008501281c00c044d00c4050002119400520f10b01c0904108400f940d504800f51248801070b0080d1451014a50042d00208801440030b0300001d0345507141e042801c0d0390782180d402d12030701070022542811802660544000a0042200c0b1100010415902c4441455240c4030b00f030702c0c55401260780d03c485802802424024900500040c0c0f50302458054401d003c009030003054880d850101030b86002510429445400c004a0710040241641e010700c0740170f80e0304e40c0b4159910316100340302540c2d81c951180a0884501c5d1001100407030960305210f000f0083d00c4610702c5150189 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 648272688 1250 648271438 648271453
    0xc03060c112d01020a030b1507020306040f0c031e03030c11070e10050603071107080706080c161209050a0e040b040b0a270b060a080706030c0e03060906040b09 70
    0x1900400d81d078074284a007200354840e035881d42110402d2440303212a00c0b25035520100e034038800340b41c050700107601c0782104980c50b803032190914560400c180034080001c0d405d54418000500042c00e0300c5c80d804582c1e406201c0f03400c249a907030780e40c0390042c0b0b0982407211034080040844404064042c05020f01420302d50900c3d440c0a01c00464841e6990014890908894070301c0340401d079820141e03100c2802415003c0c05a075928588020094990480c40280605600c52080c0014691001180000c01d072040e030f0362016803e4841226070034194100c0206002d0050848900030b0000300c0c0b04c464131003641c00603100c00c80c2c054600740030000d06500e0380d0701804050010400f01b0002500041c02c260340282c0c010442c1581c0c3d110a81410000c20303849060404100c50b40498040f29980200d82c4240944540342c40442c5a03229000d102195a0234410001c80303900182d0203120a03070094109014102c0300b4504901440c01c01000a45040c0c03068440310b02a41040303040c03100740160031443c294461035181c02841f06 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 648273938 1250 648272688 648272717
    0x2071b06081302190608011d070519211d1902011b0b0f160e1509041e020d0b03030a080a1d03030702010506091b0405131104030c03060c 60
    0x524030001d003451592400300038410210f5513900c149840c00d0703000803051030758580c9909014003608028090f00103100010811805102c0b965100584221196581d0070308062810700ca00500710410141d0406101007462200289184500400a80c41030b0305400305003000745400d402c10910790051601d0150300140000d40081c1c500d00c480013441da9082c648407088050500030003071140e103405030080c0f00c000780c182440842d5140608041c0181c01c903501204240480c00e43c143c81600c0381192250300200b01010f42140000c4100c0a00121080a4004140b40c0302680d03e10b8500070a40c0e650401c082d501103400e400c901c589200d41000007000f60011403824014010150420400500ca80241612449164100000307959607024454000d001c403622414803403406030281400300d803403900a46030040080c42c140c8000d4018440c001e00d00c0d004520b06800e020074408401c40c0c00c05402801500c0d40030035000303440000e000304010350058000031003043c110307d0404155814111034004000c0d01021b800700 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 648275188 1250 648273938 648273947
    0x10080a080306131409010509011b081801110c01022205060304120c0609050d080c04180b0a05031510050117130501090209150a05040923030d020d02071b06 68
    0x104902c1c1114214654003c075001c100281c88011100b1104840100034024444015002240242850402840311382c80c0d0801c4c003146c100c1e04021100008a6000100e400c04070100c0800c5120001140040f50391014458107508a0f4808241100941e500250481c2040000d2010102e05e02d0f0341c2c0070541c2500c1c9007100254044c00050b002070071190300608142d510324051210200f880d584038505104a0303500782040341d02c03802e038072252101190304c440000b804200c40300c049506442180e044280001d4505a610340100440361003660051404000820155820080c01c103601d503000400d4030301d074608610905078a01c040d5001c03034107002da581d00d03025035014000080c517408000225400b2103020305040107405440b401d50041e4201d0319a0b018049031f03200c5455600380c01d840681d44002310b1503840081c84104d6610141c050701011780020001c0c20022380701088004103030300204480c00c00d003025819000321703403003444020141a800110041004001090310040d07900c820642e020443c0762040141 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 648276438 1250 648275188 648275191
    0x5070503070f02160e15010905030d0f020c210d030902060a0c050109020424060215160c0c0803040918051005101d0a0b0d120c020109170610080a0803 66
    0x2031200518441030b040d442000740001048044140d1030104c1d54400140c2c0343c0c0d80c0107a07040041e078800c6019009855018011030302c1218805401800c0542d058402103580aa41341d42070001c60140e03848140b019075801241d003c0c20303070300a0140703010440d0104c500d80ca0904000140c40c24182041012405659450180c9070501140e00300094040d517149003541c014606840025442031514040c0008000360480c04c012014003210040c00315615900e00b40c5e0707681088a010b031002c0c0213100c0003440034038141c03c40303040317010840c18015580d200542c1e802031312410343d0300882159400030a08101d0742035a805203607944040e0701c10b2a15120103a40f6425280c81c402c3c0c9550186171f4450002c544c0b920340c80307220381004140504079420558000b81d201402110280c0ea500c0d0500c2c10076040d03125034900038000380300d26688160749a0003201850030566000b001c500080c0e0620400100c0051078410028404800540100c06003c2525110300701e184070015035040401c5d540c2c445a26000000d0310002221b = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 648277688 1250 648276438 648276451
    0x1080106020d050a0f050c0a140d0e15070201020109020d0b071b031d060415020f070927110a03060e100c170a061502100e03120f07020f010501080304030c0905070503 73
    0x20700c00000075903006e6442c0d220b50626405c003032003003135403035814000d41700b02d0401c3d0382003800700340d42c201410030340100c4098003031100d02a403010842074480800304a00e001411000c0c818000402c1800003600001c200c00b152040c10307600906000c0c20403200c0c40d80f104c00402d400700301c800d9080248100341c800408080d0542c6400f5020002e2042842c9141e0321b6100340c4006018021030600c0320208844000d468010b03456200350903100b020070202d45116a030103481007164062844010001070581c0c1d014500c03a45500558030101c50140304052a1940901c0402450040001190940072882c0491070090129600e8078124600000244851344c04141140c45802c54022044d05849001048004044651280c3e6241c010764000441c01500400e8180d0380340c00003e42004000400c0381e5880d00c074411000d11105145038040043c4c0344803040e0107059007020082c8110303010400701c0c00003a42101c03401c1e00005425840443c0c01c02c10046982d081c01b010782406c0c40284018101500d003d030a502018002 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 648278938 1250 648277688 648277697
    0x402041404020c0f120a080c03060d02010c030c06110c0606010c0b060d021c03210e1002070809040908040812040f0611030c06010603060f09090f030e030c0306041101080106020d050a 80
    0x2440340300c6000304408045850941d017901d440041c0c03905030003099170041e030780341012521440c0003d10000c0803e0039607208001c06091444541c07056401111040b04400d011018441c4031101c8038082419449000502d100760000c055070780003510b0b001d80c580500142024100901d00869170f0014510701540350708200c003500c400d00c006034140b0000304400560701640f00f020080398400024194489100e0300d48013880d40050405419010300202034030b0303060b402c9080c01d03400b11780301c0340c00e03010f49500a240da10b002d403c201d414052050005070603100d01e00b40550700000b01040510400318180700070401c23601000c40c1c003031405142008800000500748101002d10032110176a0260403003e01c11503c0c1c2041d83c06c04d031401c540e101c090181c0100340c0c07802142d028014841c00030a81841e144205204650040307900180c040b86550103d03451200001601e816000303001d6848141d88041040ea805a4415901c801c0e0183c03095000505903401640403504550000c02091104c0d032b0440d04980b84901c05140c03 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 648280188 1250 648278938 648278947
    0x10902070c09200d060e0702060f0f131a0f10120f0204090803101514091e041a0f0a0609210b090a061401260f0610080c040204140402 59
    0x1401803d040e09500d9041d40707003000042c4841c0d144520780c031103802e40703c00d0038107900c2c152288001240d80311030482c0e041301000c880c41c01040114050803042c0364045641c005020340b0a140b5512001d21800541d0307003078a15030264041c042010f048540340c96100c407050360481c1131705181c00740345031600d01003990180c05500c40802c40e0307007075481d560011030002382c20030035981e66400d180203514140d0426124001d80704440c0c8810329031092082801c031429042004500b818038418030100000b0307891442c01c030034030711940c8400945140c8450240041c000001da40c8464020240e070240300c3d0000c06408103600c1400e80c000c00b0701411341c00074280402c1e143c5a05403850110221514408440c407d039030007500c0308003000200030b0b000b507000900942c2c1611841d01401503492480e601201c0d0301081c041c00003c40c00548000c440c1c0e11954803403000701071a110480d1900e1000944983c141007042d11901d92100c0ca118042c02813a81c200805140c041e82604d0840c90701d860680c084510708080d00c807940c400c0d0340020703 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 648281438 1250 648280188 648280211
    0x30807050a020402120103031b12031515020d0207140a0e15090a0209011b0b010b0c0709020d0608070803031e13051f15080c0d17030108070509010902070c09 69
    0x70811440365070283c801c40d42d621091003040711581c000d110840000300000030400244c6141d4484080c000c1d4001c1c0c0e0b03486902001501034010f04003049240d182c1c03803c000d000242106c00b12000c80018000e80c0c015112404040d04004e007041f2194102c2d03050400c0c60400b0603180e440d121ba148044a01c203440c0e030030b80390b2039108034110f083c0c0c102d80c02540c0c00300d0890203010140c8401d500905040d44240c0710041102c0300c03489081d0000706030803009018101d08800402106250600a01c003515032030069031141342d190080041203800c03c1c3ea0b440b400c6550b500080c401c0860030031804010b4407080000f982180381c84248103c402080c164a0f20416080c10042480441c030f68820070502d9074010f00380c6c0d410b201450107500704c003005170081c011307105c0c1807030010000c5016100858041e0b4034031001a01100403c40140032130380028080c100c0f0880d4a030740b0601810206c0d0400780d030103081400050020a8580750800a0702881038000950f181d00c10000000000d0010424104941001001080c00c01d50349 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 648282688 1250 648281438 648281443
    0x150405061618060203130504231807090b09010e1006030207020f03060a090b010527060303070b0c0901020111030105130b1c0f022106041506050a03031101060e07050403080705 77
    0x10542142d01a0001000c034520350040007a2810912030240e920b48240e0340c80801041d10640b1143e2464055511001c80511500342d00306588820180c0d4035401e54016209101d1a1245a0f488640c000d50ba94000081c2480d161140b01c0c010200780b140200181800041c0302c00d065114490407041c180d00046840854a0b10312044084003c000c0c1a15890314240070031102510112400b296081101c0c1c0000c6000d14218842e808078007684902031240003481c001361540031b00d019202c030341c0c035200600c640000a0340700c511042c032035114080000d032103140d42e100290039079142824140347c9071010301c018003464072140880c04454080d0407001c5691440c0d500030449c90788140101000355402c80384120180403105410080e520310035030752100c0c52456606a81d80c10251040b60703801542044000c07074040791910071020700c01030b03c0704400107042c0d9660300003800b44d20b034990048000c240c5100120260030800e110703020003072440c40a081c1c0e162411640040540c27040c3e000003805808049003034018420304 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 648283938 1250 648282688 648282707
    0x606061b070b07060b090105030304153603050c03010504030c08030703060b1305031b22060b120703050702060601020322170a0212070e0c090f0d0c06021504050616 72
    0x890300b01c41c0e0b50782c065040c240041e2145440c5a402192641c00020b114140001120211024141c11405203204085c2c101c4504401e40b01c01c0e010091403826070b03d00c4c0804c0400e40b56907003142100d42c0302014a0341c47e00a041c90012408c06110364980300802c40443c1d001307140d0241d03141c2c2c019440307580c1e81d82d02c0000741c008082a4000b40b034462004141c0221841b0703e031485000340c650840c1155500d018103142d04010b11304071301445401c07040781c4600340f01007007203c584180000e0340780d0710104050741ca84400007a103400c91026003a034411003100344610a5018031904d6003185144c40036042920700316002039660b10852100c5012101c4003003031581016554140380b07003d8030902c00e030340c580203840c40c0c1da0f26a24440d0b40300580c4a1541c1d80b0321000c1410002840c034040344e200d04081441039903440c8031414540c01009010b50843d207182c00060507a0344007003844c0e00c0180314907150809070b810004028078100744041d4079464541c80c1e00034071010403800034146070710001aa20f422580402c083c002c4419911 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 648285188 1250 648283938 648283949
    0x303031b071406190911060a02031917160c1b080a11190602071802190903060f02210a1d010609050714070210090f0e090d020606061b07 60
    0x1900c00b07a180d0003020106003240a44103610400040078420039010f8101d50211900405c1c04410240500080c14407030050861584a4019a41084151400107800d2038007030300d0403000256191410801800180a0943c10010700e541040321050400d20281150305100800360a0b01a4455941c200c81100c0c030350240541131a40a0715404a828034007403441c0b505404901d0702c01c82040d0605608981003110340411103007641e0040c0140ba1600817091031051032a540703465019001c0004400707207805c8485c0310822038081d0b0703510480d0034514105002115810210076028500401c9005444164048080742210f0007808100c2d16441d01e1a1080040100094299084c1d020883d0500b03d500706601c00d0b012518105000c0c05140d48884007107a80c103a4440c03000100e50000d00085000d402d0541c0003c40740012030900d0072510340c40301038800c0c0c00c8080d03a001c07014003854070f010803901c2c0c04188802d111118803800107060760700385980043c030035000f0202000c01840d0424101004c03030800304a10002040c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 648286438 1250 648285188 648285203
    0xb0f0301110c010e060412050705030d020318070b0309031836010504110a1d040f09032c0d060906020316080f0c180111030d09150b0303031b07 63
    0x6201d141c41e25441d41100c081540300f540ba0199413286150046603170303481280c0c015614400064000f105581d59001380c001580d080c80140106440582244010350040000d01c001c5201080e01074400341c508441754000d407105410030300501103d02000010780f034800b40401c142c154240c610601050441c49070118010000c01641b40d000e43c100ca2030300c2150088036440e5000b0049a0300d80b07041c0401c0da181e19139020b4012500300280110709101d80ca26003140c002e24405002000e000300c00007815184402e8509080e80d07514129002090340203c6005038100304a84050003071402c86060200c40e001d40301143d801410031020395020031055602c40310750182c2c001e40031034407030420155540c1049803044c21607012504010208181e414600300051280d591105554038009440341e0f200904500313090428180107200b07450032641e0074103101078007512101610010f04403050b400c08a004071001c80500140b1840d00a007500f0940340401103940c8a448000341c0502c6072143d88400c1410b00c1850000380504 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 648287688 1250 648286438 648286451
    0xc0310051806010303140913090506190614060912010c081012230118050a1a011a030403090e040c06020106141c020a030c0e06011d0906040b0f0301 65
    0x8101680290302070082603000700700007a10500100d6607400203000c00f40214480c0c5214002206c0070b000108081034010b0b180d02c0858064005207001c1d03821200c81121103400c4a002c02c00d20f9403170002c00c1c20402c48200d205101c02481e000030f180040c244196507a0042100003901030040e10741d03065290360350403000700800100101d0712001b00144001e4074189049009064001804c05a006522085540082a2444003100d0600c0c00c1e0380c4007881440c0d00760554840c0c48011060721007d030450202030044000d408104007500d40071416001d03560501d100e4065440c018420b0f0b001110b02c05c0d019980d840300c00e40d6a07886034117040d180f000d9142d0210301d8030210b86c010003081080344410701c1c0c200c8520b60002c0c058192590200040d02038503421071500314184041c02100b2854540c4110001c0340080e0004403290346076121192080240c0e0010b802e01003029050002035688050103010301c8204401c50b502844100d00016001040a040c1c40e1046817600300c0451180d03104c884521140b84018002c2008 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 648288938 1250 648287688 648287713
    0x231906020a021801060206070e0a080316060c020105090706030504030e04110904050106020c2412070f17010530100b0f0f18040602070615080c030f07170c03 69
    0x1140003480c002c80c001d0503504041c229415859004505980710703a006404666a00c2c20101c1d10580c03070452442c0d00c00340c1510005004503040c4010083c440c02082007071001e1007541024416141c20048803000c680c548800c00030500400f041c048103503401883d010600b81c4403030504582c4101c00252695019161101c8e22a180c030785040104031101041d541407140340c0e6580b43c1642c665403000341b4242c01a104505221502c07900164200600450030340d624100740303502082c03090709902101c03c00c0205503007100224815030485002c220001e90440e148040390704200c040740c4200c5049514184699030303294141c2d2480320100d00300340c12402c500220390b001a002c02d1290090801c0d401d01d94040d55003280040d140f418544250140c100003e402540300000b080d0031800c1382040100309075100b83e82800b000c40003c0d142d00800060007902107494042504164000382072110082e0f0765846a80000e0244070944c0c4003264000441d00c01140302d600031000c1c9441c642c201001c0d41c00c0180d0502500800412 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 648290188 1250 648288938 648288943
    0x309020901140310050c030c0f40081f0e0a05030301060e01140a05070c0b040305010504020a08030702130b031e070603060501051c050a020c1c0f02010623190602 71
    0x9940104800315154404210713082d0003240c00039111003480140820000d1202c0d408000140b44c2d60100e03000052810640c5507809401c80e046c001c134004040c2ca00c40a0780142c0c0c01584900410f48040d040f403003d2280b9041d101e660b00d031010b00142c105860210002440c82441d079004240c24041e0700309441c0001803070300e00180c80343c1c824040d20010641810590f01c07954483c081441420b4079041c040317840c0c41d4030494144e450307030444601218040c007a048017150303951909001e80001e610a000215080c00c01b441044003500ca00d07000207400b54420311510000d80d0f031f0f210f56203918810401000540000c1580468100382c042d00841100c0e40d0713410f80c960512800003a081048440e0350741c0801031281c40b80011a01031281c20191240d00074100c0546210b0b0039554821500507070071400040ca4030040c00c401c50700741001c8200780380742c100600b020700b6060ba400c01ca40c410b04005500c000c10010382071010948000f03003910342040b1152200308003845140c84400065500301d5005545480107030f80c9600095 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 648291438 1250 648290188 648290219
    0xc07142d31050702121e090a0f080c01081e1b0c0717030a0903030f0309200906041b050c010f05280203040b06060c0c06040807061b0f080a0309020901 66
    0x20103034600030004240a10101d8544000705a981e41c480c60408400044044100d0440090000303c200300f28074100c070380c0d601c40140003e0008071272821405240c8401c081c00c203a500640141444640402c104103991440134080f064016402e465206865200c0c40581c004000b132400120742000145207100c000700061000d04071400c4c2d1244917010703290401c000743c132805070b0300791382004c20203082c400c2c03002901402030008840d850345400241c60085032141040305542d8020b2641c240000310312801181400741c826540300358150b13070a00004400c0305c461303a030b280c4414247d4800c1100109901d0b40c0c00e00290006109000010014420307400e0403004402e41c40c0c03500c210440726001c41261140014403600075039102d140c0245044032190354030414001250300c0a10785682c00e01810744e41d41031070340d07807200a800a0301211000300b1540c0e0801d00d01070482ca4500083d49004001482c400002401d07070586071410030303400450291121134021098000c0c04507000b0082d409403820740041008196000103d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 648292688 1250 648291438 648291529
    0x2030c070b1b030f0411030d0507060510081207110a03061401120c030209060126091e0c040b0a0b0d0b1005031e19020c07142d 56
    0x5440b900c40c0c840110400c05207031260500351205100040c000c511980c0310ba680a4083e001d00320880303012500103801d0400703405900c0013040d4080f480c2c03001d01040e4458560701c0415420000c819600340201142d58407414026031520410000300c01c02085a00034407080b0186000e41a0348510f5100c3ca005009010b0f9000f0138550611440300026040340c810b288070714266045000000d801d800d54082c0b000355400146661306100c1c110580724130210210180102c411b81d81c1c2501c010700e04003410120b04004003441240c0030441181c803e038103034200110b2070301f031070b61008c480c0000e00401150214041080396880203075402000308080600c0750f032070381040000d80c10840d5100f0307030011040d41c00e541034002510303003401454201c8042903000c03209c0d1108036040010408501150324881c0001c8040e40d11030b5031361201a801413281041068080400b000800004031808182c50750580c7e40e02e64141c011040884090314941044201621646000b00080142c80003501ca18203034034022450741100395119 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 648293938 1250 648292688 648292703
    0x9091508011b08090607090b090111030304050c0a080a1502030601090b0a031e2307030f0213032102030a120f05040b040b0615070201051804051602210418060302030102030c07 77
    0x91490913000c2141d6118012980341c1d0354945040a00400040d00001241c44c1072105222890b86032410030409103101d50701c0b8400a01000d07842c03106102c146a21644115055480030318640005a038029041c110a0900040162039586150040350242c41c035a0240405000004806280079456046440c180300a50b0a81d2a00c5d40c0145441c001c8803d007400214070082d80080710707625804060041d540103134440c07402050780800070f43d4030003ca9100103a4409003008420701002000b042c0040c002d01e00410202403010b020b070802d40a5103d1180c0200b82c000c014004204031080704940d8001c0c00b070288821020041403802d0724002081c081d00741c405a445150703e500244c060303e00a8041d46201094103d05800c0c600241d0042d43c081e00664082009034200c81c250800039143ea00c5810310488555000014030b02074803c020342000400d10303643c3c42086c02c0380342c00d20a4440341d6003120101d030f024006090034403086a0100d8002c2125400007545540000140207180c0d24990140c407040b4001c581 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 648295188 1250 648293938 648293941
    0x1f020303011d04170d091e05010e15130c090504030305060f0d080405130908030c07021e0901140d140705010e01030504020a030807080c070315060e0709091508011b08 73
    0x42c8020a9003080390018045200c44002010000324503000d07000c02055540c0100b130b440410303650b070311031040e803036014501207a602c002c010240030f02402a00e0060304051b016081080e038035800307600d209200400d00c000f40c0d05181201000c02007681c072541c005140c1c50b44100210304003442d00801a11055030b55600c240301052000c1030901c1c0441c011001a54440001d51506142c0030a10031401d400510340070310b659851444c1070124062400031441044040200e0303070358400900c1002100e40010449905110b2550052890307500d07942405415602800641c00040507031200140107080c103040001c21801c0044888010702d100060304900b50781007600c03501020340e076840044040b201d048801a5010410140400225201100400c100d0340541440c910b0600004085031806400d80d0088405407406820169240c0003441290050b00307048009160a007130032078005041c1c4480d030245048041d6201e060403405215402e40758003e0421400900c40302c0c02e844e64030f038645400c140d40840881c00308030 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 648296438 1250 648295188 648295229
    0x601020606030a2015030703060f0e040201083d06031e0b030109020a081f0903081501030e01060b030402040e03091f0203130e04050115051e1f02030301 67
    0x52201d208501c0900244502c04154489104061550144c8070311040d5070101d0304940d884005001c11551101c140195a80c105000b0040485461b98003008200c0c0d81000e0500229600b42d101c1a08290246081210790f160f01954194400310129608c1e00500c5001101e0f02c0d0205041d0b1000c25a0f1840d004203800d2582c0e800142c0039910380490b00c80d041c9180fa4140310b4100415400040382450280000804002c0c0f6030100350741c18401c1e00300341026444042041800c0e403500100d46881c980c0804188804040b60350041d01845014010f00c00d01e030410040c50a1a074071030382c0314010354170f00c1200a102039981d452003d50642e1040d02d040e4040c5080212070440c0450010440e407240382c003d8512100c0e5a460600d0710350704281d06000c20b0440c001040f00c058440409000e05001e400c801104500d2810645040e0742103070348821582507003800050b403c00460b036503030303040400c3d0841c052542d11794400f01d03800103802c2e000c0000079800507281110440d5a50355000001e14141c070402c1d8500300c1c15083d5030 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 648297688 1250 648296438 648296443
    0xb0a0506010e0d0605100806100f06030902010e090402042007031e170a0e0607200606010801050d05071502030306180112030c140609240f01090e030d0f02030f060102 73
    0x1206402c81c0743d00c0f5925000824503441154042805100d80c41c100fa00ca0890a061003010394180600c0c5410103402d102c2d40411015000050505040405c40000e1a0307002901441c443c851a6110354401d100050542d140c540040100c010204044183c5000707407004154150416201500001c42445056204051206402410904544585c10100c40c0c8110f40f034000e01009044c00c80c0d46889402c1c0b40c201c16003c102140c01402d05840f29012403e040c505920813800307500b0746140c5544041309000150f41c1007081e10b81980c9056800c1582c50101d800c006241c448036074015040000150140d4054a90220185010305411500d4034680c0341d140c1040b08a00c0000e0141e01595180303c050f01d00028040c0303002c00c00c218440c0380034052060000c0f04450802c2c0b011280c0607599042030456641c110841c01066002d0100038124000c0d60070f00c0856403a1083c0140284a0060b0380c03001140900442042541c0503929000801e100080c04185c2e448003035002500d844413480070620128080f036002 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 648298938 1250 648297688 648297707
    0xa020c09010e060607020d060f052d010e060324071704080d0213050d030e10210b0303070c03031205010b1204060b01110304081b10210f02070b0a050601 67
    0x103990140340380c0c5500f001c1080541c00000c0403a40710003030070440d80004040d03000b50020a0350652001606140043c201c941d400c00000d0155145645008200e540406c440f8805064a452a0540c2c2280e07650f400440d01c0d2020b0040c207020343c0141c486103400303030035040b11120f031003007013140d0f01d1001c0700100600900360000181d8000708030003000d1280043c0b040e4694040c0c4445014035040400d855910408140e07070b0071000c038060f8001810340f0700402150910200d581e541c08010300e41500760341c80c0741304030110a613200040c050417030b9141e403007520036a43c0410558440701e40183c00941003560303910300a445c00e411030041c0d00c7c4240c00d2900028240c070340541520098104100c45500942c1c0d65a921801040d0424925050104c444085544104104007604c00307810010001c1c00c0007090306042e646a0500c0100303141c410883e10340100030303269000d0610800c2045002c505a01d545100c425500a4000c541000304040d1022030060184840b82031401d0241d003070604100041e859200044445204 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 648300188 1250 648298938 648298949
    0x305060a0902010e0909011a030c01020a1403041d01061202040308040608090a1e1a130312060e0406061403010504030e0f01020a020d0803100b0c0703030503071808030a020c0901 78
    0x1200040c024011a003215108600c1450503140b070020540021320010700940b48001c45a54900c9484e00c040c62000940404070401c0700206032041c56600000d50310401c07884006c20074220b80b4507060403500b00708152800707070030b086203441e1626800001102c00c407034092040000141400c4515000d040091085900307494214680c5440c1034140503041c7d483c40009440c00716a8494401c40e500803d8400b11180f000c6501059101d491100c03030b05240c080d81c0d40011071004580384040c1449410204066104e031810360504010401c0130f0301441080c014102a406204002e102500b08020441c03c0d600c1107065035220703e544010865140241801c89408035801000305105180111880ca4000400e00c0c0c1c82e40144101c440400250780860341064821104454400c0003000744006a00c00385010400f400301c0500241c1007001149640d82e0311280d0384006020b01c400000424a1280b142105100204900900c030305a5559000388595990244070300074018002c0100395034070b500d0901034250480b034 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 648301438 1250 648300188 648300193
    0x607170114180a1b17011a09040608061902040b030609060a030c140a08031207120905011107020a05030d05031f03021f0e04060f090c05070b130b0a0e031605160803041703040305 78
    0x2030910000000364400d85500b00c41fa41400c1c0041c1e1159601c0d405007801815602c0082d02d00741c1010300394140d40c11010034100312030600500090050354040e00c2500d07402001100c800d5201c1d00c82c800810500921030300003605506541c00086041d0781f001d240303001c06510694441e00060f640d00c161782c1e180d01900000b20002701050323000c144000d1203801c203940d10120407800001e00580c43d9075140e003103400781d450604c482100482c9010a52800f00344134030081506038003610303114074031140c02081440020140d0f030720b4401d1590b500d0042c4030b0f00d1b031078030300034560140910b10750384072140710800d40c50340e0300c001c0d030340000c44014083c015400c01d4081d120484d000282113101840c100100900038150a6035100c040210500940c0081402d00c0405d03030040c0944028109056601d040c45c03004150700500910096080152100c8846000070403580b4100c054a42319000f07005502d0714030300b441503000c0c4042c4103d004520200b11000040001d00440350202c00c42074100046045098407401103200290894 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 648302688 1250 648301438 648301441
    0x210b01021c180f080c061606020d02070f05060f01091b121b050403030210090309030f02010210110a17070f1d150304050607170114180a1b17 62
    0xd4941c010800e0072030040d04001488a12500140395100b5543c0d02c0150f825680c03100070040702000380083d115114082d0703034242c078000703e280d8469180303160100c00904007a03000031100050205581950903c96008541c12182c0e152030401c15500d10050315940c20017845540005104082407040c1042c1e040400c02108050300b0341796003910408258604011455105d5102038250300900c84110342c3c5240903200c5a07110f03825400d000349081030000d40b100c4614600144140880e8001414004507070340441958001c00291004030f00b0004030417072444e4001d062506410205058801500320f80c0086e588911500b00700020021900105940c0f080205482036041e400180c800c01c550f4404000c044a8040c684260340081038030140c0e288102e004c2e04c10044140410800180b00f09604144035107041240c0c401020312440942c10188980c401400a0a003910b034161070300e500d0f44081008000d03403080c80e441e2948400c0003030009007100a51189800380c840b0010703802841900e00485000c40164101d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 648303938 1250 648302688 648302713
    0xc0a0318172101030b1806090a1106070c09020d0c0e21070806040605010603050619050405071202030112060606050c1c0c12020c120c030a02100306030210210b0102 72
    0x11603001d80d0402c403541a4615060344010b2160407924001e502c40d8841d4402850400504028540405200700e06900500180311200200040007071134a0b400c82c4610b4204400a000038181e8421a071004000581e00c4030000f031450316a034060040c103c955a414005010520f504642e0f80c41c0c5400ea0540c000201c0d840101d02604000c009036040c2088001c079400561246051858010f08540448855071524014032000b40d250152a400200650f03030036924030000001440b0401d0680111402075607030f10001082248601c0791403a00034424142155a542c40c0c2c1201c4544403e041025143e031400e1010000e030546c07203981101c4203d80c404010746803100d2841e41d24244580426440010440307480c0b0350001041c40100f00410366400c0d0340042064480c29018081c2c03007038040c11440004d81101081c6003e68178003260441e0040c0c0c0c1221040002424840c05400170200d80c0c1020390070120149080041980100c0c003407010ba0304103244141c1285003007200900b59219081c1d8a40160480d00d50000f1 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 648305188 1250 648303938 648303983
    0x30e06011a0705330403050d091110020a020f0607020603010b031b0319060807050a031119030803100509040804351f020408190f06050c0a0318 63
    0x102055060382500d00002502e03001d14001c1a5005a41c00d0300301d208042d841042c41500134044084030704e103661507524150b02c02a0180c09581c1a0540c0e80f0788590710322040241d120200c0070341c00c200038851113a200400c1d8000b5035815803964102e00a100442444403070745040800d89842e154001e001ca850341c1c2c244481c00b61560000b50101051100c11118100c40310911806144950b8005000126a8145490200654206900c001090b8100e40424029600c1300d41458094070307000b503150f0711240181d4011440004000c2e404010350303e9100c0c404010002407000039400790f034540041d40e103800d407504104070b4400b00076030b401400c01008220070049052403c056128003509405400f0941d00f214880314542d0610820004481e0401400441c810360f083c0803140c8010207a0004504080c02e1815440d907600340d8000c0c00800703954080c0c803c4100303d0b03842c084100140e1700080c107200c0fa042120b114a416000210501d021030300b461042615480a20618108982c101010300e000003680b500340300 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 648306438 1250 648305188 648305219
    0xe03030c0417010204030c09051522021e03010f0e0f06030a0f02210303010612090b040f0c090207060209010e01030c0c11011205010f091d07030b060a09050901060303020d030e0601 79
    0x402c1d654003444000702042540f0003440040540c1c400114051400032010710302030440c01c500522032040e0310f10100000700f00125000c0c3e580780d05100140c0e0340303076081100c0101508032400343d504d1500000000c00c11032140034010f01201c10401d25080c1c1a01c43d004032401c04281103410769003660105040d80b000c01c4c61540c105a8117800038005880081102000c6501d0010389040e03113405500c0000104800c47d80901498040308030100c08016003141036641d46084c00c400fa00282c0b86200c41e070305110074007107544000030080c80080c4045559070a1440d00002039040903040b40d010800c3d00c2003044155019020302c503030301605c5030b0301c1495545095039105a40c544800c9203e0401c407003040000080c2c1110311405018020a03416080c005150942601c02e0340e0b07820002414000f409100010300c10000241c10040d254800035410460340c40c0d4010500d00c010f6644003044007820319050081191042d8401c1083d2800307982528030100031000c0a4003941e040e855401f51a82c09040100040a146803128 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 648307688 1250 648306438 648306479
    0xc010c1d0105030a0f091a0a0915020a02010605060c01050103030e0114030403030c030b03010c090e0105010c081b12120907050a0f0603090c0e0c0d0615051902010920040e03030c04 79
    0x44d40000c400040048520040048407100341190207c0280781e1002105c560180031040140002105940d8140c2007032000d12085220940105610032480d00070b401c40ba02810010f8075854481d015031107000c0c003070030007840b0603000f00340c3c861000800c6500c0381d02ca800c45006035062591560b141c56400710000c0c0755481001c01095a00c081a00e0166800c2c0038100c680300080c0d44076019941030030342c01c114143c0c0680c0130906010b07040900ba400220302c18160354281590400d40b044107075802b807070b49050009105000740d04000000302c41c0f001c40155032103280603070b20103411200a147c0351400d0090351074081c041d103e0310455544d000c10840b44a5000111805d205041c03502803e075554900e4070000320b06613561035402001182d0300c00420214881d0500806034248002d034032100000c40641a8454078042c0c03001c1c00400c0171982082c0e8000d4002d031359080c1c0d0045580d4007011114242441080d0080e001c140b16600703001c0c151120200000a4a004503101c41d622803038549450318580e07440354900181e = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 648308938 1250 648307688 648307691
    0x2109060c02060924250c0e0c0708040f140102010902061e07050703031e0c24150305030a031505091f0e0a021305012303060a0f0801020c010c1d0105030a 67
    0xa800310680d48480c16030000746050b82c00c0e926034544004c03803105d59010b406000e10b450a81c0540401042e035040f01c4108907010b0032552a000d45408404110a02c1081e00141c01a440010001100007001c0c26000031aa640c0c00300c01481074910004900f6115042d4010b50b2110080c0034000d0440030052007400e11007a00004141307000d4a556803981410444e500a4012900d100d50402100399111150900c802c2d06240c0266801109d03510068071701a08800c041d404c011641c03400410070500d41c0f05400c2c2e0100421072102c119135901d80300382d6a42c49604c21400003410007a4005c50354200e6065002512070003080e000c9142da039030409818241b400c0c0061002010707600400900507a0288500340181902c0d500507035281b02c00300359030b40c00d44035990125042001e4030f514429000d080501c0900c0381d104038628140d990300e80400103440e4008a8009007041c240d41900003400000541c0144441080c2c1e84c02070181c000701000c15a82043d81d002514140c013072211902845611540c01903500c012000360 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 648310188 1250 648308938 648308959
    0x316060b06071b03060e1f0203100503150a06120510090203011103010e0103021c0b13080f2d09090109090335010b0c03041205192109060c020609 64
    0x100e201243d041905482d0107280f034a64240103005850082c001d103004181c00420030b0384610014044810032920070140d400d030b4080003080c105250140240c1c01031000504a40b045c1b09440c4000014050944034004014588040020003142030b5013050301583c0c010015040203401d14040c10042c0000e000f080764103550710454081c00d00e21031809907001e0304d0034008100c0d480d81107205102080c07001c15802055a10840340501c0002c1c0000142540941c88548044800d50345103403a91041c040ea9101c211116030220301010141c814a024101e04040814001c881c2c812650f00d4407800d02c5075003101078020342c0706001030100ca0b220360010101548070749032001c50401c0c010711000c0740201c40d082101070503410380c02d4004084807060803a80944130306032140d45003c08140ea4182c0d244201d00c102c4140b900200d00400910805000c20403003460000396024005089142c042c65020045001602400d044981003071510b10a00c505c10540e452501c031030a40441580030414030750007220134264081e40120 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 648311438 1250 648310188 648310193
    0x31509061d010c0201020310060309030c0206030106050c190f02011b05030d1e06050108070f03061a041a04120f150912020c04110904200a0519020316060b0607 70
    0x401c101140d85007038000c010440544495030300707507408024218116801801400f00902190010a088072800d0400140c23480061034103440b41030317040a002e035000034003000001d2050f82100040480e00d402100303440f1100104a41d88c60b518003000b0000c3c06541034500c001c1d0041d4010485114440e45804c07191030304580999805207941c0c42070203260095a00c0352003a20312200f0405040150745503510041c0030701803e040c0001d1403001d00a0030358007004140c00355581c50900a80c414800740a040c5180b01d004001c06811001c280c0c0580b0580f48945420260101d81c1107071101510103071030342c0c8000300800c03911a840742e0f20b401c2c000080a94944030081c1900e18003030000d04c10040c6480c45070500b0040f00310103000203403c04440c0200c1c03501030360030a001240e201908804880c01d41000b220001001018120900ca414680d0028258039010000d44032021030b0300b12010300356955040c00b100c18070b0036502c60100d8580c09990a07405a08a10452080000c0d60580000802c9175000c1c0c80e841c00c0c0740958 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 648312688 1250 648311438 648311441
    0x9100e2401080d11031c0902011403040b041122062108030714191d0f1f030b0909100c09060c020111100c05190309030507031b0b041505071803150906 66
    0x15000c400125a48500b000c1c21941c11000f9207003c0054203032b00c0c0d03041d40f6103a01d4896141200501c010541107100e00c5444659035690108070008640034540c00b0600c1c86100c00320024401030041c1601d01c0c3d0548400001c1038000c0425402040c1e22511080c110388541c41d0558107902316054001c5960400d02603001c0d00c449820464440a00725560760040070503c1070240c1116094114043c042d000003503414449071200b10801400041072411032140c114004001ca006100070442d480d4804008002d100088800080e080150101c5020800058001880c01c1d550882c1d284513002c00314a59100d1000558055604041d040f9a80d07030503124405104282c1d07000300c0b013112b0580310100e0000300c0d00400d040c81420b0203014401007403d04014484042c4c07405404c2d80181c0000074108103214005070681c680711082100e1403a40b0869814517400e0900d012400100c500502150f92864440019a5503101d0383e08c880b0803504000e6812407042c11615450200301c80101d0610303040d038031014607200103130700d6 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 648313938 1250 648312688 648312727
    0x7050702061c1b0c08070602040807060c150504020f0907180f061808070b1305031c02010c2a0302010b1e090109150b0309100e2401080d1103 62
    0x4110700e10b50703000c4001e140182111082c040c042424100300c0381c0c0c1800507401c1201c0894850708100c0150702d0f030403030f4600340019200b6900840018018074200240700c9030007814401005202d00c0e102101c804907001c0c20b5003254030840e0081d5004540e112821741504000700c0c01078105046207054403d4a0790ba01c445003c0c00c08030340c8800458401e4910030045654000d21048420b41c1c17138503614400c14600441d0380e5840c0d105e401014088000040c07204c540c5a03110481c80020400982540c0124038044148100b689014181308055428148402c4165105c1c41c24032484e4096500ca5004000030380301c458a1444034038204074207665030745107120225900c813039000c106401404650303416403132034106201c4450380607403000024030704024000e00c1001281164100780c3d4101091030791a560b0300c4c442949042220800b071803104e850310120704010000802c80f40002491056102c10840313082c450700609250910440140f0f8124803003104440c1d1060740580f85100001003104e0030405581030440c0107030750 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 648315188 1250 648313938 648313957
    0xa0320030a120207170705100909090c051f1218050a0507031205040e06060a14031302121902060c07180f14070f03050907090f0504021e060a080705070206 68
    0x280442884103035040100d04045d080e540300360895020307001036441c0d03154031500410b48a4000c00490769000c034070881000004010110040c0002c00f0241400c42c40040d6070b0141724003a05c401d40f40c002e0041402000d0200c4078525940710044207035000030444c0201003038843c00f000b501c000030881700810b07000c220403044203018502800c0c0340c501d5072409043c40030100004806001d4103000030880071440d01c01e0b0030b034042d00a503601d517996110100c0c11994802c5607800c0c240c80341c1000c4140441300c01c1c1100495140341c405e403190350426907819280350390360341103040c0e00e50300b032801e40c14120050600f18054403e445080303085403449902c804450500d1030880b00b440d4506569500c103000074038018015013060044d11002ca503d80d050483c4010225000107080d4012b054503000032503a0310700c0404c00f10740248421001000b03c0f07201410064007030403066a09a108040030b49002c00c6a4084104e2000401c800034400703854894141001d03180310310010554424010244403910240c0c45460041c8952070 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 648316438 1250 648315188 648315203
    0x18060d0905010f0b0301050f04080a0519020109031701180f0605040608061f060507060203250e18070e0d050c060f070203011a012304080709060515090a0320030a 71
    0x101d40d03510b180c00304d4240e02a1548030742e04000a0081140003102d44075000354200f5000765a405030710800351158412110a22401088042c0d812405a03040d44040a098829a94141c1c401503070340364443d0340d80c0e0070300805a8a001440c1600385051040c4e000c1c030603c20210340045599551078002030101c0e80568060700060b0482420402016503440004156050f8a103409071002d00305400240b07a03000310000102034035030010101d00c001e440440e000303500905500e1400707010380b0214401000511040a041e0154200c018401c40c9a18262107161160100e40d03240d5010310b034094100030005072501c40c190f565000d1f030441c1c44801d0307c4842c000e20098400302812541c80c11548141030071201ca801e9904c4541003240d80080f0140e0f400343c0100394429441035040c40400c840ca1a0104611840d4807007a0248200700c000296003140303401034411590204e8110952600c080d00c03949192040c2107140d64000e81400003400011031012850303024020312100304881040300d0010034030344148501c041c0d82a0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 648317688 1250 648316438 648316451
    0x16031a1003091502190507021906110d08251b0c05100509090601031a0a1e060929090d0b1602030703020a0b0c07080a051201120818060d090501 63
    0x30541003111003c1510f914030851401d00e405034120942c0c803410640c40108140055117000359a44c00b08030308210780400c0c04041070141d44520140c540c5840d0351380f100c0705005184d2620b184a01030003c0500c90001d07101000e5101e000e10504004448012201c0814041b0f440030242c0050130020f020741c50700d4071a5120000c01d604080410000558400c070b100c0404c0400c00000c0980d84581c40b4064000100b030901180302040071003068122a01458041d0f0030044035040003807036100c940000e50300041000e095200c2107480303c0c001c490140c9503002d203a20207020310030006582d080354183c0a02206440019605003681c2c1000540740030020300e400e85606925905020b0820144500d0559044940c002581b900045a40194846154181c050099403c5c1c10000b03003840384e201c3c11141703410303880030350700780d40f81045500501700b03802c10306024151504003000407508003180d000c0440da06800c240d10904100c00710101081c1d12820142058120000f03100750a01e00d202800380c0d02944e40b00d0400400c50 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 648318938 1250 648317688 648317693
    0x20301151509090203060d02010c02031f0f0501060906020a240504080d0605061e16061b090b160b1008121e07210225140916031a100309 60
    0x150b5400c188900e030300c10000e201080d0740f040c0a004003140c6c2030a1140e003503400c9000207424140c881e5048501943c0740e903034280b0304503d43e92000c5c40c9040d204004000607622038004a40103160b0f8003c01000d81e1250b40400c0215500050802958010707906a500e0781c0b100e400c4e5041900d40c1500c040703030a40004940300c19907005c00d0141c180504805c1c5d80503030518038802418000700039620102402c540c1c0003d0048a140614010540c4968200400b4412030780c0307c400100c408818404081c000410100000c0b400040b044104d40f001921a0341c601000300540e19500009100038100f015040c0000c03c00182100d000d100d4003607940301c551801074031410341000641c10b130744030580c6410540c0e0041107407900244080c02482c0202088110036903440c000103c0c160324085140603816000d04090847d03240c0344074180303e060141d40e000d802685000c41554240084404140e403841e445150024000c01550b01c654000500412410540301c140c00303440780460601d480c00651480004d4440e10701e01d05 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 648320188 1250 648318938 648318947
    0x2134730150603010b07020109091a030609010509120c0c10050a020f2a03030f0c0102030a06050301150302120a0818010e030714010804020f04050a05150d05190203011515 75
    0x380403a0072001018030361507a100146031884140200d4502050104200741503910400608010302124881004540301c1c40e00d00161000117596264481c0c071400c400190300c0d030301c18003c05000d107001d02d00074030006800140711296900214090000703486502d80c255210b98440101c04000b122640342e460b9150070301d82000703040000e0314031900c02e00e904c9611a1481d0b036400a20054289048840101c0001143c47c0007a0451190003058000143d0218540000302c0042d4000c0d03004104d41031040091594590078907007680c48642c6a080d518128074000c00140c00d02d825906020700d03100054613844601651001420b4105402556105e10410107031016542c10041030102c20004030018200c2d03c1c0b9006004082406070810705042041c980042800c5407241d0102c10600720300100280082c0c60b0101141000f002d046038445040a10080110443c1c00c000440000030360300900581501c03088400f05408124200304101c0e019983ca0040c60714447c0060044005021014008000c03643c143d4402070 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 648321438 1250 648320188 648320191
    0x40f0c021b0306160e0d0c06030506181302011b0f02030d080c1e04122613030308090a05071211030607050a080402040e0102134730 58
    0x40d0303500300104a00c0481d540094983c1e0b002c844007141d9203001c481c051040b05d207961640c00302500080f40584074010451980030300015103c1c1c5642c20005503540d9800c1080c0c140d481c1d0722841c01810818042426507031241110300003540103041c000314a0809a81c11250b00018420940380c1040340b170a0074045103424841070340180d0561800384060b0802c0c2004000070b128042c12251f044400714081800d0031044003d95004180c80649410000082c1c00d100020708601780e804010341c80c0a6450f8000c640f0020300f903459a95040307030150300050942e13809a03421403014100071050b200d14218040003450400c044000340c0015030100d03042407002d03d0514181220005a54803a4000e4400c000e515a40003080e039580f5100d45c5840030340750301d5500100c0e0041001c07503001c80440d4000a80e110300c401001484400b00c4140e00700d0340710030000038036409034015035001c90420b03000714841d40d42480c08528400c400fa00025202964070340150b6009019102240480b24010400c81c0c2c4c02c0040e03204109000759 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 648322688 1250 648321438 648321463
    0xc02210111040e130326161107050d1b03060c1b03120519090606050111010902060307030507050421030e09070221041a19110624040f0c02 61
    0x102e04007401c140a01d211500e0081100a070368052691034000c0c5841891080311020050451604a000c02c0828624145045860007034003502d0384140292035100e010b0f20794a081528015200c400e050600300010b15a036400300340e034284412000c0c002d6031120740ca010742c000d501c00c1500044c400c07102d850207840300200321804440e0b11500c41021020a800c40b108414404003008001110b40d900604503c12840c4960050016458641c6081c1080f0040d80300006440c802d0300d50383c0d900c034008110103082c0d40000c000250030100a00109141d54020341000d80c20a42c1414030034201901c0301070f011800b602011900c0328460001d4280c6050507000032481488403802e0303070308240c0e91a04d442c029603982c80000710800a4202c02d010b402c0604580c80030394004c0e003038107003403100d8010f8507100141d025000004070013080040361415903107041c02a518455411815005082a40e03542091810411442c1d5100e81758015005403c8000c0c0d621481402c09040c3d1141c4005070001000100a18003880c18412 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 648323938 1250 648322688 648322721
    0x1d07080d0f0c0209190e070302010908070303090e06060f0a03020403020a0603061421070303030b0310020a08010603050901020f0304050312010f05060706020c07080607020a0327030809010c022101 86
    0x901d003096611400181d54160103507032488064452140c44940b120400340344150b01840c0030b00190a5020215007107044034001d03a1210440d98460086e82e450307007110b01c0020045141c6a50030401c040c00741d504554049001016070381003046151900b029944142040000203034001014001c524010420901070101403404004003410150f014144c502c0042e00702d4032a03d41d443c04166010851042900003070565000da50620341c0c0c0c2e00d00500a8111401450b11900615500c02820380461007910071403552031383e03a521541d180200541c01884040c0014049540070030801c01185151001540901c0c82a4000d40e59031110070920034461006030040204030040b18810002075940a090b20811500500d0050780d456800a00c0c0d407500308958000841406284104001c064001c10f81c0341e42140a911050650740c0700c1d020b85cec800188000e8448a856080900030300c080f0b16810041e21440708181000e0b84a800380c0e07000a410800c0c5240008074004d6001c03100300c2041c0b0300303009100703081a55064 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 648325188 1250 648323938 648323957
    0x41805030d0e0a030509040b190b0c120a0e211b011d09060f0f0405010603020c0d020309030d080406021b1b15030f10030c030605060109060e031f1d07080d 68
    0x31300421620820703400c50310560f10384400b201e687e983d120b24040000b81005480324026610942c10003980c0204041c07052a000f00203202d0f000c1840801102d00f10034041d40c0f0a034152807200c0400400b46105903c000c0031140088440c01903440c200503d440c04580794243d0001040d000000600080e0002440d140321550014520540e17140c0c1c80ca61900030313a08a503180d150246036004034901c40c956081041e4090704000001440f55010350081000c102c009060714120000c521007a03075a48200c0b50b070705801d540156130100d46988a040415000380c42404090300c0d040355061420b100d0700100c001400c1c240c1001c1200c48042910f0f0790849010030040d40d8144003040b0009584205004c02400030301c200d05520001402c1d1405440501c1c055075200000e40c00b2143c890920000402c81118030302d0114241d0720707000c02d0b000d00424011204250040052025011403105001032001d01502241034544558181ca2854481c07503440e407400c0201401426064500b0070118035010304000f48009120b0b8101 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 648326438 1250 648325188 648325193
    0x1051011070e181501050f1806010815040911030706020f03040b0c07050a090906060e01051f05040f06020c1e0306130f0f03050304020909030315040902041805030d0e0a 74
    0x40e40104445044605039003a9507101140d40c2c1148074200f015050b80a41a4100c0640c1e80003054141600c40c1a84d1010b003156848051104510003106984500b100440015046d58440c0d1901580003141007031002c0c0700000f0380e010800351400704504807002a44800b124025040402005000b84079510007030400c00d038111503c58503841a170040380d070240f03000140203a140300b04000880003400041c0c4282c2d0800d5880310180d00a24003140201c9140d07050210000d000403880d511b035810780e00020103400c14a40c84000b011300780070501c02031405000e014000052040b00100c0080d000b040d954024004480000c03003005402104c9035440ca01e9100050500c080d65140042e1583e404811703d41044a1851a42012004080c04003402040a03800003402c20406911601a5004510030f0b200d09089480b1880349507100d0004a03081018209524443e4009140a0704000b1034280060400140003201c1c1000c6c141c094030204059400b17074400a40300c3c50b41c101c0740c40741e0301c40c0f071240c540138141d05540c69 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 648327688 1250 648326438 648326443
    0x50c04050906030309030a030914030d0f030c12060603140c07030f0813170c010b1e01140702100c050d02070b120a1b020d0207050d210507060c050301051011 69
    0xd00803039010392020400106591000c100b140c240101c024105c5091840358900200000c000d8040d841a03031800012076040d6043c0003d0310ba0480c034403500c0e101a59500d000c0308400a0160403800c000300a10154443c10f80c400502c00c900141c122075170302250040480102907000342000d488038a10030b408000b600c0105ea44a1020ba60f004080d2408503174540383d2a02040d01100342080140940c40c0504603460540a0740c801026083e08050080c001e0307194060400074201105600340c0c40f41c0d00c0c01060788407150300c608030030302d0402c00e840c02803130403e541a0045110a0440c14602c004207404012070400d102082000068980c1c262000b001400d0030f024000c0480d0042c0d03200e150580507a14041100c200d800d8108842c502c000042450411210b2080255200880304202c0d015000d41c000128440c03e2240c000c103981ca410a8140604150b036611002501070b01006110400806010b107800083e43ca014425862149a03141c5480f0750402040010054440d14840140300c01604809441c5901 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 648328938 1250 648327688 648327697
    0x1401030206190507050624180a0f0e030f0a030b060a0905100c02121e03090328080d0e0c0a1d040311070e18010905030d11070206042403050c 62
    0x2107041e186031140d0b05005448900400070f006001d405104104055003030a281d94030000000d59000040c5490b6000501c410ba80e85403294082c0100d40100003140070089400107108028022030004c0d0700c242100c89241103802000b0340800c858000240d00b40d14503494040c00300f030305908070303145842d1071058100038003806202c1c41039a026039020791072420228043c1c00e450054507000380c0785010350490340d02c09039114524203101d0458400e02d0f038407083c2d07200400826299682d101030f004042c3c50a0424040e42e0808090070b50341e841e503001c0f80d91080040e1f036200c05044107644117600880c4004250489908180140000900981d060b03807080002068500421138002000004010140c035a403c04541415040000e19200d00c125400000d0040b40c140c1454480c0c40c03500440d00304203203411541800e0f1100303c00007034803e40c02800705900c1c6143d2580302d080300c2004450200e20341000e5501103110781c0c0140c1c2c0140c40282c2d80000442c02030510181c01e855810844c681040300d03241940606045004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 648330188 1250 648328938 648328957
    0x1b130807080615280e07080405100c090303111002040f1d060a0506090411180901080a0b0c13270507020601061b060608030d1d0307020907050c0a02040e0d031401030206 74
    0x1383d0a0514402c024142440009000101c40c0900715250071840581841400c1d0342c1200c0714420b14940788038007491407003a8481d620301365a5510329289580c0307048071480b01c171061109460152078059901c9000c0c51000b0001040310f020a850120300c1c05608100041501281004002c0700d80e003085803541d03d481182c420345404450141c3c907140f02c0c4022800801e144041110090f43c000381c0309102c42440100321b06411401c4031801a81da80318180a0344a01c51010020711044d01e007400f00c3d2040040f0805031407582004e03e0b40d40b0000d83e8650110407112100d8030030003500c0603012a840c6c20507400340206640f00390343d400208069403502500800685402c11b06d40058411190040c0800000f0b030001e10040498804803900c8a2036080500014000c40003c090211440189018200000f2041e0750783c0700c2e00145081d00302e5684d008181c0f8668042c1c6507404850160f40310001c01a40c07a840b0300078010301c21000920740300c0e04440d009401c99075031201d2240d042014a00400040c0d0710310080702c02000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 648331438 1250 648330188 648330229
    0x20a0b07260702030703060f0b0d1208040302101107031119080901030b06070602040512060705090d0303061d0a05010603090f11010c0b040503030901050f0f1b130807080615 76
    0x240c40d40581180d41c002c10000940c54001c1c101c0000501c440c40d00300340d00800c401602004404040d404022984500707070001009400d4040c000e0907503500618003a640305010740103a0b05d10b80000e02e80741c8115240c1503500c4241060101b400300a1603230003594505940c6428000b4011440b8001840740580c800d82c600411401000503400380c0e99200341c000032000040a07200030349542c0c00d1710b0000080e4009001d04c41c0604031225941c410f000c40029494010005a12102e2070607000b68140b12840c03051480a40905860b800005650751404000402c82182d04442d46040e090122200094600691142e0201424890340501040400041c0901c5513800700040700c00c0615100141c2e080895540e01600d2404030f0020803090210200043d442680f014000f003000b95160b40b1a200c102000351140c012082c41c01c00010488189080b0005144640c00726180c20800b2a40c510f141d0b214250308405180c0d001034408011948042201640210b8001d03c0c006200818101141d1055801c4071610f0000 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 648332688 1250 648331438 648331493
    0x31b050c09090f07231c030c020f0d050d0905040b0a0b070501151203111204050409060e010c0306060908061b0f09060703030b0907090e0112050c100903020a0b07 71
    0xd060811102c5559401d00c4103581c2a155103c0400a080c940700d170b220202c81302c81644500303081c681001030b5900840c1c1180d11620a49498408440754148118201c1c0c0140c0c0007450200300343d03544452402c50034400c8001740070150645000034584c042903440319024605104100303040384c0d00e14001c0d0007179403421040310317403550441c1c02d02c1405000c8111107107400c507609072000701e000001400f8062100c2e000b81c42d00802d000c0a20100d555a00f2507016100c90000b00b400240020b1805410a00718a80074100c04034420f59513424040c01c40d8008140000800c0c3e030350314100009034208050000500710350016100741c0c90704001c806002000000c50200021300015070490320302214056a075808000380c4103136152252032901500410008011510803c160400140b0070f6200e00c0003002561462100c80746282d1801c142140c00180b41c400480b25400390040c60351003030325030030610311441358250f40d01005c0038618014050b02a0480d001419480402c002d00c4001c148052194440300403a2040c0c030210 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 648333938 1250 648332688 648332701
    0x403080a110d050423030a0e1005270a05010201090b04060c09030b01180513020102120c0a06050408040509070c120e0a0503060f1006022e0b090112031b050c09 70
    0x60b07220b2003420072941480c003400d00061100e010300140f0420050382c0214020245190300942e05d008071381e0030b00005600040410310a08041d500031104440c80d0400e14148544107010550300500892440310394603410520f103941c0d01d00a182803008207020b0000300072620742034588245420340104003400702c0d80c642e21020303202c034400c800c0840216007203058402a56158480075410031702c2544011540b6080c20049400d006203290701c40c44160b8140c0040803858006078102040c0e400503923800b1001c0c060705c0c1e60072001c140d0502840780b0a6200f021000d65a50070320081041c1080081c12200070018032480940c000b07440d2810500d40048103041500b9601c214100240030039039550441a0940605d209000115034002d07101805000443d403d41c044684800040b6079038442049880400c023900804a038440d0401c091643c0010300d56074010480c100618003041043c04280e00001e40840f01050480a041c1d1086002c04482e1105401701610516522b0781581e55542110047c0310b0b07607094010402 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 648335188 1250 648333938 648333971
    0xf06080a0b0c070f0b070e1507120519030905070621020903120a020d0327061d071d0604020403020a090f09052401050a0f0e090304030512070204140403080a 69
    0x5482d81c005003013402c40803140341240401c0c0742a0340a0300440c450b54600c10f61780c5819000010f06281c529120360810f9415242c141c11050b607824030340c0c1440340412800015607918001300b002c040158a000ca0308002e1403804914040300c030340c4180100044071040c11018484c0d1a10f01c170b0951010308015071226068000207040c111801001e04030301e407001a142880a401141c0c0c2e001c0740d01980c4040140c0e081501c0441e2000c990007914502211901503000002031403030b4420701c1061000402e0309075002e06017210a29003619500310103005850000420b100d0095607201e140c0c81070080d40e080d0b0a091540e070124181c900c983c041e803110b1507216640700d840c01009501103429140c01a00300c40c81800c050754402804807003569032540a45405002050504080b05c200341110b00300d07480c1030511803030302c1030a00310b0810181032501c10703004c00c01c8008045181000a05a0007842d607400b00c4d9501e000b481000205e60700140345000d00340404003080082034122580d01e50003c919600400d40b0a04c0184540 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 648336438 1250 648335188 648335197
    0x1507020a330b0f01020106050303390303010f060302040b0702040b220605010e010314130c27050a23130f0605040b060306010f030210090b0a030b03010f06080a0b0c 72
    0x1a0301215007074030380124034068000c119003650544107610f14482d100012406c2e1040c40c0101e9425920070015000f041e00344e03014102a00c201d408400c604c0c42102d4174502a849d034024a55010755001100506c0b0341e000c91424000209000d090031894140390411803202806680c6c0c02038030a655034480d4407499220102c081000c135020305481c40d400014408007100500581c05841d002406803d01c0078140d50180c400c0d0036080f079800d0701000c01707562401c41c07654520b4a000000c49a00506c1400001c100c4c0d8841007991160842c0c91740300e40080003090580301103a00c010a004012030a003410003a03440f1031110042050000c8070007041c01503841c1d5803200720703003103050748010310811050382100113000301030740298003d81c4180208006510b030f8204059a941e001c0c0206078085015440400051800100c040040440ca040207001c181c3e43e034200140036009011100c0201c0d480d0f2111041c070303140c01c4c8140b004000252108010103801c003000d07c0c0c0c0e621f00c0510018901888800404c180c1e502001c10b50f13 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 648337688 1250 648336438 648336503
    0x30f03180e04050d110c13020f1902030403120f0807030f150b032a0f0705101817030c0d24030309061d1804150507020c031507020a 58
    0x80c101d41000d00d04181d850101024810015800c8060b9440e110b801080c041d0b92030000410403038001c102200044000d600c1650170b002514400c11001252001040c0140894125074018640f41c5145050400c3d030100100c92001c00c00c80c2015501800039008607000341c00c040700e8940000c81414842c04100201100c490880081100040001e0103001240c001d502c54856000b071000c0e032002405915450750301c0c0748003902d2080c0301030080007410840070b00502034043c011b104803182440702d00703001022189031074070701185410408030b15814040a0680310f1690b0404841c16451454a841413a101d4000d40b00383d040d01545500200d90320800265450403008040c1e42c025032300c2d960f64980035048101501c110404140c1820401c0308049242c5540b003074413000a00250711070300c01c031100c06660100080c011640b4071400190201032500c1441024403400300c0d90010442d00d20040101031500c0e4448904200c0034801c507017084071559000c91001304440c2e00140c0d490f80303580306066008401c0c00b0000356 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 648338938 1250 648337688 648337709
    0x10c0b01120516051005130509040f0b06090601091412030a1107290a12110a27030f080c060a0b040f0c0c03050c030c010212040308060a030f0318 64
    0xc41e03038260000c000d801031881030044440c0c0080500145454040a02c44c003980820b01c584285540741c0110020f2182d8110759140b807a030300b92030340c1c00034618040c00d480c00d41e070000f82c01c040c804c20810620700c40385e0800e5084038406e03034514114000818002840c050f242c040c400c0f51448103810307240c40280d81200c0c0b44101c1925102c1d01e0310781c3c0047c01c41c00000003041403480398080014030544c0001240180506c20607081d211210501d2000003198060302c212403c1002004800b031a201c200d00c622802856120030003580d4200d01d150062210725000c030005031000511320000041c88140c1d03a80402c2320b074801e10200401a00342000201c0c0d0258103034191284c0603140c02c10003201480c5e40070039441c41045804004144815413408219805d910b9408085001725440001182c0200c01800040d0800000c50340f800c51007080160030391f002007280ca05150b6400c8180010150884026540080c0a803030700140c40d481c54641c40540700380444082e080c460040308000c0803e0100b00f405002e8a0002c54 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 648340188 1250 648338938 648338941
    0x180501020307090b12040803100801020a0f0e010905090a0903021e060f0c12131103010f02030f150a090b0307031a0403020d211508010903080f09070b0d0209010c0b 72
    0x1011800307944215101c40000d0800d140c042440100401900c042e1400c030780d104842d0356600d80e10000a07500140c0011507040d684030001403185006d0004102d0700c0000da6407070b08000e0300e107640a811281c2101c04241400718101c405d0140e603d0300c440750399009001400201f480300c59810264100400040740b1172070658004d4070042d10b940c00043d079a000f11f000400c0703c10300381d132071440a0205016414041d40300031100004501d072400c40c1840740107214010328542d01b5030390340c60f40020708590005985484064010080090320240c4090702d5074030004d042c421407008400c0c0303400141030f032545004070f000c03065030303402101c20070344007007000c0c1010316440155034031034421182031030b85100811a022801440ba010036120750a11801440349100306d20000e001c610b40c0402a210054000310300480081c048400002440700024042e41ca8003d0080d00c600b0214205141e00c4007404000900040700c50340844410004242818222201d42900700f40058864000c400101d552245206000c0d1400703c5940 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 648341438 1250 648340188 648340193
    0x606090604120512070309140102070f150206131205070c0306050103031106070201141902071203020a020f0606030613050109050109062f070f0503160813090b1f0318 73
    0x1030b8000041d005104541c0e40101a02101d80140328210004000036060241003046881a0184940080b414019541302586424289416180c1c03035009034090341c51101402c0550360180700c800d8102003001e4001c0091f5529459450080c1010f8030b441c01040380010360101071092000c1050069903000500340b0403540d40381001080c50203d1002c0c48110b000c1d000108111600511601050055070a0302c45400c0d6034540e03900d1502049030904c5041d9580801c660000107402e50745e0980303280c68580f4010780328100202e0080c41c0140e074205000442d4401020702040380d0b400500207500c00103002101c001100c640c0b901c103014104a2000800725130a040d00003040148a030400456031400031586c050303101078491704400054820000c00d40c00d0100700b0103140860760001e0142c3c1c4581c02001181e140100c2c690550422024050b000c2e1f40110000c96074031803011040d02c45600610002006010710f400c2d1000051001e40a000074241c20022500b0704401c0e54025003104140310500341141ca040c85160 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 648342688 1250 648341438 648341459
    0x20a05040302040f02090d0809011103070c14060a02030d02030c09120d0e0d030903110a031b08011b021911060f030f060a0e07030c0314090f07091109090606090604 72
    0x340802c07485a4281000c15003038144070b200f60781c1500320042800b080c00c220303620340d00029400340c9451410060b01456404d0340400410091154034030800140f0b500710f1520040e451f84141c002d11162007001b0400007151940d82c000103550003042000d80040c2c3e01d4980c22204c55040c400d031081150804400b00c82201002c00104080700070700400d07240c800d0421016020003402d068840d200502060980800344041340484100f041031f450040d1500700e0ba5600c944910703500b05440d0645070040c0301c1c0a180cd2100080c00c2c0100300050500a064614552450ba8003039203130b40056856803204a102132815080c80702c81c00e003c90b0840400741149a170340500c40000d00b40c0ea801151042c1c0c4641c510f0003c1381941c05e00d500303036804842c11024a840c00c1d403503801c0c08401070710020841c4801c060b15030000e00c044e05070030704e0007a01410340d880081c0000c10100345100d041801550202030b0f01e07458100b000c085c0b21240c1003155510442103408401541d21032001414502411052581240d0040740109554650 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 648343938 1250 648342688 648342697
    0x90510020c130e030a05031b03160e03030304030c0b070309081803010e1204180b04020414030c0a05030606040e01110712080c09060403081b010e03034f06020a05 71
    0x780e400400b544001000d070740030b907032004800704801c2c0e000300007110b80107100d44003842c3c1208a102da00c0c41148401c00565081d6041030701d900c180d0103240e0f030302d072001190032850b00315a00100783c01039400c41ca002e440140080c0e00d00c07200502070001c01c0c00002c0c030b8288250701c940c41d11580720114a8540039401030000f020760036140d1082c081e42c60000d040a08150001e6038441e00310403548001d241c1400c1901c0881d0f100c012070f00043c0030030740f10039100e4510358403800900090500840c01058000c80081014502805034090900450100c0d00a0110351804208294000004d90703001c00c0082040f2401030041c04200041c000322207010900c50204101c954101071102c45e40c1c2d5403004142c4030414904200d105010b500e5910003410001000012445405044107841c000402e6050f0480203401e40d01352031000240c104550000010040b560070a4401c007402c548100c0c9144a180115510b500a2450b660003c06040100c0d900c4554902e1040b800008120354071000941d05e4803102c01024116410 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 648345188 1250 648343938 648343963
    0x6040f05101701020f090f1f0e01141206011b02042f0a080406090624030b01120b04060b030a1a010f3c0b070c09180206071209051002 59
    0x28241d400020702c14020707580b40351501c0c0d40c1c00e0320700641d0100304800403d81d04200394000301410011030104d0082114000001d106445160400c0f0403003000403c001c3c0da00b03d01000c420810700811400010001a80307a02c03017002e00b41030142402c0c0300080d002c481c585000007540142000e1800820130b030486c0141d8400741d9021021041942c8100103030b500760003014201d000045940c5c0014000c14500e1300607240c858080c10000032000c5044000c1a80424a00c8082240128080c010070812441d04002c5004000340c0300038a980590030303a209100d4250240c8003910342c645403241130070141e0702842040c8040340d014180342c207104500e41440403c61b509100c1c4503655405082e0020344203226480f44284a600e04008844411117000394420328060900b00420344a203104000c58091030700030052036020300418500c0300381c91400d02c107035094820400c041d40c0e0b2405010947c40041e200ea4080c0c1e001e8130b500485440303060600c40170444441c05194003481c0c0c07003449501000719413030f00071541170305228 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 648346438 1250 648345188 648345209
    0x19060b040f0606020c1003020c0d0c1505130f0804170303180106050f0603060f030a1a01092a0e060408010605040605030109110607030e1306060206090610090b010e03010e1501140d0201030506040f0510 88
    0xd00c81c2d4102310dc0048030f4020900c0003c04150b0000b4204549240b80300e8400c440881c01d01e5180d800b4248982c201d01c2420b021540300205100c04007103103981142050800600910208d400d1102185840021035480d0b4081e44012001c1883c0341d4400c11030100105003e02182c4482c140ca0911100c100180740400d0445c0c3c010000119404445000703081840f89151011900300d10b18016407441110507a0202080024500c900101641c0d01c0006000511000c000803d4003420142040105c80441d03219510070b80c9031884d2100000c12106071601c1c0b42100700d40702c42d00c50a6904041e105102c0d0902d14541c440c400b070140e04100e14107648250295040307542101d02541d03609100c9541c0b90816100f003070980070071420412035031489030040c1e00105810b141122800c50076101090a442224540c0460b540252003121080c1088416080c010f240b940c4030049600310800104554a0b04628040c0c101030721600001c0242d141c540000020381c4203102c080004d0315190312401c0002c1c2003406441c0e2201d = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 648347688 1250 648346438 648346463
    0xc0d0501051f0e06060a03140702030d0f06231207061d06090d06020310030503030c04090b030d09180204030f12030c050c06060d030219060b040f0606020c1003020c0d0c 74
    0x119000c4081d6010f452903d03046141030b40320358080112642010040c402050340710105aa541c41e4201c001501481c0190010760310f60389070008040580d010080256000b0b841c202c020401045107d1004ca85407003a0384814492a0624004c43c2400740c0300c1c031540620b1321903c00c0000e1282d81c40a00407203800300d04c1940b101589803e9080220901c0342014040d803004400888002103030169008607040060100502c0085a0f00c0d5078541c15900100daa000d041000132808218030031613070088451180d8200d0180c01002c483c840d025104034034a0107503405c01e84808031000a580e90640c1124040d40d006804103843c0041c81c41c00c4581c5000000c000c0d0300181c1007080780d06030700b4020307000c1d14104882a0b0146c40c40340d0b01e18081c000900e4007a0025021803042c1c038580a840d040ca80d104003c164040d010101b44d02d04100c092100b80c0d03031240d01044c255807401c1e60401003540e011031003800c0c1030401c030782200d284031001070224040e0140b0040d250f04ca00811f051503c500381c001c030981c15150300c02e030702050b0390 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 648348938 1250 648347688 648347731
    0x8150403181203030506120f011409061902030910290603010f0509090307060903120c020d050703230d0c02101404020603090102131502060603060114010c03020c0d050105 75
    0x2203041e1880b03400c0b07404030008101c00029000303800c0b042c0e125102800808561100d103200c24a02030b0202c03490003480c8d551380e1041003e13104c0c42205a5001802c880100300d0750400c4031015200005d43c089007041d203503000c0003080c543c800c14001040100d846203424000040600e0b010039400002c0c600e426010340e071209034005e8908104060301d0490761010204098070303140909011b0002c000608104960000308280070000d5031511aa8030481d001b50f03604400c00954404100484210b001500259848400c4540c88194442c003120f00566061034881c0480c20240f2140710070302c1c030740004405d244002150020403012598841400204594221090521030329600c50844182601070665014031130000340c00350400800554000910300001440c106540c640250504a40d4101c0c01d41c0141d076804006000d42d0401509400c072100720003401c81549841405d50030800f640380028140840003d500050500034400d10000c420041d100020106080c5001c0d402003a007191503540705886c482d04080c2 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 648350188 1250 648348938 648348977
    0x40509070f0f0e0a0f0608091005090303220506071d0f0d02010f02070e1003060b06030709061d031c0801060f050a03050606070f060b03010c050a090e0406020408150403 74
    0x104607103142c4402c200030070038280881c2c3c5001d032000e0154100e01c0b00480082c1401ca45d045100003406655104a501c1c1012100b050a00c003035403030a0a01a403d1800307000c003e100100803030340c11032031616008100701c034100e01820b80094002e001a10324003030361007004482ca81140b980f2030034160190280221542440030403880c40701442d41680c000400521550055000d40444008092030740100c1c0c056540e81d40040300c0d14401114041c40460074000104204a881d0041303a0300300c5021103c8500303510b00340f50020009a0144201810072507074800c6900841c00c41e1000040c8050080c2c26038000c40318a0099142884031080701e0000680c11500014203a0721519a075400a0003558038140780481c0310100f01c02800d0054511b9510990410101c4002600c0b81c114096080c480c0c00003103800c184031401c040c01c4885c0c1c4c0e41e400043c8182084505030071580700031003e0503500743c80c0620340a5100d50a1020007400303030790000a3b1500c00e1580c0703d5505044080300700c1c4070b00e11998402421040c221384201 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 648351438 1250 648350188 648350207
    0x21611010f0537110d0503070c0b06010509030d0206090d020708120310090c0309151a1c05030a11120a0806041805070f06030e030906090d2604050907 66
    0x91042c4035406141120b503084100052000f240da000035182e180d4500060141c1012031000b0514208104000040c140401810000c031800d00c0e90561514400c05401414100b00003081c207510000040c81c181c2c040d00540e0344280c40541191205041c1d0304029545000503141a83d0520a400000c10654400a0b058060b24200d0014013400c0e2010480c1c0e04003908090103a10fa55040a00c0118848103a40329007800190181d5000c5546403450602092880c0c8154809801310300b0501e000b6041000c14030409140c41060303036441d605a1040c048175014100c4460014194000060400c0311107030b000d40307102505580c8a080d01c80c02c0a0489154245125443c0c526003c112104009009450941c3c014818000d022510440740807a6030f42d96810700080f034201d281542e44a11050150947c14803809442c191360a00851411854000181c424021a8449881580311455800400c80a170354201e035002801641520a9801c0558100d51030304039002e294001e0782510002148a880781080c103 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 648352688 1250 648351438 648351467
    0x31d07050607020d1103120d0506030d0e0f030111120403120515012a03110d050408100902180f060418120e060f04080703170403032f0102161101 64
    0x1e5150555950902080b00341c002400d03600c4401e400e0020b151034506120100c4925503880c0d1040c0c0c0c40c2c1d00c4001e070108403400540070a00030760000260300720858100b16142c0c10343c1800c41d4245000c130700440002c1c1c050f060107201d200c182c000206000d814800009225406184207480304000c40500040601c100d41c802c0b141c801d0010300304000d0403602d501a85c0042000401a21540d00171004178070b8500b10321102e20703403c40c0028503207a05241050024000044044c2440c54560718041c900410b5954819202c607150610b1551000748100b1580c901c0082c600d540d49c0002c40050301d103400b01454043c0d034012501540240e041c07a2001840ca01e582c41010002da1b44a4001a0302861456003242d0704001d00f0151074000c007081003080c40c80d42450740504010000e0000401c981c5043d0328241100d6034a0103550304c90319030280030a2001079042003060cc1c61401d00c11080c0401289800c4099641c800e2600c0c0000d107501c00104030000d4072400510a000b140510181c4c0340602c00303500111030103035100200 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 648353938 1250 648352688 648352699
    0x2030105070234030b040b100f08030415051c020703020c060715090821160302071502030910060b09010e030c031506030a230d05090901090207030309060507031d0705 73
    0x2d00403040105981d0204000003118040d10507a01c1750340d41d012035541a01c0549983c0d129500b00306501100300300d282c01403c82c4d540d200f601e02d03250201490b541d00540c090a20890a03c1502d402024421026656240c0716046800120f22115078550000d500020064006000d20311511701c1a003007650460740400e51009038192035000d0140351000802060100700c4201c0010130041d00c80d0030700326200e090703c48145400c494240c20903036a4030000714000f402c00818140144443d4010440412401e41006002840560703681e950b2803a5a080402d02181c9400310b9180900204000c400c60000c1c0c402c030a030a0720758540182c001d40c105a40c6405205074513500d548803031040100440100113060300a0300c040c048994a141c15a01d107125415010b0320004166841c00380031180080800c01652122250709195107088100b80202c3e0a03418140901102d003500000c03420300b05442544040740e4903811040403c05804c2a56000380a41001c0103440f010070b080314640c0b0b01249011990034200c2d64010308 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 648355188 1250 648353938 648353983
    0x160b060307271e06060215040201020a0b0705070204020f03062e051e0f030f0a20070f050d05090307060203042102060c1c120902010f120b1903020301050702 69
    0x41800c0108082e803040b507280b9100c4840300c403607444030400101c206034120004a0442e05003d00203241119403660030030b40510560a1101607600883d2001c0c8403500200c424609a032041c0054034030b40f1a0182c000d4202d4800a090701d100000200071314011841140e24100c441c3d00703521101c00d05002c1c42c072008601c20403035440c442c01a0140c001407042c56500700c140310502c020110900340310303006441c2101140100204110145040c007000c00d07407003501041d0401591030790107140918814841c000481c940000240f000a1010324080c104201351f10100326280c00c3c110100c0107080e6008020300502074451080c002c60210b0010085c0c03426038001a07420180464040c0000c1c4102c0c00c58807007640c209108015110001206000809a4640c035142e2120dc041d18940000c00503842d8411458403c1d03c2c0c40c10501c0180e034010320440354180a40f52505980d1032013041c0740003c00e071102d00d15a106e0251b502450708032410039850400c50303000f10020052596170b40d2090340c4490807000c0861140a2052 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 648356438 1250 648355188 648355229
    0x90c060c0c15140f0301031a04121202090d06090b071112090d020306010803070b01120b040312021306020601030b07090803030c0f0d0501090506040f0b131808160b060307 75
    0x120b40541c182c04920b0404219900b0b01c0402d4103c0e485142c1c0382d040013030000010310601400100c80000406c81c005005294505611002c8224845010380002c0040100240903140c100c0d4054602c0d240d4014060101c0c1d40103850414000d2070121801c681c0b1400c003a00240c40d207401080c2c81e91401e103083c1c0140c56032210030f4041816913400081f01c142d0001400e45148050788080207860301070000000195528266801c1c001741c540340c164400d81d035030344004006400254011150540040c0c3c141010b61485194070406006401000000c886907100410006103490f80010564100c82c0141000384031911801000c42d07002502c5c0c01400400d80c002c101041110070848000c1c80f1030200821100c0c01c20895901801c1030f81c000780c0c4181c2403552100c050104c04d00d0544a585401241020204a940f40e9000403da0000c11700c0000e1800c90b59a102c0d1403000c40c401c420010040e6808544556604001c881182141d10007840030703114a503000c1c000840300d080010b1040b05490030481079401c40014403 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 648357688 1250 648356438 648356459
    0x70b0316031d03040e340339080a060501082d010e0711011e0e031926061807030f090809130203010509010b130315090c060c0c 56
    0x103655103a91200c060b810700e54100b010310181c4007034450240c000c07409051044c910320240e2000c00b1080d0189003050030510040d2881810140300070b10b141008a01829001d0400c84400c41140100c0356038498407a00c0d60800e1420700307007684c4411894403034000c180c541c0c2c151002180c445d80a56404580c80d040892591301006169035682215040c003180200b0309152445020002a880341d200b0a20040901480710340101690380d12148800081061180c840c40403071050104684c0314645590321030b183c91640001f0300032180740d009a1042c83d90104080c0800505000322500c02a01061071034206000c0a1501800d007405594020a50082d44010510781a40000e000d09501c050550b5000d40d40c1d100b400fa4044e81e40c4a84c005c01045444800303c00074001d62003400c90340c1e0710a40c0e1040005218aa075160174a50550313002e214819117456a10400300f410303103c00d0f000074107500c2c0e060070307510010503d681001525501c41e0003040e56260f40da400c01d80380254412002030481d4440b070710a00040d00803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 648358938 1250 648357688 648357701
    0xd08100b03130f050c0f041b030c03061706040308010e16050f160f06110901050d0209031204030b0613020702101107121407170316020d02150705070b031603 69
    0x90080e10100014990751200d031000008412501038200104040035480c281745032030282c4a050f5400d015523240380107000f050200d604941c105041d510801c0240461080e409134014104c03941d80720f00340001d103808040c0e07586000c45044002558900c00490620940d014041c040c41d0104c64110507001212426111034110388030001c4118428402010440ba800e00b60030300c3c4a00544011560540604120f402e4440040f0400b0780c80c40204001001644d2080403190411064440161110460030010707082041c131048030301c1043c102060200a00914071403450080303108036895110080b00d20382d0282603000703002d0003951002001e144100360b103003d001c8481103160b1300d4040c0c4800d81e485216860f00d0030912001507954030442203070008518001c01c500390107004420342068010080405090341da1041d0041d084200c40c59102483c00c540311005040c095507801490504490070f1210b0b840002d42142e0811748951258610000b254007240003200e01541c201c1e00d085108000142c02600500034 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 648360188 1250 648358938 648358951
    0x4080307030902090f040b091908070c03051e070503010c0e0609042706060f1a0d0f05010b221a0a090b1305030d08070503310803090d08100b03 63
    0x115440b5120040c1e0358041c0c2d1521a41c003110004016086c0303402c3c21841040e0040402d6015440000c00708440b80405185140303203a8051006941c95542d07140000300140d069100421030b00c031300000080600c24001c041100e03841d070308046544843d40c4101705820303140b0640718840826110040c03807055080c660b0090446a101800209208510361100d882100d800050040c9070802000d0b14001c004c5c650081500500800028500250a01c48104c1064000a490f052800350014641c00c0d01010742d01b110000248842040106d1340e5690300210803903108480003581041400c5985121070350421401c0c06403011210110300e0b071a810b00c1c040416a00c900e524006210b016140000c0000c00e500013050b4004510740794983d030303a24220601d0310b4820100c5d00b4030284100202003140d034136030000076a5404250700041ca00075541100e00e080281c3d8200b032400460981001c0c020080c0521030008601030501d6804841c42030580500845d00d040e01074480c1c1c846011034840401141c500500035503007000 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 648361438 1250 648360188 648360191
    0x20103020c070801020d1109060d240807050901080f0c0f012c15071e1113060f320406121113050412030509031b070905100b030408030703 61
    0xc1054103102c0c038003020703a4460411a900080c007500c03100d119004203011550001c01150420724110300107541703805558440200b0942d210f600c50441c00d04403403080300c410920f40c0c540902c01c0c0c6510841361140418020940a201341200004030070100040c99094222141c0240184278100741c10406400c232110a00e50401031203012041c000c0c0740010100041900e21059856000d2b503000502440c0c0174890050b03403408800f48090008249015100509658446607508104045103800f80403031550302c2045030024040c03021116001120303807000060710f051910b584151613480050340100302c04c0309810b2140c4505400030003090540043ca0384d001e41e80042c40032500507200c909407100740c0541101981c44401d134203a0030002e401c0c10003004541d0301d0f07140c000340140d2074642c60740c40c0d01c1c84588480c1c0c03040641d02c0c1e001070a52007060055802a030348940001240702514104140e4601d010f00400b400b4038584800300c2c100d8445c0f0000c550886c0c84030001c4504542d1580c0751b0003c0390f0001804003040c50b = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 648362688 1250 648361438 648361447
    0xd17040b03041704140d24200403020315091507050714010c0507080309010204092d050103110909012405091003020108010b0c03041503060e0a060b04050d060b060a0206041509080d0902010302 84
    0x101e590884e4a90004204000100c81203108101111002e0140023078050080c100401d0000d45c902040750701e940410080007015070303240c503046030349090040b00211403d10214003d00080a60103001003050300e000d213034590b1032580c0039000c007800c84062a00360004181c0401689000031011009190b00c00850400182099514017030241964491840c0c001184000d145201d04070381060340605400c884440100480d40c10b55076816440c005103c12a40b0a901100000c2c201000035081200340c0e051002a180c107100c400d411040142c50ba034010a4440d1828000003110704820801c3e201c102da405179a0100240d18180b040b800d9a8000c1c243d05045000402010901c120349507020810500b51359800107000b45001c00320f8030000e0010386a05a00317402c0480c20044020076205a50540d02d00301c0341d20444844c50f24195000307040c4481495003001c0b0128031003440613004100a407045000c1d1055412010300500d09000b141c3e03500100501440b414006d100943d5220390000203568070604005252 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 648363938 1250 648362688 648362723
    0x702030105070906020d030c1b051c110709050c070f0515011d0903030403020c0603151306080609060702060a110c1e0705030c0d020d17040b03041704140d 68
    0x7520411110340c0041400e0220400c143c590410814050003030f60b00e4100702c900c0d1b08550013003c0e840341da141e4240c400120018541400014401140d940c00300070341940380e42c8501d00002c1c10782c11322058249061300440d80d002940041c0e0f0300800c0e105881c00ca40282c80d15982d5902c1c40c0701000750100c00e5070a842688260103944410300c0c20309001c0c0c0001003a5143c000098411200d0201c0d00410b12050b40d00144180000240c0001e481d141ca148111100c0d500c0e5550036143c0e0120b00040c0364002d5015030b0f01540c02114a5240c2c0c0010181c03504c240a513072071641c800081590720101980c030035005a2082d0009446004a94021015202d04180c010301e00b600c0c21220710700d000840a5441c3c094451008204842070040001c00c005000c107070081d16080480c007000407010030a80c0c4c406401750f403900c2850303010800480d040c1d00034404c815405907203072512a004500036800840e406c903110321142100103000b4040030241c0d000c5690800012028103801c00c1880380e56540d004084510107403c21032042c0703 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 648365188 1250 648363938 648363941
    0xf090f0604081c141308090a0b070510020f0f0a03113106051c0e0703080a080c03060a05130f0f1401091b0f020312070504030201110615041107020301 66
    0x518000d50803140c4a0101d243c0c0f9100110400c2c503440852460a050460208480c0b515154055600c0b0750080d61070b105030810390524400c20400305da1004d0b00c480080b4071820014050500a405142240d0080782c109a81904a22912014103203151042c012661031508940c0108007601c0540b4010455104070386034100c01d1740041803541398455071a003076a01c1c00c002c1166400c406001001c1600052840c1c00b4006d02507101c4c170000d8005014404d1120b0b5541600c80c0c001d83d060310074100131580059a641030080203500103c0004000410ba00301103003529405005580c096440200101c0c4090b01d00020030a070603603890700702c644440d1284070aa42c3c008141c41204a020b102060100c1d5041902e035114204090580182c1001440d0400000f010014820019000c5040b230905041810b4221010307131950088080f114851000d1108000c215540b02c0e010b0f00880e4170030303255605840344000550b615400211490b00c002d15000f100300f4600d1500e81c00021075040d08110300d510300141c0e074021a0 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 648366438 1250 648365188 648365191
    0x3f020c1603060f050103031d03160602011e09110405130b0c04080106060302070c090b0a030b010303020d0806030a120f1404090501081e0c0f060c031c1d060f090f06 72
    0x20845040100107109150281c081c0342c5002010811085d03045950181074039807004035805502c4220b50000d41c03161800c02c201d901300e40340040305140b0306940781c0000b4007a04204424414040070003107800c68041c014042c000d13074180d010550700c0072a0744403800d02004000007025002d800740343d5802000400c801d460a036014400d0824419540d0341402036844c2941c178590300c440201441081040c0206d1603a023000c5003622005100810030490910008143c84555000684691100310000080540020704202d2455954030b484485070781d003000700f644540b59000f0291002622407407941031a0310901542d0483d10580c100551030724920805403c03950007030382105415581d104014455518100002d58003128200c085000d4170302801402c5491305038144019008440090250500780d94407c1592004940c250450b40c603400010502c81c00d0030340d0101030b54007482c0713000f4141010741e1005020f40c081c0c1c03c4140091443d904d540703020003100040182100507500800350b8001b00700304180b10710b5 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 648367688 1250 648366438 648366463
    0x100c03020d0e0a0309060207120b0603010209060c100c09080d11010204150305190902030d05090f040507030504030905240304060b03122101150516170a3f020c 70
    0x40a0040c2c0f42d240c06891102541c221400f0755000c46d10422000222004a20499034001d4007505075171203240c00b00303019018075500168130170004101d40b4402403001410140c1c415a44805004505010205036001d002c180600000c5400827480464402e01410003e50601c3c034040005140940d03e5822200c050b16030446200044d07291018000310501d884610524003804031820081c408840d400030345e9411049c080e50043c00f402041c51400c554030300105010b0100040e0003440700d46030240f802401400c0c1164100c0201d10705030400300d00303402c210794449903030806007400c2c094100706c80c80100190340009004548468641413111401d88040c8a0a10000710300800543c0300d0b0300d504580042d50300c0300c507140c1040000c048010001c1c080700c404c000900c6e5280c1d0808503924910b415640465820145001d0458600d0f001c070402c1034a002ca0092401c02d0035507a80817000c01080f0000b4026401511400e0303141c5200b240c102645001c40012a4040c000e0000014900000141618201020741710712 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 648368938 1250 648367688 648367693
    0x6030b210c120d1d060702091005040207061d010e030d090c0f030309061d03100f0b0a03030806040b180f100807090501060e030303040c0306110f1b0c0111100c03020d0e 74
    0x156000a42c000c100c6984ca0400303205400904a088004180f090040400103440b600d0400082107205900b40600405800080d00079580d0340050b0070440090548180782c112402015001540c5290741032040450581a200266141c0f101466004c00a41401c80c016240e00c507204600040f941006464040214440c8c2c50b906120781c50410082e240317401c02014480c20341d580c0f00c030459290750081450020036800d07130300010340d00000e01c801200074145040080d410410701031002c820301d5000140248500e071b0803103040c844441d0250610a02d5178a40014504070017800001c900c100f8180c03410503070312182520b1045855552403a40d14907196041d4004c00f5416074507070041c80f1103684210015220441175009601e5410b09036901d10400010b40f1015044a40d41c420400b6401c1c0c5003011281446080070703009840b51440802092030b804041f11340095032150351100b1002d940502d182c0c05420f605200038090b0700007028202c101400f05c00c140c900070107071300304072100d80c00403244644031001490100 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 648370188 1250 648368938 648368953
    0xc0d14010e130b0403030f060312090806070c150203042f010e040204030b060f03120406020106090506040b09040615030f030f112a03030421050706030b210c12 70
    0x10001c000a10252240d15441032410501c0e0200700d0351081540c20507414600058003240301681c0358020407981d04014034280e9040000391505612213042000d8400e0f200954800d03444a1509452101500708014109c03040c200c6203882840b92a405954068010000007030201d24a0340b84060040390410508400d10610440c6c06c3c2950b0b20590b0185d4051056404500e000e055440710400300000502c018480e40c0300a0b600c290948042c0442c0000301c9201070b5864455803a984080d000e030a5130300401d10180d141c04009142840c06001d404400d00d0041c018081c1c80e202c5440c0d2501405410340c408220601d07845000000075000350403100d0081c080d43d1343c104090b140000007032146007407400b00d401c95489000c080721204e07080e15103144101d61010384004807000b0140424118000d50703102d00b801000c0881c20203030342005080d44c1602507116000707446555803145810741c100c900750402ca80c6c00c400b0000d00e640381454543c03803100603c500841100c4480149100281072010580881c000b1500a0355 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 648371438 1250 648370188 648370199
    0x23090112050105011e0314100e0f0c040b0f01050d0615030c0305061f111f0912080f060d051c0513060c0f08031e01151418090c0d1401 59
    0x40f0303140c090001d03000c0c1c8811450244400501103440c2d400301825034170356480494244441000ba00041001c4000144019a1b01082060b102c0001741c01140c1d45000c0c402c1020003c1c900f502c0342c000914030080c150082900f10000448103900001c6d404101d00b565400c0101d41d050b6003048010444039a60350109207411414402410340d84064050340c0100303450b03c48251800308004000c0c01462151810140d4440c401c0002c0d440c048a8110420321100ba0f81058000d2080c903801115040340a2024400c0100003028111070b0500100c42180391080403201003806858043c0f03c00c801607004808030390490258100c045c00505c41002c03490046030b000200d0061600c464074621005128a040101e004420b41d1100280e145110310003e1180703030000000341d5015443c030360038100d10301d144280c0700c555a1221800e03c203000305030004c2408240c0c070281607950a212032080b41c0309284498540500d83e16400c003071206541000d4000034030b03240140401341a422440c8280107885c2c0e0b0f0130741c00300100e52521 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 648372688 1250 648371438 648371441
    0xb090a03140109171306120b0a090e060f070203030f0a11160209010911160f0b0114130605100c080d020a05091e100c17071b050613230901120501 64
    0x41140390741d07586045c400f00701c4070014034a0601c111881c84c180941551130720039520000f002a03240a680c0000e03040c40110341c1c029254440c124000c80001107400036200c00d80d0f61200140300f00c0380c010050340200001403844801031a41c98001504070004031f030301d0a1481260249802c1074400c07001013607200c01d0130808e5150040000e8010400c1ca003003040034080c40c051021452180c021070103182c555489801e0b00308500303004981081c941201c62800d0650f101e089050340345110901d203610840520070001407a086038032030b040403618001c00e0304d469040981e0301500e9040089006070344000d03043c400089010361034001000400d600b0355649944511600802102e407000220203402a000070305400c8458030385650f405030488041c10141d611156901d0a940354901242c180211444049101c0d410000c0c0c001801c0c000d4400c0e00c0c100c07512252100184034403406204103245c049204204208240c54080041480c04c0505c541004100c0380c00d50080350b9080c5007a8058040504094840001d0000030f = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 648373938 1250 648372688 648372713
    0x7230d060506040c26040206190206040b060f0a060e120f10140702030a05030c070f030c03021902030303130611031302010915170c07060c0806100212040b090a03140109 74
    0x85d04111030b0401e071402d60008001034103012452180d620700080707004e55542a040c0c42d0528802c001c0d865000310000700007501d56400380c404441100c44034011505d03614080580344140070000e00038650051518000b01c0f001c142c40744030740d500041080030300c0040181c140050b240410381103000f00f030302603640f2501c07104a40c015004002403925640902131240d038040103c4040d01810301c1c050f5142c3e100c502110300284580080144803c40c0c49440d00101900b02c10301d9401240260295900c8a00c810000b2900707a02d0010020f516400420000d03070715410301c0400c1911a802001e00058034004000700d010190f00a40b02d00c10b030090f0708070300c1c40219a800000e107409020101394604180303c0d2000068681e009011288103c0401d03a0005005110820240c030381107500094148100000c50401601710312043c1c0d030b605c1c01403055440c1e1070002d03030001401c48031480c041c01c5003231325140c40c00c000303001150080144251301038003d80000021a10f1500b0082210780c03400c3c000603424403039140004032241c8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 648375188 1250 648373938 648373961
    0xe0d1211010207050304172401240e040c0c0b0f18120706020d0e033c07060b04092306060409020d02102f0601050105030907230d06050604 61
    0x4100d4000044d030702006440032642c0d10b82e41e420422078030240b090b0400e0b4140d064903285407002c07690003200c0741461581e50304981142064810b0001d4074a250210500e9202c000e201203000207000c9125030420794011100d00b050b40ca4281c101c0700c1d040e03503081140c0c041919081d10014200701401480801c1005040c15408e4400083c210a500490b4009580c041c08001810381680400da40800f4600354210407100f00c103010030f8070398441c040124a0b1055030341803505410503826040f9400c84e001010281c3d0a04980f656585007084030903950900545036291070f09030040d448000200c0040d90500c4484807a84004290f811480900e0060170b141c07101c020f041c54031443c10403000c40f016072030b01c80701c009003079405541443c0d0341c45181005490101c0c024582d01e10010102c203880095051120451b0b000740c40170340544206980c1c400044446001c291030510140e008440d00b00007030041c4000214144846240b030070501030100380001c00003e4244420740700030b9102c1040140711f15245c4140c655121 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 648376438 1250 648375188 648375191
    0x12010903020f0d0c1e02010512010605181002072c010b030f130b0c0d0b03120904050a0c170403030f0f0f0e060405030406050d0908070c05030d03020c0c010f0e0d121101 74
    0x41c0151259101032228502e002c541c81c000500045c15640301f541242c2d2200d8581e80342c220296944c070401003096001020461300155a0030031008207181c2051810045c010703584c005d02d0a03e060400e0890042020f42e4402c0034494001088051032002c2074080d4003c03d180c0c800c03e5180e2804820a5050070b0000380a00b101519a110340340004254042542d0810144001d580e25140000c020340000c0c503886400550501c5881a028074840c3d0300c000074488110300350b078140b01c031b40c4a00744088203940d5110700400115000c80a008140320022541c0c41d8003900929001c1900352407020102c040741c03525504403100e81e8540045451840d0213011700940d081c00c15004080b10701c1c003030700c442d07032203015502441c42003080000b0040c40308545a080005200e030000d404503954403242c0740240080301a40f10780c900034001c0300100c40c8000e01034426182c20640d0f02c0d001e0001d80a003000115148160b14400340c0a100d015040f0030074984400d004920000d10842458056240951018158003105258410240e = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 648377688 1250 648376438 648376457
    0x3010f09020301050319031205040b07020706110c041107080d02030f0c1218070519030605071107061404030b040b0402011d010c0b10030b040302030a09050d0201170612010903020f0d 80
    0x3501d001401c90301b42c1240c0051022044181d180c102c40c017034034060314107030171500f0318041c441403103030f40140e040c05060f064007164500799035140c0c2914050301a070003904207900048034150103030410341c00082c001c0b1400301b8402d24044e070ba5694491140c00a1440c01001e650110403c218500c0c41103000b0340005041b40f6140c2812002c3c00540b0003024020b0920208c5180c41c844080d00d01c42c20405040584002030a2107440450010b02d41c12020f801d120036140c903400c101c003041000d4020750422001c1d03a05003000d41100c0d4140349084d07912070085840003a172820200000004100e4000d2080e0040e0b2040040c0d09990174940001028502d0b010060107152071403c0102041c0d81c5c02c565080442503000c2134407141580c0d4841d01c01c414941030f03400a0183c04041c02000109907000c030060011610a0303c400d0403042c1c4940510400c164030842c020b001c100c3c5d9907500f41204180458131075025800401075605950910b2541d400d444103210100c0c0507038014110303010b00007024000321700300840301d2800f45a00e = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 648378938 1250 648377688 648377699
    0x9060e0603070e040b03010e0309100f050a110709020c24010609030f1a040b01031703041a0a060308130e0a0b090f0a110a080727090c02100606030203010f09020301 72
    0x240d10000d0902c100b4021815416045515503401c0005030460083c020801d810040e80c5407034a03075002080c824132880300174029200e41801620712443c1510150b0354503040010a000c103583d40029103804c442c040c86080800240420140002d1410b6001440035084291410081104142500c0041c40c0300c0c16501d4014400700754803901d094112504400b8074000441a820417231038904220b002c0c5222443c01d0000c22050104d001426070403a840385000c4c0c00c01003828405001360b4041910000c020422500f204038002807503c45c0740b90407034208038000034020381d266039441d050703409200c0c81140b450b4418010881c801c1c281d0031142d40003068003024007403c0c01001c00241025401000140180000c40104681080541c4441d80042310314922304e503120440100a404002d0441d40a800151110420141c1c801030b011140903001c130740c0c1d540f00510350410301c40e90044c0803181248021446404d5003800c14000e0346c01650b0041c1030380d80f401642d80d41000703000124162242c000528507401000100507 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 648380188 1250 648378938 648378949
    0x80915180a02040641061605070909151e09060b0a0603050a0b12030904050910060b090a080a0b06010e0d060501031b0501020a032a02030a03020d0e0307050a0b0703020304030503040b0a09060e 84
    0x5040c10443d06d940e914202085400a11040e440000d060351054003000f041181d400da03c140c1840b4042c0342181140c4610720110803d4600168200d041d50307141900e01003115007140c0062403001e20440001c2484a00340c0042000013802d036002000190301d030428041d01020b18807030b803111440c060313600ca01070ec84158101aa281300300d612160142e070b51840003907841c0c0d4081c80745608070488200b050140030b90300c84507030500c4e800c00c4204031705c038500882000032049000101c03040007562104000040b5514031b0300644a41141ea482c041d00415500260b4000900c01d104041c0614458a0f800c0c0c01800304102140c9120095005181554440c102c100c000c660001c0e0810750b1040b01b010021020f4076140c40e820000d1099410086d003511071602d07281c04164000c00c10105600c0c1950b00c0c580d0202600703003010b03a10a101e108290b0000d45000081c441900060000c02c2c0c0783e806401181c0c505a03480c0d84d01480d41c2d010394044945400d000c111103900076072080721203004001a103441601034030240000740 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 648381294 1106 648380188 648380309
    0x110d0c12110a0909020d061109031204030b060d020a380928030b0406020c03130609050105131e0305100903080915180a020406 56
    0x618904548144d07070000c0d4000301145034955042e00d5280003001d030910081c60790300d0104030304141e80e142040051480550040000d41c0c1d1846c60030300d400a0140036064500c1000c1c001004800b503525041c5103c2990341070b12884500d01c01c1c00814800d4540010100c1d40f034050340742d401e01e0011140c2c00140a40d1801602e110104030000c624490000075000d5603982e092040d04014008200009040c42d070180c49400014030b001c13140c0c5142c91031030700b06000c40f45014550110030700545038407003030301c1c0000d00c82804c01506154001c0e401400103110b6000d1410034a00b4401c41c074464442070b1540d0002950810706541d11100e4411042001c1d15400d1016004580c1d03c0001c100100c20000308100304103050004a0051f440e10400c01d445a01391680100c0380e0700c41c0c151902c01603521031217110014200403d5054080400740016500a811168200014009002c405980c0c2c0384070000503 = true := by decide +kernel

theorem cover : BRFrame.Cov 648201438 648381294 := by
  have h0 := BRFrame.cov_init 648201438
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 648201438 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 648201438 ≤ n) (h2 : n < 648381294) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
