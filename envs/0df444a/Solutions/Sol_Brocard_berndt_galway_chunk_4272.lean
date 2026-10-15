-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4272
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T12:04:35.416787+00:00
-- url     : https://prove2.me/submissions/f97f6bd8-009d-4cbf-a8b9-573e0801d818

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 768165467 ≤ n < 768345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 768166717 1250 768165467 768165479
    0x3080c0106080d020c1c0f20011107030f020a1d070212070b06010e01030f020f1207050720060f0d0e10020a0f03150f1d09421306050a020301 62
    0x1558843c110300072030f0760f040c01c00c1818000c6c55030f2590341c1c540904564602c00b0000207100c00a11130b9914409a54560080d8040c4a001074071181101c45880c1400c0d0321050040020811079100b92481c01d200808840010ba900c0b0380a00e42c4000b55404080341100d1f01041c0a10726804014501442e580010450f04220321602c441c44980e90040c0b242d818040304030500a01ca1b0b2003a4030410403110501c6046480344102c6405500d181c1100d1a1052082c01d21800309000c50f0092081d50052640401715004181c062601c00240c1d0740d0b03240c88940c003c1003d0080841911b0b000f0060440d003248020700040008001424529080400801401040c4100900c0c8903203540403a122a12071200e0401045030904842c0b004440407a41c0d0100040150300764002c501d544500c100390b58100700c22413103082980c5641d082c50b40c4400010b0000c0b800322800100080522050004588a1380710050b0b003403450018032071a80c05100800c13201c40d40164550307403420081100c903105072604506070701c00460440d81010 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 768167967 1250 768166717 768166723
    0x60506032e0612031416051b010e09010509041401020c150906070f050a0e03070509010914100807120201020114040b060a0f050a031b1e050f0603070f0302160c03080c0106080d02 78
    0x2035a69960800282803280010181c100120264440110703100c0c2403213003035032340004490411400c0c000b442c400000d4200f031504020403030613070704001d0a0321034649850b9548803441162101e6a52695000d0000f00044082404801d86045c0b0b2150200300c0c514080346500e00b000300c01094071081c40003101d038203104c907a070040c1600e1f0309e64490304154a03102081c2000900c0c2c14520352180f9845402c9400200d0b4a8a05810050050400b01d03c050000e841d40418074850403c0340c010101d00b90322480040205a510610100a1500600000406c001100c400103c0314004a409942c00d4101200380081810413510100c0207086040c0e00040c006e003044000b4107054107034400036007020b15024010b08600a0000900024040c62115104001890144c01c02c0c0304000c0c46054031030501c0d5458011030707045c000101d0384100704c26a100c64921b41c00c100154003c2d040b404040c000c07030080c0307400c00c1c00041907411034001450050f0550f5440d001c40b01c50403401c0d200507421000e400d8100c1c03456141415000 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 768169217 1250 768167967 768167987
    0x30d093f0512010e07120908040620030a051e0d0e0c0604050102060c0c01140916050a050d0b0405100e0102070b06041401120809040903030e0c030712060506032e061203 74
    0x24013020b003054450b0881145c2e2041c02c0180c079040c2510b09009101013000720030040085891030b441e1001d0b84000d501c800414180c02c200032078516003080102c2d01da404e03c69401003486c0030760b400d82c003004050250090582c0703401135106078805a6440000103821b4408000000b03440008070f4105140c1820040000e40341c0c500030b03018502100c00402c0d10001f1240c01e4000252511648d03070100c040340b0b85500c90603a1103803031544510700c00c0c85404011a0604080c5071080c04d4510140c0390125415140d550081c000d10000c5c0281c920340211903100e05d900586004901c070352007100001685864241c204194020f0000c1d2140744290300d8070500409032040995124116140c084d046026059203041543c0c103031003001042d5034403926107400d10b0200350309684110b18440d52070f03081781c41202d44041415610b0440d4081c0c0040c41103088840c10018480c0e41215a1003000942034601003085004a2041000b6010011803a0650391800400c00300301403144100a10f10341c0c0c020301409500e607d001e4640014 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 768170467 1250 768169217 768169229
    0x90c0a0f12050a05060709030b0703020415080603010e061e010e0108120a020c03121b010c020606040c020c0405041a07140f0306010e0310020d0605030f030d093f051201 74
    0x14416040078003006001d0f401c00c190f008005c0c2c61403443e00c2c01d4020030350b5041e0301044620300d6803000410485886413003901c00f84c0e0080c03180c0007020741c80c9000903075012000074201e6030715640f15841e00b402c07960203000150182c0c2c010b02944201c1030781c1e40b21181c0641e105801030102e9820100040040d41c400284808050034002c0d0b4050381c4a1880c981241404c0b00e001c103544e014440c00c124403e0f02603d9000078503207260038518282c1e0300044101c02900741ea0306c405088005a014501007940780c64030703901481240c1268011264110181804142074030740440c2c0c1910321000418524a10302c14480b0029070020b054a0681d1100034600303040741c40d034042c04194440001c008030010f80180d009481010240d80000c04450075031520162150280d0f000302001550b40d41064000a03490800242d4021000040b070055801c004001c04023000030043d418040c3e5040700e03040c02c014483c41d4041d178158110403a50b60200125552031700c0d400c40c1030300121030031410071000b0480003202c0c40c1d21010310343c15124 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 768171717 1250 768170467 768170489
    0x9040209190606050409050a0e0a020f01030207060e1b18041e02041a040606110304150302190e03011103070e130608011e05060f0603040b0a0612030206090c0a0f 71
    0x75081c8a80301050181d91911101620344407000c940c09400c1340140c011140c0c001d07028030117a81c81d00500b60591307000d00e24404480d03010009000c01444c048490912002c0180340040c1451007075110141a0f03a015a48046aa0080e181c10b8403054102008540701e080141d614000e6585640d1002c0080000140f01608285c00c0b2004c0c4a0f00da40c0d40c0d0320580030750b5002442400130000390b00362003400c0400d00c02500c2c4120720344080050300c140030b1131041da11404200d02540c01d05140800402d514407030030701485c040603400c0140e1b914051004110b501c080e0325964800004120314014142150f0111071320b40f1014106008001e012503020648205a885c00c1d202080f0386d1800c0c05030074014080a030441c0c4440d50070a060640010b46000c280c03d04840650004d0000340c0f00c4006100380b004c2c00001181c0c10200070400503000c0351410340c205030040281000040c840390350b40b82c2824202c1240701e0031070060308004140200c4580400c00c4a0700040f0490301c200207645071010341507150f511840f808070f05203 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 768172967 1250 768171717 768171721
    0x18160e070504180b1801030506070e301005010e0403020f0102180f0316090e0613020d02120c030a14160f090c020109060f020406080a020a020601030209090f0703030e100e09040209 79
    0x14031103c5c1c101030040fa0709500e80060356140c2c50f08a407105011103e100010b918280400a0b0b4904407100c0080300900000300f944100365101d050f1400b070740c4885142114402c1c8a8072000000d11407207141d00030060b841d084025030800d490020b0a05c06a0700465140340e00521000203117014400c00c6034000300044481421080b60000820f040140c2803c410000504c4c400d000680601030390003059903080c980b001d42e0b01036039428016141c54a401d800194009000303101c44030040c1817001400741460640d408171500d03682c1d19000a4a0240000703000c944440d868a0a058200b1040041c0480001029020b005280c24a40d01440f004554420003644a40b51180d54881034002c0d03002911198207d1024050f071010840184060750003403042d140040d0100000a042c8a1a8401e60b80e00205a50250080780d00e99020001c0c11440604480c6140c000c40c00c2925450604100c0d507001140300b51105083c1401c81401c02030300400c00e612190511420065a114659070410440d5000342d04885400300ea07 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 768174217 1250 768172967 768172969
    0x14010b071407060e030d0305040803060d0503070818011e1e0912061401050a1a0702060d020c01060905060f0d060c030605120109020f0103111218160e070504180b 71
    0x4607000200398840380603115020443c258001c81e00186008140d08941100341820740c00c5045800c100c6010300148400d00101b401c0d49000c201e40c580090140d0200e0b410109651110b5480703520a030030080c9600d43c81c149440d51560000380043c7c440d0000b101500d1a40c1d0f01c1394014202124103a0842040b00d11346413916140d40c054400000030700300d0b1049401004c500e6240203001000040034600d0980e04a900026030303840e0121500c810f030f071407204144d06541c4c0e4080c0700404640003000100da100303000b800550311004203440602254001c02c0000b103a06c0d440c2107084002c40d407010b0144c500601c0e41030140c110b90b450b901001c0e450964410800543c8180d02c40044000307064642080d607122060100c2205840d10541003603000c58021a55441d9500b091070042d01110500d61f02440c4140045c402c0d204020030301e0401d9070b80586010940e00381d455010a01c00d0070301d80446955106a29514014840f94200ca5860b6500c4045814501e251905040003c03030300e458074032101c0900329100c044010032 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 768175467 1250 768174217 768174233
    0x305060727060e03150702030a05090a03080f0702040605010302212508180a200112110c1b21070e0406060504150b160606030b070e1314010b07 63
    0x700040c04400012166290400105201c040c0c220072842031040d0000803a110301c1c0d114a00d0b00404c02d54000798508080704100350b4843d04641d8500f544854204400404241428000d08100d505200e45503540e03251481044102c428a8004504040c41440b0a40d40d0b02ca0102c2179112443c010101d40702c80b0340d5011320085040d440c00400b04168110700b21206031041c2c00448480c081c040700030380402b18103c0460050360320300b514003000d000300d945c51010480c80100c00189042100040c0b41500d00b48000c003d0130000c0c1c401c0b0342c2c0381c5101c0e1000011080285c0348113201001c609030000174060f490445c420001481804d100e4580c5842e0303406a45640d0700000d040003a0300080c4490b82400469240030704122005002034481c19015905003480000c0000220010f101500d54400d809410040c0703440200648241041d8103c030459511440440410710502d04030740700f02080e50324005e080b07107800280301085110b00283d4040301c0c1070007030413610311100400c968103440d03511091070341700c1d0514240008 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 768176717 1250 768175467 768175517
    0x209070315120609050d14030106050f1224150708130305061306050c031017031b100c05040f090f02160b1b04140f060c03040803070c0504050103050607 67
    0x5401e079080b07040020890560403980340d80d4010b0051310303c0340081c504180c5d640c140008281092240030001880014082c078040d143c4404458101428810400888200840151401c560745518160140e904803c161005510000140d41c1401c0b09040820205c08034001c0c10001004484042440f951400c0351400100046401c50f0440305076041590304445500740d010402d40b1034904001c0080d4161002004032801000552114880207151001c283e0020308204904001800100140c039288818080d1401c481383c0410b010f042d6052500b4002003c507941da8900400344003007800104184040038903028221818620080780f01900ca420440091290340d41542c19000d258081c1028000180e10790351140003800958071001500a141d9013640c0142e02c01c007409510520310044040c2801c2c407a090400d080502924145081e011203d03044d90855088080b8551000c1800303820300c000089114002c100a480401c107550441c0c50301900d5010040440061060b441c0e4000d6540f100003003040 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 768177967 1250 768176717 768176729
    0x1701090c030311010506060403020108060d03230309010c020c01020d1103090a0e0708010509060f040e0712150c03090f0201030c11030c01020703080c03061807020f161509030209070315 81
    0xea054503454003034480000e140040d000e56203010700055036410010103c03003d89070161a40f51040d81c501c1d080010910003030340d00310300f001007841d420b01c030260301e6102440021500d110300e03684a180260b94182100c00c48204c42c400c5500c28800b80752941d0f004500c107411801940341001e02401d01c41261480d51180000329a0081e001540006405c01001a0203006c0c00d01030751820110790340c5104103c1c5024003920303501ea00c03120620300d0850a240c03503400409070b80d8281c4144e0b22050f6907528550300d02800001d06031252064141a001d94114610603046501140d050401c0600d605458a5500910a020003410305607910f029280480c0a072490301e142c01c1c2c1c08000c80c1e60b41c44005c01c005000c4c7d00001c904801141265010403030310030800040e1781c0f1038100902a21840503c0c0390800550900291002096018503002000d04200600406194811404940708010714010130304107038084034a18001000069003040c4010b0391062144e0f50458513500e40844d00c01d650316007074480d00420364842 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 768179217 1250 768177967 768177983
    0x3020106150323070504091a041d15070f0e0607060e0f12120c09010c05011401060e10080606030a0e0a2607080703030c0c050d02060f0718170109 64
    0xc0314042d500d500f003104a2103280500d4081e5000c81c034001025440c040c0c880b000400c0b0184030a00c00f40940b544400d20300440d03030036011189080e0101103000c0390446010301c448800780c42041050100100070361031540104003040c002601c2d001000901011001e2803030030030403030201c00350112907403a902500c0d90190048070821401c110400c00340d80d02c1500e0107508100c3e015900695220601c90029110307442c4040540c0002ca60b24808514540e510451550341071000218420020842c240f0651030103170385031140c40c8042d50401c00003401c9194580d0000d0b220b00e074004100d02841d944207034115000481903a85640701d460710340b1084081c0c1010604040184910101e070030034001c1074007025490111380720340451400445101880a441581000f604c40d5504100c0040001d00c25801206034004902e0705807007415042c0d8840e42420401749110006a114509000301c402c04a00f00c55000011801c1c80c0c1d00071342e150a0300e072040b10540d00c2507041030150650302c14842582904003c5e80c0903884684 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 768180467 1250 768179217 768179249
    0x10608010312080612030325110304030b0405030403080c030706050109020a0c0f050f0a32120a05070c06030b040506060301050a0519090c05030a1404150b0d0210050a02151302090403020106 83
    0x2035070100c40003d014003500104c44c64582c2d00308d503006000b102014444c0b4005142307405d0460715501c2007000d0180080744c807440700700000408a92008043d040b00640c0002840d03031164a030406405841c41a00314000082c8104400712105400c580715040256101d0301e0941003c145040c024100408000340240c180120448030f4200000000d081801c00d14030180c0414005100c0c2000088620149012625900c00c028224104101c480034040800d520704d0304600e00242da1762a828401c600703500c4030303001c80c1d1a016106d6080c9428000e099009400b80e441358159858100007541414180c4105405260407005404414130000051005024820030a10102c1080b01000b419a4812501e1352031840c503201111452900d83d08a00d4003558208188101c821020041d1900904000060300d034800380e0742e42c42c0001a100c5080c2010b0a080549401352544074014000e1b007003400c1c100b042014180102d04000d61254480c6400c1c280c03640684003c14070303276958038007130f401080300303400030070301c036480084 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 768181717 1250 768180467 768180481
    0xc0506031911090d080c16230d05060c07031e0810120b0f07030e0a0b1801111801201f021c02130e19050106080103120806120303 57
    0x107001440326a141804000c4840d04640b554210301900f0045a4849981204940440c1000700030349407252440302620742d94080741c1c207034074a01a4203611803004020440c03000040e28040d6078500c0029001035401c1d44140c416507a07000e0b21020000c0140b07404200c0800d40c3d8041c0340c402c85110f4161604680801040080450003405100c0d040320b0440c4690602e203000b1039052148002604041d5101490307901c0342d1a0019040d1a003c0d00a01c41d4041564840f55280c0c0001c0400880034641d002c0c01c0004098204501d409140c4000258014003030381c14424445081200c55080f200401c00da4103015048189205c01225006807400014001c0102103801d8900c07240c01055900c42e0324840048032050600000100003640180c90390004102071000101910724040e4005064145000054000b000d4407010a110814000d4660b091b640451030508414228903104035805800f01d810034118642c510b41d02c19480c103601c0110041040740101c0490390503103070414000d80d207010810613203441c1d02c1d02d00 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 768182967 1250 768181717 768181741
    0x608071e180806010918080301090c0c08220b0f160c0e0108030309010c030608190501110c0708070b120406020c2a030706031509050c0c010603081c1a0d0c050603 71
    0x300918545c580352284545071207080c41a41001c09a00c8103e403030035680303041900740041000050040600002e914583e001807030460003016403001443d070991105003070410124004406403c003801d1a4070070000c3c140b07070403410000c1c0e801c0c00e9801d280389103c3c59440d00d4a51441807060b0300914054941000204141c880440610310902038240204441c0d021903000301c0c00c5d6425440744042070b420101d4400c1d110304e03101810094441c0a4030000c034000e0101d000210950b80940c0b05041d80343c00082c401d2000c40c0c01071141f0070040004062050400c0d49640c480030591764060700c000e011541c0012140b8031010280482c4622481c40040b8041140d0a004a494100003102c0620f1003405103400c0460214020b00c81c01c0c0014010320030011802c1e0600e0504c0c0d0040102a050800c496020b001400003030000b40250809540f01c0d4000a844035030032446040250a12081c00c121103040c80404006030402035102164200212213406e0303507031540e01f041e004190240e08000e401070000010004161400b03 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 768184217 1250 768182967 768182969
    0x801061512050f04020f010c0203190c09061a071103030a0909050603120d09111c02010215070503060114071502040f0b0301080c190b03040303090c0608071e18080601 73
    0x1916005640310354a48400c0485030100c0b50f40d0b50309040071000c50050704213030903031003c102c0060404034071038031150b000a071a080c0b6070151020766003030314500f06042081d110300d80001821861401d01c0490b0420f4060340c505640c1900059244501048140510030310341c52030110880301030241e0b699040034207001000003c450080b00d00582c200000b190380d50400042003135404407074900040c1054020214400075104800095a40340080100000b042e540c4500030070000741080c80c0c0180c0003100b88006803c01a03018410095031442070100030415070802e00f1650f104000340b0308048000d014140c2020300740500e10010b8456865050f0305076080d402a0300038030985606c0c1d0000d54a03d6550001080b581c03100b40150080c40d0001c2030800c50391300700301e60a8205003540e40314500c0150340340c410071542d6400c221001d0340000d0705d401e420710034000300c00a1600540070b035181c4440f941c604060040d121001c8041120303084100080300501c03203031003450016200341440a003400041e0b6a090010395030882 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 768185467 1250 768184217 768184259
    0x8010e060f010906140c0f030405011b0c0e19020a080403110c1804020402092d0103091101140c01090302030d320403020102070602070b070e0108060a090f0204080106 73
    0x25010880c03900d012807950141100582d1029011400d0480440d2402d101c00d00200c59807600780a14a01c0841c1401400300381000c01c802952114904800144980d0144604900612411072030320041100c0425420903100c0704103003404942c0b00c104410030b90401039209030741c21901c08110302c42010762000d8241d020794001da40d1208070021521840f074070f0300328100100f40c3c002007200c0b09070050042079035400e9105000030300050906142d1808141e84061001000c000c14001d2040e18148050703000c00840003400a107803c11007504141c0e1542003002e005045c0714140015545481c60355441c0d081120385c9910060000d001610300c900d0080d503a50000400700e400d6034140b1280e061040d456503490148448003110010410301c40288044442d40080c1041e070440d5001c0255202190b010b00092401c50300c5028298000e14201600800c640c0c144115241007007080340030b0000582d0368046c0c64083d54845040050307001101003003d4004d121701e0744044025402d004c800a00b41362041c081e03510780c00c0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 768186717 1250 768185467 768185489
    0x109030206070906120504050c0402220b0906090108060406150e09011a0906070f0b0103030c02120d050904020d15292106221d0a08040306091e030801 66
    0xe5200041d11105440c4c0900c0d400904a0b42d071300f8a0240550f00000d0700540284250f443c004600c40100d4180d034041612000d2405506503401c1e602003401a15a0081400310380860500100741c0004030355103c0c8010f454100a01c0394080703922556298000d00042080701000c41d0f085002d440050440708071081502d100351180c10001a074008001c458010ba0181c1c002070701c0c6004040010000203402c03c6000f5208802e004210800194030440f01c0c034040d41c083d8a400751038900901c1000030340307003001400e5844c6c1e8000305009065550064103403540390104640241c2c0b00c00b000c507240001002c41d0404141841c1e030201000800805000340401d102c0c41c900b100a02c11103050200f521548620070030f48107451400303c040d0100124a81e109504040001c2402e001c030380c4400100914180c41d140e04103001641d44c05e1080c00311001448404100c0704100103401c2c03c242c0782c0c440c03140e94091444043c0039652035030748038401c200c00c40003070400a20206602c503510b80004d05005041d00001d015100f0260 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 768187967 1250 768186717 768186721
    0x61006110106080703120c0b0702031c0e0d0819020d02031503121611060c1b010906090b0327062a1b010b04020d0504020306070c050a0f030513080109030206 69
    0x2410b000c1c8606440340d100c014420315242d0303640c4e0395a94021aa8280800c00e80000e0311001a6001920038091003a0368001c1d034039420b8900c0401c4800c20f251000c442410304d0070481241c1040003181c80c4047d1000790908d0b00a030b50314044034080c0b040700000c1142c1d0b40303440091040c948003c00e038007130360141d103420038a182280b0803401450703524040001d00800001c010300150341002040360410241500c41c00d046072130501d402700411015000060340c44815048425109000c8521a00403003000e002440c000c0040c41c501180a8020203450103918031914000000801c1120800b25407510035440d500c45014817017002e04040c2d00c074041a50003249841c140f020061411100e000312154540307074039401c246014040804503d200d440340c07109000750b5407100d4040301c0d590f0300c91004d07000c0c030030240714007003602d10b01481014108500244400148111030540e207020580024825100d9a4003a0681c9000c0d545801e0554240c02130006174070480e5410f88001c110000103401a50b4414480c1d004c4847c10303 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 768189217 1250 768187967 768187997
    0x3270306090615010c061806150b07060b19030c23090c07020102070305120d0501050a0f0e0c0702040510050f030c03030a14071b0612020a08060d020f03061006 70
    0x2400290780c0458a40d10050110300340d422003054000c405581414526841c800315a02c8901303032042c02c045c584007018001501028401c090080e0a41286110b59001c1c41604051080c0100d005035980540166a2940007441e03c0e2210403032071150421382c18500c02025500d16005c0b4240115000303c01c0c408843d5045640000d0800c1d00d5820782241c001d05501c5160f48100c4985c54681040d40c059045100d02100040814818440d6425041400d610140d0329051503400d40300b92a010323802980038185610f0300300070100440d2800c3c1c050f039201a03200b41894550306140c9449024051000c1d603c28034050a0200201c0300c2940340d000c4900135203a2954426000c810142c90f2644210590b825400802680810034405c1d010660132600045804d4149900b9440f04211241d405540c1195901c500105101c5641c000440d4203603110949020b524010450300d00405210018007894021041da803111411035030b80a4106564000160490700d80b0f141130084000081094482c03080400c82101100e951 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 768190467 1250 768189217 768189223
    0x302011409010207050d1a090d0f090f030b092b080c1e09011103120a1103130b0606041e0e06010c08181801080c011407052d032703 58
    0x1a101058020741310083c40c00b0300f40406241c044008036200d1101c100200040000a00301034001c1c8403030f00003800007141071a000f13020031050a04c0b10b402d11414900c10448101442a4202a20390181ca2030042d81c55181c141442d007040410480050031389141c070703d105811180100041240c41da5548885500d0741e00d2140090b10481c000c0805a0300d0504c00804020147d20040010310010700d04085061810030070242582c1000760000300e1183d00c1c00031f02413050000c0c010b100700c42c01405112842e50600700c905000841e500307035005140e6010380c000100c1c3c1e9503943c03040e10024040a110440c1d0030b01e180400c541c884080d40101c40003403406c00041030040d40300d1000c405c4510380c4080c885142100506030b100a00c040b55000c0e40d84021942c0c201c02c410102d001c0c1c0d060013072100c1d00c003c0402e46007000000d840080317245048446000c0034400c400203d5400107281032000003030041c00c17030300002b0341d9150b80018003001c0000b01580300001d01c140e00105103942d4480e00d000f1010050103165101d40406803 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 768191717 1250 768190467 768190477
    0x2010c08061e190906170c0102100f14090a0311010c0906080a0603290604023a0c0905030c030d0f1206081507030b010f20010e031303020114 62
    0x382049540b00c0d80360910b41260312490145600400307044500029200d46a9000115004100c803103840d20820860344a1094440030b0710b0248401074003001d59660300003907840174801201101d96032210720740855902664003030014282a40c6082c00302d40342002e01541c2d5210310400441c00100c0da4404441c080c00b043c441c01800c03c1d1107580d8a100f1914088049603005005024014000ea54400000c00588085040000e800b00c5e441000c00c040704607240900d14101c020030b9280202e004100301c41d9554460b0f946401c00c06840003012030550744490b82544100c00080d03109003140d190054821310241c021030a0000c8590071002c8410b015041c0040c1900d078814490108046103901e250b20010900840055000c100318080000d47c85503a0b00c0058502210441070161080d02c1c41c0a018149034117000da00f004540a007003c1c03149122801c401084403c00c0742d103c08107005500d800c0142040c00b9007080c100c81e0405030440e5266420fa10b424042e5469511040b40841e1007414400310039001403059076 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 768192967 1250 768191717 768191719
    0xf03080a0224010b0c030f18010206010815010b0d290301150e07030b1c08120a0504020307032409321c12090501050403090504200c0312070f02010c0806 67
    0x882240d184c80300d42011900319610034070550206000e250541c1c1e8085015244c440c0e8480d0720310540500c508006420314006800030200c0d9081440007141c2815901e000c030781100e03041c0d0b0340c1c40d07680d0600204060040001c02041c401c3c100317441489500704200480001c4418800318000c2080d0b400607810031076000440c0c0702d03501d01d040540c3c000450303860007540010301c50745014240010300c5000402e0303c0440d8646d0241194108404030b420124001000300003680b1002404007000703e8201500082d9a586c5a0321000f829081000a00d5a0701c265030300301586504c060503c00e014115040ca40500c4503198046c402d403071406150003c1240c200c0d00260881900d0603000900b4490034a44d140c0c80720215002c00d4582441503200351910126410710481800c58003840001950307081502e4010074014142d03020b54459401c03d247c12a405007600104207020400194050781d0382203448007a821b5002c3c0900000075505400300300521a42c016010b906401e8040c2d000308414075403250305503514070003500c0f01 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 768194217 1250 768192967 768193033
    0x1908061e0406020c1518060c0c03071106091815063c0a05090a09060b0f25080304031403040f030f1707020705030f0606010c02190f03080a02 62
    0xc070700440c40c50303401045400105400d40e03010008481ea0703421003107801d461010b44045084041c18140e001486216000300c10b2840451400200742e190079500c0c0210178010301030314560810b40c1e83c02d659001c00c031615104040c045031802d501080c441028002c04031100d1105d00c0250044044e1032520108031145110942d184504a8a0581c210401180081c900d8100c00703440d4051120030b40340201c0540a2002950361301a914100b00048c0119000b40e030707004c614010f00300f042c184134190142d0141c40003480d904a80e07070f884542d282d89010400705040820020510300031740303180034004d4440045104a002f62100a420744070b01c0c2541c00180b0044402409040788400d69400082c13007503441c01000b001030b19080241d268100002041510180c0b005000750780049000c2080d420240803258505c00000c0260180d460010006010000c601400910542651006150050f5102034030000b03803511800d188480350700c4e49003504580d0f0242000001601c01e10980f0b504c0031a8000d0048080c400380300701 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 768195467 1250 768194217 768194221
    0x20105030c03090304120b07030c0f0f18050a03060b090714190c06060f080f0303090c09070212070c0306141003112803060e0d0507030e0d021908061e 66
    0x5820764580025004911900081000080e24000440e104600074000c5200780b00c1402d000d00702504540b100341605060002002c04c000300f041c1c214071a401200b80d5420001070030f1501032a1a18a00c0480e00050384c002d5070140040184400c983c02002e0144e000e54103050075450b440c9050f1142c00c1221001c038810706080142d0700b04290540000715451a407400d2824080350b01d83e442d10152074441d00b00044884015804000000301007001a40d035121150195203181030820800d91105048228035005980c8200860301c1e461003044580e1005140291041e00c5000500d041400328403d03120651342e2604140441c0e5040315010301c1e0a000d28074044404290b0b5180d03a07200c401c1e44406038992a44410040c020070b2901d495a10820013001c1c0003250600b0050a519000046a1850003001002c3e40300704000e03c4510f80000c101c23209a0b0700b40c1000b07010161405c5c0010062110060025009601188620004240580800262450303481603545a90722000354424141810341c03101c109401c0800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 768196717 1250 768195467 768195481
    0x1602030a060222150c020a03060504240c1205060d050a0506010806010501031107020f0406080a060204031703090a11030a120807031d0703150605180f010f050a1e05031002040306060e0402010503 85
    0x103010f005d81d202805000d01117070341e45c40d0f05088a000301c80682d00c80103201c40c1c1c400306040010b41c0402c008400e10040000072a2034500405a80003c50014030881e81c4070b011031403075900d004014031070503031003001c40d01d1001803442c0590300c0320b03000c0c414407904d8810303040081072560003409003605489601c040c2a007000096002c024800e19040000341d046a81e8207000300f81d2107414001c2ca0f00f010b00600015a40c0c51462405041d0403aa11504403a80780091040c1315800001080c115091600700e0400b207a44081c000000c3e08002d442c001c0141a580d4840c80c2c84401d03500078032014030945103920704202c040030844440311006d22a48030b80ca0181c106003020f00001d41c0c03c00f00c10700d01c40ea0444000171280e0315100442c082c5105191400c0c82941d070b070010480d4000078210f40034050300b440d04074581918541f8000c15120300203401541080320840400742c1a04200000b40001444020308403040b010310440058020351081c04199003d0b03060490208a2040c50500180113a506960312480c50340e0f084 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 768197967 1250 768196717 768196727
    0x30e030606060f1b030a030c080a0e121803161e060912110306040c05090108070303020706210908030601110c130c1103121e13081602030a06022215 65
    0x80b004c03120303070720680b07020f01e602c0d0301c00c10280c5070321209514001307101c80c42d500c1c0c0a003001c0d000918000710541003894428080401040c0c07804120b40840781c0603107a091108024450f202d250202c5601440b80301306a03400c1c598050710040c222003000160109101c81c4a41040030350260327005200c045000710004011b480708907078481c94090300801c41c00410106410001e42000e0003540d050360714080c6001e0501c4280342003644d4074010300200c4014101c2c1c501d180e50207912010700f44168000c1c08411391584240c81c4075250505641150000200203030001881d100d08035400a80d1506c0c0050301c00001c16101503800190010006002020003138000c1c10003000b90046c0011941d444100050b41d4180c2104000802c0a407100602d0103803814001c0c079185101700c4c0c1120704c9000c150805c4ca82c070300601c084001540070145000f41c00c00c40c040d80c0c41d014526000d4503021620f40081d054407902440382d0601c007180d405095a60900c40c141c81c4407441c01d40680b06401e40314020640c460b42c50400500500f4050 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 768199217 1250 768197967 768197977
    0x12031f080a0b01050913061a0a0f080d081003061e0b040603200301060f0e04030e0f01200f0304082a090a1521020103061a0f0913050c0403030e030606060f 68
    0x101820700740780d10ba2680c447e4166072450001e02000c0d03104c2c42c030351074491600c80340080282c0b4143e4410b4205a10340302403e40e03138502110b07018041c040c0d024003103640485010341450207190004001c1c0f10b40300c810380303490406136480e404c080b00c0e551820480523100c0c6000d003e4501120340149200c21a035129008070794041764120740c607681c55941e410300003401c081d0a150407401498406000360305468030b81070160400c80300c800d20f030f445121203001c2e50302d5981c1c020b1802c0c03010150755007041c46000403480384549482d05031180d1700c0040c4008940018000300004840c0601c4d507060741000761410011100c01c0191201c01e1401d0390041c4001c2c0010407550084c1e00c003107801c1e003440d000c80074003980d20008403590001c043c0010100c051604041f10965030140140d00007066a06a00451f140221107424a50700403e020780865250000380f0300f04503900c009074400c000c1c502d41c40070400390500d80d4a0071529800f52204030049404082d00c8210391401140040c13240c607014003858607200030b04080c80c14079440 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 768200467 1250 768199217 768199231
    0x1404060e060910091a040b0d0e070e10090e010207121b0c0608011d010b030c0c0f10060e0c03060306070e0d0b07030204091d0307031112031f080a0b010509 68
    0xd1042a50541e111500f4454403a10f40d00c50040b00c40c00d01c1050603440c000b20007201c3d0100c0017004104401c3d4103800884101c0841c6d58400a000488141d26030300340703042588142c071a034800105100000341440400d03011640c0315807041000c8043c040d901800e0f40100000603041e0b0790010031820150340181d0700c4c48607041d0340000088924007a0ba548091801280d04910006040c640041c07040079000b0710600c0200148814860a80d0702d00002183d05d8840107200030103015021540c000600400c2010625081601d010b4500030703603120701c0030380050409101d210100b0032201c0c04a44140d41030b07800c1364043e000107009030400b5030340c59206403140c00c2e0701105c3c2a080703580184040c0c0411144110140200c0180d640541d40d035140000840946010749240304801d0500318810081510000031106131a9141c10444204005019070300e00304000e0f1019030070382c25000800c000b80301990302d03840d40c10102165441c00e10f0030f0302e654801e80e95030104d0800030b0002107403034018401071030700000c0c050340300103 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 768201717 1250 768200467 768200479
    0xa0b06070b0103112814030312180705060a0507060b13020d05090c1c1223070303140402010c141e010504021f050f090f04060e161404060e 61
    0x3030345684038003581000764000c3d1088800003404000a00d0a0700229074a00c0307030b4400b206118034000b1a005502c0001b0b01c18400410701000c6c040344552001d00030303900200b12400d2541a1840d0564024090b21030010a040703c900640c4404249881c0803000e46001c4c03852903030b41604104070f507510740d401000101e003000d030701807140108900180182d0004105940300701e1400300741c508000d00414600068403040c0b42c421070318007070284401d0f540642c070400e005030000c0304c401483c0c0711584107403404a100b030303420211030400c201c480d035000591000411030390781f082d5020000d050900a014291130b0040d00d0081c001030b40441104081854a440b06500350037007030956640403080307944172074803210030000b411503651560108000e500e0a982101812800c0005079007440c02c05100080c003900c6543c2c40c4261501c00456000b00584523002001d80e6008060010000d032920b580b9105400d4030100ca54100207103c807000300000364031640070312030707080f8034444205d0030117052040035034070000300c8800c46030010 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 768202967 1250 768201717 768201727
    0x20f19021002043f110f030105010b03012904060c0606050a0f0306060503030309060408030711120d0b0114090d020102101d06010e040503391614090a0b06 68
    0x1036603407005200404810142c401c4a10501e21030f0584d500d074034642d1400f003800403100303007040202c1161216102c135070200c4000c240c007840030000744c00068030700c041c5c58040d841c0c800040740340c4685000650507206480782000e4024443d0070a445001d09448600c45a84001c1c00b0070070801c1d0042012091f080c1c03041c0b80201d80f40d40c544001c15a4419076510250350b20302503030010024000c461180e980949016805540742d0324004102658600e800b801c02400c4000000c00121080c3c4140b0168252002c03040c20313290701c40e0204511b4082d0750401a498040c0300d1400c40d626050f58024114a40180007204503a400c2505007410030866000810b0103a05602031241c0c1d02248114500c1b40c00005003480380701c8001034043c551710ba440c3c004d050304100c056055000600000c01ca00006072135511030b42002c01c410002811442c4144400c0713600340020314030320b1001061501340c00810b0040c128210135480341c14065668090400c0e06075840700054100803507101003012503d29400402d14000054001c1e0720301 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 768204217 1250 768202967 768202993
    0xf0d061805122d0c100f1113031e0c0312080f04030f050d02090604080a1b03260f16021e09040809030307020d0605010e102403110c0c0310020f1902 65
    0x1020211103809a03180c0d4540e03407280c14035920f105403c0501c08076403420f07090512403010890118114000542a040035160841ca0007240010825119512407400d420003940c80c504005141075100dc241302040112000a0b410076440c00400d100c3e5415907507904030180004815034007980710018004045400b0400340c20140c9442000784020254100203140f14555030501182814110700c00040640c0700d1102000030554921080300c440191401c3c00e1490345088400c5510743c4251203e101e0344110101d43d00848085001103010001e0083e0b4951402c0000c64040b4200da54040e00050740c030980d0080401e0106900700041e200f516405411a8a130106940001c1da24030440b64013160301e2070701c400042c00005621119160807449504e1130908031410b0001d84507035140324100400304d000a11903442045403007a000406841c1c0303040c140c0c6507200b6801c0421a251060400b071a400381c45a14004050a011442103a00f038050b00d00d205420a105103995480d41c0301c02074000340c00c51107800080c07200 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 768205467 1250 768204217 768204223
    0x6011205070e1008010e1b0a0e1801030f020901091829040b07110a03050406050307020703150e2a0907020c100f080907140f0d061805122d0c 62
    0x110310404d443c0c1605962500700343d00c4181310000c010ba06040110340101810031401c00603240040418241100c41151810205140460142c440681c07128548000420300031424400300206000340c411508582c0c030ac0110b6030965070340000121400d482000c0d514040b0310034801409151b0803082054501000b40d00d400f920400c0265001c1c2c4515000c001403004807034203c030203c9541c00c0e1503c050182542203841c040d106000d1031068400744840000010155403081c460080a0340d440b144400340c580c1e0508035500180202c0c044140c0b80e200b000b00c0300451003030b000e00814901900d010100d100300122424004c2260f0301501c004107520600001004070740e00c281034074000300c180c3c0d50352080d10075080381c4c014030404000e0841603060f0003102e024403074880028a4120110801e0312408407900034603010900e01031440030007074802c51a0051135904405c00c1c1030710389240f9000b91704070f0301a4803240501405901c40c101040c80c04240d00b85414121075080c843d440754001400c0302c3d5904240700b2407200d0b81 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 768206717 1250 768205467 768205489
    0x4050d030b06041508070810031e06150801020c010c030b1f1110020304060c0c02131509090804050906060c191e0506070f090e0c0705120a050d1406011205070e 70
    0x1043e600410031946d80c2d0b00c6628030390f000c2d058540c0d80030781d18130395240c01412101c0c5102c0c41c8084440742c070b40d1100740916600510380120a84110801266030f50002038000c2d00107617040c518550908a214003580c0c468007c03507428800c0104004681d2401d400641200c408969050003403180111507004c80c0308082c404080724000d01e64002da6a4070b441c0c5001c1080341d511811490501c1094001400940c6405041c100b485412203000984e588079400142840001c660054003007900300310a100c01c00448a0141c011520195841e102c60384460701006640d028182c0c48140e42e0744107228801c0d40b01048500c40c040a401003c07070b080c45d1703203c03c114807040d907a05440c203440070360000301803100d080e0b032004c05442200382d18900280b0989c2004800030620502a00e03044248002242d0002402418010034511080006121343d6030601940302902a070480b071b000740360143c43c241106440300c240c4401c5a1003618144e407035000c3c0d1003009a03030078001c1001500d440200700044001d1611529800790b014 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 768207967 1250 768206717 768206759
    0x130303150603052a030a050403031d0709050723071b120b06040c1d0a090204032006070c030b25020f1c0f11100203070c05010c030504050d030b0604 65
    0x1c50940b40c0420030414200341e11344084403191901c4100e488003400341c03094a42020001c000070445445d2800c0480c043d080d13080200a68040042041019420000d044412651440024040e80e56035100c00c5d24440c03291100004106650100080c0b00d5240b0030041c0801407064846010502d804c1c01d114444828036000008100c8541448105100501c0342c1c0551158044a0501c0960303000d000040541d040d44034103540000b4842c00300c0146948a80300103010b0a4a0b00e82103440b0b558909160150104090141a03c07600c09050700015051210072070303904a400483c0070084911710b50300c1060105004000b110f02000d50032800d102104d6009040c2488440c2d68003c265003c1140e44460606036401180000d0000064419036001c0c0c2058201e4038003c0703203042c010005000e0780140d6007450003109507901c82610008c200041c4c550030020040400703029000800c41c1484070341003981110000c1c1c401a0a80d40000440021148039030040b41c0300c0302e0050030490415a035410900083e18400b4084 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 768209217 1250 768207967 768207971
    0x1707120302010e03040b120609040c09090609140d090b0909010314160312270608131a040309050303031e090c090c090114070f061a0d0311011a09130303150603 70
    0x7c1e00340b002d0411543c0146088032407a0443c1001d90702c40038008140d01c62500c1d07007a00c5406034410b00501d03612142c0d9072900400440c040140d03c0c1c00c120340b00c0d039003001f085004c00e00010340803640801e400c0c1943c2030b0340e10144c44100c550b420350300d6130b250083c060014402075110700d40400d048809036820380304c021442540340652a036a101005480e1100c0806a09411341c5840f0043e42e02c0304600704900f0807244070341070141c0d042d05e03140001c0405c0001c40300c0c0070341480103a5005c0502030f01c0480f1400d110302d000390744408180d43c0b03500404d504d0744010758090028540e524002829485815107940d000b0009404441c1d80100b24004141e00100854943c035201c0d13008a00c000d22540c120140380300c2186161100743c41c2c4201c80d914144507080095010380030b20341d1000c1c4542c4110103140218801c4100400b40344a41d441890b00504810092459009075424038425940518052041001d80040149200b0859803065044140788404e55426000c00d03417151503040b81d19804000f080d025100d140c0d00 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 768210467 1250 768209217 768209227
    0xc0305090108060f10210e0703060f060e1006090e07080f0718030506091006030f06050601090504020d0203070e0a050307061202040e0106051801020c060a03180507120c1707120302010e03040b 84
    0x480c5d01406c40c2180b40303801103040595142028001140701002e40f644900700003004441003031650024036041e04446215070300c000600000f040158100c0007110755030390b0b0340d240d596103c0500180d20003003a101540852800e1000c1840d040c07880d46800e61120051030540102403c8484c0070745011400c2c1e00503200b81d0031200501c0300c400400d200b001c5801c20714003400c0c4840c615503900c07403214480401e07000d00415551008224079a1042405e0b000620340244295111000e81c001c1e58005e500558481c0b000c2541050100b81504102e40d10000307c4100401a18185140c8103050383c1d401460785128072000d41c2000301040001442c0c51040c040e043c41d940742501c4003082d2200c0c0c1c003002110921141554000c0c1d01d4207100d1b03a500d00440d0b080c10164030340401c3d41d01d01c7d030000c200a88480031004207940179600c030115030980715141e043c00c51801101665006941c070708110300036520171070310f54100d078019000a0080310300c0040000300c171314460b100011740501d03000b5415046400c07e0300080244240064 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 768211717 1250 768210467 768210497
    0x170723041406030105181801021209011802150c010216030206040302070f0f150c0212100b0406180b0604150c020916120c0c0c090204150c0305090108060f10 69
    0x20803181c0400c0c06544991a41d410040041c1c0d01c8140b0304007100601041c41c000400c1c2421410580302a00c15030340c0299255200190f14840e0070700d044170351945c2e039868010390702680c003041440c43c59550f401038011000705009101d070144640c020900c080080d9020800516013402d421106d00c4e4a038082d50103400c5a04003881d0003410a0040e80c0442c0c907000c0400e409110035290003046000311001c94150800d241007040c0f007910a102404000382d4065032000400061a00c0820543c0c0d1030200f456082201c00e03041d100b00411100940151030074854a0092422540c600364450260007800902c21824613030740c1e00c4008007021000442c2c00000b81041600000c600b0302907c070740e40282c44501080544400340c031380140409840b10145140076210b0030510b46007409030030601207190300f14810000351601e851142019500510540d0901c102c0b220070780501c50b210382400c2501c958140d41305882d000700f4800445c0d941c0e00c041c0415500240360001c10070705560729140d50040a507582c40d0314051500d050 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 768212967 1250 768211717 768211739
    0x31502030412050a0504061817010f0b010507031b02013b06070b1605041701020919060503010e0a110a020a020a090b06121e1e060105040617072304 65
    0x40348038010701a091003c0c2c4c003c903402c40292070640399203140c035038418441141c054009008d40d0b403201e12005a2402c1901072260190041d440c0c2590f166401c1c0304417042840111054801d001c0d000d400500b03600c09405076402c124550611080c014074108802e00d0740c010f80145407251100c947c20743c14103030600c60920340b4800c903803250b640001203a210703040000c40e80b20002d142c1001400e2684403100e840c84842d10790f00540a4401412504080000307400c80c0c8904039000354041544188510f01100310f4050b416002001401951345030341d038107405c1da4a00080e07136201c0000034008020040c1c5403520380c5840c1142c0c201800c0c143c195030380140b60300c01050041c011a4031541e04152907050800408400544a00b42101c100c8550080c18212954071203000b0f031a10311001c1d02c4a020b00e210a0b0038400c80150382403140d8140ea43c0c01c074012000391603000064a484c440e600c60f0308046010070300b081d10700f120300c0014150312071001e0030081005903407000c240c0c08054100449000705a80801d06101030390401e = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 768214217 1250 768212967 768212993
    0x2a020601140a090506010c200f04050124091d0106080906040c051002150f04050f0c091308070203011104090f02071509050f0d0906030e06071202090402040315020304 73
    0x5140107240c0048030300042290401d080c0141c0451903100c8011a11591185c08a00d010a8001500c01c0400109420040e400724882d000144140d40c480e010301440e141a20419049401404084400081218001520044e030903150014400d40e4440000c00070281e8160103400c400c00a0b41092540c1840f101515002e005012480303e9802503007000000b40034035850030240c807801c988602c04d000514404900d03100b18814400c16601c002c0090140d0500240080c50140d4414001d40e507001511240301e0f03507100c280c8004141e000440303801240042c2140c01604000d0360003030518910b0000107802003801c4d240100c5540705240000107040004500c903220744101082055000d500d0034910380c030340300003440d50400b440e01d1550703803034180034204070082007128080f072103110566090821201018042c07000521803800443d04110003c2e402c1c100200e42c1c14896003a60302e40841d11681c03610214000c0d00700d61081900994200004801301310110401034100291720001340c0d81c4c0c40c19260081c0d480400b = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 768215467 1250 768214217 768214229
    0x2a030408061e070c0210140d1b030b0315062e020f07051914030705031e01230f04110406030c03060b010c03090306050910020307030b010921060e012a020601 69
    0x5122034600142c3e540c05186c00384000c04e140074020041058500d00c02c0b8820070795540d00040c40c286060000c03182c0032443e040c4000c0716460801c81220a0402c0c184c540c0141c2015141900c10400041c96510340200820500c0c180c009014460707074071100c04480b200603076616a0300036a1003030982c81c0c80c50404200d490082c04090754a00c18404120b0b900c040a1b5802d402840001e40281441100b9920100a101d0040c00d0007011603030317014800e480b80c8440c0c1000c07080302c030b02c10b50030058074038076518604a038803001181c115038440319541c900c401d2400c001c002500031a40d01340f22a0740b1000703a0755180641c0000d1070098201e000136a2440c6080d0003103454018a0074180400a05d4642c007090b0014140d00c02c4a07000540850680c0d00e080f07103d4101008186243e490902c04001d01c030003a545540941d2641000303880d00b18807240c86d10524980115507071081184c080000703203441c0c0003c00c140c03c4184925404030000c0f5842e4002102e0881940c031404882140c10141c0d40f01d600706690400985006200c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 768216717 1250 768215467 768215477
    0xe09060a02041a0705030c0a0b0f0c0412152a0206010f050102030a0c050a05030714010c02060420010c05060406151403030a050a0c15051b2a030408061e07 68
    0x45040520300000e0f50944003102c1d45080410386006010003441280c4604c400319040d80d9004a00e0714154041a400352480d100404d8103100007601040321008032400d5a007004802c0c86109000d65415403010030700c7c841d134031203e82c40313403503050720720b560966101c0000001d00440f15841c043c4c03003002841c0c000143d10400400350095810082030343c02100b210030f500362500e41208181d0180c20f00794582600420000d0031403000141010034030070062000f0044980d80c0000b40803103d040c03581266148401e0f100500403184e4080203030780e90035034404404101e01d410b05100c042c1c0c1e592911000e040c08001c0350180d425540300c60f00000300c400c2d09001040a000140c0d00d041204e41d140c00803c0c0e490242081040a1140001c2d1030008540600c10108d240343c1d005001d1a00c2101071240e08000c3c0c9002d440b40301e02502211920191180d810082c0c2d0820814001202c60b4903180c0303e03210326403070040000c0042c070340420400400d030341d0760a100440c421082e15008081c080380100c4003050800d4001c0c0400c080103 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 768217967 1250 768216717 768216719
    0x81209151c0501170c0d021f021c03021b011a13231608010303050304121b03210204050913060b060a021b090420150408010f18020a17160e09060a0204 66
    0xe88c91880c064054952004c004107104098101a894840c0001c1d48810481010159000c1c181d0700d50001c2104203d0b8480307d40106040a50240c269408083e250f10142c03e6414481d4003030415080c1045074003072002300031460503820381d81e83c8854143c92060f8619100340c0390801c5000401004409c0380100c0354035000c0015892f544004050b8000600014094110760f6401501c80380300d613103801c3c0c83c006c00b0400f000d5501d40a20303004e0410903004407144040070090b01c818503100084d01c250703000c560001d040c0003496542c900c1c0100082c0044442141c3ea203a4558000d405501e909000d00034044080e001000d0304140222107000c401ea4140159102d138103d80200400140b80140b0314210200521140d8520043d000004d22002e2005030f981c8030364400450b0004002d241500302c118171654040d0304020b0000302d182022800140200040d402812021003002800b05280215a071240e00c142590600380ba069150361410245500c001045801d4005124a001c4103000950700080d0b070340011807402e = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 768219217 1250 768217967 768217969
    0x51e151c020a0e280f1802030609010507051803030c01060f03052b0503130813031a040c05192402010b030d0e101b0309081209151c0501170c0d02 64
    0x4200341d140f203041003c13054801510000b407034102880800c007440c41481541041c540244d600340000c501640300344942d0020030102d80d0188110f90080c80759540e45c2c0d2603c03800c480034001c81012541140e42504c410030510703c68034020310403080905200003101d0240c500d1410003615001c640b141d0f03081101c8258018040c140c403040142600412103040194480d40c0f40140e40704075190f02000508081c01c005107514404041070103d006603441442c0340980d07100d06184071800d585044a0041c0803080d25039051001d8600101c41d280290100000441c1140d2100200415000354022403504480d0f074540070380d41241c0a014601c9120b900b5401030002c000711900c020001503000800307500500902d44d1404000d84520207000c11100c21883c4401e070340382e0f9842c00a00e0b100c80c0340305080f40c5006492102014540c60004c44480320b0004081142c4000040040800340c1c5c411500c00a524500d407500e43c1f022070fa94040e141c024034442409180031030414a50714101244045050702c58500c0364015001 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 768220467 1250 768219217 768219241
    0xa051002030601171f06020619060806420a06020d0801031115030f1e0112030f0e0d14010c030e1513140c0a09051e151c020a0e 56
    0x1051014403251389a203a03a8516030600c042c2140a815003900d40f500400d4054002070800e02503804000110311f10361002103c02d086600500418400d5040b80700491a2000703410b224810841c42c1e17100d01501244800604400744501101e003041e0340741c94402c1c4810614120f8004c0307006050f0341c005403640c1070040c1c50090204005010082180c41c0490704540c0300d80b90303010110a840312612200f9680d0401401482015408603100040d140780c4480d2514040c138084a480d0407a5800007841030504e4184e45e00b503c02240700d140820801407603a204c015103960303400c0051039031402050305401c0b5402030340c20103080d140a40721030414941080c0c44800d21080000e2642c04506440f02514211f40f140c2d000c110840301003001c040d04000e4401000da5441f0b0300468140c05412084801c980029600c440000c00e44100300c0d1000421004540c003e031500901e04c804951050410b90360856011428000903c0b148406505407683c4010310740c41021424402a014050704500310401902e160250070010 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 768221717 1250 768220467 768220487
    0x1050108042004021209060a060605032d0a140108060c07240203100801051f050415050a0b0d0f090503072918100b090c1315020a051002030601 63
    0x2e400c00c4076440e48010301c01e24015400e92000140290b644009200c8200c03a540401d0300e07110f02c0d40c00341001261441134144603107002c4550304d865032410b540d06e12140c4400b0500c040480300c00e00174034482c402d11030768110300201d00c42e041104002480d00121092000c84510507004811113510180c20302c00010480025100b07981c1d4070005c002c01495144407109100149020640d2002d070010050141305018403c080040c1c48041c1c00030045a695000c3c01241440130300a1002800055201480641802d420084c1004034503c420b200700c6a03501c020131501c00b2036a00549424401090808074a1850b02400f6845211a0810b021210740ca4a60b652039214884009280d029400f40780f082c5050402c07001d050300c1841c07071003002007450045420034415110642e0984103003c5c49040b00001a901e1088400d600d0300600700b00c502d40c0d40c02030034000660285d031007400600b030345000009407e50402c1c0a46100640307079029000c2400640340c05483c20141250300c0790f501d80180704121059a00841034a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 768222967 1250 768221717 768221723
    0x20c010515013507020106060f0c08040311030c1f03110c0304090b12031210051206070503060103091e050c0d110f13090b0103020f04061409060303090a0e1e0105010804 74
    0x328002c420b581e407103480982c3c8800c02448000140100082c00c0d4040d400b400886030035880f5100740d42c00c4a901290f01d4100c061000380190014081400440c80c0d03408035000903800a811500c0c0a01048002100c048410740034050074010b030300340d1981823a414058011a40c0110660314289005525100e41f6400749014400f201035542c00c03000650b540700d480100b603540610090b03c0c1c1d00c41d140f5884000c1100c01b2550011078110005001541d820000e19400e0038002900250090b40c88441c0115003c0d403002e0119810140c4074540c90000c60305901402c1002024122400c0094645151190400c0000b03010140b1680c800c501504c049030078440038891220084030ba0703660044114000a26a09224000800041c900b40002040001040c0360303505a0f4001c59000341e00001d00301c1000300342c80c494000c020301c900e910403082050303051020701a900800000d040d81d0514044501203190341d0740da40d12410030001e590081c042e013100040c05c0e40302180340342d08600d10f0075810540003800c14031010b8401 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 768224217 1250 768222967 768223007
    0x40624080604060b150d06062d0309030201020d0212041104020903060a2007111315030206090a15080708090a0b0402010c051002030a0207020109050301050103170d02070b0a020c01051501 82
    0x110007550b8008400499059500c01340340ca86d2501e29a05000302030038011344000c0b074003420074089090800f110504c1040500b9412001101a014084002c0d0003e90021015990240030546a24030300d80041c100c00c00c1c078421201e0710784c40c03d41000d100c10000042402e00070780c410022130841e0385011441c03036400801144040b41000f040c40501d41080079942c003091a5400c00b2030b28400300100c036007610b001c0c1c10003115801e0022a210010300221030104003e4440e03006900b1080006040c01005440301010040a000c5256a14001c5c01160099514048001103144c4108004183c11000550700444040010301030441942c2d61291504800b80c0b010341841580c684901c1000381c00c00401c039403031090100c01d64030381c240300341c265001e904032a4040b800303d031a000e400710301420144500f904030fa40000c140c4002c030401c010300701d507550700150110b200303a0f800b00500d0004c50414801d0a02440c207001e001651080140b0400d42181d40241074900610742c14015072000740e9010042c00c01c0ca280600c84 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 768225467 1250 768224217 768224231
    0x1527090f050618040f0c031a040201020f0706051c020409090f0210110a0602280e01020d02012a1101050c07110f01020c0603060402071410050705271804062408060406 73
    0x40851420107031f00062410782c40e0140d44032038280600388603000c2c0d4800e07000c030f6460100d0b0941c03d988505882c0a00c0000900601010325030580c1301e0004002441608001450706460f0041c100941d880c407102902c0c1d05454413a04400c40c00c01141c1013118018524050200c0ba050500300c5841d0f01111101a00454001c2480d0240206150078010b031030503905a0198405035100340035080d600d114261780d01500a040814640c580180035034000c4020841d004000b0f41614000701305c0d0900d0000140c400c209200e103d50442c20400d2084a000b200700000543c0c1b29039140c68500f05584590103590b009004040840000ea6000203600602c48000c0b10300c03d84a540380c0011400a010345400602450441c0d40416805480410407106003030340b0355000d01c881d07a541082501c1f58450320b058007494031a850700400c0800c1d0311b000f00c0054070b8002002c4c3c0c248092446105007600100399020f60350a031740da08009144210301200055442021806075030458980300c10541c803500001d00184c226138a41a07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 768226717 1250 768225467 768225473
    0x10e0f190213050616060507171803070f05070f0506120411120d110607091a030a200a031505010207030b06030c040c020d12061527090f050618040f 65
    0x681000607083c0134003415119100c01c0303006100d080101809880103450040411601c80c170400c40b0008003c00f8101e01d200b151a0003403c405825043c2c42500301070f0105000304000a00c3d146081d40159003c0d40c0200b4400341007112603117490345030350300c200e1080c181081104260414807644030350240e00b01035015a000f0700740c0c01044204412280d40c603494040c10701818401c68120704800b20007030400e002c542c410fa55410054540240900a41214032200d011b1580d00380802c070300840d0310510500f00454060744100c81a40752030410040203002c00c0d0045007429103282c2c90b1041c000e807484040c00052007030b4500030003c2c1d1249101e00028094554210004072641c0342000038086012001c2c2042000340010080292140d152450300400200f0721000902406200d01402c0e0640f052405c1e14007a9100340b1000f5508903c0003071807800c81402c0c200c3c011495408004041005290201c00450140508074844084540042c241e5200b021090750301803084c4445501168803c2d404440840c44040d641 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 768227967 1250 768226717 768226747
    0x608070e0f0a08010f0609020f031b070c152316080702100804031709030306040b03101416030e0c120709050c04091a0d0b061c0506010e0f1902 63
    0x900c142c1c0141c241036000506500540c0701ea52640c6140504000c0f40d9103407034840090b442504690002807200f44040780b104018001c44001046400b040c040c5000060750f98034299001c0c9510405440b02181100e2130519003000d200f0152103880341110150440b60180102c0a000d04040361006188000214081201d080300307e60040343c0081c02c3c001c00456200005001031012181100040c00c4c0307102c01c0440b24070b004010382c018680e14015504560310203050000030100c0740d5549a0512402142c9842c440d4288180110940440345405040c40c0c0340401c2b000c80c089414400040610b014210200c800d004503801e5106001100c0c80d6000d00c0b000020980f4180303194101901c49498102400510f0b40c8010003031046a507501824400d040781500070740c203d02c01c0d0b41121070300040c00d10407000014406090207a445003000f000e501c40c1c1c0d0307440e40c0c1041a22007940021500c0754400790041c0311061141c00c0d003a601071800318841c442031404510b10501c0c10350044000014640101e25000604800c07 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 768229217 1250 768227967 768227989
    0x60e161a0c2d0f03030a050c0405040c08240a0b07020d1b0915032a1a031807060c06090303060b0f07020f0105090105120a02041511070e010608070e 65
    0x41d021259040460580041001003046400201c0840c4200e2200146804074244403604100c10296045980300710340324021700390081c84c102048404200100d05690f40b442200c0c00c090065542002e030b840c00c1d03003d48004801c5880d8840744060000280341e030b90303031b03410241030150b42c0009500c6440b0200ca2010850302c20480c90020b013005141540c209048051000302d40031a2401d0340e05202d060a0380e0062024401c4074000035108d03200607180511800800140c24501401c5031030700e007045903515141c10328940e1120950000c952000024800c071402440303800e00803c903d0b1006000b9045c54008050500c1c112548000c003000d03180d01c0c40801341400303076008500030942c2c800e038103039241224210742416500c5004101d2080c500d5951b21a869446903064891001c01a119145007000102410034940300050003850340366000c01020032050020001c000703a16580e034482500d0b0100d0742c840681001516000701411034041c0004100450307102c1d14041d08181d032030404443c0340c1389010120310000c100c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 768230467 1250 768229217 768229237
    0x906020705060403020607020709290d050f1f15030f0507030b15040e06100b1b010f0501050306010605190c060b1005032e0e09210304060e161a 63
    0x40c2d800704001d154001c12040d10030101c0743c0c00d1317812041d02d400b1241b0440e0b07030481514441c4401c65a01d41031900c540103c030780c01c0741c000520300c07040c1c140241d032800c5c40c3c81c92091508011790072403128804460b60340350300c4c8030038560007403414041d2015400c00c42c051681c0c40e100141400700c1740204801401424011600070310b40103603c6070500d280c0300d0b40140d02a8001c1054034092031820160804100c40070904600850800360300d540c6142c900301d91781c119074002c0704000904114800c0c0e04a4070302e000344580890780010340e50204030307503240004241c20100141d1080c0f0600204000c1110849400d600c0700010300b11504203240c89100d02d0900000a0403850742860b00981c2844003a0b07072464020019501c0f44000303291400c41400c00e20411801c0e0001c500100c01c4031442d80e1710034000303007160712002c0750300039000c008884081d0200c0302d4103030004000400584030340398000103010601005010390502d90110100801c81e0b55041414920003081c107100d0b6101042c0141091000c0f40302a004071451102 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 768231717 1250 768230467 768230473
    0x120c35040611041d160c0209010509061305150328021509120f01290d03110303010b040905070504030812071b0606170a0c14010201060312080411091006030906020705 73
    0x40305002d02490080a482040340300c5c2c0b000010085641c8901c00710403a007540035000b554240d10381010b0102d03280e4040c000740e070701110304001c80d0800c1c11a0301c10300d8449ca24070090300740700d40320f0315040c103040402c0c020345900380d44130003500c031580f1854002c00c002034240c6c140d03540500020307404100d005038090500820780c86880807a07007503003c00d400a10200003040782002040044070001034002484407402c02c682e01904c2e0144a8640c5252003000107007254024204551038458080b906030039039000f40c02442a0040210f01881440c1051185a43c040756130300344686024210346490001c0d021760b4210010b0481c1580004806910402166a84d1010303807072600364000d020b24080003c0c00040c0510329400c020030100140c1c1d003400003941400c2c150092050030006040c0201410000d140c0100c0318150b6484000000000d000606102050351490791015134a042a00d800b040c0d01c078400304a144942071101c144004080310b502000c0445401e0b081c000351a4260f40f0300000030b40205540505940 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 768232967 1250 768231717 768231749
    0x90706050d0b04110a030f0501060e090606090a0803030702160605030606130801050a0905100603020d03110a150509061014060d093c030207030210120c3504061104 72
    0x13402c00604842c4000d51414010600c8281583c011140300340301c0e0000144842c4070502c85070030118005500044090081894140c01d440807809040c030b15400b0200031350000040002d0154103001c810418090652015103891030250001c0c42804040d00a1b03118810001e03c1095050302034031184001c20340340c4002d004520b0401c0921000340488030042e100c6015074101c00809100503c210b00559034000c1840400000c0342d24212902da400d584101d8940c461111094045160458041c200c2c00112001003800c0c40c0c1100d80390706085020707210300020b5140580511808101c1c03001c0400f2944107940b000e854240e222600d90280440440113084079a4440140c0f1020741381609a47c0742052840b40345a42e90000200003002101c001405401a049003a080c001803814152550300100d003880c020300c594844c882c50400f140d0030700521401042c1074103107050843d0000e00e050129412182080d295031402c6824104100400800040c0000e669411100420000d070041d00c0140207044811a142 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 768234217 1250 768232967 768232991
    0x20a060507050a1701121407030b04150b040b0f04050a0b040f0204050a06050307091802040302191403030c030f0903030f1b100e0c04090312181a090706050d0b04 71
    0x5a4400010000001c10500c4c611202e040c03144e2119040341c8107070240d01c0e0068101c1e1281e91500c00710b8180c9004c0d074010801c0c004045400701c2c0c1d0b19401203001e0580842d48000710001d002c1200e5000340e00b01c1c0101d042c544002c14540c0c5819662102d94016107000c211030341ca00010f90010b005171848070364840e203818a9407181170915405807090b21420380e52904c40c0c940720002968140400c840c81d0b03000490300c40c0c0a0000b440704000341c40304103c5001000d4245503d0780d001509500c20800c68500104a07110100600d10640ca0920034043c03060f0003442c40d2083c941d40c3d1540b80d22810f62000c3d8000e500040051280e1030420803142c82041c0245419110203040142034141e800030140e103801841032070b90021590010307101d030700c1220680c88000d04410181c102404013030700c2d00e09002c0e42440065050038040c0c0c007050042021520039092680c94804192604202d400c03000d2036071024004c0260b00304000d4401c0054050242c0d1000d091254035001c01c00c1d05030003d041061a036581003400c1003555008 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 768235467 1250 768234217 768234227
    0x3130608160809030f07060908040603050604110f0a08180a0803180102040506070204150302060d2a051b0f0d0f0f0e061909050307030506011706060a0b0a020a060507 73
    0xd0400400321916031605410100e0b40880b09881c080040d804c04c001d4a00040040b034000d00300107105810101d0108107039200c00c0c1d42e640281d48150046502e403010890341c0d240030308c1a15143e11481581d00d05050114017105038900801d400c88082c800c0c11070100b00c54000000902c074000d00e14008846202c0d4540c5825074182c0c2099074000301c00c0e4429152060f144506000f503609680c0302401c040c0c2441d5507a005c000190080c0302100f214400500404070168807044000c00560b843da407808904500c1079020401201080408a080741c103460110081c1603030300070220b0b890403251010740040710301c0341416142010001440d0242034481d2100c3c0818040d040f0a00744000c07c419114100c0d45a2209010350704400190501940440100140e5454084450311819541c001d0710f001c1c1c4080e625403000c0791410303c20741c009407070907030100c00100640e80ca0b2580f1807440c9038125020388014186180032403d0040e0500070050440e0002c44c111481c02c2c406c1150008060300490b09002074200504040c1c0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 768236717 1250 768235467 768235471
    0x9020102060907080607120e0601151d150a05160c05101106180a15020910050421020607020607030c03090504020705062e030b2d070f0203130608 64
    0x400341c018000007440c44400410440700b102d00d0f0401414956a800c08216805000e060f6001c2030142e03070300c240540b01d050401c5158040c0c51110b2007561a0354119002401005c54100d4640c0c21460806c42c4030304135160055412501710b51031002340c1d203035040707604142c40b00d010b03c00521002d00b40c0c48000e4000c1c0811003003000110b80d020344400d0040d07103026004070380450041580a9559220401082003129824480780b500d4481405490807190165980c07c100310b1070413a400030194001c2020301c002d14010014801c6d200c51810510700d080d1600020311561f41181c00d142209103000000704042d911460110350080c0d9004103416075070045d601c0d01a120044e0300350283c0000b8110703500030416050610071101001d800200034065641c489200d40f052022025500680c5201c401541d0300b803d40410416000d98499054002185005016000400100400c2c60003290404010313240408001e200d1941020036480c1c180e42a511b150000c2e403940c40741054076840100c0020001032415401030b4101c3c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 768237967 1250 768236717 768236719
    0x30510062102360703020406020a0f030e1207080c030102160303231303020708030903100b1203130e090d050f09040b034227060a0b01030e0601210c0807090902 70
    0x1d80394960a804030301b00d008501034803015034043d4442001040c030182400381024031a00d0400100d00142c404100c5400c441103840c0b81a41c00346009200100081c8403003215103e00f54002c40c00c005d00c400030802100600400a000d26560b4094411421490382c0c20b55811405201d201c1c0c83e90502c1c070300030074181c1c400300020790050003076040110710848003104442030300100070010007846004514a100401c0410070855101c1080010600b90071000d2000d0869082030b00daa80035440d250119010f81d0391402040c1c00d4158200c0c138410706141c1d41003804c2d5005000026001c41e1111040b0f004100201400c1074019450321401c0d0714083c04000c024000081c074042200448024044906035200f101a1340f20200c100c10410000100c0c59060300081804044032140501030300d803281e0700124208001907401d5032185403030b01da0050407941c01d400381442c1c0039910001880c2940c0352030490700c2070007200d10540607890100400001800182d030320440c0134091907030645810303d40d03440c440c000030409000d0072 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 768239217 1250 768237967 768238069
    0x702030d0c170f040c0b0c0c0907081e16050a030b0a170120030705030402221d0303040515130204050f100b0f040e040303060e10030510062102 63
    0x90043c0845002940100d42c0701070802003a40c1810b40002186c3c108140d031414501c104802203004d5950344212a010700880d03100d019039410403c030300c0da800760b004000000f107101b45003007800016401c81c111110b180340e003840c001da00c07241c00341c400f2000b510452074003d9000d84401004681d07804920f0789000002e81110007000b503040040c0e1704900c021242e200840302c1d11424070000e95814040e60080d0341c840d00c0103100c0140c0803541d13442048607071042025203049030360b034130080003c1080802543c441001100000c5043d8542036640356602c03801010600810301241000c0340c1c5850507034840c0348040b82d00030814822890082d0440f00c84843c1107a440c40c108141c0480000c45005000c2115541c0d40c01c44004e0385442d040490401d411980504201d007056600c10000480c4101d204e41c09004520102011010710b2450400350328000c410303c5190021450107208000c4815412071840b0607a12048402a0404041c00000d00d00c131005542200100e2994030303016450890784040c00b801d80862012 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 768240467 1250 768239217 768239221
    0x108071b120f0e011209050309120601141c060b03121c05150d0b190e030901170106090e10350a0210030e0703060f0c121802090702030d0c17 62
    0x840f050391203180768038041581e2071100c2030401015080200780078012406c8070328041e6654081423100c0c044031a0320030941c0044006110300341700380c407040d44415000c4690307140f02101001e215603050010034000300030303a545101400c01a202407000660050102d0b00d0681c40714082d0710342c01e46082661490807105481c1100284010000544020306100c010741685500d081c10b43c0c0e4180c81100c00741c41c55150740c44201041031400d245000344494000382d40040e40d103801d031040026119517240b4001001c42441e01c0d0051207460343c0840c00804507003040082c40c4180e25001a85042d441c050b4211011001c086040e0049034814001001890031544181031580e0f000030b1109606c030030950100070b40c402c1c00030b08050803607846034001410700600c590a84000d940d0b2a40c1780c000b241e10382161603030100c0d29a2000d210303035900001583c5409525460600c1804ca40000080c481e0b25030080003449121001e0100c3c1d140343c030070002d440a144412400300044038041c80c01030400c90202c003c140300e6402d1040 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 768241717 1250 768240467 768240497
    0xa05040501020c0a15080c0705010f020909070c1e03050f040e040c0f180c050909090c01030e01090803041e2a0b0901090311120303040f2108060108071b12 68
    0x44e0310303000c071100c242d500205041c1402c011100c521001c2c00c20492104107010038000b25200388655500c10340810401662604040140180307080010300c4101804440d881920100f08501d040504004001342c00340400390451600751114011103c50060501c400b1401089044013210740d24051801a07501014243d620f86d4051001c501038025078203580300350285030700c000103540c101415108441c28420708125078000800c040b981d0841d5200c580b9803002a4520840d40c15201d0f200c0554403510003444880c041d5182c200c0c0e82d00c4090002000305901a80c404010001c0044803000c0681c0540d510700ba00c07114165070b400c0c03498501002101415002d40024002000c041114680241a159103003030518507200c14510840c8000002d8020710000ca0b4000a00001d20007144114403603141104c0d420310310b0074030b041485060700f44134032051548e01e54030480581080a145e403000d0240392803603180d503407c41d081b21031aa03820f0b00c404049240c000c0c15030070030185505204140c01d007607445500200241c0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 768242967 1250 768241717 768241729
    0x3010e0a08120c04171b0a0b03060d080408060106030608150906040b0c19030608100204050117060a0506030c0c0d03150b030c04121401060806060f0907090504020a05040501020c 78
    0x180d03005100c0c110801c42c480019000000180d4008244100181400d989110003c442030014003114000c1d08108041d010b185003880c40654002c0c001c0c2e40d52603415051031b0001a083c840a00640d109090b01c041080c20012940c0c00c503005040765405442003941e45040140141c58a40240b1131f580c043d5035180a1040d00740c44440d88904c0211005003026220354461001c4184060060b48200e04200030400c0300c1c038606414800b859045660010703c1c0c0c0d15184003141001c5503e111100b05a0040100300400c0e80d00c00c031103003110b40b550010000603071070700e20000d004406158440c5420031808820000480e0340d030405030402861507001d460342d68410312011000c40b0204074401f0f80f42da6091105110f0b458003440915070001c21038001d14546511131a4004455a0f84901100d8503030200d0618502c0c01801c2c01014024205203004060310f00b016000140e01000d00c0d001c06010784201d5001a0b400b602c661041c0008220241c030855a41000319402021a4081d000701c074054491140c0b600d025040c41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 768244217 1250 768242967 768242983
    0x601090207020604141519080603010c0e22060b070308090c01080a09030c020a0308040614130302040e03190e10080c0a05161a0a0c0513030b0a2903010e 67
    0x28542807410b4242070401800c400c000c94402e4124401ca1211b4851103041002020744140610b81703104403100201c00201080c41c0246614000c0c0d0600c401603a40c0c1d078118900150720842203800340103031041040014030202c8141085501c40303042000001e440c04903440144183d600a0340d0b80300300390f69005101580c0e100060f690900003101800011341e40700460340062003591007483c0c0180d0f41c51551700041d0305010140c100b601e04c04400103041114a400c4281800198042d1003690b0606400c074841000040044c4406406251a0141541344020074030403030310103146802d0b80e402001c281c0c18008100300710214109004901c1d0307010b10280d0a000c7e11456210309d0305016001d2405443c0d44044a003074008511783c03150003c40d00202c00000e5168071034010300b24401b801074101890010514001d03101c2c4510b681cdc3c1400390030415060311071403200c0200196078005c0000c1c58a5141c200081000300500300e82081180d548031900420b041e40c0c9508100c1d6480100c0007072200c0580e614010f610b07001d0b8 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 768245467 1250 768244217 768244219
    0x2090f040903140a120203010f06020118050d0e0103021b070924090b040e030c24040b04060903020304180e010506010306051c080d05040317070207151b0206070b0108060109020702 79
    0xc004142480c800f1039000900c0341da1110310344169117400c600030980690b002031700450388802140b402400225030902c02c450201d030b0f09841d41000c4114a03100d0321f0301c0da088050a48200202c540707190680b42d0080e01200c541d000e813100716034910943c0e001d200e03844010501907030550318181a20b03d02c40381d40c00c0031900d19208001000191040c0740013444401010480d0300c640d0070503100c2c1c0401c1c181c08014400b074400036480c4030103884801030722030300302d4642405e414040c54031290600c240804100042050b90b4000d40c041c500007841a00ca00307040c1d00d940616800f0402c2c5a400310180b1103961440c0e0806180185000028031894441200540039034010703000e0240c1003031040820b066803ca40310031901d07005000d2580c0b180303448084510f440603200120b070190003162041001400d203c07584401e00c7e81c403030501e1000c0d000c014185180303a400c8141c42100c02c2c3c20010000000744040c1c0383c4242c0720f000d850b0b00418066480c110340c0340141b1194024424400326001e0b25000098041e40c81c000c848025178 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 768246717 1250 768245467 768245477
    0xa0e030901030504020f060403030801090e07231809070f0e0105030619060b1201051c020102250e27010b03031b010b0a0e060a05010201290d120302090f040903 70
    0x24403900114014440100180e9104207000c02203a015240c4500500140d40a07640300e08023981465039840c10303203013004c09207400b540c4015001c001141e51f1192025100010040710000252020005000d1151544148460f201110140704e1100c8000a1070b00840b460301c41c1e44d1171590f6139026203003900d00c000d1180d650583c00150000b107004291071341104101c00c880f000051040d0701c4010f030780441c2c0c202680c005074800c100070040c071803441c001d5008980001c007103040201c24840d9600003500c40308a2010b0b10520503a03000e045c054122203001ea100648405416027586180c071140f50841144460154844485020141192000e043c000c424200e20007070006c600d01407405241083e81a91201c810280355078071100c04800d696120404801003c4090605446090000420a120802c0d602c91419a89403001c241e1046042e440c0201a1703101660800e807608001d1000b1403181151000020003140082c41010545a01507000c0e0503040b805541f00241030701004148412034030b0120000c1c0c0411 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 768247967 1250 768246717 768246727
    0x101a031006080606120a0506040609020705070303110109022d010c08041211030d0309050105060a0e04080c1c080108150403201612021903080d0221070c05060a0e03 72
    0x40d018a0400d0f81114000d402c1c580380414500200346040340a41d14100503903200d209100c01032404e030040c40058190488114604900d540e40c42ea500c4400b40b1000341407000c0200c14521070002948009201a006400c0902542136101c0c0c2880e03500c414092165000714004040280f035108020802d8091344c4030401c0e520305400c01c41325401d6001c2980c02101d503600d10034400307030154805001c541030444098502180e00c6c5494075000c0d00b51200202080e000e50610401080900c13000c040994102d40c01070166580ca01c4117104503800d200c1c4d810048147c201c9003118014442d03510040690488854074252140112282d240140d07100060f94042d00281c4035441c80c68222641c41c00c504007a00140e4119240303001c04084042e4481180d502541c0c0c103004445400d03065081a89038003003030003111240502440d0541c0e4852405010b204040a64540d0105400c3c844130001004018011200c4035040c0e503501d03001e88020b2002c541d010003151036008a4000c00d440350711901a2810844005010703600342 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 768249217 1250 768247967 768247979
    0x1c02090a090207063b010c2c100903051b01170a0603050601180501080c1c030c0c15110111030115050403080a0305270a111305101a0310 60
    0x194106180540340256284417900507481c2041c0b1070342500c515450018852440d000781681e10000c903140c0d170640b82e4108440030b4602d66000f40700d440e402a6089a014240307080c0d040c409400c01038504a180c1010b81c003600c2c80340c3c082d00810708000b00c0344607a0440d00c4d1350400540fa80715941c0c0d1400303c680895100c0981d00c000041e0108143e9019024603000200c440e9240c60340e40c5044020303482a0400d511080c1260b44c1c08110f0300445001d03140340c400410404620360049410b08041c03100c1c0c500c41038001500348080521410300441d006400900c980342d51501e03108100c604c01c11340703030381103002c540f000074174007034140d81030042c1034000ca004407a0608680c0f9088043c18450000703016503040200802001c0001a15080130305220803181c2e400107841c0c501230150a800d0080d09200700724144191001c041039110015210545a41c019107001a844c094070116050f80c43c40e00d25803001a00f0942049002000d4140400403196140c02c00c00c4502c0c8982d501100c0340c0300036075124605d003500140034041 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 768250467 1250 768249217 768249221
    0x8030316051c050915280e060a05040c0e0403031b030c0e0402090103020c0f0601050907170a020d0f1e0507111902010c050709060e1b1614030d021c02090a09 69
    0x11010941d02a185d06120310420001554802c64a0b204c1c4d0420344c17007060600b1208141c038496400341840c001c100c005018106030f641d0b44001400f80c0540d41c2c840d00018200240c8020100040c5405000f0001604040c40d02030f014081d00005e40e040d01c0c0035005880f103401c3c8680640d00b1121559215600c1211955051002940c4a410111705260702008000407103003003000f0b69064a4048030141000e941410304011010102400744403c211894507946401c04075601c0a031742103100f1000060340d80c40c2c2d41c0c0c041d501400c081c0788282c02c07080c5050804100c0c442d400e4000811101001c40c20411550340180603a41c102d001c1d450028258402c114a06030654402401040507005042262642880d47d450504c9c0c804076410080380c0b251140000c00035207280000c101c0e00043c0701174400b000324a0b50781c000c40c0980500f8425079052802003461f00305000080100c02007644013081625981c07001038150101075071240315800558101c44121080d40245403090f114805030040c0703071980c0285840400380c0 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 768251717 1250 768250467 768250471
    0x80c1605070b07080c06072303063105310f171207020303360303090c030c0a290904060603050403020f0a02100f0507060608030316051c05 61
    0x600744030392500440c0c1941501c02408900340b02e07160003a030b544050303d4003504003400904a00d007484031450300702c00b03580f103d201c0c50304400c3c0120314541c3d140d039945070000e804a007401c1c61350011641e4034601d403030855044e0280c4903401c01c01329400380090349a41c0c051f44072881800040100305174150388903900000103000101041d0340903d0b4114480e80c01a25100ca0700340c0e41311400c0508040008045a084d04510221980300795140091401c5180010103804000000b0a9400d41030724800d81c5003440114450340040d5503070103501103030788030b01d030800f803c0342d0313a19621251511a01c500d40e480c1aa07490403030100403e81e904014500c02a111104c1c00d0f105043c4011540c1c14000e0b81800701001c0c5488601c030342c2c070050901e039801003041d003450308010b810310380500f800c40416080303449aa40582c8812031240c407000624940340708040b0804501b140d190242c480010320140c2410800038002c000040514011346c4a1018117040b1240300005840c144070b00c104020342c0c1d120720005e01c2484071050b40420707 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 768252967 1250 768251717 768251723
    0x7090c1718031914030901091502040f05060702180901200c030406350601090905060906012003040f05010f0206040308011811030a0c0305061203162102070e07080c16 73
    0x1211800c0c455079542185c10071a0500420f031b641d83c0b80d200521007504407c50303610510030b40462030030b0304004400007404d4a0740a0b4034001d12000500100315200c0304243c190f84101020100e400b41015400c0e98003034501101ea00510720703420040b50050180501c112880c0c54030b248000e41c501072602c030381a01c00d05041c00d00e80079280051454800c81c0701c3e0350305a0041d05440304180b183c1e1450910000f40c114840c503002152081e15200030050262209140c5642051007401d10300d80b452040003108003808804890b003c018040401c00040704007103614400145d4009880d0400c01d104260030803a0b54800c00c540280000b80c0d288010440a40c10341c0500030007203a80070740811011010f100300b05441d4410394410140b6960b40c005140c440e540b40c8034850b0001d000b03d0311000000b80044100c1d50301e000d061441840e406800c2c00b031504004000041060b000907a0760500b1b0030b8200c202010303468500d24400c8140300e524040002e40030600c03c1c01014841c52441c0841c90400400d008807200082c1803440031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 768254217 1250 768252967 768252977
    0x4180f0603080d05010e0a0507051219150305011a13050903070c0602030d0b03160306020d06150f022b0804030c05030d06080c0f010c1407090c17180319 67
    0x10000c0b86941e4002c0031024101070300400c49505d44803c40e800360b41c005040c40c0d1210300c1c080c244000c00b5405421140305000d4241500c84e240c80c0c620044002e0320030341500c2c0800628050961181480181c00750301128002c0c0000c0149484000b50f0000d514908151154000356000700e05907400c0342e41d800f1a402000c05021282400055540c01c2d442403016040703000541d001140311b41c2c00712014042c0c5034201c08260050150b00d8280d00d004400c245050000402054020030030001790140d40d8001002440074482c0701241509041c005800010b4004d461001805401411a580301030010707000c01109004444d442d440804070002c540f00c8001800460810007584502c20208000300090700b0000301d040740010703850345404580e9140800a00c000d40c0905003d0740f031884035a030400f01c01d000460b005903020480c1000b5000c11400c0c6104c80d0080c0580314503064190040d107510942807500c00c0016000395940703032100f500000c212860030a000c0c0560b4402c0040d221005486000c610000c211070400f = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 768255467 1250 768254217 768254219
    0xf12050f061005030d090b0307110c04180308010f0b0316020307020a0e100501180905060105040803130501030b0303191115092b0f1d030d0c02030f010204180f06 71
    0x11103810803005035580542e2002d01c1a040c003081c80c0600070485000780d9414410b40301441c0c0f82c640f240d140001020b0400b80445c3c00346000c0560070a0040c40c089510040c410001d9000ea040e240c100f80c4030718401980040e000c00004140103400c2c844610942e00401040c03410343c2da5030f07141443c0c0c0721401c1c0350320300440c00140200b60041c2c550f446007a0207459161081010f5240c1804115820021540800c0c100000c0c0039005400c0d0b80284021001c0e04d041d0840801c403581c544005940c1c3c1d1045912040641c4000641c0003c0e0040e00c045083c196542640c080c800990f0803420582da900945c0030034000405020342501900d03014424a105940c05002030320040c45035211a200d000b0380c00c940c07807021500502d1030701400310500c44031030340420312484840303008113040341c00200548985040c450510040542d2402c0a280c404500107005000508441e800454524020403c48101c10124000d03c100006c400400c0c80c103000f80d8042d0740307000c2440603000350070741040006406c078100441c0003680e580c40 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 768256717 1250 768255467 768255493
    0x111071a0c1209010605091b04050904050c03100c0915080f040201030f0e0304080f0f250b0406050c07050a050f2112130609053d021b03070f1205 64
    0x302c424859664280005510b42c584018000001002041000105114080c4070141500e0805450940c0c01c140d450840903030751480c18034076107410400700e00d0b032511603101082140c17030150b0000c40c00f1859950b20705000b40d60300c904213000440f000780328002080d096000500040707210030310590303c980145400704104600b00d5120048030458a0500d1181d00f001070203104081003002502d46400018006106060002c0d986076111404509014101d00e01103070442050104d9203801000b60450980c926983e590758000030f89650b00090044d0003a0144520020341e900c1d28061840c1251000b6000c0d101a503400c00170880100303666605030032980c1600119140c20380040103102d40c21110107404598440b00300e51440c0c452080c0380c0c041001c0040c452818483c0ea200e00400303000b103d079550201e07076948421702c8001e000907045007103180d890f100c511500700e07080ea4000741100e821a40701c010740480408000c2410385684040c0243d55849048140c1009402c500c0140c10071418026070960701000d550407 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 768257967 1250 768256717 768256747
    0x1120e0309011418130906060608060f010201060f0605090a080a080301180605010507061a040504050607090f05060f0a02100204030c0e0a090201020a0b060a030b090f0111071a0c 78
    0x22142066101044030303074065801c900319041c044140004582091509500013500040d0716071402d00824000101c40241e090b20782000d140d1603031000d01440315a84541c402000600c00316045485201ea030b00c171200281d4010310600050b00e08000c02200034605286c030940d08c580c4201141500320911b45000601190b0500c0300c05070782c2c2d105030a85c0d80c0d01d516181211180070080d00810b246207182c2401013205a0b04041102c210541c080400301d44c020b40342d4030400040b04003150441d0001c0c1070000300001c008020512600c2200300780c80366140300d80c4402c22144c01850900074150842401c0007255410540500506030020140c4112551003001f0380c4003400382d8000f5842103030010203c14044c0464101c04080e1176110308144c8080000c192540c0000756a1020303498007801c0c44140501160050302c56003e9000a981c0040c0100c01c98104031885a03943c030f550303102c0c50034a07501c3c00b0f8054007520110003ca90340c09400c028031000c262058805104034900140c640102d00e4be00700b04d900400c031303425 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 768259217 1250 768257967 768257981
    0xc020a06180215121608130602120405070306110c0a08130f1205010c1e03050417072d02030d0f050909010605071101020106051804060b040e0d0e01050a1d0112 70
    0x44607843d0315060181300f24400107602401d4482840040c540c000101079103d0381059200303405800c82c02ca00d103260f05100009208906c0c5680b804d6044000704000c2c00782c00195101100e203c0c01e4100080c404c600340e0b500e064003901c0c802039801d8204912040c04101d045003d0105514014480c00305550340750410a0643c00603401400f02d10301c00d01525082c002c0a1081c0700410740301e414908607061201060010071400c40a0344002e00d983c42001c141442010200b1111181a01060b00c0e0307200a207003007100d05101d20004004198000c801c241c1003a0403a000c034884565800f0380209030409040600b6512100520948801c100f4180490140c96481c2d042c9240280b803151260b030341d03c0d095400c04141c0b40d102d1080103815a0706144041246072209440b40d0042c4c43c071780d10b8100e025203440c036007540a81001424680e125040c0090b02c6003150300840c414801c00c072940c4410b26000e40f030100540b0b0328000c01a0200214119a1000f62003529841d840c94100303105160100400c019400702008a07000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 768260467 1250 768259217 768259249
    0x1f121404030804051002032205070f081e0a030804020105031e070c05010f1e1806050a1b090b09060c1603030f09090207020d06020a0504030b09030306010806040c020a061802 76
    0xd2442480240213003480010210a0380c1c20301540781d0710b48949a40d03800018183c0c000c031003412110085092083c1888000054062240000f6140e85e481f03074081e0743c1d1100f1402c00106007624001040d1140c20002d06c03000600d9060b11102c14580c2c0f140c0064525400007080819a00407810042d403c030000400681c2c82443c41e501c42400c045528101203084407101e002515641d807500f0720703030030580000b501e030321081004403680030070440c000916040100b0048132008000c181400c00340300320701d84140c00c1095241c266492495000e201c42c403045038050303aa4840c1402e50403003040a82d03601c0c103281005042c0000003404079001c9816004000382164070540c070070b82c00501001032840465500032682c20060501440a508260341c0c0d030006800c0346d101d544004c00c1c107940049c4208099002c4c60a41d4001d42d0401603103c1c0600d4201100c945070303401200d15600107025400020f00601d0140b0031803400701502d500811004189a5840e0010a01005014801c0907072400c06001a030f10400f12442c4048 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 768261717 1250 768260467 768260477
    0x11070609090518070e19020f340f08160609290105100e0307030809042d1109040905031e04050315421f12140403 50
    0x11a005040c400c50b1005050700c1d84810301045095404400001c04e2410799118400c401c040ea1a030102c2c0400000700402400310039400441d0b1050a03007010009440c1c1c0034201791080d10030700c000500c0c0000da941d076100c01e0002c1d040020070358004104140a911907140c41108001e191424003c00f18001c0341014070308440ca5500c54011404100e08070407428001d020b1020349580c2028800644942100e0501401d40524000b1040400e81c0e03126490298181c0c0c0e016080d50411510b03828011038a40c02882c000f40181c3c00c055060002401a001c00d804028040308015220780c031001188004c0c280184011102840a1214400341e584500c80c8801c580d00c030b00015075a44509248071400101d2100008400c1c6600740802c00c5640c60200d000015500c1c040c0c0c405100d0740e904141912103401700042c019070801007102500361521070015a08108200244048160702010100324140031081400d51144214595172203c4500036410400007461001001c01d40301042c90542d0b8901404132000e0b00003807 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 768262967 1250 768261717 768261719
    0x2040306051b0406020a1502070210090303080c09010516030306081e15010509040b040309180905010b0301150b090a17070509010b0a0219030224010611160509060111070609 76
    0xc2c01c1240b078a1900e4007000c0b0b910705003890504c02a4a17001040c0c80500070000b80040010300c00d03003940c11603640c113a0050540f0121498131600401e4076100d0b000c110081041c0701c1c0410b98140c8110241c9410180c169105071804d00745118400c1113048411088051586800c40800c0d405c0c828014603014440d0201d043c081d4803180380c64240703081d04070628501c4e14045400103014988500034095809a001840780b440b0b03403624602110300c084550300c8030941580708050320200c4803440d00074818a0f070182000740b00c856242c404240c22913821158a00441c03103d0981007003070004e04809032092040c02003c03614245d640300002da10103000b0280c0c40c2c2c516001090140502e180084007680940020405030f07007480741d11a8083c2d134542e910002c0680a08060000800b014401c1117041d072403203154040d10101040238220154000070130f0243c00007040006c90100c0c2c1103440050704800080710301100920041c40c00b401e01c13402c48000b8203010304111107101e84010400c0200203010040c03034190b640501d05 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 768264217 1250 768262967 768262981
    0xf020c0d08010b04050103150312020a06050601081317090604240206070921021e09150303180a08070f181a1323060a0b04360204030605 60
    0x411400840d010030321068900502c0072150390025141610710a0034009000c010b040003540040426a1005100c1c140520a11a181c0e42c08a0403958448c480d5400b805251101d5005448802044a0030118074004100e41008114421420402d41101000340b0385049140404124242e105070880701c0c00d40c450300b214498507a0310604003035120007184041c065a040843d4028001d048034403840ea6403146025041d03207181441d03441c468400e0785c000c2c0006455406840c50307400503025894698440c0500000160602d0f0003c990f02c1c10030200100a1850010032460210714000350304600d40c1c110a03105070104008004000700c002030840d98a0740e5a41c985800074809914171404048001a4140f01d8030300790061100c003a0360404942100c5171002603000112510003401c00041c5c02052006800b800030381440403084450052200b42c03040c803c03040d1150a031503010321a511400244400c50304c040741000301e040b40381030719280c090095103400303440715810b03c420b9801641003034800d6075945041c8204 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 768265467 1250 768264217 768264223
    0x12070c021c0321060602070303050a120203041103010b0603011202121203042004150302010c0609080d020a021e030a080c091e01030b030c0303040603090c030209040506040b1e060f030f010f020c 85
    0x400394640f8000c0c0091810f1900094485e896844024107011000c50b46036403490145940040c4090f05150843d00d83c642810701700b604202d01450b0600951074891106480d081050459050300e8010316401100c0703101f0790078480012031448190005029410103880c044002c20300841c0aa40240c1001440004079541d00c0c0144242e400703540c0c0328916204188002c0d240c103640000807a502402c00445517009402c0c00302c05481c500302d000f80000800a807403042c08100381d0141205006660884100800084080d400300324800300c105501d90046c00110b6071a4031035030070980e01074071701141c1d40d0400a00c000802d200502c940030554213601040c0300b241b11564184240e0304409012002801c464035040d01180d100d02c1203006900c10942c950401c2d0003800300b010065801158043d228030307040e161604000342c56000a4030100d03500c0e42d060b404144203a40d2050300c12001064402846001e4031960200000a03581052568050042d03590030380c5501030a00c6602c0006c114840c0140e6120b610a0503541 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 768266717 1250 768265467 768265517
    0x7110f070311011110051609080303060d02060a020f030a02010501031406071e0905120105010509280207061118120313090507020703051c1412070c021c03 68
    0x50a0361001408001150306102032803101030007130820340c004180d02c40055062059458140080c42e003407a00703010000a03081e481184040d0203560b4800a1929401c00c5912407006581041d44003004200b400054601740b401030200d841d650045070750081c01c1c034110b0384c1160483e0b2044c80c050f0b55524010403d0003d485a400c184910b1540600003a1074480406041c01c9158104c98042c050414030304d2074941d000340140405800300902ca000b00b285451400d0380a03020901406019040100c0414448006400b044841007071050944010440202d0058000d4000c0003040d00c110361140d001002d900e01e550000d200d41e1851080c4030112020b9041848007540c0130349441c41c01c55108020218164140030a44800d60b00541404145500d9440040f45490015000901b5a0040d241020310f2904004240940352486490b0b00e0043c90941014000f50b0003110203034001c28031840001202280f04580403403103030380300800b880740021130480300c24820a0b000004034040380075106054168181000204 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 768267967 1250 768266717 768266743
    0x1211060903030304062f19021c0c1b0b030f07261504020a0f021006141306030605180c060a0c0f0f05161d161d090711 52
    0x6280446000c00319903070f80300c0100003619081c0ea0781620000d032095084540303260810702d001740f11784451240c0c40b40c419a00611040c1c00302c800b10280240f2043c004210f010301c444040002c030004070401c46096410303070290b0f5400c4500c02c003103001802401160144040c042d20b0018681500ea103400322500c0380d4030501820a00920141e61040e41d245401c2c08040a00c20300781a01c1c8244d25260580c01300d03021800040125400703070000c01c021400d158000100c3c0c2d6550360725400c60300e03072005100da00004c0301c01c0781c002c00c180c0860015041c0200e081040c02c20b0602080c3c0345000600d2aa00d8840401310b6406980815207604855130002028000300154903117800c003100c4603850480c15540c041c00885000100030f0074058004d54403414060544182848240c00906680c5006698521070010b90180d025580d2410000c0d204114568078865082d482500c265568040c030381d481c03c07410744484034a480701c0d414058240300400502c2d103690044e64014144ca8503030340c151400000d040340c00e042021a100c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 768269217 1250 768267967 768267979
    0x803071a131104020c01060b0a03020901020d0f022e06170d080609010e060102160e0105090c070312050c090312070308010527040213180308070201020903280b011211 73
    0x500801c1c001c2c030501903465411580140c0e503041ca0b000360742c0508003130f500c81300c1d811501252000c99035425400804007100309a080e0b5521040c030101c10f44800d43c1d0704000c540140c1c428200040120103d031940740c10011002d0028440f038a1501908081d0740c2141c002051802000601d4802c04400b00b01103081c2040c0c2f420090710300c2c40d2103030104a400a05101e814a4101140c0108049074000c1c031a20b40c2d40903810300c8801219407103019000d00340d40c0170320a0343d0180c440c1c200022000f001c040c040e2103190340d1690700c006440703d076044200041d1002501400d90a102004101410360b0b080007040b0890b0191082180c440c146400d02900101d81644070f1401004210b803410081c061083d004500041c0e620301a4107192110300200343c034002543c00301c9c1c5030350786003c02c40241603484100b01c0304014407070303a203560036940c0b808422800d038020403c2d01501540034420807000c2015214001c50139048840302a44550401d4803000c0c08101700f0391180100e1601000c40c00b051054a0103009404030040d038813 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 768270467 1250 768269217 768269251
    0x608190c05060703170a0908041e050405150d1106070c090501090b0307150c17030a0f0c17250810061e050d0e010c030c1d01020601030803100803071a 66
    0x103480515801d41c10301403211540c0019106c400310741d000701c607041d420070302594841d900e480c18900b0026000c0c000c900e00a60b960b01c0003c091415028051103000b412041c020301c1821071052120309400e43d04215050012660a1915a04c070b20b00a4580d16002d10b0200c40098075214154084a206800100c941410185a07034080d480004008046902c0300c5060103c1c0000360004079a8a840142e00919800b5100a06045007200c20069405101100c1c2e0030010301610800e440200c528400c50000412010721040044556010055500c0b48010722a520405c10030440410f40c511400010780200303142030280301c6060f40030642ea40c083c00032070808185445582903100c0d075a1f10049080410014005500741d1101c840381c004200c03107440d0000034004103c40101c0517002d80074081074040014240e200507128440140c20181c1010010780282c51140d003152200d582c43c0d44000c0c03226a22001c41140000c61503410030007040513a0180042c000100002290007020010140c0b40c42403560181031 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 768271717 1250 768270467 768270473
    0x2120a08030c030a0213030602091009231203040e0f130302031602010302070605070302040524030408090307030c0b03061305060a0b090301090c03150e07270608190c050607 76
    0xc21aa048418095296100d6503001c40c080068821095160041d03000c1d01800070401095401074003001008440f10103001c0b032040b20031941c06c0c40610071480850700041c0411061001040f5814500001030140980e00041d500c0140c81c590055104501c80d1114500308500741c02d07000103150304100c10101c07030b0240c20a0340c2c4009560340260045214004079000c204411a8084c0c0d0480b80210351000c424016458040c0c4098000d41041c4500c074080d000040020301402e074040441140900f8940c12981076440c0e0740c86216054000000c0300e038040c41018004400304058640340b40c000c0041400e015a81c0c41e01c407040c0300b02e41498251807503595050106010541c0e441d981c00c5016034401a40e400d440d0503030000000d015001c4524054802c40d01140c0200610160119185181d202c1c440300340700030340003800b01a41d01d440798821074000c4e4504a0007061820102042c00c648004141008580591103c040c24181045008014061038082d01001d0801443e046844014107003102d03518144040c030b031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 768272967 1250 768271717 768271733
    0xb04091112071d090f060915060f071a1005031e0d0f03062d0e0f130f060e010b0a05031204090905071716080105150f030c1c02120a 58
    0x1424070818420800c0d1801c0f28000401440c41c41e100000f09103401c0b50805009059080d0760a07290300c0d0080d405480010a140841084501d00f00d2001d0800744c545200d09640e01c001d5003204104176280500d04000b800c80340300c100c058074001c40c1c1000b03a034000700703240104040c601203911001440e010003250316401d01300300c04140c40f03d84e0340050030035110703104550b80100e0050130241c00410f051041c4103091500900702c0213405041c0100c243c0c14484654490302c4200030190122111040e240c078201c0001c0450710b1104055240034805d20241030b4412465035104261200e0081d17140e03050f99134441c010680c0c50b0000c8204c0040800350090600600141d400c5c0000e8803803402411b40c8036031504558810002c2c00c1002c103005100808807210b031010100340c5d240d140c40031100c42c0100008880c4000c0740802042c070401e409981012201c070900d21602d01481094000c02c20302540c5070082e242020b215440c1e0420380f201403070010003200070400c654410040300c0022501069080d601911035400080d0310070b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 768274217 1250 768272967 768272971
    0xa0f020c090c0d330501021203010b1603120207030c110405090613030e040614180106021f02071203061a070f1103071509090501050d0f080f130b04091112 68
    0x7401020840701c540e00d0074200c2c859007080742d13000242c545000c44212181d080c0102c0080d03442c03d0342030f03030001001c4800070b040e64042800b8034480403004004c04030402ea5030580e0b45403180e1007824a0b9039200b401105c3d01c01241c0101e4030a4020440e4080e000040001e01d0010407140748048504011f241488480c5070398800000303100001400036408018145800b46280c0354100340020320601c02c0985910750344a00000341c2c22031900826460611003685400480701030305850711540108448a480d00001d000403080000006525a08006280201d4064818804107044540700880c180d49400300f154100000b01110510302d143c24003000d03000454240048507000d40001c0020b071241113000002c0c4c1400d0442e40304440039507600d004c038800f280c0c1101052044580c01c0c881009181c0e610300500541c201101c4000704280b15402c0154001215100034140d01c0030480da403142000800c001105007207150f81c02040032080082000c00901d00503004a070382407450340c14100d04240c1024610b5000383c0c00 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 768275467 1250 768274217 768274237
    0xd170112050a030305070c150c0e09151c0b15030c0111060609100b0c0105062b0303152c1302011b020103110703120c0207080706050c0109080a0f020c090c 68
    0x22000451b481e14407e01c20401071903042301d099515452800f9101c0010080b42c072103200802c25685149034103182000e159441043c090f052005c60848100412030880b035210520340707405c070200c141c42c0003144407150014450031014231150040c0714400101450029032408042c1005400742066441c90760204800703170405400c1d40c0c0420252100060101c03142001e411005910001040e0314000c0401508414003d071002e0343c910b8100616021611009400c00c201c0c071218050444810001901c032f9489a821f12804043c07414195442d58800480d1622030764060040d2840ea10f051500a20706408468001039104c500c5803807501c840d80043c00d0142d54851100458454042003015640260826040c60071800b148507941d16072881c020303080402e29520b1204007441c000703500c0121400011043c06880e0a640101849803800030122087c0e03216203403c280e655261450308001400f488082c1ca6050602c0c0c80300c1c00c502900e100020300e40965844003c0c4140210300c2444105441c401c01c0b00c1625003 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 768276717 1250 768275467 768275471
    0x20d0207080610090e0322140612070809070f0623030609011205010e10022502061818040623100303032c1f0b060301260d170112050a0303 61
    0x2180b90301411030042d00c0d940510820440402d40030740100c1e600040985a21000409000c0181c006200c4a40200135100d041d010400740400c16240c06810200d0f40054020102c420701510340d813f40450711250303402140070546114141c00c1400c0181d2200303200349901c003101421498200e001443c5a8018030420725510203a0042005100c402e4000d502c10060880842d1078081c22000510025848402420181c081500306007502040000c0800d0030780d60000c5c1140d00707000c44c10b01c81c240c0145025841c0b940c480b0721a00c0140b10f044c244000785203e0342c000c40c1c00040f10b54108606c01081e100e500c458465900c80740d010060704218890450003a20f0705854001111054003807103c8005020500c0c0c601e5508401000031040c0e480042e00316210440380820b00440c88488005000303a58500e040726034404014401404045560340750710780d000400d04111092080d0b0001300504080000350034078002180351074001c0010488494131030041152154044014406854240d2183c00c00000141015 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 768277967 1250 768276717 768276731
    0x9030703030e131e110901080103080f130305010e0f0a0c060807111f0b03030906030432061506040506030718051008010905060609030d03111603020d020708061009 72
    0x1d16200362507034a0f0303910440300700001c036544c519080042501046410314a03050442207888000b0780e000f07444105806846440d2682d007181e945042d990071000141c004501c2c01e100200400401d03440700e400650040c400040d030088070f0926542400d4004404a803180e00101c6140e00185101130b00c442229074a20f4400071603150804115061541940340c201980300d0058441c0350b00c00c2e9140c501c290340341851070401c00c0d80180d800385a140c2c0600c900c20b942c0641c0610005010603080104050003105280381d00340d03410041223a81c44000000514082c907a44000c04102c02c240c040c0d08141404a01212001d081615100c0016818400100302030704210340c00700c58543c1007550762003442c050310000300707200c8013001c0e280c40041582800340320318a00b190420000c20003a08161040319a4404007030702a203840b4a1480043d006041c07031000c1d48030144401c101010350300e000710788090481e520a6019055501101000a24085044d041040150050000e100490710480c0444085071843d1074046826 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 768279217 1250 768277967 768277969
    0x405010906060c15200c0105160203070311070e2406030c07082a0a060f0204030f08131d071d0306011202010207050925030e030f070f053009030703030e 67
    0x30300317003244165500b20302000700407a00c03803004800303801d14003101c4008005030f985400340c0c0c207850141c2c10780c02409a0400c10a030f002282c40344421524605510b4201c69074180d4807110705041d203004894010000900c2180c112100c00940c4131140c28501c00c642050039410700850f001c02510404e04014500000066015580040045071001c40c0c04d20f21242a001a01028025194940b0043c11070340d040c68000c03000000d203554426031b41540e420802d10f04651205580d2012142e0040044000c0d90001040c005280c400340c025140a818240308c0c440c1d01c5040c80800070b0000c1d00c40c800c80980701104040d00741c0d201d403000180700d811035020f0001d846602081d400140d003800e0254000b030350080e04170f404011500700710342e1400440b80307440790000030b81c114a0300088040f28914040381005400810610550759000c802a001041c056121818525415030b1000c2c60f0403800200d89000c42da03c840300e8441d080743d00240c840710a01000640b0702d0400ca10780000e4440c2c0c81408003c003404500403d0b42d040f = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 768280467 1250 768279217 768279221
    0xb03011d1c02070f030813080304060314060102150a05130f05070302090708040c03170f0d150504090f0f060209101d060c0c040b040e010612020405010906060c15 71
    0xa103000d24001854203203152590309441d0410481c402810894075011002603610000e0700d82d007100c2c180c18010081c1c50459969805507400086600d0b045949500c002c03400341c10502c010070042406840002c6c0300c0261044041c1c21a600800c1d0364150b400c150007910501440280b05940710701380c00e400240c2a55a22181c114810b01928050445042c4c044807104002c40001d000081d030f4003ca6101c1da4941e51404219a0901d08031001800d200d50342608200140742600c0901002103144c0e03243d0308001c1160f081311402e800c5452400d800c141c44032141d6981c021180d5580c80a840199024131101d40e040e20741c032403007000c0780b40010041c1e00e0118821040c0032441d41a00d01102c001010305e0b40172001680010240170141103081440541c18001c80880e24021003180c0b18500044054402c0c408a54100002085990f4032240c0041d00c403255030340c581c0003c2c812a400740c840d030f2114039140c00007801400308464050700300070740351440c100e000e11009401c00200b0056a61041740c0280382c2c802e8110300c01c0 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 768281717 1250 768280467 768280481
    0x61807230d0203030415030f060f03030f0f170408030a0e03090d0818041d0727150504020408030c070527150306040f0b0907030b070c29070f050702130b0301 69
    0x151011b103201d41c18160652503003021502d5100480280001d07515244c407208519014032000b4007080c442d0713001d0f01c080e81c0a2520300721140007a08050482052540040d4850141124115220800042044100d031080c1c401d110092900e50011070900a441c40800c1019a200c00f010f4070100c0d010400840b041808280c0c0c2080c0722003d0070a010359491400c0d190b6803a501e4035030715507a0f4065004007049401501d403c8482c101c100c00b040d01101c08107104000010b00c1c0d036004d99920f01c12000c00c00b0071941c8460000304004d0071124002c66441d03190101c01400c010b829040b05106581201ca10141d407510780005060180c40c5c890131b41100d884a003200c0e892521001c90554243c000d000402052201134901c025a4074018240e01d0a17940d540c040311500c031742450000410b181c42c0e21011a0310148129080d01a15103c0c207540ca800144411044100500d040300c05c032800c02210341044601a8001d900103001111820860301b05003543c0d0025540c0b44040c820880c080d541d600341c9070802d03502500090 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 768282967 1250 768281717 768281729
    0xf020706140c030c07030f0b24092d2d151f030c080f09060a0209040902060d050105011e09092c0d09051207030803040302010905061807230d02030304 66
    0x60170701d640d030340b91189a41809540c01d641e035281980018a081e80080351000d059205c91134044503041c00300301080503035840503000d4844035001c0c014044842080c103094500358289188007400b5480c003000745401d080c08070540294040c2001c00141d4078000e0100d8403507009106865481c41000d04480420054644d0010b43c3c1d80d2502400803003440360f50168410405082c05540b4903019540e9486011001c80b07041c0d41048155000a0010b141e400c2150301509545000070000308038124181c0024244d900704a011040403992400108041d603000441c0c0c150303036600e180310484071260800c0082d01304c000034410b0400003516040070366401070f154480343d00401280c1000c0d01261103038106807656072980208210105100a00205003860b0006510491051400042607024156174807203915800180044007950340b108900c0c0009002171141611843d550b6074488094804650030074070709185980f211058418140d44080342d03049105901270803c10688401c00741c01913070301c00309103540304561100d = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 768284217 1250 768282967 768282973
    0x110607050c10090f21020906040b150c0105090a0807110d0605070509040507050c07121403070b1b0711121203070302070312110a080405100f0209010f020706140c030c 73
    0x501c0b03038690041450010358516505040312503440e03007103c0001741070380400b601501001c0290400189442c990180d400003001d0b002040002d0003801103807526560b600e10300b4120304c1c003080451080c4002d205079503010502000804240949880b45116403042400c0649106081000c035010760b11541c00caa01020ba004034100218902035200521503046154401d2165003890003184446200b1002e03261400c0c0240c010346841c601d0607240740440e0044402c00c58181c0003149019000c0f24003800034200090145d5050026403070140450190440c3c07200000ca02401d0501443d00403a02800c003403ca0f584094442a032075940c004091843c089074a111491a00ca00000b04450950706401a0089902c02c1e1907806000a100300c242060b1001070405036207500c024080c4d140d545116845854109010b841507411021400e1442000c0d90100801400100e4000603081348550b4083c0110045c5644c520181540904201c00240034511b2100803031a401c10101c0c014210a0061084550603087d860072 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 768285467 1250 768284217 768284239
    0x7230a030b0a270b060d0203032a030c06010608130506010b1b06090f0c0103020c03030a0b01090801020c07050a15021e15010e090105070f02060613180f020a050409110607050c 77
    0x502d002c0a100543c00ca8500d200500455801d00340080400b0b51540d00a02840c00d2a130b01ca08148815011402402c03403001941d15001d812500a0009160413103140016084940c18460040c0c03601e0005040900500d444100d01c80118102060490541f000d0091203980c80400d045280301a440084406500d8000c00301030144000d40000c0d407404052881003aa502d00b40f01000660403401402042551b0b50000c100162000c03001c0d0340810103085050414490068440c901d0740d0890300003c0d090703100c5501040060000e07180104c4100c5c001c08026014201c0c825040d00e00035191004140707d028040e4241948480009081c001001c000280d8410309c141581d4a5111082840c0c06491845840d40307810041341c4031034421281105c51400a40042100741c0b60030f02030145005140c80c1d070030300159903101404c00d0b04a41204510030341e40241000780c0c40c1c0d50107004000c102c3e000c1c2e6110510892411031a500090f614400c40c2000200840b1402e45644860400341d003000c821042083d8000d050b52700d = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 768286717 1250 768285467 768285521
    0x12020c060103050d0f0909270b10151e110a0506040615060207030b13061d120315010302071a011d0a140109052707230a030b0a 56
    0xd005040741c2c0210211140755100c0c60040d241101c954454000007000603d09200c00501a000802038003405580b20b00c0103020b00c5800c0f404043c0b4a01c0444040b045075091240d241000100500503107141501c1e2403000c00c0d0300d00b02030b1900145081403c407202c0009520340c40c1c540142d041d0900144024151205000c10346802912aa401c840484500d440c1251030300110071071102246c290ba503990000d00d0700b10b00310b4480c25104440245480b07042c0c41103200540c0019001d0050f01540703242604a40c51505101360601d0401e01c144c07043d00c9041d4003d10403c44200d000e9198050220350038240160789881606021821046409011140a15403400003880218400403103952040a44c640829500d0300d0380b842045d12030640d15184101c0b184801800300c04501d51110b5045100e260011000d280280c00d4565075000d840c0d01c514054111080c10083c00e0302d0008070a000211503031118151200d00400a00d204040f40000b40c1507040080014071b8402017030380a800160b1a04801d4500d4031070002c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 768287967 1250 768286717 768286723
    0x10030e010908160c1205060414030702040606080403080a0507050421021002160e0103050303040201050903010e0111090102150c160c0e0a1a18070807090302090a091703040c0b0a12020c 81
    0x121040304ca40700010000203101600315005100250b2240c0070b0166070311592540d02c840b8001030065880341c0410400b05005030340703503ca20f000514880d03e914070749150a041c09059440010541a0310341e04107010000c1e51940507048601b62004e2100582c0c540c2c60000c4502d400345440c01009400250100e01042e90035000500c81242104080b60380c41c030700d91600c0642607000020305c80100305601c103002003001580210041e1940c0c01019000182810340c2c0c2d40d40341d0079034004141c0c610344000c000400108559051040c400881d0f000900c00205042800b07030300c404c9205400a004203005440165420084d06c0030121004020030700c815141d80c1085002c04008040c101d076010300080174081d1f5204282001c01c40350b901c0c003081d01c03482002903541520964403900010014010803040f80c8003c001640c412848038040e5a031086c00007070108403450001090700401c0c0501c603010390f0a00030400001d81804242d0706903003074842c03001e0722901003a10594000015441e940010b50000c0b4500310800400 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 768289217 1250 768287967 768288007
    0x61d01060b1b1b0f01050d0f06051309030c11040207050d03051608091b040f06031104391206091a060f0f160f0305130806010510030e010908 62
    0x203100c40b05107545a00c64180d0fa4060309200055280150341e1640f182c2c90f05504000c0320701c1c4181012460583d410800104440c18007030031010315035950400b40702505158104820200601808000721035040d10041d0401910001c010f100007240201d08071580c030f4503016220003603070003400c5884200c06d06101401500d0200c803144501e05101d54101c103494804c410710340c09102c0074800740c41d0b40f070032040500500120f0b184031103820686848150111030392900c0744900450180c1e9000c10342030014010401503562448200c4800c148142100312862041f00700c0e40002d140c0703131009403003d11350314105540d1041204089440f00f464900700007002075850b040f0a0030b035603440380c0e1a900b0b150140f08200b414003c0005144041c64140022141540f6250040484244800c0c205400c800c1c150340b400c030260303503000c8102c000030800b18000c0800000c0d1141e4402418515015010944c103001c0410340b0110141c82e82030405441d034481d40c4c8020001c0d4006904d85401c44102c5940f20351b0810034660b05642 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 768290467 1250 768289217 768289237
    0x40b040513030f090f0b030406110a03230610080703090218041b060806010c0f05031809010801020c0a0602161b080c0418060506030321010e010b09030a061d01060b 72
    0x9680654440f00d200c0c0c4400420b694080b01603220040c24105501130b9074100070000c543c450b6852010020015a82c40a800e018a003030703a021401c01000d0451000755400d2090f1054000140000d00659a440c03010700b480100c1d0b14649154240e41e80c4070201e02811034440080d400000c507130b0304814600c450220040c415401031035103041c4041ca01054440c128001c0c416131000a100d100031984a41c8a04c0350040704c1c6001e8035483d00b10950503290340b4255070241c00b100c001d01c0852440407180d030038192006801172240c20003c40c01e00e05640b98850311000d070f058001340120741c0069074400700349050210b030341c2e03854100455030704984e0213200c40b440c0c001483c0900d0105d0b10070100d82e00c445203810f00800242007050714101110140343c1da9914041d10001d01402e0f03041c0002c0c000d0401013a014928503403000d03130020708102254541010b4180000b4184c00c10034030408100b040300901e450000307100380420340c810f80005400115540d4201c0c025040301c1070700c0c0203500741800051945c441c600503000d8505 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 768291717 1250 768290467 768290477
    0xf0f200609010c02010f03021b0d090509220821040c150210090c0e09010f1104030b040b06041b1e0203030106020a080904020913091a15090402040b04051303 69
    0xa18000304400c41c001c07a0090790000d0010201400103520510400030355419509000d4141a000e083d0030680c9142c601d07442250780d1108800d10805640f1500c20f0000744801c0e00d5500090401c141d00c406a45e81c202c1c164015400d84140301c1c1e04202000302255403458408004625051010004082c1e10009507801e40f4030309040c081c080303810703408080c4481d21941c80e50010020100c0c103c02c01809014003244c10b4801c20101c40c1e00144010381c01144601c074250507000040c04200002103401103400c0078021404148003400240002000096100e82003a0410301030f0f00c1e42d40c0d521000401404207044400b682c20300e9080303264202500056201a490b021103030201581c4030222007281d40340024410580180d001072148000b03e140308006115550003d000985448921004100c26030b040c088444001507592011009015540b0f00b00c690600d820032446150382402d4a4150100c004225407a100b0008200405c0865a03241d0000c209040c01a20611407072038240c0628600d100442000e40100f8 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 768292967 1250 768291717 768291773
    0x10305060615180120010509060103200d03180b0d0e0705180601110a170c010e06010605040b090102070504060806040c0905091b28080d09030506070c0f0f 68
    0x85030203410307074143e00b90200000003000300010044441c1d5801240c502c1d402040072080110b0000700703005092091107040000c2c54154503528000030a2020800c0d14031f54074910310b203511000c0c0d880036a2950790300d8051800c0103000b0031603510120b131202994800c406e0794200262040b054520f58100080307401c031503000d45000b035994005029945c20403103054240071761081c0014130b8541c0900b00c403141215000040b921204800d941e084440d01e1004860320019502040b80c00c01340a01f4020142c142907904080c0c5450b5141040c0a880c07806140685400c0100c041840c0b20164400c000ca5002482d00407c18008a03075180b56440c2c89030425502902c01c400f6005000c00d500130b0500426024420900c0241002002020036050310400d049000d0391010000850040802d03402c03924181ca00300d00e6a0518138103182808031890200c070f5001072002c1c0f0142300401c002180b0013081e03d540c000400e041030407107014549412020303408604401800d840f902a403c600380a49845500c00790340305001c1c000200 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 768294217 1250 768292967 768292999
    0x30f17130204140114130b0f0603130b0415050721020f0f070f06270b07051b070f080c0d080c240403020705040501030f03110319020c0913030815180103050606 70
    0x7540a20150239080149100f03941c074541840310085070311024000036126072038a00e50310400f420b04c00f903034207594058080038410940700083c0b00d0726030031070380900b040400204254022a9078030703812910042625404646544036042020444c5e030300d071072440e200580d9030f0428540015040070940c41600c00314907060001c02d404060700c03203545a2514a2805041210700303a541d0f190810002040743d000c02205000740c034005159905a0112404a58040c18606003000b2803060365059540c09500d05500071a400801798541c0d1601000c450780211302644d07680f0b02d6803820ba03e0a0869610400a1090440403817100080b00b10030360301a9100f60309440c2810ba94034108000d441c000c1c0409040c4909000646002a001e4080d29151080d100192402c09502c6606420071408000c401000b503004481070b074104c2d1601c0b1010940c018501c4035082c644200c6500d0040c4030f1200109940d00700120b008102c921961a00b01462039105040c50590007580c6038a48076864500c1566601c1c00b0783d5641c5082450 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 768295467 1250 768294217 768294221
    0x203030907090c090f0608060405060102010c050708030a060e0910060501020d0915030b060408101404260c030307110c0f0906010315080d0c030f1713020414011413 72
    0xc012420081c1406810482c900005008080501003441030035680000c96868090681000700490303124010246880e1060200b521300080183d811645081c43c25405c0540040550308402c0c0c200c0e80294984d40c2e1101050f0041c085034100c0f0030411221000c04c9480c20000494481c03885640e103003400200c1c2da60005a03611b1080e404104003040a180d005d00104490050000c0c0e402568580400c004881101158240d48035820104194008100ca0400203102d400b684059080e542d80502076442c0503160100ba139410308044120420301d200d0780503034186503401921100b00148003a01c2c0d03a814040009001030388030408448950252415102103458088050f99aa61001c0e100025642e120001140202101d20040c01c054600b4000810764407030401100c7c046080c1512240703840441410301074030503885a07a2810070400300c000030034194030381014840e8100c141c0340c210b540080014070000e00940f46502064800c1b1543d40c000092010000c074030b10390001c009855805c2c02c00941e00910003 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 768296717 1250 768295467 768295471
    0xd09030302030a210e0309030c0109050604090c09030506071d2d010507050f0609070506130320030a03021606020a03051803190b0402041407170a0e1504050d020303 72
    0x342e0814015070040c540600e0103040c1c0d00c0e103140e0300c4034800c040780c000c0c401c22681c548001c8140c90b4000b08003100d16060400541e4050390003402e200d02042e24143c0010200d201d940510b00300c00b915164034404090091009030095680001036903003515145c040280a4115401c11001e0400182030030a641c1c05c00071542441101500d8003011420020301900c182507100b0080e40781042410801d01c40416410300c4005c1e824480180980040e0501011091a00e441c035002540728a82c10400b03400200010382c2880100c81c0e009059800c0401d540450104000503a800160140212000345c82055404903191040c101500e22100b070058072910301301c0c1c1d02d0900312001002b040040200076849507038441500b10001c8020b00302c591070300c401e19100c00f07007001c80b4800f00c0740d40102030144821440c0c180908080c038422611800e003d031030441c03802060b03988010420188481c40401045544006812410b110030b0f4210440f9003450503000c6800e06080102c1e401d48950143d41500d010741803000c42124 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 768297967 1250 768296717 768296723
    0x60306030312040203120a021b0103020c0a0b04060603020d140106090b030706081803070308180a020114030411030d12050c0304020904080d0e1e100504050303150607230d0903 77
    0x1424540b81c5007100c2d09400010308142d074103204980c90743c0c060911010041424644607030141c0041c2c512003c08143d03844000c00010b050500501240045d00c0d0300003400c1c120907400c11600d28484d12242401c100528850b00080c4d00100c18000500a00110b8007459424180000003040780940d1040c00f60100c0d1031801980d90315030040751042150390b01c240881904040c0c289100b82c441560f8400840c41c0d6448480224007007515181040528a01c9140d0400c5c1c240441380504650302007503000030404110710041b404d1901c03010000c0b8050041848040300260b03030240c100d68084411100180400a00440054409040c080060080040b500a480c001c5902070f0031000c0c5515665900407154001403610808140e80303240345242c40c3d40c00c0003200508864411001400d00300546240d0920b80c04100d444109400d15051100140700042100e6200d41c1016400c03800804140002d81c0314030820402805136a90169991070881d400309201c2003c000c054100d580003120f108013078403c003459210103 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 768299217 1250 768297967 768297973
    0x1701242303150111010c050f13091401051002030406080c0c010e07080f07060908100203090f100506012601090e07091410050307030507030303050601120e0606040c051c0b01210902040b06030603 85
    0x583d03c04230060014003c03004070f2410201030181c81d00b0315901140c0160003d18040018071004000314140314280c41c5c140401880654541424040e01405482d0054081c1c1034030b090005136280000c0303080d80310345e0403005000b00350303400a9075884205513035014120306080356015034600000c6140c01500318000300c958600240070040141000c4400a4100621030170503801814044124608180304011030312203142d200103094104080014a804c900400d6801e849940c120584502c0c03500c400300c20304507007500d0400b00303c00c904505854100ac545a10840b0000d0500040031440190103460600c11680c400c08ac04a80b81e6820406a03100d07510722001c0d00c83e400c03090060011038130a411844d40040181480d41e003612604a5031030488011074080103040e048041440f0583c603103406a5200d80301c1c2850b080c1e04282d882c0c5101150b11220b900381150490390350004000b40e034010203030510109400e5400102c008200006200500202c01c400c0b4442c52415612038110714283d025207020b00700103030017 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 768300467 1250 768299217 768299227
    0x105040b24100203070c090c08070e010e0405101505090f040c0804080f07210e090601021f11030f011d042a0f061701242303150111010c05 61
    0xb805000034140750300b0001c5010410550340824500d640280c01021030000000d0406501c9a000b01540c8019000d8400c1180000d86100700340c2e4050700040e00000c1c2220001115110b08046001007400740e40001c03800c218801e0258007080d0000040c042169043d989140203c0a90f4100030481d88040c1c04940858504004100890b500340c0c0134049000504092605e84880743e1250001001c1d55031041100c107040f001c40101c911340c000d8944a40e0300e0140c410107802e083c07610001c0d4499940d01410084049a0241e100120340203403c40b024240003104281d54038100401c407c0740c0000c00740170b10300040800300d2088c0883c034842e40f826485641c02400d01031303041c224000b02c0172101d4045152050000145000802e4044407071382400c004042544030f16a203100b009501e4020480e05070720549007918110f424030801c50b0201c961040307002546c903181080c20b0801c440850008610394803a152800c01004001502070250146185110700362141c40312019042d002270b007070300c0d450681c1c40001041440 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 768301717 1250 768300467 768300469
    0xd110f0a05071505220501031a031c020a0b15101107090506010203130e010609051c020621011d01170d2102070b0f1006051c0603140105040b24 63
    0x4101030003052410600c1c5c00d509a0008405840e045000042d12495403070410881d0703050300c035449400342d0fa846000140001d082c0002d869080300c400c00314189280c8040b9081c141e1003031156004079035019041c0001402c111148143c0400100c0b8031a005000c0702c0101c5000902850403c005900c81d4002050315a04005180e0301802c80500154154070040c070451a0041240e4030b040c0152901c0706079841950300d03110000300f000d6606e510940c003c1071402402003040756921114503103140c0590b44665141804c0d008800d80c140c4a2510b00304801000d000410341440d00131503491112084d0000342007a98031855842191100382c05201c049038081d407480001f00c1c0c020200c0004000b00c1c182003003810030381c0c0750710310069034030074a07040b07690804050070031003c8a0804d18480c6c10112240c00340002e541401e001a0031031041440403414a84d5400600c000d80e1400e0700301d007001d15030181c424045e89224800040c082e01080c5c2d401c4450b11000d20001d8560702c0c140c4403680159034004030100e03040200f00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 768302967 1250 768301717 768301739
    0x304260a2301051e0601030b01020a1e0212060603010c03230712020a18060507080d020f250309080c0f040f0e16140901031a13050d110f0a0507 63
    0x40220050200c1801040450703500070f200d102d2041844442108402c011808640c8806000030500ba05051a014000900e80da00080c01103019510440114002d445559084202c441499000b0362090809803140c10200d40030440324002c0a0a0b8004d100080540c4400d600b42c0c0c1c80344401080800c3e020589001150b030021307000e6008011030501004071074080c0b80400c00e0341c0c405144400898511500c80c0e180c200c1200e400402041c0ca40b402e2820310f20240d60303980303642c411001c0201d11940c002c61000400380d480310803910410481800d0280103545403900150840c9000c01c298003180f080b900c0003c200030080760f01645004001e18003141d00302c0384402c020003890380c0c5819000d02c0c0d0f62818040080101046015910513110000003501441c180c1c03075910880034140040d009194510040001911100143c01a80040d80114140c0e5583c651440c04690f003028010300244540003002c0d000d140c0100200b88004908070030f0b2103200c01c50b103820590750f004440300140980d020480810181001c4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 768304217 1250 768302967 768302993
    0x510230f130203070f030203060105060a0503060603250f0e0405040c1a0d11040e1501020a1502070b04080306120712060903170a050a18030e0103050a060504020c0304260a 75
    0x403466090310300c6a03034020a1a00c2c104d038204005180c0310400610640c6000c000050040c402100c025107411071002c0028054000501141e00030600880800d61303202e000a0306c0e0b000b03e04244460130b02d0b0606444000c01c020818100c90b030125a5200300ba00913070405d80038142c40745030001e4001c0c1140d880d01310741115240d0110354201c59108140254803a009a6008204a1020b003001c0e03036031110308000d01d5201d4103401900205620b8000c0c001642c4a076000700d4044001c5400008000380603907085c0c03494020b442103480050440d81c5c07050401c000c02c0b2442c0080c500600081d41c090201c0005003030030999480f85070145200d41d03119245140001281038020101e03403132003442d08841c540c4024401101c0c0c5c0070203440b8915aa500d6100700444400c143c40380c04176441c40d00982e45402642d94074003a00459450210504045e02c42c40000ca54800c160003545c02850090000c40d903a0343c040e40d02607240c1d00280a4a03200810f0040070100c207880702e606051f403285080024114686c0141d4410081001c5 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 768305467 1250 768304217 768304231
    0x51615060503160303080618160903050105090706120c0819060b0a031a040b060307231303050106061418150d0e0f0313140303090301090510230f 64
    0x151800451152803c0c40881014050040d810148905600d4083e1401000074805801900c00880004900b8442c600c850340203981090170000c04a09a2811235007440c0d560800340042d0f003000d0030b00c400d5280000313280701101c034541e5541d02e4800c01d4003d08015500c2d990030141c0000d440a007c10301081d604400a40a0040c1000006d003455440c03d2103a00740d000001c00d90b01180d50b82220b8454413409010180c0e00c1d400c115402c0110481040003d4298000034210300100321600c84000c510024446071207107072100c0124079540f1640e0101c89805070f10203a000c00c03240c0307500b00035002840303901906080303032100f13418607042c0c0c1400e280803072000d0b1000360349441a0b40107200354500c40c50002104001c01c0450707003007031001c0340444100200c1e5103044040441c40155900030441d10202c0e00340c11049000740c2e80780603200c5000401c0703000024514041c040ea600c1c0d040d46440300c080c00304200000d80710b03003a8503501014440850710751120400001700381ca044000043c1c03100040c0307501443d500c0465000786 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 768306717 1250 768305467 768305471
    0x120f02040906180f02030601050301121b08030c07080d02120a09052d0f0105030a0f060b0f030103051504030f0509061b1f0b1c14030a02010c0f051615 66
    0x20766100e0100a40b2000e501a4811001c2c820050703280c404180240821581c54600039071850611000082c070fa0710051044001005001441100f0048005400034802034cc1c0000d08601c680c43e00342a5407281e100300d4042d4141e20070194000f410000116181030000801d4000c2d1943c2c0c000040d001c0300c1380e8404007640f410480310040c003061035030b54240b4030072203009500c50703003055081d08100104136901c0a2640e01d21680100c80c840c8075582c0c0c00801c89034000082c00e004600171101c0c042c1107010344204c3d0440741c06400b02103135591882c0c50303280242d03040fa0300500803203100b020010707800c40081d8000e80b4042c001981c440e8815500c1c500500043c6503092016040c1c1d0301c1c0004090608500035000001419a40c202000c03840a1100c0713104140c074082c044170b004101c65070a042c00500028090182d4134030700b2100310311107418440001071a2400411810a5944d950300c624070090003802110400710100e00c80c007640e0500503105a081e40d2402c0f4482c001c10b000e0700c8498544141144e18480b00a41d119 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 768307967 1250 768306717 768306719
    0x160e0103081e0313062915071505270706140910020c032107060902060708030703090210090305033f0f01050108090304060507050c06070b0906010b0a120f0204 70
    0x101450003140b24071000050b001079203255140100584604000e07801420940002521b681500301841d0702c450070040f41c403503941c5824503c1c00012402512030240c113080390445040c1d036280756500051311450428031416804684070108410441c0d01070480e041303e40c03020701c06000443c00340220507003044910480034100014100040c2010351a5a650001a0003041c00001142020408105462444c0102c1e079068150000301d030440b401041d0000e407845071130b8064541507465180840d114a9082405c49550303103000c010260240a024104a00841c0a80d4000640364469003500302644d0348000514500038000020803032000c4aa03c034018018100014580102214030046211000b0310f80b48010602d00602d15800040050303201c1c07410b00a4038020040008004412a004e9400600341191035802030b0800c23a10380404000c807290041030008800c4140400307180381c10301c00d090030400ca80451780c9400c00d6000c24019020060b01080222400300e080c06440e4100d020700c030101000050904e = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 768309217 1250 768307967 768308017
    0xa03050a0e1002032703030a140405061216030203040809091e0703090b01090506031e190b010302040b03011505010c022425020a0b030c090301090c0503160e010308 72
    0x2c05485024096440040d15030111204110380194022030b00350020742d100d0b80180400d490784170300e502c40c80400c604583c4071490b000300d100581e00079050281c03c06445070564101000007a000b0341d20540062424800000c0b5a4424001c0342c0c812580090709030b0504100f5000d0151070b010160600b018094074200038228000b02d054a0f0f0b1081195903404681a00c1c14205172000c503006801c40034100d4140070400c0015100090803140d0344001c0c41d0040c1202c1c40c0c901099007001840d84410703540b00300c014591000c4c82003410311681641e00881c1d0811000300341e44105400c079601c200c1001c4555030b64280401c081d41c000c940351001d00713002130500401d082d4440340703080046049000f059401000800c040854000c500340808244110f60045407510200d44c000039280242442441c03040c9170000001406c41c04408156038500328041e0007031200401d1443d02d40030603030300342c05454041d01c2200b07811802004450894000c85614081082031a402c540303c04110703902000d2188000b8001c000f0305010 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 768310467 1250 768309217 768309229
    0x61e170a09021201020d140f01051908160f06050307090312170a02070b06060418020d02071b0305160e0c030a0b1002211207080603070f090209210a03050a0e 69
    0x98203c40f0001079980340980d80d050100c5451003201e9145200d25020407510b4040010031506640e400c44440d0303002c1c182c1c1c400d00001490b1980141489010301200000380c090009031000582d000407035000001c0b07841d0481240c45010440740d19000902040d020004a11284540f210090242c545070f00c0701d4012003400002000c05403003103117220754009400010300a611303031150380080d030448890f8900340c5414480d440d51003a8011a9241c0c5c0e500190a013804441c0d0b43c110f50341250300c0708400ea81e100d1f0326810900744610922041d5154000c5003030300c50001030350407060000c0d61780d1086428201d48900c00c5003409500300a00742911142d45280c2d290032581c9070303110340c01c094403154018802400d600c04244883c100c5203070390b4800040d0034000904440251180a0b90182451a14231902d540e43d10009103031120907400030a100c0100c3c000451625141e0700200402001a0340d19010b80b509850f1901a03911804100f03c4545c00945054000038410070003003081061034a8003654440c1101c0029403 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 768311717 1250 768310467 768310489
    0xc0405032415100c291b070f030f020118140c04050c0a030e01090c0806090f01090f1b150e09060303070503040302010c170406050304060c2c120115061e170a0902 71
    0x14605030170b0020010091141c0ca0b058941500301c050450410f070b9140d584590020304104006c0500010f64520000c05100354410900c01c04545144410682c1608140ba07000503400410342c8103000380e0404802c541064001e0364090000104854900381c031480e0102e008104501c0d841d00c2c01c0d5220f58884020420041d2088003030040d04000d000c90381070007010b1700d04d0107405886901003a410000c00c4c2010404414500e81c915030800640410f440c3c0c8903482018410303154000c4401c090103007448181e1036038007401690401000307554a80003038695008061342d80c0501c042c02000c644c000c100c140015441840b015050301e03c01d50084940482004602401d90401c0d00144000340000c010801440014003c9940005030b0b42420074200381c0102602d0301a040002c40c0c05d03c4480304003c007902d5612080254200c01c0080c81c004c00c00704003d464116511b105130311499002401000000700416003008250600746840d45078182480c00c41c40c5000d9481d10f00501340c41c03c035a6980744507400350300c0c2c10050b04 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 768312967 1250 768311717 768311783
    0x10209060721030c09050d020f120d0f050903280609050309010329060306030f06011e061403070f0306031208010320010210050c0405032415100c 64
    0x1c100c2c802c00c408581c00c0308100c0d610b248201820120800300154025401c1000d031503050f2104404040fa600104e2528590720a5040d00301600740010044200d0102d5080c00340700f099911074846000054082300c0c07501130303400a2541900254880900d0548850041d10740b0301d00c0e02e2054564038800c0d02c0f200c0c01c59200800a48254200143d000170a60389440b6070140c210f0040e2409071907554144020002040c4280c125000340710000c040b4005075020402200c4014081046a04a43e1030f04820034080e1148a44020b00c44096080828281c2c090310b0742c914158801c80e0400d0950752000c00850b61103481e0301d846800d00d0382e10200400400c0004194002110158481300941e52540c030b0415000714940266503c00d0000103100c0082c1c2c0e07404074042c01220492100460300d41c51b1078030200e02c03a10850b4001a4180f251881208000b0003000d00f6040103007100b02d40740d0003a03031910140c0703003102c41520600e40d0018581012a4a1a01503007c008000d4014542d04da040c3d0900d0300e100c0341c0d000901c4126 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 768314217 1250 768312967 768312983
    0x100c170a0f081905071b111c030816140403051c0e0a0e06040b0a0e09060a05040c0506030406090c060c020a05190e1e15090603060108030a110102090607 67
    0xc9a40e034000d800368841c0070552800358010b192403005000466840c00d88102e03815120b40124842510030014440426504040c6d081c1c0c01c8107a251521403203d540420380c0c082c41c07180c0c1c2c548043c140c100204500309034164541c03000c075030350b00f121300c040c148120881c0301e05010000100321000e0510340094005144070784014050000d400071244c1c0000f003410041030030800c1d504514a41070f114810702200316101da11019000740c44020000700a0212900062b0700003131003803000076148401c1141a4004c00c2e03071000307542c013036246c40003a001900c004540190088003114410440d9051241c01503600600440300001c0c44c0149541e80803182c074150340300e4400102140c10110652a213402c1440040c04121040c20140344000500030346826548180c20984450400180c469802110207125400800201c0d0010b441d0408060200201081900f4060010400060008e0030700084141c141c0f5070392002036050402d010021950144c54840300c2441e55001e03c803c43ca185c40310006000d44130b00c11541 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 768315467 1250 768314217 768314227
    0x14030c210603010e062503020f0d060609060c05150408120a0501211101080c160503042d090c090e04050705010f0512070315050d1406090307030509100c17 68
    0x415094464180c00c20010f500b102040c0400038441e001401c61b026103001e80d48a178282c140c0001d0b002401900d0035080041400a40044040c0655001609452054503404001900c2c0d100850351f0300d03201e007001081139210b50800021031360354400c8aa4018070590102c4d01d0140c0000f1007081d691000d5038901e02e8551544010b109240c9220020045183e10040500800f010398580030360300c00c10148507605006c075400114070161419002c4801c0c1c6207502a902c4140300c1e4500c2d00c2a603a9115100361046080c10790600e8420840664000040580c82800040c4da103046c9040307071000f0005603c100050050700b4034001440c0c205070320114819400f4001400d0a189020009056105002c0d004030402c40c08000030b490390080c500c9403d80140003407400103040002103c200d074000d4500d4010350303442000c0890601c20000c0700c001030220f0444143c10b407401515101d100582d01e00440c04000d012410500c00007e6904000300e07080c0b144e0400349084031515200d03880c4c02d0b505a40c00c10281c0d00f11200052 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 768316717 1250 768315467 768315469
    0x1003020d140d1403150f03070e060405070504060f030c031b02100b030a0f0b0403051209030903150108070303080405010f0e0f010c0f051c0b060a020d030e0d14030c2106 74
    0x249424510a0070301c0003550704030030f04804603440010200120302e980303171031003000c0d0382c440d95660f002c1660040d00311134205850b4440010030b0036040311003034815818400001d03001d0741b1407010366085950341c1c0c80d507400c5a07605da40143d0207443c600301200201036480b203000c1e00b4515a00742c0300d02c00e000c0980180c80c00010803a10601541d0035542c00c0d40c041d80c054100c00002440b0001d800803c560410340c000201d0311946011542e074030038942c1061a500c0707000c0510420840100050041490807030860f540080c2c1f0b81da044428240911542e81c1c1508903a00c01c1000c01d005207007555019100307100005038a642c5003480b40c1282d6001c0110000c580c0005042608080d00b417265040314169030030113030402010403100134614400d828080c40803100c28104c651115000f60030905040c0c034020601519514000c800a548240c02c0f0010000207080590764a000742003c02e0b88007000e0860b60312007054a08040c80d208083d84090501d913a400d004124820b104c10f088408200e0b24060340440e64011f081401c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 768317967 1250 768316717 768316723
    0x30209060409020603040210030f0203150f0406030506011e030f081e04150f2f01060b030f0c130b03040b06041b080412230c07080a0512031003020d14 66
    0x10040c07801589030496a50160341e881c1c00b6a070f0b025134125015051444460000c130050100803a51413007050010082c00380403490301001190280090f54440b11900541c41008140c0c0c80d1844041d0054025800503c100101100e400005003882a06a84890b030385c1c1e507481c440c0040b8080180c40d000d5000c24440b0076111400c80d0408100c003005101c80c20130341085100a55280d50407001000d0182a14140b5074241c0649103204844002c03035161640030744010030512200408070721409107540381210101c0d440341c068080d83e00a049000300ca4500b980c800c440003105030f00c00118024904141100010041402402548175070702c2442c100300c550601c1070600041d107400e000207045040070306200d010341c59800410300b984290082c0b82014003c400c81c2050343c031100c00c242d02c01d142041010b039050103403030404010081c46265000311509940d17640781150321005540b5000b4459082070240e0009030400030f000e15040070743c07400d180034a96aa40d0000328620030341102110003041074000c20903111424 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 768319217 1250 768317967 768317971
    0x50f190c1731050d030f0b090f1f1a030912030702030702040615020c151309090516120605091002190305010f1a07080c01090302031b0706050304030e1f0504030209 72
    0x41c0c0c4180000c680d40390f4070f141d11603c20040307078000c140e610032070b030048030343d9a0308044a40b0324050080041c0c0c0c00c00c10088012183c00300d80c0360400354060440800324070760381075000b0200d4040c01300d110740b5552101c50782902648081c1c040205442404624042d00c0c15410055000300065001199508140c0c414001035582c641e0000c030040501442d406101a00402c001c035299a003101c81505c1d242c82446050024083d00d40030000c8403680c0e00f404a1075400130741c82002e005019a080b9460001c0446a02010004600035800100f100601400008450303070082500580c01800391092031000031181400c9800100241d40341d40859a84038071061b0b00f6108940c0504a5082c81034441418007034443d20311142d04010450a04e4001442000e01c00c0d8a4180e6484980041c0244400050b5080003552038111802c146009401c0a00c244821ba80014045003240d1094490340e0843c3e83e15102038511700040c480c110f030070500400900408c0c11145800c071858415940361651100d00314014000c802c040 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 768320467 1250 768319217 768319291
    0x20c15180325060e061617060f10050403020301110723061302060f0301170f2a04090203100c110609070e0403050f03040510050f190c17 60
    0x10420002e4226442041c03000c4500603801d00400311090303140007401890200b40c0b000c0c035402000d040c040202000c4207250403401301340d66852203d00c940200d5110b8410250342295006101200a840d40d0070641011003041c1800c0c05c207581030940d01d402003429a40002c0d00240b40040000d007003403c021310482c0784410060349840308404000441d140654070031014100500104d0480c000008550302e030b0040341d10140b003441005450b03580d030311103000000c601e04103c8861806030014028410720001000540c82c2c550385000c0c50b882905414064036244100c603182c2c2c029842d0700781c400240c1c5041001c9029561038520004200c406160000d20300f02e0120300d1035041d41c0204080c0b0110030000641ea0040d1141e50f844c080958440f440d041e81c240c8110600d1f4098271101000304003e2010225010300da20364496000d10113961a240c000035203400444621108036252941c12004d148503034020409101d403410301e800141010103450804400803501e810b00c660f24039546101d40d034580ca0b200901200 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 768321717 1250 768320467 768320473
    0x201080a020702030a08030c0706020c0c030c030f060105130e1902010e03070303120e03040f0906050f10050319060b070b16020309030a2d03020307061113050f04020c1518 75
    0x2c1a400240c03214001c10b00500310810200110340032880fa2012070390003550000c82195542e810744101a120303889608110f1103070052801050740d5003000700d414034024058401401a5a0821041181c074041c00c80749104610740d60083c0040c0386801b0484010700c0c4101c0395410f0720a5034503100040c1100144403645019802584040000030340201103598240e820200105a08000d50700041c1b46001d00e0384040242c041506002544031015444101580e00a5441c05512030214051010396417001c2080c20025008200050402c1c2c20320a81d10f6590300003c502140070b5540d03100c1219588c000b00002d803903500c1729809005040e96842800031802c1d40300e001a60502d40f0040000380c50341c807642d078041c01c0c21800681c024002001e400c051f00d0a144c0d4154450541c10321800c6c000d68030341050b4001c4840504c5c0171207035132500c00c03913506982000e0f0ba80c0c040002c04c1801e10052081c142c00042e40150016000e105200e410760302441382c04204260310000410600d010300f1414001d0001c44903000c1150 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 768322967 1250 768321717 768321727
    0x3150b0406170402040e0604140105072309010903240e0714011805220e0604050c12010906050405210f070201110a14030a030c03060b09090402010c0507120201080a02 73
    0x503401990042c00c071141c444841e00c0c01d07903607400801d018000360f6420000354001c03036041100300b00340030790229250301d03a0030000c01155a41d400141c80188864684001c10360405103801e03c40316244004000c100010314103c15582c1e43d07a0350700122403a8506100e40c0701c043c80034807051811603038410f0038122104980141510341c07914880f5004814281d0440d410024400750050030280100ca1007002400081c0c240d6000c45070741622503255203000000582000d0606518002e12400003031464001d54000c4040e100e1054503408012800403c0003a060007035403110034460126a031031254501c664050000b42c07a030196003000c90395520410200424030300606101620320300d150070051311182036080c00c042650b24008803030203140200002000345110320314400d0380b51010f4080013404540400380c07001d014801a0103800e4068a246016402c0d52107024884102189401c20040f174205006050038a2607800f1512810306204164100b003044c0c400341c5041d101103507804100160301c004100c0085083c2 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 768324217 1250 768322967 768322979
    0xe0307020a0b130b0703020c010f0c11090907080a1406060904030512060427030e010c08071b030203032110030809090402011418090106080f0a02030702030906040603150b04 76
    0x1d4201070140590070000420203a9103c0d09181e500e0029002c2021801c1c1c640c455854025918442180028009003042c0b8a28600c580101e01c4251110f07030010881400c034001070300703000d00c4143c024000e88440c8034242001500303c1d424040d04810314001e00400608190301c107034152810002400c00c0780541400380070000400da0140680710035080944810205885e80b40004014115000d4001016020380f941040d0611845080d040e4080c4070307444009448841c41d0055400342800312340580403000400c07443d030002d5940c18000c16100f03035030960090055242c0d00401d1540d08001c0c02c044040620404903000c0304038003001141c1c0451142e1240c4c1266003540e03503100d024000c01c8400d07030059400001040031680502c180004d03e5103500062074403403c07250743c9000120345521b541d500410103080089200d511815200348560050541e0400d03039180c20051380000d5200400d00c00860005008841c0d459880e14004e00041040c0e079408110354443c2c40ca0600d1503d229806091110700c100010012 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 768325467 1250 768324217 768324229
    0x10501150c080702010207051003090b090613080c151003030207150509040e01200405010809010b0607030f0c0503181c1101030b0a170708061812070f0b010611010e030702 75
    0x203250b0310520141d15050381d8070050b45070403001d400043c1d004e0461100c0e08030f1988d1690008001a000380388034039050711240c00140d150315040c0c4401c288448a01803460104484000907c6006800320449104c074000c80a003290080042c2c42e00c22190040706005c10905504002c4030002c1c01d640020340040c982c1c0d252002c1c120b84a52841d89001c1c58560680c401c0480003944030000b040303000c210a9240802c040a040105d900c41d026040c0440d1460011803588803052098400913000030300524582075a50b00d00750394031503102d4107100130044609000700020f01c041c0042d02140184c07640042444071180700304220400c05404000329256050707455404a071301c800c024101c0230002c1c01c00180351901900800c054801c1c9411101c0700503522018041100c6000540c101140c2d60030050301d02d540c0b500d0150b143d94100c034124a02e416807084005182c1118040c0003490079520584405601d41135035511403110141c26131104000ca600340e55200640f500c00e014251013003141e0000765203404025400112 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 768326717 1250 768325467 768325487
    0xf03110601060216060305190c120c02070b03010905060303041d010306050114030a0308151f020c2205180f330109020a0201090c270203010b0d09081303050f01050115 73
    0x3015100c5020a101c8c800700006400d140540401c01d001c1e2044d0741e1030240c400c03020f2200284e50b1614000a600e00e0a01c04140c5205036400300d2003030351071a40f03000e0880300545806418107505010070480011118481c50113085090406400c0160540c03640c1000011508142c1c841e904d00910605240c0040d50041019010603a2600b04051a6203510411940034200c4040f00c0340c06c0032440c10039590b2078402036002543e0360400e032b0898200002da00140b000d03020400e0404040304000f03000c45a0603140940109a010000305000300340748807109206072803c080910700e100107810851904460440380440d40c02200280c640030500071048070b100c00708081c0144035121003d51b012400c03d40c003610030340050381c90a4029182c0c0d50300d10707200c3d921841125912001c07602c90100c03409020140310118000c0c2c80c1220002141e05051111226820010b40302205044070b48040c10070001401070032042e000f030041d501901c01040d0280d01d9910325800c452040e00540e54140790710751002c2c0660f078094481c40c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 768327967 1250 768326717 768326729
    0x40b09071a161b0b120a1145040c081e090c09040506010602160e04021c080c0a1505010e1603021c0207060f1a011b0f03110601060216 59
    0x21200c90b1400d002d01d000d411030302d035581190064800003d030b07804842d02428a00030114000501512050f416030116903200c1e00c0c85a80d01000c0c000d00284504580800ca05101d8000803502e5050810840041080394603240c44040001940f0240442c10117200c2c1804089c450704021950f400c05080110001d20300d0301001740e4400c2e5540028040c0d00041c040c5124804020f0501c2a40303050900d03016803030380000d014010062190038030315910018200d030300c081102c03c204003003e2a916a81c007440000c00c0e90740c150185507942c04078901e00040081c0014035500c0350003800360490480c14a4523940c541e0b41d07001604581ea042030b006206040b103d50100740c0003032082c2c1c94140645150f00095006e4066490009501c01c40103024810b411072607001014504d110350402c000e03080b40311041004440e1803404402c0000c030105503001c419405810f4541c050346c0f950340300c484100b20700e0b0381c2c4d003100241c48001240010310130301003038103c59002c0001034050402c03800642200c41d0095540d03130403101c05110320 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 768329217 1250 768327967 768327997
    0x120f130b042c0c090d02040c050403140a08030a0c020f0d030b01020c0906062b020a030632010e0301020d1104360506040b090424020405010503040f0812040b09071a 72
    0x3c01559170f1031142d000c000c0ca501400510503902c0184c1c0c05080703034106101c1610342d002482124182d1180c04074100ba5119482484e082c2143c4620700d6860050032100001c0c400e41c030480f01e6540c11480c0402060b400b4140661300800d8841070a0300090401c3c2c0d141e003140f4050300c050001d00c0745960740c450941e00703042c650540104c0d0011009249150a840c24110b5111540c80001d40d00da80c1c0740c0c550070140540342c3d401d002141c450804d44180078100d810036a044a00217544030406002d42c4034000000107080000d00140c10080721049410456000124024040500141c104064884102c6102100a00038540d040d00c6214907100303808540682e0300e80703440725551000101559203503400380d410050050117070205803805180c03030000d1040401c4a82c04400d004e0450000d8811b080c000c54081c0d0300107a64582c1143c459503503c001c1280d10741c0003219035132070038031a084096200d0740308184158080e298000d030038182011114101849500100382c8480c0c80d66902c0041c1088400300c9551100118074 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 768330467 1250 768329217 768329227
    0x306061706010201240306050112050606010e0a0b0c030405100f2a0f0609030305060f0f0d170f13060509012007090f0e060f09120f130b042c0c 63
    0x100c2c010b10305c0c03a040600c0003207103041c0100351101c802c48541c00e50b44544001c02090740c071461b04a41d8480400c03001030440c0d00c00000103046500c070b07407110001220301078880800161a600941d40d140c1118200308415440420f0801c030f186402c03400200e034907140703081c000044d900120300244910320006a20b00f820140d02c0511540103880740031092080d030000c200140841652400300041c2164040640010f4101804a0f20702d25154403880840c07000101010314182c070807824000125110201600e403011034411900107104040002d00300c0c1c090321001079035101504001030f0f00d42d08244e04420b08008041c414441c0c2c0340d800c00d203c4204c1010340c4840112109000341039910f02940c13a04800b1204d030034a50040c500c0ca0f125000240c01c0f048800594500da0780302400240c01800072203034110180d000402d104154080100142034a800c507a480900c0c01c5450404519003203400d900c103090410700040e0400806c811700f85208131580d2044a6031140e00012644800148400390108203840c1002035 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 768331717 1250 768330467 768330469
    0x20c21040e0921031e0114011b121e05181e040609151211060f1b030403030906050c122506050a0b0d2004110c0a030f0306061706 57
    0x43c03440b07041540d030800c65900340e030301e040390b0342c0d0016941e40b8145404881141202c2000010f054181d80e180c2958890084c103c0c00112215074401c2080348a0720201d940c42408601c2c40d101c2850a0041c0d80c841c0240d05031515600030f12030140c2d2400d841040780610802080c58084240c1103400f20342210300318503203504503c0c0800320206511150364890b14001002078152401e41040c1580401010064141035441c0da81c07600700d07040078030000d0a04080039040400c52400b0006070520300200c540450404807038420040d0000c408448003007080d0b00214042007017550000014001d05550b00e4024144050070340d40d82d68803101105140350503100490882500b0300c415010540791801c80354030500c52009403c1080c020501540c0060489050007118121800c1500f0080009940041000c18855286541340000440202e50716403294803000007a45186003403000e408031103080c101a019003207035450050084032691810310300381803d29030300300a4143c001c80713000c5555401200d1080a40e55440c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 768332967 1250 768331717 768331723
    0xb010b0319270b090f030906030402040f1e090203100c0c0b06030f1e0c0102070503030d05040507090f05090c0312040b0d020c03030132090109022b020c21040e09 71
    0x6440341c0440b582002144050040200700d05028242010564a44001e5110b0858903071140300d54044d04040200702280060609900c03101c13191820b0b05000541c0001420340c5038410810b1840c460300c141d16418480d0a62800340001d400c42981580108200c2d88088805010fa180030440600381c1c4152a000a503192800d2002e03000c08000d03d800d5841240341032401d0b644941c2000036084a500c038103207240d01c0b15400007540801780d4000400640c1401082020304002d044010011141401500800100304c17032039000c0c25001c0302e5030325030209052505840d01c81c82c11000701902842944100706014412a04074100c038161566038069950b19100701041501a210310320000441d0700c8000000a035101c46010307400c465070f101d01052048800c004404400215025180f66444000303c40100b01c0c0c0d840c40d40c000c201000c1550820070400141c1d600b0407205000e210248040260000380d012900c08081c01620030041c180d410b2130a04141d0700344074101900450043d00440b501840121382e00079010 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 768334217 1250 768332967 768333011
    0x120a030e1801030f14010e0d113c0a0b070e0d080414010302070b040516080d080c070f05100f0b12120705070305030403030909050906060321160b01030b010b0319 71
    0x1700000d00418003080c80300c640c0c618901010308000780c50002901c49001e00030410b10118504040d801e4408010100c00300e40301e4110a410348041c1c210345034120500d907018083c0a240c5405a000c20303d4928103080054803080840b00d10700c2c400c04d0941e071100e000a4014041d00d0030b5452072694181ea0320000f80c01a4024800c0d100c02400c0c8a03118000c100c2040400103200712200c00c4143c0302c03c021641ca5810070390311901da0098201043c40100040e80303603410100a89256170081c40c4c9200c000c10f9546030071f810b00800004060705980c075030f00c1a406100c0a401404d280c0390090740e88182c08070000d55100d44848502484640b6041c0000b44c100a0007010045a0b015540040560703a650350ba0345401303801020a4402c210f90b09045c0310000d01c9150300800c2040c86804082c01818940070b022044400340c2e207403007145404040d814040c001074086241c0c0c01d036022601c2080c1c078140950450401009854050303000303400b00e0030700304100a050034100d80a04405903082d030000c544031204221000c00a880 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 768335467 1250 768334217 768334253
    0x90603180b150a0f0801150807062d030c030c020a051209030a14010b09012c071803061a03072601020d0e06041109091203090a02120a030e1801030f 65
    0x1980b1000300b04100e940444c001261019030013000358000a258002d0541d140f8032860742660030080c0100000750091000742201040c002003c08070003a482e03105440c2880040044000030360780e00c0514500c3e5014800c4560352081c900050610300c20a54841d60b403a44483c00700c0c03014941c04960a1f0150300d04002c44501e0030350060381444882000711105000f440c24401e401d100e242c25000008401c451440c018240a4541c840c014001806800c1c5001c0d4040160150f020403200b921148003682400d0820b101440c414040450440724100410418503a400c440d07034803030341091000300410081c0c080002401c0043d107091001d000702c400c04540c024000c00030711549003400d0010181a080d000724050b403045100ba8482e80e403554070102485081e8070100e8510130039a200141841400079000f0165501c16004000ca8900a000e0b41c08035841503040302001c0810f5028000c4402090f403ca440c01c4c1c440c20007660b041c51304250240f052046400188405801c1e280e14603000410b00c000540298100e100f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 768336717 1250 768335467 768335479
    0x90c060f120c0a09150f0804020d06060f0321051b0703020a03030e04050901050f180c18010608090a020d021201140c0915070c090b06070507030b0601090603180b15 72
    0x35003800300d01120751010a4000001d000321001013009191205c5149108190303a652440a10503460f00340da0f4004060700590303009420b4000c984c00100c40b8010403007d4918082c0012500745103140c03c00300d0440d113100c0c80b0064a140e03d2800102ca511400341d03070030019074100c01c084489007040f0087c2402c60030b0300080e4000b04a07150100600d84c21102d840e90780d84041d03270700700300075a070342c03400c2a00f00c5000b510000c2090308040e01213402140800154030041d500d0205980c420031510001944104130b26142d2548014440c004114183d00105c0721684541a1400f4217491405072780040e440600404c0b00901c14003e41140c3d160040007503201807a0360f4190b110306096402c1058031148a90081e00b00c0f1403040b0310f4020b010b0540318000d07050f141c0c96a03110f0000c4824500740782101002e4038041240700d80040c400d20518003c20740821440b001140954883e81550500100040c49420103070010000c2c98188042a200fa040241c0b00300c9070f040e00410500180d460f628540311030f401044000ca58410 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 768337967 1250 768336717 768336721
    0x4090e150c2b0209130b0109050105130f080d0e1504120611070302011b03020423030c1504030c05010e031c05040510090801050f0f0114010e0a060e030c09090c060f12 73
    0x102c4190300400380584201e814100400c3d00141890a94001e07100042c001717104072104100c5035008001a001daa500010301222107034a8100207440f240c45a841100c0c240d1100c1020b514240d089250115482c2c4142d074001d4403403400140400c001c3c4100d114014103520500b0696040c03020340c0c1d00c0b400d110401e040995550361451309000f800b80c94001e240c49010640181c24410140c021700c00c0720111112140d0000c0b440320501d80c101c484400c6c182da03c640500070702032040129a10004007500c440d5144010742d03211415400c02d288245025008141802040840704c000ca03a00050503003c144044a0f01860700108180229554011a44003130b8001c0000d04186089907001400841a510a94002c0100b6075400741000c41e184015515150341800c0c6070014130201420307254411000324107041c010900b800300070100f032500034550700c050000f07242d00d43c215102d0329091000d490302207811182d00b40e103400e2000034943c9801481c81d80602c1543e0004000300031900e03001c02c2d1840e603603030055481254 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 768339217 1250 768337967 768338047
    0x30102070c1d070201061815030c030f0b011a1b07050a06020f011803090303050309120412020103050f0c190903050709060816080c060d02190504090e150c 68
    0x2000c02450b411400c841480002c540c0d030700c1403180308211b0b00340c0503070401130016003003122004080024000380840a4198003001003409105981d00452080c2c1442185406a0030b050064001c1a001105c800c074503070060801a0f000401900d02d907003059400514140308040740a4035160b503903480260030491812000a2460300410000a07980c400d0009100d590300c0190808030115040360f000703000c580703174080c10300210b442203000e5944048284220ba80c0340c00389007107160190300180e00041011850700081411560305000e065000200100842618100b030000b8001c039019100130f50708242c00140444040038418000d080c0215040001d80324030640b42e160450140a0038000c20a26209051340700608130903280d4108201d41d007a80c00b6003a0881d43d1020407a06034480b42981c84003540a1000f4401c800c0c901d051203400144c240c4860383d446c0e01c2c0500c02c0c41650121703c003115454000c400d600c0c074090151000d0503072154501d021240c0d109000c001292030160b244181c00d070007200c82e146030700070 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 768340467 1250 768339217 768339239
    0x305091318120207081f0504030513090b01030c0512010504021606090b150a0e071803021003150504020705030d0b0105070b07030c141809101814060d02060315030102070c 75
    0x200c2e441d03d0307003660711542c0c80c0c124031655890151a43c4290030300c50384081c050500107a000d6070300305100e0f00d004c070700e030225016503052810226005504102e035101d05c44052903801d40b003172480504007030805034148900c03036208864040701440f615000740d40018132000b003e035050801e0522258482010486080a81808011a0421902100c2044011446002600c0d002c40d9103000c58041201290aa5503810030031901c6210401c9400200c0080b9034020005945200c80300f840803505550008020000141081c02d40d185580481e000303500c100540d20200360040200e80c002c40c0e5902000c5444d0740e030880103e4651280040250400307100c03100340b002865042e000001804000e1350f6400d030020722400e50303042c1440741c0300310760300c41d5240044d00c2c3c1c005003410b40c546980103100c207284206560361102d24013100e031a02001290b8542d82d40e0307109101204085001030304600c0c1583d07040202c080c180d020541603c4080c0400720f2413400c01c509604559001d40444480992200c90b00c68840d54070b8600c020 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 768341717 1250 768340467 768340493
    0x30201111204060606080402371e09060807090207081e031506030f0f060d060515041104080a030c0602090a0b0403020f03210d0e0f06010503190305091318 68
    0xc2c40e5130401c00002480761181c000c0500690b00141015841c9012030040a40b00741d40340c541701ea400d41e400c03280034408510445c280c002452800d403204880b50744400500310a41d083d8000a0a4501e0007005000c08070000521009942c4859030050340c0d1a43d0341000d203500e00600c0820f014104130928040704a01c41d0134090340c05440c1060300d6810180185042100030301040f9180180b6180c00c1001412a100901c403154000c10050f00b54070100d82545c0387c21050301c40855640131010362880326020702e42480d10640076100110740c145070030305003802c614540354584600301800300705815800c013080c00490703411034100c0d1200815004500341d4031040d4098680080c03009070f00c68400144400058100844d09c00041002c5002d6203103e4890740c0c2a020030368002c2c040e444160384d44d55190604481040040c038800021540c001c01580d89400e08143c6406003615818812111480a42d40020340000940ea0001ca084a04050080c5104180c0d0001d1012041d40480444026139031414415200000c003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 768342967 1250 768341717 768341723
    0x1050604090809011d280803070f1106070609030905100804120305061906030f05070507020d02040c0c14070807060203040b1207030e0d0f180605041206291e01050d09030201111204 79
    0x45099642c0c0d07e6220340b60700030101c018041c0c01c44070403194001540000c0204800c040180f01500301140d90700c82d04103e13900740b407084021603c04e01c0240000d01c0e1100700d02e017110005103000c041502e80b0384c1d80d4082c103083e200040010b045d101d50100d281a940d031051001400c070b000c050740c0b644a50f500d400401401d812400014800d10704400318030000e114004580202e40c02401c1d00c01441c0c0d240d420310005045504400c81000a03110030707000051445400d0485503940780004014550900185901f030650780c0d0301075402d661040004102d406090f5058480446104400c11019595003100340c0107080c400040f504280507460080a031203401943d86501d02e00310780c1e500382d0030b00540b074254a0418018000e50000c208203000400c00f00c0240d0044014071440b42d03201141d0046c0312807a1203d60100100c40034a00c500300f02c4c80c0241c0d401e003500c82c02d5010712070600c64200e141011001030160310502c4800044691581011030130b150007500031904c800c0d410078442c1da07034108100b440012035a040e41c0c22 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 768344217 1250 768342967 768343039
    0x8120d1503050d0210060e150f01020304120b1503010207051e100618061401120f09080a020615030d0e0909011d0d171b0711030105070e0301050604090809011d 70
    0x303d00c0d41051211f4600ca00c092107416055140e2410800c03c1c2c8080451100d41148006c002c0401c0702508280444001ca1117499030300814101310202c404092007004080340640c0c41403060f80d010035000180600300b0700080d401150800144c810150400c03440c0006580714504241b0006030b02e82c1200d60661a5080c5031038200100c0d91580c0780d240d00701c0e400079100f0380022100140711740a080310382e01c54041a00700100020360404c0e1950307031b48803a80000c003040000d40c2040c420042c0c074000407110f0048121080f409491840707648500039059810b0a0f02060149444c100024205902540301c40b44859003510b0000000c5000a031280c1d0f900e241e0080300700083e404a41d02d1820941c0096403501802c140d4020702418410442542600c0c0c000c0c82080d20b0083c80d0200303000b8113440a11502c2d0007020301c3d0f503a104064007040c06050a40300d000d0301241c00345141001c030038007042150007503900d00398003483d1240c182903c1031984003021841c14003882d40240641542001884901404510080c0071001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 768345323 1106 768344217 768344219
    0x1060f05180a1e0e040506180c03060a061a0f0a03020a021507020303070e0d030e010e0a03061e0e03030c0702010315030602070f02030708120d1503050d021006 70
    0x1d11034000c10380164062100c403c2e51501404821400d00c9075420940d4174a42da402d40100346065041500070010710302d10081c0840401808010211465800d01c01c0b64800201440c1c03049481900e5441601700541044001ba6609600100c480e10b003815881c00e4150007075400003460008600443c14081d141d165012092406082558001c541701c1c60301c414083c00f5042410403040c41a00b0030172a0100080e4024071b9801310013020720708401c0d00c03503010000ca001e0300c5a9800007480c0900b030840c01f03c2e0400d200410500302c040c60f00ca050142c149003000303c54a910064401e441c1121041103e00c0140d4004c0c0c10010030a0031a001044c5410741d0791301c1e07040480c1c10469040340c00f2175410001a0941c50104280e00140000002801229034155000d41c010b01c00c84990140740c40c3c445000e41e0321807504001c00c00055400c8410740b00b000000040c000c1d00e4042c0911306d0060245030200c = true := by decide +kernel

theorem cover : BRFrame.Cov 768165467 768345323 := by
  have h0 := BRFrame.cov_init 768165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 768165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 768165467 ≤ n) (h2 : n < 768345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
