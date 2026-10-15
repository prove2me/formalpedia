-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4967
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:18:45.605833+00:00
-- url     : https://prove2.me/submissions/11e06ab6-13a4-4864-9c0b-9a56a168ad01

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 893165467 ≤ n < 893345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 893166717 1250 893165467 893165479
    0x20d11041a0a080c0a0e120c09010b09100f020703120305150109030803063604141b060d0207020904060609110301051807020307050604031e1e0f181d06 67
    0x503010005840f0b00001030114034036140000316000d22a05c03030341000b01145002000001d01c4410029540c0e6140c2d00000090701401c440c10020500021038816039001d0742d0300400401e81184100c0040310271030021100d16003544110000407000915902094021003000d5500041707514082c2c080d400c1c0801c4408145040c03284401c420320114400404880c1c2c010f2003a100000c400c003004890bd01c815101801036130144607141121078201c254904214011070003911500b5003105010b04068596100130030400c040d0a048004042a060180181c4204552242c0050a2400540100381101c60880b800c840f0256500800e02000c1e509204614240c1c0303c24005d6410b560601d00400c3c691500381410001c441c0c001800512258400c004071800e00c1d600c04143e581c14282450003401034160b003e032090f602c1c421800468031381c03446040c4002d96141800318249000040000959410b0b84401d40c0c0350400000c80c8804105080901c03000c00108052040e1805007050703070400420352007000e8031a921400d = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 893167967 1250 893166717 893166727
    0x6060c020114160812090d0f05070b04021309060605090109061404021602030d02030a030f02091c0303110a051305090c030a05060a0e1303020f0f031606020d11041a 72
    0x42d91000401944030440000603a640220f900705440003000000020441480080c03401c540c02100800240108844022501038a5480c202a902c1c1c2c40e04040150001c0ca0500c051800304503030404098005001030080401c1c00c0b108100402507881d549800d07515a03444003070803c203508040d4a0700d070050011400400c40076051100e850b11201d4070789078280c801d07600130401916211041e800000001d60040c01c4450707111051501944a40147d117030703c00802e10348005184140c41500071107080410040141c50840500d141c44010945909416000c0690b40c036000049a00d0b804014150b200d07140d00c40a4542d80d04803d0b180c0d1107981d43d0003103400b814084050156001d01c500680e6007041108101084a85d40d5001142550095504c03260102d0b00000070310410500c0740152a0106000c0d5080c0c82d00d680812181d03980d9170a55000300304555200b00054072052169030710b03260b0820301c80e01015103018800c0780d0042c00d461425540500a000000c3c0410882c200354450804a503444c03105a4280 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 893169217 1250 893167967 893167969
    0x90f04120e0d300c0b07050f09010302030a0e0102041e1205061603021303080301140d1709030705031203060a0f0819030e0d23060c070303240608070306060c02 70
    0x10012400340241160035419415481441c07000800f48400c101911983d9040211a402010203c12500c180c8220113404081600e09106401302c40c0d4150a201d05140b9000b43e0b000110001e601c010305010301160344880c1c0342250742d82800100002d1103030b01c03403101070704852010320a8181070399804070188100b100c0341400059408a48280c5c0710b00044403201d991104070740d041c8c0181c41102d04030700d00d25050700004010002e4500245040c0c882520140c0c04501e040e20070301c00138540400029180f40000391041c819465a800281566003000c0c0c19202c0381503032000428641800f10301242d03d006008802c221752803c02074020401410b851101e51034840c940080c4e9078465044400b0000b81512020300c0c00c0a15028510010802d0070250149081c1e804509254445901d801000d1007035151083c0d10200000b4001072150013041e03d001c1c403500c2c1003002c1d64141c00500803487d01041c000071050060f0b0143c039410f41103030010481c0ea12040031520300000003c1c202c4040e50812014400d81d5902c61001d = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 893170467 1250 893169217 893169229
    0x4030c0c09021b0f0c01031d16060801120f06020f0d020705030a0f05040e010b0906120702071701020a02100e0c1201090b1810090309050d050709050c04060c060f0902090f04120e 78
    0xb01c05e000e080c0002c420071007a4020001d0000050010318070301c42c0f144151250000c41d40b1682c211040d594a000081c3d0325a0245d03242086244005000340ca0f0101c900000700b0819070007400c0e00d210003a0340500d444821885041a40c01010341500e0640000c02d04100e000e401007031201c2e4204907881c0036890103080c035980c02071004044c054007240e070030045480c1007940c50301411145800084600c4101c2c0d80350002c3d001359155094010250030b10616130f000e1890050500940340c0601140c2c018044c17400703a2451410040220742d0a0b0b001c50311814481151070741703c10514802c40c220030000030171031030750034180284281400742c11141d55146a001c40344544070045003e0708212640d1002007006492400d00703d41a0340140c10160380950b12002020030028001b0394502125040300007031060303546440d00e4038030f03501940c03090780c010518005034000095015803003044a5012100001048101074002c50b2480034211400c007183c140750305c1030009100c107182e040110b92202d450001109080707000441d207 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 893171717 1250 893170467 893170483
    0x504030807060e15010323031306050f1b0d0e0a0f05010305060d05121e03060a1a0d0f1415060a0e030f0a06020712090f0e04030c0c09021b0f 62
    0xc5040c1c0d84076214103604005002c00c0014804c0400348129658481c20030f0000003440a08820342100d03000310300d000980c0d01000b580c003640b0184c02100c4e051490810142c5699200103c910200d04040215040f07451103a040c2c1071072450714500034001004a101c0103403620242c00c01e590b109030304120040240000c680c0e507c500307641d800c1c6008140358035840c01081c0c450394007c034001c10310300034126000512851031014184d02004440c500459244c19004040d5910084d44c039680c202c8804078040c0b241c0d4210b18240d05044045032185440c104002c48554100c0e50040c01d20b030803143d01e6401c408020040340340c10540151041d8a02020008007100044240c031800000c0c106020000d04401070b1564244411009000c1910945000074210f16052000b540402c1d400c550481482a680901c00d100c0e26404c4103a807080780318400d0541c181251a20b80c2c03840104214200b00d5000340210018a11400c4440203050386400582c9500407000040c202c01250a0441c6980c0e004801d0b13601c0030440060252 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 893172967 1250 893171717 893171723
    0x40c061409090114041d0f151326040608060a0603021c0f0204080109080a18030f031d03010c09030506010504090b0c07051e030c0c1503240a0303110d0504030807 71
    0x7001d140000302c04540641078103186d6800f248120202d000c0d240402144103904141410300341d903c010008010801840c0c4283d5803c4505a01c0b0010000001c800f01c80c0302e0f08448003004541a10862902d4002e5140c5c80703a00102d00145c1f6202c28001035007429140140541002c0c103084d410700150b80030500c114805062242c0c08907882d2100590030460030b9046901410a010081c4008006401d050307189030b12400001d00007504d4403d01003500305c54a1801820b40e9030040314004442c0c1e0586003202c164410800c1d40943c1100341000712601d079001d100e444a05151500c03004061403450a0182c28100141e02c12800b0364107000190000401460b2050ba1040b8160346507611030240b41400e030b00e07040001000d098103040e49440c1c0b882001002020f00000504001100c03000381c0003009000d01c100382052910500750007480442c0024412001039241070000313100d110300780c003000c1001885100c00c5070b006801094000d06541f1940800740200004100213003000740c9818034559502085224142c03010f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 893174217 1250 893172967 893172989
    0x8031f060c030f14030f250302040314010624090e07020f010c0504080c1210090c0311060f0304021c0b07111c09050d0303140a0c0e0103050609061e0306040c0614090901 74
    0xc103d0b4000c011990340b80c1ca201c4c800c00d207611f416800007030000d501c640025160725011407041a10322005008807015500b0005000300000c5500e0511046041c43c0880d050a02a030000007090301d00080146510441007540207021031610f03d001d89003158000e8164508003c401c000c2071202030000110141c4080050351164501c0b41d18140b0702c0d04110034542c0025050f41044c40d000103100c08040074406603402140f912000b1014a8100480383c0324040e0700748901c01061001502500c1c0095541080b28141449004d2080b1980d844032001c000c2140c0d070401040c2c07181c90803e1900001c025400c2085000d0f401801071790034201002c2c00a43c0d56106285c45514120008002c2500ca9000002c441a002503c1c0819040c2144200c014200c3c0f4050349000071020b4810481c04e40c428001c60b401048060312500f00c540340c203014843c1000d009501c0c800001c819000f000d01d1500d003080b200d4852030041c1402c03d004d03402c09900a203990003006500c00011010301c5400c200b40d0b01c100f0040d044500320496 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 893175467 1250 893174217 893174221
    0x21801141e0f061e2203021311070b0403050a0905151b10053c0f060102010915051006050a0807080a2418060b0708031f060c030f14030f 60
    0x500c80d00c11080c0d84c100000700c0110142a560688003d4554020b0380645404004503c0040348400301c0144030203540f22a2000c90048020220341c004941101d80c4440a450b080c4980c0b17038444c014005640407000150300041d10480c20340c1c40074010024000898103e80b40180402c90a0741c1c0f4050a034003801001004d540756516108204090303071303144000310b20a000345d1130200403003031304212200288c440e5000016200305000032005c5c0c14501d550070185504442d0385070041c40c6031100704002c000606641d41c940380360001c9056030184151046031302c9004911850191100f800811641d4080000d0000034040c0c4240180c00051495201040c0c1c548a1032980e54100880701030000c1007500c22000c1201c1e4128100301c40c02140141c1500d000a09500c41c03640d100e2241005c072400da01c0380880e007840904c081400181704000a40e08102e500020341040100034416200404032544140080f40713180708018100364011030045903442c0c980c14000600705403400e0352182e03444002c150700ca000d566240 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 893176717 1250 893175467 893175469
    0x601030204032103150e1308130e0a0b0d02060708071b030605070305150310020919121101080f0403030b12010608010c08160f08070c021801141e0f 65
    0x206071401950801461040c0703180e800d45410840c01180351038000207062151000d0320f4001c40540404039a81980c41d19090350303540c0c20100c81320969140c11039148500304105881c0d00c01e10f11201e400b800290201010a0803c220480200c07030700d110700035004100004046015a0310841902d986681241c1c0b1140c0d902d0b040d28117070f4030040500010300c86003900e0400100521410790302c483e00c03440c09038800b0006500c419842050031040031594030760603400000318429100941d0080c2c4800e04002e015003441c0310880c2070880c0c15140f06c2c4c0103454060360711aa50001c1c000c034144407c807903260070708103902a410403458150302c00100070005014151a4640c06206482d081d514020f00d5505000030071a4035282c01d5054040c0160a021304005a1a07002089141208800e0304400d43c503240c489031014551500b0a40300c10f0340040021044c007000e4482e81c00035855513205102c02090810038a5110343c109104203400314081e800740c40c01000c4c881850f400e0030038400e001c251280c03421103800e070f10b00710030030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 893177967 1250 893176717 893176721
    0xe07081003060903050705100b06190509040515011b0213020c0c0d030207060215060603041b090908040302012c040f0f02131a03070e0d06090b04030e0f03030f040e060103 75
    0xc1c0c0002c00040c6410360030340a0682c80406041901d204006a034950440d00e16001c05691070000d25a030702c04003c000070f11012503e810406000c13441800c00c1406c002203017000034102c80d012100301071000c0754124102c02c1982d000c9440300c001401d817448940c039221143c010503010581c404040921650008140d41a100100030040880344014122005110300d85002520b50505100f18005845195000700703100e00b100709a1482600050f02c440e045503510f848001030916101d07480141c903041d100001c500701d9114040c107602a4022011903641c2c900c0c61000601885900980300b0018207140307540300c40070440404cc100420412140818441c1c8082c1c02d050040500c110513801b0180300040035131001000e042e035071048030303414403102803a40741110682000d84401c665034030008040c28111202407030036401e10020a03014510002d00c65603241d665029882c0c0903038064010806a100e134200c60301d0280d14410030a40c0607006103040201c204129110350045002d00b40c0da40303510000051503a440781e = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 893179217 1250 893177967 893177969
    0x160306091410150501030e0606041a031c0806040501030f14100207051507020102070309090c0c230f010e0d03051918060b0a0515030405010609020d061d010e070810 72
    0x10909031040d5402c0600d080c0020441d140205034a1440c00400140540c020b207c3d0031021842034020700f072260344410412009107204164800315421109002945460030000280f11002082c666204480c2aa102801f0854010b095500c1242402e0040c800607030810300c0c41c40c0c03040d8017001030b014617011407008178241020400c03c20038561001c240c1c81c0c1031010010705004502100c186001d400d0f10b407140224203030303c83d00c5400346c00300702050700030403180e5007a502a24501049180504445c842607440004040041c1d0803c07400d540c207120380039044001444001d00c44c0064000820003c01c1c131005840c0c44000140041003459510400142e10085a44040800b0000540b00300309a00f0800e1844503904041101a46c94a1403e05c0c0e20740c690030003003802426198000d04011610003460f10a12480d440100102c2e0555201c42001030001c00a001608a041e42104c000c504542804c00031044140302d141b56021040085004014040343c42000e99000072035441d103402c0680d00e05000010f142c1607 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 893180467 1250 893179217 893179253
    0x30807021507120e03210405030418020904050f071d011b030201270f08090612010e18070b0405061b060c0a09080a05121c050405160816030609 63
    0x34610801c05503d900c80f00b00038414001210400404004040f1269240a4030b9100d804104c02207000d05c4103e20188071080e41b0910400c2240d1800d80c44001c0f540340002046030780c401090300481c80b03002d6498a400b0f00359120030b04d901480c50528091500a03c03603090000103601c20692420040d4041e4860300d01540820184401e440d090815403400038001c00c1d040780244460341c0441c2c840c405000032080c49062550704003807044040e104a448201080d8400a0300c15481007040042451207039006108500070103003051256145d1600201c626000085070048a05039000003009203c081c61500c207407001d80e6015030f00103071562120b013007074003001040c1e05103a5581c0c8948001c11125164980080c0710b503503900e9440990399503640300469510700400784004c1203038010b200081050690000900001c04a41100009107004051190201c0780c040d9000d841e25007010403100a21409134280600421045004001140e506200904d210303290340002080da0391160b07056028020031450120040351 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 893181717 1250 893180467 893180503
    0xe01181a0105250b0912040605070b0a09061d0c0f010203071b0e0405060601090506040501020c01030c140f190f021903090f080a14030f0f07081b060f0109090f03080702 74
    0x80c0a0a10b00d080e42d01c00c5845c582948502400d0200820085041d5012240f143e04d07101e00305041907841d86805000108900846580c9420603c086500380c0113600b884940d8945044c400f920446a45080c4032110000c940075800b040014547d0345da0000c1103c0c01550002e442c03030881125004140070714605540840b8060b0100410300c8284040070540f94082c0d10240c0310140c07020f81d10300c00c0c004c080c0550300c9030b5405a0000803580310310354041c0e00b100c0c0c0100607510f840f454402103c5807403826030b049492004a40c1c40d005c601c500b501030718001851001681c900b0507284282c10304100030b6071264071016549100025008a42c200341c016056100984054080c0c41c1030140c8034072402c1d5490080d5142a40c1200c1c044a041511010110855400070080300301c071031818014014009840d80400011102400c1c2042140055400311149545c3c1e10b149001803c003e0a2024030074082000c107801c6012480d01d403c02c503170300040300248002c0c1210750504108900c0c1d9241c0c4400c0c0e041c81c0800d840052219 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 893182967 1250 893181717 893181787
    0x2060f0f07080c01051003020604060f030f020d0c0305061c03110c0a060f0f0306030c090902060d02030705030612070509071209230d180b160c0e01181a0105 69
    0x801c03210050804a243d0200801140d502ca0502508603035851001a40046082005124043c8a00d80030902d10346582808200701c200c140c0d8034022680f180f11034008180e81d079100c3e40c5090741d0600400f030b0819000c135400c5251050300481c2040b914107241d0001c06001d520740320041840814001242c040c02c004004c00185555200e001e0500c0124180400c001414500352410302c40c020303c15101560340040e9280c1c0440e04140c3d101004121410090303904c0741003480341e013039038000e540001c5101d000b0550320345442e800d003038051103000462806010741c543c0101c2c3e0103003c1520b0307090300d03d40e00600610b8184c070f0240d40b03220210024184540082c217075042c090300c6503051225241140282c4000c000889541401c00e100c1143c078902031803000c4aa0300880c000070400b000210b030142402c9615003216544000e440d80d640301c00c0703c105500481d080807150004000306029104001d281103030f98001400070040c4550041010114802003505000c40412501e070030840c1101c19603c58040c45450301860 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 893184217 1250 893182967 893182973
    0x160e031e0d0908010216060c1b120f05160b070903080304050f10150e09240106030612150e07080709050f011a04170316060c08060108070c02060f0f07 66
    0xe0765501c1c81c8540465401c007800500e6940510854900e01501110b03900381c90811b0707075488003420710700843c40100b00c1851149014240070305801480144607501080e058490501c1c082c221602800c229803d020050101d070091400000c406581039a10540100c0696502e480c02e84000505070009044803001104000c01c000b000104c1c0740c600c104000490b4485042c1900300f805403428503c684100f42a800300400c96a0110810241c004007800244c41c0701d08008a090340e51031104000644010710500010400c26802d40b28030800f4010718a04a1814243c43c1c90740f8041c41c800303038051501290b64943e44484042c090240e280a80381e40c6007920445650b9100943c060001030300c030f25000035281c0f0000624046181030a04d10410b26201141c2072624000b14245025625150000030703000421601011482f9541e6090360b040c4905c80000e24207509100050001400070074041c1401554800d0010950b0043e400d2031500703904551056403450200079444442c0204c440a00d00354101082d68810 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 893185467 1250 893184217 893184223
    0x7060204060c11120d0503040609061518050c030105010503070c0203030a031514010c080f21180c0109090f1b0e030d02010902090c07021801031b060503160e031e 71
    0x840c01500407040f82c80e18802040000d00d074882801800390301150840400601a4020b541d0181c042c6200040084580d210351050f60341203030001c07440c1005120184030740500408404051001c07114104020302c3d02101031003407440706000395410301a0200004004d28860314500f112103601500756602ea5071400340c007801608071841707254201255610040b50f54001c03264194600740c1d05075261411580151255140b5908c840110800d04004104400c1d4400f81c811908180c51195400440300f89404801e004402c0c090141d0380c0c20306d42280d144580e460703a1201c651810303141c8040c4000b4003400b40100e01402417403d041042e20404402441600c16a00020300c0105e440083d4140c910036158054220300305d4284880096001001070089030a212144d406000728600c090310032144031019510041d4600c2e4240c2c01182d98a100c0000f6a40c1c1140014200000f030920381051800c40c180028420b200380b0351810004100520828051000c4c0d40810550076003050100d440c40c00c010b400014251 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 893186717 1250 893185467 893185487
    0xd030b061e0c07081e030c07050907050f0a0203040303030e0a0b01030206090409060f0902010e09042f040911040e0a05030f0d0b060304060e010b0d111504170a1406190e01020706020406 81
    0x17031961075082e207118500c3c01c04070460309190441400f038843e883c101030400265542c054400381c01c01c0400d00c148440f070b00074400141550325803070f00119160307440e52800030183c40050100010541019a0b03040000300550041d506483d81281c4040d00d92941601060082c20f581102030a69400c0c43d140041c00b203000e44c40702c0d400c98004c4e40e81c0c0400c0403902d8180b246049041e01d0003062204183c405030340030301c80d00311601c1d0700f19400741c025001d000ca920000740c16036003151025542e51004c16101d00b6185020302c6040c1024115101a00e0604d440303031101130710fa0188203000000210002020780f0510201c0d0321180c4281c10040040b0b803242042d080c0040244448518005e4541c41c4c5054031a0340d20300301500c850016400028502401220010302c818035206c0c0d1040780050505000200322141900c04294520740d01c0c070000d00c42c208a504109044900207106884640c11a0041c8482140c003108480c1619192003408103102403480c1a4500911550070083c0c261407011601194155124080d18 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 893187967 1250 893186717 893186743
    0x80903010906051b0c060106050706021207170a05090703021905030118030f02160b0c0a05060705220b16030e100305091b0a09110f0403140d030b061e0c0708 69
    0x14621364051035030b00c1d11520510254501c103510030380c010044680300314010101d191040c5c0c005410300121050025030106e003541c4d1003001c103455401d406004140a01403552040d0b03141000e000c1707403d01c2e8020548848060102030701030302099040401040e407880405000300809002000182800b110240c62058410b070220009086502218a000e02c0019001c540581040480c0146450884481810b07030140070489500c2c010300e440c050201e01c00b80401403003051261121660341081400748100080c07201483d0f0701c1e00b5072030b5100b4402600f01134180c8083c101d0030104428147d0503400c0c10b0350f0120541c004103070311001c0080030340c186541c03603040380b4000c001c0141101c1d5021a042c144080b02148192503d0300708541000800120040380c001c224a004002e003a02e24101d80c4440f8840240d02c03940080e600c0380141340990400e50010005002c00380c496207410404011094005407051192408400b0700c1031350110440420140342e822542524032550407500b8880d41d46e1798658881d51000064 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 893189217 1250 893187967 893187991
    0x70b01080303040212060f06010809150a05060418051e0304080109030f08090c150a1b05010b1207030c23040c0909060522020f0403020d0804090b0d050d0c08090301090605 75
    0x1041080034005501d5007c2d1010403d00701e89a40c0341c200444100800410005c100c3c4248031800000c2e4000c218228060410b40802290610f4128240016510004c180381106044030b44004c2c04030b080841ca2900e01c0c001694900c9081c002c00254900c0c50081d5044000d45510b0030890700d003003642083c01d90350004860b403544070341641c81a0141742c5440b0381140b2550020401500700b4007082110004002d1032006003002003055180b1079940e41e801c1a0448125001c0c3e5403030980f07407480d00c1d0499403c03001c0340e09a03005011583c02c40d500c0e129280d01600c10300754072546074148c030107480303445000411200070050401c100d010201c090007011144180300350079100f49420303408501805c03c10305207a01064855682d04a0085185504009501020088040000038400400140d03524411440418018901d06440d1800c0c503180784100c80080030614400c4120482c0540000c0002c1608136446156007004840040d050400400d644203411500d1780c0355103819400b204100c0e840d40310900032401d107105 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 893190467 1250 893189217 893189239
    0x120a0f0e060711010e01093b06130e0a021008150406060f0503040c1502061b04120201030b01020a0212010f050c0310030f051002120f0601020718020f070b010803030402 74
    0xe1107810b20034000003030010301c1c0f119941001d55000c1c1303000025800061610340d44540d50381440500414491420b0f082520b50b4449000c4448000006060031648084404060341088800584a210000c041900a030746031080b000c00088180a4000c41035006003a100c4800e4950b40c00400e000012100d0210741b1101c01c074844141c0c1060310130a001e940964544401c004070313010041c0e407103030001401115800b4100303001003036441d581820300c1098201038000380f1150520824001c480700000a002c0c01d02c00041c0300c00c000107048003000c1e445542e02803e00040e000f00006c0100d00780300302518003035000a01c0340390a03803000e041548203c590703100f80710040000d0b44a04019894a10040e40e170007011507c0d800040c0045101c2c00340c0200d0947c03240d01100c1007840d944031840280d80207000807600b600b82031000c005d0141015441940e01400c2480542505410840c042c01c0610240e50313076080d11540881c00c00408101c00048812054100802c408a903a464180580c0d82d401181c00320b000c1d00c0e00f203c4c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 893191717 1250 893190467 893190469
    0x70512030a1b081b090d1a01120b1b0c011d070501050306060405040507051207030b090903131a0c0f0c0a0506160f060b060703090302010f051e0c120a0f0e 68
    0x40d000044409950f000c2d96a00e82940c0b140d01c440d510800b0f8206440c04106001d00e568035108004034940c8203600c03a80c00314484c00c90613400c1840503480b0366503404502007400009602d1442103a0b020704141c17105080c2400c3d000926106009500c80344050b0340c0390604143e07502100e52600c41b111241c0408070381d4120303200c2004480c07900041d03034055001081404203010b2480c03d608103540c8034800b46000d5003400b0f620301400d0805501940c1c8040030985d5150384003001d007450440c0781d61090004e801180740203400c00710901c0070159442912807410030000603000018003181100c9a0000d000121071070b080070980680d80b140300000c1c1261045082c4007001030743e41003001c141c0388034030041203902c40110320341d8607402c2e115084940201e0340e2659940b2603520594030712028200032802591101110750851001500c0da00103100c984051200500200d413009004100b001d20600e2a80d044a071540004001c1d10b1500702840d000410101c00415590b0204d80e2000c2040ca03590816940d048070303041018 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 893192967 1250 893191717 893191751
    0xa0b0a06060e0f0411071b0906141009050604090e1b15130902120702070602030c0712050c0301090515100303080a02070c090f2c061b070512030a 64
    0x311821001c2012400e40740414070380041e501204043c0500f01054100710342c0740c00080d0b0341c004c18040300c4480541d1101d8030015020114100a0004d1104c1082070303a05040d13000343c0e5a203110703001c948911061804440d03905d01c2081c0143c000c1401800700e0b51500c0c0c503049460042d26028540000078450000000307540203250380e030313a040180054004a00031a5402c00c0c03000c558001c21b040105108007000000d41c00e000da100905030200e10307045210722420a4103000307081c081c950340030f6400c540c070910542c940100701013002c2040705d00302146507503c50020701e400350400c0c8001ca0750750740c5035103840d421000b4040003041200c05d02c92001c2210201c2d581d1090f4844208a00d4000074001610f40c0f000100950026401042440c2c05001051001555032400000303960b1104907010320152120f000c80d503645111407440708100b00c107141861170004d1448006603260300042031060380c2c00482d461715a0b03502c0d0602c01c5070304481d0031809903007076001114840031007940142c4076400543c0c64080500100c02ca28 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 893194217 1250 893192967 893192969
    0x15010e0306040f021216090204060807091a0a091502070815011a090d060615030b04140c030c0d060e01210b06010809070f0909031413030308040f060e0a0b0a06 70
    0x46110004645a000e00a117104c018018030707254130803000e03100012158181c003c2d0040c841c00390003603074681c144080107050220140c039140c01d202c12120305001403030252440d04038031101e4004141d121030207901d04070744045042d84050b03103440d1103107410307032081e58045012415204900100d4850301819422548bc0e22402d100d07441e148040100c4240c2a40d20341c10040005100052800c0141603698803583d0448403070343d1200d1903a100184462030340fa901401210748070b0908035400c1042060b04064003c207140c001304501241540000001d840c540d00308240c45103040d0f020410051107480b541483c01003002800780c1c410125511518010001c041003010807107507800584240b01d916554010340c0c41d40703005040700da40d80c01030b21008240c0364120020781d80103001107000868400e20034100949101c100c071500403a400420031560040c83c003040302480031a0751503d000f81c010b40d214188041c2210b1010710050030f081c2098003110b0451400100170748aa80034044000c026114403566000311281 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 893195467 1250 893194217 893194223
    0x506070b101203140a0c0506090d0207081b06071a040c05010e0d080a1805040e100c030e070e04111e0f031903050d062706082107020d020915010e030604 67
    0x640040c11004204c2ea01074440812181020350f00b0380782c0c2d955003e00b440021070704034525030b10410f104204079078100300405c010074480340035252441c01c081c3c1c2c910400c01150710250284000050300300810480d0603000ea0703031020039640b860b4981031528000305088858411140000c1000941c0b442d685400008905825800702140d450104c1110041d030311020321000304081c040300b04900140c140c885d80109154900c10381c5c05004da444444809500300ca103001c0000e0201403515020034414a00000e100d002d8a280d55031444159607645003111900c2a0004815000300100e540280701c001d840540d0740c0354400844281000170034210601d66214040d02481c940e941d4980d0301440400e001d0f00040010310761409001c9421901e4815044481009140e003507002140040301049520a510690380540140c00c060088841c43d601e40d0102d0307c0650001c01c122040c0040e02c081103546100c9000d00850380030f007000142d072815000b1005c400c90f09185450200d820400342545600c1d01145041c46164 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 893196717 1250 893195467 893195477
    0x2b050304060b0409082a0c09010308031902180f0405090d030908160308010e1003121d0307141507020a0b031f0803130b0901081f0506070b101203 64
    0x99107481d41c0016000d11002e09070030544d00d4040c1c102041c200302c024100103100c050034541c4441c0c1c10450015914940d1a900303e2908540080805a502e090308603046a803c0b200c0d00303889844e0009d945000250305c0c0a1021458400600042c1d040341c1e61040301c20001d412a04082400000300c01e100039104200c1e1011145c6d000403100450a5010350f020b486040c1c0180550703418122a02d4502c0d44c3c8008048054020494800040142c94080e5112540c0f05c00b660f5101d01445182d980c2d04030080c00a04101d03011b202007131018041c50450501c101c014040300408848080765121005220680e000781c000d0700841c03076014043c00d404070030411103d81c03541c09061b0801d62840d1134802e55140c0c1010f025050180c00412a484804200d1141c4802030b10009000d103554040c2e4944140d212145a480250302031000c0c020941160703044a030140d48981c1000c0004045440c120f40040b9a43c203a4021503444007011a64200f030241c0706142c03602ca4115982d504103070546401042e8440c205500e00100050 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 893197967 1250 893196717 893196721
    0x17010815012c0a02070b0f040605090a030f140d0207200102010b030c09180609150609060916050c1501080c031c0e03010b0d030302090103050609090a02090c04080f2b0503 75
    0x1010003240c81c0c2c40183c00e1001402e003102030340c40f00c0690500ba00e000c0c00007a0031005000c24031143c0d110751030300901c1840041016031040e540162108040c040d2003000d100c00482c0318490304190008440320505004001c44d91404c00d49868403611700402c0c000a9201081c95a8248950051091240a01c0d008006040c8802c081c0c003001861000141180e4207130180d00d0f4060400c40c404c00c1305c9406852108060248088240c4006246180c008c1a451050090710280561900e2f088240c0c0d030840407000e142100544081000d5600d4441c10310b17031601e50301c030300380100108111f07006525041c2c84614043d121610700d904205a503408a823030382d2107686c000ea00c0704034410a000300d6142e0401c480260003ca0862100c40014000b00d10165090300440d400243d0305610f580c1c148100d69000104840c15000c0b0705103900c000b5030351010003000074081c80586001c56441c50500c01a1001006114216a42c3d444015074181e1034114000e80b03412402c02c1b030b00251502204d11811b0908210b030f03a548041c195 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 893199217 1250 893197967 893198039
    0x50604090f0f09050a03020c09011503021e0c0f07081c0f1412040204180c050105130807080307030801060509030613020409020310022101080604030309031701081501 73
    0x14809028001201d958403090b050407000603010350b4032003500803c042c1ca00c00f590344c00c02a04050325000e0140c45104403200500c0580790700d41c02105040c2c1e45140040c0c039800100c2d0617020b6904ca5002003007400c140070030340c50040d0400040d05c080007000c150a95980780e560381081980c4083c1100d841c0032604540044017050380c8500070240c00c10400345032001a84015100e40110796201c3c4d0a181d0050720301a0800c019810280904d40c04a120410710300181c84940d110714208060f10b015490401c00d000652400d4101000b032014050802c54058440b10787c0c1d00e4500c02c3e52907120342c00c01c070080f401980000031b0b614061010303200c9006000e409000a940c400b0310715511a507011004a0740b240c5e503959250301589007041030b440f254109520040e5a00038410001003005c036010000c1058940303120041c40450b034007140240d0086c2e810f0402080d1041c07285401d8603c10f141003101d00e00700041c00b00000f40120b00080030300b0000e0070030141803226626410702c919015504204114030402c0980c0540003 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 893200467 1250 893199217 893199221
    0x30a0e150109230f0130031d06030a0603060e070311060a031d0a020a1401050d0f09080307050d0f06080a0b070203041206020903240c09030106090f02190905060409 72
    0x40d00d040d0310210901100e112116003240007601c03034100c0c08135580b00500c034842816114403030822480155420712245507919894220440c3c2e4001d0401c0103604a1035020080f4201c80081c10500030000380e164a400c0400000403c52840305684540c20002c403941c00020202da2401a039803c80798180c0e250500c0e0080c44225404600000c003059036500e921000c030f500040c08540395003481000781000300c85600402078000e02c25040a00035902a091410407a27070420100d8a42410034040400c1144200d600c1c4001844210700c0034020a200004100781540d11000811102040714000c010708101200300c40d007100d60600440c8001d038801500040414880750f400c56002c41c1601c101c030700d040d44a00c003500e0f580c0c01c12202113404a40202d050504c0340703805d12080c15002120340c0b500e4042d00c20b0113140313005044090b12130b0f0901e1500281241d0759071001e410050203004595028031140901001c0c2c03a00a40c070072080c0464916802031000e4003d48a90780080403075100030302d15420709083c4819a00 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 893201717 1250 893200467 893200481
    0x14030a060c020c270907060203042d0305060a051b03180a02041104170c030304051210150503010513030e01050a180b031b0702240d060b030a0e150109 66
    0x552095941c088015500c40c0301c81814002c41003644d92004441e0090745040c100094400059600208401c0c07090b00c0c1d00005032030840d5034108070140f0750302810006c035207819540643c8800e100718804000c0700b07100001680364003c1c0d5004004004565400c116072140c00b400c110891125802000403030480006d50001c00900312401d410307110f00300260b41c0001c08403aa064400c0a5208000c2020004506006121601c0741d41c510040c0040c003035001c3c00a52244250300030345100304248401400d404204101e2101010030b8007804006010000030131103980c540c107205080c401c0d828080010521005401410700c51130303140e29803c4841c483c64006554503003242d01480b08110358540d0031b4001c04801042d80c0002c000b00460315547e41001d036a0000b9800c00c1038400d03103079040c08201c50360041e00c0310581d1400381d040032041d2104001c6041c2c0030680320310a60345464402c034108080410350103c42c00c0114043c003000c03d010441c1c0b51040d95540d403603104044004041b090241c00400c4140c2240d00590713 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 893202967 1250 893201717 893201741
    0x307080304060b1e0102010b060301081903180f03140a23191b0501090e0c0f04053106060507140307170309010b01050426010612060906050114030a06 66
    0x300311107407444082120f80019088140405451403125104c558086c40780900310307402951400d00d0f5604000390f090b650824410000c00c1310208291203001d0520640304e04609240c00c400c4902d0250365101c044551514900091b141c0c0c2160132841c59092400140440f200d66103c154a210700024041c0c02c50001544c01114900c2d003d4001a80c00c11079450b0058500f03a8802d8041d00c60440035400e000d0005262034118505010140c0f41c01c2c444018500c00307081c0d000c044080c00c203640300a400b10062441c06a80c0c001d40d04958107101040c00c40d078001c0f41c00c0e049810241d8100e120f94405007000c0e01590214454100800d104001d581e000c100780c010141000e480510480e498035000c0d91744d1030038004101c041c405002d100803040c040c2e0002c0c02c1c020a06031300d0092070018201810681c000401072072890201c000394003c2111150f0400003074220400908144c800b000038448241841405400d0b14141250303020301d003600128070551240150f920409000c1c008007021519995000c0c02040e50038049 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 893204217 1250 893202967 893202971
    0xf16120c09080304030501020403110405092a040606050a03050c0a1b38010f0b0a050307031401080a1103010608030f0d06092d0506090a0c0509030d0e010f0302040602030708030406 79
    0x402c5a107400c0005100943c4900001030751a0310310f0908d07003600481e0000d0144030302d060070b044c0400b6400004021540440030780b03181450341101101d912072a04036244045e0410b0a1074000500f50741c200c00900f89025040d03e0034480c3ea0b48106180000740f04220303520700800c110342000030090300b1268200081c00e11a03940b0102084150807400a50148103120f00480162140480040781e00e4101060042c410b10000c08106810141d81c0c0303901c2c2c00341c03a074084100607010000405491098110784800480322860004551315501d60703540b00c140038082910500c03040c503081d41d0b55007014460102194810702c003940c1001405101e0301301d81c1d80b040c1040e810403130b00da020100716000b0720b10800c2e85850b81c41c0f05d600c946010a4a200e40400440498030f50804d251400700021600c0e00d4038106d500c400050700000722185209015200f43c083d80302c50a030103100c1c281d1112080b60300000300c2c40c80048242c80b45102c001440cc405c4090b440f89005800058000348800c40000701401c01950b00705e4810840 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 893205467 1250 893204217 893204219
    0x708310503030f1b0301050d020405040812070e030c190e0417030907030b0a021201030b07051e040314031303060b04020f07051501120506040803040314030106080f16120c09 76
    0x181031560b0810303211020b8118140060210710940c5134060042c201c952035040e402d40d0325200020349203180c400c401901070f54641000500f04000700c000c031b94042d0003072051260b050500078001859410f0050815020b0301c1400490047c500d09683ea01941d545e080740302004071420b0020f1000c514002500840b140d8014038040e1558000110242d807040d0100402440344c0b070b207182021300968601030940c0100d503104020b0102d13551110b6581d45d05407900114014660784805004981c1c6100307920311a000b05150301c01c42d51428420b00001c104807401403614003c018049490507899105040c3c80e0f2416181c410f5082001420b650044ca40ca004c0060005003030140c24003805a15038820348040f64030360040e2151001c90303070010450302c1c003510302c56190307458810195031103995442c8081d001501510001c000641014800c04403810044140394203a6140e580d0b401000d015010103442210003111850300089540d86016200c203c0c04070140d076401d01c5450b003061400c00502104a21504201588030 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 893206717 1250 893205467 893205473
    0x9090807021005092e27030f020f0303091f0e0a0b0310060305072102090a08060106080c0703050711012015090c03070b1308010c09060305070831 64
    0xb0280c1600d10003512640d42d034888850030080521004941d9070003403985030448104a403444007201038000e01909000d403001c06405244480701418041c40c0c09180b403902008002c000856020702c5c1d000c0c0c400e8400c41300c140514420161240900c0c040c1942005841070301c0001c0b030303004060961441c03440f1308154050b460080007107640b003401908100c8004400000b8008410440c145e400b00420381442c0c2004942001480100561100e4a4207162003200d10880d02a01c00075034121000c1040007030107600f2265442d0b0761540c89078424400c110120b0440800244507184034400c0702c2c10700740d00d503481d2880c10000d9034030180201445e080720380c1000000201c3c40910035898603480c211590761b00040208100395410203240c40c500400c4211107402002113032120b42c41c0010fa11003600d030841c4015449820700880b50318040e15542c440c450315824042000300450300a02480203445107503a0521050b99044030640d45000107407003810b50004a160444002030805015520005c2d0840000a02e0716041e1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 893207967 1250 893206717 893206729
    0x80c180402030a0e0c0312040504150f06090303090e0c03060405040f0f050304140307050321070c03030804030f0c0f030503060d150c080906040b0a050a180606030b060a030c0909080702 81
    0x40d503410a00d80d80781080c0c4c1d4641c60801590405070720490082400341003d014010050255124250095894201d21840c000200c90744ca000703803069480320a0203a580e140c0040c80320480744415000705003488800b00e800041c0a00243c403594030010f0480c03941c2c41c0c030010b200042c80020015601e41c1000347c00000040c0041001c0c11b140d6008200640d01d803800c00d0503c01c5850100031202c1d1090740181c078104426100891501c00e85500d0b90000c0100c0031441c1c6102441c1d10464200800051100c2c8001c405c040d00300b061980518082c1e6520104007005900a0701e0710449050040d018a036200c4160002030301c5a0029a03000340301601c1072990000a68880d080c00e9100d0b0303031510040e62034034540b0b61400c1c0d110544941c0441c03000010603103420310342c541465022028000000081d1200002190040c640d04213154051030504440c407400b00d1740c10110002d1171540412503030b44901d00007203a118030344800118181c980040500103002d00e01100e4174020a0040e00480e51010309021040143e40c0340 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 893209217 1250 893207967 893207971
    0x12030c071515080d031e0b0301110703020106140904020f0904170414030d030c1d01020a0f03030f11090f0103050414030f0408060c070f0b040507080601060c03090510080c18040203 79
    0x5400124246401c3c040c603281000001802e407010140303010840380b080b46584e90112007402403020000707610f000c3c6034042405010418816804240009025800c2590561140040700e0118003517101c0c0703900b2082006182641907401070b60040085083c640c031850700c10121508188a15482d200009144110600c0740e006680468a800405484208641018459010045102d24080000b08818000a80150380c222a40400c08015110480e030690080040c0001141c120303124043c1c084080c68010042c1c42d5441c4071601c04c905081d0801a4440340700e040d500c0c02d8030001d010910003012100110001c050050080c0c42c6076204000c001490002840244038201c400c107081507840d400c0483c801d01d0040003900d031042101080000e0000302d02003a40522015601c29900f410300e0315181401450004541c200042030300034100006a20364014540a06040c031a03124002035a81c2e460070000480f542e0801500481d21040010701e02c0d16200000703085d00703e4411216100c558000020904903002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 893210467 1250 893209217 893209241
    0xa0203150a060203070606140d0b04060e0313051903200d0c060e03120711091806100503070f0f15020708010504050a1a13080d060e090709050912030c0715 68
    0x80040c3d9071701801900e001c0c21015100b0b42403440120352481e00030405407414490f000c3c0041c0c22150100d0100310b501d820131452000183d0841c1d881d0401c03600c200c8007030039680c0702d000e2140320f410220001800301c192406080765080324500f802c4003804903106659051100000d90b00600f40b003985030005d00c4414034440501031a41e070700c8011307104140c01d01d0700e401c3e803041e1107002000c4107000304400101015034403070840405590641c50354650f5911500d9000d04043d5041d807030302440d806c00020380c0c0303a200c00b0402c54104408881201c0c1e03071003509114559480c0280701a42401120070701c0311408062102154011920460343e007642c0c4c501100c1e003102c1c000d550440d241d81043c001c42d02406032203ca60074041c1c0315201c030000b45061541d81d402452500000040c070b0840085800f40900c03185a012800512004101c640d0790314007039000340d850303610600070300b881da514120105903240380010b001c80703120041003506441c5448881105841e03401651044510780c40c080d2950045840e64001c000355188 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 893211717 1250 893210467 893210473
    0xf21032610030c2405090616060b090105040209090612160b0a09240807050903070b120c131802131401020708010b0d03082502061006020601030b0a0203150a0602 71
    0x2080d8a44010210400d0340003a820130506048120100c0001c0c1c1d6051034003030941042c60b0b981c0c0c01803001c10000d0240341c03504906445910a0242440005e400c0b10346036a0341200c2d8410b15a032a00200001c81c000c9400c0305412814a0000070403a0500001582c1842130000c12102006d071003402c40001c4205c0790700072802001d03010a41c002000e030004003007805000c0010100c8003003c0c5814070800e002c441810b0841c100080c01c004200740c1070241044404100000d0140c84c040c03621008413810030790110000004032103507440000c42c416141025900b000d074129031400c01c041c0c604010205251500c2110070300d516401c001c601510340d003668408008108050040d08103e011000290505426600c11203031641055180d141981c2c85044c0070741044d5160410a045031220303600c1c04a04003401845080c450410340070300b400b0940000e1020f1007410303020b20703440c001501d13810200c2e02d603c0b003031100515850125000c2032181d04a6000f45510481d0190035200c0d00794114001152142ca6505c440e015030 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 893212967 1250 893211717 893211719
    0xf090a03080f190c021e04150605180f0f0d0327061715010c03020304030c06032903070303112d010609020910030209060408030a090f21032610 63
    0x40c100c10560b0400f41514200700380881041e0300400d52142030b411090b108419800c074840d00c1941e866012980c000d28401003008450b40b07844000e400b6a018140516104541411000c0b01d880c0000d010071042001410055036015000d003400720701e0000b40360480602044108881c10481e0300a866240c450881d00b13150341c41490310320041c0003140c40d40716500c19072542e00e04000c09030504c052845080ca80a00e04012000c0031418101d00f1402a0f4100400108504000042e10396264002d425082c000b22029082088800d4440801d1030700020340e103030940c1000b2410130101c0c1c016400414921090b2043d940a40080014112091350000c2429030a4020000081d1154400d02c034002c00b50a20138011450803000c86d002034500c848051507041050340014010307810b43c45180c140c40c01003851a0441c7e485085103603014000c00700c10f004080c900c0084040024042e02070411a4400d42084a8030303044c10801e5840488150380e401c43c40d05002400300006a944074007403e0103910a115511000c42c4da2 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 893214217 1250 893212967 893212987
    0x13171b011506051c1b1b02030a031d04050a050a1805060423150f0a0209010917010e030301080d02010b06030c070f080c030a0c1202120f031902160c0602120f090a03080f 74
    0x3c41705522180e5106e000c0c0f900100700580700014100c07003040d05410110030300d4440c2c0c440411320a9a84d1001600a8244818171050300c0d4507401160050a145a0600103140003a074501d42480444401514503802000880c0c045119280c4002403081e03440d22460056080040b02483e0110781c5030426203d030700742d60400c40d003600707a82c40f56900603c6000d4150b02c0c1000c0480020071140050140e000f04000340b202012001e03000750322070109034644605884d140d43e559003083e0345032154078040b9800740d42001500c0f40316140c2001104e11641c0000c400605000440e20b81c800145c080107c1129014810441e0700c00e141c1c4200090b042140c1c0c255910403500040d4030b0099031000c1e802030a881503501180f10004103581c12010b443e02002e4400d001512959844104041c4e1824110f2062030b0780d10000b081600c1000c0300383c000586500408200c4c181d1039503541e040ba135804403103640300001030083c80000307030020400004101a000041940030a15200c1d210190aa400350202c0005848000381c1c0c040d80c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 893215467 1250 893214217 893214227
    0x628110403171e0426031216021204031a040501090b1611150705030c160c0501030e0d1d030313060c140309030606010813171b011506051c1b 62
    0x1c110f00840e002d905191038154030f181d10b09914000c0788450504580340003501c070b50400c283c0c0c1542c40c22400c04451414000020f016501044180b14018000c1490031013040341101c08540840e07038003115200400307622190b441448103000d4022035003175403203903504004030340c1c8200854064845111821140f001d0b425019001c103c86800050080c6c101360005501c0c0f80801e9880d0382e100c1c0b07144c01c01599a0742c90b500c01914502c01d10a1038448107003501d0000080c803030141410380a603402a01d08022420040b40c00594414014100000060f250803440501d01e41c07500100904100180031a400c01203107080c0150350918641004001850b440442030034003440c6440684c5040001002d54034019034100800d84a010007401c09051104030404609101081c001c0160200d8124140c0ca000b6480d481660748030750700c20b803000700e0300710b03240c4140703070749070f0340103100f40c600704008103035414045460303c8400d44154011104401c01c900031f060600082e82c0881c0a0070b02a03e11072203203403100340819900604 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 893216717 1250 893215467 893215507
    0x90e190516080c060904020a0c06020c0d0305071701031403400605070f0807120c110a0e1311060a030608010606211505030a03030509062811040317 65
    0x1d140d9000301d004042e1500d03202c0c119a42840261000350340c40c680164149c50a4841640081c000e40c40002c90740307400c1e017001c240e840342151250741c1403245881e114030483d2008800c82d580143c100c2111f00405c002464410341d4400d01106105985c1040c204d2002c0a48440d16040341d81c1441e86986107405843da12079250284002c2c820601515041c00c0800c020007900942070002c0441c01c00400c04420311041d8000d550100e0380c80400c00c88522403a041c004d2031191035013022110020440000c001d070381fa001c80820b040c1c400080c11100c0c40e584104900c0540d0700c0c0d625090b1102600721340c000b0242d4a45000810203101280c8002c100340b0b00c1c2151007400c444581d4844c604000c260b42070000c03030003074581d120072125014400105000141480000c1050082e40c03100350300d403203007445c90820950103812291084016009403195559aa118102426002c01400d102e001d0010b010349000c8105034060b40000b00d40f00e900c1e90815490366240310b0b01d200c481c15002c019820100b0b00c8801d94181c101084 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 893217967 1250 893216717 893216729
    0x10302040320030102040f03030315050f0d0b060604092f03070e01030c2708070b030402090c220e0a0c03061a0a14030f071b080301090e190516 63
    0x529041c80c40e1503062100c040d49015000b00d030064100b11495503000d4041d64003070440c081c034019034030342d5038540900146002d00491152081030321000640340381002c4003010440001d0080c0503c000c0302c1d910550800d40c000d050543c020418400810010706510a0760070106109111004d11004000000d800d00583c522100c0c01312020401c0001a0358840d216070b072289801c2c240030460001c1314405442c80c0d00304c002080c090208100c1a4241100d00f261900121500307903060700c29503070b120307007943d4200d100448002e0340218000d8089040030290400038050f4240b40700200c0c040350b460b10108201e68295511407406580041c041c03050a0344035103e01242038595003010000245051b25010b6890361810829400000100d192540c0da80202ea60800b035010385c1e000036a032860503103244c01e012001540c8110014840e403500c4002d00b0907040c480f0081a401100b082e066038a8808141c018040100c0265024001c0f841100b4407080300000c0303110760a00c00c0000d85502ca0b074000400884000c43e502030 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 893219217 1250 893217967 893217971
    0x120708040305060a14161e17151c11010c0203030f07061a09060a1814010b12010510481101090f03080a0e030d020307020306060108190509010f0212040b060103 70
    0x81541500928480c40c0144200c8900317241c0400c007c3c00f61024400c4e03000f10020381003482e0402040055002c0400800402103c940301d0082c19003210949c0e030310421400900c0c19031109800112076010300d9418132094070080480780740071946000c2340c2c0e0f250406202280c01c03503159440201c1e1403100742820039403042c003a42d500c0700e14078220001804a102034031454521035100c1c0045182200e650b0050707650034403501c00056142d40d558071140441e50201c105802c84a6200c0004101d0b803416030b80302c8186007259541c107500c8201c2c203e002a00113900c01d0301d000080081d4100628140449241c042140d2035104940304071090b2802c1c00621801e2140441d070410406450a04c00b07072a0340d0270044107403600030030740c13903116001c0c8181070340d00009005110f90701d84180000350707001550000060020034801d6080d40c219441d9500191903120055030b950b584028012600203102c40310313038400f5502c10000d50000c901a082c1d520b144003268030240d203040c082206ca400701f0091101d84401541c00003020300c0d007 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 893220467 1250 893219217 893219251
    0x506070c030f030306210b0703050406062102030106090605090403030b030a1502030f010503030301051c021212030103050f0606181b030a0e150c0a08070504050301020423010f02120708040305060a14 87
    0x7c540349400010484024507a403800483c040c00741d02da00603000341080d010840715098240b558021401000c0c2c1c030491007903003010f4010500c0c81d154002c48003140e03006405044140c50340da4040d4081d242d4150b42a4040c8a11200030340424000101c5030080c1e481d4080041c1d0707a0406070504090003005800c0079000380e10400041000e03803104004118940c0f14040400540c3d000ca00c0025141d805201034507882d1301c01e0000c1103880403034250013141264803590803142c0d5405164501038035104100e40066202c180c1880141c000c0a20701c511540c081554650001e0036010301802201d40d8109071440c44016580750480c0780401c100700140f00311144009410f1446203803800b0141030714451030000c0020001040e0100b1070f194014020b8030302420f0001c0003591070350380307400651954003041541540c0080d03203030394000c100354000c1c2420100710381c80d60301601c22035885100303001843c1d101c41c1045070354910400001001c22424440107009500c0404041812036000440c035000300c1c8060070942c0703000e100302c03c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 893221717 1250 893220467 893220473
    0x1090302031e070213270201202d190209040210140304030e0a0b1207050a0e060c06090114251403071106070203130506070c030f03030621 61
    0xd49440c903101003503402e001104201000614020100002d400203c44d40c05010403008940112a85c90112102ca0001d2814248007507075403a82d103400a80800e10079100080c504002075004021044020110396041c6047c81d56003020130307401100c1070520303c01e030400c510128100784103900904440b10301810300e408035900010b2000307502810003423042440300000c0c0c10160046007083c46034206004255141d10b40750501030980c1074002c994a11034000f40c540410b07601d05080c1510103880c540010f0070841d41c0d89020966003035000d540c1c82d10500804100d120302980d00c100080152140c220082c06090400280c160b00f501c584051461074242c02c0000c0140c000c0700080009080700c10020400144409002d06456800403202c00441d080b030b00000304018941c201e17083c030440001c02401c0314500c0c2c3c1c503070b00101d80300d00406c2584d8074070b0582c0b61300400051402d90050b21896005d0390710010318541d203640740098403000100450120342c40c1e19041101001c800d42d40c0040c40021002c0c44001d416036a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 893222967 1250 893221717 893221723
    0x12010c021e07030203031c050a05090307021018030602070b01050907050a0f030216050606030606030f1509160e09100c08040206070615090209041803020c060a0c0c090b040b0301090302 81
    0x1420501d0038804501003080804004503801036030081d098039030b280b400100b114244600f01241d262080e0500000c103011024034450a4480e006180142d81002e009600700860803400e0102203007000807a02c1c0c10803c01240300d40350801144140d07001643c444183c5002c2c0981c900c140d200340d01c5003c80ba01041000c680003812600a01c40c18a054611884810f5058009008000310070140c01c0e622a010004c000c00010701d42d006910880481e02c259031000100740c0c0c0c0341d0140c4000a41074001d44442e0114040c1c60f504c840c1c0210185040d40e110b106c0503925601c0b00345090303112010056800707040c040b000c0818001040e803000300f29010300031506840b070042c00310000608028091480081c0385001e004079644882810354203a50100300c520355448044003e9049400075074402c1b40b81901115141d4401c4880d9002d441c0d25802800480d07806d04208111a0025400302c424800d04000320700000b0111085c0501800c3d40100003d8034050000c184802c4440d9081c02d107000703038540a00000401c0d000 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 893224217 1250 893222967 893222983
    0xb0c06060d05190c120804061b08191101020c0717060c0a1b050a240b030c01210203011d16120b03030d050405030904200703050a05121512010c02 64
    0xb058418410f4141c6041341e40a02c2ca6403105401c1c0318461038850400000d00010011910a230b5200c100c040b02d0814041006004418000c0c404002046241012381d5a812401114031081c00c1803012010424240d03802c0ea442500c0b152825000004203100e00c2c0390680742c01402c00b07400b074010202841e02e081000c529100d060380c403c1c14011115401041107060511038041d050384001501c041c0c0880780340084080c2d19011901c105044965100e000c04810391060031862280107000b01101601a401598003101e0b6154000b1600c501081d000c645850f540010360007094404501840141e4600080000f40d102528a10b00003010b0030812100c81c0d0700c00c55002c3c0d8285180320000310500800300280c550310400e801081c046007172204001c203100c0d001c8050b120151041d50140700b00500802c40408560902808405810040c4005000309220300301501001c4c00500b003c500c2c0c8440c000703002014050442e0381021070345c12941d40c80c000303007400c9201d034810300d004800034840c101410101035102c50340 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 893225467 1250 893224217 893224243
    0x302030d09110d0b07020c120304050f030a02090f0604061a03041419050610060e030304140a091d010c031503110d080f0c1204030b0105090912040b0c06060d05 70
    0x54014081c1030001e0310250503084000207140c00012105407400700c1055008440c04c00141c000e4071500d00c828185091000103040a110140d85400d0410742080180034503d414142c061080c1101d00c80144c549448542c054055038240000e039140c00001c20040c0c404c6600142100510750354001810065942500d80141e84058030391074048500d401c452408a000115060804000c0f00800034007801003403030360240e1110384005100c1c2d501c13130348140d48202d8404a200d0305a8401c02c420060003440b28415038107048010150080d0960740c20448060351311520068207021007600281c2035002c0244035880c20050b1500382030102e001d141c22007000c528081c0c80041c10040022104e003200b0760b40d140f55400e0300c1b5441a822a2140f0100e05071301040c2e00500c0564290b48164003040103520901d10641d011250b100c165108541c1c200300601607a00d202500d503c1076032085207007114030348440001510281c1310780c801c101d858801040d001c03880c0003005055180904003035020100450008101d002007204 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 893226717 1250 893225467 893225471
    0x902070c03020d030e03010f2c1c03090f123e161d07140901030e1f050a060f0e0c0903031908100e070905040c03060b041415070302030d 60
    0x103c40e0a06540607421000a0f0343c0c19440c20600d03050081469010b110011104d00c0c4c150f001045400900030314004040300042d0b10b40c0042402055800c980c049150260036074540850703100804d41c4c0e01401e122180c5002c59902c0c05c0d94040300c01503544140360101d21100c5026901d41c02030050300100307045141c000c503006088802307078603c001030400304a580c86031800d107101d24031040d99849031700700c0c01c4100301d100348207d54520000c280301e9407249214200e60a400060346280129490064004002d00d4620551a0050101080b60403668680408410080c580d002ca4180740c900301c0740c002c07954560005001c007041c1c0c80d01070103000704106046130310810450300c542e501c0726600c00080c51402151145400b03210840e140c210310903170000b10f07580142499814012566200c464026410030210351b100f00142190400700b01506c0c190300401c4144025080005205840341c012001c01d900642107101550b03040395604609003041c0b85400c0c0100e0b07888910500b031031201d40d0001d4403882000101c50700e0076 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 893227967 1250 893226717 893226739
    0x304020d020f0f0a12030f0203120f072706030e160902130812040608060a0305061f1a280503190204090525080106230d05040f0b010902070c0302 64
    0x903c0390b079028a00c022000b0581404a07640f0078a00e011aa13002004030f0024000703c42074001c0500020540d0215442c0c0301d4165000e5880c01031003011017100601030020800130800400c68244240d240c58012180c2d40c0d81082143d091210140656803002c00d00c09e200e40c425041d11221000302000001070710600900175a60322941c0c0003a800003140d80c4c20024080c040d5402c0b0100001494004004039140703511010b00a90381c0d001000345241003444054040c1e00210000f03416034217414403050603014200e90000c103171074644492842001d002c400c000b10741c150010f80c0101e200c032000c01214a8800180740c0414481688400804c0da00020300440e0180d11020300101e590079454040d6809044261340421080c5083d900442080103441000500d5000707142c5110b80c000e04c20400a410307210300340c40c1e410510b8003a185c3c140a00040215000440000f406005241c07c520700815014030300525942c0403401150410b000c6d402410b9210241040c410072800001442c081204001c603501140c40290b00 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 893229217 1250 893227967 893227969
    0xa090b06040512070906050405160507031e11120c120313061b0809121803070f080606031606020a06020d0222090c08010305060c160b01030501060611030304020d020f 73
    0x141c02141c0100f50f002007000c0450554000002d8008110b4200502c1400341c0e683c1c0b01d00f40300840e08141d8414021109820701058030b41d025000a01405108e8941100302c680d101d6000705100780720445000001e114203001d00c002c0d9000700f0800d0040760540890721b242803a61814a0359440d400f510704846030002100045480d400800f8a245143c0c020f0000d1000640f2603d5991071001e800101c070001c210307002d010071842140000d203644003007140c200840c07600d80440d58668907600100d000030752621869001095000e1800601802040078500410b0342c3d05181007010304085510308844000a003010307040241d240c0c009580e0000c00d402c4000140e4079041c2c2170401c2e019201d1001c03000075211020021040480810200404407203402000b00a0043c9031202140c4041c000c2c8800350899102802080006800000400b500003001a8401503c501aa614502c500c0240c1c82503c55940d290b0301003140a0304a1040e40c80c0c49d1a6101a52035450542e00140401d543c1d070202030302030003070380040d4001 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 893230467 1250 893229217 893229229
    0x6081b120a050d080a06090e1b06130803070b070f020a12090e090a050f0d1706061201030b040501060f03020d230304090614030729070b09010c0207140a090b 69
    0x20240e048801c1e01e0001c483c200c8041c198100549480325058680ba400103507140d03840c0f00d40d03505503d1081c0601028102c52040240a0700051400d07980058108955800c02005a109500404402000d9902c41c11207003000d180079640200600144620060f228a07081d50220b0b1410340c240d84256000302c51000300f24215000e10f216082005280403440c01d02030030f0f00000031440102c074032804c211035096404081860303c4040c030204450201d009a06030381000010b58454552002c03000d41064100240c24007195121102a40103803001a07501c1e0920085c44002e0103804003404143d40b400003182c0c0b0796408500103903131000000d0a915400340000c0105118501d41c1c210140c03c0000311b82e100da072140b02c000c00520b010300c20849200c1d6402402252420045103850403140040c90340c0031b40c0000003030340b1091f00000e0700e403089640c441000000000b46981c1000c5000303110802c0005110480d05101a281801c1303a000455801c0016440351002d554130300000e01512007415000c101002e003800402c01d = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 893231717 1250 893230467 893230483
    0x50c0301060f1202030f1f060203040b0d0b18181b100e120c0a0f0b0a0507150212061008090303181501030f0c0902030405070320040609020a0306081b12 67
    0x150f240e000209201002c2e0760404610f000c0c41758181841686c94800040c0c0c208070606100c0d003405a002071008100d400c600c00081e04d0100d58451b0049141c010500004000110460040c03549101d04001c0c08640401d42a0002c0c500501b44010800c1d0444d00510360345440c9400040c1d4410040c11102d002003610582003c103181201400200e810036418032100c0c0c03198119645180241d0301900c0008269040601d503070104c60700344490900d40403105100f15400e601280007079a1514180201030304c0441d003440100b00f0034040d074081c03032110700f0060100200064100041e108125040c0706112a1000100c1202c4d04040700d052030783d600482e40c2c442d0500f8400403a0b00344110052000000052080c1c82c090342c441c1c2c038460710954068584a03005903049000a590113031050344003640c06d10009801d0001c030f4410101e0804640400c0030380e07400240c00c0e1040754100900294011600380100d94141c00f4113405000c00c040505042d2400000300602c65001404803407140d5421b0f00f01e00300c84001809006 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 893232967 1250 893231717 893231747
    0xc2a1f1704150f05040c05150c070b09011b0506010506252a080a0305130509040609050706020102091509010c120c02030c090103021e03010609141504050c0301060f 72
    0x32009141c14140504440031001c05103140d03d040004203000c0c1806803095500c40c69008000d0924181420244400781101103a1240d0f0f02e4800c018420a01c1d004015402c0102402c0780000c4e55091078030001042d100c0c10280d00001c244094144030001000468500c4c1074400545920b911040c1d41c501c21140a2460041c6504602481d080882880114030800b94000045118040c01c8010b00d06410602c0d44075200302481a00480300100c00644a5070042800c00c0c40c8120740d0403042d0720784c00010020b42c0c05a03005c5991941d81c1100008000c1d00340540c1004000b10300003141003510000105e2100403a007821104075400000d4541d03190303070041807091543c03908602e20341a0034001c1d001c0940340048515041c5d119100e00f0074615541d00d0b10710056170607a0340c094130301c1c04c034610343c0c1e1486401309004201407541340d526014086101c600034130803403070300040e80e50300f070303039090a0000000c103250060302d00147c0950300306000c0191111600301124111035103458034258011442c001150000d00c1d84600c3c0c = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 893234217 1250 893232967 893233007
    0x51206040903020c100504031e0302060a090c050405250503150d0606030501050705041a04120b0a0b1002070905060d021014040506030406050403020f0a020a050409020105040504020c2a1f 82
    0x1811000e500c80302901c15244034410080500003e101c8036409d000380104020010303400000000d0004c4010b41000250034803d034010403020303813500002020703a8812918401ca122444402d407005188005001501d0105408c1070342c81c6042890501e44803040d4050400d025958000d018004c010392035110320700454000c0020499400c0200004040343e000344100d0402e5840d00001c58030070711036941118110307000c030700c003100c1d08445660312290b01000c01401c00240f10341c0ca4001c240d281d01c0d00900050300b204164061300340107061820160840d840500303c14000c00400f0966030040e12074489401d07480c510b50529070040400c400e180600c501c0b45030030064100760048140000c0141310341010780030750b20035002d5800010000011564030500350001940c00b0000760420070440c1044d81c440d201041c01072405500c2c02d074580c40810285d0340081a0040c150b0300242030031400c0b0202c2c031081107104926203a5025003446150004c2c10603a042d1342480e10400114000031407c2d8055050141d01e0035904d034070 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 893235467 1250 893234217 893234239
    0x80f071e1422060e01050901111603081b010b0a0e0439060c0201080109050a09050303090f010b0604030321020c0d021501060512190b03190c06051206040903020c 71
    0x904035014000161400c865103040c800403c2403400380030070b0444480c06a4401c0d0400e2801d00c011100035101c40f4a0881d10302807100403120201c0613808043c091401400140c1d1b42e00701c01c001e94107004040300c2c1303000b0940e45050088815070f030350380f8142c2c070403101c101150040a84450070a41d00303001455036048040c2841c1010750107420048812000008182200e103041c440c1d4869051710000d20100c0000c0c0029407000c018403100c042ca07844550060412000065100ca0726503601d40307036900c180c030cc201c180c0c2c3c070034801d140380c0002c00d0181401d065000e5a02509142c0b842c0d03805407900442c5c008400100c6040783c2010f498009175815182c038400807101701e600301c441420703000c1d440c2c1d0300402840802c880e442c0008143d050142c42200d99034910384603058559511001c10509959100400c103400b503440d030102071105e03607003004121340c02e83c010360070301030107020614080380381c00f08650000301800300911205a03500604503000d688034400380d80101d410140d904d0220704140c4007011503584800c40c070300 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 893236717 1250 893235467 893235487
    0x902040e0a0c050901060801080c210d080f0a1e050601140f070b09010608070905091e070608150105070219050406061110020705032d0316080f071e14 66
    0x2c2d24045490a94150040c1e07601da400c2168010024012503c1a5100c6440b19100341031101c10309c550f4044e00500e149005c3d540800c00c03414441040d1102c00045c00038803c0c0300d006403c0c1c0a025401801d1980104509803005048440104c86034250f880345a0350380001074004d90144c1c290080d0400d890070700700d90f52200900c050a075904208003d80d404800240010811581440b41e902a41c455200030905d4600e003261400c00360100800740b2a0310301980e1001000318099100f07001600c5059000740001e142056002442c80070300410360107458000014640099801c4002c4420040c0c0543c0c1400c80920700b031100840c281119408107812134a8800d0010f0900d500c256240541b132101c070241c40c000100b400c0200c09900658101030100d402c10480403500540c5420494820071a04c120420410083c070790101c0a90011940b1443c5040c8a0405090381e51348200070b154090010307ca41d0a8900380080d001b449050b40c1d4610301009000000c05214079030103044140130300103010081a0350b495180d1 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 893237967 1250 893236717 893236733
    0x219180c0f020d020c06071502131a0f09131e0501050102010c0e0307060e03070b0403081305060313081602030601030c081203092e050f010f05120307060902040e0a 72
    0x8814000900c0020034160001e00c040b5012451681c0f560080c0702240264040200e1a8811402140c48000c0403043d09060111400601141d80c0385d82258200145020b10100c101e290240c149041d1120800c07081070844e000c03509460030100291130390b1203415203000e030b08001040c098009240184080c154281c1d03040054004074160b52083e402800740c001a01810f40d6551b0300f40ea00d440d070581200805000443c8905036180440d0b41c000d00301e619041d50380342448880d40c450b4000392182c2500017403901074071125000000040000355251451498225820340b11200740f09001450507034001203100004400482c0c0c0020590001d0a803011075a4070300d44051008911b10904d11b482c0250804840c2107407043e01a40d20410600e0003a14603031151030300084040b840c0d842400d10402030f0856408083c850b44c4039551094000c00d41d01e46071941080c83c000300160311544031601c0360b201009042c0c01c00d13602100f80d820b041d9002c1c002062850310f62001602030408090b4040b2184143c04c0c44809005401c = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 893239217 1250 893237967 893237981
    0x1f0c0c150e07050123090301090c06081b0c0a0f050709020c0102040e0a0c1b050a060203010306020306040b040b03151b030903041d010e0711120a050405010e03010c0c021918 76
    0x2000c490302d4903500c0c2c0042d01c0c9000c41024805115200316404d03100d0000920041204003001000010540038643c0c842c21010303100d40048001414a07001c00c800b00502c01500b010b1012030317014aa04045040041d581c2d650142003000341804004205207080180800c0102c020f8400890b0640d11529882ca155001703400c2481090525411040401c104402604c00c048440d0300c2d6969031000300300e60001c4100c5003400407100311902e00c600301103032010074030b9480a103002e10310420015075139003441e500300320a54071200c143c24410703032401619803144d5400146141e4103e04a0701e04c0308840d40c445000d1407400001c25440714512200104004c172110000c401401642c0e1022a0118444917a01c07805103008400d0144501706a03401c03021600d228012043d01c0041c0c20000c0403184264108400242c060300b01c40881d00101e00d0106081c8580d40e00700304244079544d4240e0081101d0307416014010803001e5031510290044080460701c54100c5e940000b070f640608075402c030256045544090143c003c0c030312 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 893240467 1250 893239217 893239241
    0xa1e03140d021c090f0b0415020a05090f090907090e160b030106120218010e060d0608011d010e060115050d0c020607080a1b032708040302030f1f0c0c15 67
    0x102c803901403c111841051940c50f0485528005507030141c0c1c07081c40c0c480f0082d10603542d2201c4e0303101401031140355000821200a2a0b5500707500c40c811001442110450b00304c650b44949190010440000c00005030354080b5a1401c5000c1008102203109030b04001d40c110001600c01d1140401080400c984002541202c0107613442e00750b800700e40e0710074908031300800c08454900c3c00d2082e074500c03a40d031040400400003900280b15626000341014400229042c0d0303445001c1d543d45503240c41d10040c0307000c0f9002d058002400004c0c088040c4075070040780c4a174014040c8404600c00c1826000c80103104006a8200c8100320108000d8140c0c0f45a02a43e140d85c101e80a10014036060b0010760308511b43d0040d4058044210300710a0325081c00e0b481500944107441520300d6076490b24400340744040c04a4074001000d8011a03132180d40328254014141480240804408030341d1004001303c43d180c0e0041c0010b00e9901d04035000103080814440c00b00c039a068100e1000d41140252880c10000c000a50700241159203 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 893241717 1250 893240467 893240497
    0x1b02060705071d240406050402030906070f0309150903021e060a0501050d020907030c030227041d060705030912030c1315140906040b04180e0a1e03140d02 68
    0x800c1900803032028200726810326100c04060488240340400c00d0443c00c200c13400034004035000d0740b00c0d80494126001100c01c2034940d4004000c0c0400d140d000540c1e20100265480c0c01e100c90300241d1242400c140c1140c001c68400c81da9008240c0034144203000464030140c01401d05070041e840444003c1c0d64203400c0d01d103c5510f0b4500800002c41c0d103040b00c800700c026a070240c40445982d4607a00150010081a1100002e042d02004a020300010b803c2d040c20100305180e1260010b0200303070040c0b0088601c3c0c014040443c2c11406140325030b10030f001030b48990090051900303c2d42ca580745606c280c2007420b00c1d9103c9000c5500030050048031031164001e0b1040c0102402000c014954030540d001d400c04411110502150050302c4030501a0a40001801c80541c054006464282d0f5044107007a41c0d401640202c82d1102d4030a080c018410340740c041d008200300e100d801014903031203640360341c0c0d0603101510502d50703406a92455401014011045644440411400d2640b80d00c503100024010f54400c0c1e2010080d40 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 893242967 1250 893241717 893241749
    0x161106070804030308010816060e0301060306020a0302250203150c070f2a0b03060112020702090405010c08010b040506090f0d0501060e07030f1107110d080406090315020c0d1b0206070507 82
    0x80300000c81311a4181d888d9244103201e1b26002065980c02ca0009840350555220000440460070a0004103000c090983e07005030348644000c0c0c0790341e224418400401c4042a408078404c0540e40007e02c075408501c107644000321507101d908844440344a03203440144201e44011201051024000341d40c8086a0700d0500340c1c1008411020041800e4154003d1484004045c0007044030765214003503040425910b580018a0514607800050b09110125400c82c0d50380e44800c0b41c07911b100d44c04403071180100142d01718107040c1402c19000850034050580e1a81c09200c040801520075514031800c0601103400c00b0003003100907181c0160550f036103400c681d048042401d11442070054441803007035014108200701e0303407410040b60381c0e00d41c00c00c50012034049602001d03607070f060008500540002c0005054a44034450010301d98035210000002c16500c01d40b02c50300c1807110450442010618083e501403c1c80c000e61006c0d1403001c480200109004040c2d00550081464001c0000000720b4030241c1e1040003d61170b002e = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 893244217 1250 893242967 893242979
    0x909060c02030a08041721010f05120a290a0504030e060a1b030c1b050102150402010f230403050313050d030203040605030c1603030f0c02030f16110607080403030801 73
    0xa8840e41183c10700207407214001801103121000284484903207030483d54038115410f5550140c4110444000420076907507001040307602c1d1442c030200c004000c1600c1c03031040c80d10300840840c0c403084403000203450b902031a1701170a200804205542c0c140c04044640350001d044c017900d10801090100c80072400324a04950601c00c81c60304c0f109403480107807140c2c2c0c0d03070305c2030313500c0401e4080d101521000480510194500d50301c00182403200040c0b800710004c2510304600d181c4800207190007000d420100010408105000c05070360700191700151643e084c2400c00d0740c1501411004155030085012051501d4045008010010040014000f0050481c0030050b60f40e196401c00c80d22410459004000d81e000b0032040200c41d010310041e43c0d100e40005005824200054900341c02c070700b0114401c80c0001d03900e85d415645072943c0e00c1112000041c52005500301000803040c0701081c440c900c503010401010707481940c20050b8408000480721070150081da00c1d0711003460809519080303408101e022451020002c030790 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 893245467 1250 893244217 893244223
    0x20f0c0108190207140303011d01050603010605160201020718020a140c030a1d150a23041721030414030702130e1c0504081e0a0809190909060c02 64
    0x1802e45044103181000c800c40003070000d40c00303100f08031004000a4118000c05405101840c000d151448003d01c10014041c00100f4006050f04004c1c400c43c014401400755651101c19100f03604004006140440300307500050345402c0c1582d000e400506101500004185001d40140903100800d031181c01c44e5455540001c01300d40034080c44105258005e000006d141440b810341c10705000d80942018828010200214a500340423080307100e007000001810f542029071202404c0659000c038042c0d91103402105105400c0c40c81640728030401d0640c45d5450361403004041c0640300c0d840f0203030140308140c1c40c2c007046042441d400445058a002c1c0c0c25a10841042e900403084807842907000b00721403000301842d80400001c013482900041705e446900350b4400d1003580e561040f410304181ea280e9584680c6040c0c5201d00d803003090184103503c419850021500c2e180c0004124154943c000007464490503100c011401a0311241060701c025100d0031070000342816a81d004140076801854188581400c540060342d07 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 893246717 1250 893245467 893245471
    0x303120402042a0c02010f030902030604030f030e060901150f03050303040213020c0609060603010c2a06111309051006052a030f0c0706020d05041a0403080a020f0c0108 74
    0x844104664000380041c0341c141d0101020b0842903450314480001e04a5007005690040d00307010210b00c0c00c44070042550703003028207084200110714052041e4040d95000c0b80e15542c020b4402424042810701401d101c5000e50010444569420120746161405504d603a0182c00003540c81c1000c0031480c0d80203e8420b4610107410103494100c4015803030f603141c0340cac05d2000d034400741540603921540c00d0281000c0510144035050160403828020000780c20010101030031205010100c106001c9a081c40056440e80c0205032024003948003191156801e0740d0030050064200c071084e01074450000035210604102c14070500c02660201082080b0380d0b550b080e40c101d41062039006010200f81300340701021451541d4101c945440010307004070264042c1c560219840d580000084082d8841d02161500d4016003c0148900600c894402499180002240540b080c415030003243d030403809410103c000d240919044034020b40c0e0081100340c0c1c45d121202c000391108640140c04101b40241c0340d411140398456903801e4 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 893247967 1250 893246717 893246737
    0xe0603010c051c021312020f10090905060f0a0e0106080a050112020607170d09021905010f120e0d0c0b060415050607061d01060e0f1302010c241a0303 66
    0x2890660a00101035412030700c14425082e00d9020040c1170044041c64a004008100004a40034250481c0c810414141c41072242d0501901050315026480f552060a5100301d614070034001807142c444101103010310600890141e00210400000220801d48034a445e041310000d5456031419250030139820b007070314000c0c41039400410b1080c5002c4054076024000b0030401e8403412103500503001d00710440c0303120b0b0802071001000f20340e40c1010800b0340c100001040c513580000c4680301c5006007041c0010303003408a20705040c0200851190b101003017a25030340c489001195808101e40402d42e0110300103004001010044580070419004140241014001e502c9924815000c10070307a41c0c00d000902100e6000500245c0c0c905442d401400e07820140a4114810200b0740800032501c0c40c2041c08038409d010740a800c4215003c803003000c10589200074002c5650107642440d1081e0b010b0b46600b4240c400c0b8281071000f0002034000610100c2d00011a4407010720b200c2c0d02075204e11006260f0007016200d010b20325650f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 893249217 1250 893247967 893247977
    0x308070e030c130f14070e010315411c02090a1e050405030901031b05160303090614010609050a030302060a0c052503180503030d0e250e0603010c 64
    0x2c5951841c2008000c0200e10b06450300043e48032980500b0340659110b50394005035004150180602c45500c0b80c13480d00c00ca0000c0c2014000caa10b200c101c0c10342c122043c0700c2c0c6180800c407a50b04030f0f003014404440126010b400c140010f220325003141d04425040040c9091480b84003609040280c140c5020641c41070103130010304603246d690301c0c48400e8024081d00d114400000104200401181019204460003580500000c540310044040094111400c1e000c00c0c0c100e1000340c528101325998000d046945c2d02e01c1c4168030b4038084985140c140c01401501790012311705820700909080502c12001818101d0f01d0b2540c400f03480f29500c1e018803500448034000940140c0021002460143c203541042050b40d081d440c065107002100217080041045191048c030391444070540c0300f0203143d4803214004110700d031051141490f074503150010b56284a01c40781039020f1a191040141c610b0350602c0110070340c94404d244007082c00c0d005d004500d403a080324011400c040b903101001c28002c3c1014401c55425040d180c0f18 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 893250467 1250 893249217 893249233
    0x801300b0403050910050903011a03060a0b0a0b0414090723130b12090d0f050403032f0309091807051908150f0702010c08130c09050708040308070e03 66
    0x100c0206000041c426820300c842003012034855259160b07401013806840c0c0d24192102003030800c040c251104015000010203029290000355a0049a060742100904030005841c01e82e82020400301070b0b032503020030724144000c10002000c0132075400701004140212120a115625445d00781d6403681d54103241c0c03070b10b02603042d00c00c60900f811100924601e540fa404080744d1640e500d51201090307124281840d0450207034010701080140404c244d8041080e03c0c2400340c00e208626000a12038082ca2001400b006082d20107072020031216015200d00c0c08030805075200b119000c4602a0343d0b0f50140780074a010350b001030001296203e240c00310100c1400341d200600740c810320305010002806181e46511002136998100015255020024400d4410a0382a920042c1c613141c07090425800000b02903c06590409010242c115400b4840c2d681c041555050448125418241981014a5500040c0086240006020441d5000361226100d40d00c13a9845034015a581340c0c041303403101c0c80031880347c0d00b503808108 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 893251717 1250 893250467 893250473
    0x91921030b10140f1b0109080c0714060a0c06021b010c020f0102130e0402180f0414032b020c0109060615050c0c090a021204140613081213080a080130 66
    0x910f8080f00c0200c02c50000010f17401200d08607050528110741140000610b007102c0442445504014400740b1010f041c0c044446001c0b810a1288006c00d508100c84d4000d5076003005115419107540030b6045024001c01603e0b880020f00078400c00c1d070700101502c01d02e000003036034100500895002c8440c0f01541c080d03962510340c80501440e07000c0c00403a40000e694050a034030366000c4010328441e4615a05407001c60500d0f003020700000e0700c02c55621009400400c0308542422594100340d01e5880ca000300a4104500160020001d029440b030280b8507500700415041840344503000750701540c01c0340c100c0e40740300312074070070305681500c031308201880d5641103810100342c42d140c01c189450780310079158405460280007070790b9510007801c1140c00310b500300b43c4500702ca11007074010001698040741e80c0c94030300421812038540400c2805031209a400240209000496201032030120070441580410425214080f481e0090a1000c090240c43c40f00a2880401104101004101201c1c91190600c0190760049a2 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 893252967 1250 893251717 893251747
    0x5100603200415020703120507020906060307082e0f08010608061012171c1424030a020423091c03150e0108010f0e06091921030b1014 59
    0x18540f0400e60041e81e00c0000440c00c2c0c400c0304c85858620740d80e402c0d03984c44140b0410a64010203020320b03000e001c0c02d0041141e855007000304650400c10400c440350340f5214006036911810034417409401541040349002821100c0144800c083c2c407a46002800078a48030342c03503e40d8514080380c00000c02d090840702081960007142c81c600906000f0460f98440b110460b8a00910741e00c034030140c41e5a06402c0e442c0c503080440d20305c030360412603102c9000500311382000026190414107211034140e58070312014150306d0565040080502d01c0c1d034040d1050004843c0c128003a184401c020f2800c0210b001c01e40c00040004001050f40008800d01c2c0f0b45032107020703c45500440003031003940b940001c160342d001800710b030340b0851b19174070341c02000ca000005c11110203c184250aa9036488000c10050b4081c0382403251201c0d02107103054210b4070500c400a406047c0781403114180c4603000300c82010401c410a011a015403540000000038019286801c20951080d401c8509280d1070ba45022481c1c1c0500460403039032462 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 893254217 1250 893252967 893252999
    0x90c0a09360b1008030f040305010c0801061d130903080711030a0c110303160b060406120c05010509190303021b1905010503060d021302030f010506031e040213051006032004 76
    0x45003c0d0f0030303c1c43e154400c261855124000c0002c1c0b400e0080b40400401409004860002c6454648810780794940340019003202084070100c7c14488000d8403c41d180e03280c4906000944107000c1040c002505142005440540281c074150001001c1c0d03528071138606c000000b01d8860104035640c8140850054895480050000344043c1e0b050008000b0454158240c034130100010380508011881400c22004200c121541548000505034503d00c2401c0840c010780c1c440303807c07a10282001795030390003146d00090040d10112500722a41e0b9203104040241540000d442d5258064140f080f214a0503900411000c2860910201c18811040100f400694403801c040e5801c0381016000c60404101980090110190b0045d441c040039404400c01c08605840362850b0300501003070311010315604000c880c4001912051030515804a034410104046440d0391515205140c6100d03000c00003030410188082d60f1005900c1000c002074180101c00070a058421002544000c070b100504d07207030501c0c04007115510712310 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 893255467 1250 893254217 893254231
    0x80f030901030f1107060507080718050d05011d0a021302030c0304140c0607060b0a09020a1209021c12030f1505240319061410030203090c0a09360b 65
    0x1d4841c11400c4d042c1c500301400c0201e03c6604081114900b200c001040c06000511150400c10481e03035004003503100f114454140c500036a45a10820b4407801c002c5d001d403007140200d0444092401005184032004909149501e00c01c0320408035a81841e840082039000580703400840103000c001240c005540003000e50062076103141038500742c80c10007000500c00d800072002640d1b0f5076190148081c451415004800181014450071421720102c8000180000202098146c03403640c0d990f480415907503040e403c0c0889210161041100c00703103d2505514590603042038001007802d00c07800d04d103440c07400d004081500900c0a40780d820b142c42c0c4000c005200481d0752003a24400300188200002c1c40340240118420406081c0e48007454040260f110200c5c2d002d5888450400b5100d00025550307580c0111600c1800064503000d078481d1244511a0304112035510304980c0080c2c88200025811a990860700340000c3c040c03004154804200d0704c90f180b41d1001d00301d640c103005121090000003011210303110342100e0 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 893256717 1250 893255467 893255471
    0xa0204050a0b071a070e0406120512160501024b0703180e04150203070207150e181b16060914121b0d09030201050a0302070206040b0310080f030901030f 67
    0x4113800c42c0c6401005039070034000605c1c950214942030070140500f4004059103480c8001d1058030352125620ac910000001403880c0380002c0b01011080300f00026004283c110008541c1e43d099114000c1101080b08054080d080c1e06150720b4507140310020319000c1400100799504901f0a0060303d10307203d0340c0100011001e00a940d9108111041001d0200d4040d0001035221074640c10f003801c01e00715170b012910020803010700400030032010b06c0d40890200100d03003844148180280768940162003101c034a4400b01d41043c16880e540e9407111003400150302401803038828460484801c450098684503003460313900103040f550031402c0011500d42c0400000c038041c66060480310b0652020a05101c0403c1c91818644008104c000c0c140031114445aa28140c80c0c005141e070040f2817030042c080f81d40c1c0b1320000e070500002151940c6114000d030120340410303a00800966590341c5440043c40c0300d42058911000c82c140118003c01c0525000412130070080d9a2001581441544801180034118240341000e5441e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 893257967 1250 893256717 893256743
    0xf0509011202030108010b010e091e070e03030705160b040b0906090f0d03080702060a0e0d110715180501020a0807060e030d02180102150601090b0c010605060a0203070b0a0204050a0b07 81
    0x441c50748041d42c060306412001041030101000018003e5510010b118814987c54080c80412018681d11958010b2940740000482e65202e1050f158415a549215018080005c8140230004d020458000e54000c0418a03c54141c032040c03006220b00a0340564a04c900080245000d13304e0328001034101c02c58003c2060382c02d03040b01404100c0e412502031048000c60907500a0245c5d194042c0f0407203a000c611401b003040140641e200c440daa80c85400010804e1000114118a013510180039000181100f8409083d20a40514004000200001d4009000282048040360b50341c40490742052170b0b41c0000400781800400d403a10300c002c12407840703850303014441000788200300300749400500310304420a030a8002c44800c42c1e001a00b002151140e400244000341e00304035490fa00300f003503101565100214151106110b0b6801c0340100b6103031f000940c0c1720074042a40c41101d80c1c0000101710b01e51050001c0c0c0d049869030b802c0441680240e004050313002c1c0001005220241d81500544103040c00f07404252122 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 893259217 1250 893257967 893257997
    0xe030d2012030a0612120c030e03030c0a020a0b0304081b0708010612020f030c1c0305131e080114131b090f0606080108030d0209010908190b0114010f050901 69
    0x308405492003000c808002c002c00410400c81d1003204020240c83d0000c400328112036443c9034045500d14071000078010030004035001d043c40780001818540740507088030b540d042000000c913030b00c20f00c05104071f2051114502c0442d1822108051380d008562210359181484141414a440428134a0000030a4030565200051041003401544000c04140b45000100c0c00d06d0700501508281d02005640241d00110b0b14410549408414030b51600c2048401901408285821115071082011403c868441502c2c0071038110a01e440821550302402100020540d40350754040c2a2203000000540036101c1c1400912072030f0070301d40401c3e0340e58460b500440c15a031680207904c03800c0825804c403924540e035030081c0c078680358400e10401c1d010740403d0900c07014a601d0041e080796203100e03122142d1070f11354000c0f54405083e4003520714003026104900c183d544d800030340010648100d58a4106461244046000040c0000080c0a8140c0c6250603511003e1040d512a4140c0d9203a12a101160402c0380c106c18141328 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 893260467 1250 893259217 893259223
    0x904171c02040e07030905100c0e0307090204050108090601060f080414010c0f020f1203060409170f090a230915100c0b0c0a1209030302071e0b070e030d20 68
    0xd0314034911005868604100b030f2102d6551009085805042c504007921000c83d000041c1d800300501041030215000d019141c04031900b40103005107642602c42c030300b000301760a04c07960043c000303880302a81c80024079a217041070130395140c1d428480c0102080d01c000c0104081d82c49440b4183d40310f4003d03c074082d195000768201508403040b02156400082c0740d150348058a035030502201e5004020034008195401d20744200d002035120180c0010303c2140d4075a4103008000c1000c05042842c04050741c4180c446860b2000c0300b400307601caa5401481016148404203030020304a04801680003a52091400c50140030700b4081c0e001005402850072865408030503400395584402d40c881d2070791075900c410002d0346510f040d0407203180c0030713107916013030328003408a440c0c150f50110320651264603000000c514101f460170709800a116081000d0030504e0912030a0140d281d041112988151040713204900e030f0756032100c0c11035800000410380360307141c0c11424410880d584070ba500703995800c1000c20384900680c1c11030b05541c5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 893261717 1250 893260467 893260507
    0x31103011104121a011802090f120d12140c0315030708070603050f070c031d030109030305090c0a0e070c11190303081617130c0e090c040b090417 64
    0x14000c04101072810130030402070710b44042110746861031442541400308044154290010300e010044c3d000c5011051507903a0b2002c00d200300f030301a205024285850801a4444084549400100300700102d10340c50070143e4400d0035401101044810714a440b08030740c00407146d10107041d029004032044500d05050358240328140040c05407034014814246021005810303a07000070b285500300104d00003001111751b0014012500d640d07262a000800d07803421000c070708051102c1150b081c0c1641c6040000400c160b059480f040c0940c030410112060218440d0801105c85020f000b543d580c640c40d070004c59000e80c0207000040c6058030802d03214500200710b0020450940d11901da2801c82107802008105041d042240d15030400c0c0c006d0010383d4060500540600360300e001e007a2300c040c0b007128500011b2403940c401e850f1103000c981c0502030f03c3d2160398a03001115804016110700c0c125020300c001d4424540b6086c85403034540d07080a055100240e6a0303444000c00040e8089070901c0319101080f00004000030208959 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 893262967 1250 893261717 893261729
    0x40f0e010b15070c0314030f030a0207060e0613020405060d2109051c020925020a0201030c020c0a0b0a020a021002012a02100c052208101104031103011104 68
    0x4100c9070400400082840c0c07881a800c1c2d104042103140d001ca81c1c441110002d9a400112015003020385c089014514401c0c042050349401001c414400d04c0007494001b42899405000b09201c0480d9200c4800d89031301041c0d6244524010000f281401401c01d600b102da07000d0002042c004c40b1410b180c403001098140004203c08a400c00b942054155800032141c01c06080300b81e6201441915802c85050710b6103a8400291003501c8060010b541d90314110410300460380302140c040306100e22244042d503158043c0000701c2c00b0a050081d609800c0340300080b038000700c58005000ca0005841c081075213040f944400704180450003031398000c02c056140c090419800c1c2406500000e80520301008107903e41d1500c60001140e04448000d01d000254002191406001486030001d501070159a0945103072080d00307103501c0c0740504104903240701d0b07040001d0707101180c1c8014183c410151001d01d6182c121149404800f50300b1500348414408034916054403904288050000240d08400280c511040c0c0c0042d4044 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 893264217 1250 893262967 893262971
    0xa11070602040e0f0403020604173c0c07170304150504090e2e0e0706110601121e060f1a0f03011509090503070b15150901120b040f0e01 60
    0x10003503180c8010405070310501c00c0351071301c82d00c2c10150341c000e484e80f002a1001d4441c00400e800c1c881909100005c581c03980e01000b280502c0020310383c1c804c822801040c3c102c4103200c007045120082c40591a402c03100307442c0014014040b00c5040c004440021101d40c03d282c91240700901010841604c90b608500b03503103840d61140e54559240014500c10b440c40c4501c411f044ad00f0498072801a120794074854109803180e50300e03040148503048020002840242480d03c02403290600001d9040d401c4045034035000d44d070409980c2180e80324051480c156101c00f4000300402c1e8a41001c4007400e2042080c450568400c503404241581040c0c00103054440c0c020326071800e4840518291740c2464502d01451011000f50000c0c0008010a00322608041180c85500201500c6d83c2c007210070413509104035644036601c18030144260a103d4118070302906024295030055281c10a14444174031a80141c03407604c681655603290b05a011803403000900b40e8090b505400079152780c000102100300d8028004044407035400 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 893265467 1250 893264217 893264219
    0x5100506031002190c1a07050c0f3c0604080405181302060307030902030f0102030603010507080906010603020a05400b03010b180a2d06080604050a1107060204 70
    0x105400c110005110740c02d400c0c0b0411804e01403000141605840a40c0c0c1d06059000521034206159880d07038400003e904010310000b00080c450700000a40300c620814012225488483c5030300796a09c07031940100c0380a0110200102054001340708800c10100d510400c4903c440107491500d40c275000056404a50381c0c00041001c1c01141807101c010040720160b115880340d5414195188003003840030b0000a0700400000002034241c0d4002c1d000180e016034090222081d050450080034000e400540d00a8425424200840e80c8240b260103036a000b605600701810703450b41303080b40540095100c605180d0a104050100b1201400034584119428404601100319100d12441d1044142500da1b040c503802c1d900b54a0501402c0c00c00800e581c15245d5040b010b5644154410703083c4880c0003e803449551049410501190b160400c2d100b0441301450007940d88450700400054003030b40d14980c00b5240010385d009002a280f0300e02500040d80240c0d01550004140700152140342c03c6071300101d4161405600014 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 893266717 1250 893265467 893265469
    0x100507050607090509071103131806050103110a0318080f0d05010b210603010b090c040602151303030504020114030a021c0e150403141303050c0d050d140705100506 72
    0x601c50388101c40c1c0c07a141c2016401d09001688240002e0120380800507441705030450004204200c0d1140300181f9004d80c40c1541d1800d890b01201d01e03035460581c0c0389081180005165000c1c1c0a00ca0780b11010f802601e0500b046081c045005007194009480c56248138035011010540f410010b100224240321003a5a80342501c07010360036140c060340594a00c43d010443c0102030f102c002c075103281e1559604c0f48045562581800071b80501081c3e500310ba0300c44582e07000d1154900d80c8400601c103c8202d41c094558003021100105501c1804450a01d4514084042c002c00a8803e37170141d94494414189040402d424004041742c0750400c03030f540b03510301b81c0c001551a480d00404009900b1207140310303c10f00c2902000c600700c80c5c07202c20142d800b000380102c42001c102014000c2207420030000f0256821134a82c088007603c01c458401c3ea10082d24603000c2c1000e8252141411001c00f09011341000c02000e40014194044406266048410004030428001000001e000b07010584016003125000b203114103160b0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 893267967 1250 893266717 893266723
    0x10f03140309060415021b060901050c070f0f1502060402010503010b090d060c0509041404170c030c01020d02030f0a1a011b050a0605040b1303120908071b03030914031510030210050705 81
    0x101c4d880f02c03981c1214151f0b103240d403840c0440c2e940e90720a1a0086e1203c40303003c80740e0314241ca0b50b08101442c034202d860125181c51003000c010b048032000080171038802c040342002d0303803560003da90180c00644100014003100b20f0610041484402c094601104142503403156070486007000c0d569000680c00180e0300c107080c43c01d402580e40c061411680c40302c40d810603503602c9071800030b48900301000e0034002c50560f03030030f4205006231921f5040000003503540d004046030710002544102c440c41310b9901e107200440c40c1c04800d80300ea0345c040c449403204400f828580b01d006640340f1082c2c034210080049245a07207000075106002d86c80c1c01c01c0c45040c011945042034a481420928020501108128088080000b09510122407030320800c0001000501c0150303400e006030b891003501030107049030351024040031061a05d144a0011240690b444d503c10940302d43c61070405401800c0c04642c0f560225030580c907209080c5100c5a0452a81101b15000a903690b000c20b6950202403290000701d4808995481400814 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 893269217 1250 893267967 893267983
    0x90c0806040638131401120606060306060e0409051207050f1513170d0207150e030f04050f0d24114012140303010f0314030906041502 59
    0xb100b503d60140c1c10b92030056030b0984001c244241c0d00b03038180e40348801c12607101541c00080e4604004107580c4909200c2412000288122103191524600017000e610a105900a80b141a92070140d103148100c1003101070422640207440c14050b480c1c05182c0c0090300c2005210503072050307001e81280340054003182e0818401036050241d001d8600b041001d5000d07454903003000c3c554042e200c0c0c220100d00054008050141d10000c481840c070002c0c00c5000d0009284e03154100002c070120900c103240c10114195124050754188943c401d005103c1404580361902c00f0200c10400a020080101220b4541c1c22a00ea40140c0081075812820b0710000d01c44039900510710101111164940b801c030a01e892841508410700d0000380349454a1401d200d0a84000c1d1482e00014000803044011519500c0000c06000002c0c4119400d00c80036444150618000c0180d034100c0740c503502c060401c186903407205040c0f203c01254800f018001004080c0d031079901c00000d040609421500c90403d22100303c0040e28000034 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 893270467 1250 893269217 893269271
    0xd151e09022409090c0c06040c03061508060a1a13020a08010f051e010e1305160c110d050f10060f0b0c120a0306050d050a022809090c08060406 63
    0x242d15080700381d01c0390481160443c00f41929054096034520100c42c2d004d019500741d002140c0514800c0c0070911180345484810389014001c1040444d0500803500c050064034401c2c03182507009a80001c1c01511a80d00032100e17050590a900095100b0000140100e040c0806126903d41c0c0031030849506a88054000d01410080401050083c1080d0008003009030850000c08a512803001c595401e0341719001052180001038008005040880c2d005000f4003070803501e2856658422908800c141d1186840501541d0094854407100304c3d070f84240f100b040488001594148a0303202c405075040b404011185009854010000e142414640880b10011413a8480c60310040280080d50707006202141c48194188002c0c145640d8204160055020b00036540c000e41d8440d4204090005110001c64070f4440988200d6001c0c0e01c0d180c1201c00011995444034800c0038500802800f4071a4031600d5204000080c0540d0043c40c002d0394900802d8581f600c04c0303404441c1c9948070191045503000c595064000d0642d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 893271717 1250 893270467 893270509
    0x71106040807020d060f0216330c2303160906050315040e01060303020c13021e0d1d03090102100b060a050d0b0d0302030a0206060901050d151e0902 65
    0x203240d01d8400c1d45000e1402c010744601c0700f91012404002d50703035010443c0014041815502c654a403900320241107400d610566500c5042e41040250386500e43d030180d4134038030445005410300506400301c0d0044c40d03a00800e00a014020214116801d05044520101c1ca82d02c8003240d66031030603030811400c0e83c02401c180001d01c410204103200045d000001d9903071000c85042d0003030101010780001750142c01341c504c400540d5480d01d04040181540480c0540b000f21060307481071180308001081074102e00c14001001c1784100048045000300344910018010705041510214031941604400d49840805807100b003180da000040d0604507580610201c1415074030481c1c10015481500007050080c0310f400312207010014009148018004540d11040c0001c03c0541225800001880c004e55aa4000e03a5003002500c51072002524518148044e02e060351800f92208040c441c20380d68280500d14030b41d0500248a8072032419a03000d60307003204200d10450041c003020900c0d5110f401444001c841240024004003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 893272967 1250 893271717 893271721
    0x10e060403031d100c0b06090c04060503070203120f040b06010801081b03010f060803130b09010c030c030c120e13050c041413020d051009020315060a2303071106 71
    0x1558000954040700d4041c104003e228885114580c040b41c0428480c0b42d1080326582980411644507811001c443c1c03041148641c00e4403a0780400151071412100d20301008810042400002e01c1000034641100147c0100c90070b001c01241081c2c81004115541100045980d040105200c0c50880071034000d0020700f880107081d41002c090940b0f680105200046180503400080f0141c0c400754000d606584001508000300e42d101d03010301d51030341c1c8655040031810800355008520074240104031070344103405860300d10700c040841e40c081c0c40340d1014000076000c0c010300100a0300807400b40c50046086280380d41d509002042298200f001500c0000c0700980c0c401c1c03030f000030084162285d008540a481090891a0184180000144032542180305480089001003824500b1006507085180103404440010000580314041c42c000ca02003141c050541100c400c50603001030420744000c0c540c0c4156484c050250710410382c031031070384111a8050741140890005c108100c0b9644003080340c1001503a080548424 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 893274217 1250 893272967 893272969
    0xf080901030513020d06050c09030f030406020c010908030a032c1005070201020a020c0603040206041d040210030b010f030b041b121b020a17120a09050601140a0b030a0e1218010e 78
    0x1420050001800c6c1c030759880c08100c0318840401920b40c0c0c1623000342112100300c4c101c0d10f150b460750018400d2101520a41c488034406600a481030025a0190f038002c0d41404d940309006c501901140301d081903000d06580582c40d8020a0501c40310007040d200005160003c8281c100c0011581c0007030144046920611030007244a5005c109a402e82204a4060743c41c0c0c5c40d1800040d8152003143c2c054200c4100e0405101c0c0f69210302c01200e4400e9000306e8450340c01b03c850050941c01e580182e0b031198005a04180b228100900950040c40212005040050080a2402400d007d040440c1d0742a010520201c0194502c01e40380c003400f05001d000c00d18400403248012000ba48c0c2d0107028000070003902000860110800b0002c055840081000c914100c0e81d04103404181e0007004007020176541c43c06180e0010840e80c945400c0b130806544003070074003000a40b07094001e002c3c0750805000c46803996100d01d01889141e2040107032880380c01298003071690b98062030755030b506184a44000d25060010f080a05806 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 893275467 1250 893274217 893274229
    0x2030709110901080414150f060103020f04170a020a06020c15070b041410140717010f1a123c04060b04090b01030c0f060206010b0406050a020a0f08090103051302 71
    0x65000c080c200360130941c0700c91410302000c44480641d80064030840e001c010b045800e0340609030266414054001d002e858a0300110160b109080d440c22284408204c1000701da442205064000100d04d030560b090f48449034000b4403020120751004c80184d0044400e481d0514250881c50090764002c40b41900d08040c40d40d03070301c50405c4000c001400e00c0186103d8000360305c0040c003123019020100d180401541030380149543d90320030192038240016081c2d07100f100660843d0b103d0a416601c0411180098614090343d81030f010b81340c06402040e085040c00030010000c000c840c030038003036850010204440807600142450030a201c590007490f8150fa03440081040c0c518801c031540080d000354020401d041400b001c1405002d9501c002040180e45200000038050200011320076940c2d2580e00210059942c00126a601c0081c0148000c0b020108410082c040c081c6005003101803203801030702c800503032640710075420b0407a0803401c1c0d441c8500094803041d19079240c0f14090340010515007814841c1815004290 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 893276717 1250 893275467 893275477
    0x50a0803040c030b040c0e0a021215060f0415020f0a030c030c02040e06190501090c021e07051003090c0f210204020d020a0c0209090a0b0c0f13030503070203070911 72
    0x2600000c0031505200e11800040059074000103800e00c00e042a02c0d01c1d0b40c050844c4e205602c2000e02c54000304400000c540201d80c0d074103501e02100369140d12810000340300380411072440d80c0e000b04200705140880c1d119a01070310080440d61080c801e114240c25029003070042034660760000381c008180e408002034101440060181d0540b510146508184c80407400606400700e40c501248601d004001c002c8151008012402207034840c2405140da07207203007a90a40ba850440440543c20480c21b00481030074880705c50810415050443e034059503540081107914501030300110010307448504902c00d00c20607049800042c02c180a0701106185481c070100c507040903104402121302070000e98102596641e805540c0d0900c0e40c0d400c02c55a032242c1c0300d0064000b50100c10224015454000002c0f9251004604040f40342d800c90012000c8c1d0345e6811803410254030981443c4c072446828403034640b1201140e444000614441d0000316900c22080c0100340c42e00a50b40e00100a0034100000100b907050380300183c407 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 893277967 1250 893276717 893276723
    0xf0105060307090606140d0612060c030f050108070e0a0b0d0b18070b0d0c090f060924080402060706090c0e1e01060e010e03030d1104151403060121050405010b0109090603050a 77
    0x40d00c910203244001d026148c180e0100400d45031851101c0c0c00d22240764040220129251000c0003080d5200070200141d81091261103440d82001e8020400b529103416002c0e4043c43e55503000400750070074000503494400799901501c0c0c900b00c82040022080610740c9001035425280003d00306c4038a01107102d9524400e0100c040c02c0591500c6a03080c1450185080901402000c6100101692100b030010248002341c070030420003003600d0030481c0d01082d00d4a032106029400b03070b4030b40e0400e990b65001d114550344902000c6581c40c1d03803100d00001040004e040f4401808201a000484c5d0811081042da8445500b04510003180620010851940c124000503001503083c24000c2c025450340d400681140140c145503903030282804d031840d01a500b4030300100b06442887c1d8030060941c159540c1150103a80d00c2288021040040010070020344c000c4103041c5040200754101d0340140c0c2044c07038100c10384005035400c03901030f03445049000239076030460103200c00f400e0502c1c4200500c501e1512001c0c2c4c3e03410103c2c00a = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 893279217 1250 893277967 893278007
    0x6032708070b100e13060f0c210626160b1b15060111010b04020d060510090b070b1308070b060a120b22020a03030206060316260c030f0105060307090606 67
    0x85c00c00c00040c0e030492a401c2c585c0341c2c0100119090204040e10b01500300c60b107071050303823014610807807503070850f00c21082070710500404074807010014501030b0f0b07824940b60300b0340308148120303c0d640f0420b0026038140c03030141000d1082291510320110b04c00e1038508074240340340250f030820256100405003c0390051380c071050900c1e0101008017103401c4036004146940782035810900009160443c91a2508403104840d17003914096008031801500b2900030f0100d00815046000030801c1d030002c1480c03070391010340204070f50001c003001d248503650f00c0e442c50344a01c6049030486d8226082011501d0501640c500901c00c43d20601c0c07800607243d5a895452000030411201c030300c80d16801400720f0b851030b40701c1010305a024180d0b54000b40c607800c020750340340001c8508034428840d08401050070401d14401c5812102c00c04000c41c039084881026180103c079155200701c1500c0b0f190760a1010b9a0208030600b50a07084400000300d9042c003d06150a0100325004150340d5824031381c0420401c0d900460010080a04401c0 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 893280467 1250 893279217 893279251
    0x1404020319330503060c0405031207030e0603010303111507020a060e0a08040602060a0b1903020d150f06090608060c091012060b0c0607020a05060106032708070b100e 73
    0x44040c2e020380c866560880c60200303a0300d19000054071940303001d80d80c04800300c8030300da03840c2d1030781642c641300b24091507400d0307005a0035159030b101c0071310090301340f041c4070742800031402a180c40410311070342090b4400d40029148103410781c2c4860007440b0041000b004ca0014072a10329124001070340c2c50100700720080209075600c6c0c0300d0b036100e40705110407483e1a502c400301d10b41d1a40d071000000d5583d0300035690411102d103040100003407807a0459500311181d201d000391000703451441d02007244031481d0394001d4403000061607819a030380075640311307094846c83c002000095460800003210121030054120600390342c8101d0070f02030032a8881040d02c160140803a60841c0d0315040b10011580f500303072400070800150a040c004180485560050080942c8103401c90f2042e80d84c2d004100e9039182d000710003a200c5c6e04500010310490b40709070400c038440d1401200030130300280000010305408105010030784c0c03264800b003140c00030407052054440e000b0400201d141111810000402c20401d0060412005258540e007 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 893281717 1250 893280467 893280491
    0x3120e040b1509011b080a18120203070308251202120405090c0307110a03020a11061207080c071a0a0b0105031b031315060302011e02100902040608161404020319 71
    0x1c0b1700c4204980c081e60722a10350700010300113002d200c80600007481180c0103082c041031000a56880b410b50076002001400450b2031174645250503840843c1400004074440154030842c074802c040c6840e802c0c4079100740d240d0b000035260000d0900c007820b1442d00e002c135000c0004000580e07a0390078071500070f07092080441ea2510750400942c0d41c80344101e402c83e014091651007900303040c3c01251448460740201d0160098102c2c4a0801c9010f1050f104000700c8444000c010544c5c0ea840780c50665840f03c2105001440d116164490001d42c40210b1a030403250207000317042000d111900c3c091043c02e0b000c28280141036040600d05183c001802c0080c02031104800f00001e1503c45854a04018040c0c22016402807000020001405048a800b080c1e01280c04084a1440e40114107844482400c45501420240303090100309005040107800582c0d015845840c08a110034040c090401000280381c284141249040740c20500280d42d082c96900c42d600c14001c019086004000c200c01c0080200702c00150814450 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 893282967 1250 893281717 893281757
    0xe01090315020936070c060506210703060e1f0b1809100b030c01021504170a110609070e010306020918101d040201170403030603120e040b150901 64
    0x101800340d10004095041e40c00040081208003030360184050150135045040f0500001c0301e0556100e4001600704000740e0216002c0c7d030015410100c014105880c10801c8a000b00310780308010700c543d8481c1c004400406c1082010303c920300d2089004001742640f80c1603400c41c10000a04c0c68404101d203522061020102d54614050001d400c0b11031401180300d080002849954032040c20002c6040d9203031581841135464002503001100c0300c140e00078005c8280e02280615030761800b4100302c400142420301c4c40b0307035517203c00c01030100ba4015607640f40420120100c0301d440c014000e8040c2085403c404c8040c060080e00141c010705481d00044007590342d1003580c010be181e0100c26245c000c01c4201103c2481703008411101414105d40c0c0c25050140c0ba4410135030b06103280403042c0c03402408510541c01c10140d42c01d201c01ca85910070b0003800c0011b401036072901c4005218051032480b10015203990f25903d08ad00c1c1500c507030b41e050300040ea84c0d40900d101e00406500f0380d100316a4014140300c1e000b03840a102801030 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 893284217 1250 893282967 893282977
    0xf0307051c05010b0306011d0a0501050a14010504051c020a0b03091c023a030209030604030f0c20100519141e030a0e0a170d0b10020c01020d0e0109031502 68
    0x384c2103a0240da91290915100201c200023001147c004002007000080c481c0a0130341690f00040c00c0050207417501c1c0300c007007441c008080d00c1030501c9170600000130079640e9031100b0b0f413400c50109a1070345007801c20f10421200310f5158210b070452510a205005030080001a81c4a0440300031144502403060464140c0c6060300040082d80900d00c02c0d1b1010010715551402c6030540121850080303142640b17244190264082c007001e0383c3d0160b1041d0001000b092045c40a12100801401c00300716417000e076111a5802040b001040701c5c03040c0403485190b8a400c00285505080c0300e149041810501061100484844441c24543c10416450701c0d107a419003020048640c4a00034070466071006480e078451000c140c001b1941d030500140341682c200c0e8200000700301d01d24102e500a002444015072041c0480e001c1d033000d1050a04582c0d0784a00c030520752120425042c40740c9142d002400c140d100000024941050400d24600708402e2045201c50369810020031010f99500140780581c6000801c2010000c0c014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 893285467 1250 893284217 893284219
    0x60b04060b0c01140703020a0210090606030b01240f020a2010030e01061d0c03100504050403020102091e0f06030c0c0d05030702010f05061e0d0c0803090f0307051c05010b 75
    0x40d10b03000c1588158400c0b081c070010501c6540c0c3c107030365219041d412801542000c40160300180191801140998044140e0707511078600090f0311501c0e40c45400007040260004618003120503d0080d51440700d2000705071210f620310700707182c2c1410040c00003500c4000b0000010701080701c12002174110b042da00d0800c80c105401602100000c866600010054051505205440d519000c0c000c140d0700d4003894031107500480028403803403946803804005c2c3ca50f070004140c0d0f640301c1104000402c6c1da944a0007141d0165009074005078071204e4440810035400395801d41041c1030210034000044540350007030420345450b8210b420685a503245a8810100e100e4005100054051010100080d54006000d180031b54074a600803c90710b203001c034400080742d40580ea12036100c8100c0d22041d0306202820f246141481c0c000d81040814055559170101c0100543c000c030005400c0860802d0142c101340f4500e00842604400501d8035901d410045200b000128403034003401012010f401c000d0103425000b03503c510070 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 893286717 1250 893285467 893285489
    0xc15090a1518080706020a140102090a0f06081f12060e190c0e0108070e1510080717040209040209040c0f030b01091d06010501120f050117070509070507060b0406 71
    0xa45072100801075084404416407100c418003011440510000e0441e0940e1007903002080031041d6a110555580c407102e020000b2990200034544850320b41000d0071004040e0369440c032203501d0820f0300103820010001e048501a0100c0208003043c4141024107100320b800b02c1035040c98002031410710f04c010300078031802e08456220b0005105070b101c02440310810403074001c03a00d400c2c05a40354845940000030071321071240703070343e2129078103201814180e18580e0704003051000c6d4030550300c00e140100b01c4400802c441c0070701240b10141040070058208000344411507001c0395040a610b410b40c0050004030001d44003a000e441c004000070100840c01c07050001070b122071011521516074924000700000000d02440300a541442c41c0e01d07045009904401845091440141ca0940e00740f000441d11403402d1603180600da078482c2038070b43c0c62071510b1182c2c41c0038052115011009102c860520ba00d050015444a4040c10400c800c210b50154458280c03103c1c2584241d01040403100d9900003409820b0903000525981 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 893287967 1250 893286717 893286749
    0x2010b15210405280305041a0417060f0601020111070f03050c0f070602010f052503110d1b050f030a050a021215040f110403020d1506031209080c15090a 67
    0xb51001c5002404007031001084600748061358155005540240800e4080c002403240c00e000d5450485842c003501c80d000d09240e070f20a980b017034040120002e1901504820180007041c0c01c80046564003440a000070700400060280750f00031445490005440c510302a41e0400825108100b1a84095500f4044030701402050440d40e4840c0c1491251101642c80c058002d6030620702d80c05000e209000b54030007818800200c0007000c01c800d0480420760200342c1e80c0c5000019034281c0c071001d0f101840d0b40c3c100000345101403c5019046036401680383c02486820302000190b00c8240003203030340c8500402e101160a859a184650190140c1c042100c03c60014100304407000c1170f4030400b03040d069400c440500c01c030520038200e102203c54481d1041d40d5218108004c1c0003600f000c00012899601c074280c1004c1c3c100d903107200e18007166115041140c40e9142a2a440c50b440c2c3d004043e20040c10348000a8400240c4507400120401c0d41d000c42c1d050004000b04d6564425a954083c8a004200302d4819034115 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 893289217 1250 893287967 893287973
    0xc07080706021504021e040b0402030a060513021e07140a030e091003121b050607020a05070b04081b0609100e03012f160f120e0102010b152104 63
    0x500228041d41005201e21000481c5032400c1281403401a0f0300641041102116240110b0315003a070010700c2d41d0819142c485074281501d03140f0045100f00000c2c0d100099030b130b09140400042e00b0582c4440b000080c0140142c852200140000421892102c200c0c603581d8140c514242448800c0744401100754042c52440c1d0040c507400c0000400110340441d4040c0c55940c941041c03160302d4002d4040a0200050410181c01c042e028130fa032544401011010007140c0f01d203035640c2601d45503084680200580002e2045030812504200b42c00c003400c81007068134109400e1952850780c0c0c0241017400511000507484d0800f9544490007240c096040c0500204104007030341101500301842a49898041e40c40c3c129074101c140c0d08880a404c12101c51500801120203004e0304d265140c002005807002c2c03007003c0c6900d00028103041c4042030f4062013411b80102e0b030440000017034444220008450705590400c88400172940d075a03401048000c3c240c1d00c081d5181d44078480c00390109980c142d000d000303c42c1140e00340b00c24 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 893290467 1250 893289217 893289223
    0x30c1e121011090f0102030a090e07030b09090f06070804110f13020a09030c21150b10110706030905060f04051603050307110d080f0d020d050a090b090313090509030c0708 75
    0x381c0041503850011207544c407001243d880c4581c844880000d0091795040c04443c1c00010101c1d00545281360200d0451008400108401700584500c000c41e48410341c000c0d03145074107010705075000d10369003811842c0385010b41702e201c00034086101440c03040400d0b03010b03080266250f15551140c405c060b48215115203000c60040c20140880c08152412541e0010004915210010480f60244401c040c8900b011140d9140305010950f10718645906440d0030019101d0f41f118072401c40c4525055440c8100409102d00180c10200300b50020780c100b41c1041000713004102c000402c40c0e0801017019071200319031381d541081c0d410a070342d100e60340c5400c05400c04000103100002020b801c001340a0303804408039803500000c0204000c20490010903110b0180050040007400502a0841c12282c0501510300785641e4808421204221404504103985507506414401c081003404e5000301124015413420358004401440c00c101481222540e40d00c580005070210424000c0d40d90001401048814403600c0c2d5050301d031 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 893291717 1250 893290467 893290477
    0x30f0703050f0c0c03072709080702040912030f02030103021e13051f0f06021c02010f09030519082412030f1e04050d08090303071b05030c1e121011 65
    0x110a00c02d050000c5031160901d0142000c002c07c45544407086030041c0c0d401005042031000a031441a03080c0407400c0980c41d180541c141e00342c480c141002d01e11081440240c21a0300d10030700340c9a1148180014001078413618881d2360104403103103c046055200000285001e001c900303202c8485420710051090b11440340701116281590300c071202204030344a68900c96607100038400c0000590204d20081c40d21944e03c1c10241d11800c01c2d01c00442d00c480c49845130010f0311442d0104600081000410310661955550b8a19201c00f113480d14a00a00b002d140d03080c1044108404003e07614201707004260f1956880030505000f28044003901d0b151800b03040c034501c0542041d0001f03441c0c9140044103888007580344040b6800d0350801000c0300c4420341e01c0d4451009540050301d1154040c4010015030001c120b2815030005a05d441000400515080c6400d26080c4004140e505004015a1640c0f40751403440200140030608141c4d08007540c85002c00240c1e01e0030000304400c407520307483d0240203c0c1154000000385 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 893292967 1250 893291717 893291719
    0x12032e050f06090f0f0a1508040c1e0b030a06090e0303090607080c0f03070318061b17060f0d0b1e0705040302060d051b0a020c0a09050108030f0703050f0c0c 69
    0x201d203480c032050000c00c0c42440105030384014003000404440c5004040710803041d0003d4484140b89884103000c12404030380311880d801055420381000100849410b800000e800d05101288140f001c1c042c61001c5071030780b80510300140c0380110019035500100e60129000f41048042400700500342c0e84045d460303500580b0692254000d000c0000c03030a42c001e1404501420b95a5686850300307040001c1c2400030b4201518000c02c0584901c2c007003654601903118403c00601400d40000c10780c00303c02c032003611620710f580c10700b0a1000800d9035070800680d51036000c0d40a030007640c644e0390010555000845010441d10300030941c822000034052981c440301150310329604850184c5005465048050742c00c0d00603880b00a60000c0200a12003507a4143d4000b40c1c1c2044010500a46806004005941076000042103400592000300155001d150010320480104a503000411942d4103101165880b40704d82c8010b0131842c0000118001014451800c940c00da00c44500269151141007400c41e4503429601001 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 893294217 1250 893292967 893292979
    0x2191e03110d0c27090f0b060a030b0301060302041a010206011401050f090303091903060b09150105181237020111070902070b0403030c0f1d180915090f12032e05 71
    0x751b028400d483c4111024603000a007038030b0401d90b00d039004070050440210b1071901035495520000040c1c503030740220000300e40341090b0b0148500c2861b000a15024050303204040303021180520880598000040700c050740032080e100d5558243c850b022a1452207115501038010b11100c800c52039582d0b10800701b2003568420300082c01185020800c11184c20000d641e202c1c0300c40d9007124680e09540c026001010500e503d140f28000d000d02200002d0001455084240c0d11600651400103010320061401910140c0302c0b0b407000da0304d0f4074110b007010008080c40402030500030800f85e103613078811040050000829207a0400d40d44c51074241740045940005a030300701d0201c3c0c2408000140140601e0080040781c0c5543c1c0c0324280e045516600245107950400030a4000180c4e10782014090161503030a0b00c2400c078040182072019001c2c1c400907011000034540c2c00b00e90043c02240c0e02d403480c045042d81600c501001059129114450060010b48890082401c000340c2403074481d48000c564105603048070011108 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 893295467 1250 893294217 893294231
    0x3070e10030203282d0b1f0c1b080307030e0306190f09050f0114010602070f060e041e0b0310061d070302191e03110d0c2709 55
    0x4107038140e01007510358020074003507105055000c0c60b6000640d40c0f013010500300858500300b80480414101e50a5609101001003810641302048450207030404a00c41610340c048075039251714000011041d03c2241c9001c0110150880c400d0000e030900c20700400d641c80e0000050140d07641907a541c0e940c004c4108801054500c84551801e10300840c04a1058500d1719200c900300b00c20b0b480d101c00800141003c414803030b47d10180c520110300e04001c2500c0180f6071200000d08580652940b0400c83d505030701110455010361800e125440300340c0f00341070407035505007021050800842c0015014200d40078080030704030029900c168281d02550403210540c00250705954601e03000151060644050303004103c071040c9071f100740e184c00020303d100c545d40c01461841c006080220141d00754400b100b1804180e800100c04185100841301c07030b910f4a854404050808002c079007100201404070b4000da03030103845c84596404085040e140200800031200c04c211249452558044403500301442541c0a040c0c9090b01d0021 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 893296717 1250 893295467 893295499
    0x3030f070e0907210908120c040b070b090118080307270513020909190c0804030807210c12051014190b0a0507050c0f150a110303070e 59
    0x8440320303022001038103040305641c0c1d40c0360645110144032003c00004100c44c0284082108522071034904520030450070740c0d07400d09a42282e8400d00081d1507884614410401049100c3c0c2040840e140d040e84092140700326661003c1e9a07005000e003983c00d1a11a841800c01820803401704020340c03041c106500d94106802407815560b03400c40300505480d43c4420074107010722051900c040e0000090301440300c003600c0d0100c1031010580c02002982e034400b410458006403030305010107024061040000d4076081c145454103490080c1000d40190107901844112911120085c851615104100380003030720074018144840002800c0c1882e0b000040411403404010610100080313081004568040d012600007040c80020400400010f03803c0c2080450500340006110400c035000c0c0071056800e841c0c3d22380350107a0f814890305000c40c5c886401d100340100102088195600043c80c140285400e21003a00c0f0341c60300c3c209640c0c00200b2803200c0040d103c040700b00541c540d440140010a41c001b90b0301d0301c2c00c480030b000d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 893297967 1250 893296717 893296727
    0x201140606030a09050c060d0e0f0604031b02030f1b03070e1618150c02010f110d05030903090301151406070308010509060103060b1206010905030d02061302031c0203030f07 76
    0x184405512010410115455a80c0ea41001c00803034040c10035145000d0482000400523407103a01203803482c0740c480b020403c3c0c51105001c03003c00e4042e2180039120138038240d98020300b0220b01180e21540c10b6100750021003036490801240d04035012600845101c00d1001608003030000072455030500c03070f1040100110b240240300c5940b078010040000803107105917081ea41581d07150505249108100e80081001401d0075200d05041d034840d00c5030316800e00000c820f000040c5002070304145c15040c001510800c030030412000802c1c0540d40320301d20344139031a07031a00301d0600d085110383c184040d4150309040c003482d80111144010811240c0320400b980c0f04400400511400f4080c10030050042034104c00108071500b0004207a541c001414900021483d4554105031040d410181c1c9216100000e00100308041d40c000705588040c100c100c004004a03800ba180003940e0341d000800c482c48503822074100604546080010694a80345d00d11002a14804028001d689400880d8540c6005003081c001c100298011 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 893299217 1250 893297967 893297971
    0x30f0a1d13051f053007060315090605060d050403021011040e07080702060a18200924270f0a0510050d0201081b0a090f0803030115120213060f020114 66
    0xa81504880c0850502c140f10040316070050b0f000d1784c00c5011040740300740700620070b6074061300060701c0006910704a02c40c600c4031211550401d00b181032800b1001e07c89551084107071842e00946c1c440118403580c5600c0c00302e040c40b10a4007141074043c146042c500d10076003401d002d40107849180d1a41031b4607a40f140e00c105ca03610001d039021000b40c0c1203280400e81c0031003990080404403001c5500050706c80c41d01d46c5e40c640141d0240c0c0500c401c40030520124003e82c58904045500f00c02c041416000d4144a16180d24a0100e0218240d01c0b900403490b03a5102c0307002c40d0744403842d60380004d1113081d01442c00011003002c003101141d00b9071610f1b02e0b04000445010307100c507804066600261400205150302e50040d11007080241c0240a80130420080d03100c0e807018031004103001040c030b58504c00310910305110309441d202641c0001f020b940061005100c7c03000c0c03c40541d02c0c40703100c1d03140c44203490440c0040000240309031000b0802c810f0280748007080841e0070005680c00384055038020400401098841d000d08001 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 893300467 1250 893299217 893299219
    0x60403140f031324080f0903070510060819050721060204030606050108010f0b120c070605150a09140601050a110a0b010e06040b01020709020306040227010f02030f0a1d13051f05 78
    0x105c5011880e101b25080c1a640d0186161007100c4c41e01c0c41da40c86651030b10864111120110b81c5461051041e25030a100007129080640c1c201c8160703089907910705450b0400c500502411010920758001084e80e100c114060b45904210308550791503d81c14148040c081c2800ba050200301c0b00b000000d14620010b8098040303c042c00005410903503107c4245022440107010076a043c00c00b1320445011803402e00ca281d02070120003110207000a10b1100344a030b002241e60251180c64034040d410b155088900b9441d41e03101009190080c1d503102c1d4501c041d5041c41000f40305902c0c03840340002c450304024032400000e0599924040c04e4100c1d0341d884e4200400c3d590003071030481c01030b00561810841c090722031b00515003243d0014409400c0190310b40c20044000183d0b0903424000d40340a80c00310895070480031481890001e07201862074080d907400840400d2080c1c00c2498104000c40210b041058880c1d54060b0303000000420210154407121000c5029084c2910420729003441d0b24101544422064061012280 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 893301717 1250 893300467 893300477
    0x3c08130503032706040504050910060519031b080d08011a0c0a03080a0209131a010203070c06051c060608060406270207150e06070e040b060403140f031324 68
    0x10550441c44881e650f0005a0002d4052001050a0f900e03801801c1c456101c6100030024076079100c0b440740555005910a50207202c01c003104000d05800300300c8040c140e9400005500500b0707030928044c8907a044170361102c034260068000d0b684030203034404007050488441c02c1d43d0b403024290001c48005c0074440d4140c51000360b0320510200c80080e0150305440d0f4841c8000c9001810701c030245010034840703c50158055800e0b582d42c0d160144a500043c56503100030020303c011418500b40341e031740f50800d85040c0504818020041140c0003880003000084141001e801000d0003a240e44580140c8004001da1310a0302c00e40c1041400300337107644260003860b81140c6041d400c0701c3c80c00c2d010150074000e5204800c00c3e9130096520380c000c02d25000d50b005841e2007200400040910b0300c1d040c0070003400040801002403045081414441d4556201e400341c0742626000101e807444140c942405a03d03060381d00c102c01803540001f040e59200140340c3e02c9000c084402c001404150b0010041030208174190500711000171032 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 893302967 1250 893301717 893301757
    0x1a0d1d011a010816090803040902070318081f0209030d0c031205070504150e1807110a0213050c1209071502010b09070e030a24183c0813050303 63
    0x140e180d509039004144c82e4100046031503200c1e07008904591003500100380c0650002281020941e000700320303102822091080003030690414900355203800007440d03a16042d030b40c610102c031005c0e190f5604403111401c0040460300c0400c080d44014054404600003603010446001c1c400d51041c3c0940940b0340b06120300e03030317400f441c040c1040350444002103401d080c241042440d0038103120b05e48448003c980440f112800c1055a0310300904001d000648040c07001580360001c002080c0162600c1c0c09180132400208400f1a80341c3e101d070840f094900500720003c100c20492014400101301c041401d0b002d8074004000001005031039402070382612160b018180e003042600c2c0005d0610f0388112525030244200400b07443e2241d00a850759840382c8814000180760100750150054002006d101e442043c81c01200d41d0000c0c80c8891711219100b20005004d0400120304840d030002d880001c0c00710508407000d07001c40c0303034410380603042052712600f051018102c4108007480105461500005455800401103100c80e044c07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 893304217 1250 893302967 893302981
    0x1b06140a09030f1b0204060b04050301060b07031d120114070e04020c07050f03011d03090102070909030c030e04060b0705060f0a09020901060c030e091e01140a1a0d1d011a0108 77
    0x351007421540b80c401884c500e040c01a511400f0301001020040c20b01c4d41c40701d050004040c21609154480c035103014040003904000390304414021000031040d02031140a01c070301c1000c21591080954401565440e00c519401c00d4505480d070703603008a500769520307032003200c090091208034458000000c0390742d44000801c0100785440441080c80040141c000b003684906c0c58584500c4821543d003890507a040802c9040065904118800042008030414401c48030182c801178008180c0c001c001e82040040910f885180c5c46030f4001074020011040d0480d5282c199081c865100d1005036048840291014045400d0046502401843c1900181605100c0c1d103011703400d5a0b41004000124140400310300b25054990795a6a20b034412006000c50552003145503101c009440416000f0131103ca00d2519148110340b21100300b0010354040e10840d180010455115107424018141824829030502c0076110118920500e802110398100c0001c0c0003062070f203410120543c1102c03042c7c0380003a04010015140c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 893305467 1250 893304217 893304227
    0x61413050a020c010c08070f050319050702150703090b06032103042d05013801090519050916021005061207030c08071e030f031b06140a09030f 63
    0x1c070800300350040c54412110041800d44240030740c60804141003008015a05400c805075400c600150b140081c0b0b10f18004000248414880384800e480c581c0d41c2d0006807100b4000c0014a1990142c0603503480f042c0b412140c014060704011030304540000c4414040703005414001050000a0503083c0c51002c02c6846584214540d04014030660754500750031500c0d140b50851003c2c1c840e80a01e50002100c0108050034001e0075140f035160110180c107030422201145000852007040f90020f030020700340c4a140710000486030300c5100d800c0160b2106240304611008291140072504990007035070840704070765070307802e40707038220031040c50030b48090780002050310b9040200703500090344980c0040144038181e0305000c0c92494001d80e60022150790003190000c0c003200c2400c011034001046078905d9219802240c181d0b1800e00082c503c8028405c030a8245204205400741541d00300b21444101d040134250224209034001e08030a01400c2c900840d90030201d103110003240114000c00d90151540d06949a0390032040759 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 893306717 1250 893305467 893305471
    0xf08071a091023040f0f050d0815030718140c0901180305031e07150509010e1b0904061407020a030e0109052107120602040f0b07050d050a030603021206040606141305 73
    0xc5e41d581c090b42d0800010000501030340c0950041c802881e48114008010301384a9001d00f414001e5410301d01303022074a590000c0c681e01583d4050080c0012801024504070160510315159010312903030704204440412840e000d810941400da8075008210f10042003d00d01080c0f42c0070140c01074204002c80a604c40544180c902c00c0948486102c0c0790045684444a00c42040401580e1403a110380078405031100900072002d185034490040c0031600c0d1007181c00b428860040038518003501c2440c000500b809041d501001d0400b034002d000c81040d1501c0c4500a4454680600440100d54092204401c0c1c0d4403e144001c1680d50140c414440c511010a000480e80262518050984a002c0002c5031100b0200c1c01c40e400c0d544070707110142e240e6062107400c0347c5042040d080906001404d00c82240810303c00141c00041040074148183d48840b0420110041c5c1119000617400c03040c80c05c1c0c150004400081d030360780b00b207008401c2000940c1d202d81e680c109484002c001c250340400c4a604040395001a588016 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 893307967 1250 893306717 893306723
    0x16030c061d09040303020304060b06090f040e160611062a1b12070501201b0a08030c0a0f0c02060a050f2106030d020c0109030f08071a09102304 63
    0x1d4604035140003800312030040320200c00080c0c0110030720040281c01d0084026241d011a0042d0408582030701003a4095041d03e1401e12032a103480c1000000309082c08009981d070130072074403155015100c0c40040c010140c1c008201c00f281c03140d0300c00074984c4180c0c09c80d0411a204900b0251040c1c1c1c074160480ca2181e0841208145c01c05074400d6101c40e4203104020703140c01c034034042c0c8150341c13654000d0910340e084034512026105200d04007075501030124503440449202d0030703481c501e1051014034010346030324040d120b54008108000010038012044100f00240050801d10364454a60b24050001111001e00000d0000d40060f82809243c0c0c1c0301d030080000d4203201d150202840e09180101c00cd00c10440b20010b411300804180301c051289504041c4104041c003115070000300030300104400020030444c0948806485054142100d900700001c003c101e5498075040002c05c4240c01e43e4044006510405407003020091043c010001c01c40c42040c0503444100700030b1004c0d20100c410180c80c0b1512210010412 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 893309217 1250 893307967 893308007
    0xf010302012d090807210f05030705010903020c130b03070524030406060608010b030f04110a0b03040c150e01201207060b09010e0105030a11040e010204031416030c06 73
    0x425048090748001d02c4141c5a80d0f641c03210007460b01411034240411600301e008002c0d0641064482c40403640c01c404a0b00f03612409040c60700081d0309000f030940c082c0c280300400c03650070700b050f80041c0b42d0700091910070f5050849410b2109010f20a0110840c5c00e208a125056080707108108001d20380390303401070600346515501d09880049106481480d41c000c407411503180381d50b02c078244403103035001110310701400c0300d2141c0614501b050401001d000c80000d10050584507070800204c000c1e2640000c0c1c0e030041c003103806056142e0519107028807018016000e20070003010b8020140c0d0015108038400032261006864058480c040815840011800302609011601c1000c0d10490b43c180304400405110340600700000d138a05c2c3c02030401c01c1104042e0310000304c40c0d40c1d03040180400d40d40403541c7c44446610129450510a4050110740901075145681e442c40d480802c3c0001804042c2000001a0702d111040c1d8002001c5c03c81c074225400c2d04ca002c090620060607006002c141e010b06070003880d804641d241 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 893310467 1250 893309217 893309267
    0x7080711070303080a0507030507080103081323090912090d050a0c15080a05040816030e0a271a120a020301090818041e0b010e03070f03031101050f01030201 69
    0x3500c0d14080c020b5104070300003a00501080180602842841c2e089141403400740450309144600805881e010701003d82039080026041000100361306a4500804800303101c1c01c030681480c03210300c1102c0310552507a409020b0307020007d256200045210100549040321042c00d1295003414498030b11050741c6c0440da5842002454004140c03065403110050007602070b42d100d2418801c0c030080070101c004d404640307598200f40074000050100401c3e294108050030ba462006035950400b280e00c0001c400c8000d40010791841d0110301c4215040510b40511007009120800c141e8180d00202101c100305091420004800e100310f08603d45080741c00b042018040444040314465000a0f00316203407ca0211820100040e0f040f4101e0307104e5a10107a00704045500300304002003c10381e01018184010119051a610190008aa03003c0c251340b4240c0d40000d03003155821511844200c0c44000c80c1d0100b940410300820700c1081108050041d148a158401040030503030340ba41d401502c0b8450701541c54001c0010b00c44c0 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 893311717 1250 893310467 893310497
    0x902060d06151b030c031d1e03011103060a03060c050d1803030e150a05071803050a0203010506060f090103092d032c060c1905010c0905040c08070807 66
    0x5100180c4407559594500b00212000949054600980011240b1451616001203070f0000442d0b0819a0141090001918140002c4c241403095000869021003401105942e43c202c901c4030003a450810b50080040c103041029140c070318002100d01a5000038441c80c04e10015181c2e800c0410f0510352824418182540148404c003520b101c1c4401c00a501c210503a03200506600d030088d45420000040600001c486190030401d260100408000c0710701d855201040886102c3c451481d1081c1040181444007a141d1a000751500002c810a034400c2d800d180200e5442d01d4200701300c07158400300c0d000c424a080a0b00d4015406024640f00540701d1004c246c1c00001c0c02085950703d141000140c08121301060210704d03000c0d0a10303c054164640001406081116007030841c42002d04551049895a80742c01a400007640b80020007810300502d0054440c00b401003060540214409101c40d403691000c3e180c0703480c140b07c200d0f1042c0c241040040c0c80207010a9a050151442d41d40240f0103103000018240951 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 893312967 1250 893311717 893311721
    0x90c030c2403041b17190c0803270402032205031605060a0c03021c0b0a03020406230103020a090b071704060c0302060a0b0a0303050c07091517070303050a030902060d 73
    0x120242c4021204207101c5041865180902e1301410803054000e54844401c0200e07562500411200030414820015030000d000c610710355080240f00c02c1342244e5480007903941b0708040324611540e11400d0a016080d40d1002c0c5803900a680c812102c0448080b64880055050000c01a88200079580c0c1d00003003060002c0840072004540c10f05000344020b0074141018203514045600084c0000101441030041c02e080510380100580c00c0c0800e001b01060100b840d20010301071001c6984000c1d4044c1c41c02c440040c10b0a006500100020250a0741034405c0014000543c1607204492032000040c603246402c0c00b03100404005400124011034095100072a06030030101280e00a400100c0414010701c410300030140d0402905500401d4441d05000300404c05000c100b582c1d01c24040201172180204080340252410050b400041c01d944e14140244900203100b10410701e02409001c010241405000202060009500040700e03855a142c134948210000120020805800201e910040800c105c4610714014 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 893314217 1250 893312967 893312971
    0x2f030d0902091302090a150513060302030706080408030c0c010f09032102040f030f3e0402030405100203180a0c1e060807080c0c060708010e090c030c2403 68
    0x400400611100305004114910700028656030020f52102c5043c001a02e801034000e410100c0a41e0108030081c00c0425880703212095001140c1152908140e008a850a508910100d0b0300a405840c0d640b5103030700d000c454405c01110080c0542004002240c0c80c46105801003e5680201c0d0000685941c6084000c050392750b2508245d000800f4100795514032000d4580038807501000c2d00b0114500762400358450f04408161102a142404140c000d909001c2d0a070381030144000d410030f54070300650524101d403681d804400d01c6101c1800b05140c902250782001e100716800350390404028100d8a1180c481c0c80702940c001002c844501c400c205c80d01d901c1b103501308400c4215622801d95403000c01d08040c0c24041c68803c050405849030b0001c01e040091b0f45d0050149a0889414a07082e82c540c2c1e18800410564412442012000d1240a0800c10030b1940b09905a0607036055001c0c3c4200c5444030801e440c0c1c0e50450b010100d4cc550081c14036280c0ca440c00c1150100200302002c9542c90f101c0071403100544581013 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 893315467 1250 893314217 893314237
    0x41a040b0403020f0d090308090117090d020c220c120f0b030f0309090109090627050d021b0118030615080d170a0b1503091b0a062f03 59
    0x48091204040c1c041c0b00301080344d0304a60040140c121054002010055030b40f1014002c55000100b184031640f141d514210075244400c188803003030070140ca1865403140181d505a00601480386140818981b401924420340e00200c0807020a15448100d40300a2940d207043c0e20520040042800e2a02c0701806082d181006003440083c51651142c01d041c100b40c001030507145550010811121070303941e42e0804c14103444904d480080c299810b450b01c00018840001200720084156000016010b48800ba04040c1c030300c2a020f440020039008003d0b85e407400c0341c0880c40081a019036440405512900c01c0003001041002c0500700260760741ca5010440356911003440c240c905409003409841010030041ea0322140914181022148281d01000040704c00380c20014096201c0d869650981d0721001c0195141199007a82c3da560b05299a42d16903600b40001c48a603e540100c4940d689407500d031042c1c00442e12292290035204a0710b2301d0f900520342083d9080410080090040304074001d04001409903a02 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 893316717 1250 893315467 893315483
    0x51015020705090c09090105100c080f0708040e0106180503060a18080406200f0601050d030201020d0f0b2704030e011205070906031413080c0c090f040b01060503040b060603041a04 79
    0x21705030103111501170140c001c00c4c02509000082c19105174440c1842600c00c1d0082042529244e00d42641c440510039124040c004810214021170070f40b080580c42e904845180c0c07a8072041001250382e000100500d40b07c0e00c5d9154220000045402c8055000900d9424141410300d03900710403070f070b01c00b070307080d04035400c20310016096000400c41081c1505404907080707001001004070040b140c01d81fa54072201405114000c580c9a8044000c06000b5012340c0c0851401101c20b00411700402000401000351003d91072007003640c5c0c0030f1001e2036000703e00c1c507951024591003016100c0c0c0d62b90f00c040e9028540d5032003490401c8010504501c1d44c0342c007803048070300507510b655070f1480d494500744000702039601f240507a40c12120084203001d141000300031026485a8005c0c0c0c41511012144206400e01c0d06641c000742e00440c1000402c1910454021003520586c4201d9403500315980711003045450313003c1250700030800081140402c4a0741780c5003001d568020f11a48421100d41c01c100d4000108400030384080b16500 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 893317967 1250 893316717 893316727
    0x1e0c0a09081f18120f08010611030f090d020a031a06040218090c040b0d06180e030f090409060905010c031d1207080c0f07061101051015020705090c 65
    0x40d441400480104a6007000b02803000c03128203440b800300041c0b240c41004655925100016011241e04030203219044110058050800c1e20050070718000040f440000429507000450080d000d04a401071001862004505090120020360155842501c15030360121f80401b00000507640c592055014510410a41c03c03850940c0c00f014000c0c0300c018010354400e50040c00043e5003c1e44c001440756150740704540c0c7d00c403a901c2701071402d2010301c103e0f00604094040046c801d10500899045181140c004003000340c180380d618030450b0120341c84444c0311170a5800810130f1040c20340a40b000b400d007000c0c00800001d5610b040d581c42000315040110225143d03512611040f402d00d0300b40c840c0c80710f480045d000c1850f00c0d1508016540e01d4281c1414078640c2008081014014081e4910503200d41038103810844c0c2c100c503480c1c00346d5a0b443d11103201d00ca00041b0903c41580e180c07101809514001e0007107410304510309080c4006008658044a01e4004500c03a1290020345942e8101c181da004451902c0010380d52 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 893319217 1250 893317967 893317987
    0x15080c0c0f0a030801090902090720011d060c04030c0e0a0204080a0309050f0f032119090f08190f0303180c1406030c1603020a150c170910051e0c 64
    0x284146c0c4918101c0b0701c1c0882e002c01513118102d010368400c0c8103260420b02c2174883d240d180301c080d0624602c0b01403907203051100075492283c1004025030100c140c00702c6407070341d4603003526a1562151707010040c1007101003641007200e07400049429422401300760001d41060340751980545408107440e4150300098400308100591305008098104020054a1031a5910112008aa07848400310b20080c1c0314603240006010020b00c10003500e066140100b03c83c10a0144007000912208060040c0003081c259044001044100001c10f494811601d4010300212801c0d40c444041803030b40c4260a4003419180e2404003581010f142624002d11f200c1d94070301032070508004011001d00185210315001d01c40810034049108805800d452145804444060411f42d062030b04038101141c16a0080c01c40f0441085084446140c0d00094940c0031030350b0310486145800311600d28081c0013a40d0301c01d07484e0403002e914070362603081c0d070031540c2c0c0600c194160408610000f8902460014102c490590400001c5088041 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 893320467 1250 893319217 893319227
    0x228090e03270a0e0a06080f030d050c121f1815050105040f03110f13020c15012105010b1306090b0102150109021615020d05090715080c0c0f0a03 64
    0x30300c00d502000c2e1019120440c0124007501d07414018040500382440004220703019507007100f005000d100040d80d0203030f1032074a10706981c0e03001408041400b07401e05002506541e14141910321030305c200c0a000026031101c60440c0c603040e070a102d82091504034101c000c100307540f211100078801c07043c07144009820103180c41c030141c16030150303004241041400c100821280c980100e18100b580c0c0c1000c0d0841c0c000c991980000d40408130203070900e400a80307503440158200d001d6806080071481160036551a010100d003903000881003405001e020074a40e00c2d4486250703114602c0b294485120790000120160108001844020101160015651500424405801c260240100e0700c0020b0006210081d01000414814901401103807100ca90204848140d40c3c002c105d2080d01607000030300c0015290924400b4030103540010411284982810040380f080580007402c9412182e80c1071081042e0700303503120700310350000015103101d540c460240b2094903071071001d212006000901c80000d0291301080d03e13010700 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 893321717 1250 893320467 893320507
    0xa12110d03051b0f0d05010e01030b061012020a030e0f0a022d0105130504020703050304050105060906030303060d02030c09070f1101020a0509010509010c24180228090e03 75
    0x405050000f84001c020190880c003004051644416440360b2184003a800ea42c00388840311007100d4280000022042001c522940c142c90050150041645d2040306101c90442e03280100b17000101c2c601d100c0c078002d100355406485151303410b18001c01c00b454541d002a01d005480d54013660140c0000e06c01c42d086240c00c0d03548969807480141e11b0708004031818030f0120343c0c4004100d80d606004d800107030b20a42c1c4821507030580181200410442d10b4250f1814010110303007048500302c88943ca05804500c5074600b64840901c1003400900031450350780e90300d050102826044c2c504903010b1007080030040d400d42c1c07501410741c41800a80d41d04511401c51100042840c3c01108800489910411914600541c8501100c400b607000f03092a507603c04140c401251038002a80010f4151031084121001c004500c03854548026079008042c8190030103800340300540f4810180080d84100749400c0c0e0500d070a072042000c2c80c00542d4102c04c01407950b481000805850141065003040e03000020840c22021140400f02 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 893322967 1250 893321717 893321743
    0x10f180b040b10050a0f081e10031506050a140d0813050306040f02010305010608070207230301050a090b1e01050d060b06070f060501120224090604081c2f0a1211 71
    0x400d8504084e85668800891902c0d480418008080000e030f801a203261a64002e40c2e01200180015100c0d2907644000c1049024dc244655034100c0700142c42002074020a5003444000c0c051800e1001c10b580b03041c0964003c400342d00ba1038034601c034002056a0148121441a400741111720703402c0105100040031508142c109030240400c0205000c512170b40003c40300180d500300b00e4500041c1000010600382090019812645036003080100640381d00ca94006c0200d0a200f40e80b01845034441441d0400c24a5580c0c91011841e9180d10040000b40386c0721405a02a0f40104070018103d51903402080c00c942c0300e0041a51100080c0548104100143c4100e45c010003010703420f0750283c1520f50004586c089045094409080034508105001c6001402c94810040080c51a0381e501e5940d036055469800800c0c0e03405494900c6000c5c00ba01c64007079000c080d0500c588800096040c410030b41d85290800c08003e41244030304c00c4030b13040000180c00003034515a42403039485880d07101540f00070352440c094841d41b883c = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 893324217 1250 893322967 893322977
    0x510030519050108100207030c210201111c1e060e0f0a0b100e01090f150e0d02030c1909050a1b0e0303030a110706090614010f180b040b10050a0f 64
    0x100100c2ca00454407617484007204002580d150301c03500317044490b000c4440c1c02a1480901e40038074591001d440052440036110750b0020b00c40d0028800803000c0c5401030113421090340c07032600325400da00300041d4048010b000710011b048a03880c1043e44000202c4406410140304507900302d0a0109003c0c0b6110f03610703030010b843e00d800c1c04590001c801084000d401100b007801800300d103076410529a8094034071007010f414103110f110340b0255901520f400240b841c1c5011404a00805442c1d080c0d0b0401d1034003400c5040d0054010444503042c401440103400942074602040d180b41d50700440c01d030400d40206409422001400b24000750080c00484007554107090800070701c03051030b1001d0401e803004400e0341d600454010700001c0f5088026a620251320a0041c01070003185041e00550402c00c0c203512249424030a82da400420b07a884012900894419001d114640d95a403190000541c40f542c0040002c100080c0020a5152401c1c011030a005224201c03840411301c00718014a8035540504080c081d4000c80c038107 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 893325467 1250 893324217 893324219
    0x2010b0a1505040b09030a02040903120f09080a0507080f04034d04110d0c262202030d030b040b011d040b0103090507031a070503010305150403030605100305190501 72
    0x1028050f071046104000d844200403e943c5010341d018050f25038150340140050180c0304e09031030010a40c25860742182e1078a0701e00001a0304480c0144151089190312012441c60980300310f00544554008002c01c64412000b04043d010100224010b000158030814041c50000c0e01901c00c5003420300c28807013895034200c03284072007000d4403100b40714503900300c081c0c81e5420800000100403c0141c011004030f200000000921003042c07051942c003031844103082d0383d9484442542150341152095034102c240d9454020b100c0400c002d200344800c10000b80003202c3c5440054a0b0a40c04030741805d080d003045c0000300e559418041c0d0b0a040c180201900000d0074a03004000b01d5203910001c2820305866060341c00395583e1510002c099000b42c0c4010705481d041400c8505282d901d03d00b5203036003202c4000406140c1d8403603001c40e29041c0940143d074140c1c1e50040182c166403090704a20414040c0007007054040503107502001546071990020312800f150340f69004506450004001c903e49001030b00540c543c9468140 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 893326717 1250 893325467 893325509
    0x3030c2d290c031b0c16090608060c12060d0210020607030516020a03110a020607140f06101502120c030c06090d020d050706090b07090501020f1c0c05030705010c02010b0a 75
    0x45030340c0020041c0d065030242c03c00011040d0070340100507074005c09100304002a40c00701e4079001080d0407034010140138860183c075048030580300c500c141d500c584038100901c00b064014050b01c0c0a184d1204010380f401001d00401d400142840309402030003009a00540140b1040580c180100d50380703c1000064000c1011b030102c4000e46d02d06071100d000d001c00010b003401d01174152003441100b00c16600288450740395402ca081c8401d2445001c01c0044462042c071442c0140b49102282d818843d000c03680c82c10f1a0703640783c04545000084030ba003117a42107004a03803044142e10381d10f5005d803a43e104008020340c0c5400712840c00d613280840c0680000700305d9010100d001d00c666030008010190307014519240b80c070b941442c64580c01600304a4401010310903100c0030007020a83c4611a4000c07520240c1c2100c03074007032040310740c2030f02d840000120040ca440c4c1460030200742c900a480030208030707100700708492806840d502c83e41d08444020386100c00503511004400ca0728a417000c8400e0240c40504000e084c0d207182d2007 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 893327967 1250 893326717 893326741
    0x30b0109060c170a020c09160c0f03120507020318012d1803031206060527031509060609010501020f06150406080d081f03030c2d29 58
    0x881001c0402c611030485904000750402c0c03a54449201c0d22120391075080000c0080e440d4000c034485c05029007020800180d002520390211640c1254945404064400e543c4810b002e85a00b66016003e02021703003074005030382c0c00c80c5c481c1511519550740034540320f000595180a03003034400c5a0483c100140f2010340500c6101003007140001c0c800a01e40410500f2180c1d006031620201d40e0b60342e1080c00030494002050541100410200562031481085941c0d01e4160644841c0103001c1c558079240b81154031403a6501203a2900c0051510050440d2400c203d84894508100306c100ca840c241ca070000018018142050f0240e0b5024204c24006041d0041c02a050b190380c0d2580104071084821014500100b9034655a101c10042e1035400140c3d40c918100c800041e24910064442003c0300c130385a021010001140c600400569900d980c41c0d81e031600047d11307000d2070600006070014058140c07600c0091244080c0005080c41ca11404059103100060340c9001c842543c0c401242e0f90000c1000300700600b03000d0135 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 893329217 1250 893327967 893327969
    0x12030a05180f1002031206301f092306041b1503050f0601031104030b0c040b0c0a030e1806190f080102131d01030f150c050d0c030b0109 60
    0x3034445060a0541c1c1d1000500018070b201c225a08040c100b114a00303116804001054082d084540c1034442e40c0703d20040c0480c558100e0b103510385465824040401490303106021902012040c000c54114030000e91404038003410320318140c0c45841d81d8402105c10455078404402100d0341e0700a07843c6d040c090707103440c40d03441c0c404c000d0005155071499060304d290380c10b40d00d0485019101e10b5125803000c03440480c01500802040d0380b03440103e000b0f0b07000550030398404e001d865602e044440007241400c0c51035a51041ca084080e0404603410010f100106510400c500500b429003102d1004003045410743c100608001c041038045400cd43c5803410f45880240380d03550154011a00356990781d0030450344091000580388503005409600000391001a1202054014240c5d82070490421a2026903034940e420040a44c80e0303582c1c500c2c910785001080890010b9000c0d8030790a0180410104c413031500c0280300c0442e003440410b640070510100fa5100c4c120a5480740e525041e001e410300b00702290030030300040e02d00e50507 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 893330467 1250 893329217 893329237
    0x10b10080112080f0d0b0117010807180b12031e09030312071107060f0f020f0607052203150b0d1a2a0c2e020d1b08010512030a05 57
    0x1204110b0010800c4080844074029020707022141c4501081c02110013608070b840304c0d9400035440a071442e00c83e0148200c0e160403285000000c0c800c20303190080001410b50400ba414038020f640c2e05c0210345c41d0319400b8001c43c801c0303960070103503940d00710154401004800c6400400710000e07042c410f0700c1035030300d0001c00c0710720640014241000e03a40c0ca00b01c0c01c45110092925a10b00c5001d044030000b805900201020340d0401c07039032030301d9104607070f02001203940e40c9214150101545c890310100b44c41d40d00075401050601040720782c04006406c54209200d05070340c1c0354800c4852010580301c0b0201d203800c6100783c0d60394900880302d5005005d071a844441c002c3c518a629541123084010200d08010841d40405110201303410100c41a20b1084d614000582c001252030b0000c1e0041039000000740302c0c0d165a400e82000c0c0240301010b04941070003201c00a42226020001c0290b44a02111445811781d80700303a0308803650741e82c131842981844203002c1841700442103105190720070301545462071f070403005a46503012 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 893331717 1250 893330467 893330489
    0x605160228060306080307020a14240309010516021c0e0312030402031c0206070f02030d060b090102010b010503130803040501140c0a0f08010303090627060f02010b100801 75
    0x2140005001d194089000095003495403001600200e08085810102d861588003003208582c4c41100303580780d119a9000a5000c680b210040c0080c24407000d52004c2d0002c09400705815000100c05030b041c44102c012090b0b00400c0200030080142e03424065140d1000c4041d241015100c5840b40180d038841d2858900712000c03448483d41c5d44018482c068111224000404907400d880b2034906c11000b980c001d0743c0c241d0080c000d00c0300c01d0f150002841881280061541c0c010011545e9405085424900003016041140410004540080218081d4101406244c0f042c7d941e01d40c8032400180c01c6070740e150009814082c0510030016540f0400082503042a0800e044a40c0c82e074548c03500600410300394042c006440e2400092200120001010b81080c8950fa1510002901181d50a0701c03030813000d200040000e45400c60a005240c811001405400000000740b212807080c4540c2c01584102e6801001c00540c2042290641c240c3c24018030910f98400c0e25064155107182c4801000e65605002da013116071 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 893332967 1250 893331717 893331757
    0x1090f03061a0a0b090316050d0f062408100c0207150903051606170c0301170c0d030210060b04180c140d020304150e0a1101020c090a021e040605 64
    0x40b880a06906407900100241e8090b0345a5140400c0d507001240014082c1c4508048540085601413000040c0c55008009044d40d40550f541c12091071312071842241c89075100c01071022845410b0b0f0150482d40c040b04400c0b8030385410f10080f03501e0011603110940070641000b005c080c41d5600070802c0c009403031072001c0368090701e4052001a201c4800540c00108688500f00d040743c4200040601c40303090700d840c0e98a501e50741d085001c1101c44003d06a8045007040810801003140c805900e00e002102c00c10001a83c0c140d809080008014011040007900036070444104003a00407641d200e000098020070045a040504140343d044410651070300c8505507a58600c00210458001c100701d440081c40c2c00405a83c461a0310300c1e89020b5001030b107046034000303840c6480ca00c24500a004070320030508540024000c14109854007120101d410382c842e03041d03000d41401c10320941c0780d07901000d225841d51400582d803168000070055800c90710401113651200c0901087c040b45a00c00225120940b5007442401c02d2 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 893334217 1250 893332967 893332991
    0x304030c03260c041406070b06040b0d0b15090604180206070602131203140a1d0f180f090a0206071205040e0403170a051509100504020313050c01090f0306 68
    0x1c00c41c408000c100007002c5000f006610304880c4010401e40b40c50300500040c0e03184c02000d105a6008110000b07240000c110005021801c0550201100c0d40c0c000b4504c140f803500365240c0c40490700066803d04a201d820810703440c22030629480c010342220040d282000544c490002c200a0b540303110400038854400046d001e8240030305c98068030941e1040c54405001c06030369000c2c000040c0d041403021008511462011050000848241d0350b00c1e29003903d895044100e03802c01c1840082d234850f5000d501c032800034150300c1c1c1900d03a4400c445044c0c000001046081c01c0240f001e5804910007005800380d544820351440c01030b11400c00b541c502d542d005010072107c0b0b000e03035420f607154020380e0804a401a8502d04001c04d045d031000c0e2040f4003200c408450030300741e16a45480003e0b20b80403642c0c45150400d10f5001d50380ca09103002c04d954084c4080e5135524009448100082c1603900994240d846200c10030310f00f005011003840706000326502420803016041c0340c0b1940b04138044840c800603004603030344c8000d9100 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 893335467 1250 893334217 893334257
    0x60711030f1c050708010e0709060906050705152a0406051c06030204050705030604150e0606090d08040f170a1211010b03070810140108190f0c0801020712050304030c03 74
    0x140348000b070030a00581c9090640248481c2003441005202c4103103a000c14074880c003422400b02602c19542c0c840210b541050030694281c1c2c0b200e81d080b80c6510900210f4a5080401e808050044080e2840161a05040f9100d5544019426200300c05102c08000801c24107400801712005c06c1c00003c00da1542d07002042e600c50041500e54006500681841c08110342e0940c44002503101f84c404036810480ca030000c3e071589031605100d01462404c04a148041102442d02c0400751221035001010b01c07c9008190382d506619800591083c0203640c0c030200184600d2070781200c070350080080c40340102180000d580380c1c0d0341d41c010700c0b8000c10306001c09564070300c04619085d08448100e030400341c1110443c40d84c4540c0c060b503507a5064071401c03081c0c0ca0141d090070010130313690350181200d48500c0204bc000b1810b8101c20701d01c01050008031110880d54081000040507540d605000304400c900040e00c441d99810046d1214035010f00881c01c1102c10020003000903003245540c2d41060b0989041041601c503107441c0781c4 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 893336717 1250 893335467 893335507
    0x20c060d1d030c0a0614040b060f0d0c0e0603010605090c1e09030d0e0307050d05070306050c120103080c0c0a0b03131e230f06010605090307091805060711030f 70
    0x501c9000014030b0128015000980340402803280c4810081d54448000841c8940c0050300c00078854000000441e0082ca0010280a502400100074030807600255490290242c1035600014002c4031281c2003000c207107020b1017035000504042e01c04895500c2c146104000340d209010700c0c0ba0b0b100980030322001c9404026402e0b900a0480a802c07200110724805000c2c180b0315016a00030300c01e200d20800422a0b09020450904050348036004280e040d00396035545020b40802800340c0907450041c44840c100c0400114024021401811301c603565019500026050a00e8445024081e1510030401c002a81c40750044a41c021603841a9001068461070554204c00c84171000f1419142002089403d000d02404d90b50100b6101d00c00385601003072504189a214041d007507404050b03420040041141a0095008050103000101038444440d2151420000c5407140c0c8240520789061400e4141042002c20040b508030b065403c01c0310b00c00f0701c0d00140306c1e035078810b011030301d40c0011001c41e50004601900503000 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 893337967 1250 893336717 893336771
    0x5060708040809091e0117030a0c02040b041b03060603020307090612090501051503010b0a03021f03060b270a051c03050f03011706010608040206030f07020307061d0d020c060d 77
    0x301c503003044801002403426207016030317056010800c0002604844007455030b007680d2100e400b65040035038078a801d80310a040d4850503070700b26480c1c0e80720000a43d0b643c4112400c02c03400d030368500c64101c2c60b41030040c225600d54211030241441001403013255138110a9005c11541c8074034000790080c8600d00030202070403900b03d0042c030f590708000034000e00c00c4901d0400380604800358002c1007400007007002c02a04801c4d6110183d0407501c4030703441201b041606c41040352000d055040204407540d17a86100a1282e202102900852000c000340b0a8480c0701e64811414415003110b201d11000d00300000030342c0c80300d10b405041c01c80f2402d8281000402d405042541d840c109100100c988030740e0b40e05c01011211031503010380c030303d00e01410300081740103801008001c0c02203801400c214219030710314019081c0311070301502d9402980710922030a00007840a0044c010b4040004207148400b01940341034a20340003100003180150b4101d140c440c00503485e41b40549040d14013048020404085010842881c009152601 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 893339217 1250 893337967 893337979
    0xc050f041d0d0e030106031109091f0504120806090c031503030c0c030d02281e0609021c03021b01270f060c02220e0304030b180105010305060708040809 67
    0x140300503901c0462010041c07000c41c0c55040815096108240c200c40280c0801071104914078013240481c24010a4260710400301c2003203580c1c91440d0000c074054404441000c150703054846042000300103003c0c40703000141c0501d082c9030f641030800034005980074000510a68000001200007141205200d101c0d20203080040c0603260340c1d054191030360b03072600f41c0421040d000b0f1065031500321001e4400150107164007621100c947e00c0c0c0c007691610301440240b000d025281c00000300410310b1031a0320101d242c40c20324440c4a0004040d505031050000e8038404482d6603c43d0342c1120110700109402041000d4658182036102c0403101341d000c0141c03919a203d900d40c45018014904640942c150400c0c0b1000351156a00807a004994880f01125583c0d240e002c003e4022100f91000d07009808028101900400c0c83d405c04140a5118a8402c1c40d6401660040d14400d000d00e06109a07003811400c1c00240c10000c00090103030f0b6043d070700d40030390b101e1000e4070080c20850444005014400c1e00c100341c1c1d042040080c48 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 893340467 1250 893339217 893339261
    0x30a14041208040503070b0c07031101020c130b090105030f10020d09120f0207090c140c07051906080603030703050723060403031b02150a0b1908060103120c0c050f04 73
    0x2c0900240c105004481c02441a0800401c0410740b9a0030b40d103010440c80e0050030083c2c1544d544621001c10100001d05611402240c1481c6a54501ca5003600019942d000280080c801e41000200e18040e4007540c043e80190910544400010070f0300b0365032030310800c070160b601c0c0e070328200c180c00908050102929401da40c0c01e210100c141d10180d25029074080b907080b10410342c3c5a9850f83e003100c407c02c42850104800e0010071115000500180042c2c1026800781e81403155240c0105030400301d10700a1443c0c0c01c04541041c090260000704035078202e902540114289001c7e0380c0d0143c0f182c8a00da030041c140c9680400d88000036a1800d00710425070907100f040d242c050500e40f0700500a417668845910301701d440c00c04581d582601c002102c020b1841d180300c025415840303905030580100045484960000707690815407524200c9042c1d80c0000f0031903100207040a615500301507081c042c000c1c000c802080312403000040854071540c0c0c00c0c1700ba10000c950242c1074150702c00008009090b04500400d220000c415 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 893341717 1250 893340467 893340473
    0x30e07050612070206010f0e13082710020606060405040213090e0d080609090a0b060307090207050a05060709080606010807051903091b0b0d05060a0320010e0f0102030a140412 77
    0x1e0b5004200503021680c00340d8a4003002c41d01201d85010341080007080c1000110f90700101d08000c0180c5002d00d1844d80341c00c441030b10124048810b81140c40c620140d180c40c00340700c0d040c400443c040c3ca54252001c0c040504180000880a1055100b11031245030007040e2040c0080d0b261400600070407185001b0460b26a9a61449072203480103420700001ca2038200000c0c0e03850400b810702d01d210b456884050105a030941c0d54500e03100b54042c102c070f9014495503c0c04940000c0c1407001341809405000200f174440a1071911602d80710f402032100c1c040000c000c13400c00204100140c0315030060b00034201140d003552040e500b01c6040c081e42e170310740c0e000e02004c40d400c10b1101c0c1c250b44010380641c000e0410340b0031401440d03080241c0700c50700d102d40100703002e0810025000300c2c03080e807100c0c0d000b0000509081c0c8140c0d81e92036401440b058100e100c0c40d1008008545c0b1000d60704a041c140ea011010f031409801d26071038100107034503030043c1c0e17004405102d1620f180602c03000e0604100c4020300085403d040340440d89003 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 893342967 1250 893341717 893341747
    0xf0306060d14040b10060302040509040318170a0b010906030c0b0f070204051302030c120c01030509211b010c092114010c03050a02090906060a03060803120603010c090303050a030e070506 82
    0x245c4c4640f5944136000300464450321038000c90b41a244c0c050400541358641382d404403606410046402c0c50304c0c01806010844181031080e0141d080880c0e001046510841c0c142228020303030682c010320700146040000c00014080d820100c04450a41c7c40d080d4440b0030038034140c003c0780704805000b544a440d14041100110900d00c40006190003a41240e809401c00803d03c007111258188000140d80908010941382d803098103ca58004200310603150005006405801c813140c0c03413000c2080d00d0360b010801d40c480303400c1005e0744c0340202c0d0664000c0c0807603800190f026002118038080c2003060f4203603008200351408500140702c4140d5100e103000d0058941001064020a0034601c0000002d052102048035010316009035840e4010007042020191100c404009465110b04501c01c01d040d1110000649541b0510150003862821b040e00420707131400008250848025920304000e0101c0c614050001c0780d80803003134416001807400c002403140005020145020410703840140c0c8001c002525440800b080 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 893344217 1250 893342967 893342971
    0x1020c07030c090c08040b06060c0a05010c0c030212090607030815191a070203100207031b0c05090a050f01050103020a0e040e01020a18030302030708030709081c140f0306060d14040b 80
    0x200f003040102c80104141103841d0101603d020740f03c5155140803a110b85031840041c444801400116101c040c0760340c0d285403c0d50f803034030714410215240340601c2042c1a0140150510542d00000703a5140c054050001a014010b0240c00b904002c811800904446c010300c9240c949448000c0083c07103420414111011144940d0081d9403409032382c40302d1511800c82c0641500c0049034024041c0550500c0034071400300070f40010605404202060b80100051441641500751550040403a945010b003400e0a01404a0018108101103407030f0004014001c112a1340f1581580d40910b005a42c1d68010203007101c420561004081c0e20a01e00540d40c6038400c81580104141c0010381c461007071450340c9281c40c102980c810304c4080d002d1b07041041013400145c01c0c1e40080d54090074604217400c05e19141d00710740b898000c1024268070240d151425250300103070001a100f84035502c8011080ca4441001c1c03136022079000150100d4000c000100d1440e00d49110f6070400c02d01500c4020f610601c3e894541001030b410201 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 893345323 1106 893344217 893344229
    0xa05090411071e1709010e01030c1223010b0702090103030309060204261002090a05090a0e010e0d0e0105030103020d0f1505010617060a0806010b030901020c07030c 72
    0x1103c1a81d0340079007a0b51405503440f8628640309111051032809000744600c2400692080ea82c01092007106050a06c0d0206034011840c17000d440301040b4503e4600c2e0304d0b05003d4440380d0b0104102100301400c04121300788909903610450780020344a02d11002e50016052801440030034001d410407406984146001480c00ba5181c5105a20301c5007848802c00d4106111840521103504000c4200b00080048045151009030000101a49800d21800340540d000f100040c64240321a03112280d0360010324000d01c14009404200c1c2e03250001040d582d001310390100d200a039194403840589040e079501410150b62503d454981c4102500d45410884903000981d405010498050140c3c43c02801641c44103901d00d00d000040c151407080060115004400000e000c004e402e2000030744034111420302005996a480d2071a2a5003e4441d041e50074509105000000081000c410b202c102240c0d4 = true := by decide +kernel

theorem cover : BRFrame.Cov 893165467 893345323 := by
  have h0 := BRFrame.cov_init 893165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 893165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 893165467 ≤ n) (h2 : n < 893345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
