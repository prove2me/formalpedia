-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_1076
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T01:07:57.476835+00:00
-- url     : https://prove2.me/submissions/a9935867-20f1-4831-8884-3333ef6b1ce2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 193345323 ≤ n < 193525179 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 193346573 1250 193345323 193345333
    0xc0706091a0916030611070b0c0301080105010f0303080f040c05030a030c0c0b0c030405060702010e1e01080114030d081f09060e07030b030616091d060f0a06021203040507080706020f 80
    0x2107103030021640000d60043c03400c9a0403000d003551605401424a0500005c0710401044480003003031a41e04500e100d00500d4103d01c2e80d03581030418040c20f56206900412034111034840600020383c02c507018950103078000d03442d0010341c7e40f142018508004c0315840301c0d4041c010080c003101811390007070200209174020307d540703034616030f85507500e5580344160b030240151508140400d104601d4400000c241681c0145090081c8407022000122106c1c038501c0c113103089024020040e0380e59600501850300524100b100308403004034072404640c644414160081c00c100e41e4030000350711107100003a40111442e007003a00c0420305880d807001100a201c14010a10764094131400205218481e0141030000f8101401410003a101c1480d420302c0025940142c900384280b044020032071440004240140390799104034200e05042440a01c9030040c94007c40d140940460070041c8070080d00050b190b40c0d00189254032a42d00d50721402c0050400605070000419401101030000e101c660009403010440120020380f4 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 193347823 1250 193346573 193346581
    0x15020f150114120708011503110114030103082a0f070b0f07140f010c0305190605092202090405011e1a01050a050c070609090b03010b03060f0c0706091a 67
    0x30862801d100e0715800c100309828065590810000d81d000001000040710110741d01c1d00e45403400d4a035103440700c030311940c04c11a0400500c8075009494207a26420309205000000d030016041e114403050101034043d1800007130710007031403582440a8820302d0501407080c500700c81f00341041ea01e6443d000b654590521a5032004943c80e0542e00440d400c0480481d416441c109840c1d64400d84a0a0a41c0604141c041e080c41103201d110203006203440c0c40501d540004041c58242855a04d00d8441300444007210300d044014401515041075144e0818180c144001054010404e0350905241445e40207402113820824482003001c150400c0000002c00755004148a0340c10a00d8402c88140f22a8079002400c0c9501c140015400741c0010400054a4a41a450100d070301480074a440c3d8540e002500090035044200003802c42c52048c2441c4000c100c001f800840a442c0000340e90b200044c204010b270f88084004a40d40c0304410781140e4480382c1c4943c050000e04001d0030a0000c1d048840c1d985814910444002 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 193349073 1250 193347823 193347853
    0x101b050114180f25080303100f0602030712030e010222050909060f011a04120b060a08070e01210b0108010605011e1d03010f06080703020a120b0411040615020f 70
    0x4030143c100c04100902030714009107440c8030214a20440904401844600031038100380a00007940709410b01103502d1a00f618114205a043d2210b50101c02103420a10500000074054904078200f400d0614000c2201280c20900500a11408001005004031200c940303c40168170301c0301008442c01101c030310b001959042860341d20340d5011914807009014100062100c140c0b43c1800c00d140402101c20b06080c141c4940c03903040034228006040c1c03200607281c420030070f07a8a4540108405028050041c25100d882d21107080120001800303014680c0401031480151590400c0e02032801075002540a04556540c4100c0c2e8000e0006015140c001016503080e50708410741801d0011454200799101000b03026810141500c802030100c405a165484e4a482c0a55807400c1c010701d00070300b039104040d2103001d1840c0304000c8a20350301d600c40202400c0140d4102c02182801303c1c0c0c0390303020350081350000b545e140000009000300482c5c0c014401203030300c01c68030030344aa81c0050301441c1c0c00005400c40b140c00440030a5 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 193350323 1250 193349073 193349083
    0x3201020a02130207080403080319240315020c0d0810060e0a0e0703090803091e0f030a050c0106050310240e1902090d03080f0c09101b05011418 63
    0x80d4001a40303810000d410415a4010403020303025085c890f052680729600c403040ca500a480207540c040d1944a90ad02e003050910a42038201000c510401861410f048038480700341081c0300241410359000180140900180c0443d413004001c1801d03109407103036441010b02402d00903074000e4003440200c0340200300140650648040480000c1500518038903120800314140402000e8008143c0c50344045e00020700544040c50090800c480580900311641c0003c0b02c580ca4044d0580c40345500007406000030250102c210350400126141550399072070140e5130f2a000d405168402a01842000701802c0e4003103003903002120400300f440302c2c5901c0880e0316001d980606006d02075000d039285510089074aa042c02c3d940072850781c040e150003506055000c0c00094680107110b60036000304000004104041f0481c0c440d450340a4401c40a66051105000100d20040d98096030780091007801105402042e2500d040181041d60000003408810000c0c401c440030b55805984071b064241c0302080c0d0000300340740812 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 193351573 1250 193350323 193350343
    0xa23040605040302040f02160b070e0f0609040e1207050709060501031a01200a0605070201050f040b150a091802040c050a02030f030c04030210020607020c01090312110304320102 78
    0x390703203828141113400704001000391006145049030b0802500104940e44500e440100f07024403c0340249103410500036210320b0380900068468100070443d403405549101c1503501d000e030192400210300711b000ca103180c5010280c000c80000d5400105135482082000184082540c030000410b00c4035940d500c00650517640710044d0606001c111803480c05c1079520030701c40964021002203604411aa01c1c80d007075400c001a18005480303042d02c403404c00850031b1702409042d812408055203c80907181036180c1032030120025000000381a003c2003c0d5941e980c481c0c0d11080500300b1008108031216070301e0702c221954540d111007240124100300700c04030a24042e80a43d4103202098000d9072404640c0a0308011340e41c0001c0041008000074400803001d61a0459500c50780c5415400804080c101244060b10f0400f000041a04002c6c82580a1000585007005020680b1103403c6c20501c01003041e00c81415800b680d0000b4a10aa29401e0400080d850f0f183c0c0c1c286440f01141c54240301000700340126120310b0201 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 193352823 1250 193351573 193351577
    0x305120c030a0807030f09030305040b060909071a09100e030606030303090c0609030a12080406140403140307030605040c0c0204140106050427050a0902122d120a230406 74
    0x200104080c2c5000702c142c80d50004513440c000624540804400088848862040e80029942e00030001002180361810f904002d00f00c45001321440c1528002d40e41d071354203000e41202c1c640e952007107850050202c0e0540f000d04100511998408030803042c01400c110340509400d200384a040041207146c10003100300da004000a6000c5e0217030160f4032040c0035440d4404000103070144140c00c2ca94021490f201c010f10418640c2e6540c0d458607003002d040c0402600e0315003030070200e110802800d000001e40c01544c071024011000d01843c3d1a50b4401d030081c1e00400c100e904c01d035041814100d41c2c10489500c500c014a60f144200c0d0304008121a070b00e46500c042000f4041e503130101d4401c120600c07061540510301d16641c049881044111000d185102040d904180d8940c40c81c0342d1185040030841c50f1801a8900b403140000040580446a46508001f0120302071403eaa03461f092161882c1034500740302d9000807214804080c1ea40d405070140c010410320f130b1142402e600e01c442400c03030480316440174201c4080311025 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 193354073 1250 193352823 193352827
    0xf1518050c1206060d0c0b040602070501080c0a0507110f130506040c1b02060c031309060312020f0c190e090d02070e040c030201030c120e0a12030605010c0605040c030b09070305120c03 81
    0x103441401781d01e0769842402e4450303d01e40500050000345d08070003040600026400b5010301d0b880c2c00005000b41501420a406e110010b105040c0c003030341d001040d00caa440e00400c0031090304044030041a40058602e548641000000e504851404e1450304101d01030729058404102020b10b0349421582d5240d40c01d0345546584c070f06003c0c0001742c981000076121018441044da46001807003007040300f403180e1a0740441107003501c3c0c003410001c2c42072000f6194044865400a004c042111810254941c103004020a100340e0714024520002524541554003400030b4511850860034018055540c6074641628040103118468011901259001c41940035a60145000d511142540d006401401c5c90090b1313401041204074800b0924042409541c2e0810030400c00f400f1402c256003801c1021410307040700303d402d1500300281005144da0064200660a40004000070142c54601d0a0f6420701b0080e880034220302918800d100c40600b011800204070391046045030103d8241052014541c012030030b03618140d40003 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 193355323 1250 193354073 193354081
    0x706020d09120b09031303030f020c040c020309042d0203010e13030816050d06030b1009020c033103030512090a120c141c020f010b030a0f1518050c1206 67
    0xe0040300390882c134080152810886a170100701e004400c40d901c107500140200081c58201901408a404d10f900c06882c180225045488042d40c1d0b48519507100d1f0107940d54a40542058540079090042c90700110250300440300f0fa2a00b290107904203010380249100c0c0300c80032400e00242c000441c42001e515890b0300309a0760b510203900702d00109812254050000411029405502c90700c540000b80d40300ea440482503081a130340c031446260954011007101c520410000048072030000079110b00070303807040c9150700c0c00000c540c1002c04143c00c40320300c980f40c40c15250040105a0050098140c414130081c80c42031581ea120b462a580704100640a401d8200d8034100c040540c0c881c06203405214025404c25500c0d001e201404ea29040304a01004c1480b02044034803070269906001c840b8030381a8640080c407004000500090f20303240703010001403200900c0624842002144100050703000c4800200300541c59403071544050590843e80e040310a80200c685030a0140f03000c000d40100d518664008181d15a2 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 193356573 1250 193355323 193355333
    0x120a03050304080408150403020d0201050603071e0803030a05061002070302011b05210a1701080d050c0f07060302180402070f0816020303070f030f1e080c04050d03020706020d0912 79
    0x11015100f07448908041002080c003000810180e0359008003882d0f009054507241c03c000303081c084001a0802164100010b00c4603998000560005451103410080789003421122001103811039a801440e2a000200401c900000b50b03a00580c400e1505032010392604213125401ca8a980507130000a01040000820310707588070100080803d05c500ca0f008407450025a000c81b10015a030841d01080007007400200058200c1d402400314100310f080030300680d103550402c410030303485a0701110a20200040842c103440c0c03c220030045114080303545825202999124403000300170303500c440c40c0c542a40130209902141030400d8403c440207544c0040320b009507110380750384560f000d602000e60800300304807450b0158056a4240010100305110b1a00b13003080111900d130240003200e2010030031701485503812441c100d000c86036040c04035500503032174403a4a42c1d440a4010289000d01d0b0001a00480e443d0900300405800103035003810f071400c13602151a200e0f4000c0c0c00711280070060144806030340542d500d5000080f = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 193357823 1250 193356573 193356577
    0x1103120a23060a0f0302030606040e010b0a080c0901060e100c020406091404020a060504060503130c0f0b071401020a05180301020417030a03050a02090f240d0c0806120a0305 76
    0x20140880110304403031549070a501e099107a00c180c9100c03440080c01e2007210314055502100501d8542402c040c00c0307246800003505e8213001009140500e498103a42080a01c080d48080c41911000b040710113036a48403486103aa54407480c05071801101200004a081030141b20088903c00c0e004107800340f81d200b0004102c5243c5500307030040340c004e620360a001c0303a00e40841c0240042c090b07500040d1556840c041c01003002c03550041d8489802d221003003006101c010f5011044a40c087d40750101b000007803405207085000c80c0100c1d804043e500da203d07007010904040d010010000c1502450a0b81d0700600780d21441c9080b44941565140800d40401103910340c0341c042d070101e140c4600c006000600300365076001400c00c8419541070300403594100041e901c1201e03425224868003c040100110f040c003a5000200d07010107541a00f4034401d0410b440441081c940861020b10090707909103034603031141081845800038008d02d04219010030140030000d4141c4c10304000c1116003424000c0200711001c100c1d28113448035 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 193359073 1250 193357823 193357831
    0x4020f101d0406140f0d050607110114100e2508041b081e07090606090509090606011709010e0a060506030d08060303040e0907030503070b2707051002010b0406080d0f110312 76
    0x10407000c6c80404241d041c00707058030507c59904c401c842080300303141c06400c503810325880038111420003081c80491105212a00203494404044035120303103e400c86039030700048021481040e1192001451415944000640e018a00c5803814850040115082d4040d0101502801a00758048010b030340d407640700369400042e000c5031b50302038400d144d40720020081680c03416080540400d20362241080385081c01c00d0310a13441910130300505024244580000c0006c13425074022520303026014041945000d0a5000111801321901181d00d000118a4440e000e4802201d400384280a6400514815801403080b40e20681d4018051860581802107000c55130350050405a1207210b00d00c804800980c00300010401203001d92440445440d204880ea0640342000060540b80d44400300810b034007150016580301134034000c40d02104081280402240103102009107070754442e051510006040c0c001180b034103a004000e60741c10040d1a540c1406603281c8114000f030030a0b0b54030070022916042c0c0d5003e422a00 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 193360323 1250 193359073 193359079
    0x6170a0b070504170a02190803030a0209060906070c1403030c120d0b03030a090f1202030312190906060503060f04030c120e10080a05100b04050904020f101d0406140f 73
    0x1090740b904c14034040d10440c04440307002c1d9841840940194603102604185c45100d030700303a40301440c0c202041c1c0f6440e030002a065002c0503402180d039032030b80c0d0340b00000d4410182000c0c0050740c0721a03050800d000c20b21a6480307016000482d1401840550a000c411542c1c44070310f41c0020304241900c050750707908540c4030100340685140e03501007000b0300742d40610003821066115510807030702500b0704003401c9040140d907125102200003e43d03560016200031040d101d0340c00c10001030094076a50321040d582c0c1000c0f6013020940c0d23103151034203c00c02c100d050307800113003a0343d0180d0450f5115070f01c2d600d00c0c07403a80720182ca001c0e01058107915890005004100220390503440762618001800d0781d8004202d261a4034801c440225a8402c100b080104251240c0c6034410050b0040c8170325a440e08042d10300c948124021680181f190000003000d54032030300e010ba4101d0101412a0140400400c0002c10703001410021620380700844540340158505806150207071129080705095140c403900822401c40e04078003050790 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 193361573 1250 193360323 193360327
    0x7060e0f0402040b0c1606300609150902030f0c1c02070803060f0109050108222a0b0316030c0215091b060f0306010c0c0810090606170a0b0705 63
    0x40039807a0350010300001c0c100e92800070348808020801c1d508100c810340c0105500003c05400b00441c0341c0c4140000e00d004084100500702c442c50071a40c5405043c6503980c0c07070030a4200b00d00061341050700d511440c95820301189884610b500c84d40e1103000d91009072541541c0308601000b04a0340c1406000512154100c21200480441d20240142c141d03003140000b41d503c2d0402104015442c20540108100c1c18000d1a216540f2814000060182c880103418000311400c1d10803d03031400c5828038440c40c1e940f034101d903d10703540410a014191680308451040000007801032070004038030b02c5800070f40303015526402e0924180168a40c00301c2c0149800103402e0114030480c2501d200449603043ca00380070b28000c8003d45015181c0c0030150110300041d811290141c242007101140c16907a2409498000703900340707400010003030749040c00810410545c2050000e80125021184140c2083d8010703504540302d45010b002d80740c0d032001c456126042025031100141c00c00005400000c0b01d0f07860ba15400348007418158 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 193362823 1250 193361573 193361599
    0x60703050a0c050106062001021e03060321030108011404050d0813021e01090503031303060b0d05031201230906040b0103020d020c010e010b0904020d08090d0818011101020c07060e 79
    0x5007511003a80c04403000c601f09451b0002c40110740c0040080b9414004c00940c900f0614955510008075101218504650040003040b02d682d810b20010341d901580c000e24040c0c640b0a81061746840e8400c2c89841c0c00f03503203000c2c00b4180701081001b00724400c07a00103019104800800d4801d841c001c42c0201800141c406048440c00169103100d9081c8865100040c10a5001424400034010003115000188203501c140140c048500203840308070141c03641f22402142c086801004500601e0000400800d14080411240c58000c030400034281220503801d150010030501c6000742d40e0018605428641083e20140050128100340d00f0588003503406160051514420b0056201280c0080710740400b5039440b200340c9402d03d40240112124010120ba01001c0c60410350f0015200501c00c805c02442d20030f01003031910180e0303621080d141c40560021040c5940c2c0048010311b82901c0481400309d400b142d015000b603000c01005200b518908000c443c028040c007400c001040e101c41c1a60500c8540c0101503201d08 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 193364073 1250 193362823 193362833
    0x30412031e020c070807260106030206030403020a060515060d0c020a120c020f040b030304210b0106080708090f0304050d020a1a210601090308030604090f0503090102011406060703050a0c 82
    0x48940c1d900caa030700043e10758a10b800840e00300070180d8042841d0b07501070f490601035103280b91600c210903290f561260441c03810248140c2d0141210f940302075800a40841040245600400c80303829991142808200950325000c1441220350a0800030707401c0b07401408800b003200e000d40d00c2002100210300480b15021450380c0e80e01d442c01603c008440000740800700000440c01e226403003008400c002c507018041c505545002c640d89001d144902004096440c64441e04c000d08841c8160801d5000b5507080e58941c1c50340c201514141042d9080c5001071340c9000060083c0101080550594562001840c40d007480c2c0320030409242d00684099034000c805074400207946901d00d00304004004000207003a00c076241415800303e08502441280082c01c41d08080001c180c3c2e2015501058a07030003070f6040c1d1a5200c400128005000c02400107000d400706035012801d0150000140c8070400d000d038003e003c4514401d12210f2901c900b0b031105500710100344040d01c000381c060005014080ba003444c040380941602d07110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 193365323 1250 193364073 193364111
    0xd0203130b04061b0309020d080a120501080604140303150405190e010c0216060504180b10020601050f0406050114030403050705120a030f02070f0609060617011a010207080303041203 80
    0x42143c2c1150380d4182030702004500e4811128400340360070100300f40d01c450f0700840c0c0d0040300400010040c00c00058614029806078280b1802074448810070001580c490603910341d10807081d00c00b81c645091604400d00034540000c01c580c8512504180414900350b810244009004054a8052910444196110a040700744100c0c0304440d5442d00200d0001c00602000c1d003001e600021400d0700510400003406602c0e0023504a8044420500006000c40e8428004100401400c0f2915501a81d0380d078184603803950020740d260507110215444d018100d814010441218903074401c1c20b0100700c035070741d220041e414440003555204d130003414000e10300011a512203080040001d00c018400101046a8a0460349441900d0104600d410110318008142c3c0b18040090004d00c2c0060078151550116400c10281d900300c0d200810214400e40c804800c0609454040c00c40c0e9007010b052806843d400602d20340c40011004100e81200020314510388958907030f0301031403118841c50000c0c982c031108010b400c1e01107024 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 193366573 1250 193365323 193365331
    0x60c02040903020c150909011d07050904060f0e0601020c0103060810090f0f0507171f021e030705040e0c0702091b04080a0809090a060f05060a0e1504080607030903050d0203130b 78
    0x4170180e0ba4041c0d0008000003180c040e0490240f50500c21b010310908400240060b40003010342c208079403542c502d40d001070044c00e010740060385201c0c46083c000503030101e0039001074020a4260213441074048208011402c44a140c841e40311160712203201d0181003807841e401090552302801e650320480e80f503511030042a00d2913034011142d07580034500c20400480314880c4041e1a210170409040e031204244050300e0408003c02500c01c0d41c51f400070300d11354020003241001004580c00340e0603d44030310700144040e02d160043d120b42c1d1403465188c070000b014142c8a00440708400e600404000040d00c402000400d00c7c0342400b110341000c50208000315900e2400c100010490344036903005540c1d540c1c00b40520070300440151a1003901c2e803c0c41020702400503445185010340794155010b50311000540c1044032442544140c203604042081c10106080c504480140b0903500d0345001c41e032403600c82141c01c40845110b00c401800003441480150203008054004682000e0001000c00d24508551034028020100b55 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 193367823 1250 193366573 193366609
    0x3300e060702180405060708130311150702060702010b0609060d090c090f020703031112011703210114120309040f0608031b010b0a05030309090a020c03030414070b04060c02040903020c 81
    0x30400040040800c4000d5000b0752500e8040e0035800c1c120b034580c9d1300c1c028209004050081040f0304c00d07258407080080c2040c4100b41400d5034403c2c1401d0300082e466400030b0f50084019400c006a0080a01b40707e03003110b0088c0c0380540050f20305485140e083c8014002000100c9400fa0070000019602c60300340034440c1c800c0035028005039100c84600c1c002d001c694a001c0b98041041d014450000088031407020306046a100003a071b10071102d42e440d007e505610a0b4405410006079a984410030314011301c900c00d0580e00054500c033b4104c0c817480c0c104000da251211541006603c104690a514200b5030003014000c2070750940403034215111b1140b03d0031a085900d5008030f5800001c08001c0c041401d00850100300001d0314810120342c10300000c02c0d2030b8407800c0c00c842d0051407800041078492001d5030485010b4030b05d080c203880c1c40341424503048030070031910681004213105510010039894001d0040300c007200c04075250250803024640c203001c0a046074200507019030007010034020454503202344a4042003030398 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 193369073 1250 193367823 193367869
    0xf030a0305090d0305090a03030b150406020705190f120201021005040f02010e040b06090904140703030503010312020318012001020313150b030309060304050a1b03300e060702 77
    0x60300982d460f04018110f944100360421007070011481000c00c2c4860400e0301458081455180c1d000031410001c2c485194010341400010002099940411b490060b503000302c4000024001c0007004404410f243c2c0187c010400c0080c0040121030b8400c117042078001d2060060b61800c1150302003010032a1401c8900703a134001000d90010013150781c04510b40ca041d840844080000c051048041381c510301500d018039000d007143c40040340c103000f4400c0d17241076031161750800c488100c2d8076841c004003103403c01c0c070046850300564418880d8640c00803017550490f0000100480d460041d04004407100942511401c1c0007000c405800a0780c10b500313000940c0f0422140500040da4200e518020092006c50301c0000f00ad28509400603c0f1583c1c04001c50b072902c170080700d0054480c3c945040840c2030140c0148003c1420030b1009510040c48591840001140c3c05880d054119001603401444c0000c00c60703400c15180100c15401c06903003030003103c50404070750002c0c25807428200d440e40461134084100d8000b04500b405 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 193370323 1250 193369073 193369081
    0x50f160905070c2001050f0309030705060c12070c081308030307090506030c1806120115110c010206041b0515120601090e06041e18030206060a0609090507020f030a0305 74
    0x2401100c0e0050001d1402c1c4424802540b100900d000713030701d0010307455444003c814003842da204000380c40c80c5508180341d075556410708201c0240d0341d07402118100c850340281000603210009070010f845e02d001603088201042d50340c00c00d0481e2141a1101c044640120034010484000f1074000454044d10344038006680d00d042042c409030081080e54007880c400d80c0c04004000b1221040c405580d40302044c0d481d88955059403100140e440d002c2c50b180c1d2400c4414810000421480c5c07181d0188240c24142c0b40c6243e03000240640076100c1c00e04049003400750b03119001290000318100705164004c7c22401c1c001c0401d41d11980002d10040c16905408410100480d41c400759413080d03091942c00c400d003420b040f12918581500c52041c1c941c0200401c0c403a554032450003074031542c0303008019002022010104003040c0c0604158034103200381c0c08190010300c5400c00040c19410550303200b0099851720340780c9a05580ca000c1d10600034045c0105143e085018020803900302000800103445101c40b0340c3c8000c15030f450 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 193371573 1250 193370323 193370339
    0x41a0615030f01260c100309020603190b0901030305120a061203050304140606031b040908030a15090b01020a26191407020607080304050a21170402011b050f16 70
    0x40c0640c4c000101d002c3c00700c2000320800c0008845204003000d5504545039200328500360b0082c00d10140294200c0e00000800c60600041c0d1450038202440150400ca500994014030a445400b400002d000c248100201d40c4500204d00a00b0303401500c0c00e001060a50b241c9005201c15001414200c02080c40072050108000c40c101c480a4642d6540008150305c3c40c100b00040d5607969034102102108080c525204600d072143e420081407a43c0188080350740741003020140006004855480d80b00300c44880380818440700c030f8040c80302281416402450040c01da0740302c04c0d202c20025007500f0f4800c500f006d054889404404041c201c03116403280311403500c40310b51401409003000104c0715a824103003000000b00507070740c1000b130703030041038110702204d481e60790364a441844c080d401c41c070103410800641d00c101e1406510b00000ca104c101d250f900c0d08000e1107000c04084500b4420f540c001d0200c0c42c0703440707a07640e0080040341c01d14030a4051012580e042030038400e09418141c0446200b111701d907650005100c009 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 193372823 1250 193371573 193371599
    0x6010e22060617060f09040302010f110d0c090501210b0307080f1005040203032a0715030b030109020d0f020d08070b0703111315020304030804121a041a0615030f01 72
    0x1102c100f031490224549840014200c40c0c42c104164800c03025400841c09242c400d6200d641c1259000300100070160503100c1c05201c903040041c8030040c44d4104540f022520703215800c07070303802c03a40306849540c0142c45a5100102c0c3d0340414403d02e8403255a02c05401055070708202010040c1000805007204c1c500d551015400d0280c24011402c01d40d007000140001a1030020849811141c020200b03083d40c22185110003180c2d6120001d0040c602c50b80c0b01c00300d1004405013118520f030815490400140d080301b4145400e943c0c4940c40030b94400100c050840c0030458644000100920060000c4820401d5540b1a50680c100450642d03220f50701e50101f01036980c05102c0c901d0018601e200b01e0303091035512080e44e00d503d00140100d049804083e0b0b04d002c1c0440c005c1042d280078643c003081d0f0907151511003242c950307006c0300d00c41d0541c1c5050040d10074511000c109040c180c011600b103c20b16800c803110f60a0300c5c2c00342e600a0019500002c020140f80003048000c00618040c484000f8088115450954001c41d41c1d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 193374073 1250 193372823 193372847
    0x603060510020a060c093321020906160b010f0b03010e1305010e100f06050105040b0a050307050d0509010e0c100507140a0b010305030c060108030a050306010e220606 73
    0x2805207001070701d20840e000124220003a511800118011440c8402242c42409540c0515038544c415441c2c10500c50620840d0641f01d402604a43c210000c4240d04882c02c075150f01031000360030002c001c041c040060380e40040510a101804162600340402d2504404090720b090035a150341c11034005010715000221500c0040844402d01d505550425428103940703130003d401d45d034911514104040030468290440c2035042c1e035543c2030714600381300e040e500f9024128405038282d9051800350081895030140059800b91002000c00a007850301e40401510103500144c020020b001d000d11254200365001e01509206075079510011401072000350440d07250002d11017000c1e00c910602c000540e590b660181c269007040340c1080003a8483c142d000300c01d50a12013848009040400000f002000340007000006020600880c412180380380ea0752445182c513402001400030004004001040f441c0d03119503401004400c005003003c007181002d01b070840381604403448000e40c0715121007040005a0704840c490f400 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 193375323 1250 193374073 193374079
    0x1e06090b040b120912031321020303010303051e0d1e1e11070b04080304020907090f0b090609030f0709060b0310030f1a040303090212011e0b0310051006030605 70
    0x1800d0a12904855a010f01c1c11098189001c6800160a0080401002c00c54407034500b0110781c0c905200d02442c650303480c0004107507061408180703c0490007122448042d180511940030350f055900715503088449034080300540003000103c80b90703a004880240000c001195004c1000101e040410302e1100350b140b40307404c03a041920302e0205401e0362960440c1004407206152500000c81c42201103290445000b080700c094400420b000820081250b00e100540c0168001c54900c2303800e5607004000c407070840c40c034011101b40d503c03180010030040e51403001504000740010100f80c200a15034005c2803a2024406001e40b1940c010501004540c4591069074060000544914a586440d0380701603070306c402602c1300a1055a41e030506070103120342c1a4105080c1c00c1c4d100a404007500745400d000340980103030325041e41f01d11282e42c0b08081e01407051044120000981e05002c00044510000000138111044103c3c0c05005104081c542d404076480740d203201c0d14003401c1040b405803c041000b0221f80c00f41d0003140c0 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 193376573 1250 193375323 193375327
    0x60306060203090306180a051e0601170a0308040303111c0c0905030a02090403050702091009060e04050c090615040303031d01090510051906060807030f020a170408041e06090b 77
    0x4801d0302c0c00b1411550104e03c4801400805130001c1d1202c7c54040c80b503001412601130803500700f61031065903a218400070007a604a40c1941d032100c4081c0c503140c86400b1407841542c400c1d910000040d001d81410303070b40301e4000d0074002168030204c401c0455550020803861312019410405a003401014840d000040c01d1506c0d000031818108400700781c1e0390100a002a20038021031002404044c4120700b02d442559001d040c054580c10061791254104195003d0320b401e4a08100010649182c2c151500d0b10403504203000303000b24089081480520300c3d000c0c080c80d4104003220f0341c50300102c440318000e20003540310760b07000203008110203038003104003040ba800000030380d0502c4419408901c2c00500318400e080c2d6080c00203642d450f040c8807000e071030030304c40f40308400242000c0c2c0c005161500442d0340c510807505a1400d000d44a0703007810701e004030700c520142d08021504041c885800c00107e5160550700c40e100c1d8555500d440c1c1c4440030660b170106003c000f00e606450710074041c40020751250041d8010160030a1041c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 193377823 1250 193376573 193376587
    0xb0402120109050621071a090303040612050903031e06030f120909010803040509012709080a020105060d0b19020702030714010909060305120f130305010609150302030304051c0b10060306060203 85
    0x36106c05032032007034808601c0038052940d20241d80b07500300d03801014028201c90b507442d0789542c0075000041024001400d1450030001410104010041f80c2c441c50410103e00028078840c0202400040080c00e0640c04d44992001040c2800e0100201c1c25080b29a0b07001c551076800010030002110416081090580c009000c00c00c81903c5004445040d07075010f6041340390301031044218440798041d00040035407403820244080140f0203140010005400b4a41c003e201a90f2128103001d4624075500004090100c00400160b400101c3c1071000f01d280390880000d481c242d21034000900c0c00317049800824082c40e10140c0b10703c1568005440200901c41c0c000300344046841c1d0340743d59885200c036074140c0c2813020000a24440000158045881204842c12000b103400e8403414031500900682c065039007030300e2408250702620f22004500c0d01c202c070381c014000e5140c41d040c082031000d40311880031150741c6201e080b4060f0380007174504092039105002e00000b819051f49000e40c0202a102076904c48820741d00100981 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 193379073 1250 193377823 193377889
    0x6050406050634080310180911040f0906021c0e120706110d0c030501060905010908060631051e040b13031e121505030304090b04021201090506 63
    0x3030400500c01481074020550001050f6190f0321418600030000440001048808420400d0503003c3e10a041e51103982003003a041150100c0d4600c56000d08114480d4190202c10710305508007109d1003507001e00c0418006159601c1c0b1003a600b2820701080c01102410b11010080e8151084410301510000100756401582003030a10500c1802005050191138201005800d001c0d0401c036a805281c005c0104048070f1007400c000c008150138002c440014400000000ba690b115920078010303681444082d2400780c544d00200803276481c00700040410b10004629148d09615441c034a03003407556540c60041a0361420a4208501c0280014600e5240103204140004510349200b0700350b008a0300c0807000b030001210b043c2507860b022030712020a509401c1100340c4440c01e50205007403000380b000c403d05100450f83c010002039629258010a501079005000401000307407541c2125540200150005142812010400d82d203960b00341c11424a0507240d0081c0072181c10407115020043c640b512411061018031000 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 193380323 1250 193379073 193379107
    0x20301050a0e0c0415020307050c030f030d0b0a03140f06011d060d05010f0c0c0c05040c14031308030103060c120c020319180608070809030301180903030f050a060504060506 76
    0x85010b600b94030400210010107020450380640390707804c1c195070f4103030115a00a40c0e95205020440c0c090180a03003000c201e040010f02c49288500f10000b8504041801e040f080051040503051030384455505c80000c049a0b0001010060181d40c5000d40b03604083d840328140303044010b0f84105524030740c41a2191201c4408010725401410803204140c026030b82d420f205002d00503a9969440380d601c0d200b0809a81a0881007503032181e80b080800d1180e42c1d41c1d400c200011905410741d1031001c91214401000c90080304401558450381071400c40054070a42e8a481601d5002600300711201c96072900c0c07100350940c2184510b00103088141c1e003800b16510448000751240508003649200d544503910001900c1d0255031401e10442c00c50400b04d440c1130b0388402c020010001514107a0215031038102140b04550088105c038143c1c2c80104948241101a14001d401080208000d80405135100340b100c0c9024840e00560707004504050001c10035504000411003240c28903482244031b040c040040c0d000714820b03451 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 193381573 1250 193380323 193380329
    0x222050604031106120a06050f030f060a09030507170d0506030c1f030b12010204060e03030a210f0f06050a0909020d0209060d020a080607080708070c02042f07060b0103020301050a 79
    0x600c0c1ca044003c048003280c02401500d9200c01070785403020400842d0000f940c000d0013210b00481e01c04181c20962400d141d1207000c0002017012035048140007c2c07012411b80c010604552180c0b030110b00d48110790700d904405080881e006008042c0000d52002801c07914010f690700326000707c0c090002404441c0c002000b1014028400706200005c01507403d081d03010303902540b01084c001d8406029510584c901d2030007988a40154070118055541444c0c1c42d04000050b144056180d4489109280750000299072300c1400950300d44100741ca45440000484440c01031202c81d400c040d801080541c10041040140340d626084100c41600e04807804000d0383d50740851501d51a019130303c0580d5500c81c980410442000c4a40280d00078642460000b104400042c403d4400d0480c0e076984000da807074800f0100c1c2d1500741602d00c5400079a85220001c054502503000740c0c0c100210044010034040d0f040c02e076001003000d00e100b07200b6218001c142c0200f44800380c018410718400910301149190b052800003640180540 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 193382823 1250 193381573 193381583
    0x503060603160324031b05150322030e0102120c0c01050913060b0703030608030301030c090e15010f08061f06140c01021b0f1507181701022205060403 66
    0x1c4001c1031003d0190740311615051801000f1801010000401220000d07184811100032015849801d1111140c3c0b022400782c950060115601416000003805240c002500340e048660701424a8004018440342214900380b0a4030341d510540000c10019044c03840418000369281300801c10b040341c0c0c9201203821910740800742041901c6d40c0300c000114520440403001c84040900c1c00d100032070300a10f141d019000c0c0720702c0303030394240b003015110320f40140c80780800c0c0b20081c42c0310170000c1c00b40700f0003030560001e051151006c001c0720607036a940b942d07003842d2041c282d01810303401040040500a499092040725032002a0484036125505504d07902c001805840c49a030042002c0002d1460204d80d10b40119603810324510025034582901c000444210007a0031762080781c030712a00000030b034808070108003e1b920001062840360756603a2500142c900c00c034003400c14082c1c06030030000032501010b00c1600103081c1c03522000060302c1d01816802c15140380304000f100c070f0582d01800f200300416610401281c064903880 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 193384073 1250 193382823 193382851
    0xa030503060d0503190e100c0f5001021608030618070306050f010c050703020111010b090c03101d010302060a09080109050c0411041d0702070513020309010b010503060603 75
    0x1418468114000c0785d00b50885001d81c90540000d190307000e420400c84000860311080c000c01c04c10390589a030307010400010303e40503800d54400c000c981c401803402c06801500c0015042101440c4c00c0c001d196604150187e82d41001a2400882140c450300c000d0020145078001c40c980000e02e40f00a8001084c0c0c0401410800c0000c0096203079100c41c040b0b01c003c00301074189240c00b8182250080c015002601413140200c81c5449210302d558400c40405c581c8540160252081c1421034004440701140c08004192645d00c409010900f916000b0110340b045010340402507c03401c01c0c00901250410692008502e2104045101c032000751031071032181181e84c100c4501ea50368030758000544000300650b01c03440b890351070144c0da5014020f0108882c468040d0884042040c00300991902d91140030f00d016150b070424000ea9840710310a04421000d80020240c0106c07802c103507480b40003981d038070a401c603c904c2d085d8002c01400445c0100b405600b52101d400d00780b40b811403421f00702003000b40c0001404801100c8036 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 193385323 1250 193384073 193384099
    0x3141803091002010b0112022104050c0607050601030b06040903171e1f09020f07170d020a1701080604020d080a140c0703050609030405060403151e09020108090a03050306 75
    0x810000c64010110240a00000304070040c0040e00030b01d050a042800b0441074a0001014075252080314a00143c040e0f0b0f00c01c95070000198101d200100820442d040d115640d2006220760b1071001501d8030300e1103403000f450103604515020001d41c2001d031449000d01d0034119024002034008466035a010f40c1d88904a07480d40e00d00c440104108600d01c0d072481002090024070400c201504044402056503400c410314551399842254202e2244506012607013400344a020001590309000e44003800701c0c820081c0c180040c45010030b00302d0307006000c500041a0100c542d03440000072499546e006240f004e0141c00700e40781540100b40c03140140500140810380c0000e44030401406210307000161114419081d86070f00e810400c8079a0f0b01181c1c00f0036502c1c2d201d4040001c2c0d00c1000041240e09844000d80060300305481c1d80e42c1da6204402445000c910180c0b910a5200c5800d00a01404100841180e000c038401404e80005001e2000c054100c4107950410b03050f40020035005401c0f660003083c01e551000100c20 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 193386573 1250 193385323 193385371
    0x10e060112061503031205060108010e0c090103021e0306030d030c0801060c081902031c0504150c170412030f0b0d021c0503130807080307031e0309080705070303030605010314 77
    0x1c501c040c503c202180454001c401d00d6400075030381e0707245082803600b084981c42d04401901c0f400c20900c21450001c0c40e4000107a0344500e84000b40420310342c181405070414a000210150b20082480d8421542002108020007403904200c0300b07030318411301d0070200030a04503100000c2c00e4240502406040c000c1d0a02803408014840c000c0703400e04440c00307542025066640308002d449920200c0c11144048240e041904605140c1c854140119130002101c1c041c461170b4030303c58028180e100c0078541809403151050380070032880c004484c4514814142c1d0303048142e2540b4082d08503101c0c40c11400500c1e240c0142590b50307444038818551400d40464620100e049495034005110828100003003403404042041c05480c001c03000040146c8030290241e59642e83c0b9811b6035a41e0307000307616010b00005c12500d41011f00800c0c0c100401c04905851a01081030400d41c0c07140d00306a171040d001191140e00c0000700b001495450311400e0043c102c00d00e8280504005001554261200940040c0d80400d00318801041c00d1 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 193387823 1250 193386573 193386581
    0x30b0a171636091b050301060b04030b090c09040308010305100507080a0906020d090309030506090c010c030302090d0b161805010c08090f090f04050d031413020a0f26010e06011206 79
    0x142542c02d00c4000d0003490280d5010b44285518148444c0030100440ca030b14042c0070300025240303290341e40d40c00c1518584502e0030000010301618024010101e803603415464103101a446140a0b440d44941c4c0d526501c1c200b4641580111071600303080c42d0901340220740303030710003040d0390808a0280046402e42c0a420404000e10450402070641d0303141101000030150080481c0040728080d40a841c1c041c0d940080e0140c41d113a60b410001d000030240041440044d000307602078110000d0150240003568195a5020f00300941901c0e034003509407000d403900b0760440e413050b5084042c903400e1b030b580b0700060b2400c000a0500c4000000c0203200410115006056032900e072450040410010306564035400c11a080742442c41c01030301d050f2041d010f00f11403090450302a0065005110900000900316038441101140c2405100000ca9000d00065800101c1a0020790f02c0405070041408001c800d0041c1e0b040310400c409080f00b40601031341040c85040b00c20704c01060300345c1127a200c10389a0300300e0001490214014 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 193389073 1250 193387823 193387919
    0x60e04060801050a1e0608060105060f07061109040b040c02030a0f0201113007051902010912030c0e0a0b0a111606030c1d030606060a030b0a1716 64
    0x290f18082c208640800290026034643e0840814480c0390f140c84e10f034000c00e60b80c4d00d0003004815405640104106d04001008045125116003510b003080078650f24401940c21041c110726200b0f00120790070f01c551038144a8540745100840d0300f004401d440ca8806900da0040e40e07490414003c01c1d0b01d0000c110380c000e4002d54090b41407a800d0b156100038195a80085002d140e031100034400510903e00c11030891405100d0140e030300740d2641c070300b4070660b09441c1d4107902c2200449030840d529030700140c000407030081e401c03042e48020b51030201e80d203040690010081000000c045104007684502044003c2884007100c01007180b51409150309809440900d240001246c0300086803142001c000640a9040d4441c0396480126519400b8841c104101158843c9209036a03581c507800810209404d49002d01c028804038242e81004155140908006502c11803180c2c06035200c0c0c070b044001034520540c00d00407613401d4200014a00305440c1041e50031100c000043e03240c649030f080c06644d200e01154110b1030040b80 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 193390323 1250 193389073 193389089
    0x906070f020709060e090d02030a09030818030607031a06182e0309030905010e0f1315170120030f0c0403170a0e0105090303220305061303020c03060709060e0406 71
    0x108039561410518070702000c64071407840740150280d0307082e03091001c000c0750303440c907940d581d4a01d0bc2421601ea261603a40020101c3c0c8221642042c1103400b601c0500a082c42a5941d440c000369003111080c0781c01011314503109080c03040d102000300d110301c0d0140360015101d405080c1c42110389103149142c2194000c001c4d003840d002a01c000d218608080e94580c200c9007000e480780c0e46840109030398500540c0c1d10011581215403000c0c1d90581075070103080c00b400707001c0003480880f00032441ca03940a480c284440503035045600911015060921100d800b4041d400d1040b160454004110415032000702e624000a4682c0901902e40c8011404011004054174091500084072220600039841c00820170303804624030387c001c01c00c44032070000e02e0744c060026100366900140145280041400121985c0003411091220185900c100800441e0040003801d108000da100c03115408a0b850401901d492180721807a8405d40c06041000212680440f41004132501800c0c00e00c806840308000070054403035500328000e = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 193391573 1250 193390323 193390331
    0x1715040603150b03061302061305060d0212010806101a0d0507031b08010501050a0e0a1d0702121c0b03010f090b160903050303010e04080705070b0909010b030906070f020709 76
    0x30a00c01e19088000d10092681d100f08224603405003815100c1808581420441903041c000502505042c002840c0c0b140020b03261041081e00c0f04009030082d041018140c803d01d41c0414002d2042c0c4901c8800750160082c540280241d150242107440d081c0c010b0300a40f50700440300c071007540707841100d10141d4000d4111981c05100600e0300e024002c0c014903010101400064094070602c000034000d00f010b030305845043c0d440c18509040f00d00d003078440b84404150203030850490b54000401004c1b5a00c3c0d1001c0c500443e07800340c028200400d000389440122540d0b80d051060402895280f44440c500440188180c0c80303020070f00c25200300019004005440100c1111814440151300300311008450502c1105140e8044441000000046038a6003042c04001c00c40d03801000184901010042081c0e0b21511407580c1750300c0d0102c641e694a04100d0182d01403222120007050002c2940f41840e6034034007520035140303102c3c15403400224441e0381e0400546040c0c14043d40d41a80d03020103100b484840f0260540c110240 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 193392823 1250 193391573 193391579
    0x9010b0c2e050112150515030307060c080601050c0c0d1a04060e06010801020f0d11040f06030509010b1008190b0a0608091c0906260901050a1a0117150406 68
    0x61900654030100c2542803520001050100fa1150300d5413005420001c896203038030715140c0c1c0070000c0801034480c10700d8110b0b1802e52034056504000400e80f05111f1203000c1503203090380300b0251403000c01511250500c03d06214040e0a4400050040745081089513149120070040c20a0354691902004848018044400700410702100f500070307070003416036881268116a60380f0500303401c030b0048421316407a504007007144601c000201c2e0000d84c400d10301c0b2004545011b940b05503650404000398401008292110f040088941080c03040c48440078041d40e0f0030207601c01c12a00103210a40c000c111107001c0c0045004840094038540c03044008d4000a008c041e85607440743c6026040443c102c428100038801c015039003000703e002c207407422010199508c075558603a040c0441540d064004120810034002c0040d02d52010a600340007503070280c06101c00000c1d40341801c01900c0c05413022584183d54404092000034590b90b44103a081c00300d200c02010b0000b15403603420b201a8410f40c908a403e501a0802e5408 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 193394073 1250 193392823 193392883
    0x91003021314010e06180d26030601090303081812070b0a060b0403020d031209060b0f031204060f030e0a030f08090d05090405090309280e0609010b0c 66
    0x1016100303588040307500000d50701c001d0400740c0c905420681d4002901d100d54041c09090080151104c041e1034402160352010f0b0002080c0600d82180d016164482000c400300700d01c4510040c119280860709141600e94600880081c0903034206100c01010000900c00040351055601803c8051107440c4040d2110030391005140c0d082500700840c09e50340030803884085081c0348070034071a0604841c0c41c00e0b0554100f0340303960200500122041826814400e10b41413400c500ca503584101c4210364401c0000140303680c501c03820300502d903c0040a01c3d00981c48403e62802110004050302c4c1160b585d0311700000001c16001044014103180f4405054038410f8202c0714041641004112403c1c03051540c91058a03902e1040c403e685450716040f440126100f08016503990905030801d0350f00c880803404070b07842e1a84030004104003400c80c900c0d08240e29410701070b400104003000c03003100c01003402000e04800341c02c0040000da8102c0040c42003000001c000101860181c5084c403e0200a14180700310751030b0700c25a9010 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 193395323 1250 193394073 193394077
    0x15060a0e0d1202010b1f030903050f0c03030109060b0a1e0905060d020d1503030e010822051c0c0b06060702040617060105041d0d11030c010207081215060f03070509100302 75
    0x882c0c4095401e0840840441c10320700009000700c0c0d00007030301d0b060030034008400398000e01740140250b040200400c803d004480c10240180840300b402c00080d42e80e507150000350320403280c107a00010a00d0200f04204841c065000c111862665900103444201c4a480d8500381c4511405511580d0010340200e00703c628402a03a01400301032140040c1400035070f880d810030443c400c4083c0002000700f40100504031155104504030356200840d04082c06c0350140100c8142443c1100a01c03c640a9028400382c2507010b07542400000741040b80d0606851604d601c0e65841c5400d10000c122074013424021805000707641c1c40c0d8120384000c081d0742020000080f04186601d8944109003e0140200e04080e481c00000c0a8010158400d140000160980102d000d1085070303001c1014030071100c0ea20081c0100c0600c15403e1008202d4544100d14543d40c3c0c004059809200c0b9900030140920303020082041e102076180c90b012280400c51b4441e906980356100f08003a5542e019100917981c02503240e00d0800340960700750b40 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 193396573 1250 193395323 193395353
    0x19050304030b09031216030605120303150a050604090e120c0a05060603070b0a0305130204060b04030b060a08030415020f0a0c050429040b0102031908041a15060a0e0d 73
    0xc0c4216065499070701c07940e56486131080c800100400003001031070002d0405840005100d0604d408588140e50310f0004040c11001c43c011422b5400c004280b08410501507030500882406554a052091400000030b01e980664810550b00301d480381100305840105000e50803883e49941304903511801080301e110f46c0c4000311402100c0d580b05080110301c40b4500056420300b180c801000c054540300184504601034000500034046909407a501305005a540e0b01076840605030307030355003140c0311861401c2244031464041c19080c026424001c0900c4804804001c03501a246268240c4411081c507000491030070f00b4000104c2128040c01c10354004212000c829041180ca0841d000c6c00a4100c5000d095403144100104441d81c020340310f164650b5040035000990814414016a81003c0718006424030704800f465060740000c01d14420002005118200d41d001d100300d24104000030b18020103880d10019521080d5417080350003207003a18425114603030036155650003510507642082c080c80e0503941105200 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 193397823 1250 193396573 193396583
    0x8060103050d0206040f02041d06010602011e020c0a03080c041206061a0a0e090604060810091208070e0d0c05130e07120503090618060309030702040506060a0e121905030403 76
    0x1100300714544000340c0136008541025003042035140a40c02c00004240074041040100100ca8500818150901040b070080030760f82c0002c250b032041e25000907031311441540e0704a0510f2040c840c0c8400d400002482d400000e5040c1803018954a4403401c4030200e024541c40f41e910134a0320401039082001030b802940454005c8080d05e130a0880c0000b540d1098060444800d0000300581011443c41c9008404075420a0780a030002602685030307660b40307082c01c4069010681d9a038613030403414100b140d0320f2140000da404500d0300003494107040300001c00d20500c0c0503241f442100c20140b2081400100b0700d103003004000c0140001e64038106a07644101500d612490781e0000c2c014a00006500321030303a480c41040aa100d00550314015003101044215001451100308002d26620742d64101d44031007000310300500e0200c0c0290303166003180c4100b00545100410442c050401404415180c0e034204103401c80c10802191030156402a25145a2030041c200102012000261040f002440070120040054074011 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 193399073 1250 193397823 193397833
    0xa03050d022506091122090201110f01061e0305060c0d1514091014061305030f060a050702030a2a17040305010b0405042f0a17010f09050c060c030f03010806010305 72
    0x2e008001d60450354411b07100d0801d402032009800080d0030f92085040c180305040000043d98140384142c81c3c10061401801d8682d907420b03060041e040783d8402da0005017240a4882c0c500c50846c0c0d2807a03220b41000e0300d01d4000e4000480c4003c1101d107a0b40100d0701407444141084030041d9035841105030701e500011b07102d000c0c03a08403020031014a1120035076000c3d00c80e0380051030401e400c0c0d90184245944644018601c2c1d5a10341c1000c101541c00340301c0c49a4251000004000c076040064402045400c05402030b0103541c010069245401d40000c2090540203401c0c400b0101002201e0044440d1503041c1c4004020000b440700c945203c5201001903c00c5c0c0c0d0081c4000c200158451042c0000c696042e0f80161196004d003504c0d4291030003c05001155411013800c614061701e483c2c02081c00c1200c5604803a2181d014042003c2c400340c0244540c601194590206020100d45034039090b44544040d0400c6000b0100010711007000202001226411080110350a43e6036944019581d00c6810a0008a03424007903 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 193400323 1250 193399073 193399103
    0x5150a0810030b071b06061d13030e010c03120c030204080c03240405030d05070c12021b060d06080304180b0108010b1c0902060712020f0a03050d02250609 68
    0x34181e0381800303032540001e0891440c2c80343c000c00e542891400c4651046510342c21913240000d13141e802044001c000100c0101640c12011a09189400340148a0400040003506510110398081c2c50900881401e0800500c07035050b80c14200d580c0d600302c264048a5074240824000c08641c150300810894031258103403209005204109601c80f2844295002c03881805941880d0b20b0944000560304240f083d8212407601e40003a03901000d4a4040380c0240104031543d00410a21120102c407030034601940c405801c0954078003403000d40c50303891000000c0c0600d50104000100200640c42503000e8842502142d444594500992420800c910300c128481070410401c4580d9500a041c110b040c0c408070b102090419400c04c03043e9408200555011501c00d8035420b090700075031035034030040034054080c0700000304000304150043d10f44828502410500c0d8080202400460b5001080e6600301c03000c1000941c1e21000028450101039003544c4051826542a03a9401003103020380c012600d07a440b8100c03100401070 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 193401573 1250 193400323 193400341
    0x7050d0c15051f081515012c010816120e241e06090403030b031002030429060607020918060124030b0132160c050301020f0a0807050405150a08 63
    0x4000701300245c1e90142d400c0421500101c5002c1c0c400300c1c02c41854602c00e41048011400c040104048010241140c021740701038155910415040c2d010b030452400d4140c032400910028005903610f40c001074920790b1110601001d030020f01900c021900030710421405c0700034030b1002400d900f8040c2c505220184440020085c0740b180c1c00304540c800c040003440c0440680c1c0e1914150094141c2e810034950501079800d440c0c0038003034203102850240e801600304d05c000c0d0151a0540100d0151003014a06408000041158a03528030301102c41720740c0d0641d040d80c0213440e0489000032880d4442960481b03401000d00100310300b190701c0f240c0040b1300d00340c20403103140e10600d82048c1c0854a011380b94a0024804242c281310720035915200312940c502400184140c52405182e140c2550070412000c4455070075441e044c000d110301d040c51340d00070340340480003189440b400c4440c00f142445030440510901c4203d1000079407583c06001a100140005400c0c034001e126001d601d003966501100740140032a07650000b20304100 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 193402823 1250 193401573 193401583
    0x115030e06092b080714040801020f041706010302130e0118120f0e090402060307050c06041104060815041707060c030204090513031d240702041107050d0c15051f08 72
    0x7002c5919140301c1a12144006c0341d41403644030b00c500c0f00f010104000102090248020322840c2400355250303440d0f0b03050106d0f03002c030000c80100341c0149074002c90040c8056501c00c0300e03443c041d2501e004006550301100501d60301610002c50303841d828015645180381400349000400d080144c0c00d90f40d01d2080e070500d410079104010303000e03010b6401110600018005081000040d50480801c0c24140d08240c502c40100b480e03d14101c2d021580529241c0d181003882c1032074051140981201006051039112420703448101c000c00810181202c0b5a8484800c140c04070b4800b21002c442d08404184580b03a1401d101402035842841812402480c000006064203c107910b4001c200d035041c1c0d2184401301070b11030f00c0e204100784141c7c40c50f48401000407060a080c402c4a407124404003000000340c40b0304103801000110703040000b5102e0140c408005610005602007502400d14105c0c2c00c0030400b1602b14200345160000c0c4021200c003551401082c810b403e0341a200d0101c1c806429000d0054080e191001c02d5200c0c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 193404073 1250 193402823 193402903
    0x6080d03060f150c0305071407061404060804021e06070c0e06010f02100b0109050a0602060a05060405040507060810090908070c06020318120a02060415090603140115030e0609 77
    0x762030f001c001110b00920520141108a009103400b0303081580715110140500300341c1c0c00c0c42105a02c2043d003040030981281640d98040002004075080a19009002d00035000c0180002d2003054085844001c00300502840d01402c0c002900d0251902e40c9441c1008025443c3c0c014190309640b03200c0003a040c0d40c41303461150b1845195901030041014030340c400d07501411000083c541808a8808003040c152102c4004a0003000c00342d0050801c0d040800126048440c060910340c0034600703002c03c00c8041a000182e0303500311b0303003a440c0402041c0d64a180094440300759401821a05040181c4c0505000d4088090410f9500441c002034a40fa598041a44e80b4400c2540300780e0a01900f43d030b031003018a4000611840301e82610300b0703547d82d500c23141d0000c0c01c3c41e4416001061061f00f80100500303166401403880000d86024202040515802102c45143d444148a8052450114070941c4178040c4290080075161030088111101d606240d002d84e500d5003010949851201800c5411035032040181c03040c5503007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 193405323 1250 193404073 193404089
    0x51515040b010e0103050405070e07021e07030b070f030e070609050f04050126070302040c0207080d050a020319020109020406030c0626010b0a021f0b0108070201231906080d03060f 79
    0x1810f0f03440300040d8040c280040c400da40c9402002e03400070b0a0a0143c1d01c0c54400d100b1580a40301500c0300300504c0700c082c60329024200c0360f44d00114003400024545900b00d41c00c8032440c18480d04000e500c1c60120003805443c60102c5d42030040050008180d50000200c2041d14411101a41850545414801140c009201d6101504c51b90701180b2010700c0031200710a00000484203442400380c03207401240c02e852000003200d00680c4210020000f508003031040403548001460024900741990358001d42d41e0090111030049000e4101604510794000d5208407000f60b40500184107279a928100341c0414040c40c496070020500b041c000001c03038804c1c584488040007030000740001caa4240020740055420040102007035100d4281481c0c00d081800b41244804d881e0441c000c00c0341e850103c001000710b58060484415681000f8503000030942390099140d11504003410301c23031765a03202551455a4400c1c50440e810035498a2800b107000390010501c0501607001da02e090001d0b6607116400e043c85921807140c085 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 193406573 1250 193405323 193405337
    0x1a040e0f0f190204080a11040e0f0c0603060117070309211b05031b030405040b0d020306071110060905061e010504090504020d080a050d0f05070e060313051515040b01 73
    0x182540e070b01003410482e2902c0000c0103007826141c00c02540740040c0c011303054880c85a50310352982c05150a004900104048001601818170f0f0302c0c49443e55070782e003202402d100340000b0001880070b92141451340c00c42003d0b01162110b500700304801038010b18006c202a11803a12080758955520141a8242c2e1540c141c0d42c1c840814030602d100300240002c03403200483d8103000c1080221203441c45034103e101294020006035030740e10b10305020401250b1851040500500b079604103800541d602041c100c4e442405403d003240300d4a00c01d6419400c100e1130302c0f16600c285d40791580100d42038100b90300880c4184000e80d041050300340d15130fa401c003100c69905042c6001400800c800d0040c9212a080719410900c003412403590f031529981e03880c88a800c141c820000007030700403458145a0155000303005844070040010061800c00c103500030403030a0310743c50f000d001c0c070341c00401319202210b1184d03013a0711150003c01799072094280340d000c1a4410015107401c1d12014080207a80114035040c407503812040e0b4140c603094 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 193407823 1250 193406573 193406581
    0x1e050d0807050f311707050a0b130e070906110303062b060615030b01170a020a0c061d100e0705011b02040f0b011b0203030a080405071a040e0f0f 64
    0x72400c0d5016801409815000c0800060000e104d580060660100050002a501c2c18030300c0011404c04680d01281181c0d124060412054030707040c6681d4280d5020031801350351034078000892000c43c0341940c010820103e03904100001c080d441083d0f0400e642043d540d15034400da00f4070905969000603170360725601c1414458030710b0214034404c01400c2241c4e80c0d40d4807045a1203040d140c80084802c580d10946a5811200c0412404c81d81403080b514681d4003401e003541107070640c983e2042042001091110392980c000350201405004d210f035410055407140040c4600e0f140c4c2c4500c64000700c4002c007500844c3c1700e00c4000c0702140701d1078010700000d080c201000b820864a8400111409660f50300000075080d0750000c03075005a1924010007941550074240445c00c2407010000504c2c5000808109a0040b20440c20000681d00442110f418020394a004506034a4500b0b002d42004a03990161410280d030b0399082c08800240c0c8090300c1164002d205054066840c4014806900d5081303404985c8119184001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 193409073 1250 193407823 193407847
    0x32a0a0806010908060903070b0609190203101a04030501050117030711130c08070905030d05041a0405030601030506060906010c0b0402090403050d0e0606190303051606091e050d080705 81
    0x501d510141c145010a0300a9464090307a00f4400180c0381c00c00d60360000901076050210044034a500103070291600506d44c50b0421a207011480d080e9449982039800102141544030300c090158050051056200c1d52041006030290065020344002c445a5082000000c1c040c8014444501340c06240d00280d80b808843e99105000260b4100401e940a003400395109103484582c8140701ca18071150f118036001d803e2a5901030080c5100b584080d120f5400342c0000041c0940c801c0c150740484072608040358405040203214000e030300460b00060b8251103054000802e0007000100ca0303004400981d610201e68481600440d00080121006094a10000b02140044c02d0801c4804d50281c0207241441c28414070303d101100342c0b1860100c0030b07803175404203050118034580a903440303400c8104603400d42c20362850b55401031308a005088040c00603400c2410003a0a1158581203030141c07580c40200802c80070341c201200c50700c8500c0540150781502c80d00440340f2415000c0e00080e40174060315100d55040010b0382c504 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 193410323 1250 193409073 193409087
    0x222080a1e170f0a02120a020312100b07030f140702090105061804020d0b0a0e1b0d021c0f14040302060604090201020c040608060601120c0e01050c160902032a0a 71
    0x4903403422940c0300050000760400c0243c10740c060070000807903944425000007490000900e100440071201048400c05007170b000012540714680c52803224980e5034519421000860056005205d05000010b11004041d40000c0413400811140c4800d131101c4040e5214000318024908000e4004804000600503890301e0401b502c03083e003000a0440540030000042810398003c90149000f554603000807008a1409801003000b50025041004003482c10800a003000c1c06408200740d800200080c100c9c00b1840a13070120f03540c0004415180541101a0003540018401c00408100d11442c1100380b60b08007411920709401640c1550042c09645c94001c108001050092000c030b040d4418001441490748135401500d0003890500040d22103498400009001c034049a1303100490580340c40e03440c4041c60f41051074130856801c00c1c078080d40c550309041d054510b425050044d05020242e042000a14951550002c5100303446d4210311034200e001041d0640800c081d4888030301030142082c007000041c10b02c9600 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 193411573 1250 193410323 193410383
    0x2030c07140307033e0f1207030f020a08030c0706030605030f0d03110c070b220602060f0a060306021201151107050d05070b030f07080f190f06090222080a 68
    0x3c1903800d200c5040745c0500d056a1059000c10351150700c1012540c40c035003120580c24201099814907002804952071a4803480c840c00001e00b144032132a03000c015500c8400154000e0461402100c0d0b031600d03543c601e182c0d181a944540d04c002800d00e80c0104650074003250220709990581d00616120800401c1a07007c2d100c4503154640400e030520801c4a50241000300b0001040845040c40e41d460840030b00140f80401102d142c80b200eaa0307004108102607002072201e81c4a40e14100c0300030745848160342100500a541c1c07020707100500100f20803c0c0095807145280c100d4210001c00b00d0340c64001e490031f65440985039080c482c643c001d00e82c01c000070305086180860301c0c0d10800913100440d440d9038100f901c540081d640070810001d040100924075030031044a903005003001c0c08141007803030b0101c0c55802803a008034500340c2d02911400601c0042c03403c0c0d04400040c00320360500b03540350300d105001181404581c032020440c05621150002c0c44000119004007080d4020202c6002c41c50b00222102d11800101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 193412823 1250 193411573 193411613
    0x1006080f2802040e0c03040507030f0809121b041b110c0d15051e04150f0e0c0901090b0d03110a020604031a0604050c03130507030503070302030c0714030703 69
    0x200101c800001c581d81200c084000350780050b1140c0c03c0116005001c48000c140c055183c1d8100180f2001c07400000c0c008044940c4031200c07040d801d0491802107501c0c003604110582141030707203c015407042400b2a004504030828205109105044800c000c19a841c07a4010341c85032185c507042050f0584a07541c059101c0044508950b0156140300108007200f402c140c040c1c8200080c0381c10300211415034000c140d00003604884081b01c03684640c801514508010340020000703010108c20541402c0355802c6100f0010303d0354000c00a2402c80301110b174455400a031030383d100b10840400131039880041e100d51050300c1c00142c044a03074801255070613108070b110f801d040e000a10940006c1d50040c3d59400c002c0c00610701c0754030170070b065802d0b02150b10510313000585064800d9080c0030400071002c1440c41920750082031203005820b8200b480c1041810b00025400c0a0924080080c2c80307424140c0010050003206040c10454000c0ba9179905000d11421326600c1e8203078940c0100404201095100b041c2c0000403003c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 193414073 1250 193412823 193412851
    0x1021203010623030c0408101406010f030e07030804080d08090a0305030402010c08031303030e031c020d0b04060b0c0c01112a090a0b030c0a060c1202010b0303070501060302091006080f 81
    0x180c0005049400444000180500c0083c0500c4104010b002000d20050103230001d100c02c00071000380501c6124002c0c00c40b8104400303518290380261094101b0000846d42c141038800c0d6640b0303800c04c984558418041c442c074612074425030202840c0315921407849040c4500280064003040d0f941102d0310350000c1d00c241c3c10005400c8448010400717500045028054003a22864021940c0c43c1c00380a03282c54020803156504203111021683c1441c64850001004080b0300503070300c0c02c0510001d0010060203000340d410a14003c0045140c2540700010035581d051a4101c462003100c0400449043c071003220a090140c01468980c21401901c071095040020760b000550b011a10b6000480d60092044171861001a150354001401c3d040c00d100150f0a401c1c299a01c00b04a41042806010203100d070700000c00513a180051041454800e40c0000700800008080e40d64508036410403901a1401d130206a1007041003401041e00b0040b40f01000040310b6460720380d1521966413101050303103e40010400c1e1003a42c0d072 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 193415323 1250 193414073 193414127
    0x140d0203012c06070503040519060e01060803071412040905060109030609030c02130203060a050d14030417280b0702070302030f011a030105010f051005040302130218010212030106 79
    0xb031020031003081c0031001c010042c601e541807142807528038054043c0080c001d0400074040400c0000c04c5481c040c01c40d00c0c801c203d0f2030003145000310050a50f175684114135440c6c0b40b80400d41c0c031008030042290134061907911038540000b1030301a49420400c3d0b581240c98104100c10005410a508010341c4900e05050199070542d407070726020161000702c20b0850002d442441044110f28040d038680c00c0c8601410011400c515103100814540741860144512549003001c5220420520407480421005081c017030f26101d071f03918031740303007040d01c10950741e08105015003c00c40300421480d02038000c000c80840c107499800f0700c0d15151055030001c05810700c011801103100200c0961810040c00c80c200349050300020340c1c0343c24000e012904950041c5004d00c40e074104401003150303900112000c401e40d0001c59119814407045c070000e0310103200c3c1d90301c000d4001da00200c800c80801600c0d130280454181c030b150000d0b1041c07040001282c86440c0b0f0b00c2030208440050005000003031040407802403030002980700e143c280c18 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 193416573 1250 193415323 193415351
    0x60f050903100507081003021c0813080604031403190209121e0d03050103020d020402031f080c040501051014130e0f090d09030309060e040612050a1704140d020301 72
    0x2e4101089040c40391101d09000c1d00507800002190301c0603002c46840001d90650780001e010208006c41a039800510080010500c1070b800111038041c0540160007258a9072200c51507280d00c411201030340851100481560801001000c480c0300e01010340e00c3d810300c0c50341d0025100094124095042c1c000007100002000e5110410240742142545842d01c4a220b2004e100e90b842e20045107500c2c07003050305050040005850707030010190907960440e40940c4940e1a83c80c081000d203a10a160304440f000800c00040d40701c40490711844c80341d0252410b01031680c8550070b110245480d10784030000991517903140b40c041074408015061014009513212007041d5980300000101005940d68021220510300340120204100800781088005003008103d075031458a01801d5001d6912840d0305004032800243c040b40d40b294000009041c3d801c00144e880780701410b005540e00d5014a086804010904842c10801802c40903030b801c860a050340c94443c03649441c144800c0034180a0202e8041d9214054400611 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 193417823 1250 193416573 193416583
    0x1f09020c0a0605010b090616260301050102150108032a010f1d01060803031303210507030b1e12030f0301030f0c0603020a05090d02030f0f010e1c0207060f050903 71
    0x1654010050602007080d080c0b40040f510b042e440b510010384100003102150300c501c001c0e6020302110000c22201e080d6941401000c0030740e81d100e80f507004440b2560519419250070091416540203900f29020b600816141c1c50b80d4104c2809500c0640e40141701380780ca15243d11902d41741c01c101500d407600c51009041c0210f401d480304980002d40c0c4949800c85220224400f01000e0b00404004000344080c61802090603200e11002d440b1595080c1d42c054840181802040c031001d07544621501002090396a03290740c80101b4080e0b49d5403000038240030215003540b91851106842001100e17242c00820a04810809000504500a00365000a022aa1401c0300c1500918021030003007043c6c802c01c846a00d41078400344041d8124200345031041c880702000030303444000e440041205440005840c3c20701d0000034a00300d120503089103c0d11414441401682064119441a6131000101c8022003004040505241640c98008006078055901080b00340d2050300c0c00350440c02d20b030600500d084400d101003400c06e = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 193419073 1250 193417823 193417837
    0x709120c08070807091515121418010515090112060609061d0906070909020304030e040f0b010f0507441306050705150c0906040e15060a081f0902 64
    0x30344c1200c00c0801102019009035214000c0c0006109202400c02c0d00034280305802101c004200042001c05032088050fa03846540120b0324021030103a2890890050028805c502488881075400c0c1400310f030404030318000e06440300b140244107a0310f43e82440d10606248202d000183c400c981c403042c0000d0481110300c50900601001c045200e03480c9100b07011403d40580183c01800b1680c0540d0820000c0d44d442858541034440c1100c026070340341ca8500f01103034240d50900016a000d13140a80714070300518160b000b144803110a0721000c034000401101038405008605d0042c00100c030b41501904428003803001c5846a14250b40907140d00c52001510014499040e10410800000081c1d000c4003000308540360350040030b50b0700e860b0341380c6243c5555403a19018849113480d610f05640340032540c004001030a660407500b02800b11529a9556000d1000301641610707020b0400074a04420112414050121a840348080c0c903180c00e00c1e183d94100d40d040151610348000d0101d1419001310b0680746a000070041 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 193420323 1250 193419073 193419089
    0xb03031603030221180f06090c060f0f160606050a0b03060d05011803020102070b01051203070f0330050c070203030421020d030807120b0d0305030c0d020c240709120c0807 75
    0x1705420240a007882d09800004c5030300316030310580c1080a04600014540d504841c2a540903445400318110340c240c3c1d000701002504501000700752500b160051180a0301034a00900c024404a5921401d1000c21000c40c0102e80046504000007000da00304041c085401500c00c40c0002000c0c011416610050360855208500503500062900705200c2c19528240c0542802c1741e02802201030503040b2581d904c101e0724024040701c4446441824140240c540d85200d51200c085415035090440c22600e09102080b54501514640350101b44600744e60380c1602c00c001d07400b41c0194500340c240070318904581c40c0c130b0b0840240350724081e80365401600c0c0d10301c0d00c403040c9200f603c03103c245040400b409814000c7c440c0d00d60401918000641c4090341e40d03000c0e40500a030701400c00b682d0f2515420710741c014520880c00c1c059003080c0001901c0380c980100240c4404100300c00c00e44503040c003901c9104200c641c142034a100c000100d403003200340000d441500b22044031603c0b0300c00d480e004c01c0d621041c060421b80355901c5001 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 193421573 1250 193420323 193420351
    0xd030c020a1a13090510030f03140f0a03060801020906090904050708100e0d18090e010902060406020706080a0203060a0e15030601080f0c0102060405071703120c04090b03031603030221 81
    0x25503c810b452950340500501d003018011481d240b01c565150000f02e04c0013401b0240c0c84003024092600640200749402c0c40e480d840755445064009510941d40451004400a032034041c0000304030780306200360b0f03c140d4030003850149001204001c2021140020b0016901402445000030f1304c0002046203009100e005a8042244000312660b103040035403810740002440441d0000080307210040c48074100350380d0301d101e0010340012035030092401008032544c001d401420014000c81d2080d00010b980c0222411951005020390b01c5240c42e000741c0c041980c00d42c0d0803050104081c00030141d020005a8007191550280d850366045000082c904007081e0704c4229903402a1550200d092828084444d118030203000a10b007906040c0e4072151384031445e04c40d01c1007888504038107115050091044072141c1c058105540e0755818030480143c4141c1c890711400380c0c400d103441c3c2000c0d560f0402000362a40d241c0f60b0151070f101c11106807420f40c0603502020140f424580602c02c82103440c0040c010381c2d8010504465560 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 193422823 1250 193421573 193421587
    0x9120f101a09151201090b0f0a05130f02090705090d1103010c0e18060a05100f030501050f011e050405030d02010f0e010605370618060e0d030c020a1a 66
    0x201240c5a0184803500819000c010400c0071080500038040c3c2038020b6401d40442142c400442d07004000d00e4600800c0315801c2e10034000c0e8480080300d082e0144106400400080d100c10200380c0740b07a6243d0300000d290729880990200545880811290b000c0005d06049141c8480b00000629956030090f084854a00c464682d800720700382407059070408440e42c1005444510050001440a4020600c0c100380e440390b000020610786808001700c00510019000200e07501d0111405080d8000030945040020301d0100000380380e2a004040300807948060b143c260420104000071001e48200a04500a2010800000034681c408000c44400459182e0000480d0075000c1060015a9545a80303070041e41e04109061295030b9600700c0c6032405e521800811100500e590200304482c0c2d0807160a454950022900051100d4000349600c09c88410f455000600540f0781303d041d03501d401a1820640c0100e496005440000d00810304000072a0000340390040d0a5918040c1100d40403201d00e01d070750f4401d40480c403a = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 193424073 1250 193422823 193422851
    0x10111b030a1719120501060207061d0301020d0c0503041a0106080c0901030b0a06021f1b050a02010b0307060306030b0f01030309260d021509030703050703050d14010b0301080708070b09120f10 84
    0x11707070b024110b5803020701a16031904400402140703030014041e21035003807202c41d20b200e0341d03007507044800c00da112140a01540e0003c0d400508240c1084a064a0708070200c2c981e083c91070780a041c0076068030179546034415070380c0380d9610160964004a198038189660303080c401e03620740d0f0786000d500c00a00c06a4000e091340c808400e1000094052642082d51346420305d8541441e44101c07048400c0380c00d155241940d00c4114404040380074100d1007146680500a03810040754203507058020324240c03070290380001c109844001c1d404081c03140c2403201a0004114550602104580c01c080c0e40303107401030540017415039003030320746041c2880407600c440005603001d03890800000c822100f503150f02840920103581003085949014100340300301d110003000c0000c0081d20240700b0a46903c900b07181000044c904c00f05686440600215610038020040c0d0f51040d010001804400050400c054454541c8181e0801c0d0403a020f005e04005040345400140c080d180c004a855282007041507a034014880c4003144001c000040 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 193425323 1250 193424073 193424081
    0xc0d080a0f0c020303121003150f060b1201051002120c07061b12120f050406060305060c07020a051302070b0c090a0b040b071b0510111b030a171912 65
    0x40c10082c400d10a8961026940110075500d000c10344030801c0201e03643d0b0b01407a0001b031200b504010101842d421200489440300e5128086146207500c00704429501c0c1c00c821007580c040e09500c00c20b0003200e00f00602c058100001d15402c00781e00b034012a200000c0504407422140c10134609241c0350340c4442402c208040c4d010740c0034083c160a01012a002114503285d02e0f10f41850f184900d002d01c003012902031030900c1c0a503c02d00f01440c0c1e0711020820b906091038800050b091a1000f540d0764420880494900c098a00032180640e03070090035508000d1824041c0410343c2e05241c030002d00660f0a00022010805080d929881125a400000d6541183c05c0c104605484240c200c044400c109200c1401100026001c681c0c0641c0c108442c103103510101d58a41300c0825183d080aa0840c1004511500c0c4030b8004245011945102c400c0d100b4454001e1035010000740a84001d9915030b100807518004a0154030001d580103c1081d12a4648900c802070304542c0c2e94000d49008c0003d6105c81d18191017441c40c82 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 193426573 1250 193425323 193425347
    0x1050a03050303010e070207091d15011206230709080607080c0d090f02030f0d080a0507050306012703080c100519110405030a03030b100f02030a050c0c0d080a 70
    0x1821000141580c031059540e0105000301c40c0844010f50200b600f0a00030400100140300405092002c11040d504419405803050842004e6200703908425070f000852400050581d0b01c4a807018482042648440010b0000c601c14400c032201c40c4007801d2185e94130300440d9885242c0d07540300c402c14285000207080c58000c000f0507030b004000740d11382440081e107904001c07103420208032100403541ca041c0703007805294510f400e60b0095243c41003122051401502044400140725552520039196a413000c002c000c2e68802c5030201c0010340200002362056000e0791a01409007151814060034000f100350140540760140c000307880c845400300b84a083c142c4100000c080f00e500d1148140040e0030902035a40b1015400744403843c015441e13007003a1981801890030344006240040c03c03554840d840f0b090107001003c0b40021a40a070b02c8a52074168481d000e043c040711203014941c000c5141c040780700e204503090f1700f01d21f00740701441c007880010170003503130750100300408090164880c16601c8400080140c802040c01c0 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 193427823 1250 193426573 193426579
    0x80d08010801150e04050f100501170102040b0d021b06040b0a0c020c0d0305030612100c0207050a030305040e0a090602190e042a021c0507051b061803330105 69
    0x41c1040f20044584502c0000326411603000100070b03280c0b8038005007031601c0c001c4507072a98450002c1c807187c035080d2038202c2d034100c4012042c194010207041c08510b00740c0c400c0b406800c00e421410032050516510303603402094004114003110802500703041119041c0b0f0f005403003d44151f03180324144611600c0c5d034410141480e03030b0340c00240649000c902c0420f0060f442900d01400f840404030000300b064032500c0794141e224072a5000c1c0c1e100e0709084542c0070002d06016846030018420510041612305142d0303122800c1d02d4043d1a070b94101850710b0300305e02d41c40707800170f000380174150f21030505100203003031030000e0010034044808102c1c1940100c00014030344d802c0080307000d1050b400e0429607e40c510a41c040000b1400341510752002080c40d40c58141d103006140d010860440c540c2c845205407940d40f040140c17081d0761290302903851041c10080d00c0103803a403a80103201d611030004c100b034404c144012540b148001501400fa600106804c0340750315800003000c1340101c07070f1801d4a039640c1c50880d410345200340075083c00c0f = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 193429073 1250 193427823 193427831
    0xa03080a0b06071e110337170723010c081005100c1b06020304030309141309060b090c04030b0c0313080a020c101d0103050c0a0e010306050901080d08010801 69
    0x161200c1143c40100041c407401802410340880a1117001959000d10140c00340803a08030385000309610a1b15540840383c0f210001845801070418040002c2138500a90006094213900350165008401c41d0f0081c281182d0040d194083c046000d1003141d502c007000302140d40000342c90303400103002038065900101407a000503441c002c1800580d4a0b00c203405242411460034000c6081c40c0c3c942420035090600c0c08042c0d0400d00f00c000180558000010015a0b100740c0e01d050035559038022501d12031001004a543c008010054201c07000200c0c1c1c4160340315402404003154003030101c404035280b40000c1d01d1550042400040030f206020340c04003580d400182003101d1030328500c0c190622004e01c0c0e010000051030500000f4144010310720800640030705900007410b503480044a040003814605c100c2200c007007800c0c1c802000380741e158000d22600e8482d417980380f0240c0c500400420101d031039403080e41c0c007030f814160341c1c81c00455aa15489034084c0684640c000500541003803090240041105a01c803540c20303810 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 193430323 1250 193429073 193429087
    0x5010e0a0c1d15031302010f03020408062d090714031504020d0c0f06080a0b0d03020c010311040909110a0e0103080f0703090b07060f05060604030506190e0a03080a0b06 74
    0x300c60010750004440402d20a540090700e030009802c0c641e624580c0181c18404014000600800401507460b14401d0320740c540b0001010405a09070b0096103d800500c1e0803610000380d1813400020920710002c500000d80c001035140b8011a00f41c2c0c1d1003512080c40c158401c3c00309114000c903e507110461120120014001186800d0382d00402103c0103200a0088020101400030400c0c4641114040d1007104444c201d0180c480100a181450446d01384408605100300c0c200b0301e06050038031940300c5425901600c6a40c070f926005402a003034a0381354091124082000180d44260741c4201c1415903c20313138152000b5000ca908000007420f05410012100b840680104002820901140c0503500d4801c1a00d86400d2030741400e950040d590361044030b168a0000c0c40c6010808982d000700104104801c0c108840c2d11800c1c24805513002c0c0d400010400e501080c0401c03107820401c0040401e8074012280402d580c2c4c01c448429092402255044010071414070906c2400c2001b8000c145c0310540a40344d440c14065 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 193431573 1250 193430323 193430327
    0x2130f061404090209010e030318010e04051905091006171b01020a030c020105040b0703050d06060206090c120a120203040e15010906080910020f070303051305150705090a0905010e0a0c 81
    0x450b81c45403200082e80083c1141050b4010b82d2044103a080040540791112000701c0300d850810701085e0074078001180b030406d06e440f525091003014021940101d4a01d00c200c00840408018075006d402d004552003404034404d011720041c06440044d00b61403c50380c0134003411000d454640203100c47d95032440059159401e00c03c0e6030000c0d8500d910754061415954031012070006881078442d54200c07240030040010b80781c0a0582180c003c160300a1081e50401c14640d4941080f6201c08060700d00d003040c0e80003403000b856945003180444414591807410749410005a940da90b409440e41c200000140c9c0020038100500ea143d0046136501804034010007a0620b02440028010341441c000d0300300340b00545000c0b50510748104000d40303d51651030030865581c2c0229803039490366003008204400290500001070309800d50044d404000d550311500800c9a44403a0002c2204c0c020001c1840e003c000007071016507165070f41c0007400401402102c4002403e0b5040c12002844440c00503c82c52025051018000c0e00b65 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 193432823 1250 193431573 193431577
    0xb01110a030c081b010203070c1406010303120911030102160201090e06010e060a0e0a0b1b0114010306020c1f0c033207140c0f06130807080d0b030102130f0614 70
    0x39442281c07542e4072824960402c4107040006696401e961001c1f04000181c0d400064480c4010300500711990042992041595a1a0709000040016806113034404c00754005410880480e03101d03d4880c0c0800381d40501081c00c90700014425040059122207482c00d558000713000c0000341c44808164411403521000291800001c40074050040c4000241d01d1003851085c1032480505d24000c10b6a000b00c0d42d10344000302243c2001591200c01c4020703c5104a900c2c90500c5052001c0f02d280b0f4244606a07e151540f400940000c42c0c010010300583c814040c03074514108040e00150080c1d040024005508000141203442c1c0c010801280705601c1c0e107010507214601c040c40d5510b4014804074400780d8400d00126a40080246003603c605c801290801d9071410226280070b400c00c80c40d044a140c2d64400fa0306080b032460303000300906401c80070007070a40807916a0000b050f859480000100e01c0320044004070b0b089070b001003a0382e0418010304030280302c800d0b10f21030b4440c01083c1e28940301400f100324200c130311164 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 193434073 1250 193432823 193432847
    0xb0f0c0f07020a09050403080402040f02090d060902031204030b01030b060409080715110c010203160f050706020a020705090901090605011509060c0c05030d02060a0525050a0915030b01110a03 84
    0x20354000c620381c8215522145a0b03400b0780009003050186041174540a09800f20666049101c3c504082445400203603520035503901c0040100041a00c10b00e9456003001040c3c3c411042c1e1300760140c0d8008200d44444c1c10700a00080d441000740b20443c0d89541040e01d0150f601a00191103613042000e50004078400000b941d44458110102000d0f42c8500ca0205006101030384801000e081c0100d00703040390302e8040d8013540c0f1440910350680f80000c071a003011201e0032401e8404001141050082c400072a9080c0d0103040b50310fa4074012140704c26160306c00540300032004c54422a45a4445400f00108003c5001c0d031030060059200c150360800303945501610118184c001c4c44100300c014600001030098010904001f080040c09640d490038035101e000391901001c8038890702d1241004040380185c01c802006060403c5c800035541c014414002c404c03681ca40c05440c00700c04000f1038803004945204031030164100e0b580d01e0344000444494040002d041d102d0003240c2c0c0c40c8c1542100c0f2412003c25048252007442e = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 193435323 1250 193434073 193434097
    0x16061103070807030e120105070314151507050712060603110312091e090705030601020d090f03060509011d03130e19020a050d09060c080105041a01050307030b0315040b0f0c 76
    0xb11759140000c00c20211800c070303c0c3d001035800e21090100180e0540d1102d91005000800160386135100c3e450000444c0d800c0c06569002081415034180041036640038002c114424401e88035440c0e641d0b02203030790603405208181c41031070b960b036802c104104001808234080c52041c0c0181c02d0071403503c000101c15004980a031401216500c40040e14038000300980c09101c40018070058050030103400c000d00b550000c0312030a0151181d05002e00b00e5070b001d0404c1908495028040003e034078159690040902000341c40341006641340c810428040b00d901c1807101542018030300031606c4041d0400076040080c125071110000440841c00c0c004161081c038424031034150190409a0340b080000d108884500c98003480d160702d2881d00c80308100f000705540040c4060842d5580e208101c0c2d888404010464a415040070784102c80000d10317450a5018102945c0d01020b2410002401c0050381e000c2410800031401c440703411031001040008100034072054503041078866001031781c42d290401a284c1c40c0e21400e514010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 193436573 1250 193435323 193435337
    0x20f06011404090203010501140418150c0915030f0b0a03020a051203070803010b0c0106060809100507091205030d050a09030207030305090d02130f0b090601020c120109051606110307080703 83
    0x224544941d00503088080d0b02400070001580d4914128070f00700c003272800703c500c55410701240f240441d00c083c00d15020150045016104000035090090052442c00700c8603050042c1c2c000001060240c3d03000544100849840c082203c04000000404540c00000028410495040c060000d6110b01d000348055980584120b40c03014070071b550003440c1d80034485004040c1040000041400116100a0040441304000038000b40e40c646105039000001100c0424081c0c5c0501d400714003083d4190400e80e0410361a08003500503035100d0941040c1c0c4459444140d0b4180e0000902d401396070002d10460b540700218030170411600b10980ea0007512410345120103230400501003241c0701650b540b03440303a40c030041d801001f21090981500b00341c005040031079005003a9601c2c08615131958185504024401c0320141e0191904550754002c11442c0390ba028081d440d550f60301c0c03821f100003803000c00c030303044008a4016076240701625088005200d80000300114000307400901440c800194040261004940d042c10650 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 193437823 1250 193436573 193436609
    0x3010e061026010e16050607030c1101091505040302150304020306010611030906040e06041d030f0a0c0f03111011040509181005100b04030f0209060607051b10020f0601 74
    0x4402a000c2e042e01984039407901c0340d07800c2d00100001d42c000c40b510300d40e2582c6409568841c01c00001d030280030b20103804244540500000150404c51149600b60141052924580c540140d4810b0b00916210a03000c1640003c0910540c504004119800c09413890b40503e1403415034003103070b21003406100c1c1e20b00f4401701043d059a401018020361b824800d0107442d040e1111b982c1c071a01d02001d00e06840c411700961414801c1286080c1c080003074000a80c85c500207600e45108180f0034802580049010303800c12401c02300140c001480c10a0031200203001e0743e00c4494221020010b50304003010014218042440c10071442c0ca20582d001c29070782140c1e01100d0515850741e0b805501c61030040d4038820860b00b805030981e01000360009134806030090780c1017100c0d04001c5072a1b0700e56000740d110342d00002d482c1110b10345c0003400501e040c0038070680c03004001e405141003103099600c1526020000000c80c004400081d40e006090070100399800140b00144020032070601020007040e111a01030243c00320110540300301e2 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 193439073 1250 193437823 193437869
    0x150307081b030a0f030201060f0503030313121b0c0905280b0a0305060702060108010506040209030307080724020a0e0603130b0603030c0d0c120c12030b0d060203070e03010e0610 78
    0x180c49040d0082041004c1121501e8000d000308000e009040301812001000f00d090b04000080d6440b51501c0268110f0722801500c0e000c400ac90500e8201007008a001030264070100c0e0451200c4020340f20306200306009060804901c191400203280c041900164001e51000e44500142e1149a2144200c0042c92202d4903000c2220000c103600042e0141c030508050251040c1d0002d2428100c1341194020042c507100d8800b080180d00c6035800b1654590f00500c49040450810f000070246070303104071200f81c0c5480c2032198400e030581e060340410000e01d6000c0b13000d03003456070407010391444101f00710750702072a61400d01108104007451a0303020b014900120002880d640b0b00304111100340104804459114030a00e400401103820301c2c0c0100d89a4003c0c6140e2112140115141c0b01c10396480807071024206041d2404078001c080901205510014046601011665a10040d03015596030364038812403000c020207050966080780c2466899501200400c0b8648692031841029215012034981c1c80007860100d03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 193440323 1250 193439073 193439083
    0x303021506090c070602031b0a05090102010608071a030a2a020d0c150911040e0f2b1211122202030d0e0102010230070503060f060702012303150307081b03 68
    0x4114400d14006000302703400d0b8000e0050417058400343d000b0b020160715000403984642140c030030724070144000702c00701ea1030380101005180d0200030841c0010301420351910b0701e0039641265005462a21401550f980d00d168148401003400c013460402010b0000c9981d45c5101c032001645100100d00d540b001c00000b0891a02481170802c80c0052080c405540001515600c0e00cc03242000303211403190540d9220325924011000c2c064034650200c0407030b0011024401d403607110a0102c1c040034503070307034014084c009a009405807200b25801c0e50314240030b10b4040b0b01e107484049003104540e007022590106000694001924903083c401c0f92805c41361082100c070040c0d019000d40f91441842e0002000d0008609000315600304112210312240003507030b00d40383c0081d01d240c80143e9040e60844c0600e8502000383c1031603802854000d10601d082c100540841c100c160042c0d18540409040103030010074808922642803072904c0d0024124064041d070713407801040c180e84011407103094100c0c005c1d07034039622043e95003444 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 193441573 1250 193440323 193440361
    0xf01030b040b091f121104110f0f0a0e03032706040801050109050604050c1602060906041520010c09031511030c0a1206032f0303040303021506090c07060203 69
    0x44640307410305065603458455070b40b010b0f0030040c213241800005100081c09491035031680e0005250203449003403900b4040600b0140700c0b9440c44039820032051500300b80083c010f084982c06204100e44130140712000800742c100b242c040b40e20940c024000d01981d075080b540d0b04248152aa1050001110b14001043d85030246500442c0e00794a000000076101e02160030840c40398600701c408104654a010200d5114011481d00d4060b4800842c1b1180c010f040030801040b20300c20041030541840d81e1111501015a4002034040001d10208140b544580303d020300f8441c4800c1e01402400340004000006145a06a04c0003901e405005503146007403010b268040306890800704d01d081d40e40c0c0342ca82100f0519520160084001654950314034070740d040d2034492007040d41d5100092403101940c40c188000306403003241d00c140d1022090143d00c841c5503030400060006511039005003100807815805094110401840c86010740084403c00501c9501e59080f148025408100181c40b80c03100e5503450000e0650302 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 193442823 1250 193441573 193441579
    0x617031902010e0d081f0312081909110102161d10080a1b090b09040f03022b0206090114010308070804031b080610081209040b091006110c0f01030b040b 67
    0x11000313091490b80070314a03e01c1815408007100300103100801100265106101c040c0c0008401c81c0c001000328828071006401004940311015906000141101219141c3e0390460f0038540c103071b0045070196018420510b49041100344520118941000c0c80c602e6014a40100c210181c1c13600020170840074441c00b03402609203407088034114502072a00d111003c1103140f8038488040341c208001035040701c1c0e008442c0d0324003000c0c003038508a403500d0b0b80e4000c801c1c000d400300b181540904603031042c00240c000e646410140302da0710b0300100c181655038080d0505074042c01485959050099240428000b00645d504403a800f20002e03030303540c0750703410440c01307a0050b50001084a1071178000002050911085c81d0103a8a0a00586555465600401c1300c01781091040ea03815030086216031880709114005440d5048029101046611004000480d07040301102c5030502c01c1d550b0202800001c0d407009003c00a004444014010b03000d1600008254526003400380f8100341d210151411551034941084006080213 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 193444073 1250 193442823 193442833
    0x50d02190e0f0124120b130501050111030711060915030a050406060b0a02101802040501030501090302011404080f1804020c070e0c041409040c0e16030617031902010e 73
    0x314190780070726109031a010280ca8140002059005003295804403a04100081480b0070742103810540c0c80220403030080d041c503a50f540800c200340c2c441c40700f80c0c1000c01102c00001120343c10580054050401d0030890300d040e610070302c113410004a00c200003000d6100102c8a0320b071a14803080028554103902d0385218100803012007808140c40340c1e60003d50240d4410b11050000c503031202e002590b9402010340040069105060444007069a584815642021281c1488546641d80c01041c10b0302d400780d004840746d80d507400c2540141070307081c0f045550b00c90000392003043c0c50900707131505a994041c07025040014640015022041441841e0451550501600564441c040d52029680703a15091103171000c103049900004284c81c070503400b124103444014030f00c07440c0c4225142c1803081c01b12004004503020311450b1030200d80300703000001d02c0d8440c800303200801d614258400300c010300ba15400c2e44090444142d40a10136503081c000300a8606016840c00340e19540c0c80c0d2144103d000d4159030310882400c0c050 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 193445323 1250 193444073 193444079
    0xf0f03140f100614101209050f0a05030d061217030a0209040c0c052b180503060112060b060a0807030e12030108070608090304120206030a0204030b0a021207020115050d0219 76
    0x1242c0042c03044079400944d1102d42400c2d4824000c000501007012800140c551009000c1c042540e409220224041d104a4600056035030b100380c075081d90b80b042a03c0980c000304143c40e4503c03250140501401400420700c20640390b84c1e80382400412011080c080340140400000c2100b801035042d41da820b07100600a00c9248110100074010742c00324001a581ca0040020b00c2c4044043e0203032610466103071a400130720313030300440740112030244143d0f15040b03010400fa8000501981c0401055010304680c41c00c65101e9505450301c90100d564001c402d500500e0140038001d403007034004e058140c4c004180d0501107418410911194208a5040e8042c4440600840003144042d00002c810080c0c0b03019450340605d586803a20f40035500e008620404010240c0c50b144080103040c550701864000c48600c0000d410f05440341c1d564225803400711110019aa0301003000741400b90002900c942108050008021501d0301e0318402c940b11a607401040d000e01503040e0040d0071502c4015150070526403c80c0540043c5403 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 193446573 1250 193445323 193445353
    0xf22030f0f06180b07180501080c1309060801020a390203010e0607050c070e04150e1002030103110a0b12010b090f09040507330e150d050a060f0f03140f 67
    0x11780d040800107003208400c6455040382080300040d140c050316442c487c1d66400b495400158020030342e8000c200c425602c005031852030713402410f014007280f40000d622003085480017440014491300e009030360346d484010401992000300c20748040c82d0b0070007c40010003086001080c050603466807003040e203106144c200a9030b40e80c012701500d5005031250a981401c0e41d0b901560386400300503513001d000003480081302c080e600c0c0213512441304c081c240815101185010300907401260000d03071007584c581c14030300035a00d414608102000007501c40500c00d98240001400b205101ca4014002c0c0c4081e5580040c02c0c25080c1d44440034007031000e100507d56060351030b2610f092511180c441c0b1400060003011112580060940d0500008400c0780b46464098134520300c90071215104201c1c00c0e1070700a01c0c11280844626030034401000c5001e000800440d2130306101801c64129403140c0c0c4211100d80e0f1920003404020050101c0c0011241c100012110030f00c130b00030303107241844070060850400344180303c0003584800b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 193447823 1250 193446573 193446593
    0x8070306150c0b100602031204030c050d08010f061e030f02040b04060e100c0209150f060307050c070e060a030602090a05060720010302030610081504020f22030f0f0618 74
    0xb61095000c00800d0f110701d00f840c94059254090740002da001441000720280415040d107501034000d107004808900c42e5226207040007a10181c510014000c400140305910548600d030004105a2400035034203004100140d150441d04040c04080548030740c07491401560a80541c0c028140c003813044d5603140d1341c071000500b06104148169000c0c80d002c03400c0c00714060080d100c0c1e6260740e80180804485075120550002e20103c411202a071003815240ca603241a00c03010040d42c07003400ea03a01d40c80d40c0d0b0700f0100017091400882d40d00040c044038800c2d0400c07d140c0c803080000f0303088039400000582c03515011030009401c6207940e006260810030104810081c000d01010000104000e906080014145007004400340d110444115810001401c440c0340c140303109031021a8003400b14006a031a09a8100005041ea0300000c42450780000101740d0125404410400340580c0c5088082186c1d107502c3c41d0303141e215041400c10082d001d8075500c106801404815004280c8071a001c0041d489844640d2810074404 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 193449073 1250 193447823 193447847
    0x612010618020d140601051209070b0d0b120d020705010c06020c030f0a11010501030c03110f1009050f0102030408070b03091609090605150a050906030c0913111e010807030615 77
    0xd050280d00e007000c0f502130168178010a4103035949403815039001002c0d40d10600241000f09103100754140040ca007402c15014081d107005520011524211010400c00008841e5202120941144c0b5820525580000c2d80d40e0840d0004c0c2000e0120400c207051070b0009003d2084002441e0000091040c00484107900400c00d60b01d258695151a0b40032030b00e02030803180240002007140c80e122805001054600003480800040204800c1c50501d812002c95244410440038102240360f05500344941d107840704030b81a41110038402181040d10744038925030b480805200d802c0c124000080450a5104240a41b404100c00c0702c1c4115200c680d11a20a00103010300d00c0e0a4030480c0c50000401d514041e0f00350702e0041d0590042c24002030604003020420402c60180c100c2d5418800c1c1c0e4081c0d0754545680c0348042c0f00c0ca4a10f07054400708100303410403034a0302070408840c82c40369a078009070300c500009192041d40355207001e103031403030260f43e888034190000d280940080c1c03081390340510890742e03442d4010356040030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 193450323 1250 193449073 193449097
    0x91c05070204110c0d0516061d011401090b040c050304120207080f0d090e0105011d01050904091b050402090915010c08071103010e0706050715180c060f17061201061802 74
    0x205520344a0455150250740312104044030780703c0e2101f002c01c00e03941019030001e0703170310040011140c840800d4500311240d07014800e040c0100c00004102c024a103214074881c00c041603c003071140d40780c0103100501070b1100400c01444002040200a5540c3c800c00c0240094402c0900f11407010305051a006d43c1c0d070070341d140307100300007440207602148915140d084a8101c80040c0c40702c003065001222201400054900c500e4100b00d402e000700e01c03d5031350300e0040b46141c13030084110000c000d060303040c450090f090304e4005c075014500421019140341c4400e400c16500c80c5440c03404c0700315400c040004960001c911040900b54a4001c102c0350148012000e44410b40741048000b001151145151503071264413a00c20b44000c5030342845000701240e00c890114420180c100000548030a00d1100c50001054440c0c00380e40c5800034840502085403c0382404090303000b58200b400c034142440f82c01c45504103004261502902d817080d0300254103042501b052010b070040302000f000342d01c1d040c62400c1c000d41110a1080c2 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 193451573 1250 193450323 193450333
    0x60804120306030f021003110a030926071202070503010203040804080c0906101107030c0801060515030903030105121c0206060a0509010e0a0b061905070c0806091c05070204110c 78
    0x80454000d10542c03080300d502c1290f507908002ca6808101c0514440036001c0103154a4070044001c1e81021401450840720380d480c001401358581c140000c1d0302d030300758601c5203003c0f054045c41c08180c18280165400d00e42d200c0400c41c07002e048241c00700e003060052ba00443e00f6600100600c41000843c00140094030014030485d540ca42c00c03401040356503501619140d806c01e80480300c802c207992048156421054032002150500d5907a80c0c0c903440190320a038440b0031316956480042c0072501e0400c01c94030b01d4030b1f1000390031230940c100307007080a40300d100c180b04951084a0603ca094580360f01031014403005813801c0d542e400a99203040020b0344030042100c0c890300c103182c201c80210301da1420450301816100d50303100b01c0b180750782c031110a40300608031803640b5548100140619004c4d00350419505900b0f8003030b40c0d1510344031001072800c0c2c6103603c60394004a00a803c600100724902c14001200f039070740020343c0200c00c407421840e80251000e224a0b10041e4001e030401c0030309450074058a001b0044500403000300c038 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 193452823 1250 193451573 193451603
    0x1a041203020a08060f0312160303140c120618090604020a06050a022d1605031002161b090e03030105100c0b0c130e160f02010204140603041b060804 65
    0x203049120b0442000c01290201c400704601c4e0806021494100700c004d0211280c00004401c90622504031501004003910101c2241c1e0801d540750003005110034118040001c64103044401c1e039042c0c0580b000002184e00e0030400560b16940d030301d6424164007602c2c620384e043d038107216040946401e000c45003a4080c080800c0009407607442001161031241c2981e006d000611550b0511080905400c01c48150b10b90790102d4452403290148481c050070700345071095160712840c000a060502c0312050407041c141e44103001d181404100b51407002882c0341e125081c4102c01c2008084021400c80d0340c1c002c260058580046114026000070045050f1078044840e8003005500c844100c1c1c002c40d490038010807030404100400c1d20980c1034009001d180000d494410070054a071450b909004808456088009459564001586801c0124a01030340d41c10301c029440c16041c10001c0c0d04c252004006240103850010002d03051041c2d40c0c58070b03101d0488100940e611669241402404000c05035016a29070030070000368 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 193454073 1250 193452823 193452827
    0x3030e0309010512041a070807090f0501050304060c0201061e06090509280b060d090b0f010e06010f14070b0403110a050c10050712110d020304260304031a0412 70
    0x20754084801695001c0c50101c42544403401c21a010b081200c138600f8a803110113110350109180c40c890391803035660580900e40100c00a224110680c8441c40d5050164014402ea9a020048a174402e03000200810b0a07807403e40c04038014a126440b02200e18141d403103000000508512075000c5035903a90364001d06540b5601003014841c020347e81505469048100c140e041c4094a17464081d040030440c00040c940c03080d10116045502103240075007166601c3c54030800f008850546550014080c01e00382c3d18940c10251800003080001e46014140b1800b100c00703d2080340300305103c46590070f240c689a0b4503141c1501d89a410344005540860218400d8501d8846100c0000340c03e60015810500070b0401c090b410087c0401601c48850410070041c08000c40d1021900c403500401c0030441035994804255030072641c0302c2c10308050750900303011900208400c0203042c10901858070003046000904240c4d20700310b400e161030751140b40c1c070041048070b41c501d0300c0c8849441c1c07005c01c40c4194000c81516050306015041 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 193455323 1250 193454073 193454077
    0x6050114040b21070e190c0c02030705010819090809101b0206090a0909030c020f0406080601050f010c0b0f101202031905010e07090b1008010608040b0703060504090f03030e03 77
    0x41d40c22000c0f4951000a00300e6482c10020818620825503408a4a54600307181c0b1841c1192261460000b24031814210001407203031201e031030440e151801c42412654000b80c3c584c000e43c405c8a04200c1900042003c100d01102205480701d500a010410000c043c5400030300c84e000310032041d10415400b1f843d0581c0074002c5080c4072660103044890b8140e200142d0070420a0341003c820140c2000c06c1c0b810110300c0003424800c0c0c4401c140a5100c0c0c200700301851041080c80c4000282d41d50155040c694104500240052500e0540e241281c528081c0c0d114880121002c03c100c51000d0403013100001480201241d4400e130900540c44112501086503c4440340b00c06802c2c2944000c0d0154040c80c4840c00311022250407050a40c0714000102e01b2170134684520b031030310f81e0076001421040c0d0340b104242c000307245c0904010054101d90601c03996543c54000041c003c0e603402000a0b102540c2c884c0081c109030b209510550103850000c10402584a81e030800c400c06104100007240400d1030b1260181c0c4000300082 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 193456573 1250 193455323 193455341
    0x10f050108031908070e0d11041a0a2102090106081905160503060a0e09071d0708190902040908070302150c04050d0309090f050f0c07050d0f020c0a030605011404 71
    0x3820003c4507401150894a0060003080c080810007030720800c031620b90350562076980c0e0324003810b041c269406c0014100803c6901c170699644801071001095205a261003024408550700d068600b01c11302280d1807144011041000000d52000c0d028001051098011192a0003102a80c0300c00300844280019042111415651002c0d51085444c0d000d4081c0c0c496001954800c002405042c1074590310508100764002c00c1e1010607030780e0080f40c41802560461008c40350000034186103441c841c00c2a54000c0c14050b80035003100300c3c0d400c65100d8440030300c043c2c0d008081c40c1540070304100251441d03414010015040700000324010301680100707c0d040ca004003081ca0250f00c2a5503110b1a00e0301d804200201c0c104403060032814440410740c002000380e60b0380311303440040c4c0340c0f24000b180c0c030320700704c000140d0718980280b404200003014007050001c900c001541042c0c180860034040d0764501e40040907443d14400780c903650350154610101008000080c3c005604858250424904000b050f80402c01540d00341d071 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 193457823 1250 193456573 193456597
    0x70b030402090a09030e04060906091808090409030c050f0a060c020c180604060b160227010b0702120105071e020106060c060c030e12130605030103081602040f0e010f05010803 77
    0x3008100d83c0c0305240d006440302c601c030b0b007042c0c41e18002460114083d40c1e1960b01031314149640d84030400c0170310150300603044504484031140421010710303600e80015000d0340e80c00f01c0c01582c0d55000e00c030425000b419150b080c0754004088030070700c00c003d014030756448000300001c4850b01d00b00303500b03540d45a000140300b04220300001c0055445050300394101c10b00a00040c502075010380c503070000040c0d0003507080081c44056241201c0003000c1c082801484620b45004480c1201c41d02c1480148070411040c1c400141510440d003030481d40d600311400001c88101d05d03089450065403034182409100d9402089509504914280d18108040480021b07403ca034441d104140c00304143ea54010700056030b942c0300340d6210321079040008014205900d110314100e03c1c0a1044000c1400040341580c041b4a100502c00420f0b0628140e4519811750f920106d41d07008221a14032500c002440780710440d41d480e00016800c8203009410412b002030039114902030720f44c060b200e0940f28500340000c91800008002c032a1942410 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 193459073 1250 193457823 193457839
    0x1e0e0310020a14040e04020d0305090a170d080106080c0d0b150307030b0f06090625050f1506011d01030b04111305060304030c0f0614010e07080a200703021204030b09070b030402 78
    0x268090244290024008808002c41040144a150b5a505040c070237846c0c520b04100150100b00d01c618546040c141c9168188140080100300c415807250002341e11568405007a80c4071200981c0d82c00c094110780d400168443e5504c103d4420030200c40d40070f50f21408003540c06001040c03011090002d060100d0b80d1894004100300642c1229042c02c40042010103c040c481076400b800e101c006202184001000321242e41014030521546802008441c21280302006007205a080c83c030000381c000480070f0080000b4030206144406240e0207544070b21281e400190052004609900c07900c112507102d03401031185001d141b1000f01d070a0920401b96446298103403202c0610034100c0c0c072012891140b151003154860380707030502000c1c095041030804c1d00800d41c81b6420040c07400c044002602c2c0401c0203000f04109850a10b6000310112103c0401c0500c50316410740382d603151501d0a0072824070101e1001c01303001c440001800420800b030890880e2161120404ae540016110b5444a000d88010784010b03600881e2 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 193460323 1250 193459073 193459081
    0xf0b0609011407020a060e190f1202030102190206010503010e060f040206031f030b040c0504051b0f0c030f0d0e0a1115070b07030b01021c1e0e0310020a14040e 70
    0x1640146044020181d1850b0403c0702d00d600151100081d900028000740180080190500b80784000d5403c5000b03046081d8449070904038115542004e030700c11048004c0c036041502056403004c0d07040302c0c030284100a0701100f141002d01c02a43c0c480d400e02c69140250701e401000c4c0c03890f010208080303000300d0381d1034000d0601c3d468a03001c006181e00085d02d26152480d20581e07840f00ca003035811007040110321401900b50540341034106807071401c01c0c42d480079000781e04240400041c404600c10000c00300b403c17011155103070044240c03554900c0c0148202d0014a01c80003a0483c01e01c0f8442c00985880a400d0782c003440040d030100135403074680e180305500502c0708511491418007860244049000c41030081c9419052035600d84036035007005816943e00020941d551410003055a0601040c14000e0a80c8d04107403501d07800c3d800013000142c042c0724034802a0342d00045821090311400304001487d0000b41103c942949084d00e0b40002e500000c14400823075072648041594000700002c0d94112444e65501080c40c1d0340e = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 193461573 1250 193460323 193460327
    0x50717030402010e0603070c0309140904060f02160f060608030909070c050a020411030405010506010e0d030c050a0503030c190c08090609030703021504060201272d03080601030f0b060901 82
    0xc0604124180622041c0b110f00c15124031001d184200071554900c3c0c600c10302c03828060300c806519000401e036044266403000300764460080150b00036900010026007110503c1c0e2642c001d004020000b036000c0074054141c410321500b42040c005107409203500f008926941d2131629528865030140b250044500000201e10301c3c01041840340850092080e24440d40040d0300240031914000e08208003148040188000d1240920680d580402c00f0b0070840c020000c1880007131211007181100030108100100480c00b0418188100f4810b25809000c5940328188041d6021050708000d1f40b598240300070b01083c450191151090380241500544141c5c035006641040c0032460b40600b1108ae014440c0301c00010044c0c9a142100c1d900002e02c810302900d0f20700300380d002800c1d5000714004496040c0c40c01c4018171800c89000c4a00c1c80170381d01c00f01c0100b5400340d154850320840380c0c8080303035030f43c4c124460718210a040d0071500c1e41d849031100360707001c101078040e45484e0401c0f62000c44026422a4040c422450554 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 193462823 1250 193461573 193461577
    0x6020d1e0c0210140a0906030b04060b040504020f04080a140d090605090402030a181103010f0b15090a0305151e090703140703020d06020717041203030b040e060a051006050717 77
    0xd82e0900e041c0130413902c002c4043c21140d0108402000098a2003070812051b6403500c80c3c0d03090314104403024001c092421940020a004e207014123441541c3c005030088200b00c10004031401401520190382d00d401d40783c100566600038009809505000b6041503a061a106990500542e205038507500c0c20010003505000081d0401010314080035076860814848149a030f0804551912070510040c6100c0c501061600b5a80075120b4500490304040380b90041daa0391b510201041c81c21012500e848085050006e081c441040d4405021801900004042c114010414502c108003004103190f40a5174081d40c07416032002102c00003080e0304406010b00c00600170b0f00d00400504c0810084800d160b480e074000920140303101000711030351a40040c0c0082044900c2000c804c812440b44045070900b86031954142d07442d9075003100181056610452450b6540e201e50003112a8a0504201c031418a483c0b000a1b00428060310f98402d028145a000501c03140f140045030807265204c042024084c40d01da03041c102917 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 193464073 1250 193462823 193462849
    0x160f14120a020a111f150509090d030c0e0607020f0102070b0301061d0901060c0b0402150c0a050c0609030304090b0301060306060909050105091204030314120c12010803040608060108060d020a06020d1e0c02 90
    0x861b40c1d00045c0c01e55589030348038040d00410740038042c3c0381c0c1d00440141c2110a8070001d1014401c0c80c24841e407042e9154415500259015181014280400380040741040e80740e030480c00c20036270040000305238103520041d69420503400e002e000c1244030f5041c040061094091162400140b0300c1700e800c800060f2480106908a0f1015240d42e850f40300044954901d500404000150369110401c07000521a0402205071401400c1e02e0080c64254043e02080d168410f03400384c46003d5454440040b12610300350321650045070003910401500740c860010380c0291150b010203845a60800d4045100040040307424960410b80120052070240756aa00b6517a51003280341c1e12900d80e10500800ca002101c02c11074501c80c80108a031240d80303607183c11f440316102c0010f801c0344010f503105104c1400340a80040a041c0c01c030300b00b400c01e00c07107d44d40c020018504030225030000b5003083c0420400209140c0000e4001d484030305617103c007110140740c03017030b41030540404584520015007000b10a0016051241b142811 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 193465323 1250 193464073 193464101
    0x603051b130305100b0316060e0118090c0507020102061b160c0503030a08100e0108100216020a03081917060d08220509160f14120a020a111f 62
    0x1d0642c1c2c3d841d6181420700505182c1c500c15280e03050402d40d440d040c051900c0d100c40d506c00000000d0f08000004104a100b0403540e814000030442008e000660640c0000081411250a010b5182c60b148010890341080408138003510503080490198050051403502e90840101d0f41d5091059140d660360307500c07101003016128205141d0f8086010344040c0001e05800c0d042d07884407402400c003072030340642c0c0342c54603401800a50343c0140140015940416250142e0040c5000961036200071001a9419040c0101c001d50040c41018000200900500503000c28281d6100c00e52030598484000e4a65051211540d5410140d1000040e22031501880058000740102c2545050200c5050103a2a490720044070341040d8001a00c100300f0751a101425070307800300b0980710160f0901d544410180520313032588003031020300624001620362650000180e0380400011800b075445030a19032200c02c0298806242d2100140f00002c01150755000056000c02a001e040e11020102404003079071401000014402c0d01 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 193466573 1250 193465323 193465357
    0x250f0b34061104140a0e040b04030e06070c0602010509010c121a0901030b04021e0112110f07030905040e030405010207060302090a090207030305090c030c03150a020f040f030c0603051b 81
    0xc0414101c0c428400c600c915500e01d5903803181010145418000b50101c0d4a100b0904008140a4580315043c15a00700e544500c00c1c0d040d50b2140d18059a1031000461120f82104010420b0400d02c400342103d0b10448a542d00204848c2e02d801c01405e09030350f001c01024011070480301d030605624185500541c2003054603140710507c0d44100000030b00c801020381c010303203410a0000500c415807820050340c01d05072026600300f513007080000c40041c03c50300b00d410401290301d540d03030b4020701100d20040803030721080908240079544c0c03078042c81d0140c0400305502542d80680c1c030301f0a000300c0c0d078400001107500355981600100181c070328141080f006948610340076070708070034030710340000c1c9001160029107800c611a4034040350074035204018900c0c14521040f00383c031a03401b200c1c11028030344011500044030800e60311042410380c0c072200e81c07401912a0355001107143d040002c001803111074a507000300507207109000641701d040d41c960084042e518182c465000001424201079015024500100784600500082179 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 193467823 1250 193466573 193466677
    0x3071401150f080d020303010e0105130603060c020109170705151f03060b0102012d0b011e0c0b1308030708040311011b090e1504020c250f0b 62
    0x41d003003402030b840400803029220007800388180070310800f4200c80080c8000c41c1190f14021030010401c00610405000d511241c03401c000400881d00210040d6401c500240001c11502c8070090081c45000c1c411b0391300c031600f031180240d0b01c941042110380c141d400030000c1800c4190044003020790100941032194240b10502c1c02180b117048460348100031030084800054500740c850019080d070b80c3c1c5a80440380c8000718080d098840b40802007100c0561034021000488000c11070060780c803490502503551141400c0b40001030720035400320104404500c03481c034400c05070303d076480e00c040c100c604540c0040c0920010700000304500c0c8204091580940240341c0184248072110b2401d003154045650080140058a5030700e0b2110303006442c040003451206000c514a02e0f2414034001031000c1ea0300010f21a503000951000404030800045480c50b82c01c440015801c4407103c010400078400b071146200f107003500d503c0001d000c01d440c000d940c100300c64012005403d40d940881e202960181e85403491012510314018 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 193469073 1250 193467823 193467851
    0x50a020a1514010e040f06020c0a06060312020f0303040803070e0d021e1009030b0f0705090a090204050f040b10080403020708120405030709020306100e0a1d06010906030c0203071401 80
    0x54000d8840c000000035402d4a000c0c0041111505800c104007061695091000054100e100d405182e9004080143c460394440c1d0101e0400d4200140541a0303130400d007010090000b0811440900c40e0150200c691581d10456815284d00007113a000c2e04050051000603000e6008aa0224000d14018014650f251040d030024040c0064140ba80c00ca00714002070b03101407820503001002103c07156060514140780345654401380c0100c024103003545001c6a40c0031400da14090801d864420350002c2c90404e005450744d901400031341040c41007900c984550010501c140c1098031619000e04000b43c05006080d109200a40d840d03000504118210b10829100254a000c140100d045000e003150740e032075549217800101407503d00c0c69004058650b104006000030b0744e844142e1046060941d041800e607620030900015618101c3c0d85c0305510303080c00d040420710f400108400c01c5220b150300341c03503000c1840d842c0d1000b10119110301c0c1d50302000d45c4c0100140400705d00108c40c02c1942026010010031440e01081c1c1e0 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 193470323 1250 193469073 193469093
    0x504030912021c1a01050102062406090604030803190203040c0e190c0c02010908030f04060f02030d0f020d0e010e03030703150f0807080d02030903060406020a02010905012405120d050a020a 83
    0xf0546051201d180341c1400e09101041d140d005080900c020529402e14000d039988050507001c42001007080740e540707110252608401e81c4c502100080946883c0c0d0ba0b6030402e1800c40d40300303d56200104c0301e2144e00541a0003d882503038040ca4101420380348142c00c0c003044080f0000b018008001d0a080c0f001c01140400720340c01483c007802304e0307a650700030403c1c03441c40003408103992900304200c540c00c02c0c0314134419000f000d0103440c1100c90603c0c1c07110040007615001c0c0d0551052900c42c45036541000e04248100d5000c3e001070100401c10f090400000d01c6001c04642260511150044150000c1002c191560302c25001860005c80c0845a00107140c0d403003124a501d07a0069101010640007044108031415060000018108581c0040c515200303040c000030350ad4090051001780003607404518200214806d6001501690344070008001e00b030f02c4400402500c111200c9100c40c0c0204564000c51641007240c1d40c440c546038250010204452000d01c1a515034002488050840c440e404403e00030400403d0 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 193471573 1250 193470323 193470379
    0xf03250f060201050c07030e01050c0303071e02030705101a0603040b04060b0d050a0305030703091b0f0b040501120f090803070e01080609040201020a060507030e03070c0e0901050403091202 83
    0x10012051031400e00140420031035a400071003564540803c10040346000002c44519503410328200b0310a204890059901d40258040710300a803202004014415400409000002484009654091119040407a0380b44140d2030020480d03001145d010076400f0b500d4011303c8001070f9400092140e07031410340103e041a0012501a80c0440146061009101c01031280300e0340301400361022410300690f619050307501d20103100c00500b0004004001164244241d04c8100702d00d0b8040b4141d00c0a0301d40041c00d401741c0409020b0964420f00d02035000038110141001c450845d0b006031200f14504119694031401400060111050030380c1354100e03000000e401030001c40c42401203807111000321030040001449000010002401081c84109000242c0e800242500080c0d9000d400421940d40c1c40c00c2c11001703010032040c034030b40341d101c04140e040400c40180d000000743c41104404108617620300002c40e00b6203409980180115200407001c0c041c0c2c85c9d111990218903070020741101e07803580004c4005440104010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 193472823 1250 193471573 193471633
    0x30506010203040902130e0a05010503070b030a140a09020a050a140111010207020306010b031e10030b04050a0b160809061b0d02131410090506031801060b040308030906010602010207030e0f03 84
    0x1c0c0c0500c409034501e081c154000b003200030204027660504003c0b03a62001d02d0700400c0c00c41c040c048005450250b44d50415000241c02c82512204c80c28000303222009401d903880101e10490024030081030b5814014094000c980c0704140340c100c141100f900560b40e80320381c50b40980d00c0c2d54003000b0960158908002c164020103c4018465888c83c0a11090747c00c03541d52813400c0004e4002c0005d2258070b192040325401501c0d0005403088407034a5501d403003864401090310040c4001111410051a0344040e04103040c00c2e00d041d1280802661440000b980303888007102c80c40856044d016a10350b800c0078002c00f8200b5104001401880c0c00810307503203060440701940c0302d104559901e452107021402e0180e0040c0c080c00381c5042010300d240c00c4c4400117410b80002445440c01e042c1c2540e60520080d02500000c005100c0c00103459a40c58480c01c02003003a6204441e8400e80f84560b40000071158814400c4605050301a46c8c2c1100544961041104440200b0031095041c0315240c0701403404003c18507a4680720046c1c0b = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 193474073 1250 193472823 193472857
    0x10e0a03050303071806050f040911090904030e0f060310030f150e0a020f0405060d02041e020d02070318061b031101050a20040b120a02040e04060c08060a0501050a030506010203040902 81
    0xe507400d4017075a842604594200a400e005d08003400c0070b424240c50984425100c0030a1801d81020420340c24010300c4107060b40800382034180b00070715810031401407031540c00340c0d400805c2c0509201800100e02c4140d03000d107606038403904d0400120701442c0c1c1c4030f4000d500c2809410303101b004103164031080d54000a50240c1d507030080c980500852a0070800c940e00030000380d85c18000c2d440d00d0000654203994115002c1c0c001c98503000c1040f56440c1e000004103c0307803550b83d0119298000041020020b41190204601150100c140c0ba107515012004e10030890fa095074910801401e41c5044021404003031104034240b00c00f440108008420a0280c82d2082c05540b00014900031964500c3ca005040301200c00100c40c400c0009201c40101c103000c8030309202c00082e1184c580c0d01c40025010007407089900017440700308a001840700700709803034001001042c00da0351450025141e013410030941142034880c250125000308203001046020350800e0360310141c140181c904081e40c03011241c040ea0722503210300031000a0707 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 193475323 1250 193474073 193474097
    0xc0307080c0910060206060108070e03030f0409200d1113080d02120901020a060b03210403150203012117040f0e160504030b0405070f090b040f0911010e0a0305030307 73
    0x302c00d42081e40100c2070407424049628140c8040d4450401400c1c2c00d041140c1c0400051449018820050030480e003e400c80b0f0b901d034032101e0040008d1708940107441000e0704005101140344a2550703411000e0b9203a078001854907010103840d4009004182c80398166034024000414110044100d8000404401c0098190007180e580000d01740740e11228000c075070000a00030100c079a680014400300f07103036000e80b00260b0304d5034050001e46041d028040020f900c001040302c0c44900da03480ca01910490784141c914054030903401ea102d005a02090181061014014441451061489001e2861503019040821101c1c0311111501d050b54440d400c07080307810030202c0080081818a40100d40e210f0601c0c810101240c42a200080c0148114440908503d403028041000c1c81803c0c4113100080a41c142034034401540e910703001020340304040e51380b882186070510603401c06e120345c004d10716200d50040c10400004180300055903200070000340590829040f40000c00000c5040005500808440d2a41c0f014100 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 193476573 1250 193475323 193475329
    0x30c03020606040e2d0607200705010e090c070b04060506190302060a050c030409060602070e010e0f0c030a0906020d02070606060c0c261902041514120c0307080c 71
    0x40c0c0076010310b005602c0c040c3e00d00b500d001c020503585c80c03072440071280072640401d4a1118062000f100c0f078045035401140107000805401c03050282508100d1140298050380621400e91958000d10840e4040390028248140914041c02c1996004081c160707038508200302915010120304044a0444450b5611000c1c0000782c9045000140b56850041680700070b6815a4003044c00c501541c101801808804200d10348001e500f0310542c0c000d0209030504118050f80c84000a599a026215000301b5500d07030000440c0c0383c17040c401902d01c1740c61110300e004803a807209440c80821390700041c0120380042c0e441c00d250000a0302c1e800101032100c2c0ca6030001d622003010342071507003c944165010b03405009504002d40001001c0e00c1010b0100e070300441c8241240503c010010814080d80750300c03a04035001d075640409a1240322401450310307a0003610304001444d4201762540300d50b141405900f4000f05040c9902c5001d10700000742400c81004001070302c0e0340d0307451100800d103401c5464112210b6030b000380c504d102d0182 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 193477823 1250 193476573 193476583
    0x50a05032206051506070809060f2101060305010e2e090c051e040312030207050c0a15091a0906070203010f090807050c030102120105040b0a0f0f0e0a06080303071209060504030c0302 80
    0x411304560461410b42d4696a100c0c40d88644d0752924040e82000c11403521845491043d070ba000d15403070680704141140180c42640d001e10901602000c04d00e880000300e00c424480c0146403054941e804e107072065540e20ba00d800b0ba1403c01c1d010115401032054408141c0391214060222003e0b012b40b25107446904161038a03214000c00600304012000500041005c25286601d030303624040390f820016a15002c0d07060040c107207641504129007000d180000000c1c6132107940e401c00781721107031540e601070500e0316011714604060002d085540c00318420b0015a80c3e1340342c054002c0c440c2910042c00001e2160010b20300100741c40f06503000f61200140400d170141403090502510501200c200e000318a000f840c40d0700c103c583c601c18040d80c0d00841e40c91240f22119100c0000c400080c28409082310030617039a6004e515103071455030082c0e8404140600c003041d42d14007030340a454241d80442000d136081d40c0d141c240444810041a41e120120754842c0c51941c0410014401c00c0e01441c02a640c2c1d681584103414081d20300303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 193479073 1250 193477823 193477861
    0x80f070503060919050f01050708060f03070506340606030c09060608040f020303120c04060e030a0203030d0b01020717060105011b120311070206031e1006050a0503220605 75
    0x107a0446402c0210503480440c0c41d000c009164108904c002d880c5041c954544102010020015844d03d020b01814540241045204240465400070029889030030b1549405040c85215009542885200110f60005c0062024600111645001159903034803401d01c00801e50f80079a080796071803005000b405540c03003070030000d421b42030428005240350020041840d600100050808031a4101c40421980d040c4100c0c0c00c145240b505030503d50400010040d6158050322840c0f01059045180135607908002c81c0e801e400d0340c3c005001c0c600b8401c40070391b08400307030401420050450044980104202403240758080d400a4440d006103000d6040000140c07444c6280040140c02c61040c001100011300740714144121075100740307000719050303091443e03200e42c40c0142e0500031341c00340000c81040103041a609401c1c085540d00303500f1864645500381c07404c20030046801035100040041004501c1d46000e04021900448071020b41080c0d0f1401e2022031b0401d50b1458000c80d00c4a448038140405440c030700340c0c01100 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 193480323 1250 193479073 193479079
    0xf0e0a030c09110f030606130312030b10090302030a1e1401090b0f131b0b1c0f0e071712030103110907050412301101050a06030b040209060409060204080f0705 70
    0x904544e00100c200180001404107200e850000f070340c0d541c040c0144288100441e400100e6842614100b40068050441c0c048424000d81c010154880780300d2113100c010007202d4020300540301c08030b000e40705c80c1c4200c44200483d1002d40250300300000001c19240004546440c00c0c0000122492517140680740032401914402460030000140f02c250502e0748288880f0a900c88009124024510303d130320712424455115000d84240890800d26010501070320036010a0031150401c024450f004041084401c1c103081e0540a620428090041c0039041c0f0103808003403091012561901c0c424010344086500c03d03002202c0707404d00d80840e407903581405512103400404904100d41810308003a44040c410141c40c0001d00050354070485038042140900e0305030031006c500004d40310b84440002000e0702c51074001e0410220740d03103082e0000b03001c081b4920403c0262070303000140c400b4544464082048019003c1c1050798029502c2101d9000140b152000b80000c0409401420900c00d101104a050500310307402540 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 193481573 1250 193480323 193480327
    0x20607080705030c03150a1206110f04030b09010b060d06060e0a031205090118060f0f051c0f020904060e0603071e05010c1704030501021209010e06070f0e0a030c0911 73
    0x44420703045020360b0f6110300c1c00d100132610b03559401c0300c00b035280c11011260b5800c5816a1404a41c12924090440030b00d401a04140511189000340ca82d1a10074420000500c5c04148400d000003130410342d800d0f400c88041c00000c00d403003004100154407680100d545a904650b140c4041103602e4112850343c010740700865801c003a203841c5466100740f102d121840070741000380014003406680e000f80038031608806244000c51000342c13110009010111822403000210b00d01940c1800200c1c40744080312100400c840c1022880c0046da242100038001401c50710705015020700c041800b0303440b1480381600421010200040c241841c00605040c0551600314105c603042c10340e03102401c0340c09203001100708e52080c60010880c2030203041c182d01505c101e0b1017a00303190703000090020601c0415009080c1d441c0800380001100d0b200c00e00814220348481c2e0440150380c003c04001915035005901141200301e89040040400002d50009000c0c1c00c12600210b62456006005105619807441204207900b251800c0354 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 193482823 1250 193481573 193481581
    0x1052703090d02130908070f0c0b070c0509070302040e09060103020a060f2003070f151104050f0d030e06040e09010507181509031a06010e0405060d2604080d02060708 73
    0x2d0b4003801c402402a00460f00c4020403040e1032200e501c0f4000294200c40c00c03640b41c03a1603141c4951450f2000c0d0f000c0d1040022041c0114a0070398110803585410b500551903441c82d8502000d0101c405d0008100c48180b603401d110001d101414007407814441c00884c0c020704960360440c41007003505017094007c402001101141d0408507a08000e040c01c0141d00c0c0504504842000480c05155208410004001120300d0062200300a843c0b4010070303c40d54444410f016005d04403108984a00492194a1340540c4144c104101410481da80488541c06440c00840320703207094000c2000c070780c1300fa17101c1801c201d4000d0030010705640030301c1111f412044914190754050202c5101058441c95400354860000e450440390801c82d0181d46603400035030b84160182021602e590702001a28800c48011740402c0c105014110782d440c180c031880d40301d507138001c2240411840d81d0f00e51580e8080b06080c00c4240b204411069611a005540a4002028010002c100d021559040241001c0018010f1003d02a000b0240 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 193484073 1250 193482823 193482829
    0x307020112021812100c05040602010b09040b07050d092102070b07080406050a020a0c03030c12020d02070b0d0612050604021305010f0501050706020d0606050406021204050f0f120105270309 83
    0x1015040d104130748109580301c2c0e9203040703400c20091024001c40249000d00b0a16040d070480c0140044811a4000b000044032048c180b10412408940c000c05480c1d9101c000707182c10b40103c0203400035691a28000801a689544851200e010300300c02d070703000544078109000441e50402c000030250612200d4181000d203942d44000315400f890186105016000c5007a40c06c80d07108010b409580b40d001039595806a90740c4c100600460030010341916008102e564403140c860001500114914445d8020f00400f4607050b401c0300e094000042c0105207a40b1001c0c005031220344048090345040c040e1002e0035141c10a8410042d40c281141e000345140760510004200111111990703004448013030820f1545c071360035890500c00a00c103510010300401e00e070200c046182d591120103001581d080fa001c951082c0080500d80049002d584640741c0d100903056403080143c106120032140001025180d00d4045111204407400d445007114490040d00d451825203505040c6002600c1500148001031032509501c4008 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 193485323 1250 193484073 193484107
    0x100b030c01030e0a0b01030f030806181b0403020a03110108060102120306040c03060b0706060e071b14011b02030a0e060403110405281a100504030312020906070302030702011202 78
    0x5a41070580e50a44492000c0d8144040582d42e81e2000d05c0c40010360b102c1c136010a52051a00c0c2c02c2d00001d11a000181441c1400001c081e014880c909815030b10781d90300a10140d540c10501901040e0300700901c030000068885581c0c10018504c903188058001d11007100041442e44000c09050441d40b2020441c04000e011000300ea8000d40e05803030118600b40c10035030590203004507500150400c00c00140700c1040c400198000c00c26514000d010741e1700d54851810448901d024225500c1900c2403441000f000039100600d1603c10102c0400040f40074400740ba1807071500f502480302100541c01c0003a1a0083d1030f40032244441600d0219130450030310f0304548500d803600345a0030119014030b0356840800c0b0b50084505a45402c040b03001c1004030001c0094010801419226082000c07140f0700840303140300e5140801006c061103860355100c0f401d00740b07503407030407a0540c03078000701590304541c00c0040035440d459000041800c64000c2d001103981d203032944001024044110400403a561051049103850395124074 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 193486573 1250 193485323 193485343
    0x30403050c12071101180503190f0501020a0206090d020105071b15020415090909030c1704030c2d0506030601030c090506040e010810050903030a0c1b0501020309100b03 74
    0x1900315140d021000c80706290094210032002c81c081c1c003240307000420a00c29401c10780a1404c1c0e8410210314000c1c0d040368100d80712805690707450f4000c0c114515040072a00c42020340107020707040501041c0501d854460881c0c0c000b1a4000058228804000d100a01004a014080c0c13440c40200141c0c60049030091041000301c0d008401c240342c40c04480140b09101c90b01c44900c0030300c032108541d910380c0d50031030300d24064180c01103901059000800055840e000e12900d03040c00d80640350050700d60782e2a61440e11a078461181800401c60900001c4041510718204a0150080202c801d404110030100380d039480e40846042408a041c08805000c1501c0300b0060700d4100d1000c0c00e002ca50900311040540e00c040c5d5076000703917070021004980040c0c07401d100d00e1040c0c100c402c010301740d64803044202014415204100c9041b03190b58010030125621001c40d078441301380006d0601d40410511080f402100079071088620503103046c0c1d004801c4c484065818003200340405001c034400c03c21084d0503000b083e120038001e8 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 193487823 1250 193486573 193486577
    0x21090a08010522110d0201020a2015120609040201050c0105040b180d021b04090b150f060403050303010608250201090b090703020d080309010e07060c05010c05281e030b04051b030403 80
    0x2003d103821039000700005841c1e01e9004403c0e02240c409403072b03824411440f05020900c035240701103804103495903440440c0d07840d40c1c50b4941115296510418880c0c3c000014000702e0400c0b40c100708440b0002c000384142c1340580d208a40800c03140c105050a80c145c9020103500b034010384c010741d85030088140c0000380e17a00c403c1440d180038a095030550700080d0050003070480107030031070500108001d004c0b9201d4000310340c03c407802c541c9250b07282281c1060003002d011f94080244141e10401c0103002c10f81c020b10240d540000004903640d503e10303415940d041c030190400c03418001350b07440d20781803001c00c0100b035126075000c075590cc0205913640c503680004400040000010300710f0400000850842e183c290042d0a04101030412503080c203035030f440c009001c5828100240c6182d460700c02c1000c074251080c4125414241c1c00d04460b20310707581d56954000f4030030b41040c00500348843c1c3c220500c04402191400059003207503403030004121078440103102c240d5200418003924800040c0c09420104803d07030903650016018 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 193489073 1250 193487823 193487839
    0x20f0316050d0c020105060a080106290d0911090108010203060d03260921030708010302011d190302120703020d08070501060803030f07110f21090a0801052211 70
    0x9400280d60341c2c4141001c807004603080a90003001c01340c05402290060b8000e680020545665095850032a0fa09001c0d0240c122005601a03000319031140d00811a03070903081403a0315000c4c0320041c0108035000f110f8200c0c0c1c6081d1150f10481c403813030f007102441d004141c01d03402580741d86044000154080d101c2d8200606028407094401501078a2a201010000514913100c00a082c15060144c0d60321068030480510b018240d000100410100c0c2640d005814a1316a0b00150b400c5600540b030ba0403c84410300310754401d251002c1010380d1a0503088503c4251450650b040c50b007580184014080a1410360517607034130105040005032128516203039015000040552184c840e450081e025200b035a00444041c8004018800c200000790000e50180710b0316141c080c60b000d40c1c802c0d9161140002d184c0c0f44481e0300003020710781c000c0344413001e981c03103601550086616044000300080c2e40c0280981012682d44e5451042001c128220401c4114041480e2a40c010a41071541d4040c0e141d400000e40724000c0d903035 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 193490323 1250 193489073 193489111
    0xc0a201503162001060e07020114010512210d06050406030506010e040f0803070e0a0504050601020c01030213050d110a0b28120504050d1b0312020f0714010c080a020f03 74
    0x1080c07042d01c2c1070708280c041805000d161085103d010308020300850515806c1c00c004102d48600521680014a40c08001c0c008503a19020402c640e400150488482078044c06100f8104600500a805200320111a40c07540390880b400c40f101c100e51203500118040c1d49002030601c0841d4002034001d0468070700740030703625003035407280f915828845100394000d100322404410311003aa078010354086981101921b6540b0650358920400c815100305071021409a000387c1e100c0f0180d54429002401c411110b451103821040d070fa4404940c200d28440d105840324446001d150080b40b030120038000040003003500e428240040c007412981814240464207444a100d05070161085014451030708010200c58002c000e5440c5c64100301d625544000310309400101c42d810140ca00d0a100000320030303140e8042e030302c2200e0f080100c521070b002544001c000700c0c0074801c28004540090190100c0580403d0764100101e51044001c00c041d1050384003a0807010744500501000e0f05124040060f02c2e403240c03000e43c2e0500c0401c0c07 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 193491573 1250 193490323 193490327
    0x3090e060409140102181c020f032a040c02030a02071719030302030a11041206050a060e04030906030c09120b06180924060307050909030c0a20150316 66
    0x8150540280070800b0f161000740d0000065018004458075007111000911001003005140c0510216036407500071006030341409403e10f00951103003c0381c040d0484e000e0a18806400703241c403903803c1e000b07803103d40ba000a960150070315010703501100e581400114100a00d0b1440a03481341183c5c040d24141d80c007805800707926160108102036035103220341c1c01c01c4094481d50900501075401190b1030f061160074240840103140144080342c2c2210034480001383c4140703132565500c000d08406000707a48810f49030940404d031030440444081c041c40c4203440e401900c51406201600343d5941c03000020074051010710800040e00b040f0340aa0413258001d00681080c0c1d00c401c00226030303807076103a00910b81e60070082c100145a9000140d40d0840c0c4204800d04240d010b00262400e2410002c444503909604a85000c00141c201440340301c0e000300d044001d4a0510341121540d034136080100070306071440d0700300c490740d06144980307280041b00b904015913100071500e82c0590b0340d0500e0b11003d0140008120074519401000d4 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 193492823 1250 193491573 193491581
    0x403140a09090204090617060c03130f06021b0d0201090b01030b19052e1a0c0a0b070903030e010806090414120f040608010f24030f09060606021903090e0604 69
    0x70a250b002c44d1075070303140d00840000b00040e000e2032607000c02c082c01c1081403035400108117100781c4106c2001e0340b841c1d80d450411840e8103c0708008445285520011170002040ca0020b0480312903440725031014014100c00c170500e440f440e04410429640741c001c10300080b896806d0901e05581e049070000f4003d0b200c48503041c8944070310000c0c20540178034000c1404006020f0428106550f00c500020300041c0c0c000c2911041901e5452280651180c503004040801d07128210107480d0b11591441520030701360b11510340e41c2155804452410010f88201810300c2019004100e200900000b8070b03203a41c1914065002c5940c2038000351000d031031070741c2580c10210b107444100100101e20740c8000c2e08541300c040c00022008241c00c640500b2010032825000880c07600d0350441c2c0d1070300701c4490380c00b00d8120b040a000b41038504600c3c44900b40816849440403142c001d00ca00882e00304500c01d0900040561800d0780c000d00303054001c204480075807c20350550f000700368060402c01c15100014101100307034440e500054010 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 193494073 1250 193492823 193492829
    0x3020c07091d0a06021312050d0f091d010e0709050306011203091508010e10060f2f01050a0605121203040206070204020412050f0309060915070506040c090c050a050322050f0a03030b06030403140a09 87
    0xa005a5a4081ccc480e105614818121030003038210340c510317440700e880560741c001060041ca601684014010070800508034628243e04d40241071581c101900d80c803846041c505010b003002d01240708030004200ca101120340440d031100d01c0940032030249080290041c000b104401c03100e01002507007036600003481c145040c050040c402c100e05000d0844186200706018010450f10704a8081c901030000405003000256020061000c4001e00703042c00c848034540560b03400280040c3e0700324100348170810068440784018805004810320621202a0502e0210314004071040c800400d174109003c9280070781c075000280c13100c41e1301c100c500706084016441420401e001d0040c01034901d115800c2070000b803104c42d0207881c040c0c461810b010301c03d00541c500c2c180ea0a120b5108a10001542000090010181c0e800c1d000024292012170312901c0c089621741303500d003c00009114002d0703000740d1007035000c045e003500c06c265070b80300156171072170442c070305a00c01400f1402554600040140d00288034000d0a21a40d80c40303001d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 193495323 1250 193494073 193494089
    0x9090f060504061d06090403080c0a031509091e020f041802030a0305090126040b07021c020f16050604090e0a0f0c030c0603020c07091d0a06021312050d0f09 69
    0x83c590f407004001c05903100c055100780700001c0302d8082013140c28078480e45032089030580c6841002d500d42c00c4070402c0702d600118406042503034902c0a1008000a0420100202400c000200c0e81e440c490505c11400c0c4c8400b4070a92161000085d0740c00142c6503004013101e05a070440e0001080756000340c4400d504172842c600254140030f4071780a04101900040500b248034400e0341c5165490342d014001e01e286100700d542022003a0013200000d8005034000500641c40b5107244155070001d54040811001c0c05440c080c11400358108400c001c0903036a0400000032074400e405420854207180901282d075500c614003e0010040c2c48211414103920100082e400311580100c07440c44401203418800f4000440340030031035048c07040e0640010218864000d940f0000c11660184c55100d1600e8001e400400c00c0c444803808450321409144084ca4050000040d502d025007400750b9034002c68040401d03881110b40281044003140f1a104000c20000110100415101e0429441104012501317a03814071513a405400 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 193496573 1250 193495323 193495331
    0x3010209030613060608060c03060409030c121d0103270c0e040c08010b061c09020f1302042907080711061605010c1d0603060a08250906030309090f060504 68
    0x200c00c07a0086104080364022101007005c5ea4568001d261158020340c0c1c83d03242010300b40b01040c42e9140507400301818902c07034240500141c92543d07030f90034042e84825402003c115078649800c0f034212144490112072000f460100305004c0016490001140700c4c00b0401e00e5220a401341c4800c1003a8a2408000703042c44107040045850646028607100105006640f0385500740780900f80d840c1080780640d20302e1f0003080824242d00104200d030000802d43d45d001a40e203d8100c00190242d42c407010030b00d0700c0d0903103409405a1f407141070010004201c00710a0300514002c085c1080c4030002040070056945082e0f1010865645029034184012000039024410340d20010001c3c001c40d034090440c0001003818441c60086c031021101010030740300e140307450340d1150070328021510900c964030345000296070100005029401d41d5440e4401c2c585442008813101c4201c0d101d6071000e561014901b10004002c0032000d02c240f02d00c50a55800404c165982c0c270581c0001c50300e0b401404c00e440c0d01c9400580141c070010700100 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 193497823 1250 193496573 193496581
    0x409020c100603050f160302060d0f14070509031b0d030f030e0102040b1c1b0e0d060f0902090a0e030f030a02070b04080306040e010b0a0509071206060207180203090a030e030102090306 81
    0x2689a02c408035041c2041e1240c003480b000506d8000022004480d00184942c0c01e0000701003005c00504540d42ca80d8050540e111001e051161080115074010211a940d4984448850062500e083c410230b41030403840c100103140ea021a59800500440380ba414504224819000318003640a4401c0541702c8032a0350011a0118a444001c409044d40364403901b08241c03901200e800480886e0906070030404a03120300aca1036036149020308122030a80c24003903c044d03c24141512041c040300c01d148602082d4a40714000b09056113080300c0440d40103c81203000308000307550701c8610b130303500d00c943d4100b2254004040300144c481c01166060fa8417480d0015210842880c00d460410500e500855100f80f103203141514440d010201403246803444a4043c04828625081c40100410310340001c243c00e00f080480011070352410618059100108000d8006181007814041a030180692119400c02680d2041c020803480750000030310311140c0d540508004100324102030109000e80309400c3da40d07070541b007141c00f44 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 193499073 1250 193497823 193497833
    0x307030207051f09030306050d110405190905030327101a37050d060203040819050403020114030f0f0709170f0c09070815040f11030702060702070b0409020c100603 72
    0x1120a1382c030030340d000c010302030f120010031508850454010f000380c01a07214844840c1000d900c0142c20900c0310310003064035004510352006a40e406001110749800100c24002584074031880074843c4517176540100e10714154248502c0d9900780390b03081c9400d01d43e1646800c0500c150b40c140d40714803214014100341503c0c20b0381307003424201004d6076050019072100c0303420303038140c60103d40b103002d007551402094240300f10b100c0c1e1101e0020f504040e1041c1c40d060340802400385500b08104c580702280c03c0c9919403a450b586035000151116207400458421140d0400030441078802c001d44440c0d20a96002c03804009880300354007100c0e030031560741000700c442ea18408517110b1542c0004d03e08001141030307011250a501d0210070b02100c09410340d94800460031400104810f002282c0980d80d1a007409080040c003480c1a80d4074100782d0f44c5056001e02803038000400c0c02625a41403011940c0311400c0e00040c014a031905600345d006201c0c0e4070424141544c0172501580040e01402041c44810743d81d41c0a211040d16401d00d = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 193500323 1250 193499073 193499081
    0x1213170f0307090b030601050a080c0c070f0609050a260c0604060c0c080708030313030e310615120212151206100612151710020f0307030207051f 64
    0x20100c04610300d00b200186000304c0c0400c892203108181d5506003406a003840c03d888114019102c1c10120710240722541c540c440400c14074000f0062040c08190b82442c1c81005000b2240d01c1c0c01c05070003200942000c2c001c406941c01062240c54010a0380c0c01c00084101c0b4203424811405803003a800640001d0020b0729a40c84080e6842150048402c0c81500d80c1c1d0f260942d984100700e1181c483e40d070b0030610016202e82d94080055800074001d0a00c0c0700d07134020450018450000b222000c41010b81da02d00c2d48411000d09400e00314105040d990704000305400d042580c50030310394031012307603040000031070000035004c1064040c0c4910540c203449400d02070034120828031984034445900c6004001481500505c0000013400501070b180141c10000c030329080000c11201b07210100040003440340c032000840341c10200e1240d45002003441c07540c164540c4486440c401c0c1080c50003c18901510f005008517040c41c0007501c2240c1c2c002c0b4a5050050341c5040714608641003c45004501045042c0a0600381c0341c4621504 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 193501573 1250 193500323 193500331
    0xb0405010807140f09010e060d050f03032401090b090a03080f30071b14060601120204030309050906030a0203061f05040c27120c050301111213170f03 66
    0x605280c034820090107000b1001920090960301c1102d40004007c5103180b90350040d0001800750039540e0346122521a245403808840101c00707698000070811150814044484407508090f1582081000140000030701002c16801021406d160001c0d68500319964102c0680c0290b40c42204e240d180c0c2d103902110440c0c1d4000a5054881d841c422000100188085a40c03c00081d00b02080c0310281d203401c4170071a01803281803200070007020315049110124506408250249590303034010406031030090001400600c1000c024002d190041c881400003d800c450040309803072081d0364502d1681c0d901d00000c2e1030403000d400041d405008400520000750340c69002520450303040002c890342140d942080c0012210001030b084001841c9074010028440b005d8482da541d05e00c1803400207031441e01c031030301842c0c1420700100803100e000740e1000403c40d900b402c2c010703d000888003902017030509401420340c680d0403500401c00110700f0003d510810400007000e085120b44a031209a0795141c049a8000182c03590040d1 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 193502823 1250 193501573 193501589
    0x2071404051608071704210810090b0303120103080417030301120f0f0507080c030f070f150c1703010521100b0d0b07030606080a0203010501020706120b0405010807 72
    0x80104003400e05024403030140c008541e40c4401109000d50407548128050240b00811482c074036500145032110100c0381c00359000d517240b11070130400350384002003111031852118284450182000548420400303140100e860a0601242100b03c42c00040d0442c81341c01c10307402c2c0340709540d400803041c0094140600280d9000c44011000121003021007690790009103d1849030116884611000640b6103170054200340c42003155000003030190ba561410102e03180c00500d41380d8494101005030b40380401c4007407842035509000c1d2a0f03407400c0290394604403010703000d014510034042112203503013803080501c400301e6030700030036500550001e400148203907038828840d13640b0480844641d042865605140b00e0442d407003260040501c015450f0061014001e0012200da2025400199001054208068622822075558002042c909140b406003000700090000d20729103105000601181e41c000a0250a07200c480c20080640700d0084142c1020b001c80c0d105003a00542050b00009107000005036a2068074508 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 193504073 1250 193502823 193502849
    0x50105120102040806010513020910050c0c010314220c080307020a060f08060112020d050f090f07080a02090c1911060703140a090302030c030703110601050f010f08060402040807060207 81
    0x10303444550a030701450280c04841c0c1c100c24010445803400c0b803900c00324544404800341c24000c002000440210816510703001062001912041e2107106004004070340d0401d0034100040a16000c1d4003038102d600030070301515010b02c2400c40306507003118010040882c0c1c0c0030140c2005c50740c580d030b801c50705c0780c1007280100c0c0920700300c0b10b000c1074450003642c1e801c0310a0246d80e1122504d0740c82030011648200c0c18091001c5851f42041000d02031001030103802c1c4603c24240b05c200e01da0401b100140d20300010040d4a92054000315030903c1b0b40840401d4030340549404a0b1a2001500c8901102a0520a180d048090052240c01000900b900260180750001410301603502d19542ca030001e6013590310002d00140070b440740c4400074860320700c1603010301d81c0140030344100c0e41002c80a00110786198040441500800c0203465106001502001000d02420040d60342108070043d000c000f8146400300c2c40d00105210601d80002c101c0c3d115513050710000d02000c412105070381e903140070207922030b0a03a000f814401024 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 193505323 1250 193504073 193504099
    0x60108070e0a09110118120803060a050a03020303120a141501080907060f111603140c0a0303050a0309020f19061803081c09060f0c030b0103090521040302090a050105 73
    0x150f842800030700c41c0c001c00d10f00f8071080400011903280d07600f1201d40d103003140c1100300070405180c0c50b03107176241c0c0c0d51081406a5907802c1941c200842031609500091180380b81d11000e00c01a100803040c2d4140341c201e040c8008090321041c41c1c0f00c021f0401c400344104508024401c01100d1a4121a55031140100381c960802a841d1070440c55103034107043c01640045800301055603c1d1911500400b15144440d1081e102c00d0115114a81c5d04a42640d00550341c82042842010303003084244952643c0900032035a00355814a103980142041c0240341c901e9043c142c3c0e40c0304810a40d00c5412003c00007480007441c0d005501c03000c0318075007004901d070b020f0b280000c0c100200301e20400250904038410389030000512401d110412400c40110038100c01e1006001d911000300c1c100003141030241c009501072800001c11010f031100c200404486003813882c0b504040c10610003001269010641a074814001c01106000b10380403000351004d8407541d403000307410103901d40400c48039680f40d0344442d050302c0f8101c0f805401011 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 193506573 1250 193505323 193505341
    0x1401020d020a1701080706050d060806070903050f0609060c03151305090706020118021014030103060b010806030a0209040803060105070b0907030b0f0c0315130e0c09010504151a0c060108070e 84
    0x40034010012541e1003071b0024045180203001804143c1c2c02c10308042115074980710243d041c01340545030030b4082038001000788104981802080303020700c00d450040105260507040595603c0020344003100b11540000411030b00c9000c1a00481c400c40090180030145001201501c0105000c0783d41072a640a001d0021031140d2041c00344507040314241c4100f80040d403843c0c080100f00d08a5000c3d407070900810401030030310500004040c1d0b009600031040001c64044107070001d0241000104220712a0300241c600c0d800580c1c1e66884503800a802120040e200c1e0340741c20050364148200803014001e5803004007000004a0001240803c1e0380c41400c091010761208201410020380694180344a110184000740085d42c4054030440700f441c00500c110020840b0000b01000c075030400c06002029080641100320380e0401c0a007103401400151000c10402081711a038914210850113442c415400591880400700345080079206404550410b880341540d40310481c90f62013103140301d0190050455000119850 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 193507823 1250 193506573 193506617
    0x6090c17061206041502070209040c0f0906061e030204080111030103050c01020102030405100209030a0803011805060909120702030705060f0301150c0309090e100507050a11071a071401020d020a 85
    0x2801d180148581c1d140d5a8440e004145400349000d01700d90300b48940e2016a4480040e6400f80340260028418142040800c2c000000160013982100341894020040c1907844050b08800e81440005514a03800c002d10840181c42203a22074112982458022540c40380003000540c122445002102d6042c480440107a090380811200a052a041a428017003038500c0da800038106c508005084d80d103400001e40c0c03041a950400c1c0c1004c03040390780f01e002048800c0014400c4980090301100e0443ca6403400c18031065456065134880c00502c040403640204540b010808003000e44030040640e03848a00c121100a0039400c00d21690500403940d5800d001050300600c464000140c05544150342300d42003010a401801035054109014450947c3c501c2c10341d089442458001e0895a43d0a135842e100184001e104d1040000440c000e5000590b0400c070b0980101e2809600e5184c010342e0585419140c1840e01003000c40a0300030402d5400003aa80820704625801001629400e0702e611488c0008150300f00701d14 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 193509073 1250 193507823 193507849
    0x90e34020f0d0905281403371a010902090307060f09030b090a0b0405160608060303120603100906020d060e06210a020607060b011407121206090c1706 66
    0x41440000c0c00d00c04d45c100340c01c600d9a800f081191005d030174001d00440c2c140c0454154801ea80f480b0100000e041146030a01103041c4008024040c82010b0186c20440c40140301e000d65000171260301d444078501000300ca010134501030040204195000d6a42d403041401a501642c0c0d480e101c0c2c001d1700c0c03010a207180030340403d500200d805e50701c98000301c0c259607a903134008070f0281500c1050721602400c2e000194401812a00c214030900140010b400541c4000c0781241a13070300940240855542008940c0c0c600105407004800c030065910309035140c1d40003117801c1051a42c640812181400706403c28030405400070528662038440c2000420742e140740c04402d510081e1840c40e802029030f10140500400105400c21040440d0700b511018a000c0d0700166090b40107600c202d804030346803095010a90780100e00b02c01960a01802c2d54508420703075540c940c6210f9811441c03801d001003010f130400b41c0d802c1a408035000d001201000c000702e28440002034510b101d10324210700100c04c0040003490305e04008039a9086 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 193510323 1250 193509073 193509077
    0x120b01120e0c2701050f0d06020d0b03010b010e0d0f03030902030607080403091502030703081506271504030f0312060603140702030c0c090c190801081507090e34020f0d 74
    0x561390a140801c08184107041460350700c41d41682000000c01d1042c40104141401c42e103000407081c080000340b50954185d02065410700c21308000b060300d640c88049110503c0b5074030400c803c114090502c0d050300180000100a034140c0314070300400c12101c0d04150a54004c7d4040c0e01d5501c000f42e0303a151034201c0b22600d00c2c01180180c10074081100002d0103055840d400c411408030b00340300f401d01e55011a0194109038111080f1020000790b17018000c0f0809500b0540040603100e14900f024803c00c0c8462500c82c0d44802031200d00a58501c07001d05100e075000314040d1440344000e00809640b450014042d111291030010f168214401062082d400013003121020440e0300c0140c188040d41004200d6215070045c144500004108820054160086024400003009495a41c481e5060030021450121440e01e101c00040c2c1100910044c1c45d00803030180e0440726004215080c070707992800031541e210304d90005507080624058031391014a00100f07024032043c06a0742262a042202c100c0301d41d840000c2039501c00 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 193511573 1250 193510323 193510399
    0x50123220807230f031803060c0f031801090b01030201021b0109090c090504060605070b0c03010806040f031803060b1003050c04141f030207061803120b01120e0c 71
    0x100180402d5203011240440c0e48a10f1403009104200b42d007403030001c199880081c1c200240c031391810950402500c05544059008042c1441c01c580600d03110321810290306003002c03021001403801c041c09414075815030005002806a202c0d0f61800c3c0303210740401c1c0000c071b0150180900c48100d0fa41801011441c0403016911031484a252660010003490b4182c100c900b0400800000b1445860380c2c0039540c014040d5544a941c1c41c1b002d4140b501e05000e01800400c0380c80070030001007200d00000280d40d6001500b1410040702c0c44524682590084240b5050900c0c0790302c01840002402a50b6000003103a07542640c1141400b603142004031b084130f4080714410000003051100b404540c1c20243d0305e46002c0c2016000350003c41441e020a0301e5845c00c40d010b800000d40016a40e01004020301800c800142c88112445828000e40d0b0003912a88041c0c115068595481616107040d0f8400c3d056051600c44040041000e0b0314450342058491021001490003000b040314424070340c1c00c0700f85803100343d02c0c8941b402ea1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 193512823 1250 193511573 193511587
    0xb06010e030f1203040507080703050703020919050406090506060103022a0307080d02091c0f030f1e02010209030c0306041e020307030606090504020414010b0a03090501232208 77
    0xda221108621560380500c070355518040d25007420030048214203024500035443e45042d142080c58264641c1012909800500d0b0400000b00300058140941c0e17412102803c80d43d941d8155905041c080c05444003042d414802444240301043e80144649400351043d680f080e91070741e0040d020f910030012000d646007259440f14400c44501d0b02c130001107030341110543e0700e080c190780c40d401d403e500b104a4040d68240d00095298041c6007002e042c0b11009103000310a1010000c617212080c00f103c480310054140314074040714003010b5128010340c9000385000c0c940b880000d0316080740203000b0740007003034001c1c044e200700040c0500e10315000070403a11417980300103482c0c401d210360b401019410080ea2400c0340c262040e000d01000080e601e001e60341c043d02e900540082d80b8901401044182c66100130050b040400403001440800b002c1070485a00916504001c19000d2082c07400c0d80c01030928401c111401000ea0180f401c00000c0210494040c7e4035080515208224078181d95404d003501487c007d006d80420031421b = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 193514073 1250 193512823 193512827
    0x6041512050102040e040b07020c0108060d060203060109050a060f2006070c08120711100912050a05040305060a0204030201121109120f071806080f0606010c0f061103060a05030303040b0601 83
    0x10240d07204a001504107691640614030f0950140e13800c076941880e040400021a07410003900c0d00c0d900c42443c0810140c10b000c4041131042c4d112980140003241c00200040050740694041e90060401070481010310303542d07c40040000700f0710f9020000150b20b0700e28406038480d0311108052240c03914000392000d40c507000c800b501d03010301e07a00048800c64420b2021800381840d0074400d40c403515480e1600c600034100d03516180d042609903d552201146000f20000215001c1d04225404114500781943c0e2803001c0300c000d403401d0260781e1000707010344141c000f084444680d0380c01130421280700b030302e80000544214032117109541006d280c0200b1040300307202d155035920744449901d40e0754000c01d00baa4124240305004608094031a008a40c665095070103211200b8000d208440080a154001c0d010001d140340320030351140e00107012541040030070034495060266482c01d1a10b001d601c403004005911104000c02c18640040b81d0461042c41c6514000420382008800c4a00c629407101001e8482c1c0d40322401 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 193515323 1250 193514073 193514099
    0x30e010f1e050912030108010618050709140f210f210d020c010203090604020f04061409091c020706090909020102030a140f0c030d0b03010c0206010b0a0509040c1106060415 76
    0x803103c090f03c100c1d0081c000034a07200c4002c0d806030020750000f03d28941410001c019090341141400ca40920b828100900c1035840201e16090750114201c080d9403411550002d40091031000c4510380c00607c400400080481c0f982550544090000030381d010030403540340854642001c141c284040c84444032420201c000c404000b8101000c2c8544010305141181e07030002d00b2038000311003c2c24194404410f0009510b8550324084102e0710403182848105d0521a00010240f106500140207903009000b00340300c8001484920390741d1036240c0d250252440c50a034020340e60201c80c426840820035140700880e180419010340190075406030015071030040d222204494040210fa2007880c0715805111944e00302412a00422080b44204021520344103100e20040032102e03006413182c86a80340c580941c02c80d41e00880c88504441c0070249954443d90300c0c04d42a5420711a8900c0c041d40180741c046100e01d40340e04400c1400100010000710b07011541c5000911007150008640e060440c0b1744a00208040804140 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 193516573 1250 193515323 193515331
    0x6100809210d0903030f050c0315010e041b0f09060507170705070515040302090f15151207050304050607021b0f010c060c0c1203090b04030c030e030d030e010f1e05 72
    0x3000750314015000981404035504200d00703d00094a07080745502140b414040d2542110f8407611081c0b80d800c09004c12034003000c000440e04d06222400c03040c4505591141d0204903004941030000c000038219210042c002001c660303894007ca800280085442846842a1154594070101303019054020650440f456002560115041d118112000c5800e45603020092610b0100502a86c0c1f80d03800c6104010341e030035000349844400c640c26000c020750000c03030001c404442142038500121071400803400c44050300c0b6448036800003107002c1e002d20002a0703001004521a0b4020700c160b0341e01c1c0c0c64025080342c460101e03001416115030943d04c070003400c2c541040d0b251004801410902d02000c069540ea03c15281e01410700c0c408113005008843c01e124490420042000c00e518042244561580c1c94002001c80a0700240030050302645030800c16000b0380e00600120310080858100380c1000c88000c01620125940106650038031072320460015141c01900da040220303d8110842221384240c3c0001008024 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 193517823 1250 193516573 193516633
    0x709091a0a090c0e03010e0d0c021f020304030308060d05070501080604140112120504060206131e12090801140c03040804050d06020d05010f030312050901020405030f0606100809 78
    0x408150907541d8846418000d142070480465501800000034102c000420f5089010341d040c00b2000090110204944014000d10b00f00a2510940b5001180401040300104140856068010760056400101410443e8401da480204960f11301042c003418400c202001005517008040501c8558055104981e101101420000e940e640c44420b01c40d0101c0d0a911a4002040e40380c04c6005008000340d43c41010541070401607d01450040700942c0c440c001000e401203240f250b1514400c0181c00412011041c61904a011650f01700d4149011104072200041000c0350900c1c100003130006041c0111225032035180145440e0303135502030f18005640d00044c42207803071007c2084080703080d6840f28041091180580001078660707100c00005022540181c100c008000e1a0100400000303501001c600321062207403a0104240e00c4d03440300640a40140c0e000715500d40100e1101288440c0006084e0f44200b03012251003510710007231503003600c40c002d0603503086420760401c207140c100180c81041d0854072000d0751 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 193519073 1250 193517823 193517861
    0x1011031603020f0d030504051507080c0901020a061b110601060f0804020a09050702060406200f09010903230c27090a0c03080d0b010f0e011b0611031608070909 70
    0x80c3c1c505007080ca0283c1c0c3d00700400d40c4c85c402e0200740141006101404040b6407025110fa00b403201c40902161030007004051158400107400e880c5901c06d0082501e040d81c800c0048c04060003140d80844500c05509030000003d0030a0005544000c0005071b850494906441c0d6240e001030b8028200d0780c1e1140200300366000700c085100081c1c03003000743c401c41d8400c0310640d000c0c00c0b180c10940303420800d82d00c0e25501014124203480c00090300b689294200c1e1030f055480407510399141001c02c010ba0305402e29030300141c180d080d03590301c06441c45004005440f2400030342e425210700b032040200700101000294a981079403201112000c0000c80c03607a80031034004c0b075600c0c2211011041942d40001001c9190030458007400040350b03c1143e80020701603020704000900300082103140d91100104402c021070041c0b410400400b511104100e11098000da06070340065013440030100c000500c03c00344d8004d90780d500c0d038139010312100d07407059110b0100710780112110303541c0d01d6809140c6034420004d0018110106281855 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 193520323 1250 193519073 193519093
    0xd0b010e0d0c0501081501020705300d030b0301090c050103180c080a0c0501030c02060c03100504050a06030b0702032110050607030806040501050a05010c0b0c040f03030c02101103160302 82
    0x400d4030410704140301c0c1000001060910f0b0004040041c06843d50300c958908100d2074242d6038021654200703640003601c001c00b003a601c00c0440c200500c0750005070b40034603014084045242d28046001442c00649031000d00180b01c41000b41400c07a801000c0c0542655203415043c0f00d190301c203800c91325100c1c1d840400c0c40041c0800c0c0c0c680c0c050001496204081f103a00c44d141c250101329500305d0080050000b420100400c0b02000360103502e4080051100c0180d0300d00000052011006201780c801503c00504100050700e819a020001000710340030543d0280070322030000c0c86142c03000044a909100005051040740145100c0d04403040f4050615445da501c811070114043d05c400c40030b01800d601030743d510000c3c0d04100c02408100c50068021500450521906000598200c120610b030b21f940580907064694a04940c46074500036500400c9a02a0f44200003050691049104400c070307008940422103098a04000d4408480300303002a941908140031858444030b0180c10110598040d0040e141c1c0e80070 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 193521573 1250 193520323 193520329
    0x90b07080f090111150a0612020d020f0420040e0117030703110a060911040c050414090a0605030d0c030206070e01090308030a1515090b030606030402090c090604091407140d0b010e 79
    0x81426034180340e046517401004040038950158000800010882e030040d43e1450b00030a10b2103194141c0030340103a09804480c0c0043d12150b026180d50341910302c1222088100c0c510700ca145620920458504a40b0540007191002d1f080c1c0520480c2d150100081d490321642e81e4098170844048080d207046401410b01c0310307001c212a80110ba16503407007402c0c082411502d0341c0030001201c12101000c0200002803209000c1400351440400e00c03590100c480310469620345080070050801c5812032600f5001d41210844015001180110028800d4080c1c610685c2c40e178204444580194003084d00003403020702c04001040e141d100541d0401c01c40c88011840b00c81110020480c40b0303056100d000b103912600703c0e01000340c1d40a513400d4090006001d01074918101300c070004084e0b000c040c00c060b20803c850004584d0408920b030480d840d0070000740c105034890341d60300c44104c000c01c070031000c9040405d920b00001740d0040c400c8503130000600040c140b4a08040c0c000843c01d0060141421881c18420002e0003000255 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 193522823 1250 193521573 193521583
    0x801290f012019021305090705010c0c0306020a0216150c030c031205070e0a0f0b040302220908090114070507090b13020d020c010c05040305070b03070e04020a09030201090b07080f090111 82
    0x1c011aa0341511071941d904c10301180c881e17a0300326000460701e842d0078400c0111020404004869092801109050031030911540e031a065900003000305200103403070694203401054080008000040c504002c0382e80d003011012001711003a0140005400d072110708002806400c00840c982e020703103040c40c03001d0410040c0508440043d1005000714a0456001e1202e00d402c12050001c0c000c0c2c03d60003400c0c41d10382100844d6902507400000d2161040421040e40752841c841a000c1c6070682440070b00c8170300210b081c00401c43e800305c84400d00144a04c50144250480d04080b116441e0348000200b480c207191460400040807001016644800304040f81c1d1301074180b90000d0300104605c1040165590040c665850840310040868400e0243c18882003001c140301041e25822101c5510001e03a40c4d45d24050111010781035501041c1d0712030f20101e18140314660142100c02620720030380350019180d494a07040e14640c0600c0000070305d081010009043c44903c0c1d00d010b0030147d036040c10611203034441103a042c2d0900f = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 193524073 1250 193522823 193522843
    0x5040e13050708010e0c0618030d030b03060609090a022b0c080105092808091507020301050702060907052b12030b0d020a061d06040801290f0120 64
    0x4a003a40c540c480a1000610265004001d01e90080003084140140e10b61034694206000b88641000301d8a030024101580000c2422600201a280040c4200102800074000c40d0302032802449118002401800c0056a80c1d0084806800800720f0051039800c111f1800041e041c0c0300e0b2030003404045042c8030002040908141c03031103001460642d905110b2814219040100601e001d503201038803810500e04c04102c2c0603410510f071400200d280c68682826502c601c1104a8590004680d80b4803622202d42e0a0203050f400d4800c5009100726120107a040340c0e00d00c01580e403803e8a802070401000140380550300d003025044440b002c203200203122a0200d4140e85070300c2041e1506400d0038000640241e05100d401c1c03040b40c04444500103100141c0200320b108516001304000e009030f84c102c0b42c81411513071641660490f00107100582e102d480d0f40d5001e020380284050340e9003441c041700780400c14400e150f65040c2c0c003d0020303068102e0040f2034001110340301008080e035800c0030700c00c0c2000b030740c141d500340448001 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 193525179 1106 193524073 193524091
    0x605190302090603010f0608071403060609010c05151609030312050a0e010c020318010e030c041d030406030615020607090905090f06010305010c0e10090504050705040e 74
    0x34890ba0b14401d0f4400004000003031504061061340d0199071483c0d80e00c0e20181c4400c8405c0d07425185e0808070184040e02400020010f0070110040e100e40310051408030780040c411f0312181c0c2000c40c080e5082c4061500d1000f00441d10400c090100068552840d007000503515585000707103109000c072405001c150b11a4081154000980c0055080f0904107000f0411141c2051001e9501e5100c1034083e951900c42e0b0f1100212036014800384c0070054009409400004001c004001c002c20b510500300100c203842d02d2056100e424204003810142001d030b113001406034100180810b40b00000080c5104551104040080e6258014000000c03924400d001007810380301c603c040d504082c1180303000b0209101c2c40000005110054011164140194480000e007420703041c14003c40888018500c00441c44560040191741050360219901c00403034549a42416129032a800e1203890507142d44131 = true := by decide +kernel

theorem cover : BRFrame.Cov 193345323 193525179 := by
  have h0 := BRFrame.cov_init 193345323
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 193345323 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 193345323 ≤ n) (h2 : n < 193525179) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
