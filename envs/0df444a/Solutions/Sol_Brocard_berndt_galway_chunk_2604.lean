-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2604
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:12:04.179438+00:00
-- url     : https://prove2.me/submissions/5c958dde-b837-4cae-9cd7-87b389f1b15f

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 468165467 ≤ n < 468345323 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 468166717 1250 468165467 468165493
    0x605040b1914211506010e010e0f060d020f1917040b06010c14030705070b09060702010c08040f0303120f1a1e030723030303060a0302061b0105041101030c0e060d020c 73
    0x81003c00d40034016207454030f580300da040c00300d01d00200802d0603c0340100c000303000d03a64020008051030740c054035210010011200080c40e24010061040e1540e400010b2a0035000d61500181a00e90b4440a0403102603e921b18255001c41c1c0c0c01d00c52400c003c0b0200e0004000c642000c41850700301c401818041d00d28095621031205150b090b842014480e4000160141040020042c12000701050b520082c20200c2d03800000e0b14520400c00d001e0304100111410380144402038007203d00802c80f0f08912880e081d07032450090300b0201c22000f00940d00d8905225040d0085581c003c4c41c40c0e50030b844c014400aa050581000003022400188015404440d0400501910b0400180014000036510562003082109403002500300700304185001342c00910501c0803684400c40c0740d4082d607504075001912004400000001031100136001c0300590b0818040c4018400c410302d60518800080c1d0b800d21103403a0a946c29035454440104064100d1801c00400d081c2100e180d0217480f0030b0b900c4006403802c1440b045 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 468167967 1250 468166717 468166759
    0x60e04060b030915040303110a08040b061e01030f110406080103020a0e0c09040c030b120303101409071416060906050915070503100302030717010b091302010e0d14010605040b1914 79
    0x1e270011005c240c0f404203000c01d1291a20540d82d1011045407122080405034055030044500d4403481c905050300e400403400402400e41244400b6000b2203000d40d2261350316840148a008207200c2640298200702010901320542d07a50a8400c000c030125007468008510213100062600c034140c6000c01d0f42d60780c0007015039514445511289413642e0011034a9040c640300074181e62040d03900bd035a842e2440c03003541074507440b456592648000741e41001c086d0041c0214000e4410b2198140340c4010500c02440003040005a902101501d40145010000c90b601c0d0f14441c0da403029600c0c1404c5c10400b1000c0090780d02482240110351200070f08160001c566600c2e400300303181400c076030008901401c00e480103184544091003403c65910045a510640d4103013001c0d80207010001310006410070000600a60464982c0d10603180f4456002e218035003024041003030303240248100d010703072445035042082501d164984114a00030110307030904e008150324501500d1103500702c4005065604103401d001407100c0001c2c12 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 468169217 1250 468167967 468167977
    0xb0d2406021002210403090305191e020d0b0c0c070b12070c0b0a0c03140a1d01020f1602030a020414040302060721050a06030804060e04060b03091504030311 69
    0x1846512600303052180103420b0081d242d241c1415103106210342d1000300120041d01000801030910149952500d05040b03a6a1496400c080c110340b1844ca01140d12080b000180342160303000e0320280c0400c2090070001526408003400196008000380c0c0901c000c94030310340311107802c19002c641c100e20b442a031040060402e0000d9202c00c40070f00c40071901f51442561400341f40e0b07010340c0d5450120002512070b80c586425032001341c148000039030f5400900c0c00781030091740000c15420302c030181600d41b440d094501c9030282448440545e1910000b00350380d15010814020b0303d14a10000d0200c508090101611a44900250300c059a040c0305800c103c1c0056140d510410b40401d000050a80151400d4103000c0e01d072002c050708030341c01c01c84880f0700c4c5031401c2d00354910f041401303a0b50700c0702095030703111503910002030030f07058001903c011400203000404030341103003405070700420540c2e0500c595660b41c41c001c1070034003007100c03102e1031038100644180000c440e2701d5040740d201e44607040001c0c7c04107240904035101c1e041 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 468170467 1250 468169217 468169271
    0xf01050709090f11030403081e04080d0c030b06030109020a050d02160506100b1c201e1305010f051c0b041404120e0a090f050a05060303070506010b0d 66
    0x41e480c02030244980300c2c00b481c0458408030342c0502000d460f5031030b42001848001e2002d003c0000e804003199140003d000e0400503100b00c640342070003904050811640303662051a002095920740811a0400c03400307406419000c8200074010390640e803030540e0b201d01a52241001e0420001300304500e015026081c40544012503a24600c110a0999840c1072441d003100602b01210390f1040740303010459020304100b140e141002031041000c04c580041400d0f0007030f01c071001181e001d0421041d01c02010802c0d98014100034035401c20130b45411200316614031050b01c114008200c0d80c5076034180500c0194010200048000c81c945065481d202c2500030410a584442c4000c2c5a03203074940241c107002d03103814012084ca642c0480c4001000d81442e0399150390f5580c180064000340002900001d80341d039590342449000700301c0e4500c02d1103c030707180e10201e000905003160050807852403c0041512418001b094400a6074040300410b210390810034011310039040b56145200c079a4075a04842c04e4819640261200f000c6 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 468171717 1250 468170467 468170477
    0x150e07090603060e0f10090204020408031c06060c020102030306092e030201081605160302120a0e100504080a060216060204080a0510050c04060804080f040602061b0301030b070e01020f010507 84
    0x1042d4a0314100b6101c40444000726544001c4022041135008144045600a41040041c03040e0080c40031402901559001030003900000c00d00c20414814524144c50000b0303140010401e0949030982034803001c0c50b000010740143e2003400090761600f880070803950041c01400c6041c06240d840c9200740d01c0c1c0207600c40704225160410008108558100d0101d82c0c1150007100700281000990702c000b0294041c40c403410404100400d188024107009101003003000d61400c003920b565281d0b801016007c40038100b5028000e1450301100f200b0300c2d04c45c505031741c00d41d001d620142401c0306a46d291036000e50818081a0791190942c050000019202d1005100410340600500b00b80b50413400c0c82c80c2880749041040d2401d904200130055482041300445017030f01c0003030031b000c041d9494a04001426011b513203541c238031104c80020b0208106400089981c891a0381034120401041c2c2004081482d02080c40000d0201200e1030108a125004001d000340e42c88040c412a0340c0d02e40720400c510300390340007a243c2c00c000c10 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 468172967 1250 468171717 468171719
    0xe040902040e0f0d1b020d0215130503070b0a020c360403020d0305070509040f11040806100b1c0902030a060609020a0306050109030b010603110d020304050606120a020a03150e070906 80
    0x414880d4806081321070411920440e9a540d074044d03000a0003000900c1080600c0c011000c540c1c400022040300c4071f00010883e101e00d11303445013030a034079140d004091207403040e540001810b0f010a02105d4800d00254058514003a480c1705000d580303103a680e000c860510446492000008030f0001554941901c0b1184900500f030505003e404c0c07078050982d64040500b403070100402c0036000030440d140100306850005071310020380d250700d000b030040c005441c403940d00000780001c01007400904039014403001401100c46695403802c0040d14410031450700400350b220a400c898041305540a92b400f07a002a05560380030240342d0307a0b0801c030b403c0b80c2c000070302c82940400d5070015241e2601c20007018110a0800341c1c1c1241c10342e102d4a105840511a0310304140d22614641280c01000090b02c04c080e400302015902d905103458900c0e10b42034110703140c0307001d0320f070001c404082d041d40010040e039900e4004d0810103a050550f00c0301071101c00d4808440351281c1e191446420754000401026001345401d8100098031 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 468174217 1250 468172967 468172993
    0x203220c0b162a061119110909030301120807060605040c0816092d1d0402190b0315060c070801060e180d030e0c1f09090513030e040902040e 62
    0x50001d980b00820115101c605110208040001d55415070300b070703400c00d101303190312002d4178a00e002612103581c41c410b5201e041c1c0e04104411800c03000100001100d10120b15030b900c01d06280d99000920407400402211000840810b441308001c04030903024910220321140c842000c01e080d00e00003003880c40003443c4002007017103d00088281d40d01c00403081c50150503403450000313140048020046c00d8411403141014400720080b0344081c120080002008081100170090b00c044840031003107030300780c1c09011266041c1c60007001744c0e0091026500c0c901240703401c580b1a00008030301c82d60a4144c2c01d80281c41001020070300003040100b60020f1070101c0002c26810b00300403100303443d41c4014003a40b943e81c500c0006510703080130100340403038660800d1800049c000c0200d00c01c1460724074940340706604070466501c41c4401990450f10a07100d48030680352001d01ca0350b581c0598003260821a941444000d05151803c00a0300c03d80118662040090010803111003a800050480b001d0300d07040c0032154005181d50640e = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 468175467 1250 468174217 468174233
    0x1140319050601080c18030c091608010503060112080c07030c12020f060901051e0909010608070f02120414040b030105010803042c0117031e0a0e03010203220c0b16 72
    0x701800038a05007400c1d040c40c0c45c0703043c0c86006034400c5c502c0c0344400403803400485d141000610413185004102c00050704116907400035882c2440c555030700141048001003820700b00011401c1c121042c46840f00d842c59a280c4418401d600003820000c11405200d6001022942d041040d00241c0008611104403d040d0710400400c2c100c00c4001c80d0282c4001d2108015aa8010b01680c4520307404800c50034901c42c1c1241044164420000c5682c0d01420050002c00d00c140d001a08502c5540783d030701c0d403803084656034406903a0751564039984030150100300010320203140d400348100310701076001d40007142c02410f040001c0e00b0741e54240c02001a5910104003000010240000160183c42450101000459285081d4203801c01402840c070000c0398210400350f10350301003088030780c84840d0202551005000b99281000c95200415110002c1e00c91540040700d031606108503030103000340d41c0340c510300310001c400c0d0454103601d00a8207071020701c41d90342e00040d4241c00354010f0802802c2450600010441d41c901502c03 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 468176717 1250 468175467 468175471
    0x110910061821140a0f031409090a0209040f1107020f0607080a0813020306070c0507151205040f020307090c090e040b0403031a1207230a03030e0114031905 68
    0x561400e01c010481d00030151070104412002d4890242c0442c0141030040054085035000b50003031140c00f90071802c3c48401508000c0c56446503884801c09102d041400c01c25000720400302e5070010030000410b50200f5103a00510841d40043c2010030030580310301c0b41b0b80031540d00c400401c2d511000041c800e400c62802c0c54a503500c1c11001c4541c5428000292501e000728000d43c110102440090808070b03d8850b01070504200702a07004084039000d00d460718009106c051461022151031140030b101260301150170070f0f000754a030303110303651200700c11503103d4941c026090151058402c102c24008410250710140111006050f55070030100e00411007610040801c10740c3d074003450800182c042800001402e001c861034215403d441c0101c1e0401c2c00d0302d152010b407101102d805030301c0001c110b000e045e061000314500e011148094440d01940d00c0303466041c0783c0d10080366030080c2e0201c40c2c0c0205100181c00740303107501002841031600c01d03820030f0484d1002c100b0350b00558024200811443c134202201e042802665 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 468177967 1250 468176717 468176747
    0xd02030f0a050a110a1a090301020912010b01030c050a1209080405041514040c080a0218060c07031112060106114b060a02090d0f0303052502030a05030411091006 71
    0x10b25514180346c00f04503500303034412100015000a1460745540e402d4050750321481004006401c00d0a01c120043e000748940e0000c940072a0401841090140c01042a0742e038181403511107a4402c2c42a2680714010000c2d04000c44940d0740a01c8042840d40b07952107040e41454210b81c1100f8000c2c01c04200000c2045002152440f950901c40c2c41c410741c1c0e502440c0181c200201801c050f07152178440b0141d1016640854056030407080114015071200c0d00014254112801815001d244601880c1484a080d440340503125041c0d11080041203003902c56114005402100f00039106c029031281000e000404e041c185200d500041e03441c5085642180542050100701240600e1034403480f1903109a45486e001007414200340d901288500694440c121841c03074481d8001c0340003110800a1a01034020501030f1885820340300c03000c0a14850250108521030841e2050b0001c2d82403038066002110380d0740c0010421100356002a058044035256200854055560094250903450520303900401c9061054654 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 468179217 1250 468177967 468177979
    0x9060103241b03091406090d200f03090a090221070c050714090f19050c0c031603170c030a0b0a0905040b0105100318020d06061e0f060e0f0d02030f0a050a11 69
    0x2c031201070740014801401d123070380b03043c80540c000742c0314802c10100c0801e80100815007d0400510140d003004001042080300c1110160f2219031225501c00880c010552045250b0540860804841d0610000a03501c841c05180c44080703001c0300d03a18141004803070740c0010f0340a54454a0902c0074607241c4c2903e40e0040e0008100310301071412400040c41707159000d00001c4e0041e56034021501c49001c0c86c00325030f000c448500840b82c0c1c80840386010510501d0f50341d010b40010703205444803040d40094107005400740440c0a00107040d0386803201c0c050000c8c14041e80081c2c4c0310710b4141e0700060f08481d80c02418821406642c00e00d299614203c14041c4040c486c2d00b0500426240007652040e04119400160f0055015500900b56600b1403420b4001031555402c81c031000b40c1d0b5603103e110b80c0d100c1c5004843c10b0f12900d28007400410345d103190607510095164025640182d01c16203400c4281841a00441e090380010b0880e09114040944c1d42c1c10440d03103050640b074940080700c2000a001e00d5560442e40c0311019698 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 468180467 1250 468179217 468179221
    0x304030503060906030f0d02060916060f120b0d05031c1526030c0d110c090a020d29040605090903070330060303030509060103241b03091406 62
    0x10220301c002007045101c1c2c040d94010581684040040000c00b0000c8811503032042158440a503a900084888002c1071080300454031800407040fa00301c0460726a6114105030948104003030390100b003001c21a0800c1541c88410341c449a030307490f1030f403c400c5000700301660b50b4420f503042400c54510019002401d0700c0c2072050741c010464009151004480032184030744000345e0f07178048000c030340c401d13820300840c0794400415040204040030130800ca981d096910f0340b124460407a00e48589508118600c15801007403000010100e64882c0c000381680340b40b284000230207108c1d06502c0c0e1f50815080700080c45001c80c1c0e0030309030442c0c00c05205501c09800c04445c8182146884c41c0450750f240306041e0b0080c10049000c0042455a1039188070b00026a01000e4508a8a01901210008100350301c42a000070b400c020115401d5200424034034180d075003010704c030100e0807010304110400881e503481d020030843e036503803004c86030030f110151000703103511030b55008a40c147c0107042c246891003030007800c150140c0114003 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 468181717 1250 468180467 468180473
    0xc0316111c05070515090306010905010807080d3915060e0907090905030c010c020c1e090601031509090602070209010f1d06041e0615020c24071a100b0304 68
    0xc1c454212101101c11703105d050030a20079800e543c00b070f055005415100d200000b0078541041d41106058807804800c6445040ea80c00c922540ea00114042601141c030308039541121505c11401100c0c05104508240c410314082c0d9054480f800c000708054801e031428001d80400386065005260050041050101040c10403040880e00c404281c40b61622640c6d841d6902402c100c400d005036100000713950000c01c028040b0400103500c40d4211100103116107842c00000d6000348146440d04450980540440440d82e01e00006600414498035110b80041030000005007801041c000c41c26a18425540561900c4071441440303980c01060700b1107841d422801e0300501154418280d8400034141038440840e8584612011900400000703076103002c0301d503940d6078008101e03032035030041d00c01c441c2e4070301b01c031040b44041240c100d071180b2020601d00d40c001c1c8070002c08120054842000416440c007140580d2610702c851780c0342504248032060300c0c3da01843c00c1c03003041448412045088020700303000c0d1420740b951525075 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 468182967 1250 468181717 468181723
    0x61519050f010c050601090606140304031e0201020c0d0c06060b07020d0602030a06091a010e01140a0c060b03061608010504050601171e10170703170c0316111c05 71
    0x40034260258002a000009582c4522040000300341c02005030b80d15540c44000c2071004c0d00c164000e0b000480d20b03c44040f04200200c1c0e048900c19030309641c901122007503d440d0383d11214003c000300c03021036400784490944202d0030710500000c00450749641c0b20070802c40c0f0b008002c0d00c01a5200f00140401800620b000d03854103011442c1650b402400143e8a540b212013550062820390040040a4601190078144446441d002d6003408000d80b5510890324500004546148560380c4503803d440b8107100d031108103805507a00982e02071140002240034060398010a01c0c00ca012921441085034242101020a42010030a8003400050318180203902e0464006021850141c400d0351ba45242c4c41c0004641c0150940c0010381c00c1c5030160301d2101c03803c1500012026610501844044550340050030080641c005520011268484a4032510f1020004085040c0c0c01407801d041e000c4c04100000320b0020f450001c8042d02900c205a03140010011800380b01e07105042e201a184185051040c01c00490302c00 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 468184217 1250 468182967 468182969
    0x501021005090706080a0f09030302181009090f0902090f01060f080f01030807030318030509121b0907090b0c1f0c14180a08030d0c05190c030905030a05061519 70
    0x3d017000341558440380c0f1003000800b05214002942860408a4000c045d4950003c0c11001700c0072a0030074040581e402086668000d14943d04046103242504203c1c0741840e030040303800d100550382c0c00100030700e003900800c44404044601158154410340180403160700f05448a80500e0b2901c0e025503035280c071003141c40e2410410301001c1e0940d0030108510341010b1081d0012200b0078108520034801e000315240181181e0410550540302e000f441120704103820303000130720f4407a0890101c04d4132034818900007400120759001e0a041c013000628800440c80e5400b181c005c06070210100b005009400c0720003500c1003294900001100c4450903c03800043d1543d0102c1c40f8a6260500701006645640b10800800d00001d20000580c10000b020740004a0613808800340103505c600a0f001d02c40c10441200072a1180300d204171079232078100c00d42007aa1449200d840642261446420660900d0b80c4410020346400d2140034114dc84d5403018040006000d01d44103014448041560000c0710401d0742c142400301d601003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 468185467 1250 468184217 468184229
    0x306070203190c020a0b1201050102120702030c040906020912030d1a10080a20040f09021303080f04050d08030403200d03020d2705062202010e121605010210050907 72
    0xa2000901507603200c81e00d2000030941002d0003070b6070388047c036100c002c4102d0900c501070141c041e40742d506255110107000c8032201640100580f900303441002c1000001c114848080c0e42d569805d1000380e0140c0ca0302110a040382120100030342e01c810010501c4015a251a80340c00140c1c0c0c01100c40c0c01c81a12405115040920b2500b00f90901303548218001004148404550781c043c24521411000d41c40540011700c142c5482a01e104079890b11540c891081e48a020308054000010b12810008501c2180c0a041c2d02120a1601031610743e40720009120301440440a42d2001d1000050004241e0080c0d480200316060307107803103c0c0d005e01c131030381c601d80301c5030a40b08140a1580020716049040d10507071100e00d09509102c1c40c00c24510940e103a046418100e0b20084480f4030130000450701c50f8044020305182c41030044112400c6601710303401102c1008250302d0080e00b001100c03203a20410712061046013000285800c50740c078101d18003030009152681801d0348940a03460301c1d00303000a9103404075041c015904 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 468186717 1250 468185467 468185477
    0x9030b090d0c03081503060c040617010f0b0d060305010c031d06150d02040e030a050403260403020d020303280e010315030f030c0f0303140c0a0804020103050c070c0311030607020319 80
    0x900d0510030b01d03284100305d140130746c140500c004100001c0f8900e005030007541c01540c1c030000248880000806600c0c000e010342010000f03801c01c03c1040b040da0800806030040f40c1030000c00c40990342e6545074251030003002043c002c00d444180852100350020401f815002e84800140b40c4c44c10203040048220003503d0b4140c1c020b040041c800380a54440e50403c8509005603000c40b5541d00c02c0a42c020314540050104654640961f18150204500310802c01e42082024a440d8a00f03480c0d942080b030303581080b0500300c1c2c00d4041170020f007240352580469800d0007440c01c48400d034118100c5900421034481c10048a05140c030b080450201200c00c02c03051800e40740d0159000003a5019400d0590b544594548010014900c6071000302c109a0b054102ca1150a2040e138110381c0c5480e40001c84440307004481308a00041e0007200000c01662182d00300310b03040a0304607103091500000c0e0712500c80902c2190010f90300c0e1440e0100307128050504000065100c410740c070140d030030b10745010304030b05020003084880e400f049 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 468187967 1250 468186717 468186721
    0x1404060b04020c060a0b0a06090f0b031b0d06080115030f0f030201021c022104081c1107062c0318210109020f030d0e040518060709030b090d0c0308 65
    0x901ea075030442c0d1049042208071100c6207006003000024002034a61a40107c9941c840019018020ba100c4400d4525824562400c6814508a081030b90802851351a0304455401c1d103000c0d81032401d0052428200c100c0010408030f05012090f429030f210400412000300e60b10004201040600c8840c064a56015110350f1541d00300e410100c1c0a0b01036112040d030034003010300c0c00201440130b41d4020a28503419441410078000c43d0b05152050390000c5602400c50407007006010b448030b00c446075030f0700300ba01c0b50500011915010080079482c2e0700b004004a41256942c21001c1e0848400c032580b2040d9042801e5402001c610301000588a0048181d20b042d46150301004000d070b56110b224103005250940d5070b42102801c40750b00382d4081d020040059001e883c04002c3d9201505012036007640d212034a48910308105a02400c1c00018603008008450440d680562070752030407010300c80940594400c3d9030700d284143c1141030046c2034560143c004030455016040966401d40c00102c0c98010070381504189180d5 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 468189217 1250 468187967 468187969
    0x108011502030904021804060f14041b05070212030309030c0105090d020d050706110d02040e1b180a24020f07031509030c06110307020f07030b0114030a060203070906030b03011404060b 81
    0x5051b8840c18660190801101203140c0c0078100d0040d08455011001075490100d542c01c0c4402c1b41d01c8404242181034004104c0100d6034002d40c014500644080d000781ca59a404100c62402c40d0030546100071230790070000b01d648000509018458101a5903800360900d5104244080d5440d010402440e0a00c100403580c1800d10400e0352010324510080c1c04d406983c0d10403412841c0095101c2d0180510740411540800c000c1913808000010ba03890b5819218a44000b901c03503101ea5401a5500d40e90000710035101080082d4006101d41480803001011003208044002c040d0909071074602c0b00c2c106901c101420004609000747c54001041c00c1c5030300142c904046d007000c484103103107450068425805c1c92580101080b100d8010b610400d000d81c04d40c0e0020061380715407a00ca040e00d2001800da040c03d00010f01c04003c810004010744007005003241c07480f500700c0d9150416a08103c400d01c01080e002c1c8000c0010f50b400d402190f81c030700c000324002c000c16800301c3c00d00d4030004400f0b84003401d074941d039030f04036001 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 468190467 1250 468189217 468189247
    0x60922142514130510020105060d141905011a010c03120b060d022b020c0a0b06041d010614040905100902011206030807060b0307050a030f0f020d0b06010801150203090402 75
    0x41c0c8100d01100d6868066100000300a61503204e201e0141d00c031100c2c8605140d02c1841418058040100207840318819600c0f400501078105422204e43e005030008200c3d610302c04c2500c2d00081e8410400840c210074450719144030150326203820740c1448410b0220f180040c2d40800c1c0c003001034400e808006689041c02003c030300e207070252141c4103203240d100049a00ca03d002c8144400c18031902c80c9600c900224900041c18281c3c02000d00301c550340d038000034040d40050400031119612440190000400e81d140e04110080b00342030350b0304a803d99540d0310041c1301000e59528100c607071040a890a01c012180350b918195519004240d0700861a0b070b494040341168801c81c2e00c0d07086507450304002d2110075201e040200d129404044115180f070320b801c0ca420b800d42000720b1100e040b00e01c02820109110728540b06c1082c00c0a1586045071132035901c984e5400187d64600c2c3d40d200003400391089244500d4a0000581241410f0304441c40403240034842d504150f031300100300e440603002030b100982c0780c000600e28080c1c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 468191717 1250 468190467 468190487
    0x50406053004030503040c2702030603100204170d030b0108130201181e0f0311190302030706080901050f15011b05010c020604170307080c090609221425 67
    0x107a0007103480c180002d01d580701001d1070040c1d001c1c6060707411240da612203c03e400c0080b1444020300860003007100042d1036140d800780d40c0c0002d000c3c00343c1d1a0903040d492808104d07032050301b05941c400307081544840b540c0c10402002e4160322450408000c08801200040c0807168010701d4984110081c51b5881d007164400c0c00c0365008100e9400ea400700e19500c648001c1000c03991030308012100c0510b4403000a078131740030541e0181140e8102c40c1461011110340e003030064541d000d002c07045601d034200c0c0000006031410003000c030090909544092150402d00c01d00c07420b484014010541c2400d800050005802c0160310090f9030110900303007034003030310241440b10711a0301c06600080e165518040d0500100c03070300480d40034803c0d403140500301c04840030300804200e03a0105440307150002d58440b0008907880860002000d03500001400f131800c050b0b0440c0006d00f00041202244035801444070002c04280c9280650070008400c0504c0d00454a4004c44044202ca214107050180100c5021406912401419554 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 468192967 1250 468191717 468191797
    0x12010b0f040e0703180c06030e060606041403070b071203050106050918191814030a0e0907120f1406030c010c0818030d0f02070e0106020303041709030a150c05040605 73
    0x800085c905151074240c69500c6043c010908180404906160201b0351074421034004102c6400c040c00e0080460580103044411505881485070205102e41c0204c003a2495521400980c0c02c0d8004181c002130684006a1240090020130b008281c07140c0d0b81c41210740e41412112904e422980d9a040c1d600c070303240e80280508148940361008007110b078001d4040140007240035440301d132000145c10600581d6032140708443c800003020300b030080b181840c05001850700305a00b460042c0d10900301c0c1e00d5003012a01c44c04240380300303075036200c40042000980c03001055201d04201c0190032160211400038140c1108100010030042c0b00060215080414440f9440c0d0300310094100c0d00e501d2041c0e080500800709a0b008040548140b040028040041c2d510b050306903500fa074051801e5407036a5a038903004041460444040040a00144a0a40f004c010070403030740740696111b40303000d0008580f036012505914548010405c00300010302c10540c00c1421101205841850031000da4940411104500c5000d0107503 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 468194217 1250 468192967 468193001
    0x50601091a090a050d0804120c090e16060908100510090912030b030303060d0809031c0c03090803071a090f0615010237110a06030212010b0f040e0703 66
    0x4030000d008420040c010303005069505040d075a4540b805c0255103620350000400e0050104028800e18060035401607030030380b1424801040c0d6071144803000035909003503a10541a032207410400121078800380040c0080c12942407079503c0c5420300d100c258484003541f400c4a01540c480006c2540c0e034404440c600b00400b05036008200000092818090710601c2c889650002030406607290742c9071402200f02d038015200108940354100081d0f1740c2d2039054002c00103040e0306029646081d5110080900086100f170100d40e52542d11840034500540460140e0700036101d1540240710101c005111151410740c04040721002031043d640e0070118030b20789541c4100c0104240200c2c17081c040b1b0013441469442c082902602641c00c550340f2001e1030420381d02019055801d40c0030307004c407521041c07c4450308070f816070f0f018030310b0710309000742d50340215403070307031650303448400000c6d40001c440c0d003c014801e021901600c14a80c0351407401d4041c0103030b0002401140108008041802c1c0402c01e854080e0f8443c05e0031055041c65 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 468195467 1250 468194217 468194249
    0x150c1e0203030906070e0f010e040b090702281a0c04030501020c0a0c0503010504020a0303080619080c04050f010803040302040b04140f0109060807300c03050f0c0a060c0605060109 79
    0x2000707403203070401da5000740b4521400000c540c44600406108851a1000c2c101801124166004540140c19502050b0b0800d54034a040c09450300d070f02c00000d1243c0304070340041007640c0d0b502c0c901441d81096034581983c0d800f802540302000480d108000480c001c00b6001e8520181c40d079282c603810074891075000801961002983c0e051541002c200344207020300440c0120112035441090500340d03981141e009611010100d001d1000a0090306042e400c0751001c0c10300c2d280b01525500c41242c1c003220b07401c002034680c008a2040b250b442c06c0d000309540148800d562481551410020701e07540d00441c000284110340b01c0765000e0701034035298068403000504440c450060f00344441c454600500a00950f0103960070721720041141c0c000003a41800300e400322181c40c184411050a114043c0e1409410780d411942040c8290000c641503440c204007941c01740001c0c0caa000c114062041c50f10f0b440000050040b11641810401d00e0f80000d00c00210710780159000c00c641ea543e500403107a00959402104c2e610b009811 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 468196717 1250 468195467 468195527
    0x601170705120c130e062719060513120f02010f0612020310060506090904060e071818020904020907020c060f040f1d0c3a0506090103150c 61
    0x800449460081c4e45030b002c4102c0040300d807016100c5907043d0140540c0428007041c000418440326006090783c81400d11020303a0450522400e0400146405600c4419541d04000b4443c05104040d00545240500844203846960b012002604154100184400c6d850034050150003901300c2c0052005180d400c03c001522484124504140319500ba0b00034821450410341186403486400c0669034010080c6080144100030050b0201004004842e0b03e602e442d080981e504d81000040c000c1d11230052445407103581e80e00104101d41c001c6180060015510302c0300382c05070310307480003494000d038058401401c181c2d00c11030168500a004540c07984c01100002c1c03208040403402001e003065410a042040042d6520040500707488681c04050050700c85100109071940324040c0280400d0400c103c6030f4100a80401c109109e44409500300d01d0411001031004189440b00d1042e243d0107201110a20015415038807020710356035030001131803180d9540700602c0034454080c2489000800e8a030440004001c1015 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 468197967 1250 468196717 468196723
    0xa08030708071b03050d111308031b0114010b03040501140f0a1d0d051e0f030402130c02060a1d0303100e0112050d0f090e0a140c0903060117070512 65
    0x110540d0005241c00040030220000103005400c40d84c055403454244200303980601d005221050040481c00c40410000b91890107060710301c8020103c00001d1911444034040303000d902c0501250741c4505914042c41036501660361942c26064421481b545522561240340950040200f0f0349507911054030325080180440ba400106846501580f0060104086841b105000303c0c40307000860034160003003503d866800d07214401400328010404d025004150030800403407071940c4200c005c442c4800d400001c0005500b01250405c04180c80c460007009030f0800c4407002520b03484003501c0005020f444400b000d03034050300100348007180060300e402d03240d5a0070140041c1c01545030501c40c01c00003008440c000120702c0003404424400d16040700142c00c072031105043c201d480f40d00d0210043e0070f001c881080440c8035014002814450b00f5900000121419601280418403078018003400b00080200300d0412241c074040350050458041c0e2901c00f0451090b258241d05014258104c2600180e01a2450721512000 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 468199217 1250 468197967 468197971
    0x403031d0c040b010c1106070812070201091208041a09070f060e09091f050c04090c0f090503060c091302090d0503040317031e07020f0f010213120b06120a08030708 72
    0x72102000403001441c010b581100701580c0246c031220000744403404904224004000307007407081c0c07101071030490074012001e0f40d08420740b04080142c1d550f4500c0b40c00c01c6626800b01100000f1802c0c04610b40c9802d540d03182e4068410b03259144518070640c0031420801003000000050030090300c1581070303140c6465008004c0000c14909610035403000011503120180442c1c082803c40315120108010200c182000015040180c400304d44984100400035680f0b2481c425900340c3c40340c0d0742e030351040e0b1521050000d11245041d08114171a4101c07000b803000004144c421940160000d070380c01420b8a4542001c10001d0003840410ba0700300b06000004020801c01100400540b40f04084070002c100009035500014003040b120400c056050b0801c501c10140a4005168480080e1045032480a400001103041c100a1910f49007160f40120b140d421b02a038850145025140c4e4035007100c0300b000981c880045142c03000c1c118074000d4208900c071200208060114000090300103040366501c0c180844020082081 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 468200467 1250 468199217 468199219
    0x2130c08060a030804030f110901141e090117010204030f14100b010c030e042a0f080c040b0f040e04050303010509071701030201110a0b090303180a0312050403031d0c 73
    0x40040000c80d2460900ba00c1c0040c1c0341c2108240382854116a1034034042440c04806403a0f5080200c08460266207003070486010744080b0410a07400e80040f01442249400c1c80c0d801540c245198040d0b48440c1c0385c02c0c50180c115001e0740c4540c84490642c0c1c030003038020f1083d5000500b1154141740140180b21403c01000a40780000c800c4407100381c0c00c0380c085012580070301c02060001e030070740c029280440d2044e808808141c038010000507850300310a003031703100f42200030031045007100401d240d1024035130308101d0b840307101d0361903080610140c43d000400301210701c95800f801e01d00500200742c030130035034541c042901e001e00034a0710340a403c0d00709803d0540c0e07250024428a0302c00c102503030000d05118454010800140d6806600e40c0c156401c59005442340d544540200d80648151240b01d00801c2250031f0b818010400700d07000d583c0d281481c2d03031484281c11a0400503e129882846500c000035030042500b0741b0070a100c0d00c001a543c51b1450100e000d854480c11101d0719800807202c0c080c80c4100403548110f41a0 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 468201717 1250 468200467 468200477
    0x60b12010527010e100815041424070e0d0f1b210627020406080a1a070e0a090227030304060509030c040e0a1704150c060902130c 57
    0x10804510040704502620b40d200d00003003000100800b259003443e0641121900c69403150740c1d83c80e1003030649000c010754070300002c0175070500520003813105502901c48040343c0000986140d0180312488004403189583d0740c041441c00600143c102840340300054000b803802080040c81407041e092614035018540c806a414828104125841111202020f02206c008141c0e9004403980807222400c1624084000e441d15516540e0020b50482c10601c81c142a0000921140c3d40e800c890050104459842d0481181680442e0300040454ac110b5940004d1920342c0c4035092150b074030740300c044070030040c0007038616000440c0300008141001145c002d42280409500d64003490010072441505250f8001c40094245c0c0081000703026903031061000344810700340507003200c003907100d0030010408031007240d01c1450085d0130072a0031104019000b15100d559101451616040c1404c02c0b4055000315440d56a84c4140220094001c0c204201038010545003038004262917885801c14440c100a401e801a81c400050 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 468202967 1250 468201717 468201739
    0x6070501051f0f0f060e0307030c09060305010b06030f0c0c0a02090a050a050f060f0d06090c120c06021c030b12060c030907061701060c020a17031c090b19060b120105 73
    0x11030f01d6002d05044411340ca4110781002d181a03c1500c40c1c081c4030f19490b406000d0084040085a0700108600041440d2100041d0162440c20140d0031108025a60342c421641003052098031805840200c2d00011812178841e0b54100b8134900c2442c3c564400300c001d400616032420003481046d9540705520414040c9001d11642c1d03a6480d04005185003280c0701940051581d112084074200034855540c80d611071100090750000c95210381580c88070036405030000d50500f981000402c4200700040000348901e000501148000016449504004c0d000303441c2055901d420411655958031641091030304107906613200d1b420300c9204801a03600485a0710f07094841d54400083c150302c554070740e00c0d05079100a4410102d9007044400c64240e4801e59060380d00003019940801c0c3d1030104902d1605450301d140042d03540700516407000c10400f81d1800e1178840e251501080c0d1011610041269900c01c10300c0c0c900d141c1078104c07058800001e2045c0c2e00180004840851250350031405103542d00c3c141d44007100e40100355 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 468204217 1250 468202967 468202979
    0x80102070c0602060f1906332a02040207021c060c0e031c03060302030f0708010f090f1202390a03050d030506010e06030c090103052a0906070501051f 66
    0x96000343c0798502c0302216240052860030040c2c00102d810501d00c1c1b0042038a95031580111441a1500d030100a1031803100c04e542d611208a1208103040d004506181c0324080c0000c40c486803002907114000b00f0640d0360030000045580b41d41c1200d441690051905041081c52040c42001c20540c50089482c58605460b41e4000c0380036400c540702c03640008000b01280c884001c5140702418001561300c091680390480480140c0e802d00055800140c0100208051490040640e095940b0840245034075841d25140d00042482d4055030803400e900300c040c42c03c0103251440100c1c50301d000214101c001c0008c110103500c202415901811030801c209031481180c1c4155002c021800c0c2003440001c08a901c600c064000b003e0080d0032840e804041414244442405000803914aa200f1145c1ca4420880000d00280741c0d030b0076100b01a00604059603401c2130071112070740080d40150000742003240303000c0031820302c0303c59803808121102c580d0b020000b0700031401c001d00a000c42c8a915a000070103125900408100 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 468205467 1250 468204217 468204223
    0xc140403030521061c0f0b07022104031110120204080c01020105010e07020705151608040510090311060708130314060a0b012a061b11010605060403080f0d06080102070c0602 76
    0x1300c00007800c555000703202540c0040d010b00428001c42e0700c00f104c010202e002c10040b81310184500143e1b000340ca4004010201e0502c1081e030804040703440708082c00f091020440d21003400100000c159941c0d841c0500b0241e041c3e41440c0131203001c0840d40c1c0000340204140304003240341401c2002c00e800a00030f5036240c4400c400d030003504860060044e44403c0040026152094003242c00a5441c1451490420414040c2007c605161000d98030240c00103004c0080d4202000b103018104101e1404501c81800d690b030b28070210241d9000f10388100e401088240603c64201c0444501c0c9081c2c000300d4200750f035240b411b221b41000c50105c9501c00d009620001d4102d403218018100e84900c141d580b800800500281c0c0e50b56854034000506090368201c801070b00040551054402c11100c02059000441442c2401490456080d113441c0c440d03410510208050b4852800761401d59610015151304c0c0d604d00e0403407042502484200400349801d04c100013601200c1276008000d0b01e80528242000d02e510b4600a980d = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 468206717 1250 468205467 468205471
    0x140106030c320703050f0d02281d0301020c0f010e010c080c0301030f11031b030c06070c0b0c1212060a0b0408060f06010951030c140403030521 63
    0x303042000050094890302d9030010001a0b101e414414100a0045900740c20740c0c0141540c11406640015801c401410340304418441c8a54070610f640705811034003004044403010100e81030311a00901185903c0c1e5800c0d0162040c05a030f40044500c9a410201050b000e40306403051480594649091413031141e209151091151441e00241480c591a503590b08401500b40a420347e011070000c0d5403148156018004225031050a407070701e00001415004041c104030800380c3d010301c542d0003000b940002800e103107008801c48120703c22280d01c0e92643c0e1440b40c144010408100d001c07071000904442e4001380e5000d158007800e02039442c00f03000f40c0c4070556450540302d50f0250074880e5020000080762800707600309196105006140c4500015901c210041c000c5010000700b804508448042002c440c8031034807648001190b0203416003048846078600c1070b6100c0c00005410805403140c00301c2c1c00250040e025081400304206403150f54a03038a04004040b9000351080550114031000c03441592504039901c18 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 468207967 1250 468206717 468206777
    0xb090a031d030c0406080105040309080c03250b0309030c0106050a05150310050306010801020408010f0606140d1401090c02010e010e06010b0c011103010b091009030302070605030a140106030c 84
    0x4509000082003000030507a003040342d4584500c0d0030089607525180280c0d0010000e08002007200d043c945070152460442c3d800c094182c0e4040c441e808040d541c00184e00c0e410302d50711400386640c15402407500030400350a401901ca0b0310b100005100003120300000920710020040000c201c520340790320820020440c6132103038a900c20b0070f811032140501c00a100079608511080c1c0b0404080390b0351404241460b400f64072045c1180d60103c1e003041000004c3c0107903440f6030650001001518104400904804407171010903c4d0040f01290407008070800d64060091322043e10500c80b130942e510034030343c4041c164811034040154245a071f40140d01005000d80d1044030710100c0940216802d00c03032480703425001045081034a640b50045e01000d190300c10002c501910300005ea107640d40c49981c09003c4006091541e15041111118003000429408101d441c15510585802a0b07641c40b00d00c0d1900140101204140f246540c000c0002043e54040e0712803c140e50710350301c40341003d40c1030030412107824404441607 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 468209217 1250 468207967 468207977
    0xb0f04150209060c0f1f051b030c0f07060b0a060c030212030603070f120b0c07050c040b0607051b13020906090402070305040e010f210305071b050310090b090a03 71
    0xe8240e04160041d00d54424054103150519140801052404c1c81c0200072017901d40080c1c0b034000c0c00000d60000c4901242c1d81c088203002c141801a0b0b0244200403489010302d0500021000c00c0e200c40b007140864104e2001024901d4540b01c980c1080340003807000c095174502c5042c40c1040002c0d5607000d03220000c50140c040d0007500c0c01d00286c034883c12155100a0000e5810301856001080700100a64a00c0c003402c02104003c81003000c0d450254001c00015001c0b0000e0b1405001010004d0000900c00400403410740f00031915011401c00301d009406811b1000f410381c0100170074170122021300750000021420882d2654940c45c048a2000f049108a81c11035812510401c4005060b0429400030031070140710345400c5141c40d80c0d903503c1d8040030400b80c01c00350ba8110004c10401c180d0b1440061882000c240d1842d02949001c259405400c2e07106e002401080c810400200d0381881c0c401c448010010000038040d1118145014440b20050201e190122211090314000c2001110f0016440c0d050503455210 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 468210467 1250 468209217 468209243
    0x412080f071b02010e0301020a11390117070201051e10050108040807051c020106080102040b040e040c03020307090b120d020618191a06040c12110c0105090a0b0f04 72
    0x22a40040b51510000d905202901c5ca42e1981900c0910040248400b20b6840254062007912243e0410b480b031460204c48490146800d42d2040c6c42a03010310310b940c52991548000ca0562006880010880303201080a850520821035666019000b0030b03c00d01d20f1141248209410100325080b000b0143c031038000c80c6584410034012540140ca04540050042c0e0000c3e0030300c250f80d50b581d464101a0701c00d010102c81440c42e1040c11036024014403002d002c41e01d0007075003002c1c1860215000c900603881611120400c0340701080910010f0319003c000b03140c0280c259044c4544803803c2c003000d0101035002a00892101c002780b10341c4c3c000803c07200f02806055000d080251200a000c40e4000b5120110303000d6801341400544071000303000b61400030036101d0040625141c0301e803c02c005c5032030300061500380141c0c00d00052003050f91340311040c031110500c618000240b030a1b20a018001c0d44c0512100c8886540c689010301103a0400054281c2e0005c1c4500312511103552144000d0341501001d5030010010520802 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 468211717 1250 468210467 468210497
    0x14060607060e030325140a0c060b030601090c230d0519091101030e03031b0f1303080d0c140f03180a06050708060301021c091a0412080f07 61
    0x28420385004401c0480e4444080801a04640c010b0311180041030b103039198640380c0102e11070341c1c160818050034034030001884800000b00c075105206903d0200441c00c44000d0410a91b40e0003441c100e00d01908071050f541c0c581e22484014840f009030000425908010304505540b80420b0303880c560f1014184038108120207160b60046c041c0900364000a41101c0148407011690b48100b00c0b10364041d28004c1b01e404d07081c00024084803e0504071241e15041041084119040c40300d61804040388625080d41c3c0c0c98100003080c0c40340c0a41070343d0310001500c84400105004481e00508845600340c48108220100400183c0fa00d040c4080440640c04041c00b001c1d03000c100110103198440b02c03202034107084400c00b60130603060450114003191180c0d510010b0284a0354400e10319036000d081034000310b16100408404010714102c000b907400300240c4654041040059840050610340110b000c448805d040034070348049040e00c000120800181a5130010302c3c0d9202080c40a40150250307201c003200088454 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 468212967 1250 468211717 468211729
    0x1c1e020a0c080a1b0302030702011205130f06150e0402040b0a26010204030b07021e07060903080c010e030a0203190305040308040b0a0e0303070201060504060e1e090115060e040f1406 80
    0x607129800b0b1020845900f01d2407103985515541301c501c603a001e141e03950750324030014200e0000900e108400900d0001003040b03280f400c10b0710440042d0441d00d0000701e4012450a03001400c070200c90340000300321214000803080c0c208100303180180c0c400c4409204d20441c01d410b2150a0b402481a0103002c02201202c54050328114107201c24000110005450140c9035111a54000004d64080c0d0040e406140b1b100e01d29024451824111812040a000441d10380480100007500b03a0201800411000500c103582040035071011722543c0d402c50541e031f00d540161402a441e40c02c45110040706184c03085192840074032921400341301e5503041d00c0391000794035151207800c6078810041420716035030341c4c0b10501d5090320310800c00340d44a840e20340d0002c5070883c2400207010645406a00002000c0b0203401400a44044010070848600c044245102d4642e122013259024003c04240d106081280f6900031803029030103250350203050b101351018401d9000b91512882220030041c00c40001c800700b10046016454a8 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 468214217 1250 468212967 468212977
    0x522080a0c083c3406023f04030b010e0f010b0a1101091118060906042a05040f050904030903110f040f02031509040302060a0902061c1e020a0c08 64
    0x2a02e82204075642608107035180c1804c0d101001c5601c41304400b184044042090980c0603602c03c0c1406a01e0720740b4084010707580301d499100c1601c0c2ca1a020b00060500619400803118a20b1050300311500c80070142c500540b154080d00007505e4400d0000c0001c50b80d884003080396805040c04401307605070360f0b1803c0111100f07600401225802c2003140d0b03e0a917203107002409141d14860103640414103802912013002034483d02400310380d0750380c102031003001110f07541c10340065400b810540703011501c0000242b40c20750a908011400c1d401400350846011080d5112001d401038410740c00c0000e03a941d454004025100008460090004070a114188002201c0780c401e0400110080c0c02007036000f10400c00a0706640c0440700d0b0f00c40302c69021041218410116808025986041d91840ca4500703033510001c0d00c940300206141d5081341c480c100b05045480708422500d081c00240c0d100c0d60401018810700f0082c00c01c050b14001080400500025441154070895500304459222200d400740c00e960307024050340003 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 468215467 1250 468214217 468214303
    0xb0d0b071206030b0f061e031203040c0e1f09060305030a140d020a1707030507051b10020307020105060922060e120a0c0c0b0405060a0522080a0c08 65
    0xc981c0d00100003285000228050081d16612510030b1600c4018841440031107d05201603514002000030303962804a0003449000051100b00c3c6d80390b0341c9080c9501d03040300c01d1b030040e407101c05080c0802070021070540c2c0c0c03818460345580b1201340c03155681c00c80c9000d80340a40001b42c5141c0003081110000b9014500300128404d81c92011410b00c4202072040c070880c2c008038034400104040c60490b42d49400700d0f2a0099124206046c20807850800a400801c030f8041c441c3c40400150680f92001d1690300b00b08401603101ca03196074295900e24003450001c0c040d11042d43c5c928002c60300e4401048103000c1294500340ca20321103411780541014141c460001030240c01084110303502500c1c000d0843c00c81d44000070f00c3d02d11180d88925a1000c91483c089144554540c010034a02105020501841e42c03842c3c2140c3c10341e0b00d903107031a81d01c0c2e203500e520040c9003185c00c0003d0714030185034502c005480380000c0b40d05c541441c050741d03401000e243c0d00c103501502d43c0900c15515030802c400047e9503100940342d04018154002c = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 468216717 1250 468215467 468215471
    0x8150a0e09030408060903040605091201060e01090207120804200406081023010503100b040f06080d030e030903031209100507050319020702012f06010e01090b0d0b0712 74
    0x158a003020032620106444001c00e41e08001814401c0500400c401500506450020b40c5042e1510714024028000d40440070705c40c201d03448074864101401d42021014242d40c4100740265652800c0300c0009500844089804001c04800000320501416520340f16940107403100588880145068011250741040c9a5001e0381c1d43c0404503188004018110420582100024101044005642c4a80c00341c1100301181e41d08040144981e440105952082c00300c0b0203004100902d2480001d005051903072880354640b031902500184028001030b0001606185480c00c00c0418040100030b6224447e2561854043e07008001e0402c00c46c40108140c0c0d441458002500c800c10b12428881081e94070580380c03070f0000341000c4280720480c0110300500b03030003020050003180b50501541c006001040400140321a0304aa4903082c1d00f0500c10090940400e561082074444942e15659001d400f04800e01a00d090b0b103240010700c080e00e003040002986a1500b00c005202c0994544100700c84010000c40c0c50806a6 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 468217967 1250 468216717 468216719
    0x305071d03030f0316171509070302091e090703020a1409010311030a0c08160c140c0409030801181103010902250b040209072322060203030f0f060108150a 68
    0x20b07040c0001e140201003000307117500382c0d20f48020002d000c4816001c1540d00b00340d11805110400d110005480e00c0380406544040495480242c168001d02406440f030350440200400c1102100200c243c02e00449001c807440802070b20380b030300700320100e000b0440f000021400c180390780300313107a604d19011344207602d414540400e42e990441400485604240e40705944961200e070070041194115440e5588031245a241e01000e8900210041281440420140c003da032041c151310401041480240c40e0307442c001d00309005948103803600400d203802c2440342a80000e15050582400b107114003d604180505541d02c600356402e0410741c900035030010036014150304643c8001d03030140a41000d0b01c14440c3c041c0b60000d1a5162500602524400040c00700c0c0030001580c148074008a48000d2030800182d0201c10240c4924505c00311b000d10340d91504110902d0141c0b0745000030001c0e4004004c5114070a443c0e40e00b18180c8503100e0b0105210702c241c680d00c4c0851115000240302a86110b031a8100c9680141804481c03 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 468219217 1250 468217967 468217987
    0x20402071704030c2c07020a0b010b040305010e061b0310050d06090b130803070309030c05010f150602070501050403020f0121230108061612020a1e0305071d0303 71
    0x1901c1001511241428081000c0040c8a508031088000b082401c2000f00c1c00c400643c02442c5900040030220441d440000c081001140308101c1440c403258007104a220558480003d52503d820600c0119420760a0051240325224082600c0d1301886451800c0030150780c0508071050075800040c604201c2010200001400355500e21040c2d1566001f030400203241c0c1300905103020f040e00014003110806d048404284005904801200e070b22054618001900c0d1100c0d2404685190003440090400e600b040d4200d03400c3d040a511003120700b101c44030104550381d038921003640c8074a280d2041030301180c01840108094105088004101d1030145880c1114030b4002c0d54800340d45403191540c00300141d03240390492841c16042c09170300b80c1c0001d45881c4a00c0303601d44003040d5506c120040492110340011502502020301541195a4000b059002075442c0c12080d4001080b45c41910303036240c0c12483e1a01c2000c0070900a218542c091006a501c040810a14180050600e500c00c8015074052000f00448024 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 468220467 1250 468219217 468219233
    0x9090b0604091442060f04020f07050105010501092403020d18030207081b090a09030e0604080c0a0605040b0a1107080d02030306040f050121050c040c05030f013002040207 75
    0x400109100d100038106031a48100381071013402843e41540040c04c00444500341610265540444101d481d04d034a112004c1c041406800703680c02c00b1200d110040340c188200401900100d050324400e0f81c4038001256100c0c0190128a00c0120440705120503c111710500c40c441c2d0005c1c01d08500000c0e0201e5401e5194080411040f00540140c0040e04000e00074003041c3c5051100b2059014403060030400c1050400020310990300140c502d071412551540b81c603040600814032034591200003003034107440d075a559440ca40c4800f0b488801c00d22503041050045407803030164060300d050721210f400190800040d400b0070b0320041004114a081c92140c0d240019400b0b00421070031601140681c00b81d80c0342e08000c030500044e07566058151703801c42d08010040c4465241d6a80c00344462241002146c200009401d0007401e10080c100d8194019040074041c0402c29000001107009222640e842103007aaa0f074064010034600911125407044070703182103015841210b82c2c141c1500f600007800180f07040107031fa80740e5035 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 468221717 1250 468220467 468220483
    0xc0315030a0c23010201020a091205070e1e01060503100e10090507031d0c010c12030e070b09011d013f060512120d11070203010e01021309090b06040914 67
    0x22046200341092811080d840320f4110490700a000940c2024981d1101418912140c0951f100040300d440168013400010401c000c028865910848224280140380c6600f402c2103a9846403c0d9a0060000480c2c902c120100c1b4070400c1d42051700c038002070a101c0c1c01618407101404440301d114040c0c001040d6902c1303900c201c0d40038070155100080e07040b403c0344019a490200305c0640744a604400d100325801e9800c5030210940584c008007003403407019140000d030003e000f00035210055100c3d0a00100355450318000900e01d41c60300740c03103080540070141c0e0b404070601d143c18855800188002200100c2182030164280c0e501400307144801c880c118145e41b000c06400304c0c0100c6600c15210342003004241845444240160a0140600020395207001c0d801c6951241c0010741c0b03400d980e2001d0341c9202400180a4940c0164018000c1c0b1560360700c0c40e000c50207500710070300c51001000714880c002340700e03602407081e08003441e8040000c01e0142e88150401004180d04082902d44a1220200304621402030001d11 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 468222967 1250 468221717 468221729
    0x180109141c090b12180307120311070507172803091502060f1509040501060314010605130f1b090305011d1009031101091103010c02060c0315030a0c 65
    0x16421040c14814038450301800e90340e4003480342c410b1052010076008812900e409000d000101e80c0794481001199a595182111034558000442c0d10000c120342400721180071462035030144801102003a004107180700d1940c008000c0c0e030040c803040000f00c4400c5ca04036080c03840141541c0251503c0c2e2641500102c4600301e1500300d07075411081804158000785180003508091402d10101141c042000e9502da0f0051300f0300587c51722460000e140c50b44600e40356401c2c51000340508130b95003800e1030031a000e00241d010445004000184600400070144201c0c400c07604010402c00d90810341c050200010b004603160000481e4680c840648607101c01e074101004020b9682d5000780e80e900c1c0d41082c070f0071038142c00d42c0c1642680a40308041139000000070100e41c034201052000031101c0d40c40c81c068484c283c0350003507007255509041020703080c0b00140600015940d010ba00900c00300102a0b800c98940d40203c0d201300d80c0d00c0c4140041501c0001512001104d0280a01107400c1c50100d61120701034003030907500003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 468224217 1250 468222967 468222973
    0xf04030f050f030f071b0f06021e01150509040807020a060903060b06120c0d090506011202030c0a1d15040f0b2707050c070e04030e03120a0818010914 66
    0x49030030854100300c1c0c1040c00305440041c5041000c0000100b44030b118070134000c0c00b56043c400c0c8000c0341c0d0310042c1c00b21000740800c0064034852070752004045d440703c100b400f0040c55422406641d10b0444018010001c140003c003140740851420001007204409000d0700c250790b0034005005200c01030321030700c1c1050083c4ca42502c44290051031460240c00b0f07030f91840103e40c011941844050b9071000741040540e000088a14226200c0d50000018801002800405841031051000018603802c03070f01d0709405c02e20700030360565a00d18034980600042c1c0f4610301c1507d8081000d043c031984d01e103a00c1c0940a40298841c118101e0400e40180001c069840f0b5403440f03668a6902d0f01c45c0003072840c242c00307800300425818400000c00300003800e241c0c004410051004003400741c0060000182c410500c0240064050188001240d0406084c01420788024000c0c40c1d00034441d9102c0040c0c01d03180e08055602250640e030741c01150b90703201c00c0112611a00c00f41c0e03000642d0340f0782c00d400300020b40203020380c01d00c00c41c06001 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 468225467 1250 468224217 468224243
    0x1031212060308221a040b0702120d031d03030f1602070807031b08060609010b0a0306031a10081603060c111b09070c02033703080a1b0509040902060f0403 68
    0x72541901c892540600ca030882c0c00c0e00302c0720045c01c502c0d0681741182c0700b00c80c00c65201c8400d40040b508a02d4010f465040360b00a1000101e402e54040e030020150a03003540040c9000100350940642ea4032044c1d86802c0c00510000004003210813224000e64001d060b4410768202946e10060545418101e400495841c01c100500c044070b0455480028000d16102c0001c1c000d41c1800d0021840c104418020b08008120026070000c0c054001e070410743c010f42d0b010851400d90105066010981501502c40c20100ca0886100080744403001622014503a44c04100720200c514590340c0100620896000d282030041245060800e49800d02c6550f412a03002c0401002e100c4008007084140c09005041d14140450358000c3c0d40581c80010742c446040f00c2152160013040360316602c880241340c0c1c08150704c194044000e284170405500000b145e001e444021018010b04207450283c428450841051500140303003400f80c0c1002d4581500078100c1c05001501003440d2216075141842c0b550f0140d042a20700014503e8 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 468226717 1250 468225467 468225517
    0x7021804051e030d0c0c08130e100e2e0306091703061806190e040c050405010609090f060302121b0103060e07120e0303100e0c0a1b05030c1006080105070801031212060308 75
    0x982d07243e021034140140709025080c28814000e2f40e6020341801411b40715001c03c481448050000044030060a0f940d011140340d40b0302c1d0800150241c200d007280e850710134075061081e400152080c0c0b4000c0c4801406401c01c0350303002c0b0107600f60000040c0715682c0301c025900c0e00407210000c2d0414501404d0316880607813041c034203410f02c0100c0100da41e220b00e0246240000401001b50300010603004d803020800040f444a540d42d142c40060081d5405c00313548607036000d81e00c2c4543c0c03100046545800c80102c582080740715245005501b03c54403482031400b20502c18001510092007040c00002c24102101c0001d0794481d446400c6245400446070b000c001d04a0400c00d00c1a080718501e80e0703520001185000789404065200101940031038401d0301c0010424200d0b001c2000700500c1502c80c6a00690b045603c0940caa08505016101500c6031034059440c00e0041030340e26215181050603250400540d10150350500412105203280c0c00922a820f6590400440058000c00062950000d03140c18580c099801c60 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 468227967 1250 468226717 468226739
    0xa120317071b03030b030d0c0b0a0612030809031308101a0d0206070206120a020d0c020d1e031409012301120201050a0507021804051e030d0c0c0813 65
    0x1108214401030386104105249900c8500c2c03000c4404840310340800344140c2d00d8141c016200390114541e16000f0700004c10300700d17079105818140041c01032002000fa500c0d02c0017808104e40b503d010760313844016070803070920201e0b0140600f10b030006224001c80745002242d000165a103145034020380d819401003915880c154034140141510120020440300710b99a60000040140480103002405240d010034444155900c00081d20002a9072850301e90f66441c1202020000750b20070b24a00200c989031044007215188001005485103101c0c1e121004040b41ca8140403060b840da0104240400d503e030074040c05000420340c0c00b140550300250021500c265400341d510b07203888440207404080c4803440010480a00c4010100014540a007005c81e81d4583d80c1030100e1302d0744507461000c1d4101ca2101c0c4210b2890340705d041282d108601401c00d807400c0005840c040741f101d521582c00408560300a1054903075800c100d9000c604034000d070341410015403a166032041c8854101c0c100240f9040403108042203681e84036 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 468229217 1250 468227967 468227987
    0x30501030303053402010e0f030406020d140702091906062105060604120804050d140f011104140d050a0305070b010b130e0613060b070302151b0304050c0a1203 70
    0x4441d18086a0340101d42ca041101324660000c00300994007101510644e000394025040c0d441c08006660062a0305006c1541c1c0782d1241c420500180704150316044440e101d40b6601e0a00c4200810b0203142104540800c102801d001c0e10000004603120310002c103102c018858100102000e40b50200305a6004100d0480b030784403112098401801d240400c940d40d55030504075011313114884039051443c916070a1503031160185400641c1c0250704004101705010200c60740040501b00881203070100146120282d090302c52509143c00511000c0c40140280488401c04400f00031003d00101108101500d607a0302e029007180003600460000140c1100b801501c80303866005d800910082c038540103026030000c04c0c021039032040c2041500e0860108034507558041c0840c024628044007441002c2c0c5521002e00b85600c108400c8015109a8402101c0001010802c0d40b0405107880001014584000300003015440100111464000d5802d0034030b10755503031460000544030b40c02c140320111074685805010f0440c0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 468230467 1250 468229217 468229231
    0xa05191509180503040b0c010f050103320d0c03020c09331302070f1202030315010801050609061c0e0d0905030102120412020a05072405040e0a020f040b0a03050103030305 75
    0x2e6403a6034010820000454040b503000320b0300c803960341203400c00b442c0c0145410f005e0b810720702c0c0c02c01000005000400c020b03003031004001c2c25010300900049810040070f030308070304000d1800d800144c00f031580540910882680b5500070300680700ca250f6101d0000d40408021220408d0402007008207048045c000401480202041e90301d989544668100040e0b080740310009042c4400e80018155042260b0000d10307884807680101010b0002d9169407019450740c00484a8400043d202c1400d50703850340c801e104450403200087c003840c0c03802d038140c030a00c142e40e44140e11050141343e40c00c015405030112449900040d9000e0b00103445210781040004007407079030310380c800d910aa00501c904400700c10441040ca410550118070b02d445c16244003010703804c1c4150707414044e12038040c2c880c0000b909c1c1910001000f0010310658040e001000c0a2815501c034000c5d805080c0d540c038102400110011556401000188203111059007007907a560311000050340718804400000c2c1c0c482c8010810960103005013034010342 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 468231717 1250 468230467 468230501
    0x20429031308070f1208090c0d0f26040b040509010e0c12040c12030203031503070303171506070501090605060604080a0312020d0504030206220b0a05191509 69
    0x6100340c106451611021025203264000190f141c1040408a421105198000145402d80000c003402a1800f441182c0c2d4079800d008030a01c0e07000700e1502e50078619071079501c80480103010019868030121160560040c900c13a65542e080f4041d14105000500010072580c000e26954074144020300000300c0303040e80325000302103000d001c9c0f1100035106c030140e0740c60200f0960b40d102c042d03440e810f05c0392000816500c000e520f41d080c010070006240d4040011407103201c001c25010700c411803000034543d40f029180700240008a00b04072004441294a4405400103100a40d4400c60600c2000252040d885281d0448a0b0b83d03580d656902048468002e45070b1251007200c140c1c8c00d01c0d1820031890740310310310031038020100001102c1030b0400700c1c0c441d030550700c840780d1a001c10400ca03e09450003943e224001c2c3c0b941c5180301e00c84600d80d413105c00e500c0044c00140e58041c100b101c294544411240140c540901203c070345100c01c44070f0b00010388180c4100c51803c16981400886a860300102e40700b11a2000001710204c0c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 468232967 1250 468231717 468231721
    0x806190b0f1e13090b010e01060f1101110310030605070c0203030a21050c07170f0a1b0f0c0609170a020607020d0c0f03060c020c0f0907030f02042903 66
    0x1560701c0d03024100c5101c05440b10308020125946061030100d440c0031050f0b000004a000750714520782c9500004a0a218a1003c65180d0701c1700350410601a09105103000580d08800131b030b03d680c0c8075071007041009030218004074600f281c0ea1408840d0760021a07501c1020650301d20100107006040c02129005141800c03c0348004a16030040394483c400c0410f8001440a840c1c01465515039000240d050700c41c0c020f01c104081d00b017100146c1d07100e034407038081901d8410302d60364044480042501210702003a100b07081d1518100c01d0380c0e0292480358171070700075540041a0071184004242000e00d401141446804d80075619424084c01070400d51b842e811046903841721142481145500003500100240c0444005445411a200041e503081d80e01d14000d1080c1c20070f06000071000030034410381041c0c900c503203414400c5001040382203a4801c106414140d00c2a03048286030018200a115141c018400d0700c2c0101e41102a01030703260a9a000d44d2003c12000031205010032282074918841d110050607024081c614 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 468234217 1250 468232967 468232969
    0x60305041a1015140d0213060503101a1204030f080108150103080d15081621060c0509100915020f07090c09030605150a0509090d050f130806190b 64
    0x3040b054003a04100c103840588210145005030500e5290086808007079580300c19000924000e9003144414200003480f80001103803190050007a0b0713103d00406600e45285514103080703440b4134003421211070000c01d0108120b02040080d4010a4400c5010b170701c0d0b230007800c038183c013000b8134049050b409001380d50010700d01c010f28803201d903c480b8112a00011540d803a141905100030041c9242d403000e1111034080c5e10002418030003c60f59072525a1280106041d0341e43e98080309a0050b0303407440c507015441e1640990030000e071f0b0a134084101ea03e0b503441c102e4102a003041c003140b11210002000d03070125401d0b075810441074001004064003103010344003400740c0c1d41c9003052182c3c0d50400750280c1c2c1404c58907804803040c0300b13104425600007075170040130034442820140a01180741c801000a54060307010141c02180600b46580310600619202c0c00400080e01c410000703c6040d081400d612410030720805c855001c0002d40d1080d8406481a080501a0350400f40103d40c900000040d02280c0581041100446 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 468235467 1250 468234217 468234241
    0x20c0705010201060503031206031501060801031101020705130207032f0f030f030412050d021222050d1805090411130c020c121c050a030b0a18020f0d0501060305041a 73
    0x407034020023540000c0e588808000905001e01007950310441c00000c000029a00d90104049049a0080e02c5084244201e04012616050f060140b0b035082110203580804030360103a0b004000081c02890030003006010070342d0700f040c00b040082201d490800980410706160a041c084585e00c0c9107148000c510304a9140c8815103540402040582500a082d580062442c0a01c0403200d01409000c8110340d10600750030030025002d000d0700d20b804580304121000600c12607001012441c1c603006001441c00d4207004008598400010648000703003101e5020003c0e041c0c456000d054040c40c46410040040f000e51818803210000071181101103a0608041d0307185c01c0e40210300007004c0741081e2980806c40d00d41241051030028000645248070004c120201030044c1e01501400803821075a60a011300c0307125000b0040c003945540100c5000f45041e4484c5408a201603000300001224207840f2805c2600641c00801111400d07031082c00030986600c20032080000c4180244107001c80901940030a0510780e4056031 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 468236717 1250 468235467 468235477
    0x9100c151116050d110a05100c02070f080a05150411010c020409080c061f03080412050a08030103050106050103140702060403030e0c030f0a06060918060c17010603020c070501020106050303 83
    0x16800e55507414490300540c100701210030b81c1c010711241c445842007600e440d56540b034000f81e41c1d4000030814500280c2c80040466100203464100e001004c00d101c070f89034181c0040001c0c402070020761242c5c560004400500441c50001080f040003e081022801d003020303030030644054020460300200b0030401000500280c041040440d003840c019034160717403520102c4e00500312010003512846020644403900300b80021214890844509645040d004a022003104010369010062486809000034402c8094140a40314098002c100700ca060b0050740c1c40b0741e00346038020f1300169426512014107100550b018021000d00d1500415800203030700e40041b000351100400f030801070401d0344454030071212140812a02c0385000c001415182400b0450b0210b9644051002044a0040c2000750005a80b0164030801c0f0198450040e80080c0130b48031340e17400d00101001c0c44204180104a03016041c0c150042c0101c07030284c00b60b51001681c5094200c6e40e14944030050307028904580c10188240700a41340402665 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 468237967 1250 468236717 468236753
    0x25030614060a02150a14040809030d0f05120c04050a0807080606010c03080105090415020a0f03050c0307020a2a09020337200309010c091d010b1c060b09100c 69
    0x4540c0d12403c1450011304101c0000103200c06c0c00c11306000038070003100010184800210201d841d02c210509042e510720106040140100d44240b100c0d07581d000c0c0300c0f01600c1d4411420409607161980f100300040407910700e070b040a82e06502144050003440c0342007050a41162003402d0000002d40642c2d4010900c54050240902880822004c5010030012114bc1c03450100c5d174000175516080705950040071030707800c03084480009080201107107996045104890041c10564054191211a503c0b100780481c0781a00d5840c01070b80d5540c00e103650031b0130a80280c000c0c02c3d000001590b03a0801c0c0301c41c45901003800d42c40c507801091a400c3d01c3c8a85408444004c41410340c200041050180380c403160303840e0f00c005514041c41c01c2c030001c01c0141007403065102409144064458600341d0303445a800344c40e02c5121100e0040c1540030540140010b0010602400b491035440602d10350700d040020304201030354401e50040940c0600481c88910b2450210141400c042d61403030030304441400358450000408103003e9034 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 468239217 1250 468237967 468238003
    0x3020a020307061d070f081b1c030309140d0906120902030a0506061504060504030b10081e060702030a0e0409020303071b0306200a030525030614060a02 67
    0x54514024000e40c0c0102e41c01c408104802d080700d0405441030300c9082d10342c000314056540e01040c06021840a0f4098844100c0203001c000101d0307444c2c000e00c94001120990100c41400035186440081e0900c02c24144666000f10301d18030f05151588020011204135045500240c0c2e500c10860b62200b10740c01103400302e1901c00b130703000e0350644801d00402881c0000794050140100c1041800300016000d4001d0360b00740c880200c00003000d1500f2006000c3c0d0700400c0001641080308102050038804180d4109cac51340180c680c1c0440e07079030240c5440d01003103100850411106800c0303d0402001848a5540608180042c40c60b04003003d5000f0462040000c1c02441a80d5030440305042d0f4800b0005c2d1031009034401e40305c5841c101000b12820f40303001c0c00d204c1100c015003841014103910303583c0c90351a8003c100e1240201e0604203074600039405845d0040420450392840c4400c4441c25412030062082d0240a0b180018020b040c40d000e003150800304042036000310710820440c00b01550000b80306100c0c5d0303034aa0348 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 468240467 1250 468239217 468239227
    0x2060a18090603051609110d0209040b040f0b011103031b0c030d0617160e010504052a0d050a180209040303060b030a0c0f300b10021606021504030302 66
    0x2440385510950300481c40d040c0c50060040f08100c1e0014410704060f460b00c80117003441360365401c5c3c0c1040e01c82d09140c0050104080c85040d000701c1080d0090101980010004550084610f0114040710750400000c1b84444d258102c14841d035800c0250240c106032108065441d520705120141200211201e910818010000d03510329207140920540300801a42d880500c8081e5031150151429802d00402c0b04560180d40250701c2c3d100744c1740e03524070116041c40304c02200c3c0d43c0c6810300700001000020801c06c034500c0c0103c80c204075100c903180d40303078289081c0d0020b09880d5a40202c0c40f0045030ba00603d4264483d1514440b00d55100c031300510484010b6040302c0c222003075a1107290881c05000e01ea4841501c40902009010100a00e42c0200f44980d0300f681e5241004001d03000101c1e4048104088888800405503141c100c0c1a1209003032032150500c9603020a1100d1804041200d0760f031002d11000c016042140000c0d50120b0040054000b410984003c18800380b0620350b138244002c0280004080c56070001e4 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 468241717 1250 468240467 468240497
    0xa150b01091a09030a08040f260601090b01021006030318140d0b09030d0509060a110306010e040e030f04140907080717070e060a0f1e0504030b06041e0912050702060a 73
    0x5c03441c462241d0001300f1588541d42d074203030740b03e50030018000d024880404240c0141da04281500310f02d10003144800030204c9900c2e0104a000500c68070044d281140124004048004900c0c056100114481d40d602200a56840f405444075a285c0d0054600d214140888000c0741d51140c03015882940c008000941c01d071507512030145140720341010748042c0d40c2460700300714509801007400b130300c11180c0c1c00c820f02001e1121141100d482c4000c036002408904160001c1d400c60505034442440540d50400b01c9240078485032011200790010351124611041d00c040008050034104051500401036050000d0349003406140a000c2100582c03403404450b1255001850442c801c1d1112241c2a201400701c96590100040c02040b8140140f9007002064800042c4441820154030745c02c000846540c0d00d900382030030b65903413800111001e410300380e20540310740400d010b602c00c2c00043c9034051103d00d03000688080300e2500741c03500100e94040d1801e00900340080005612508104c0c1c0348104645051400d00101c41 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 468242967 1250 468241717 468241723
    0x30711011b030801050411160b060310021c0e03040302150f0d05010905090106080f07050108090c1507030e0f0901170a0602131e030c15110a150b01091a0903 69
    0x41e16048400303440c048024103140d0407030041d60690b401030300c0a12000040801e10740311131040c080d4218030900c0b601900e80101e4225900310390091001015036032115032815034041640c00c10300c4062540b02014900c2c2d2003d040721b10505900c8421070000d141080c2c03440e0005500d035510010780f00c40c100c00c00210740398829154011070303034402c0312074400300000d584030384500b00140421a1412141d40ca00700300414281400207001c01c2d89140701d401424510b08240c0119008040a4460b04241c400c42c1d00085640d9174144079500104000c07541c264950740241030080804801d0f040090203600c030058040c1032030300c8285040d030541388010301410204061240c0e081c130b40311030844c0141a5030301c04a5800e014003032000300c2104843c010542880540211840c02241070010320005001d100060f508114918114120002e4200c0d039080a0780c1482648400c0b80c20300580704401c9035541c00d0058100c10110b40c030b11a4141a107820310f0444261401e00759100b1180702c008501e041030030380100d5050601d49c0e00f0 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 468244217 1250 468242967 468242987
    0xf0609040f08030c03041a010302030619150308281209020f0a0b041401030b09180f031606050f27010b1525120f0c08070507051201060803071101 64
    0x202c10119540c0c58805000380302c42e0030940307044030f10943c00406207441d10501141541a690010007921007034590800710030f6030025510401c0c4800b620f5481c0300229400340815980114010001d041e9030b0100000a4840c1202140c6103156900b2000a4211006c1c0c1c000d0380f60b02202c401e00303400036600d040e40c000600e1282c050800642e10030b0a01401007600c1820700090011179802003082c2d800d503d4a0401501a195504005034000d605640000c100e0f00d030644540480c20000c00c16950050949880c0368150383c4800000d00440d4a1034050804001107131040a500c0710b6402d002c00c1880c01c01f00201080130082120303801c59081002e115041441080d0f1001400c020300074101c0180d1115104550002e40101c0c07254040d02e91802e0b2a0150f500d034001c00c10740c407a54050100c50700030b1843d0750203882849066802904100788542e04000040e040c070014209031703002c7d9004100032841c19041003600744440d680d80c6110f034103000c41004849800400e0310030301a440b00c5400d00d15042400120303440410 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 468245467 1250 468244217 468244223
    0x1703071110060302120102070503121b0307050c0c0406030201050304020118080a050a0209010e130b04060906020726090120121b06070513060c0f060e0f0609060f0609040f 75
    0x590141d085441c01241d0200d01280d03c02d548107444820200c1680c3c1c00c070700813104013030300e59007041113005040c031030382e034440b071f6006c81c2c140d034641c02000c040501c0a2503a0401c85032034011410001e10110110710802c4a030b021424212070600146046a000820718080540000d040c009254400100b2100c0024a0b1001c5d150142c02c0728100300103424102c4d55091035442c240c0c0a9040c5400100b001c1c0e0b22121414030170384031618000c800440541d90441c5111004005a45650391100030303600140382070000300300c10f500548082040d096040c0c01444411410741485072200c00c03c2002588503600484840c6c00a1b6030b01c0c003460030b4010f02d810543d042c00014441e6014140001aa0b40f0b071102e8400780201c100405d201c1121b216584d045000c2e170340c3c0e21072180044000284184100141441030b003003400c5080c454010313100d80056590394801519004e1201c69415000702405031030786141003190030344c000e4540e4000d11241c00d00c90070005000d8000741c4482d0040030110001010b114504d1189240154 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 468246717 1250 468245467 468245473
    0x60309150709090e010e1906060b070b040614151c0c06050304170a090b07020f09040b070e090411090612060f2e26010906050f07020a17030711 63
    0x191201c8002c000500c54095004210700d0013849007900101403180b584060f80e04401000043d1001c880100004101c001c01c8a10700c0d190000171921203014009020711500c252203103449801c040c949007042d03464070201090342c00601d10810414450181c3c10b450240d0301550121040304014807040d030200d15048002d00581e181500c0092200d600c000214070541c0941c03620b5100680c0340420007514030a03551032000042000e5424019801040700400041d4030061198000d40740340070204009644c11201a034540d041344003003148944d005100030341901001c850701c0c140d504d0155980280000110341c0103000d1300500d4002021521003108940400031204201c2e08207103400c0541038110142100c19440060300003254942000421381102001000090400d00326410947c1841d175030411400305050400c0c4080204010fa00203100e0200304900640d0041901e1038000307403001031110b0140c15102190303c175091800100b071040c10a120481112601c150f641e895201084402c048d040380c503018980 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 468247967 1250 468246717 468246721
    0x9062f010623010905010906050715020904090f0c080c0112150806040b0915040812190e0307020f0a1203050f09041407021203012303030408150a05150a0506030915 72
    0x144282100903440b07826600c41e0042600c1d000111560a030900c0f07000d001c00c4051051200041c280e0611403000c0c12800d400504203403004000900b5100c1c0c00341c0640d095000c007072907001807004491401c1b02520100000340206801c01000800040c04200c031080c49641d58198460210701d4260103100501d00d4100304c42c600c0c00d1030308001543d114290b8a00c6180e00c03031007a0244490b91840c80d550b21076074201212a040c03001c0c0d0702166030074000040c10021419a94111000720110b107211712030400505000842e103680d010710500005400030800f49208480c3d060040010b4150a131600b201154985015034031091482548030280c00b414560940c010f003050882e021410300d01c503206204110941c200c85065001c8040744c509440203004008020440d4111100041c6580300200703091100a8116440d2030b548600e02405d1603c2e80504800364500d03401400381e882c2d0306001d050342042070071404c030f69003074101400031318008454482d0314000c0c900400010041403050280c0550aa564200d25990f4 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 468249217 1250 468247967 468248009
    0x9010c080f2b0501152c03120408061807210b0c0a020d0c0b06041d0609060f0709050109060f030b040f020913061a0310030c08010c09062f0106 63
    0x1081011000e07003540f86004000a995284001038413003402c00c0c2e8035070940e9074208001082c1a8920341740070b142d494419503611030080d01c0411040824041c0300a8003170302e80d410160014100007000d820250101c1003410080030300480030030680c007100c00d0401032035214040c0000010302021000c40c00ba01010345130013001845d0045800034511050141c0c00c1d500310050151050b107200e41c5141c030103018540458001039050400c0ea100c501000200100c020018404c4e41c449441d000003200e510b84241c000b44103001c40c20b403150140d182c024007142081c450039420100000c01000c00c40c8210810400d0414441c490107000e540585100c0c0703000380c82480b0050302d843c0400c0c0a0b511005c8000c3c081ca03601c05031012035100600c60503007610142e0b04402c0c0d40000d410340240050700040d05041024405110002c0010340507044803004028060020600c01c1c00880040e181180c2e5038070510511030354a00d03100743c1d45c0194540c42d00060500707620010024014881a00412007500325005090b1200d01c0f108034 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 468250467 1250 468249217 468249277
    0x140a05010204170a1a090c03060c040305150717070903020d1a1308090d03050c030a09050a090618090501150f05120313060e03031e03071409010c080f 66
    0x380d8192036840251500d000c194a907071507110150180110700461010354240170407544598001000c01c0446080350000c000107802c08030700351019608286d000804204000d018041d000c01d1400300c000242c214588040050002034292048803064a200307000655214010045140556000f07014080b081007985045403008000b04981c841c600d07040c0c3c00081e424100c40c041044d00e250f2081c485070074003801c00180b0a4000e519242142070010500403d4041001000507150921295940390481c0707281000b48042002071781c012440303245c103002003130041c0280341446100c4208089400504480f543c00c20034018000c0c6048001104031010f000070343c0655114500040d81d40803100f140c1c03c0c51a41c0001962882551110001da02d0014010041c0c2400381444001104006e000d0700c0c584810840084903141c031000c2c0484100c4000b0080c0200e4590000844001140c07500c80d640c541003040001800ca803c005000a01210000500c0d50300c0d2004202541d1a040c0035815000f9a107001c940754880c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 468251717 1250 468250467 468250469
    0xc0303050307120b0f060c010b0603090d0305010617160c0501020a0e01090518190b0a0f140414060d030903060203091e010209101409100809010c02011e0504140a05010204 75
    0x2420400100a064210b1088445100d0300921703440301e0007940000d104883c0c2001e030301a00d45550381c901a0020303803a000011880340361150080e00c1980001c18000d800c84806800050400c2080c8600d0b19544039100c03022608412036044214003040440c1d41264011120200202154004181c112055421000d408042d00090301c428050507220303003d1224800000300c134100c410b000000070800410a60848070480e100686011401e0300c004408521031044d030b5440002d02d47c0c0d07280b50401030003100d11802d41030742d4401c0350700780007400d180740803403202d6080900b00c544030b40c2503034800c0c100309030240c03079882d0040d60302c003e00307545900d4410003841e102d80c6216a003201c4903200c1d160300180c104061086564403c40104a940e8841030503d0840384035032402400304c01c0c0d8104012800303080e9030f0042000307003800384d540d668011440c003c041c15003541e841c0d003444019a81041101240c030501400001d909600100c00069159074a06001c600c0748042840002d841c018130080384180201034000300 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 468252967 1250 468251717 468251731
    0x390305040501090503060c041401050705030c0606010305130c300506090606010507080406050702220f0f020f0702060d0212042108010806060111010b06040b0705061608040f050a0c03030503 83
    0xb11915130b640e0249030712a2000c849850190078104801d004000800100f9051410185012420884941c0d182481c680c080176456001d90b0016080000301d6074503000d45540040c6030300600c0c40401c01c1d035558124510380360059007080e0301d8a40001c0305004006210031151603541441007803495041c1000c40c5c8900c0246c400d28994010381c0000b4034070f540900200e0340e0490b80504010700d043c2c036001c012502900001001c0ba4405403a80110380400c00322140c02c14083c031101000180c0b04030840701581102c5003005402802c60061144410040002d0140c40c41ea03078040e15680e503210540c82840d0f00034451100700c03511b155001d100344400e01116000f01034811600c011000740c4082032043c180e0740b85000b4424000e081d40200c0025205510502d452500407490030000b00d421000703e00041c03020340258116040c042e1012800d1070034400100606070300f00056400e2110583e07140b513801880e2400041001e4002c07000c40502d80200801003002c40d14076078006009050840c0c42e40350082c40c5500680b200 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 468254217 1250 468252967 468252977
    0x6050c2505012711060a021902031c031a0f030c090c040905010b1207180b16120f02070915050d05030418020a0e0109060516030e091017030406390305040501 69
    0x50010340c00c000c0e04565070f2003030b40d1300100112500e0000c080c0c2c40c0085000100d0b0180692f0554421001030140c014003403444503100440d10700440e00d0301025074007100c000c180c4251105d9015081d2500d0100d09240d4020301600d2611107540c0714107000141c0e200d46d50185602c1c52500f400003582c5040003014101c2034448801030f141a40340e00908030f410310007084038080b40907003086040051040d0314004224800300c00000411010a5403244200300c180b10b132030540825810038a07c400158180004c4010340501e01c400c0101300d0f5005e14044034411140030340c5008410309003140c4203102080044d24018880b5203407618405d10440080c0c4003075003210440ea80800ca181da00c0701c03115070088043e0001c0d00e03c10740c0c80c80d0900740030a10b9515406e14890f0207800303205803450842d416458034008036204180c01c40301003800d80d1814442c03408650204140c0c1d06107030410b1005000150340325180d6482100000c010034207104060900c0700303004500d44494100115000b103100101500b00d005081210803d80b07503 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 468255467 1250 468254217 468254243
    0x910052427190b040e070e130c171605070309030c0602100b030a0b0c0a030b04140412110309061305030d09030b07020312061002070f0f0306050c25050127 68
    0x8410b031500350b80100c00070350340248000c3c03104071464004a0780c4003096107000082c0746409004070703096208103a0a003480076100c107083c90700b0740e400880d21038800d07113116030400c086d290003070708089400c1c501002041084000070340027080c90310a49105000e16000011a088079076185070183d0f0b1104601d2901900900340034052070185030101e1482c4580382c214801100517660300b282c1210369440320300d051050540d9040b401401c1e840e64400c804d858024591008002d0500703062021240c801084000b0803c510004c41101c3c2c044040261100c5100607100c40b40c8800707500765001e980302074a412094040c400c0781012040194031a604d42c0845c2e0080004101903110380504070b844c3c3c85028895100c1c0d110340700c007040b45410007003e40ca910740f8503441600d09440e161600c0315072101e01a4050f0610040ca40c60034000d1140a2083d1a0001c641c4140b20b17207070003180b5440003164009070408241031003401844105108083d00058400da4041d0700d00002214501c54500304170b1410390058902400300c0d00 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 468256717 1250 468255467 468255499
    0x100509031c080709030f0b0a11070b01080f0102040f1401030603140607030c05030c040512030706050403020f15040b011205011508030703020c0f0a05220c05090910052427 75
    0xe221000d5940100b080e80c8014020b481f1400c0000c2c002e4980b0300b803541c0c0c0d0500791542096000240c82054891a20740e8083c0d4584420b003881c017100140c0346003103a44104400c00c40c6c0f2a035130141c0c104a424002c0702d400c00c9207005006800034030705640060405101c0716200c035036004020524500c180003e4804000d8a041d8940c01c5070140400c03220016000030400051203503162000202c607007425800203ca01d040b50075a203070740c00e40d4004d039011000b5038480c210219160300b06201c00c211500800c20182101d1400d600c0d1001c4902040c4240724155104603d83c1c01444001e400c081c800541d401960202030fa41da507401590f03a44003002c142d00501454041c150703140303800340760540c0380e0b24000d0880e03100504080401682e070304c540c0c80500b41e209c0c602e11000c1041800340500600c500041e1903403526500d0002c284100814014508e4280300e03000c03401840709580d0401c030600102064040400c0a88203041c02040b1840f03080e124220710f01e4810b1513418124041d1590040352601961200c0d030f04080c1003 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 468257967 1250 468256717 468256727
    0xf1e010303051e070c260a02060702040c110a0302030301050406080c0907110f010c0c12050901020d031503050304082116060b060405040906063002100509031c0807 72
    0xc00018000b0741c08001c610202d900e800d1001200e429000081440c16685654840c0000040d03402200300c00d84e0a1401d41c0c02c1c40c10080740303450209604010b40600055980011518441c83c1e81c02446507544140c00c0820703d110b01d884017000d844500c11071b03403182004d0501079035a41092080d02d100e0b80c00d0650100d82c400002c903036904c4410300544180090f0311582815101140d81140e09d83c0c40d84502d0708c8a00d02000c090143d000011916200c401c008004c44c1008640084958090014030600300003003c66640d0000d1190030039112440d00144044140c8028001380c030b00303a84050403c0c440400c02060743c05020850102c1144141c50703d0400012458400718140038510b000c0e042580f2a040500105042c0d400c8201c0002c40205007910f0161921f0002d02180e040131010b40740300d60f0714041400503410141c01c0d00c164a501189141c9480301c0c0b000c1007842e0104034180280511483e030320002405000b0000d42e29101c5004081e6003095005112880070a1401761070100000d420f2800300310034074014 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 468259217 1250 468257967 468257969
    0x90510092003120d021207090503070509130308150d0605250c031d0d03030f110324040e010207050d030b093303070f0504060b0301050f21060f1e01 65
    0x10b005007250180010724a100e54010480e003d500715002c1080040205110100c0351042c03c0c20344454100300d0030035040c50710b050900c1d00400d016040f14020701008403042e41069014991601d8440240e6039585040110024014982c0d50041c12012804042108a810552140d80700c400c011306080704011401c0c6980d500308580002043d2045e2035030010a00c00e0710003030a5041c9022201c0500c10010f00401c170000ca1411003540001c2da5081995100142030040c542d00e03501c00c5054a0840c10f10300b0b1a0f01d9100c1780e610004181c020344021600e11902d45030080c1c143c40702c3c41c030000c41d00d6000900380742e92078407195010080044e140030b040006d0303445e0407906e442c0150780c44943c0100b0174418566091070103040710780058171048100601c080581d0f0400c03105020300401209041d0382440d08040c0810380d0300715048401e508c1d1080c40180700c3d58076240005130900b002112050703401000c0c10508a218010004249058080c05080025100e0808a035900820f01c0c2600320344071100e030500b540806842 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 468260467 1250 468259217 468259219
    0x1401030b031b190e07050a020d020c151b06010b1c0603120503060f0d12020d020106240513090504170c061807170d110708150a0905100920 61
    0xc2c086011050a000490003202455481c452a005803110f03a0030b071004a00f00c41c10300008030f001500180c07040d03040c00f80f1043c03006140010242060400000744c101190000d2480303144070301089504403441d6204110b071f60fa01000081d40c08a584078034034481c8030b82c4030b010588091640a02c600c041007006101e03050481b500605107505003070111100f1205a80040d1180394003110100c102ca402d6a504101680102c1c420052440880c503103420203030810268031080b10642e450003a04000740c0d00c0840158224105020304081d0400c004001541c4a000f682c03d8400ea003076242d01d003c1781e04211648640e024501800d07160340c0704400100204c0e0280709111614400d6000180800c8141c0000300515505190510960f60107e44480404001c081329201e00a00caa002104080320713590006102860070208202401c0081c5c103041c45a56240c13070940e112908000b00314000741d1240716540c04048241d5001083e01d890041d050f9007000074204028044c3ca10504030301090018a031080c0d066170400c00 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 468261717 1250 468260467 468260503
    0x1c050703021b0d05150a051806040215190f02070e041509080409020a050318030403020603010611030405060d021e03062d09101d041707030207030b011401030b03 71
    0x1d80c0c000d6a0b07040030360350b10103508221003014050000d041030050300e41c00c48801e000c10500349054a4050161400075240c4220440240101114010702042c0203074816015180d1090107921a401803489208024609400c000c103500032000840c0d10070030000c201982982102c0c20540c6445001c0301803c1d09540040c201005844200c070000c02e41d4001c00c004034040d00849003460750ba030346490b040e0381c04000d074000010400810840304000511150b0f60b018212402142041d00355400f00300079200601802c4240200c0c0150402100410411100079000c00307400242c0b01c00759404040003a400140000200c102c1126505108103000401e44c0e200d40b6005015040c40c040d03111400d2004aa6180382a1200d224050240c03419150007094a024040400302b010303119203801c8450b40c50310000412100303805800380a210100c2d0203160f049159000159206688244900e0217a1404410358001080030482c1400010058842c0c030801900e02c0c02a04c041c09260590380806407030720030101c20142000 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 468262967 1250 468261717 468261733
    0x151003051213031b08071d01080a1208150316090c0f050a03090f080403050303180a080306100c0210050306040c030e0601150c0503030906070e010c030e010807051b1c05070302 77
    0x40191a20181e13440100c0030b030b040055180e0507200e003020b001c2e0b004464010521206c020b0466100c005050040c01040d020f40140019603480d0300801c3c80c1e00c00d5010811940101007240b07203c000300c0030f140d601001000c60714603d01e5504007103c4003ca501c04c01d807265107803070140724a0a000d941450040b175906c1d500d140c9440c11a86080c0c0052596400582d51400b4481d00400040c3c00040207202171740c0644003c54036498540346c103002802c50459000400d410000708140000c1d0f41c0c5050340d4200d0303012609501008030150044407180b55010000c0d6000609106040760380c2c0d003020040d370107580c2c180d80030b1044405c0a0803d070207698040306c1958165020900401425003084211070340304540b03180403001d0000c2500d607d8615041581d0f0070106030410020f0000168103c54100204003080c03e081c1107000c107d4401406159404840f0781c1400302100000e00920704c608203c846801c81a540d5a503c80c0200740313071a81c0c84602c0d00303c00b0111101100171708040340c09403040c0c03080642c1c103900601c195 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 468264217 1250 468262967 468262973
    0x30a030c121b1a071809050613090606080c10091505070c080c0109051806010f020c1903020a050d05030a270603050402091b070602030915100305121303 67
    0x2400d11000c0c000c10044204440414a42c440d401c00c2d0101c1e01540312261003061441080d10501000740110084c401c0903c50118500004c0701d22104507003420310001036a032344132804036422004004c80d04240701d00e40720040d800c01069503c500c0c19038081504a8071404500410f2151403284881818086805078000300b0a003c242e50180b034007070495151180c14203a1680e98020300f62210b0f008440990044408580c0a5034050465002084100c0703003c03c00c00700d140c20141220101800c02d40c108040719240304400c80c001c01c040c2008600241ca0440000c146420040c0c80d500d807400124480c900d01100041c003450851200c00016800c480a1460302c81500300c15640a0001004800c0c11820703242e602c5e100d055190844002000580c40100c0c65241c940304000300e414001700715082da030f0f4000c554028417160300d506640b10190300410040c0d590301d490320300510b030a581541800555007403c013004a00240817511004480c4503204450795440c0e0304414001c00c4c06010a88040681400310403c04 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 468265467 1250 468264217 468264233
    0x6020c0405180601060903150506130234020a0e0c040611070503120307030e0a0c06120b090c04031502070b070807030f06090209030d031506050f0c0601080d0e030a030c 74
    0x84074440066408510b481e00c003072820210241d10910201e0714004c4c0410622902840d500c081728201ca030104420324203000001c144100780d0f00920308030303035010401004410356001c072420204015005800c03009c4035100c07c03270b00c691341000089010300a284000510b40000510aa00800d48942c415042500b0b05d00304903403405015107500e19a10400100007101e45007448140d82064200903000d07601d14142801038181e49012003442040c0d84090340070000700f15551403580c1078030207070b01d0134141c5c1c604007140c1c1d14080c0c046a0b000136413041c581001d002e00400580010030480e4441e01400b24000340c0c01245004034003030840040c040d901424006401c01c0c0c41a1075031a401256410000f9540c1c0c503440c1003170100e8126802c103101e00307580020b200c020b0785000c000d002d100782c41e40d00e014084800c00c4260b040c00b5689078807501081c01401300c2c0048117020f0101c262901c210079507085803070541e9170307201195481c0d02045891010403910451311b0141d0070007241040c0d80e15015243c0409628140d81c817411 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 468266717 1250 468265467 468265471
    0x20106120b0606120a050103021c021503130c091b0912170c0a060e120a140c0a0206070501060509010b0903190c12080706050a050105090a0209131d0c03010606020c0405 74
    0x19103e9010000e400c505440007108a01441031480009055070451050162a806001030308011102540c1d200d40141d4919800f40d0050806201240d280d8a41524510a0001580f40100380351030080000c02c00c2081517200040400e0032450b82194140c800341e050303d00b07080030701840f40383c1000c1041030404640300d0010900c0c10003041600d00d15124403400440e0510740d0004080300c0498444c042e13059a5142004100c070a480c0d070ba64200e180108405024100d102030305031000240340c01007048422190140200241150040d1610396242228a00180280458007800c1d1245040800128148111f841562030b1440c2c050000c080000e111380410002840c0d9000481c1d08154050001c038500d100110f1140d06544241078060f1514550714100040c0c64004004c59101450000100120350f290808942c104ca0480001a50f0b6031a490200d4052200c0090205016080c05170b000307440c0c1c400c003017007503038480c8860203070382158490004050a071040c3d441b51100680c00850b007a007480c50103034002c030303 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 468267967 1250 468266717 468266719
    0x150501090f03061814010c020d02060601090501110a020d03091a1305091b160303050f28020c0d080105010215070e2e0201050412080106050a14090a140f01020106120b06 74
    0x340200d00303545da810150005002070581c0d90351903e000007400f5404020010705006039002502031840d110000800300845881260b0412584e1100b0301043d0301d080c01440c002c00d40107007100741d111600d8140582070301c20341e225078000403400e10004200c0307410220541d03e0b1580920140609030380341408106c510840030b80141403034031140740c0606c0041d01c0c0710010300480c40e40040700c0d02030f034507030b802c010b011104010909125802e1140411000d11050005103410f21212440c02c0840b01980d60054024040c0310760380001ea1003000c00c1da45045410040450403128242e0132600c903d4200006100e60440a07103280000c01c03002c40c60071155160156010007540e545545a100300444001c512044026080141d405030f55510144802c2c0f2214043d0064000f1450a00403207551410348000c04510500c00d00c1002c004440741610001118441100c02d110030003000804695280c811404030104500c2406101e4403522074140020350060040d00220781151080c2d040c48910390700c402081c26402040c10b = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 468269217 1250 468267967 468268001
    0x60f05071101052b0f0501030b0a09052415010203071203020d02090d060204210b060409060f1401060915050912030903060c130e360d0201150501090f0306 68
    0x414021180049201e208010818807100040a5050303600c040f82e0317940301c2a203245c9051900500106441e400c80b6500070082031030008002c2020700301a8201184403c08220803604400d104840388552494503002c0c0d444103600d4968102c0322401a0b07640e1007000001401d41a604a0000b03580c0d0090303020703010f10701d2440c402501e01510440010341480e1102000ca80e11640424140449001d90760010002c032002102e100c0d200216032070380d001c4503600410f072a120b03588400010301004220f4010840b042c1648500344092201d02249084ca55000d02810000030041480019000b41c00c072400c1e280540b01c3c0d11010301e050154401d0002c5510004114202448204070704211514200300903132107400c1103002551120b0300c1d81d405080700d00c0e047c0e101c04e102c0001c440901c6903150a0a0150b202c0c00030741c07001c100c280d80c4108004c2c00e203008400c284400e10301030a6119910b068064002c902d01d2804c4401e0108c890f5107036001902c6240c881d01644840310100d510510000d0340640c011803182d40c5203907803 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 468270467 1250 468269217 468269227
    0xf03050d06031a071719020409090f050d05181207170f0c090103170306040e010c0203070b01170c0907050c07030c08010e070e1f03060207060c09060f0507110105 71
    0x31010a494466000f210041c40c07100c0c83c1c1e40240c1c41d0910694200c100c615003020140701e071503a14100054054501c1740602c0c805c04039240304400d00c0d41220001e00004000f4007042066044c04035208401e035000351103a004007215070301c2c0144604110b4605001c0e508218114452040034004000c0701d00220118a10844401280d4401c15901400c0101001402000060b02115225090012241840c4c0c054200720005000081c080d03145e440c0d0141c8a403031410344942e81e04000030040d02c2d040807401071951909034028442a40400108501405201d128500340d07079903203004030304007100030302103d0503006030383d940d805450080c0200f81c01001910b002802c02000d441e1150030071406601c110740a540e280f400700600030082c02a42e80851400d0003400c0302c2c914003d04004640e800030000c1103c51a10300014802480300c2c40c0c601c016681082c4115140c1e6620700c1e1100003442070007040008506201000260a0710407080e08074015410f9440c00c0c01c0c6040755880800c145014032401c2d042c030000b800 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 468271717 1250 468270467 468270487
    0x6030714030f10090c0803030c0a0c05150708180610060503190c05120106030c0c1b180f050105031b060d0902030307061e0b0109171204090b010210180f0305 69
    0xc0c0c554200c824000800d04d0b0305103020743d0b02119a6100a01682007882000702c0c0c800404140c0701100081d050546d28041585000c60900268009840b54410b000d000e001c0c0c01c903840391000d4414244070084800590f03503c9281540c0e400222401d102d08070700d03150244100c510407400356401a040e00d078806102100c1540c2d040944158000100002e900401c1d0062914040081180104001c0c1804c02c0813030083c1d0300081c00031401000c007070301004414031408200c00710901d00000501202d84446021640000d028002d00074a40c0400d6800e41400004662480c005c10a20080102c6481e106903d40800c414011340d500017a440c52000d40c0c0c0e4105100150301c041c0011b01c41117100c1d100004a0b400150031842c030354070100241103015440e18441c02e038940d07048504502918071580d12221190700d6501120f14240003810340642411020500098503040768111413406d4070240c0a8503c006141c3d61894120351654000381c580110804d0040e004c5200e01540341251030103880c0040c13500341841 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 468272967 1250 468271717 468271723
    0x914061e12010b01030b0f0f0907090f0f0302130209061c0902040e030a0306270f0605031207170901050304020d11040203072d0512180a060209090f06030714030f 71
    0x201c040141a516401c00100d1980e2500c07568000700ca0489400c0d454091000100d100c1101d4400f58038003e0f40b0040100708010700465091009145682d050881c0300d03162207100c034003d17503035120403401400501c95407660079039980280c5900b580050400340c10140601020085102961060402301e55942d03003450150306c81d40500201a48000002c40e55495444001802c96465a100510b280d4641c2c5003082d041d440714980d0a40e0820711000410000d0480e4428001008a0343c0a03c0c0e161142c050945c12441c1d024004c0c1c0526801125440310b182030640607080c1e0380c0f00721400140095001c0000900501d4400008141c060050403001a0b4030907981c0441c08907401500e06da000314140c07a00c00300c1d800c8201c00f00991002d00031607072464008482d0201070214000d054040c2124600074000490310840684c5040801310340500b12908103c0508008009620040810f40281740950014443c28280a11640907003c050010b240592900c0c01208003203040690b240d50501a8021800c030b840420 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 468274217 1250 468272967 468272989
    0x403020604090c260c09010210090c1d0106050304080705010f050f061c050307080a180905070801051210050601050715480c0b09010509070914061e 65
    0x5100e00081c1c0ca5a03c1c107000c4c100c1810080104030242012102402c2401e00c2842540c001c20540380c200e84540000d40142d050201104c44040c0c410718020a410a01842510410440d078503c500d0500ca840c5802c3d078058164000d001d4600800c3d0b04001040004034100c008211080c000c600010368110f06291410a50b541555210313018403180040c400e042c50308c0b6140d4201482c1444201d03001c42180e80d21152680100e0748083c10000c808100845c415020314880109201003403030741c9801a44403217006000701810303203007000010141c0c0004205418484c401090b00c88206005000740c030510764074031000c0c0a0041c491f038100074050200c5c100040c5848010211005600004190301a40b2140e00c003440e00c2412040700154800703004c52a032031a0058140000325511139010119003d1000c06942d0400300c8080103110304065402c01008110660043d8060a12801070781c3c00c1c59078585000040d6070900c1610400d030a100c030007041051400e940e1403201300c400d181e10500006d10306400901400d0341c03 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 468275467 1250 468274217 468274229
    0x5040b1803160e0612160b0c06070f1709121b0c240313020607080705010c020c01090605390c1905010c050f030a0201150e0f0f0403050403020604 64
    0x4640642800d840c0c28030102140c0408030903581d0030309291080d444204800030301180e00a01c1d019140d00301720ba031309018110101048400b0700603201e650b4404d10500348d101c480c4c01c401901500c07000c0b845451284409401c4120159140788150b644110941c00c103520244c140f030160f100c0c45000305080080c50002e08034511031090210071508100301118181141e19102034841c1041c40c0f04000301c0c0300c81124802840d0084584035403a9610709548801c480c0c00707000061b40c02000810a0001c1224440040401511500080c02003810740d00c41660307a00240329501d404a1400d03034081c01210700c545c0113066408451010700080106450300035a03054400e8002c104844069440e0302c60000d01000004072050090310b5081d88000e1105207c0c0549a45000701c60401c10034008503028040c040080150211055060342c2d030b01c4031109000b0307000b400c8011030980654000c540c00205a003921942c58455540c03101020100c0e40d0782c5a2a01d030100000b4811014007005010110158035100040d0014140f = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 468276717 1250 468275467 468275497
    0xf09290f0a08030a080109020901050301120512030f2415160b0414070b030610050c0a1a1e090c040e10150608061c03200609060f090703030c02010f05040b 68
    0x510304d600810360399050308031800060040100f1a0035985c003100b100c1c1100ca5025400d200401c081c5041070400400c0522002e0080c400700600074101580a0040c0c040c00f0a6407074800c0300c23040104101c0c210620040340c40e03801400040d001315000081401040000308241025090030702c207503201c8090031002d4070140c8140c2d0202c180b04411a0082103901d001d0907407004030301e00b5407600c800024002c4205e0b459500c20040c1c042154841920104101c07004241d000d031711410160b20855410241420894200c00b501c400844011034099500240030300641001e0080d2040c078844c201408090400c649440349180300311001030b0187c0e5091f10480494015507030448090b2490401d005244100181549200b03408001c0300c0c0c412007980d010a401501d5040c2483c80c401e0415403100310b00d076009001d5401250080d00104481c903180401c0b02407268440064001290302d854500960b0344009000c01808201104880e10240d0701030211091011560b01c4c0c800d250a4440e040c03400ca40c1c0004260f6060b0700 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 468277967 1250 468276717 468276727
    0x303020309100203151c0b01260d0e01020c04021201050f0607020d0302030408120301150e030319030207060c030912050c0a0c09090308090105093a05040f09290f0a0803 74
    0x440c110350714001e40112107036140080c80040e1108140b0847c1803142407000c40540c0b0003858088a030240210680250034266a80340da2001000b41c40200703050100d0f40103005210103c0c20381d103054403d5803001c821410340030306035070300301002c1c084c1025002d040d09510080910401c0016512264a100c2151007503002d162154034041040e407400450500d6001c10729000d000501012150f00d8252200711514a01401403652500200381107115040c60611030005118040a00b03c0e00340d002001c410344181820001030f116040210100c41c06000000c2645500700e0340354444238402c102034103440400784241c40c04440f40d80d5610040d0126544400b141071788640b089000d16070820900c950000582000f40810f10b480100746440301780d20000e603000c465100b00503601c8140e84c00003103909140b20010802e06903406801c0a4900e400c07030b109121584181000104402803140030388441e884400e40c0c4c10241030002c2c95003202d454a9416202c0e00045904002c51041e550802807000400c50f19020355074036 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 468279217 1250 468277967 468277969
    0x206041505040f0602070303050904050a060302091003031403010b040e07050d050a06090509121b03190e030d0f0905041d060703020a02010b0102030c0d0e03031b01060611060f0103030302030910020315 88
    0x2200c10342e44844e055401043e4204003003a004000c480d058a011140018503036201502d080c02014160000707034120100c4010880d0104450000744188c3e0702a4030b482e040801c80415440c0584000d001d06001118240400c1140089801d200d9402c41c0c2142003090030010444060021182d084480b10700054507038604001c20300c1c0900c160343e0001c0c40303c0b02900c5020000c034549000c40c464000b04d42d12444d041050040c410310240701b07450200c644010b0f850407402c0c0300b0300c1c02014110301810f40d0748280121060864514082c03003514103242d407240c40d02d1910520704410800105210402c02d13850503140580010211001c1c0320151140f011038500580300c3c54500340090844130f03401e0926055500411010003500c0e00011658100b0205250008050100e8400719045004000441c0c0b8122080d03c87c00b0811001900542c0945040b940e030404d42e1001455029a5200280d0788220150455801440070911a13001140d02081e000201c075018202c1d110380724200d90084814003000d0503240d2045801e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 468280467 1250 468279217 468279239
    0x703050c1605100528030204090e061006050a0903030f12020a0201090c140a050402090d021009150c08031b0903030a021b1f0309031b2102070f050607020604150504 72
    0x200401501d030181c00d0086040b03c185041421701d284a5610318410001e00c100c5210b50110383c00b82030302080502220009400b001d40c3ca40003921a52030181500902048e680d21030b405a030081d220344ea03a014221490f41e201640d0390340c01c4507200d10400491260814001000340000c082110b41540000364400c0c43d81090007041c80d560300b0010514035080c0464529549081c1c02c4810703204222030041e9920007480000344858002c0328020b40100e6200c2060158a0700016a401200c10003110710a030448110030803500c60100300c4c4000c29800c805d04c0404c0c240202070145190003224800554540100240082d15540003885028016800035031000d00c80d208051210382206401c1d87c10b60702400e0a45841c0d149203050b0812042019650702c007013070074113108184c40001c1c003485500340701d1080b8450400f4500d50070610086410316030301c600b01101c400e1001900c3e80481d5141705d27241c42111304100412200d41c0c0040e00603a4801801e000100f0500340c145c80880004e803482d00c80035503da02e44000c140d4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 468281717 1250 468280467 468280489
    0xa08040314030910150f03170d1b020f0109020d110d020a0f051908070e0c0421020108060d020a140307091503020312210a090c03050d090f1404020703050c1605 70
    0x628017542141044003072080c0728032801380c952251114030404503007984c0b88110b00840e003500c442c06040104101c054684032340500071583d400c0c0d09403400460902d03034850985842c060000e4000488803140b00100f0301d0080c5000c4181001441c082c40c154003038000480317200349500022041c0c080310f28100400d2a1504c0e00900441d40c800034804464902049240c40360030b0340c03186800807649030300051507144c250341c00c0742c001d031240341c0301034880d008090319045000d0a00402280400c3c102c0000c221140381950018552a1b40101320b86451800c00e07000d10002c00f0136501e40c0d9018450074001140546e00d0740150381260030030780203000503e80f13980101440c0c803111402600180c64104985601d164910514001280b03040c50200b14a4590040040003050700d03020292400c1c040040120030880b01003400c1440001643e2005d10303a82e220440300801240503c81c003100e91010320912851070403c0d802800c0c07500c1c028100141801427030700c1014200020b40e1108851400a60030034006464404203800c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 468282967 1250 468281717 468281741
    0x1121a090f061c12050901051c02070c0e15010e030a02030312060306070918091110020714060a020312060303130f09200d0b040f02160b1303050a08040314030910 71
    0x8084100d41c80d1303541003110954814007006070028081669034000c0044800907601102d00e1000245a41c103808025001460115481c00e81d0307540006600702c5d1b08100c14000c222805220380885042c40041d201200e64607102505801050320910143e50103101070315004016414080540c50310508040c1030903402080d5400340039582d0010302c400603050110741d19108075584006a0340d0580c1c02d10718100000030300c400340c0c80240755070445019940410713810102d03080301da144030a40b42c07e20b0400c6001d010b44e880c3c80380182d0013400000d0305a407004207441d8000c0000340036030740b422011540201002c0d07408e80080460ba901c0c0702d4108926816031041c40b00c40301581c0804a106a8180f0742c1310004d10a84200000070f80c5c5030307510b82500d80d035281d02c2448900400340085680c2d450ba880c05c00b050400500b01600c5603800100080d064100707a812030b030003007a0b05554451908040c204141c50140340600242c08005003850001040501030000750300441c01c4200402d020b040c0d80e901d40c81501c901002c09 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 468284217 1250 468282967 468283009
    0x50a0605180c04360c1a071403090d200609030a080702060d0207141005160c03110106090903110106030215070c0f0303320307030c05090604141206010501121a090f06 73
    0x40c89180ca07110054550103540110b21414107011417100309c0c0356000b20000740f81d02c005482145020084c144203444d40050f50251401414000c004c108003040c000c1245141e0150004200f0b0300026049000a00d40144024281e60070840400400001c0740c1000c0401c0f150081482480b150011041003c280082d1070301500380001d01e0045000c1d0301122000e051207040c45480014142090f002d00f03001e81402c04505e001304001a070360440740c00600301c0d490702900420202111504440410b010f076800b0f40350050003c03440011306043c40061a40300f18019500c598210b100491034403103c2034000c2c01103000781c0d2013203101c1800c2030140d102031624a10407440028401703500c07a0460364a0342541e03403000c514100081d002028000030b603001e1080d90b1b6025803026001034045a1030180c2c10861000c1c003000d0b1148041c1c0013802d02041d03550082801154007180c00d0390708400c542401ca0b0804c00e010b41000e8010100c0c440800045003920078190f800d06040f220010801001e4200501d200321500c400d8840d03 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 468285467 1250 468284217 468284249
    0x4051806030a0b09010e0105040308011d100b0703021005040b0f0105030c0130110d050f15060a09080a150e0307020d060b0a050607050a0605180c04360c 67
    0x40e648410000005102c043c0c1c03c0b0014202034029400814500e82d2040240b01c0e9140628000f04080030034026620381903242c0c003100d00c42d9149a480e03c1c1c85040a440034000403414202020055001011700702c08601c40e010074011203800d507000d0940110711440c1c414185041894000e8000c0f14160851402980640c14000d541c1c1c0c0d02042d44c42c80e41030100c01800e070703501900c2e030480c2e420704442e0500c200c41800e110410303418001b0f0100421010781c48a0040025460720981032040b25000d8600c49010f600d40b1207144241c0c0f42450051a1000d09400d00c01580b41c3e0b1003880e1420050700c150107880100d049042004081c046014800e4254140720103185460400d42c000f0b40715245805025190301e45d200c265503001e0f00e4484018000e040c000b001191a00d03c80c2c5843c556552464504454460811000c9243c422088031141d0213560f02001808691840c3c005002c0141070200071303207152740c1018078281070351031390b29412403010240c5100002e22034545d800d2611087c0c400798044c00f00b95241c0b80c0 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 468286717 1250 468285467 468285469
    0xc0a061e0e0d0308060a0807081005071b03050a02150109090303110c190503070b040f060f0b060a0f120c031a090c1e040b0a0f0e0f01050f0a021c0504051806 69
    0x4034110b00d440d07140c2071202d0f50f92918404a6503800944d00103000911070070502040c0010001b4941c10115075025060126648003602202c0450b61482919940709035545240b001034001c00141801707441a10403201c032030784003005117804407100b07074062241280e80301070290030315505000303560003814408621752911000d01c5100780d4400e0541c144419441082601c201003180500c101d0f2022500826021168146410b102804c0d014640781180c8040c03400810030001c003c3c034040d80010031801032040d810b09008207020b940915404241c4800c01102c031000c070960640d9482214808642a030300080c7c0505920b501d81c40889003210050f00c1001b100c0b0412041020f000300319101044c111500501040c20800750310201c0c041da402c0300340380550100f02c1f80341040d03101c40b88040440e010356585410041c1502881050031030584040e0001e901088000d82c614a80002070914440610441e0032a8003c00a100f607d60780311400100003075030000d02001f092070110f070520b0b100c08214a04401c9824003c3c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 468287967 1250 468286717 468286729
    0xb130c08060112020705030a02010b09010e0f0f06010e03010c0801181104060309030c0c03060b130506100807021f0e0d0206010b0702040c03020403080d06032306180c0a061e0e 77
    0xc1c8010704112402583d20300c00100b58040c0c3c1c001d554048101c03030315038100010290182409240e00c50082161070000101880c0583c0c001c2c6c00b0340c4455407046015160442003400070000101224103104118010f052562401d00ca881c202019581d11441c8650403d01c40d0104070320000840c0318141c0c03c106c110300c0710204041c01c4030202c50300e5060016030500589800c1c1c0d003d485c801006060045003070740000c1808a950001e8000301d000301c80756140c3e410311000342c0044034401d84006130440c585041090030103004006103034020f049401103038030100f115885c026004501100034520030351100481030000100f008030503500134081c00545801e40c1000207200e254000c0a201034071070b5071174203c1c05030b006000740c0c11900615042402166100012003029000d0800c8d840211480c690740c0e05090b425075048040381ca2120f007820f015028030303103524580c44c0d100c100074680c103d0750340142c510040b8659140b102c480000c0a06444e104085c0c0035400c031125000b20075052400034400ca400740d10403503540740e07 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 468289217 1250 468287967 468287971
    0x3180303040b180f1b1503070503040510050705181c03030b0f0d020d260d0b190617090c060c060a0b0607150e0a051e282904060b130c08 60
    0x32155280d05c499004001880c01e600283c03454013106800000d002e05190700c600114444c60041c012614406900070500c1c04071001212050005003052040d5100b202545d5050000305100611008850510328040e103001c03000740c0d500701c001c00d030360301051800f608100300880711443c0704551013004101c3c5a00421300459550000402a070350f40007061492a10740051400c1000c1c031500151b8980548148090051200541540c811002420804640740b40f0310100020b40d0041c0d942c60421602c00c2e405602014009403e090103406400002030341515488042c00144d4103808c0180041e040c95190381089690441c81c00e8018001001442d001c1a103601100003044144200081c04c00310390700599080c50a640b000038040d00610507a81003580c0c80540805400780a4415541e134040c0c158504c21030050640544080c9208011805000c40c0703041d869145255405c608440c1001c07064480d85140c10003c4608a840d90b95880713080d0007900f825190100d028000e500b0400150300c1e04480a8040303200 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 468290467 1250 468289217 468289243
    0x7050703020102071e05060f090d0309020a050315010f0f060c11180a020409060e0603070905060a0e1608180c100903020409211b060203180303040b180f 67
    0x24a44040600c03d504540c40550041c0011805191301d08155901e188490401d0340c45100b03a40104a02d40c000080aa0050951784001c210b0000d580805402400d955032007643c0c040d82290000505480900441f035068240444079210b549c1800250000d800d07064001c0100070304815014003903c0d421802d1101581c0d004000c481c8a007047d03200198545003503c0380c0039510b0301c0900503c081d0411b907030050001da408130b450511010b0b0321502d040c080343e0411031303880303034075a0000c81d0802101c40a40c0c8103e80000f0040c0c42e840070309440c0d80040c16501e10907a20150304001031600380d10031550020123140c0001e50503400b422101d03009148107a441c4010b1241a106681502e60a00010300410502c4011036000d04144524003150034481d8442d070400800c00e5400d19180201104640301e28000241c03007509a00d02040c403400398540e50000d40008094100343e11002040e04c0801c5000c0024502c610320a08075841030b0724041c210903041400d5a4101400c69001d8900b0850804e0041070008051107 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 468291717 1250 468290467 468290477
    0x103110705030d09061d1c020c0f04050709261506061803010605100908010501050109031208071b0803060a0b13030807170c06160507200a050a080c0112020f0307 71
    0x300178188034004100c0d00070400c0c100d40316800d0178811100085524102d500580540034207040c2c002034140c0e2035103040042160712242d202d1002c613031450507a10050300300c4180e28004011a4540b90114103410104000d00500c240300d8108101201c020401c3c2d01d6040c1681e00358068504110300410703100d004010f401c48094009000419040d00d003580000c3c0180030050802441d1701c1031000280c00d40ad098002d460407035080000205241d4011400541180e82c02001e005604511850848440d000030748124100903404034480108105a49407402c4a0b00907607a143d80ea0504000b00010050350b5881308960440c10b0181003192102c140340c40301142d400c0065543d0390885843d1004140c007000d030020032009000b1a81e81036400380082e250344210000804c0100501c4034010035506400380610082840d0201d400d1084c0f41c0f10301d0070304d00d80400d20243c003080d40961202d0000d0391180980c0c001c08095071004012040300d40e800400d0792000c00c40b50000b10325202d039501d107541b442c1c4001005102809 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 468292967 1250 468291717 468291731
    0xb0708070311100b0307081c08100302150c0f0604081b0c1201021b0f070504090201020c090115020c060f07020405060109080f01020711030d09030221060a09020103110705030d 77
    0x50040226210b009054001c3c0c0f0300d41030f04000190010a80051040d0003840307a1040400c41190019040441090f2000c0001002080040c101ca042c41c4c020440742c25141c5040c00000140c903102c80910950525a43e101e8681020343d0602d49800340e807030400300280d40403409200c04101034400b1034044803400801100440615000c180c58040c880c04042c1d0411101c140700d0f1400f2406501400e600c0000b94540c811500030080f1460b40c81a109420860342e030400300c0200007914180d8084a07c0520600544112000f51030005030b940784240d000c084504403180900706180d1b41030259445464045603001d00f0300c261540c2c201c10070f0280e003400078007a1303a841000c00c1843c0c1c011103400008200c0c400c01c4500c61040095102e0103500003400444803440860004c60301482c01141d1110504441e648510301d00b403660b020820003041644019010002c03034042c14030013034014080644140d01510b00459445290b1000408035144403122104006050020078006030021044071400ca19103034020810f0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 468294217 1250 468292967 468292973
    0x31e040b0610030b060315010e06180d030c0813031214120703092a052d0103020906130e0108070312030b0f0d1505060603061c0c090e150a060b070807 66
    0x149624003919030b00c0030002c81000f00e201f4000b0744410344108281c6e06d01a41041c02c030140728440c005e150a4105030301c0b95184a4280e4241700c41e2040d002d5000f498100c401c0542600c2d1400c044d84221803600a070080707000113109004140640e2036100e0210300d84007182420002002882e4028aa07103070398170340e185801091145100f0f411200b20103400c00d1900038072000b0400c101260038070081c40e1098200811030000703241d140c0360007420506140c089100303100c900e131102c3d0249440819900d050615078248210a15a181c0720007a05a802100c02900306003410024004540441640100340940c0006400e1000509040c0d581403040d40c542030200300c2101e1400041c10a05900020980001314001071b4801e0000400302a895001810400c02c103540f82d1000340982440121010341d004401803810b0211102d00340071003c080d03401503012205064581c00a001a10b00007072500b100c40e40100d039022a55240c1c20041d5401c40d81da91010882d00f0f01d4503829910b079014a4801414145001c5084818 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 468295467 1250 468294217 468294221
    0xf060212072303190206040c09050604062301120e0d0f020304030f0812070215061908010f0605030607030c0207031202010e0628270203150a02031e040b061003 70
    0x40c2500a0803a0303564903420707802d899034a400000000e800c101c054410701012900208400c0c1c01036411032403580c9010300b411010340180c40081c001307603041607540b480050700036200380a240b11940c0000ca40b0340b0100345030000410b41d040e41c00100200d18940030000010352000103500c16118404c6c20250244c505450041e4114003032648098001200340301610104045040103008490388010200706c3c5881d0048200c0c3d42c4c0c9104c28010241042890201d11289003000095034021180f15009503003607194400c0d1400d450a24080100381900c074002804645424088540d2003050740ca400c107c10859990002d58450345417101808411000c910030a81920079008000f003460004e08484580c14520b00801710072000c410200b1202c0e130b40b0940070700411042d0082c4481101c0c1d04525680e00400c2e201c4000c0d8405102c001240c0c184500b0f203110101c2c1c10045812846410102c000503240c1c45c00f4441d0340f40070344520401c904007081c00010080054107804290350000301c10358244103210800041540 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 468296717 1250 468295467 468295493
    0x50f04110d0f1209080d02060a15030c0e090706140d020307050d0c0c020112020a09090b040219050703141c0b1c0c031703101505070c0b030a060f06021207 68
    0x1041d81c40424030240803003001c051019003ea544c602100c1036885e036006844100e01100e40e00180c010034003190000c030058000414910104a00e1100c0d50b90301e07500d0748040085a40000ca0310b0601400700318001c0b03424010400240002e06080d12856601400c44d4194031403c1441c015965010011031480741c820420381303200300d541441c100040701d400b88020b820031495490803030000c1d07a0b05070a00e010003042e00030750f108803507141c0350b40c9582070920302200302800159607074980080e800c0c400c0c1040c1c8082244040b0300c1c62003c1d1a40d0b955100503003002000240603080326035024104001c03880c59200826402825102c0c000000941e152055000540140c081d2400000190344c091002041c804109601811244075000010b940403000c401e400c503d020413a0040000340c01000c0410650a8680068070320009030f20b422480c04802d0703031b5140c0c0da0490b2900002c007141000b0007006209641d9100c2c0380007078540c1c4000014a145003400080d5520350f03446040c04d8040010440d0b2040003141d000b604 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 468297967 1250 468296717 468296723
    0x7051603030f020c0a11100c0f080c0102030708160228060609110d23041e050106090506010f0311031308040506120403021e0303041709120309010f03050f04110d 71
    0x50750b84c40074099480d68440c0302080560b0107514060b2016040e00d022949002480520780340c840070820192221851040200130607140940e0402c124030b0b40750401e00c0154031030421600d5644541c10080101c941402c141c0c0302420a55010701c80c004030800c03094080c004007240c8060249401c2d881e83c030380400034040b02d61042240a080c0100489a80325100c05070948030044042003000034452842c0d10345080b800c0321200807503402c90000c80d010550f00c014492500d019808002d4950440d40c1da80303400c58005038450030703585aa500030301c20b9139070f0700c150b980100300e9481c81c041c802010301d10034501044c030024255801200c40204a4010045001f0688005007801003c3c0c0d61100f4481c0d81040c2c0414003200e04a0041c01103103069592070541a24804500e504013000314203543e03442e62142c2d17802d00503091140010740144000540c1e995040140015455028050341d101e11280001408091040c079540050508100812010212100e0320360350041d0042001c0701c107820030401041014600c20005 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 468299217 1250 468297967 468297971
    0x40803160323072a03030203091905010507113915070c12030c0b1306150e10050102033408210105090708060a0f06032307051603030f 59
    0xe042c00c40d501c02030314400d1015440d0a08080200044080182580d4441401c13900c1607024030704c0401d12079030103990710501100c12541054881004006400c0440000b181e49039118000c00c4940e5038080181280d041d1004003c0c000d1600c0c4025440f03164001c52074881070240e01c40c0001c1c03400c0a480303040200250000d451017021a8450940c04270541c00b54406495003401c5034000150249800301c1680d542c1e80594235070440c0f60056403404500d50010b00f0500d500b00095484001007030240c03103000c801d40c1c00c7c81ca2501d80341e403170f00211211400c001030110380e038100380ca441003040d640c01104849030810402d104c3c22560715203050056010980320442401e0500e07501c200340400101700c0c01800100c42e8950120818007000c0c0300030080035001d0090a4000040d000400e8070603000c0d41c001d03900b04200403c80381d01d040d00d40d24905c40c8005a9030119000031707240c402a4a400c03a00c0340d4014141c48102212640503e08800e0240561060300103601102d50b0305030b445c0b001c0c94800e0b40189540c002a44007 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 468300467 1250 468299217 468299261
    0x61d0f0f150415140a03050703020403060f020a03052a030c040b0307090f08030a09091d10090308060a030305070209040809150d0c090608060607050c1c14060408031603 74
    0x501c4442d400c03e003e004102c045401c1406211801118520110f0740b0301d104040c40c00c0c601c1007085014000c040d08900505400f400080009090350103101160b210100c1d0058541c217807500d00030705542000e0255501800d00102804c002c49100341080021201c1321035065880d201c1031920030040c4107581c800040400e01005024032594810600800c4642e04802d10308070503121406aa200e12550540c1004669214000c00050308250403901d5607031703504c180901d8000f0071500307418107101c11441c0036244a0398420101007010b410280280c0c01c1701f01a920140c02c1070175640c002c0c046100d0441e001e8031503580d40000808001c2030400304d454003800507080310388072102a43d601d84d154111405142516052050724800c0c035101f8001d100844030950345507a4aa2a420705002c00c95103c4c88041c0e60380d01981007410710944800d607035440710004640c0c4503403042a4606100c0e030b9000e0340c0d0802e40407980100c420310001c00c2d045001ea9412104071100d104001c40c0ca030078203178024180036168041d0110300d241c03 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 468301717 1250 468300467 468300499
    0x20a05030a0207170f0309090601020a050d022410030b060d0f0318090c0801150e0406030b040203010506100c02010e040b090f1501030b0a090f0605060c030c07061d0f0f 74
    0x51103800319081d4440c12103445940d080510780704c0e6940c103030105d400d0f84103108000700c6150194a1540000c0180140c600c045241d460705400c01403450341407070159100325000385410000341d580b0500703658001651140c5003000e820500e1284054400a40300a00c0100469003d035182e140543c001540400754014030303110340c039000e0304c0c1001400c1d040145995060300061522164054100b03400101d42d86e880032030b0700300400703a00c20030036041c940300c1040041804280c90341c8451090b0b0340514042c160142080c602031040509544009189900490103242c00001319504111103041403542424884150081c034400304004054944c103031640060300800f400b00c2100b031000782038040d0309989a0024013030400030040d4240c5070030404042d000300c05046c003009107040d0b942c4602081080004040745050f40d810000d00380c0d400c440f03a50b25440c0c0002401d13100307500f010030140000780b0090910144124425103400b5a0903ca20000390103604004501d00f015520110640260f0074010000d404c1569054 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 468302967 1250 468301717 468301723
    0x905031b0d0b250233040b0c040807081006080a0804060e061c0b1002160e151512010f060503010302040e011b030b0a0e0c041707030204140411090c0a0f020a05030a02 73
    0x452852814484001c14402441c040c00817650450146046081d1034559800412400052624008410500000c100201c080c41584010002e0700000c028040040f009481221a2036108130640c1c0c1c400003c8100007482001518212016824528000ca408601180e40e62160241c0071700340308042d000881e003c0000f90b02c880300780b82081d1003140207481196002d0b40d980341014240741385001c082d4010440000141c665582c07189003038030440301d1011040d02103003400801d14040345a400d00480d11100000c101c0440794010180700402c41c801c1c610f000000ba01900c4180400b034020794550700c0400f0036070825080100390701229052107402c0300c014040240140b010303d4041c1d10074140d01d50006090f03080c503c46640554000303d941d500d41450401000d511002c403210401c83d600944a002016907030b01d200e10706101c141c0305603080051070186001c000324a1200590b40c8100a00401d10004200d010b0684804000d9401c18030318890345101d05901d81515108024190b120000b80620300ca41c0c04 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 468304217 1250 468302967 468302983
    0x150509180f150108010504111207021f02040f1403010e10061401030e150405122a01090507090e010204030803130507081209010f120c0905031b0d0b2502 67
    0xa07005031400c54840000d031191160040385098009031100b00180900d15041e840060310206500d00305241040906100200000454120001d608401c01407036074015003140304050003a000404501d41410100c044490340d66601800f2207210580114400d43d403002d60003040040b202c401298217150b011141080540441d028075004c9141d80c100c95166540640a0071140c0c48100c00600185015140001c02c0070074024000c2c7d0b02d910415202940150254000f010141160300101001d0854a51740340c1c10010500c21400b83c0381c0c0352080030008a180030404000380c60710410080f0f0001c11840000b806402140c0015003101c82c00000c3c806490006c0017445019031103401070740c9003240d9540c03500303468602c2c2e10200c0c003801e081000764042540c420031402001180300c3c240700c2c0b0300c4d43c2626120301c101e550070403001002c1503140f00203020b1840c003007101c030b00c200b2040c400001e03a02050001203540c500034540c1c002c002c02c2c4807130041200b0010140600c41c502c41c814110f50090714650307000139038030721603 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 468305467 1250 468304217 468304231
    0x60c030c01050a060501030b01080103080d020702180610080405030a0815040e0318030606010813030311030a0e0f062a07060c09030318150e010c060501141201020703080115050918 79
    0x1d0f200c03000840794002c8c0507850130504142c441d051203a185803110b1010768420300880308116820030500300140d0300d8108090b00c8400ca0321445c0d82618000c07040c40b104a11000c180800c0c0000c00c000c21002807000000c90b1290a80b42c80e1280407501c0700301581001c00092000c4991140c02c0810ba43e0300d1803000005000348801544420404584250a040e20781c0c4095424500258000740080c225541c00804500400d00c80e240015035601c195103404003a40017600c1700780c405034880c141034444071801c0020f040c0d11304000c0090540fa0401d100051402e078254429600c4040600d01d00000c502c441c1c20944a205400c040140440145050000d12800e4540021004505424400c6a02c06544180344050700c020f02688940209844802d943c940c0c10362100c40e041200302041a00054003e0003450b0080034031610f0145442e21000800200040e4a5030004d111780c418030039a004283c5c0585d0003811985601c11003801603501c00300071101440340720a800d40250200c2e004000b20403454400c14800c0740 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 468306717 1250 468305467 468305471
    0x207050a0b34140c030a0f050606090c09040b011803030503070f020a0302030f0c0a0f080a030b0f0307063b09010902070b0a020d150e0103021f08010b09060c030c01050a 74
    0x24402001a40481050040810742a01070b514040003030405000c042c150860310303003100e10406050340028078000c91200304598103241d1800c4038040103800c121154011004076450440c2d40f60444940c040c2e4000c0030f503110b104685070580340030282d019003240303000e61000d0b00210035030303d469040241456209840300000038602c010b1044400d4800b103100d00c01541d0542c09117107030540040a07110030b5000881241d016006009400c00001c40c07001d140440d052184400c10307141c4001c444044c00321001884802d001e5115064059010366020030f201e01a1011818840101c1e03800c5500710708085ca44100b05003250410180307110124a44080024a40d10101c0301401c4581e20342c5d83d4a0140c4c080d000008003a8501ca1011550001681e00a800030720b000440003e5040c0742180304000411969000c4407464021200600960400315004081d8049252030442d40d0f9618150040400005114096001c100031540c851140d82d51001c0703d1400407c0c0040707948034071110748198001c10017503452246a44c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 468307967 1250 468306717 468306757
    0x20306120f0c01030f020f130f050109060c0605070309050a0602031f080d0305250302070b0c1c0c0c2907031a1302121617040c05060a0207050a0b 64
    0x2a000080c0d0710040280c210241402c0c0305a100150090414080d0802500303400307028003100030f50140040e2100f4170341082030f601d42c02d28106080c00442c100c0d42010707040055900d000c0c007100f6002060704003800d43c00303000000d41d961000e90460061141d444020000d000e0458450b060180704c0d0090b40c0079880e841c0da007601520b50f21019085261a0b4890314541d50400118407028501981c02503a001030003100c100001112001420100c0b4424842d507008640c1c0400e10b90180101c4e100d850340d0205030056020303c0d0403900007030f0981c00c03102c0f03690340c054954560305488000781c42070900041c00c640c0b2610101c0c5410500c104003210025042907284610f5500e80014000f44c42402030b0000d5000c010244c50070802d464040c07243c007582060315170b0002902000758000d0b07009480e40b052300c1280c801c040005100d0030004010403100c61405c0011207080c00f41c007032102194410400310304440007190540d41d91003007814203034200800380c1e0010340d000440140001d00c000500b0014241c4072802c21481f00c0c40 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 468309217 1250 468307967 468307999
    0xe0103140c011e08090708060c04091503020303040b0a020c0406030602030712110405010f0c08070b060307120308061e03010501090b0f0604210c082b03021608130f0801020306 77
    0x180c0c0b0082e03a42c45948500f400c8070f004080c0030307070040c41d0005800c500340d4040507143c4121515104082d01c451400850002d420401d040c5070b4801d003246010050025107c131840e640010340e89010740d000300f0903040310002e4440c0c0200e00801c00d6500c142030140007400110358030706080c0d000307420403074020f40460200380103022403403418483d209003000c000440394201400c1800450342c200c4007070b00b94024001800e8695002c50020009050b120784030302c045000c0b500d402c0042c181412001e501ca505003584400d03544e0000703600b0810050f4084003c3e03c00004480c50541d031850f1035280303468400c0c1c05529104c00401c1c040d84d07903040f0790194041a40c28400d9441c6c00c07400e203d82807186108242480400e01100d003005103000d030011442a005880b5044116151818241800170504440742c2c280c6400071403c4100c0346c00840b0701e070002e5160904600b00700342e10510889000322100014480000001d00740005200b051145001d17092102d11040b03090740b291038040c002d5006a611521410208589044c2 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 468310467 1250 468309217 468309227
    0xc0c030b190c0c02040b27090f06130614010e0f06060d090c030314040f030b1305160f150e1002030c011107020f040b0303160503303306040e0103140c01 67
    0x94001f520300e010201ea80c4102210707507a080c045c1000d0428041c510400c2c0e4201800c20109004803403d003150703640b122651400004403281c0041406102820b100100720b455070350080c0c0395014900c62092007ca40d039540016481c4d204508034074000744e00d4561001d042c414a000500309a034800d0f1202903840041c8a0303542c88600542c802c00703111a0201030107200003410030400d0754002c41a2000b00310300701c0c0d0f141da800d801e2051038881c0382040307400c07130004100b0076190922010040c901040d01001083d074440e402490007514002d0640185140701207465140c1c42041299416882e034402000f400302d91409a10482d441030a06074490700d05510f5105151400d03208000d10618000c000750310742034a000440042807020b0314161843d01051111031228080b1802c421a540c131802d00b05c18448403c0d4440346c640c90340203004048100d0098481400400b50500d0b42a10b00381200f5507441408016400990b291003030750828002c0c0e41c2d00c9000082000004c401e00e2040302e41d0030054443d2004080300444c1c0c = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 468311717 1250 468310467 468310489
    0xa020f01020313110f0a0315061d071d03030408030409050c04050d03120b0405070302040312020703020306061915020a021201051b0d091a06100c0c030b190c0c02040b 73
    0xa0f1181000b02040000c51019210502d13400c0680141403503e403402c0043c2001072103a0003541e000b0840c82075000310702034a108440c084c21814214541a108680007074203000d00c001d104030180040190050903070704e400402c07543d070245d004003140d07076450303c0b0b8002903142d400030320600e0f130340c603041001040e4106081c0040c1c0301035a50150a00d0134402068500300c0300e460032a08509600c0d41e40e40f04001007030b12f590203490312820544c1c0740941c0d5a80f5515204d40340500d224064011900010418001030b5004500d45810a01c04c640384100d41c4291410345404061503405003015542180410301c102e6004038640c50428004c54002d0a40071040011509a440071540880200b0b140e0b0b03801141c4540c2d030740c0a0600c020080034001403070300c03c503074a0f80c0b50710300d1481c6101b407401c1e441e078100465031514105130440c42e0310524010744020415684c0c000740000324003006200305041030015206040d00d290309a800f940300c510030302c80c2c4501004090049000040c041c0d000d80e040085100c824141104244 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 468312967 1250 468311717 468311731
    0x110a0506041205040816060f0c020d06020307050c010f090c0f03081210030510151203140c0c030703031e09120f030e0a0b19231e0f0a020f010203 64
    0x60155180e560b440d40b001242010030091000601c00071400d01c60401080c484990380708a61501036081110103001070740060100e004000a40b02204c005865581904508039481030700903840346c458103410341e02401420702c0701c40c0310740c41d1051003050101540c020414103401008112003081d01c600c80c0790311038000750201501205d030402c5004580991801c1d13071a8020211110030720600d0b102d40e1841c0c00d107d0540100740f031080d00e40c1102112017000c00d0940300141011010341e07814800e0b40e50042c0c0450702c0b44d0203609044501042d404a407540520500c0c50f00c40d0002e051381c0340e4a840b803070007401c064414010000102c0594010700102400b030f41285064800440741c8283c24002a51135400e802000c600c12800c111076007591606907103aa56909000d0b020308580300d80c0720101c60410200e02404070040004111515003034810760350302d40b1001c00c040d4829082060f0707225400090300c440701250300e00c001e66014000910000a0750301ca809414429999800d50380d6803149410001e090340029245c1c9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 468314217 1250 468312967 468312973
    0x14010b0f030714070b0a0b041a0109060804060e15010608100e040f0212030c0a060f020403030e0904050a02030a140c030105091c11060106032319090f02090c0a110a05 73
    0x80344485003c1c140041214007103690140c50580581d641ca0014081681d1686c225611000004013070f10b05402020b02e144800381401440c5400c0100083c02d60340107225032004d2207141c00228003807003400d800c016005081081204c684800c005d45040044009204010000d0381e900d0114454111a8000b98112520011040440e032100d48030011401c01c500412640b1a4001c1420000d0b000700344041c10541c5082e8000d41600b20503410b000d810340704c01103404448644104020300c006508080d00c64101c1005584c10641ca5846280191030700547c1c07400a136044c403451010700e042000c1040c00c101200709c980b0603034160f80f007404103042c243c0f00c0541e0583e0442e0040b1200130707006160185100c1403540503180910b011144406d08506003242a082000080d031919400e1005800c42c6141c820191011060745c040b038608405840c028401105008000740c0e140c51109090007205a8514844c540050414585040100080030240e108a0340d00c40130401641604060031804100490f20310781000203 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 468315467 1250 468314217 468314221
    0x1203021306120b0a060e0a060c080f0f0403170310360204050405011d0903040b03060d080910030b030c040905030d021623010b04110d0f110d14010b0f03 67
    0x30540b0081401c010b1540995540c1c40202020354503240720200500d031646811710303100202d100f8850040001d40010003445880000740d000511300d0401c4801d0103489030350507501c502c4903407040b805600c599440603100025982011840b0801c01e001103008058a03904918a19541d1035020364600001e8004038026003410502d41481c052900c003043c0546400d0320051425450b01e0002d0b0480c0c2c000e07000784c60701c2d1a60122010440b00c1d201c03002500011036400035414145000c81540061000401544c0076605862034038080090600607100f50010007007a00b0194080b80030010014000502002c1c402d00c610000c182c0142060300c2402d180329040340196251903010400040651721a40c44041940c29014029001c910f515050449074040c08032050302ca00050703083c807400c2d21a00c8420501c2140344c8141030345480c1855007140c0b204005c130400410318400d5503002000070046241d0910580d000047c042c0960f034140c0e400200581c11604130500c1a03604c07038031200d02900074041d006040c4441080 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 468316717 1250 468315467 468315479
    0xa0f0c02030c01140913090b092a042013060e060d1e060e0a06150503040f060e010507031e0908071b080a0f060b0306071d060906070f12030213 63
    0x4240d07030315408051509464030702817902158490030b08030f900066069481c1c4041007004040380e6002e8200d6001d1005000e180c0b580681e20050000c86191100e140c80f005a9411403501c581c0c2100307201100001c40e03015010142090ba142d83c0c2c0c040952400902c10705440855110b001e000305d84900c14001e055982040e00704240034004000c6040e090501c10702a10082c2c030103c4184c040c0360041c0012003859025410035520490903114641c020380ca25044d054040c0d03c10075070002c00c0d2644550803242c5036004034080d09003a8003c0c0064016400f03654288401c014000350903810114079480c44100d2102015103545c0c0007021501507020040540501b04224800f04e4290044884525554005034544c59528010f252900900d403c0454840281c0c0500d1000d0101d18440c0110095094000e0035140c54120300c01807080c240702e0b01c20001940c01e00d10f0030300c3c02d85840e02034600f008409000681c1c0c030060360a264050071444042102c03240001da6800c1c032580c1c800c0c0207507140c6101c2e4942c05240c03d81018 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 468317967 1250 468316717 468316727
    0x109020703020106050d2f0904030e04140408030702070e0c07020409140102070c090c0e010807050d0b0613080111070f031d04150305061806060f03030910050a0f0c02030c01 76
    0x900c05504542d00c508002c40d29598124a814100341306031000c0720510444034007008226a01703e100c4600120042c602c40e0140c40e40140346038869454034240340c60060320000180185801201e904140b18144204010403010000850150029808664007107336070781d0700c0b1540108200d0b46c041e8034000500500005050581048201d1403281c0640a4824400c05085007240c11100d4103540c600c1312860204505002482501c1c108549440c000343c0d071000b100d0020f451644041e050f00c04000f80010b074044000700365402031218500c001c240d03640e508000d0340b102403100d04600440085500c4e01124004051002c0100d45000c4e9200701448285482900c0603140b4005aa5140e41da009200003403640554442c4541c0241d0340da482404581e850075400c043c1d10b0103100800016a0002c010510004c00800141d41d9900c15000c540d500308403c0e01501203410350044218103078004a6a1502c05c6035560020060401c486580d030303c0014425940400700c0d88212896400b0390550410081c1609a5100d8 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 468319217 1250 468317967 468317977
    0xc091e040b092815060b030a0b13091e0c0b0a02031206010309050a080c030d090503070b010803040609090b0a0509070c14070e04060c020109080a0201320f09010906020a0e030c01090e010902 83
    0x3e10b40000e15a0380c1d8440c85141941f084507882c800980d5408403010514250103402d815075100c6000b082840380c80e80c3c4066150790448034100481e03c0f000f8404c0c04000300c05c8040790150221104580e11030358042d802030740d603070043c5000e11104003541000a0095100388212241e1641200080010428503250f1501680c00120054101d000810a40d5603104090080743e003510322810045555a0b06810300c002c030102d060700300304240d40082208000d295804421007041d1802241c1c0000c607a901500003800f060100e0303000b142c100c0e03451820030403000d400030303400110740340540c00e9034000c01840500e40d9110750440c00340181c40520007000c02c000c82c0860b80b10707803d00c420b20300001039500c1070b40e2640802900301c90000d00050391030b414807050341d010b0300c41c501c422054814141818603104240307100b04440002c02002c546541c1c240010000329094010304444c5c0e400940841d0b0312101000020700c41202882424000c0c440d013400400254441c4107000304480c0e00450b41143c9900b0194036402135404 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 468320467 1250 468319217 468319253
    0x6010b0f040807030c06030c170a0b030312040b0612071203050903151f08060402030304050402031b070c2c0403080c072108010609080c091e040b0928 66
    0x414000440d003040204003d00255001301c0413850254034004c0020265618840c9072000c01c504055085960400d018206820058054010a0040160f004645035000307403070000110318168810722003440018036005005410a48900c6c10301c81c05050850707901c448038401c210070005032440d1140403e216001608095038010144c170301d002e0805c00f2030700902c40103403190750000c0d5071411101c0241d8141001c1c50300905004e00038184d01d1801d03800280d12401644141c030302643e00000001d01107035265074000c2c140084031112070340b2486030b4202524070719a94000d08008070080856a480e4892000b98110050b00d4804071100580e01c070740d002c80c1d43c040080d010340b001c0081407140c3c2d400140d016500f054034003104030304104c542152482c01041110107a2014003030081961091281c40c401049204c0300c608103558070007058444510701400302d50880c0308080005161000e102c01c02c01c0c40001c140c00355204d0783c00c072910749503c1003641805c201d400119810f41405060b5500029191110400000c0c01c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 468321717 1250 468320467 468320497
    0x180106030f090503190914010818070b040f0905010b07150e030c010f0504061103160f05090a030305030405011a030a0f060e07270203070f031e020d02040303090b070506010b 76
    0x5083d60b90700b80b03550070000d001c03404c605921082101d000c1e804648a8000d1540502904003002c07ca0300180030500c1c060f04200760442c14880034171404e1403c0001c4030043c0708414a85550755640e4040c00d00c00000c0d0f01030707114010b00700b800004280018000751286642c04c101c0e40b040c0300301c1e00c0300d03080010425128046000c0c081406254000c2c20288a04a086108140c0201e030350306d080d1804208468056010460107001030013441401052000248070054290912000d0621200003d907240e0003803980d174503440114002c0c08410154850050b5014911600090000b50054402c611918900095681e0154030040c2d400e4041100d01412035241030240c080001c0315031030004440c0c02c082c001e03008000b0340d10903842c000718150a0000d01c5040d81103600400c506509044400401e15500002c03203800300768450800106070b550302c42e8281100811194215510089420500c02940284c4420b034041604003000050303812544040b40d10040c0e01001030310b80daa08181d03142d400e940212806940a038 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 468322967 1250 468321717 468321731
    0x3090f210d1e09020a050303071e0f0f0c090e07060f050d02120f090d020604030c060504020f0d050d11030708160f050f010204260715121406030c180106030f 69
    0x30120100c078000c688180400410f81e444240140510080940e0125000394401c00c104001702c1d607002040c42c07030f0042c1c0d0340e800e15902c04541482a8000004030000d405080f00101420410249101d0384c4101c90b040c200a10188800010b01511251240b1801003c150406109401c1601c02d10007824089001c6d28018104205000068005041102c869050280e690103102440808004800035103a640c4028015880c043d07900511410003d100180101d4540021400319641e070004c2070001c90b400740c45201650341d5410400c1d51203102d42c50b81e00200b1007001514020400c040b00701c4820a81103804249024503004a4810318920800190303141c00c80e0803003136400104188140b00f9000348000c00540c845091071700003081c1d044e20400d05120491110118404001e011500310b0480c0d040c000199840100c10070240d50007103665040c2145e00d8944540c000d5150000000e1a001d64404c0d001c803041c6a03002d10900000080c80405000c038845044010400380b4400d81007100e0b60401e10002007401 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 468324217 1250 468322967 468322991
    0x801051302040f03050f070f030c120c0509090c0909030429040b0c0304050a051e10050f041d090a0c09050a110307020604060b1f050304050a0506010b03090f210d 71
    0x40c030903400032140303500311b041244900e034400c1190301e001c0c103011400540d4052944c0d40381000c2e14114819410448141a81807091043c884401c600400700a8141c00392480c00014854035850000d5215200343d11074004a024804008152825106085050413018000c60034056014050110b80e9a0001e010003000c1016402100903060b9059004020340d1501c0c02c4c5000c020088500d90130050107140d0441d80c1003022284402c1c40281400e00307030b07a40d029904c03030040112010710035442152401080081d00203041a604c4102d0b00181c42000503019181d210106201d0319048106c1c0007604040b00b00d0340a000e050440d0780310540002c00714100080798900007218130309641040f68031001680202c0200010701145000d0f641003140300320750b11039040303151018a0f1048005d08804404102011000608004003000001c40054008084a6880d83e40d12960788840d842111068405d010b190300e40e00324100d000410183c80c1d44240d02a001c40c01030707085402031980066a070399240c0c54540e00341c9001 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 468325467 1250 468324217 468324239
    0x50a050904090c082a3a021905040f0213030b10050901060905010806120712060f090f0302190314030601031b0305010602010608060105031e031c091110080105130204 73
    0x84007000d401c45114030b031701c4424408503940800701c055000f80b01155030020b146082e00c9000440700c000703a091801e181c031601014086035041c4072000750003050260700c841081060301c03001401c44800320340a12020f4286156041a03002d099098214030a8050041c000141c0600c001640800450940c0307109079507440010300025020b0b40102e0100e880400240f003a56800982a83d00000980703110114182200c11207988400a00c21440c0080360b40f00940c0800003140c00410300420700e400300f41700d156054100708440f0031203244214051300c22410040e100f00b081d403940318600703038168589010302c0c000c0c09010f0f0031a03400140f0140c1015179880c51992034140ca081a145c1d810015900014251b040860113400c64100d40c108140700c2c0d100c4001000b0700c0da00000c07031058452440401000d10000429000d20314040c210310002501c881040c85c4883c40701d507910841079140144207030458090f002043c452038000d541f0002c0b00003103588006009908202504003c0406108001468240d503003104683d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 468326717 1250 468325467 468325483
    0x3020904150213090507020f1513050109111801080c040506010e030a0501272105160305031f050303030a05060a121110030204121106041d0406050106050a050904090c08 74
    0x40f080c1201804e1000344218880c10f82c1c17201d004e00040c07200006411800750345481c90400c0302d039120555800145030b400348075201c08041d41e00000070307c000081850420101103030080d1040c007400c1981011410321704c03a100e0080c101e818040190201083c6141804080c0100600345070500c40c8403080720000e81c90410110f08114040c400010b180d80000940b403480741004007030200d003030380381100c2c0c00d0202d00244150703040001c030399400740315112001130141d03040c0c01400c0038207844020040240d01850f8000006600c5240314424030301c00b48600082c0702c400f011450141e07a800da40140000341c040d10641d800300307401c03000080081110560302c0801000312401d00c0012911000c0c1013a488040b07050120240800302c00c0743c241075082c903041a0200851490606001e480c00300120203802950f04c496003260b010340700307508481400a80841110710134040543c1e0444406e481e0900014441c0d2140058410004295480318500b400c00000c10000d409180019201c980203a00d0000700c04408000902c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 468327967 1250 468326717 468326737
    0x1d0a020f032d0c04210c030302101b05091e040e070302090903030103022407080d2711061b01050a09020310090807080d02160302100609060f030209041502 68
    0x7075160760041140c82c045107050b00814855502c0c1091001c114080c4003510195051050007600742881640d0075030003070100110140500620050106c281503001c0340034403154041c0c1100340100c0244028164070624401072035000981d01b8030501441d80741810740251003a20740d40400c1000d003920340000c1c01301c440420405075160b012203000c0045041144070ba070380c04400000914203541c07541e004600510300b241400145104000c5d1b41081640e0540184e6041c150002ca2a03138450401440d1280101000c20907607550b818050390403082d59501150560701c080d4094a402c00182d0040c041c0700c0941c001d246840c6d8021495040810b18000900c90f440c420100581c010840391031038018107040042044042c07a020b03040c420b03a00b020501106c12910350990000c000c2e0342d9030503811001e500034040c1c082e40c000502101c1902c481030560010f02010741800004e81000b070f080c1e9441004088400c140329200400e00048001c03c09403030140c51140e40240107040801081070140c004404a03848030f2110 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 468329217 1250 468327967 468327991
    0xd060b03010f0501030207150e120a0206040c0803030907050f01030b04020c1506090f0f0a0902120d300c0e03191709031e0c130e161d0a020f03 63
    0x10400d0003041c06800000f44002c0c00c0031860420540c07522821000001c9814249a4554140c000c0350007040050740c07840c41d90780660645031149035400279154003058030240e0b2005034103140402e40c020080100c1c0d000700011402000704078502018850004000c0e001c0304d0500d0b03a151f1540704107840d00c0c0001d01c1ca092064010b401c003410070306008011480043d2090b03005106520821804100b038083e1150841d140b2040c890147d42d8070b96102020f0082041d00a400414810b408880b040c070008a85600d40d00c0c070384881107980707660100e403180904500c0c03010040070365043d071144a1074520707070207140810440c0c50a19100340101000c00d250141701000e04030038205050180341071006002c688205402854803e80c500451140000d645200b40200f018140d550303401e08800b00c81e000c02c52880c000d103002d0003101c00c5507240e44c0018001c19100c0109115805102101c240900712101480262078283c01c0c0e610035150095420286600d0003050460f01940c00c2099050b62035440c405988101c482c00343c1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 468330467 1250 468329217 468329219
    0x1206030b0108010f020f07150f0207081207020309010c11040e030415030c02030f030609180f0a05070f052110110405040b010801050609061c0f1515020a03140d060b0301 74
    0x9043c00c5800c1003e0051486205008411031034080408844a8130307008080e0070440100341080748010440d80c0045001948005101c008018402003d005c8800001902d103103540e541d40c000380d86900c07404030250f00041058201c100041c8002c0075000d4072500103440044c04034200035800c0d01e198001d4029005606251445901c1207030301d030044821400540c0b01841c01d001d40d40d12440c009010162149204034840c00000301c00c0007031914068031004040381141c02811508a8a40d19880555416a81b42c0210743d804110b503510030729040201c880103005c1c1c00c8000710981c4080401c080000c14402d16005080d0042040e41003405102e086032009a405030b40c580c600070422080b0380c00703407800c00e05224800c401003080b591181c00751000980c0c16111540d40c0c641c10b490390008000411000e8a0191a0110340e0000e1400c82d4800100166801c1c0380301c1000f91100501150411982c1580b001a8004550071002902c98031a5260700c444400d0180e051070b101e05540d4050354030035000082e242c1c50101c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 468331717 1250 468330467 468330479
    0xf010509070e09030a090509090a0c030803010504060504090b04140f0d0504050109061707030c1719200d0f1b02061005040207030e2b0f1518060c1206030b01 69
    0x40e6030f040750640d0300644c42c1c103620341c1000d400d012461180034884c000801c000742075032006120861000750b20450b218a81a00c81ca0443e00c10b41080c003d59004900c0c0c400d0105a80c10301e48108503607581c1100e603000c119540c5650f0803035820b1802039100c0b054061041c0c2c0340290042004048681081c6854040d00c41e418440010030a0401e03900c03940030099042c8501500b140405046900105189004a240c3d124a001512030440300d040d091561180d0f1402c00091503000f5908554003401d1101c00d018103c540195004800e1441c40d5030704120a0411030354555804a0340040c554134018440481c01241c0e5402c02c0c0c182400d08406840580c1003038007088040700c080c00c0307138801401089030114201121900c00910601205031280c0c0120a40311213910000e1454065525817101d01341c1a00505103240b92200d141c0400342011a00c10142c4000f4115500d25401a110b404452078a02e03900301405880703e2024020f0825031505000000b00c00f40c0041000c0c0c002c25004d075000d4000e80101303501d006 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 468332967 1250 468331717 468331739
    0x506040b09040b150a0f09020d060e09071413050403180608010f090908090a150206090106062705030d11061312050c0f160501080604050603030a110f01050907 70
    0x1400d46124000c1c820801000544102106410000704d5854040d0195140042078007410f0917000004c6100c2c003650000707803620154004107604010305506010b469602c203940c111042049d00d80807003941100724180700e014041e290205120704020b102140341c1f0308004103401124000d4a064000500070500048202000042d19004000134548540c43c1e6241c912172016103207c0c1e0088920280d200c0c0b0038001403100400a40b0b000080c003c1c80030000740d0b5101203a180c6807201481c120003501603c0d002500030076040c072460b812902503454112103400303250480400c410114018070b80d0b008648001080c15101080f40204030313266601da00722544e200120741440d041d40201101003425a01181c40c00240788000c0401651201c0c3c1022500c8426000c60b441c144151b0046e500b030030348248c02c0400c02d2001544520002ca600a072507410203502d4040602058503c2181d649406074810441c104499128481d481301c0403603401c00340c48100444a070300c1d0f420340308151440102030384104424400c1100341 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 468334217 1250 468332967 468332981
    0x1170a020105030613020c0d020619020a092c04110310020301031101051312050a0b0906130825060c020d0503070206060405070e09190e0309012a0b0406050604 70
    0x1401828400219400204188002400c041c000d180e007030700300d000400250f0183c80010000c18161510b02e244124025600c1c0b208a030900e1000d130800e030581ca2000002e100f04c0700d000f84250b40d07110b80642081241c660243c05500100d80c0300b2030600407240c0d401014811507005a205903c00080007002108040c40c1451b601c0c4010100e0b407041004000048200b22007441001080c20815150400302142121000f06ca60200e11602106c039001010000041809020300b07115024005003501d03421441907403460101d80c10b83c01070401c541c87c00c004c80c0515000e0f00154006002c1003540c0c200d101c00c0302d03102c4102c00ca4106c441c640c481002031110741c1c043c010a50841d586281050440c03500800096071230402501c41030240340d948001c91300140c03043c0c500c40c1c2140d4000e810582c2d5402c14924030420344503c041e40c800344074a0724030340800c03144000c411525940e405a5840d15030001d6001e90081c00405800707016041000c3e807611900081051540328440c6024020010781ca16004051005581c20 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 468335467 1250 468334217 468334259
    0x4050d0f11150414190204110c030408062212030917161e02060d02030603010912050a09060908030403080c0307020307080303010e0c0405060d0506180109270b1609030b04030801 78
    0x10050400c4030010301003141103c06c0e01120045030040041400f003d451141540d151428000041d001c10040400a007417802110501d00c4801c500030b841000007620400c90000801c0d05140e1100702040c544a500004103150064850022400341e0841750321881c0d012425080b149000030b045103050100880116a00d9588203064051056039a030006415100d0005500c0c142030b404404200607071001d40c84140001c3e405288145000c40070b03000036240340c000039503060005402800208526104204a20441d01000000d6050508640d10591079812807000b9004c1d074071003408400003580d810443e8400400120380a180d40f541402c42907842d000d001400c5900d1010100000c00c00794a0340b001302e039800b800c028400140d40c1c98800005070b400d8076003591307010003540400011500c0503d41e40084210306a4000c007403503440c2c01103a0004404119507002d020341244000191001c1d07098a01c8602c007100a14017020790680700e540b8002180001d9406400040c004801480060380b02c060316120454 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 468336717 1250 468335467 468335473
    0x9040c110d020c030f0606010806010f09050a0306020909071d0d02030a0c0905010f0f051008060103020d1406030f190b101a0901080c09030a1b08031b0c0904050d0f11150414 76
    0x41c7c24400030301030500281c41c01e4100a8036003e003002040c400c4050a000e0080100701c00c50745556820004041e402c64400c1a10604050001c01d24181c09122045118009206d01c40c01c0640400c08108101c1090603041c1d8150145481030b0000810125055000d405071100005455040030504c0300c0304109904501c0f01a8100c04091149681d0311940c23040580c1c0034540400d40d90385101c012000707170080700c0c44586020b00307140d8825050301114001c90b2140300e09130112045900307061902540e8211801403030b000700550360700301c0000c9a00d808146500c2144402c82e2145d0594074041c91701026081500d100c41c210010450301015070380030701425004500b0b000242d040000c81000a91181100f05004000403120484c2c1c03e0039101c40c149250050000070140ca45031300c4440145c103985180b240007a1424051500c14210030703d003240006010b00e81010050040b158080740680f1000d4911031100140103540c204018081c90800614010078000380c1c503030005040c1842c2c02030340d2046504c14007295030 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 468337967 1250 468336717 468336721
    0x71506080735030310080c01030c08060409060617071505030c030a0b01030b060403050609011503050d080402040902060a1d043b01020a0906090e070509040c110d020c030f06 76
    0x1007030258400d01e180300d5100c82100344100b1079201640c8488950b4040c4102e000100802006406101d00340c0116080902a648403482c66030045040312400c240302c0001c9401c800c04900c4904013a405254941c1c8200c100061050b266201d488408400342c031210040d500c25101400311082d2403040c41218801400c101d821070911110712104c600005080c0718080d0354035100600c1d180c3c840c2d0442210725501505042e9656201c0c1445919858200c40094070356080c0035540c0d00341c1241ca00d0b10f0342107941020250104403810701c0220b0719088040c00503a071090f12903144501607590000108158507031511615151208200c0ca40f190400c2c13041110f00c03862900b50b5881d8000568114402c18041c0d0b02c102c0340510980140080480001c081e01c07a1031984041244020107400a00001c242c1d40c3c1515140c00659482501ea001048129441c0c0d0011300140100a074500305608040400301480c100301c90400984624989000c01d009180c03c010f078006603601180e42018480301d2514078500000d819a8 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 468339217 1250 468337967 468337979
    0x70b0f0a0c031e050603070f0f08011d0a0305030403120f020c010b090405191a010816140d02090c070614160c0f11031006090920010c0b100b0715060807 67
    0x30300c0442d01c002d09184d100da000a466680030701180c0040c107640d000300c41d462038a410240b1f1501415010b0344005619010300c60380002c071156550340400c0c00d000c1c02428940950b9600f20b60036040a4001c5040c045561200c0050401d203000e00c645000344440010f846010079810982540c0002044600803d401e03002e02c40407803c081a50900d600d101e0b00082280100c038500300c1c911181148010b0001e044c8000042151880482c8800c1c00321f046107004845207484092824054201030b00386943328a03c6120000103040420207198808140d907401c1b410000385407900c02c29222003010221054134030b501007042d01ca44941c0c07900164016807130702c01417402d1720b540e8098030b0000900340a89100828024443c142c7d4040020106020010702c0900c400340c1d40b540c09a000e001900310031204901c8080c101d09403c1c2541010110b4250140d40d1000d02c0f40c51525080e0f1140c8010304000000b401c2c1c05400724540c0030310801410203c2c41000322030f504414103c15003080700c015410143c21900560030030442 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 468340467 1250 468339217 468339251
    0xa021810090c020a020d0c0e07170f0712090605060411040b16020609060d05040b010509040b07080c090d03090e0c040f09050c07020a140a241103070b0f0a0c03 70
    0x1a940e000d20700141601c9690400da240c0103c0420095000b822901da0b803040000d5216a0000c44501201c0713481592200030056403e20140d028101420041c0000203c044295000c816008416801e194180040740c4200d5800d03610454800d5074030700d40360030503c903042c00c2602c41d10881d82d2540b42c47c81d061504180b541000c40c8645240c0c400b00540201454041d90307124421203170308000007880c103507490108a54000203080c01700c4058aa0588107400001c5508000316514451540201140c4250740c0b450001d8940103030240c40d0f03500d214014030051146440f80c03420070f501a8020386070011420724208060f1003035080207044a0105101b403104005000302c00ba070000a0703d030100000310740c59940d441080c12a000e51300000e513204000d0300000901c040c841d0ba41ca101d000d816108407681d182c03103056070340741c100b540000209000d00305aa1109603511490301151000c0032041500e05c2c140c43d5444405020348213546441115440505100c05251300d8824240d417091142403d120304914000c0b2100 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 468341717 1250 468340467 468340469
    0x3041b0503100b0a0e010e0f07020309010c0b07020a082113240b090109050901051005010801150212040b1308160308210103060e010606020a0203030706021c020c0a021810 75
    0x10034152183c001c001240d460020010260070030007030070320107503a6921510401e40015580b04000041c19004a00c4161021084844a030b030180c491103070602c02c50352003031540307400140500110b005d0302e4403c50011b006e881c000c1c0f0400c52018020705d101502c610145804000180c4600f06496403400300a0020340411145200020b920301700100c034501e122000b01c05010100c04140d8004490000424000c910b540541d002c1c000b920300030040c0e0b0b0741d04036103041e99150600485021894180c010001100480500032103500ca070300c15680202c880c0741f000582c0d07400c86d410060411502007401e03000d41001240d01e03001400100b000300514412141c00220000300c1d404041c0420b10b0004180040c8901c8820382040c208907190303040855a5a800e00034010460301d0f845425550a080d400150140b0005140c51a103400602840ca80001c540e1100700075841100700c440c80030880304020000f4000751025050010450020b800180c1c2c1c2841044404075034003230481d2400380c0c03030300900030707051000300c5100 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 468342967 1250 468341717 468341743
    0x19061815050c0a080d140606180f0f03060f1614190e03030c0705010e03160e061908070e0c0412030e01050408010216020a0e090a0b040309030f0803041b0503 69
    0x42d03035860071807002900303085012601400d640d0340018120441e03a819801481142c540501c60503054440c0004c2180c248540c00000d0f206200c80d00c0d1107011441d01444a04050000500e0304258514400110341044011504446101004010804401c0e20a0a1019062402c1c074003884440101d012001d228050819a0b6202c1c0380540c000c071308001d000305030503696040300400712900c8946800f0515550001c3d40261800207034240e950300340c1802e0024141c03890900100d8426885401d01d00d940007846130041016500c60041e03080703402040048a07a020190003000080c0c0300300c5040c141815034040c400362540d81300e104104400c005400040c50465907a0f030b45840c4c106034414484004072214000c82d0415485c9500c000f450622410080341c0c00b03c003031403084e25100c0d4134540e2805605010f1104030f54107096500010340d0b21000659024209074443e200b404d007020159100c0e00c810350381518400702121100000401e100c1030100361400c842d201c5040180e6210040d00707140210ba151240c80e043c0d1 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 468344217 1250 468342967 468342977
    0x602010e1005280b010f03110d050a0603060501060206150a050f0d02030a0c080a02151204030c060906050a0f0b0306010501270e0411100305060906090c0919061815 72
    0x801c25046608424000c0c06207110a5407408682d10f118030801025411411404070300724282c0d1a1180e4000e00800020355030590020381444800c880700c4015010045c002440385548072004000201e661040501814113940188150301e4401819200b5803000b0902d148030b01030f542070800c403540e40d10721501401c10f41691000709108483c40400c0c9895039144000f032030380000b2540424540000a200e21031903000f15000d1307a00100510703001e01d06115010032040002c0d05680002c011078052490b00042c68070414001178244082e480c5d6404441d030039140c8019117034076905e80d920310b1403450003117410b8520120043c0403035514100c000b0b40910b4920107000f0322081c1030380340c9507084032040c1f01c180000c1030454500303800792506141000f484a02014121712038182820000311051091103507034403454014068170502d448140410001c1c56008202410250b000c210620940c3c86849182d80440d0b07030f082610310003504050000e800001c40c00100400003203101e004000d0500754084110303489a0078145 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 468345323 1106 468344217 468344221
    0x31b03060e0109020c0a080711040e0f0706271403070e0c043b0103051c050706090c0305030304050f0115050d02011116031b0602010e1005 61
    0x40584000d10741d801400788100d103600406050820504a40c8820400d985560340c55019000468650100e01c4041080341083d010306940c0c0080f042c060901c0e65010781589030394a40a01c20703c0100030102e41c8440a0711210070102c0424640e20341c00304221a109e000c030301401443e10456502074803d9480000700c0c2c80c0440600383c0a010340b140704070318182c40d0081c1030005600c00d00300304164009040d4406400b8603029006200716076100080718486d80f440c00e11b1030a02c120b407013055031009118220b224582e40d22030100c843c50ba500079000105030095007008481d1036884e420017452480004140414060006005003108028000920403200501035800388888203101c1c03a60400002408030006602803c0c880b00f650003c1d8044506002450014424040c480c0e4026140d10101a031521001c0980540f81005030000c3d0000303000c02031034140c01946d80c80543c4407800f1115a00c1340 = true := by decide +kernel

theorem cover : BRFrame.Cov 468165467 468345323 := by
  have h0 := BRFrame.cov_init 468165467
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 468165467 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 468165467 ≤ n) (h2 : n < 468345323) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
