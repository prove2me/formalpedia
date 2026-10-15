-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5509
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T16:06:08.679913+00:00
-- url     : https://prove2.me/submissions/f729a527-dde3-478f-baf4-f8bacc22118c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 990647482 ≤ n < 990827338 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 990648732 1250 990647482 990647543
    0x6030615091803170601020a140c040e010203060d081309060303030219020619020c070e07200a1502071104150f091503060902120102030408091507050606040b0d0f 72
    0x1025400b4407a80d8030002e02c5020707005107491041c83c414010882c2a03100f00301454007146c0186800010200701d0315480c0c6d60360b05c041c8215005500b80640d80000540602c00d6078425003025004003aa00f00b983e030303428025400450800302c0340182c20000700e6403030741c240b01d0100610b00c03070348005030748072841c245000350318001c0d101c000f08648c0700310b041120004404000d0240d03480724102c0907842e4040e00e03000e80d0034a881600f1040181c000c0100b04104590b120510b155180300c68801850f0441c0410041a110580420090400300805821910107003040d4000c0010b0340c0241e118007400449a0001003e07070384036986d052041440c25406004c6280042401c00050241610801ca800260b135224000c140c9988400f9180ca50f907900e000d400d640b02c0301030000400030114021581ca290514101c0707025003002c1403690242122901203540b00c21b08400b1200c0c0690400c1c014034607541c805007004043d2000c0d60f05150050402106040011400a01620500d2007240510040514bc04442c1000c810100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 990649982 1250 990648732 990648761
    0x3040c05040b0f130914010b0405072303180d02010f050606180906181920030a0f0209030703030908060709030f03050a03090209090604020a050103020c070512010603061509 76
    0xe16030b5a030701d1420780028018140d07081308021880994481c010000e50700c01404101c504603c42c224244107500c03a10010508590800503a11010340495078a0002c014400b42c0301c0e01c0c030365200c004000282c09144e011a040c1c400702c81210303841c054107013401c0341607441c000541e44a9801c006c0040d2503008003544000706a030640c2c00c01e039400c0705244220000d2081c443c0030f2412600400e45039191440b01804248001c51041c9090070000c680005200fa0483d17004502d600d00341008021900031104141e00c001c03404007160031a280c11178201d00070000c1c012200c080540c2000f2032401ca0320180090303030065000740c484a02c04c5180481d02801c04030b00800000400c401100c0602c00103040c54403042c0c410390980703008d80c3c0320310714000182c00400489101a500151040030820340450000d941c40c800c9100795280c2c80d2050365140154180e01594526404603084500c0034005410640007020b0401e44820010601503601c4d1113070340858040d1065000c0c0120b0b0407070288040c00c00c070b0041c00f0301220400f = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 990651232 1250 990649982 990649991
    0x50d061a0d0b070801141c110414100807050f10111606140c0703081c0f060501020c01080705030a1e02030a150605040312260f01140d0f080702030a12030203040c0504 73
    0x800901f4001030079096424a0840e02054002c2c001c80c041c0c0d0082007003016108000212542c151011400c00031111248103450310000843c0121000c075603841124070103003000c1e108030b0740007041000c41c842004070841082511007107049013400404c04800b26005041000340a41e0a041c0000d00f528803007100b003880c031907040051030011100001c17104c00303c0c1d4100180d80e4842141885000f15210180300d01c03048541001c10303061000c00d10381e00640885900340c0071903a103c0109001134400003011a1603c001c19014000207184050b1500001a5400d1448170140801516940c810480c0c00a03900305205a42e160100080d2100e088400d001074a0325042c030303030f08040c0b5581d40c040140c203201040b0020002c40b50b1001c00c400600d092000c00b5410081034802c034a151401c00100092001d10a03051001e114012a0391203041410002d40c0003070300076020982c02c011640342c00045500100702240c0500c0351706282e90108903c03410000d0114095540580e59007000e003422000550326030440c070b02c100c2c42e2 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 990652482 1250 990651232 990651269
    0x1401051617060303030105100225151b0b0604090f0f05060606040b0a030b0114070f050601140d060c11030310050112020307020309010e0613030b010306060f050d061a0d0b070801 78
    0x70175681100c0085420220f1554125405c81c10311601d24040002983c001c85a82019500e901b00d020688d6020086601e40320070001c070445000c20120000060040c2c00c103041c001042e42c0403031456000401078004100c5030169525002d503c480e601084c0e910912a003054001c220060042d5600084115080c83c1454245040c8120a00c100a40071052690360525a503860b401190079920b1500064695074440400b418040c01c40881c0c184101d505000b900000f1489008129408011060140c18450b0100041c5e9902c0020015414400240b1403401241c076501981000154800c10904e850f031000245040000340c009a01102c509150310f0041c0b0402014503400401c0d9910507200340b034050248408000840c07034510070706403070200d6100d11403804000c0c0980c0c2d5204604980c0310302001c1224030365400b1034607590300c103500031141d01c0a4107560080c049281a0441081034045100e0f880c140300c042800140c2a40500408607508901c00c4100600b0903040030071640100124504a401c1404 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 990653732 1250 990652482 990652489
    0x310f02090717130204110a030e07050a060e0105130504021903050a05040f110f03010615020601120302070e04140a0c15090f12050a05061008120a1704140105161706 72
    0x38010811203c3c9100f6249000a40d60b0307641100039488030f4020803684e9444440c5004000d0100d25010010901c10040001614213180c50a10f00300e903120799460030754402c900011034032948410f0145200c04050000400c8643d40ca00c01401003c070701c0143e0324202280104042c042c0c5070002c1030740304d0b664501000c01c008900501003629000d86c1c42185402d24800110001f000b032030131070700103541641c40c01038080b44081c900c1d4480d40e0740d902550219011681e0742c0904c81142040580010700681040d4001c01c01081c0c2d000441e60054825070041d070003103180d40c1056180c038000c1c1c1c0b4241c4a0944580b410400c40240100f541d80038440c92500e00c2c204ca040a0981344900c0d5280700d00d8a41c52a00000602170050a06c13250b444c065108066442c58105500810841c003a58083c0513107034094a10324000707031161001210901e4400c1c0d110000490403000121003400d400a0003560203502d10440c3c84c0c0024400e11030140b29500c42d40d05915215240c0b180203002c80d03000e4050a0441c0e9110091055070354 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 990654982 1250 990653732 990653777
    0x30e0f0d09140612071d0f0a03080906071502090a12021f020a0206120f01080d020c094515010b03131205030f150108310f020907 57
    0x3815000c0d602e90350546040801d40510500041a5001910a041c000400e5110745140041402c14040f0030380d402030f000c1000000504115519800301c0c1c02103007000000d500c04050542d64000814060400905860f64800c044441190740c603150360008501100b072510700c41c0300002d000c120750040c110030a540d01058a0491810480400c00c080545c1e645409100300548580c095000d00007584030011801c0c80c440c02c00046c2c403c0ba2500e4101030020401a1300000d4008140d604c0d98000d080081d510070a02c4196034000d402c0c0745401034080c000d070f004213580b001a0341102072880c40d50030818400c03c0044801d0440b2403000039054009100c224551049101518103480d0b000003055600d4581021003101a50070101c000d000042640041540c6508107002c0c1d40708130036001c11030381e4581d07807622024105803448058a000ca540b100114050701440842c003010032400c0d006c3c10340d204914403c0a40b510300c0c4400102c5402102a02140c00c504111480c20342141c540d05191188580622809003000f = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 990656232 1250 990654982 990654989
    0x10303020c011116180f020f070609020105120115110d0e040b06090d0f030201050a0213140109030b0a090c080601050603071b1a0a0b151c020405040c030e0f0d09 71
    0x9059040090380042842030005072130010901d551250f03655012941d5107004424003554642c41d00c0c4400784c400b0102c0c0201d03041c400c1c4582119140185a540348801810880c0c010782c1004804e1140c8104e60990400300307400b070104119101e00c4151704510050941905c003031682c5068105c8c4212107801c0b600321200602c2d00408850102e03143d00b0030804500a802481c020a5100308005403c07810f021101c3c03041e00d8058000e500030311559503540112800e07445903800541400c8040e080801114040780200541080140b421006650352030b16030303156400082e20022542550380803400704000c282e01e00c0c0c078004d0440f1009490b50358504030000340c4a01005001c1400c0c424509070305403c086c402d52840212542c0101d00384070105e0901c0ca0301180350001c0b20515003881c644101c070b0f0118580380c00030124442505903503920704812500c651200c0f0104410985426400340400700d190b41d0f40f40581c0c05000d00c1a500000e2060020003064a03210062880e0008c3d600680d83c000e5102e41c3c845040d00a9 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 990657482 1250 990656232 990656237
    0x30105070e130b12010204120b0a050f01050103051f0e09150108100207080d061401030e01020315060901090314030c0d09060e040c090929030d1707091511060a05010303020c01 77
    0x120320f202c010031801340944002444652000402044d50000b845510a1060141c105d0701c1c0c00d603841402480c22070b4000d80312190205d0001004009a40c400c0d0007442c2e000f100c015040381c0d007441034000454a101076400c007101c2002070504000c03410b401001150b01c40300400c1c8003c100e552405404030385440b0050b204110340b035000118001441400300c201e800d00c3d2640c9a0401442c0d5843c07101409840d0740c059114002400d00c0481c0052001c14001e030381c0513440000803404000c030032004002c9903902c20b5000c2414001905c030000302180200400301d032004840030196568440d40c103a103500700240c440740d05051108088091158a51021441480c0c6405031400940da0035070482c1a0f40d5001c04d51b1002094a082001244036020b4445a50007002111800c14007400700c2e080c2055120501100c4090000740300071641020b07032150729681500501c3d00e003025540c0c6902c84c5072078100d4919292030800418882c460100400c00e0802c0239540c49103c81004010650455400944618101408604 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 990658732 1250 990657482 990657491
    0x1407141e0f1207060f02071703270a03050114252304060e04110301120303110408120703020601060201140402061804060609060e06070f0b04080412060506030105070e13 74
    0x10b03480c0c00d40c07800c180c201c6800440728060382c0d60358000c1a4070b544280e03610050140c130320009239030001110041e003680d450501441c1015018002c0b2030002004c1500041d00000300d18864030540c8034501c1000155000b10300110304410030b40751100d5900d2026009503448016a8802541c0080301010410068004e02c1c208506c7e41032130003081550807003040d4081e000e6038001400203d01e6013001614003207880954081c800c0c0382d040f00d0300f420140801d100b014110b0240c0f07044100003d01c81e900240340c595011441604040c1c548604070310f49441000551820040010340c01e0038103804202140c010141751009200c078000070341800031404000380c002805443d0110b42c1c0152201964070b41c02c2012006481044603580c0c41d44001d0646940340301d110040b0311034242d03e40c40e500b0b110007111a40e50704815040c0c116909a51052440907008005079140c078070600c40480e09000c80b05040300b0301c0e80a620003237602d0415108050031100003504140030b03c0000d40f00c1c05415218001e6000304060b61003800035 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 990659982 1250 990658732 990658759
    0x6031903050d15030b0f0108120c01200717090604120809120601061d0f0d02011101050a020909010503010e0d080a09050f0d08070801180b0402071407141e 68
    0x3a01da01456103a60542c07800c001400c0010421015020200c074010800030000741c40d041000c1c01c0245081c001d02116400052030540039403580030003007107800da41d0000003c40f841003242100b11403d001c42407140090000035184c0a0244001503640c00c1c61038440c060b403510070143c0c0042d1891080344548540c00304009181c10a0040480a03200000ea002d0002807c000c15440c00e161602e100340140004a8251403a4855a1680d11500c00301040e025208808903000d5404100b80b49070100340480c10070a100c0e240400740002030245a005000041000d44c1f60070071501008000780f0143c000c1800f0784c0c5060203200115500040100c3c0504e141c0c100703903205440300a05070001e8840014040c1c0584102e68071056403050010b41c182084040e07580719481d40d128a08100c480c486d080c814260341c20034003d9244000b444550040020941c0280018505075860f41c44250902c0e40307520100a580007d1420070013400850110004c265045070b41028860210000307601100e0b840301c00318000d81550304480d = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 990661232 1250 990659982 990659987
    0xf03120c0d0c0804060c050705060402130e0708070303091d07180b0c06040501051b0301031415011e08030406050f0310091b1e1e0c0210091a0306031903 67
    0x8441c01400c1c640c09002d0b440d012600500440d505682c211285481c1904c0c1c848450f20880503565101c1c0d00501426498640d80c08101c074807090446001c00f465540c1e08030a000050810546005000344400341004526604002d0121040c99014500c40345511111120281e0b0000f02141d000010342440180482c1d481c803110141105038101c1c1f074440e0750005e101500904006500c0b0b21840c8100c000b40490b940d03101080c40c00a22814a520980c08140014400030303800402c600c0c0d4000161048030201503001d80303001c440c5a022b80c4400d690155900e410004c0d0306125040d000940100d00003146042d2a0031001803541c40380c0400c0103440d080100100c0d900005900c0100c00801640f4018448121002050901d10784801c0029002c2480c0c4811010031400e8a82c180c01011540c0d143c00304107001c08402006450b000c20780c18400c0001d0400300c800142d482d50100d00c0c0040d4290b03103a0404a003804503e402c141c10101030807002da01e050080001d80c2d54000303031104810280c4401c805420429103400d = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 990662482 1250 990661232 990661237
    0x60801241e030f200406050a181409090c0a12060b09070521010e04060b04090c09020c01060f0317220308030604050c210601050408070e090c030f03120c 67
    0x8440d691861007201c800c820b0b91542108842c006640420000031214084c514410780d030004040402203414441006240e002d88007820340c044a6040504210358441c02c95504100c1d01d800200806000d000b410f03d06040503001d040e440442d00c0014440340202e130002070700001c0d403031040b416405021242c2c8d07420007056030048a40d1004c00b504a1030541010318000e820794001140008450185491450303144048000450485411310040b41c9241c0312510790401405078400c0a60304180c076a844440050344401c000350041508400c01a218080702d42990701350780c019440612a85100b4809002040340d518041d0b05a51003424000d9452003071000302c05002602d910640c5043c0170a1600000f80043c01000b14803030031040b5000c005035500c000e80c030798042c060001e03000100b030350b06000d40144441803099150000e4050400d1410907503601e200903d0000d4a40002802c4800c041c01d002c01c10798104035a02000304118003030034404a000003031a03524040da41c900103071500803002051001104004 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 990663732 1250 990662482 990662507
    0x20150901111507030b1e130237021b04020a02010b030601090b011814041e0e0307110609010c170904090503090102100218010e120d021606080124 64
    0xd95412801480c05100034920440340500400c1c14200a1a001d00c0c00c020b004084129504450003031b641c1e0081484055981d00c648901d0681e8204244004860751840980300c1501e1384498500c0490b1500ca40030010742c1c04a000e0302554410b04605501d480014480400420291001616104c401038101d024104201d0140c3e01400b540b4004291100907030000801c15400ba00e174009044c0b40507884c60081d110500c24411144081801c820081c030b003c6c1c115810800790f60000c0100040310382e00f018201d075245c1412003c503078000280346082104109103803408a104441c654140401c400c002b17080c40300c6c00040107000e19680c03180030090300d1140d400e0790420b01018004019090441c500246c0ea58012104035000d442421540c00c203850090088440403e02540a414010402d80042d11002c0340501c07034541c8002c070118001c0030103004202c0300d50500410342c002c0120101083d80c0405c0c8102c96000360081000c180300501170b4a00d85500401c1d40c0504100400c80c060f05020200d580e03034900c51 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 990664982 1250 990663732 990663767
    0xd1704050c0a061e080105010e042003130203010f0e4603020f060118020a030b041505100e0108060d020303070b010e0121170a260420150901 62
    0x401c0880c9084d804400600e0320040c1c02040500020001001d0390004000d20030180028441485a01c00b81020740002c9a400c0804200040d011508503114815402c22035414540e0800456003406601e003d01943d80705d04080441007058201d956850b90300c442d0807040802d4480a402002d10442050004200d0111030b0034401c4000c92a192010b840503001581040d00148a1240e0a1029140c04102c0314103c403104030200c000540f88640d8000030f5004241d101d400c3c036a540900d0b0600d52224090103003071b80070320040c10305424181010428201d40103041801040542c898011050b41c2101c80341380c00070340845540301d0305c030614400a4a180b0490384010600001000005908401108428141d40b052240081d001410504038841290564006801040d14041c0220600d542100514920030645800c01c40098030440790480440f06200300b45002030f184040000b4440e0686c42d140d90751090301c00d047c003007264510001c0e400e0b014420035080e00720000035509003580c1c0101800d01010b40f240c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 990666232 1250 990664982 990664999
    0xd050702331f031e1a060d031112041509060c1a0c07080a0e0a050102030a050f0d0b0607030903021005030402130b03011b020c120604170d09080415110d1704050c 71
    0x30207030403e607001101300480e5400c1a1484525050824003240c0f8840c0101401c104a8204552412541d01c55184c100050a000e015105206220390780c0041015002882181d000314440680052580d0b4455101c1010003a05201d80c80000310706940c080c031054580640f03001d0507112503112a5203132281242c014901100051700b030001580101000428060840b4a04103050780d0700010380e124858040c220b800140708200400c01d00310314801810104400c00000239000e03a245022035030b150310003071066001c00e0020004100710301e001034800182c20400c1c900541903040a0380030610444015001441c01d07a202c0c0d400c041d550b00c0c2580100041c560b001c0303d1402c0d0700b503140c6019443c0c13680b0794840c90240c141503402c0103880c180043da80b405150312044507120500d401d81300c15626000180c0e21050243c4800c2c000c404034034104064405000800b0036181000750842000d0555421400e034111281c0010001400c1c2030f4000c95a505000c0406a83c48025511454041e0420000c40f07401c07030340000c52 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 990667482 1250 990666232 990666263
    0xc1508060307140f3609010f02040f06030c0c06061508090307020105030601110c040525030b10050d020c0d021c0503040c1403030d050702331f03 64
    0x806a034003400e01901a41c2100742c50301c0f4014007400f1440714564200941e201d0300d44550801422110500c1c4409440740307140302180f4001c9280d50036034159400420302041c14000791503c203214480c41142c00003030441c03400c2d00d418001e6581d502e46102c1c0c3d10515a8030000d49212901030340e040e10b54180d000004100242e10340e90700c01140e0410010003000a500f003000907114110000031105c1c019016107a0f541940d0341c1c40f004403021a00c40c020010715000b1088203000940f942e018060040001841e01107800b800024180410300741a02031300100760501c4034078010f544440c211000d20134050301d0507950741d903020500d030006403190300c1d01d004c9244101c0181040640e404240c41d9512410100c1c0c0840300780b440701c0304480a00013554043c2140b081c5840801020a24440d40d0000d0000542a2400c02c0802039001c02200e404032501c3c4096005021000b1480c140c2c0e45056071003403114105a88a10400030791081c6800340100700201038098040381c048111451601d0000961340040d410b03998000 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 990668732 1250 990667482 990667487
    0xf0b0409060e071a19090305010c081e07321308010b19061b050a200414010b0f071401020723030d0f020910081e09060c070c15 56
    0x9107041d118103140219200881c0f16182048107025015850004034140740c4d8060710340c2413500c0000c50342e4086c4407441c180000001c0342805030000205d500c0e162000246000e0161920700960a204011880f1207401040003068115040d640701042140654800c100720502c03020380300049104040592802180b43d4417503986c4c103008241956040c000a129034864032091055180150103030039810031602c4014000140f003460025960744404408000c800d942d41c6035130781400c550010941d0300c200031422001c003a0017400c58909500c001541c040110019070030070200d07a030406000b150000080000c00d0742601da01c6109a402103900025080d440841a0198a000390f21030328040b240031014007030300100810712000c0c400101c09050099458442d001008400404800e1307900004243c0c00d01480f51503880d19070281f00302c400c541c0c403484600d003841050f4030002e480c052821b5402032600401c00180d41030100e44a60060b110596450302c07484d6900d404030200310a6000000412291030400c8422503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 990669982 1250 990668732 990668741
    0x6040b0702070b1c0b030106030f060207050a0803010915060816080903040e28090c0303391401060302030d05030403091d04030f0c0b1b0903011127130f0b040906 71
    0x700c50b448100030380d1702c0c80400d04d4281c1c0c615100c00742c00c0c0206103e14401141c4e80360014502d40d44a081a030303000e8909655400c480b5002a0024840789a54070001c1d4003c0c8a1101c1d0800a01a00d0400c7d0b10b081c80d240307440b20f01d005050b0040004000c01c040106070141010801e4401501482082e0341c003a1a019144900e0b5014074041c90b0021b43c0140140c01c401c1d180c0d842001c194507001003118499508549040e90b4290541d42822040c1c10465480507514000c04405010201d0304102d2003103450450814030350303224840c1c1501c18240d140c00001c00040c0e400140e000050200c5082082d241e603910b0400741c44100f0b1660040e200144054040030145404c0b0b44480c5c440d41c841d4403140458151090202c809071011000241f110070340380c02041c200040c03203c02d4424008111000c6107420500c4010a0a5868000029034050004503120902a0058003021507600c0c00b8000394a0030540000010b40d240780580070551119614901112003094503081034090440190050102c40003030b02e490720050 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 990671232 1250 990669982 990670027
    0x1812050c130507140c1b0d02030a03020d091d0f130506070206180a24020906180111030c1005060d02031912030c090b0f0c0706120b0a050306040b0702070b 68
    0x380d121007109108280b09001c0d100301c0302105c0d008107408400c0700728030b007042500507821036803181c0c542c00d1a034010b80e020000b40d9402407095006c1c01c04445042c0f80a4071300e4a180c0c100584c01580801c0d403407001500c400742290720848102c2010000d1700d8017a0204e0071014103078005040d5001d100200040e49800152040c043d000d52865807018501203805940c0b11605200c0042c03803580310a11180c1807150041c8400c010030130a0000601c6c12003800c000030700b5640b18080d0720050448140c10a0210360704080780e21030341c40c0860051454007031030704002512a406c5154840145907104041441d94980050a003001c540c00fa00b11002d441d81b042580c68410010041103078800044165060344c0d5101c1e0245003005212921952580b41c1420300c8881e0540100c40b11a101400c21300043c2c4416008005000003044540c507903903402c051001c400b03000d440320b82242d2401003155003420072194030300060041c4d01c0b80d00903483c905a41c41d281e40403400c0c14156400343c84804c0c80403805803506c032403490240540303 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 990672482 1250 990671232 990671237
    0x6040510110304060903090906091407170703180b0106030b030d05131413021201080c030c0a0519170f15040c050114220e071812050c130507 62
    0x500030300812050030740ea0011200a6169814030102c0e000941076000f005010740310703080070515182c80340c050008658656101c0d400190b103484041050010014000341c11108a161501c04280c105250000404016240c0c004140d5901301203010718a030010300b070b540f4944c81034405046580d04d12008015001090046101e070040c1c030084902c25015004076141e000e220701006501601d000054005a48070b250969001600340204150450180c802003000301c4a503d0203007919410000003c0c504041da151250099100026401c0a543d4911518040f0346086a464002030089261412001102e51051b0740b041d00c0e0381461031826001084035072000045104482d040c0c0c6141c0c0c4038003502031060b80c0c040c01d19102540c003030209501c0390002a07100c1b00701c8203009240c6141005060340d41c0700000d082c20b003903420180b0b080c00548641003201da00b041141c60310750031800d0a402665505080d0b4403c15245488180244040000a2008228014000f001a0103403488860000040c010132140c0e40d00 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 990673732 1250 990672482 990672493
    0x60504061229180c060c25030809040c171504150b0703030902011b0c09050115081f09050a02090f01021f0914061e01050a060c0f03031d060405 63
    0x400001180c10858949902e03002400b2949800510f4044007a10045080d01400740c080030301540c0e2101001001d90f980610028140d104280e410f00040c82c6003800d0600c0500d584003000c2010034030030700596801c02c4c000c840004451048140c240c903503494040c2500c07040090799040104c0d0324020340c8800c4001030b0549003880480003110090180303170614041c90314010424401d03070001c244a54805c0340c09920605001845036a1030f414000d04803150a0116200360f0360344014005502940101801030800c10305948410098000142078040006c04198850550301590414000e02c0000c4000602800b05e0801150074030040c581d000e507000741710b403e025a00302003810744554030004000300450140e442001518401c00782120240042c2c0c00e081c1c0d07a410b000300c01c00e55000000d005203801005c1c0d520315548445450311100c00000c905030b100074400c40206d0801c000a070340285080c650710394807a04c41c0d440c0401514054005050386002c40e0700c0c2407c500c8c0c0c41c80c0078080c00200303e401140180300312038 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 990674982 1250 990673732 990673763
    0x40c0e1806091e010918140616111506150d0f0e030f031513060e06011101060803040b07080c0d02070303020f03041d0601020f12130e0f0403050a030605040612 70
    0xf2441d800d8070742c6642121903481c00400000c801a0310500c0b03030a4072101c0c4041d42600c15103e0b403603e46c81c0c0d01503030340c9150418002e0140c8241c042000b0b5195100a081005581c4241580644c0303d100ba609034092080381e8000040107591003200301519000e18100a0b80c450610151100007000e82281c081d29103403403c0036840c0d03480000070664620380340b0758140920b503a4030b96401c55912904d2540305604010110a25185d1000900500f4090b100f289103030150740c41c0000004111404468081480740d15010046c010a50080212402d4501c0c0b0040242e0b40d80c99894403800610549002414500500840d040d40c203901050280032640260f003183c1c00e14609140c0c490b2248900d104100350410000200a0443d1204e03126540c01807050045d10300084c410301d095424001c040342c1000724241e0000349030b0301000d00c04403ca0082d029144130b00c4001c0c6130041400541c480003510260901c18003080e06030003580f00e90004005004041d2052140d503a69004e010340c6003c10030b80807594100811501d1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 990676232 1250 990674982 990675001
    0xe0105030307111c021305060118030206030703180501110c1c120b0112060321020111030601051303080d0203011a07030e060f040909050607081b09040c0e180609 71
    0x155045030300a01c94280e10b0804004006455000d020300f01c01251402c213080016a980075050180d240000c1d0000c5180d140500c001000710302030a00040041e40f14141c14030141e101d13027007a41d60003002403c0028108640014100e90501340c0c0c01c0080140d8200b5046140301c902040203010094034050455004a25424040c20058148440c48000a1188080c074140d5170464009014203001810410b51080c4284030b01010350300e403900283c903045050031100c0d0f1901044e04022200788110310003048034081c10074414406100103080d090400c200894500c1152444040150056074404241070340e80028040030310181d0000d00c0b8001705440719201c0d42c91812014400c0364000c0c2d52550354440840e64460070828560010309491850120501000c0f034031100742d11441c40030f0350080004007000d1038080c2d00104800001420f22000811180140e201b94110200740c0780307041c20444012078283da200380103c0701d41e484224410750103071f00e070240030195001340400b041c000c000c192013041c00341d926000c0c06c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 990677482 1250 990676232 990676237
    0x1006090c0206040f0210030615030501150903030206010e100e04030807170105030606130e0a11030f1216020114031905010608061003022203080444010b0a0f0e01050303 74
    0x383c13032a110550510014904401c424450002034200040c40ca0b4880c01c07c014020000c0c101100825074410042c40b0700181455001840e9030245403655002c1d085a60080d1240c8040c4216400640740101155003101e0b8114a803029081d220400107080c0f81c603060043c012003050302e12401090308112491030182148485905840d80540100f4090302c4e02010702c100041c0c18121030b440641c0c1e945040c0c0010b881400440802c40c024041d5080060003c010181400824500c0d0001503004540784018508030305c0039030380e8040c50241c4807010410a40010303612841d8007642401010800000c201c100003001642403503c4200e40420080350b0b8841c1e80950b1819025903480f60301041050b0380880036441703a0020041c02880c10110f0172030440070303d80c1c518152003981017181d039840040703814001003803441c0d111907000e101120507115419424840c0418408401c10328100e0484121007410011825040a12080c0e00070300349600c1203a03102c035907444401c924000d03e030007084028000509450000103 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 990678732 1250 990677482 990677491
    0x3361e020904020f131d012a0c030212121e06092403060705030906091204140103022208010c0e0f010c050a0606060503070e120c01120e1006090c0206 66
    0x114001a0b02d55408200e11800203072103140c0d10101c040c43e059144c49081c0960441a0307415007444010130316000702e550954441260000c6a8016034120402c41c0da1031000e46070814655042c0001d107000c0c60f0804030704200b10602b030384150420008451b0a9081c51190240c421074014581420181c2c00a000ca410060252081603100480101058000c40ca66074440c1400a0b484040640c100030103022904104085444a0204101008000c0381000901c080c6901150040190101d041ca83e11017a880b40540d0080b030505600d40c00d0300a07202d03406581290707a05400300038001c0c030155048107a075205160f00d01032a08503500305604508600e0190300501060500245503070340981d140c400458095980d1001507640b8880c98400b0030200d80580301c1c5101401130795403403a90700d01e44000301034420006017100b90301038840016a060407000106041004040074608090b0f4254826140d034003402e0b07440c07070548460003804204582000c855100c541100d21700c907414404080355000c2681c850b503003100c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 990679982 1250 990678732 990678739
    0x80619120c0509090a060528021b0601060906050715020c0106050307080c061204021c030e0a0f060c06110c100e010b060c06130519030315081c03361e02 67
    0x111150026600d50842c80d80811302e030714103030b81c14070b820000e48007180000c00300960823640c0001d620100003510140c01c80c0103440355004043d2540742c040c4c01441c56409210760001c00c800800c00c842040044202c0d80030002c0718546c10f43d1503880c04078060b4002c160500c1440d00c6807040381400581000c02203101182882c0050000f070500020b40068002124000c104980c00010300c808034150702a001c1603000d03810f000e661042d07048a810014040c20703619a41016054004120b02001807540c04254443c00561003003010480c2c4603003401c407103e24003640740c14400a00545c000301041c40442d901c034800c0d50748584001d003c2c00900e00203200340c600c50b0082111040d007045e80010361014401030114a42c5106030219a0282d103040051402c03100c581004800094407208800306410107185914080d110000207070803264a07032030707501e2034a28082003244107064840c5441ca0083c0160602082c10703c480c88445540c3e2a02e0201c0c0001d1180c078503504584415884280d0300342d0400c2c13108510511035016 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 990681232 1250 990679982 990679993
    0x924192106260a020a03150507051918080d0507031701120b04110d0b06101d10020f01020a0e010207090b1804111f1407050607080619120c050909 64
    0x160036640c2d00150318103140000e8807400c4010801a280c44030a1801180502a5104174103042c0110000b55100a0720203810400309010700c0d101403044004030071441c9031600382185001407076860f00405c040c8a610000d454010b0441d0341d0034280d000707001052114800c5d60350030b207441e41c0d401c91000c2c0410300380245041056000802000100b004401c10b1308180500300c0302c2c0c404000c00c40003501c1428403880440b0310351028000d200050801c280d0440481a071400c00740341052446580880150310500440c1c03046a07980e8070940110f0090100410031030110300250360340c02c140b51000e0b205107400c500341801071203008800a2050b8940c421800c00a03801004400c0807070a007a00c55407602c0002c0c0c42554000d1804a400c0150b0b039403880300400d0481242c400101c890303403081e00905800650801c104040c601084000d000030408220586e001c245070500b41c006481c1c800c041000c608045079544003543d42c010b4049000740c3c001182d2411103206411010100e9120424041e508a0581d02100c056008 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 990682482 1250 990681232 990681269
    0x1030308091c09030b01060201091502030c0c0a140d08010b0712121b351e090609060112201210021b01020924192106 52
    0x80c21016400000a03400c0307542c0c000315141424080c800c00307408107010520f404404c008200041c1e600c0760040c45140000c207c42c1c040f549400003060410302c4000b81540c0e0001c00202840e801006981a61003084102c0c0d800000600d80203045200340c100e00b29880c8a60342c1111561481180700364143d604a039880c5042c0042c6c0c2c0d4429540b40c001c000d01030300380400143c80c60340060840c820080f0481e40342840282d042ea1894028000c4001111141800048170520100c404000a15850001c1801090340c1441c0d54106c4c00f02500420518440f540b044050244444a8000250a40103850300402c1c2e40b06e0743d036240c0203000f070301c0b40016006007000100030400c10443c0c3c88504a039a80c0301c018100c003200d074080d800d0550500442400e00c4890560100300d00441034031012085412841000c000c5243c01940400165100c124108001d040300c040c038020742010b0000300694074400b008400009800a00b20809440c29005035202c150b019400300c01800e011880b030060404503440b16008049000e034 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 990683732 1250 990682482 990682487
    0xa020d030c170a090b06040e070501050904180b010303030c0c02090402010804050f10020a03060911030126070308070b06041b1b050d08010513050105030c01121508250b03010303 78
    0x25004400400d219a1103502c4801125900c01c1e244143c4810f10005240e10207403912540a4502a09039800391740b50030000405c4450006071501a80c4017402c242e1f403600c075807034000f40241c0141010210701004480d00b00342000320094110703059030301c26182402000807201041313035003e0103580060340c007908603408100554041c000507074119001d003041d2881d80c22440d10310b52800540440035030072240d000070140c2d00c440d4188242d070045c1c505500144420b80008101200501041c0a11481040d140034200c01110060040003810074181083ea00c41d950340303007427809030364101110950700710f0072050003e680b03468284501824403c0c205420a40000e100f241101e40380081d410f0038081c0c0d03640ea00d14802080b402c101041c05110b1b559107450583d0304007030601146002440c014071005013480300507c61950003240e5844800b0082c6400d0440720f980190281c0500b1000e0800c1d011240000030100f204880810f8640c0303000c060010460588a0305511300481c0000b900c1580038000041c80140300092 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 990684982 1250 990683732 990683741
    0x20d0e1c05150403050309010e1f181406070806010509030d0e0112050906040302071e2306073e0603070c12181a31031a0c0a020d03 58
    0x81c064401c41c0c0020007000901640701d58242d40540214501004124102e4030074000d280c42c41010744d01410304d0102c0c0751541c0d641490301c0c1042064903525105041901e81c0e0400300c504000c2d401810301415003800d401699100c10f003d544c0030000a0705100020300d103500800c11550002c0b000303001040301071030b102c0301100d004001b500d0060421441da00220142012030107120300030000300010b060309040601d0064030301440e907400901100006c082076410503070b20160b0072044505545070901c10040d90140c40727400c114001100c42d8000000b20341c140030702c40d02c004100c41200c82c070201e01d041917005503900540300002c003c900001d0344000c502c0c064181808800396412581c00c3c200403885c0c1c0b1090b9a03244a90510282c1c0600045070702c0b9107805201c1462004100801c071410194040840d00d41c04890203200300c480c0107030301100c2d04040d02c900074440d5010704001a6600d400d0403a40e522854034080e8070300e0b034485482c0c5612004001c40d204894013000c0301d07d401400d400a060300c2c19085829400360 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 990686232 1250 990684982 990685039
    0x50d0c08041205060a0b030c031c17090309010e0a1a09060403080729071e020708060c04050301061401020c190f1d1305061b1303060c020d0e 62
    0x102051000080003590401d80e902ea86114201500c29840e21442501c121060800b00754801e602c4a0009a01500d002c100140850804110407505850130f8909507020b09503280714100d0400c0c4001000081c0318044060700b0001000d03a10b40040752000c1040180c408828020b01c2d00030403c02200c8a004048076004222440c0d003c0d000701e00f019034a894803409c80d082208291030f90759036000f107000142c4583d080800044e0b11802000f41600380305400500b00368094000640302641078540c10500d500070451000100950710807500b103443c00200107403050b04580300351800b80d820080c011a04542c1c4860203c5d40a80c10381c01080c10000342c20030006544c090060b018031321180e03414041034000e842d510700c074007801c0c0700381800c2e000c01440215480c1d1882d00a0502e1a031400940b01940061004102260005100410180d2207040c0301c40c0745e4040e01c00e8848000084101444c00802c203d2150442a15035401c0e400307030b68108810b81d5060b10303072444456002e40d004d82c100e4074200a4110545040044 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 990687482 1250 990686232 990686243
    0xa230d050d0b01110a03080601020706080c0405090a15030c0f06020714040518010f090c080309092404060e0103170a080a020f040b0d060f06030204030b04020f190b040e060904050d0c 80
    0x791054001d01e242000170814065002807280820045656010850f8000405082c58403064911700403500000c07500407401242e10542107100481c0300b148990b01300d099250005004030180300d0341c034980307003100151503c5000140c0905110005440b400030414108485801c0015006546101c003004000c1c1401031224041111280402480724400d12502c50f10051401c000a400206410980d51001c216441010584d000300049449501c505042c96080654000b25250390b40c582003200070500300b10075509070814076040001501c0c003402c2104d0340c12a402542c3c0c0c40c40c0075031103154450709441003075000000b01d50100042882e80181d58020b0542c241482d0701c65040c80c0d180c00183d10580d0080d00b0218203181c40e11003d000b2417801d0749940f4020401d5040c118602032a5a8880c1480440200064442d0f007040e070710355186403108440040103d0b0481c942082a03a02c41d02c10040d507070094000c0032061180780000806034107200c2e50403809240c0000050102c2031046da812130f00c058911808444 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 990688732 1250 990687482 990687497
    0x503010213050f1c03050310050a0b0a0f052511030c03060f090307060f150501031b0311040b0307200d0909050414030315180402150f09030a230d050d0b01 68
    0x10b80134a00e01000c14858405e6451607034a090440080e580130b81940c00440c40b9040b500010450011800110f44094400307080c5a00d034100048802e4429008208809044891090b961002c400030448050729843c0f1903594681004200390a00d030b40c45201d1940d0640603440107001c100300d60754030740056500032420411207140290b00d07582d001c20ba0700c03603805005c003803a1500082d4801805070040d0740d01038602881c08021080c110a15030041040c1406900c040c55560030301c4111f981607160803034000e8001070000c0f990700e0500200c0144103c91030a007070310a002d00d1031400300510380c0200d00b840c188891a5216a030b07040c1001c0ca271074001d0901800859010f40312400c095415002803026520481c0c0354880040f05015180a00c4510741900100c2c0d0f2501e140a810080141e44030a299800c0400705807c940e01c850b425a851450361041e4520503034148200c4005008001844280500c030845420840840c1410030f84099a40d0705054204008204d0600c40c01030040d0259020f0b03905904140b41890 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 990689982 1250 990688732 990688759
    0x90b0a050c07020d08070c4e060b0904030503010501120c020703024c09151404030c090f1802030618070506030109020a3902040b1f090503010213050f 66
    0x221080e13a50744940c160560b07440004c2c80300308455425040390310b265007241a902c1c5800c0300e150b9840011604441252541e054a48c00b0312549a001102111001e82031107200d060904020346907800034442d540c0010540040500c1600060160840404107a001498468119800c0100d41c407403101c45981c042000000c039011160b021203421220002ca10191050000c1441d84200100c1e5046a8007007840102001008035021446d02c0303102020302071404040da05c402d1b800c0d404080c4116440502080036052010415030031942c032003941a40c0c220400c00403004402c8640070075205052019515810200004000030381004542401080034415100f0081d00e400c0018400c0d0400c1c2c0181d4031003940417680070b804507000700c8507440c10904102c01110fa200112500e020141c9074100000b41412404034034401c54481e0f400160b20001f0040c103450882c414014882111640c4916500015207840c4001409003010b100b141c0c4005c41042c02440e0582c10314062003041c054070050b16804ca200b508824 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 990691232 1250 990689982 990689993
    0xb030a05090d170f0c12130209070216170f0f100605040506060a11100c031407140d0e070b0a020c1008070914130c180509060607151509090b0a050c07020d0807 70
    0x45101d80781f50700401481c2a01030060000e1000f0082211056512921030b0300000c10101e1048411901c0803c1c0c03541501d40ca00c100b203810240d0080242109107e0070720740c0d02c0c60000108886c01d24041781c0e442003181940e0f960401040e280f013614150740040c8100040461355100d074100c02001848042214a24000c40d80c07294111030340f4049038030010b44c2e100744165403a11800b0300c8913000b880d03c0c038100c0304c40310110700215200d01c207000030604140d641e05903c1040841c18801d09008064070342140785c031403031408400b03500c400c1504000740c0705d402c4c51588160414003c882242c025211581c61049240c1401044403862408507403071940b18140d121404404191400b075144020300a07541d040c03447c45945200ca1030020950801c0f07108130030710001c2022545a040c1500c0302903400c118108201d41d40000d504c0001e0515081150b4040d0107036601088010007138000601884c403501d000515030741c41c0d440c0241220f03015a6480c0f01a141000f51001625180700300d4070b0014000e0702040c0c60715009a460 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 990692482 1250 990691232 990691267
    0x50309011103070c0212030a020606091306110301060f090e061003060b030c0c0f030903030f0711030609240606160201022506090504090506040611040b030a05090d170f0c 75
    0xe40019811940342130860608421007071403020200c00450419000d840c020351203600043c02e281c0200c4090002500c145600b48103001400e40102c4100018040c1c511911034503803090180d1004100501840c5001c0d510565040e4115803240e901e00c0c0941d142c400c10407082d2480414000c0402d9141d9402141105800000350702a00001c034800380e441e00018034817030a007460340c0044500e80e001440000056100802240c4162032080080303071f0354034202d1420301940c1d421120455014481d040c1080802540080c81c002000030a0400c4400032403024051484507008581098220070103010901c480240b944403c14880d2050060782c8540440c025010114005c03c112804640d800310340c2080b005130006260000391000756002e04c0041d1a948995980d00f2010300f00031700007903841118002440c00103059038085d1007008544c50b80c07400d1111007003000d803005496104180c0611042c0001003801141800001c0c01a01d099061540c0d903044401c1c074045008058080c5820104407081201c05201c48 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 990693732 1250 990692482 990692491
    0x1e0c0a03022a0f0303010b16080c0105040302010f2007150b120d03050c070305120901180c153b040920190306021c020a0801081504080a050309011103 66
    0x30060140100303502d03450300d801191040d00c0c405800c2040103010741c80701c010444617255203c04554400c071601e0700c0c041c000d610428000c000e00394a480d0a00c001c165040d0040300034044440c0c0d0074840e0307070b51041d400b0503000341c5000350480f0100101302050025201d40580e00c4404034040c030024080980700c02082d1103900c0d803160320900350410440d100c4400d0b058031401e82c00000d000f0603d420305803180c0d0003424034030a48020710366402a00000a504850075088451a40b00c0b0302410000003000e4540542e076420140500070b100e20740700348031104840c482c032804100c8444010180740b410542c0034040c4001100304000e00210072120502002a446500910244511404248000c0f0000c02d14181e42c403100b8060852180c0141095071000415900f820f00070f82c0e4000000596462844005800d1482c404032804182d90010900c0724815400c07040341130403110742c141039400d0800c0d03402c28150400f1040318020483c00c1c041c00a015058400c1000c0c503071045103040001044400b43d51180c505400886 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 990694982 1250 990693732 990693787
    0x90f0b0d0b040b0705193204140906031213030803040317090f0309011b0b10030201080708061807171008010b010504050906010309030c0614010e1e0c0a0302 69
    0x5040c08200300e0240001e81c0d11580b98542207040142c03456900a0826882541c0750410011f01e080e039500000d111100c203401510329142c0f50040384110843c414941140c428401601071110b1519000c0c1491000386110320801400340030700e03102c0541010001d40004158101180f00c0701c1340480010101c00046006a00940b01c0c020418540030741c81c098007100810300d2186405c410b01300c1280f1309000007920f8600000342040c0d880d2a850150132203400c615000302034002d4550707009000d55003142d42c00700c1c01624000c0c0e27521001599444000c4c0d800650545603240c05c841891700c4440d281d507041d140b894001c9030700c1c41d0400502c00d400d1240c1820000030f581c548a01035110108015240e4240300e05142d065081c03d0003810240f5005c0055210700004100c07506150b21090740c2001c0511030351407140c07030641c405810401401503080da000700c04401d015410103408400c001c560307000a107400c250004c0d003904030003d00a0340c490044a81a811260440003030503001c6c4003034903c1c40c035150b10012540c0c58170b1 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 990696232 1250 990694982 990695003
    0x41e030810060f02070e19110705010e030a17040305040b0a0e01030633050c030408060601120902131d1b100504030803010603020703050417030706050108010e0304090f0b0d 76
    0x500c034807400740d480e40d01c00014490310b11401048140c000c031724401122070101201e203865544540c55000b2540d2613103038084a5207003e4405000d10b603101e018000c007a0003074008222078440c124041d581e902c1070140040100d40880ca1aa000c2d90342c0304500c0303601500c030340b07041c505183d5903186004981d0000c07991180800e0450030f507038000e564948a05002054240524001e1031541807401048000d5a20400410300442ca21000954003810844080c0800c41e01220b41e51690340320b0706c5441e0503040d101d1303900080e105d451605580c0050701415005c6a002421800c103108081c06890080c4a501c000e021a18000140613100d0301d010300800360041090600001a4001c050400003580000c4015405200c0305010034008226240141c3e4151041420016901c461505058a190003241c0c445540052800000c1c001210301001030404d13588a1030042c40f0507625090000d00340d950310b0202c20025401800200101c490a07007000900500706540001e821800d40c01280400c011440b0a80d98079184 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 990697482 1250 990696232 990696241
    0x1523060904051806090105061e3f011b050c1005010801020d11030c04030209040c150e10090b0f09130c02150f0403200319210203010b030f041e0308 65
    0x61202c4da620619000c000c01241c47d0600004030781d04802410300d0f03220042d00c1603410454a600c2404954010481c101d5042001d400f44e40503001c0356070b8a412045e0403d002c80710510304605010707071140081e04100920018a940c001180c1c0c541000b40e96040d2449107041d80300500802d84140c40c040c1503810000350340d40307002ca42e44c107044c0da518610110001104208000d042503044003502c05803541220541256182d6041140103d6002c1d0400740d50150380d49400c00c0125040244200d182c2c070182c80072511881049011307124600d8912032002084000c20105a280b080d9000a02d0041c0c1300829508040c0308240b96070084441580e008009a40580420094510007103031040e400560614003011520b070a40d030090042034101b01803c03280d040340500b00070101e0144140c40000c2c54a500c240440310314120001d00580c80b82080300c140344680310fa00310003000e02d402141d040c4c51015a01c0351454450260381e0102c128010302c01e49034040072486400d2064015201d4040903806655040d105090 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 990698732 1250 990697482 990697531
    0x61812010c09050a0509040b1314010c08060d1a0901021606090201030605091315090b0406050403090909051c0203070b010603020301050f0a0602101e11070501152306090405 76
    0x301c2d5002607202c0c1d0100c04040119a07504600b065025034000c0d17401c500e94030f411400003d03205202718001d0000e49801d50904c2190015801078450780c1b001d55442074151104010f0022001e01010090555040050b911054034000000340390081d5903103000600e005d0074103000d188124912003086400ca61a802d624040d0f40e85030240d20003601c005c0300c2c4004941001028002c40301603d500007421103d6a640040107291a640300e485e200350010f10040b403030b180625005008000490f012000700760100c00c0420022017a00c01c1c2505d0aa01c0401409070040c00321002440311048165202144020005c00c4002030704552003500a02494402503181d5041000304840100d00d521418001c1d407210b0b0042005a40c00540081102001c1100081c01500b0f254800c03920058002030007a6141481d075180032125402009041060090008200e050407503120124500c0441c460644e2240c2d442030004055040e4600080011000505140c5006181808030f016201e0845044200c0800d82d80d07010803100 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 990699982 1250 990698732 990698747
    0xd03030911060f1803120d02030609010e0930071b08030708090603060109050307141201060f15020708150603160b03070e030c0a091e060311061812010c 67
    0x100311040b60512180100c0548580100040b210040030320081000c226201801102e150b4030620b650030f80e0314008000e0000180d0300c1a00e8031030041844c039000048040300400080d001e10840b0000e0101603841ca42500203107112811071915021151400002c007485910040c20058030910398039003400760400c0b80c2900380034a80d014014941042112a00140e40e050482c0c134090012600c4c0c42d125140c1c60012204001709400185e010b200701d403c0410050302849480096607000c4407452003055080c0006030030395800b403280030031108030640148281c02240741416042030051045810761580c503140d4074980390300300204d482603031a8a03061010383e05040c40706260034880d0411002140d841e000c0c07540c16901c001400d80040001050500030665414890700c41c40d42c0000382048a5941c4503080e5000800303803204070194605003a40f1814521441d400b43c001101d4010390380c106058001c00a100c825070000500010701d59035400541d020341d80350005040301c241004000282500407040103401d58 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 990701232 1250 990699982 990700013
    0x1231b1c05030f010b0c0102090a0602030c070b1201060302070f060204060801061419110a140105070e100806040203220c060801170c04150815060a0501030902011710050d030309 78
    0x30030000c1068003d00b07251140d044460000c801591400326403801030090088074140e41d0b000000d2540041c100740d000014141400c1380e0016191400e80e0364001e801c841c071450307a5114416804100401005029601a04a140c000e5003070700008821940c801040781d00a070004404104410010301c80980e000b20303444003c54514041a107030004801600ba540e0552545a50802501d107662200b501c04c2400b032403a1a82d40818800001c00c8510700b514043e21048400ca000580a03032000030051415000302008030b070721511403800a80320703002844069407000748030848818080c800d4200000c614080341d40e199008007680d90303000d820030f1402000044103912403c1c43c0300c04503122400d45140410340510b014406c440c0060207040760281c41390342160543c021081360280b0b046a8060501580c3e00354460b0000722a8001c5107a2624019000c5590144004c0d001990288403540900822550960400c161000710168a43c0c2c60300098286508406d045000a450300249001c201c2c40c0584039010 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 990702482 1250 990701232 990701237
    0x1b24040f1a030c0702040b120d0518060901093602070203161409130803010f03050c2b050a1203090303060504140f0a0b03030406200601030201231b1c 66
    0x560519290f003140c030340544640680705540d191514202c0360307184200d4801034206c10042d01c0c61501800b00242c07240d0401d205034020031a04512103611864441d0071a403c0074816154008007a0802502c40c010a4030034410700141c070442d000c0003c6c410702114113080c0300307548800302607030b05c50251041c9800d00951140034000b00542d0003081c00703403072000c2e4210b2180303000a440d0b0b161aa40e0713480c0021f00b0000039001c042d000c04400000499411100007000c8290782c0141c0499003d40c20702d40520921103521010078490242c00761020003804012403804920364041e000310707004040d00344c45682c02030105d8040c030408241d035002c3c0c480402d501400703103200400c4122020442d05100984d81d8a102c1d1000349002d200b8400000001c513581e24a601042200c403001d8122622203480c1d10002c0e1a4890300580a1104481000c101050500008a09e81641d606940345215201c41014403615500740134481080c03410140020100307014425800512000c0f104000c0031091842c042c00150411f041c29032404 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 990703732 1250 990702482 990702487
    0x12020d2903030301060e040b040518060130060f0608031b010203060303070308070903060501030b0a06090c0e130e0a1511041406030a0605120607020f1b24040f1a 71
    0x565030701005aa04541140c1030603030035030100390005801030000c0003005034014074100c107000746290520003840d82041d02d8800c0ba042c0740d0301c0d103142d0301c449034405408101d80001548030191a03030941101502e43d51043c0c00100704080859a620191510f1340c01c22080caa2010456111224071000e90013003000c001c0000318518249000400e03100c0c8a0b411011f41030000c03ca011804031441202044002c40e0001400c100c0c5584030300d0007140c0d40b60705482c0c05001a041074404604000c1504c6040910545c0e911051081044030060207504200300d54200e1005548800b50b9180010500c14042000c3c4242100318100e8030070a2010101d4886002c07102c02c18078280820b000c1d00c8501060a01044001c0701c90350b442759580400300e805403001e604401e030410312142200410b09000203040e40101c6c455000d0f600030302c102104803513685500c400442d68407030304c20421800fa41002c9441140303144607a040d401100c00d02003080307205684141d220031582035502a00700980c80c0d658203481c01a40c001d03005d003071 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 990704982 1250 990703732 990703811
    0xc1211010b0a0b091e03030301060e0301142520070315060b04090207080d110903060a0e0c06031503010c050a080903040501170603010902090a0209030c0316030b0712020d 75
    0x40c035010707014009010b1041117129448507403103801c0704210300300024110b03a07496846240c01003030781d01c2c40c0c1c90007402076007404203280045184c801d01d10b206046070703100c250032814440084c00340b181c241c8a00600703100c096100c00da03d5528400021070001500302c0209145403035440d01071013000341100307405070b41890060140b03c0c0d0140e480889044039000d190151f101e001c1d038184900d1920a5841c144c0500f464102c41c0e60b07040e00e10b04003031b120020b8110306880305962084202d400391642c00c400c803841030f0050f580301c0e059458108052340d0423580018220007568854004a421190b4290780c00c4045074020030041c04184c0d22042c110b40c001d10b4038016604080c90b19002a05000310361819848240d035110001d0f050b174400350b100c82c0042d44c0040c114001414440c0d1031034001e52160b51620b0003802204029840c07030030000f0341c0148025480146485092440d00d8048000324007501c098100401c000d40d200c04040c070350014000b204445900001c20507260881155000c1e41c003803160340c103c504903000030b = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 990706232 1250 990704982 990704999
    0x61b0c021c050606090403020705061813060506270a08150a0e030a0e18040303060f05060408030307050702031c020321131509080304060b010807110a020d02010c1211010b0a 76
    0x6134208100f030710103081c50b0b15181350980c140302c076940107950019070124262400c8041c0c084100345409003a80c1040c10104061070000648070140a000d0f00070004100ea030310504654801840110040e06160750700f02c0900e00054550500d0740d000103800c1e4801a00c207220500c91420702500328004420402210204000c0c49071a8019411540f091140100b900d5800d510f031103e00307510412032100c1c400141e00c0c1a103000b500030300c0140902d90700f0400c203010204881c2040303011501540c801e00000c605584c0c0ba040c04542c0e50b84241000c80e00350040041d41c290f0300c41d00f08424048201190041c1d5103825400e8001401c1d400462583c150441c000010711507075002c3c071403028000b103030020400282c42455102c3e442c0548200304009016401c0003082005001503648040058107090f43c2d900c409403a10a0101e441c0184a54882440d03002186039100624011280780300c180e1060424140380411601e40000103640791100c00c000c211a81403030751481200f841142910a02103400300003043c1041804d = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 990707482 1250 990706232 990706243
    0x109050702060601020a051c0c060c02010e19031202070215030a0219090612050403200f06010f0b040e1909050a050c011b061104081204090f02091c061b0c021c05 71
    0x100d0400c0160b29100310a5100f49c9070681400e400040500151072482c0e0001c4c020aa03c180d603201034081c02c6109001000070040d10b0202c250103a035207664030144a110340c0003c1d880307140104d0380168802c0e11042d15031100070141d03105144205005840c2c2d40b504059600d0791003201020002c2024404c0c1c10f00c10710344c01014800b580710703069600003596529072906a40401c202c0b080e451081000350301c844090a0f00003000300c3c244503150140c4640340d03a90f1082d03403c59032880c003034140406402d101c103012a016001240761b01402c211131084508010340316410807146d280c04191000d400610a10040c41410050281003910a20b0006442c612181c04070b54854540c0100404080e01c800005204003a5030080e540076282c907000f55601d050285030516829400f6102d040305c01c5080000034000c0d205984255510178002402607070384444140119039180019010494250303688590b2164001800d50140c43c003007619495802032062140100110398007094101c0f00030400390341508001440c045030 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 990708732 1250 990707482 990707503
    0x40c0f050306030703051b0114310b030103030909050708460519020403021003020c0a150e0114190e07030f0302030306010e04150315020d050109050702060601020a05 73
    0x4240e600e039140c02d4002030030803c03070340d01c01b5103103124070101130305a03070f0226401d182600000d0725001c8452010b8a46481580102c2034420030078910b1807042450000d00807440448070b01003c0c12410742c03070b03260828403005400a0f08107070b0020b80140c405100f41281481003d0300000541043c14030f0b464101d40010066803103401d41028605400d000c00c85040704c1a00c2226042e611140f2865040320500080004140482d84015003031030000f00e040c444d441c14401c450559030081c00700319881d0032001064001c3d51081002200a1003506140c10124081807c2c0c41c140d440d001d040854002c8104100a0a440c5180018684032502d4014000e07400700d181e80048103803801d9a004602e01c00705407403603420017186034405000028907151400401d54080011071040304242c070350b9800d5800c0b100c02c0c807040b1b544501c0e0002c0c0d501000b40c2c0510110b0404005206510f0707170600c02506c0c150315980c603801035a45c00ea0002954544800c10300410580520075150310020a100400a443d4103031101e6070358811290b03 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 990709982 1250 990708732 990708737
    0x2030c04020c031b0c01031808070f08040b0c0a0606080d0804021201020405060a11011109061b100903030b0f15070b07020a08071406070918050c09030d1d040c0f 71
    0x81c2d041000360103009071129114807100490809224a800c503440d0754a00d55120b000a181080e0840b18082a05c6502d84441d00040303e942050040e5481c00030311200440c0c00c2d82c49a8040c0320014a40704100b0003005c008000a0142114245525014095541640004669402200900990315482a80107500035012610000b1100c143e514040c020710030341d08241e4110364006132048071681c012411501d02800c00380200100c001c400c0074520680140307803206901220422200c2e0489400241c882c1502554030103a03580c1d411105074610844881d04000c80100e41c40b140d14003407602d481160031151900a9805101d200a03001c0703405014800c01400600018658010403411482007100c4195583d10102042d6240c030030341002840ea024101c014070343c51240c040026040f6100307202c807104441a0086003030130a203011400c1070203420018100010003209101c2117080b59410040085083c1e16a2260000342e1040000b600611180e20107550086003455110f2303806941c8405240078660061 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 990711232 1250 990709982 990709987
    0x1409060708070629030304060806010305061f030e0609010b06191202040f05130c0e0f060915040e13050a0f02040f1103180a0506040b1b030c04060f0c02030c0402 71
    0x207107412081405252400781c81d080c500303640700f480b0600032610114185520207850280031007031410543d880c45903003d2140041c00c0c560101d9229402904a5508008001c2801d011a0b0400d030032104540e2203e80b03070000103078131f9110241c000e080603c0020b4111b030f516802400800c0c0040086400c0e440b5802003181c403226007200840c1210700c201d40d0558250084103096603182c1c0c2c0d47c40406d003c1c02c8540156840703828403c240c054201410b00c03584005c080b058540c17010700904a01040341250f502c0d510303545c0100b0100850a040d0362008502042150b2503480d441c0c40e58249401e038914004002c1071101d0704905600348502198001504030710035540300c50501031080d00d030700c08070f00030341032910f201001da03818403915084841c0498040c600c100610701c41d4620840105002d107030340e140e01c1e40f0050890741002011502069510712400d5011144011030021581880e50074145a4001c45080d8a0f6000c00b223014405264000381c450b52454003841c013400011801d8001a841c1c030510100d41d4400d82d0700 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 990712482 1250 990711232 990711247
    0x30913060b070b10170c09090102030402130b0d02030109060c080105011b0602031803120402010201051e010e040822050f0904110f13140105040e01020307080f060f0925140906 77
    0x200e02c1403002c0c140483c120107528090f1040c4c03941c4c2d614031b403040301c2c0301e4100072002034007030401442500c0c03256400902c0020980e0307603254004005c20105003101c0d08028010110303401b6031002d0040c24500e51160000003190000040010006641030f003040d130400c60030346200751010741034490141c080b54211000603580d82340c50884402d040110036001c4000d003c0032940c1c0e90102c81807000544180d00070780090185903102e025000c0000d0015111110590300c150040c0240d036000e510041e0300a00c9002814640400540640a0026203841803101010007400500007800c0668810301c44000c00d40c4c1d41c40e0141401ea032000f01103840c10002ca40506540c5032090010350780c0c6c41880d0a048030900301044044590510050340303100c24081ca0380154201080004000014400c69120f503a0540e21001280c0350010185980395001d80440e03130150843d509085a80c1d64001c501d400707a541c02079807000200c0d541d40c600030844070b072000d8141030040e01c6a0403080c400a00007140c001e000c0468505540c0c43c1c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 990713732 1250 990712482 990712501
    0x50d02031f030311010f2c030403060e030711010206070c03210204080d0315030209190e0105070c03080708060109180905010f05011e05030709020d1d030913060b070b 73
    0x420314000d00d542407010000500da00401080c0c0003208101c001c1c00300d00e8191240906031182d5503081000101004002d00c8150f0342001141107100b03401090381e14103070383ca8650780c00b035410342c4000107141e410020b1140100300f01541d60f802f2202003030000d009680740410300a4402200c00c40e0180501c0800c039040d0b0301c910359088904000450984085444e00c1d01d0b0a4070035034850300c210701c0d940400c1c40c0c155003035291040003054808403540105821110b40d581c580018020700b29081e1080060703110030703070002404020701034039100d40483ea032100d00d0190103080c010408031000c1c140b00d0601800b08240304199900810f5403064030013080711a12604000d185c16001040d400c500a080c95280c01071402e10841c41e0380180341211240788511695641d40104c0e103191611912a0700c6c0d144d80010790400404102d43c01900300030f4900c3c82c0004030350001221985c49103503c00c14108941d00b0001d04030300d8610b00500e101103400f02201c0104880c508040c815005c51003104070242400f07005030b0005d481c045 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 990714982 1250 990713732 990713761
    0x9010e0409030206070f0503011511030d060e0709120b010e130813061e0e041e0e0a02190302030307020915030f0f0d081512070b1c0b090601050d0203 66
    0x54080c10811480916081c025207600701a02e8100020320300c4071680c5106880707981581d05a90000301041006944001c044d504c0740411070350800e0500091018200942440c400d0328010000400d2031541031802c0b8000604000c142e8000342050481a4500b00101d1050000907054075802c1d42014041e881d1001ca044d00b1488502e001804840c0000b02580c11a50410002044807215100e170138604070070040d004c903404040c1107043d00240412070040c80c0d42c902a0010558141a01c14001884002e030212038256407034180c5910903070b03010715500c03811800c09090b0380328070045040c407025065003541d000a44130300c10000c010f4818058107011601c02c9144240c00703404d40d00020100c1d0304814a2110580d215242c1401c0b403607550003240391300c140d400d00034031a0b5441203058a00c8224220000410840c4000304041001443d101d0203001041425500c002020042c075030014080054040710341140556018840380340c000d0082005100440e41c110f02135903c0090a41c40c09a20b903504c030301c08403c120 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 990716232 1250 990714982 990715007
    0x14011d040c0906240215040b281a01030c0f14091807120203131b1e090612050a0213140a050f130c090c050409020d020c07060f0509060901 61
    0xba850000c00051401210741c0a03c409400500030348204042ca100a07a101c0504030b403050890743d110000079000402c00341d0a6503121080b40c2c10540c000d4200c000210207803803040515822a550b49214800c040d080101d528041c0070246402d105072519081c000305499443c0006205000384040b2184d54182c2c0c2005a681520024000d203400405260150f000034005680d1000800c0c5410060750800d10310307000f143d200b41100f0402445a880a5442c400c4a1051100020850481c03013004103800010a903031160140c1022082503085061a1a40c8101c6034194000744008151109050008001140d0260029011100115035071080c1c0e15900162484d1a05042410007600803c05420043d6005601400030a4150708180d40c0717054145844203622100075008041c1000100861801900702c1d903001c03583d81c0b40850915594804210030b0383c124821400c03002e0f4001c50035400c045810010f00d8000c00091900408420740a10050304a2003007600c2240116000a65908542d00610100556 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 990717482 1250 990716232 990716249
    0x1b070306020d05100b040f03080906090a03050c030c06040e010909050a080415080c0703021203070302090d08041a040f060f0309020907030608010c03060308181215040614011d040c 79
    0xb21941c8401c8680100421622005440d10308600855000d0007041501c05460031500a28082407d6031191215074101244a40d40040200a0300050b5210b2981c024000c51065000f4054060389034101814500355050715806404240010464403013000c148504542c05842c000a00ca0a0703400c5c040d0800e0095040a4400301d000540003e0315a50001420201e210f156070342d046503200d0301c071002c4c030610444201500603030104608610044054000b990402c1141c20014600089200440c6100039051010f80707500c1c40c040350800130311006480d8030400c0344400102a290909184050b00c5c1d0480c18003c480400c200d4000d240481070181d030202c11801d0f001031170490a480d2140000f40548514000c1c080c495080815502c8103500a004034420703641d000c3c140d90b0600804048045070b000d110583c5c50b90000021551a041b0002400b81842c00b00082c1c1400c0c0141c6071a0400303006651289441400440d02c1c1001007260000c0c1811030a05d0071000c0024000f66201c03418901400102504a03001 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 990718732 1250 990717482 990717487
    0x90b031905031201051008040308061906170c03160c061d06040219150503101a0703020f150a0c020c0a0b040503280b07140d06051c05031b07030602 65
    0x240180000a00003403200f0071402ca081d03030b8a4105010000e04101d459601103000c040100340024001e240c1164440b00213420f182c2084900b00b09541c50030116407200d404511001c00c2510200310240802d80d1254202d03040310318506140c901e8000219081c1d0341002007007000c0e54000100442c035001028000020769442c009040c0102c0701c252502000d95007284141d2010b01e94a620308425040682110740c8015100d440202c00c120648040d800202040702510800201013250b903054161040454040c01c603040d280c10841c600030f860300001c40700100c0b00f64069128102c242803280903042e8449917110001c00c044403545401d07450300b40001a0507622090b0080d0208260700c4000182040724411421a58607145d100016580c5600c0e41011135041001c45100360003141b4441d4403a50010050b140285112652004440741c41d04484c40070b14101d500c2e01402c2085140511a0060001c0c1d0361800684c0400c15a0b501c695034494070040d045010307036070340c031404440100780500c500440d0004401d66 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 990719982 1250 990718732 990718783
    0x6011d09070905130e0d0c020609040e0a021e1e1f0f1d060301031b08010203010902030a060b16030f1b0506010312050a210f090501050901050105040c0801090b03 71
    0x24407441603400f03194001c4084103141a00580203005410402e81050003604079501450380c02c50b40122031000503600202d0802400b2a107445c1c502c6098030314610540030f00350100c07051041082c4001c000d02c8403055010514411400c6603174090980f2024000a440132000340d4000c0e022820081d01d00340800743c0c1c0d04c200c3c00300c130112541210500c40140826910400c0b40d41070311640045520350f00c2ca0780750300601c007480180001443e074000c140d040c00740295142006039035070044609a901c2600000c044a4020040c8500c020407030040e2800f03032603080c4180e404c01014030301404542c451443c0c054108040c1e04000004280104515140491f080002210344203d905100d60360301c1083c40b0488484012194004845204034166200135855580c0c0c0e802030502c01010b0b1510036416990b00003103581e10050780d542e0403d10700c11420010b1003800003054a03e041400c050848505900490003a030500c00d268602550114a40c3c0c1510a02c0200051500c03124000ca8605581001d000060482c1d449110 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 990721232 1250 990719982 990719987
    0x3022a06070807030212042319060c08010308070605061201060603090203070611060a02130b0304050f0607080601050f03090a062901090f1419271406011d0907 70
    0x7440754065445051079612075101c12412131103645c260848083c07101022900052108248154090007642d0014009441c0801c003030410084041600c40f40c00b06400307110030000346015220001c840c600b0b141d0310940c51501d90345094420325800401180e80c680010b60701307a0740c980c403000e4252290002004401c0d00c42401800406034064181c0c403d00c12890002611032041e04000c402910f00c40107015a0789510612102039001183c2140090421110101d5142010405036106601907801055007020008800381081c001070010003c0115885c00c2040c240d801c07508461b100b032884265241c5c0c1e0340d0342c3c19146040221a801c02030046046c03200c01b0554a68a005001813040c106401d0710902c01e0f058011744e00b1488a103e203d400350314500e002c2000050030074500c84946005050144038641160f805803000e0101d4001203c00d07140b81d1103061503000310341c0c20f82c0c80706d0801c1401041208645c1b0b50120009500500480c1001182140020b80b403603020341c0e89005900c09440c11140c2e080c0540302 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 990722482 1250 990721232 990721243
    0x1f0603200a0203210105011704030e0d12031d0303070c03051c0204031a15040e010914010c020106080106080c0909071d0f06010216030b130507030813050105071203022a 74
    0x3d41c1c0090701030b5604080c03613044408218101c0308140c5920818094440030029559002007040c0c1c03d00c00f0300f0070355841c20b0b19501160394080b0702c112140110f60f002800084c0840b01c031503420f0082000341c3c000c02c2030705980000407607400036098104a4109410703440c040340c25128009058004e04000440d64043d90101d401400960703100b10304000a001c801e5400265243c030483e0104188256910b400c6603504042d80144212001e9030000302c5c042c007240d102c0e84140e0303c030b542d6855040e80d07580c20785042c5140e081c400e1001501001c00244441460401102d981701407407104644222130702400300d1200310b4100a000014031407213441c1346028601d5032111550500482d821400d000118000503119032010500c0094811b10380c034440745007815500c4002580100806a280c460820440080460070800412008601c034080055681c40030070300003985c103202580540c3c1404803e000c0d030000180d005000a401801900c0c0042e00c42c2a0302c0c0f020303440341d0301c000c900d210701c2c0c4441c070148038010401052 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 990723732 1250 990722482 990722497
    0x60c01060b04081903020c04090606150e01020124260f01020c071a1902010e032d0903070b0a05090a03030f0e0609060409020304060f050702070602061f0603200a0203 73
    0x50394070b6081158000ea568203900c04c002001a0007407483c01c942c0c3d2425500014400e401754130300141058548641558900064204002017170410342201c0082da424014613064140700005042c110058400300d5141480e5401100e0030540b00b0159040d600b0300a0021b100482c0b200c0d01115242030307803861124000d5004044203c800c0c0907104002c207420540c40c3c06050303280b22039110249000140d030085140801000b81030002c5548030740c00d40e012510204080c0c400e5001000a07404000401e4143c000070110785113801c80040f1061000352803e59011800308111200380c0041c42c0d496090303000450b254442c8684181d4880350032030001c824154800c002041d980d109031503d41e40d000324401041803a000e0b00740311942c4000104014041042c01e50055600544201c402050000c1c84003c600c0c2a5102140d1083c0103900080081120380c0d4108040780c2c004400491000c00040e070042001ca80b24107500aa005040d150129000d2200080c0d0120900f0440c0e001c3d10b039125200d000c0d001b503e0b0380c007421 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 990724982 1250 990723732 990723749
    0x50d1401090b0405060c03150f0f100509031c021c0e03030f0a120603050705040b061201270b0603132a06031d0a11010908060a02030a0c050c0a11060c01060b04 70
    0x10001d00c0311941d4108aa02900e05d9200345034180b00c41808000012107276940c0035810107940b07a610983ea480b041c0303101034092019160030fa22145103100749072030480051342d00301540e14480fa4100c40190040781055605841c4180e80c0c0c0d44a500c0340c0141e0701d8100320919190540710000e5541d181a802e540a0800501d281d43d071a00c00348101198a000e80ea820701010b006900f050340200b00d2458582c1c400d0500520140c03010382131180c1140700c0d028a8030b09902c0445180c8500c80c4070036034030081c10504908c503c10000c0c10070540f9421000718655000c02410494403841a0600303d05100b1217044000c00c0c0580c030316032030058a9510f044101441c246100381004a41050034481880050107090b100e0800b03164010032040c0301c140c0b01d906010001003861f6040c841e442501161524003817020320b118071170204003d681d030f0170b002c80e4202c02c641d8002026410040d050041c1c80032040b021981010494001c0d10000702602c000c00010841d10452550035419840c002000525039204001b078800c868450 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 990726232 1250 990724982 990724993
    0xe041a072613020d050f1246030b0a08070f0819060504020406030813030507080703030210050c09180108060a020f09010c0203160320041b030e01060e04051b040b010504050d1401090b0405 82
    0x3c0991040c406200c080c034022300410418880700c1c0031621010008000264a4045408072110b404070b041c1d0304450f0041003040d00102018400215403006400080c0440b00003401c182c80051610186059105001881c0340d844e507020030701355500c03608040c018540242446a4907503c01e280c0e000182c0c080c3c0300c1101c440c001e0b0b4000083c002c1c1d01184000c06c80ea0181c000d4895040000413030001000700902d002c03940c0d401400850503c0e181c281c10780d642004100100340b059410710031850300c0c0401c02044c01c80c101e80100141c0350f0303040640303080d901d074040d0a08000181ea0302c14400030f4100b2003035440c0141c12116841c1e0000500c450144081c4000071342000101000c21840706000a9451102500140c2c0c00c4c140500444a8880e5101e00d114a501800020360306407150040281c440301901e06403106d80c0b284404c0d549000c900031040705c104100f1a0300308401c0c3c1d00e9800107041d6000d64070034544a281d11801d11414019002079140c00072050100810403c1c1c1356142c5401c0002054400b61a0b80c4581c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 990727482 1250 990726232 990726277
    0x90b040605120a110a150c0606080a080703110c040f0b010806030a120c0807050d0e040e151302011803060509060703150e041a072613020d050f12 64
    0x40c2d049420764803200e40140c0b00111036a194034442c44a081c3d48190405c603103001c0060602e4070118840c1c10303c019a0b450b08100c405604183d01503443c1500b1040154104807c0540040c01000c00c03202c00c1031345810040824942c400f250b40c117050500e0144c94000e07081180181240040354030846007000241c90354403840d00d400d07040c5641c81c00d8501c40281448a41c0d000710741c0f203d015480c5880350502c01c03501c440c07800490b503a4150421450300c104c100400c0c4c0075090b5526510b03190140c14145101180100801c0c2e103240d1804251000c00342101103225450002c1c00b096911842c6805c4420612410765828240d1b603103880700007444201c8a50740d83e401010080b4114a22034091698451f03c4060310501361410680c010b0400d0740013400880318050300000b0010141e00750b030100c92244032180c0391594404410030030111008482090800d03045400020000c0100c9580030b88031440d07030180c50b82d80c0c14404600e0000d1030441d5441801c0d480d8803a468080f844c0005a00040c6000100c0c01320410841c1c02 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 990728732 1250 990727482 990727489
    0x120103030e01020d08060d0803100b0c06060a0b070b010b0a05040f08030c0d1106040809040e0109050105070e0103090c0b09060403021306030309141008070e0a03050303010305012a03020a051201090b040605 90
    0x1002e40c6c0c032962000110700541d02066006000d0f5400500e4040b5a031081a65000420303c43d038030410080d90545c0045013003003654a0415013190003050100405460703c0016541c0c120760740e0050007007001c075180120304200c0c101d210740c05860252128003403003120583c0f2000c04c26030302c1c2c00044007405a8441c1c826044541031140604d80c1c0a043d5220090200c1c5d160b542e5058110303005246210307042130f500d05945202c1402405544102405000001014104048010700c2d405940d41c40c1d0303060504111030b1800080e0304800c000300300c074100056591200b500d00009081c43c0302c3c0c2d40c80a54000b40c00102004082c01a074445c0301100c0c440d44a6100080d55180081408081a1740303280d440f11b00062404101400f80c540e240c0d21144900d08281c4951454002581e485556041500c4585c004401441006001d01c1040c0891180c80450300342220b207100c40c0040a040c072140c8104058010584040e414022000d882c42441e0350040e220013980c4034944800280352185d0014802d40c10240005030070f04 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 990729982 1250 990728732 990728747
    0x80406150810020a0e1309200f0f180c22120b10090c120509060925080d0c02030c0f06181302040605070b16020c040c05120103030e01020d 61
    0x100c200d0094411008014600c00c02904400c070301d9401c0c454043e60a10541da1840106e0040d076450304800141c4c2d428908120940c61084080c42c503031800344040c50400e560345e9080041e00075404413140311a194445001c900c0600010540c0a41e120f0400c00744140a1001400b40540710181c400486141e03420581c0c036201a074aa120300d002c03e800c1412408042418011000c0d0320040d200314a1b20130558a502940c2115888002800002d03810303d001e0700c040f0004d00405811445c000000d08442c2402440300e030319091034100c0010b003101145000300c40100640510802041c0040a0785c13510f809000d00030348109244070040b4424050345c11706001c0c600c1d004511820744240a0b152030b0600300b03c1a801c601c890100001e80390f1081840c041101415448d00041002d00450f999151f02c1301c040d071a0140d075030303600074004c1038101d21020004c3c0e449940c00119508800e4080701d021840c80c100c0301c802e40301442080123035004400c86000200501da045038942e09455800c0c2c0c00ca401c2c44030101011074050 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 990731232 1250 990729982 990729989
    0x15061e12040b07141c020c15010603110403050c04020a02150a0911030102120f0903070203011b0e0d080a0c1509051f060501210e15041509020d03030504031e08040615 73
    0x1d0700140420500384151030803104050726038040040c64034041c0b004081c03900d023060315144119035911700180038813a4140a03101100700b40c0400039003031900b980ea410791035002d078004060003a40e01107407102e9501c0c82007100c803140d81e250442c2815141084030b010382c05086c1040c8181d034034241208060855050510071210100b022495600494407a004501401c1d0400340c0302e80500e00c000e100c4103015903028072800354214120b0319404240418940054104180d4150003072140107030b17212600203c3c0c2594215201420f9625141c020113405203006040007040c61507040d0342602d0002500304000000601400e03015108020384801860000c2180503134141380510360029a580003061899840b00390f640308410340c0544003141c032040705540940303081c03403400801138000454000c1c070050111444070001ca00c80e101e0024401b41940d070300031548040138200700600309a651b000040506100f48200140b100c40c10145802607210b51000500b41d0805603401d85140745041a90b0540d24040201003084 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 990732482 1250 990731232 990731267
    0xc0307030233071202181e0d0611040b0408010209091518040501060b0a05190203040605041e0504110706180c030807060204080303010303030f0e0615061e12040b07 72
    0x2080500000b92220b81d070181810050000820043d100410280090403150790319040415440420b5020022981c101900d0110b000b412039115a2003500c588000c202200d030009400308a80020040c1700d0a01c2c416030780051449480480c1c04030320301c40190000c1c668072100300d4403c2c030107480e461840100c2d5014480031a178423910000c034420803100355030221030707019000300000510319a50741c1c5050125803141070400c0001e00000781b1a8588007901d92803800d041c12a20056040c94202070303001d0082d1040c1c1c01038480d00d040119003440602c41003500f00e405000007500c14490001d154805070159045a0030480b10641032002d030b880700d00d01c0c005c150160180c00044850303805165855021030795000324021703550035408000115125038200000c0d4000c40c03107650002007003040c0f20865002c448002c4511900d41e0020001c0c000450b20780300c2c1c507070900e03071044031180e5881c040096070502c064405071501d04038120108070040150049001e0f075106500420004500755104a1f00700c4000020010091a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 990733732 1250 990732482 990732553
    0x12181502100509061803070206041214060c0a0809100606081b07020a03060c050705060907030204050f191806060e01030b06010801031e140a2f0102100218060c03070302 74
    0x5020035005600e01c0000b0017202901d1405a4603004580f6a0780103030401d0000c406018540000c21031b003000f1682ea20a42c0e0701c003403c81c1d170616000f4080180724001d40c8104100045000c100e01903020b10020881100c04801002110b81e03d0f032001c1c03c0d4060858480b00c00e4104981c0c241d1004c0800d9044540c4d5230350081c42100300034110b80e40c0c88001c2040480181c02c004045c001280004c204110703060142d8114001010345600c0c40c030400c801e80340002c06011201e0b06a40030302403031007000801d14880d4103c0c7c00d00402d810340b6104440c003940141e1000a000c1c43d04210340015909904d141c12410782c3e004403000c100302d0f5286801951141400c4c17100030414140d50350080c0030400c0d1043c00035400c500c1041510060003000c04c0301c91a00444002c00e480f04126120f113545420700c488080880d89010140c014041d030381c003400203500c910701418450a041d0b000200e1200c0c42c07c02c1d90400b450500010b102c40d4895104604440d034941001d80f0031805445400e603a69090300d03a007400100c200603100d0301503d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 990734982 1250 990733732 990733741
    0x30b0102100f0b09010803090f06090f0d141b0f0f010801060e0a03120f0e040507090501080406140c0403120305060904080d0603050d030b090c0f0301031218150210050906 75
    0x80091564503185501c1d941e8840c208070710b968580000324024011b0000a6072142905010800e03001c1c00185409e00c210703020441c55201d620b882468404c0e52100304c1e211503120059042ca601c820340582c094040138018640d0f01c0b0b00703402000e40b0f250400b07003007034a8092000142070144001c80040d0103201c2c1c0842c801c5001003000511a481ca8910310b1b002910030720465580e07541f038022800e408107507480402c441091000000d40c2c4000d81c000300c49400c8600780b0080c00c04030000f40c194107160080504210b0f000c0005010b024840d00100400340c80941c1c18a143d150424290f82e40707802c6800708076241c40d00c4a5107985243e10a01030300340107400040c001036098995a4a2102960002c8108031100b61540c40020103d0000e1101d1440d040309503c0c0802c20001410401014000046c528810030600741302001102180c0c5060f20305680d440b010881802000940545e40300403400501ea01c500404c00e00401c2e41c03854040e20400e022182c0d000c6411f0102d00700c2c42c43d025524100d49a0388564800030029 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 990736232 1250 990734982 990735013
    0x160b1006021603230c13020d0e07060827070b19020601061b02010215040c0f0e01030803060f031207081207030905120a18081e0a0b0103230319020d030b0102 69
    0x3c4d2024501a02250010003255000c103040c4140e0310340c0021895130201e04010624014003500042c056020080d20100781450000780c40708001a220004c00c04580802d45404c0c0a003086582156106404840b6480e95450041102d640004488000701d00c0000340d02200600001d489410399400b0748502c41c00000680c2c2d4502e25000c407103000e90440c03203080141d1140b03d90311030000340114025103801c44028102004210100c505902040d41c62680400410101e00d501c01500e8001e04121101400300130300c0d10001e0701d0220301c0d000e8500f060500050840802c0986c000400e04402c50159501c120740c2d0340d071016002c075540b1010103000f580262101100c2d8840040003440d070801e0a00f040d44549204032641400c01d11190482e400c2a03010504191000d13400c08450301404404100a001c171062555510048403010720008000d28090603c0c0c1010500419070b0744001c0c05924100c81d2641901064176210160380075440b805405400506056984a0300a22038007107010703001032400301040c5080707 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 990737482 1250 990736232 990736283
    0x70f0605070f20030c120a06050c370305151011010f02040815042001030f0c05130b0f18030a05030f030405070e04110402160b1006021603 61
    0x200e5581c0c0e9405101ca000a10f00400c1d00c100702610301c005410f1aa1150902d0b1400f540c0801c0c25201d0002c2c0f00114010140c0040e000c00c10300d500c0700010034181c40da031100c2030041c020302c03044074134145481c00c6101c000c0c1c8070210400d0104220312081c031034550140038184d04071201521450380f10304805070880400d040101807201d407504075140000c82d04800040030760031200c00e416a088501d40009042100c1201081711034104404a00d12640f242003d80c0c03403e011b0303507482d880010490a50702849805e603000c2c4c0d000344943d10a0b0700c030a000c0c41410400080c00b81e07001103820b00d48542103117004201e0b940f111003902d1400074030001480c50043c0003810102e01172400e0044070380c5480340d5601d807000920f05002400f01925161151303505e03400d15107841030030900f01ea0048030f05101e00b0307010840459081e00510383e42c804199001030b07852501082c0700703040c6281020050400b9840d441031250418400c40080c044402c44c0e42a80d81103000805648108541d511010306020ba01d01c54064040707081003c5c = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 990738732 1250 990737482 990737497
    0xc01062409050a0e0a0c121b02160b1b0c0405010b0913060b09010e04090f0516150c02010c0809090f1008030f0a1b060c02060a050a090506190b06071103010e070f0605 73
    0x70210b00541f000d4101d00140d030604042001071175800c1d0980b0030102e804010010b01c03903000c04a4040c1a906141902400f4050080141801052444140809803003444504035908006e4400e000310741c2c4800804d07000b54482030300c4031300804c1c49280120792000140f02e8581641c01001d0601d00d410406401192100074003100c0719440b03940d1ba078070200041c0a03840712000d2244650040c14807089581081c99038201140e0012101000b600d00118450743d1100b02a06c419909007401c031110329050a182c809802000300c2c03107410200907002e0050b0814600700d218411015144014005070711800a0b549a0050b10b90582d09030b0003d100d4096458001c1001c14023001500403030701940d851544640d400d8900e40d0401c7c8015801a10500580301c055026040c3c0c4028015020721500b0659501c80d50b540800803c140d0340721520845011440959820104000c400188250b858045038205840009450841c85100351720304240803040d60404204003003114540410f2030300032841c3c00070079107590340501c4 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 990739982 1250 990738732 990738737
    0x5070b030c121e070c150207320601050301020f041514160c150f03050a06080f061e06060f070f0b040b06030d05040f05060c01062409050a0e0a0c 64
    0x1030307101c02c90480e10b03140d4411150800000b03610003260003010702c003180c041c091108009200700c0c69008207481c01002d010003620034400580c0c4241a040003013403000108482413520500b040002034411412041d420301400180590302581d0f6110105403c0744143e150300048000188410095003082020038a0303154210b050501c244501142ea44015600c2030b448806910b181000c142c0a0111854400780030f44403442da10a00d416850381d010303128044600413201055215000510000a203030440380040c2003a0b01111040c0300d1040318681c98044c01c031f6440d06030074076900c081c440c1282d152003201d010360401f80c189450803900c005500101d078004681911242070010310080010280090103201d49e014500030708640c10501c081500b030004402d805000c00070213101c02d10020682511080072202d0403903c082d503440c00d803403045000d40782c940e004002c486140000c10300703a0381070080809200c4040e40c0d5110b42d110340b50400c000c519a01400358450300b021030f20026107600e1701c691060001004d9030 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 990741232 1250 990739982 990739987
    0x91003020c0a050327040c1704050c090115031a0a05060a0c020a090204230a060c020114030a0501060801170d0e0d0f0809010e060301030b06090c4305070b030c 70
    0x1e4854504d9079000c6a0404400d01180380e030281001d42080000f0442e54048406210082900600078034050207003902078194041c0c0301c081810000100304050000102030025603980d81d544002042d05014004120086420440c00c0315024041d989040304584005003101c052070308040074040a034101c4010182448150420391025a48681215006100900740540c2d1a0300b01b01e018617641403e40c48a4120720304145240c081540e07408040d03010b0322030394036141400d5079560004885004c10341c00300103407070300c030001c20300c00081011b4104605032440c94640080ca640d0f81e0004d107a008520040f00602e40c0c001d408a03500071403140114900302d80e401003016078103501c207890352580c0a203400003c5800c0900050544000e5070881108440d990088071618155032440d2959025140000c0110b8840c3c4c01000010301c10510f41010b4801040e0480c1c1c95281581e141445101181004041101c0451018039501e01840302208084545030348100540005881c1c4084813080e50406081c464801005 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 990742482 1250 990741232 990741253
    0x210c0806040807020114090f04050a1d0d11030408060c0a05041e03060506010c0519050f0318091303020c120c1215090601061d03011b020a17091003020c 67
    0x108030480c0103501500040395100c180703100140003240c0011220355403580912020304166500b040300c1003416011f54000c80e1310f40e07420314900300a000700c48809820181940c0781d071607041000649800c00b140b513503c44460070243c4e101415540d0080b44a003000030b5114a0015080b502c60b03602608400c046820120700345900c80003189021424000c4184a40c14084020020b00000d40106900301d0790a0811004482003500c50640302c56000c00f81c2d84d0340c40b0516030600204141046200300003050300341034a4942c890242c13180e80401c400c0c0b4a461080d4040c130089100281c22001c2e030750003254550000c0c00c03a91891030601070340300714820745402d4501501442c0310045c0c0700c0348240c0c2d01000400000e0455051408501000904040c00f00b0045030301c502c005000300342c0c000802c1d20128521050394038803104c114002034050720502e5a1a5060000c0141034800c007900010741c0034400740b180480c0075000d525905034104c2170050700d400550045040d002900c1142c040c1e801022110515000c2e281c07250303007 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 990743732 1250 990742482 990742499
    0xa0207050d0305030702060a0203070e0402091c080d1a010f0318020a0609170a05031213050102040b0304050d020c031207230f100213060e0301093207210c 68
    0x41c103a40503404182d0000070020140c0e818001d103075111240f005e00b1070540c10820001480e400c01c02c03940ca40525400a0350324250382c0c5681407002c5440c10481d001400b0016407402d4002c5401860719a84241c1c20310303600300344d050340442080441800607524124041c0075400120050013140b14400358071400d210015026031a2196402c0c05407195442d06c2c02014601b01c04105003c201c4490340714140c000301e20b05070000720044210744440d0302d0892000c21a485603a12081104c2c000d0400600f2503200140025201d03c04c18003862140b8020000c4d50040d0700d18800c02e0340c1710240e12031401d616411110340c1103502d601280281c040035001c4e1100750354505e41070790103102d030410400000300ca41c2d000b40e403406000c0004001c031407001e9030036841c1582007004804070298511000c0c02000c00b80250100440081d4500b540032800050f04180c6001c075122141060401810345007c5080030508140808200c0401c000b880f50204c4020041107490060480c01d0424843d0000c0800c8811800170280094501c1c3d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 990744982 1250 990743732 990743749
    0x609140f010606020706080115030b0307180605041a1003021813410408160c050a0504090c031704120c0503070f080c0d061503061e05040b0c0a020705 66
    0x5451000000c2c0c1d141c28a64041d2a0030940d0344034004002c00c490040c400305a11409600400f074150401154040c0307040006400c3c4001c5401120035100f4200c00201c074001d407034200504a4505075010445050044540502480c6c2007880b10b400c8507440a02c00e408074403a600800745000071200b064528a000d200240f604040c220b0f802c3c0c1c81ca40c85d01c0380030345288211001002c0140c144043c0e1082c100c0f0b00142c40302c143c040403038512360406840c000101400071003011118003401c00314200c0c4521050345800300c4812006e00035207018807004903010505c7d04080c425004410382003521a01000e15696900300c0e800380f51404803000540078803001440c0d0f0000551040801d1140c8a9000224100720900d4a80803142c2e1000c500902040c50401400f400441d06180a45094503031b04140c0700e49040501c00740180400b10040d10301b0f00d000001c14000030354800b01840c9103040f049502445910403100940701c0a0340c02404400040e804100315160f180000d100c16941ca00550318a50ba44400007080344 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 990746232 1250 990744982 990745003
    0x12050403030c0f03142b0203130f030216061d120a08030c04241205041101050a201e0708190501060803040b0711030d20031312050d0f0804060914 64
    0xc1c4401d031b0400d50903040d81110605040c1000021410b62030b1420311000041d030340e11006003a0300d8400303140d4414076209004210323101e522801701003005035491000900003088501d071316040400861b01c60704645003400c1084141191301d030051042c9aa103441d0100580e001420040d0050f00801001444540340b1120f003005200a100605001302040300c05001000c03004052a8814508020000080e00960000d40303003443c20301e043d544498040405a0716440c0018111040c2c1c1d50076061050341540005044c01c0d13450101c0a00e4601e1600d00c03101030750322500d40c001c81c1c10700c1c1c008903900b039034240c0d0a011005001d4000e0001082266459901d00c2c210340c829017001a04040014a10050000c0b01c1c0b0807280d00311040c0c004000c0c00810a0000304117105400c00409100005040d00450031820400d82f198a02e000c86410103569031500c03d180540034480c403c4455002b248021400a405144c0c0440340e240303a520f070904e581c1e46680d02c14008000407003084848804400f03074011110303803c11140121 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 990747482 1250 990746232 990746257
    0xf0a030906110f01060f0807091104090b040914010608150f0a1e0f02030f24010302030c04050901080c04061a030c0d020705030a0e03061003110d24060312050403030c0f0314 76
    0x100b41884070084c100101074001c05601410142641a408800011902190403d00c0d00283c0e08907440300140241033f8680019103032070210083c1803060081984003404580b440011250b009144101e40d48a44030101c0d4034209000c401400510b014400303800c01540c1c6a44d90300408220101920088120382d40c400709190001c1e4080b080001c5100caa50065401c49003104a13142d41c0456045e1718640391000100060402d40c000c0042509107807072405450150400419a4440d0b603103880c5401c0c0d4a04820280b248114100301d00000c2007000403c11088500400c00c6039891542c4502904600d1307403104080c606010f41c00c00540d00130510520140288030915507845403860140401c051a2010240a5458031881c202c010000036020400058141d00c0640788600000f215003400251040c0340c15500000e40f03054070030074034040d005503c943c01b5039100e0581805461017182e0700b103d843c0583c3c000100403071640004031020072507990746040c80c207206e86850a40da000642e40040d482c4c102d070200546 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 990748732 1250 990747482 990747509
    0x2060414060c0313141804110a0801020c0f010c0e0306130221030a02010b03070621022a01050f070801030813051f0e09060a0e070210110301080f0a030906110f0106 72
    0x2650a030070040402e880011580c040b60b46e03104500201500c0e4014100420030384208543e1401d41d1284446840180b03030b480700854603442808a181e0f169140d0300c241c8020b6500c1d0022580c101805049000c40b80b4901070010f00243d5074404006440c0700c041e1a060fa400701407259985000940201c00b0140382040030040c546034400704002a0a407000440d003035100307400c400300c01d014082c0c1c070075542c45040303003c480c1c410b00d030105280c41ca000911400702c68080c041305590319a00840c41800e6294410302445d0000c100b00d42d00d08480280040081c0d40b004002544503004002080194010782030a1550749070102500e5650b100140c2104000380b0091402c40c2602e21307801e07405030080c0300f85803070140a568140b090300d0010002032031001d050298103454443d03500031514a6208000d03041d03440c81d0074401000510110008141030341c009106440c030a1080d0758522555803030201e4509882540350710f84079002c03170800d0000c0c1c4508034214a421520b109403c4400301080b000d0041e04028840800a890b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 990749982 1250 990748732 990748739
    0x80303010e07211a0d081e040306020309061008010506010e10200d0f0503100308070305120a0f0b0607110402161e1202071d0a02091306060f020a02060414060c0313 72
    0x520040c207101301d0321520009084c0d20100b6090400c648189072a000901c000350201d1503c01034601540d00041c0042c1d20101c10018000b0000685c103000c0c00a1019155a45982c0c001450a070b03942140c000c0d0004054218944440c101180d5032aa4281141050a244903428000110402c0d4054524880e030b4441c645a04515800440c80f07840d00d5440d01c0d200e442c5142002001000000600c001060343c14001ba001052500c40c10999582d0403200317444040608000078481e0103416094803044100d86400c030110760a1501c041100e0103550b1080b03801c058810950108002500000b0190a403500f001c00807800241000903185880d50010f4070345c40b0500040d003003900441c9515028041550b0003c0c809125024581c1c0c0035030b4180020b0403846444c0c1d6241111040a401010055500300c60b008907098080309480d0400320079240c0761381d035440003d0041c041c01c0380d94504220380a07402500800050021100411003043c50f88170192070b2520303004c20300301c1c1c1c18a9a486041210182000c192051 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 990751232 1250 990749982 990750011
    0xb090108160903061a03060a0c1b0b061021020903161521060602030c0105100b07080c03040e0408090f010912020d0f02060a090608010b0a0906030e28110a080303010e0721 75
    0x29001c61010320465880c10b03e80d9035030104684bc080c3c055449a0001020070b085c0c03c4c4250747c12501e2114054900417400542001c00002e9084801c0807031080c00390301c0e000e001144846850300d080352528800b0b02c08544000000307940baa079004000c0d144821401002c940c0d090480c1c080e000042805900440d0b8480b09070300c22500319a000303002001c205500c604200682610742090b0f800013504024030740c6d41e075080220341b2895441507600c000c486041e0701c0308000c00e01400b00d0282601010654a50085824000044031180d1040c02180f80e10500c101403940541040d20007007194920906001c40045800e0300080c000390010a9100009000c00f807007171186c1a0300089090052020f10b190506050807244054906081d500400d410140d80b404015071150701000440280c0c8030002144030100d600c14401c404401000d04150b4000c461001d0070081c5081402c0800102e82004000c0c60959003404401c0c40603000103400001008440c880c02038102c0241840c2d0340140a08501c0003c0101030300c51030 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 990752482 1250 990751232 990751247
    0x3051603031b020619050403120818010e031b101a13021c020a03090f060e1b0a03030c051614010e0f030a2303040b090108160903061a03060a0c 63
    0x211080b40708140c09000058407039200742e4805800294190300c412464900071902809160310103800a0b442c1880715000e1a0401401c5018601c45801000380c0074907259a40e003a129414a010f200c0d0703204005d4012166005c42024481c0e10341401913615425005030000107a1300090380e4002c8600e29001c0e560074514140e0112800846c08003419400d01b00c0110310400590a0b450032910556000a58001040d10a5001b003040716030103009056180104d0402d10002c10039803c01c41c0d00c52150312501561449284c402003041d00000b410318003c2410f6035400c44903a00f4160084440d441f0789460003c0080820440d54050903c20180c9002e0f8540000010403600c4c01005190107881303018802042911f0202c0d1590b0020b401c0340d901804014003240c03803015240d00b412813003910b000c04203010425a1840d0010324520100f6030305c190032501ca443c114030b0700b00f1401c0d407900f0219a040e08100001061900400b07242d80700070070800e00c1d00d2010f10100c3d007080c3c411180c50401036960440480c15940183c00c = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 990753732 1250 990752482 990752507
    0x90a0501021b190b0a05060a031e1b29090a17060f040f021002102c1614150409020705120f04090906090501020403030801080f03030f060f03070305160303 68
    0x1200070400c191180e1104c2c0c000902440441515440014810303103c0368400001541d0200c4040260300307554803c1e005220340e0000c1107441e01e1581c1c407400c1c000b20900d9001070a8403485280071940142c2d074070500ca203c2c0011401044c02c44002d1100d484107581d000550f000600c1005c07040e0220400125055050a0004141c04c1594810105101c0481c0c0d601c400c07030802e90b41c103903031176040050074501c00c0e490700103001820109141400e06003c1c0070203003051101d012082184003011030301514920f10352191405810015170403802081048648503c4131920340c0d200707014000c00c05a100e60042c04035035a01c140c2026803221380000700c034010002e00300408810019560306131814070512580c0b045107403040e1310480d0650703502c0f000d140341032100d02c1d403200101d1503028001315902e5651303280185c101c18007440345158074000c452103944c0e94900842201d20514951804c8526640d840041000e011001c0d0400781e014801c081c00800010005c00c510408002c1e40c21003e100d00b03242d0f10f4003c1210b0390825 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 990754982 1250 990753732 990753763
    0xc070503071508240f0a090c03140f0114100c020603040b07120b10030b040b28080604120f0203091201020315030705060406230a170601020f1203090a0501021b 70
    0x102114610689030004403d80d84e03003202d08050072025400000e50031302ea1a08149441031500d85001045034140e840a040c1144100d005041981c400e11110401c200911441041c00303a4035084c1802480c00d401401c0000807141170034010154240c0209040f508210f50484400028206203e841030f0403c00d00380503a44050b40c14840e801c060004541c075141005984c1c41410b4541405184035510380c0c10080c80000c0141840da0f146090642080c4840c4245110145e020420480402c1d10100400c03010704c102d411103112980405558800c6403407010100211003180400c0c0a0944141e130b802d03441090200112002503182c2c14050ba001320108240e106c518401d41c41109d00300215100c600036902260030034246600762480303442400503000d0902e00d8255014100055036036101e50400c0d000f010100011419003103d80c0c0e03c3c0c00590340c0389120a241e40c0f0300e84c0003180c900d8100b141c4c4401154002065015108041016a40c0d40d082e0780200303020480c260504504140d04d1903040101110464096 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 990756232 1250 990754982 990755011
    0xf160804080a03050d14070e041a040218040c1d1003110a1701060f081609080d051e0c030316111014060118060e0f0a03030f0306081209060c070503071508 68
    0x40e0152008d640c0c1041c0c68002c0d6203d01c0107802041122642c07034154a800f5000b0355441b43d01c51080d80c19041c001d4522886580750200d40c0304184d214040c0c911901074640120071400285c0e400308054214034280c40c000301522042d410700102000030207004184000e44800001c0b109107102503c1110b0145c20050800c682e10705956031045d030122405401c610041c41d540302c651781c5101c0031940d95155030881005c501c40e08c000c00704007640c8500204000740070a40c010000c142c00c0000021720b8850a1580d403040d0340113001080d44409400c00140c08284541004002d03500c2244c230403070400e100c007005403034040e41c2c4100d194081c01350b00c2099544400c09281103c8440403622100e01543c145005000420580d8402603040351625a002075200340e0040c144c2501329560316000300000d800440000003c0e041c80c4000030303080d200141203800008241c2c5c1e0a410300b641d045c00d000184d04603400c0458580300b0140009103030f842c24480d10010341b480f070110003400000050060501c02c8090104207d00000 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 990757482 1250 990756232 990756241
    0x91103100c0225211214070b090717010b031b0303030115020307020405040c080f0a03090618090f0203040311190809120d0203090a06050f160804080a03050d14 70
    0xc554100786034080741150a03c48800c20a07030f0a07816081d004038100506210080c09503e0604014118161003420441413049000b8400c5400b0b034968018103d980e80244094000141040000c40c1e100403000c08803040c203075880064030900200c0224820459650710a401d010341418800f41510103a030702c0c2122089404c1001180d92480144550025514684070072070b11284288200c65005800820511442c20f150402160304d140505c12408036100fa1303c03110f52400800703d440ca0006802d91508210145010401d84116018451082c1002e61048003c40c0107082c40c070030401a012204801038891600d464090182011000fa05655600c103414003d40307075141e01c0d400032055501c06034141d2034008103004540015407440043e48240204c1b241c0c007091607800006024059000c03504440c3c502c1c0c1d1400d00759000d11541c01102c0e0454401c1000c0c2c5030109010800340045407007420010310301030b62a10094188020fa070002c0f00060b40021342501c2c07204890089803040540b203c603111184c2030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 990758732 1250 990757482 990757487
    0x130e0d0e0d060c021005240f03250902072603040b04020114070b070c020a0f0f090e0a05030a1706091909020609100806031b031b03030d091103100c 65
    0x6850301c0080c911a01c0d040c80740e860314400e006855201d40950300500241c00c110980008100c3c1d19181032419055035a0100e0742e6280c00301c0e40315225040a030182890524000225607585041d40d15203c00040300c007800101da107801d00c014004d9074003401100745000921a440b050b0306a078400007401501c0e00b4801d0101095065010300e800c0390303090800c0c0d100425078003220242030154900180070900c00e6006c001710380d50400ca01540311442120358486084d1142c03d102002c011a004540c8018908642440301002d6075001603c017260500071203000b105190380d81f51441d880007401b00d0000f40b0302120421402451030000740c000a08030b682120915120300003a0160141040d81d00426845110680940d140c5034112003c40c00040d103408071003400790801420035507080d1400c60280c0301d80801d01400b04100c1d2645001203c00030058548062011084466080710b1110310394540409c001e010000c440510a0380c5080b8803501e0061200d0031494201401d209141016000c42410400584072259 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 990759982 1250 990758732 990758749
    0x90915060f03020d0f11070c05010305191503060509030d0f06050f040c030f022a010b030a12091805010302040f05100b07110a030501021c0b150a0e130e0d0e 69
    0x5040c80c0c0140c9503454200344001418a00080017860791814182250289501001f000b0319402442c00351030a6039200e00441c11207004407039000c9a00f401c02c680154549071504125868002c01080c3c4a04684a44030300b0100c520940d0b128605500010700e500280d4220300403003401d10f04401c0d0802c5203901e48000309000c40c5084000a01c115994014446210b01035480281c0f1040106411502c8540c540c01c0b40c0380041c990700e180e0f05400440f9008000d8410140200b02c20180058040e1601c1905607441c1400c2c65840c0224100780041e10307038085803400211542100601e488507010540c0c5d495030042c04201c07404003840f013030f07014184400c00c08100a10b0070b1328011204507810b103903903500f61800c00d0624148040103e80c1c0c0440c600800100b402015000781004060684c801d4001000085400d42140c03511411160046110f03500d0781e044060510150061900d542042c0c541d98030b5400000c0c075145c9070300c00303545d0b00745645880700c0d40c04030401c00000d582c0e4081030030941c080082200008003010f = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 990761232 1250 990759982 990760007
    0x4050909060115020d120e1f050106030b060c0a0308070c120206101d070f1101050f0619150305060a090e070f32030a050a08120604060509060409020a1509091506 71
    0xa80c0c40d58000450410b007007101c007640e4901c20446078040f004411240d23000d040700b807050400217030800765a813045117001c170308540448600c440288880c0f00d031540c0c152560b500041106040c082d5034406580030921420300f07080035030308507409442146071101c2241d450444640208481c1c01804044010221224006c01d8000d0081d042c04110782c18500c2080b00d844448960b0480194208030030312410280400307440d40217202c103d41c080c413404070110381009030b0441072080b031540c21500348840141718040e50210f03400c0803010f0107110f6a40e40b41c031b04000c181e03214010441020744c0010002c100c01c00c12004181c01030b201140c10440d052038626554005119691004510700107400c0c082c4103d0340e01003240500c0c05074044191055100070b0b0519400680110a030042d510103580001409844c1a208150555100a0441c00d0b20b41755103040c08010000c4000c12a00a85101408151140d00800705d501a4555035500b000c000d0510051a09903030307200400c40103204207070005120140d04000511000e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 990762482 1250 990761232 990761267
    0xc0e0106050906180f0d030e0901051f03050a0f14070f03020313082109060a0b09010f06081305010e16090603080a05130902040f0e1b030105060f04050909060115020d 73
    0x6400070800011426100c485c40c10303034440d24922002003059004100201103580850b24410244e0740c83d401e110350b404194001030130380500d40da8085116030090744880d030001e242c41d03000980441c41410f2402214a4020111410300104040040d803903800708000707801490525007075055080c100f190302c0c220fa2450900819054002c2480c0c446282450000081003003d01c01c070380300e10700300345180076118903042e110b007140380b420600000c0503424400800340c1204d035007103d6000c0d00d074540310007210428006000c2e00004c09402c41c0d080e0106000340a8104a002100050001e0300c403e03588250134034010754491158541000410404510f1041c25518aa04a8240195031702b400c88040403803160150002e13000107102090118011262403807003410b5603800003880070162506040303440c8202c140040d0302400041000180400d0038408083c00b620402000c801d8101070722100050302400d022240003070a0751102c001048030028003102003070b0109680c0043c2000c04002c0000034440ea01ca610300085 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 990763732 1250 990762482 990762517
    0xa0506031b120f0103050f060c0f070302030d05160e040b060d0209181608010b0c0d050c1029010504080d030b010e032a010e0f091b070c0e0106050906 66
    0x11409481c040700d18450a00b880c0448a20303111585072401c400a01041e01c3d030f440f40c00180103010100050b08e9000d0042401b0003800c0c40803040c600642540f01c0a0b04504501040c082110503558601a441c00b8040c0d00702d20381e0b000c0010b01b200600000e50441028412400d262100c0c0761910b60000700e40c035540302c412002d69501400c0022400062580c50315526510030030040104542c400503d21180c8502d0b60b407071020907640e88040301e50b00d0042c082d4041d140c0d004011408403190156000345408429481610b6211046295000c201c501000200155541d4403021000103601c00d649000c401c482400c0588c00c20b41011811513803454100002c105150381c591a05017143c1c080c181ca48c0303140d040141103031202074550007881103001c01035130385061a042c7c080140f80e00c0e60244e002c070350006c40080e0002001c02c0c4100300b0070271544000342100456041c0714408659107401d00c0c00400f40306000c0c3c0ea0702094540b80160501162505a00181c108041030001c006a030352105c1c100c0d4080200400401c4 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 990764982 1250 990763732 990763771
    0x30d080f130c03080a030b0906010e010e0a231017041e0807030c03080f090a020105071a09071401090b0301050d060605030d0908011401030302060106081302060a0512060a050603 78
    0x4403164a070345400b070003645020300000100400740009160075411954180621002041803002a070003d03117056000c01c250103425000e55210300c407a45400c41000304120142c40d614210302800c244030484240350082c2c1030120b20358605184a080480201c14940240061f402522143c131800000e04024810285240d00721031520f05024070340581c6402c2411070356118202d24002d070280c0700950007200401c010400056441030b110640910806c82e10026140202d03155004582d50382c45001e0071034981d140d2514298000c851400110302c42d08000d07005003c4c01782406403800c11080c01c559050304106480e203051003e40f0b400c1003682d0444206655207040b04c4000c4c03400c540613044a0b08125003501c504004005096032050b0303400100c0b04100b0080024a0200c081010065000d00010340503910000040001030b100310300c46980300502c580c401c2e05c420a583d0004185a01c002180c8002a0021030250305182c88a05c10940007a000c503007007206146440c000c00e005010003001162910343d005000da = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 990766232 1250 990764982 990765001
    0xc081b0a0f0c05070617390c0d0c0b09010e0712030c05011a120604020d0b071809020a030c021c050a05090409081b030721052208010b030d080f 63
    0x10440315500a0540f10038a41742c0f8030003400039041000c80e603802010580498003222000201c1c2e4150322001c100c544d1003c004100170a801c51184030382c1e40c1c02d0b40e010004040707000750a00c0302600c0031071542d4550ba20040c403800c110007455009007a0182c0c6e40d1425043d200140e40000d0884200d0303910108400b0a4840f904003941c0324169583e000d0015401d166403071045900414162034440c00031501e00000c960700c0850b2030341e5000200ea0094000e0514000500481c20100c4e11650051043c548038222521003060f203007190703055502070b4405030b4000c58529803407034141c0901e0003420100c3c802003001084041581d80c00600b1a01030105200000400c2e2071141d2064044074405038000d07200303006030040b91030000100e07480304c061720080c015440f8100c2c090340808021a000700350000701d941440708000c986d081c40b00c403514041c070003809410808403004464040d60400e21061010143d41d100b450900890309440c1e00340c054038460f401c07184d815a0029005030100381c2001c0742011807907072035640583ca07 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 990767482 1250 990766232 990766247
    0x22081b03270a24030c05120f0a0b031002131a1207050405062206020106030218060604050d0615270e1011030411060403020609040b220c081b0a0f 64
    0xe03641219100c030b46400811224044031103c06000d6a00304403400b02d10b00e086505000c2d144912020400c000003081ca00404001c3d20b0b500b02c9507408000820203113900001385481514242e20641540102d5000003560303220b01c41c1d40013410081d08924680340d00c0e1101103402d10442c82c0b19140c10341c510340898a10b911900941e4040e200c050303c5548e403508202c1034548a1030200d98211000100488042416403040c0a110100d03640070340400d071110b1410403500c47d80c280c02802c85801017414800081e03595220031141340c030a03008044c000358948940000525400a82e0421913180c800444c2070304000441046201c0f00c0f06505a00180d480d00d5001d510341070200e00b11199074240c1c20b0440c480c01604000e801140503501c03a03d040c5511410240912009011321b1001961014051002003c00d0030590080c0c400c00c00d008200080305aa10b0f2100b1103501c103a03e62400c070346a52005107c2802e5003181c800d41d00500d40c8a000c084007146421078240320321500e060b040800c204281e88520182c064045e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 990768732 1250 990767482 990767489
    0x501050306210f100f021312140109060203160e010f12090803010f06110f030712021009240b03100e0703080f090907170a020322081b03270a 62
    0x9036080308510140840e50384402c00030b100d440030b1030040c495018055506c02c49410040c2c00140030412407030480c0d10551106580c20903a101a040740e01c0c00c11070002031184011040c0f00340001078990070481280c12901464209040c280950f490310038605d6a00089411940c0416242c680103280c5404112406424044002050b1010200000c070340d008042d41d404040d1000c584d1902e8000d258120065900c0071660061a11034000708100400315903283c10710010b401c00c5004a03a410408a903000b4101da000d030a00740c4501e00c562007040011003140507483c1c084c10701c4407005e0040040c1800004c0c2c5600340c205040f010365644142c109061a01400008002c0d03030070115051b2140d00800441050313034850030341c140c440c0c400000010b030724501503c2c000000000300050f2a4a698038620302800a40c0060410403480f4424900004a071020340985804030f48200c44803030726151840c1c2c0c562071400a941412039103800c184414560076280c040b1400324100d07880748200e013002c0d0340d4020400c3c03a00d5a81 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 990769982 1250 990768732 990768799
    0x70c1703070b093702041d0f0d02010609060605191412010302030d0813121e05040f14101409040221060a080d052503080a0e070501050306 61
    0x508024600c080407602c1c45410584c0160810043d411540001c10303c140fa02c040f4507001001e00424016083c5688149400720b141a44287c040951036503542c64400030100320312007a0b00c0f4030341c1002010f0342801168020300300c02c03009000f098140b01d8050314602403105541040c0d1301c139044c417482081c45048107600108210800c1983c9444410400360600320900003a8002e1040140aa01c0d172031052044510418000e850028001503668461507121004035007801000341c2d07480c040d40c9052003416544001000e64490550721890410301c0b541d0781e48941e0110460f40c180c4541d8080c039895a00c14a420028903291000e9020440040340a40d400b401900e145c1051000c282e03561550030005945c411881e941c1e0442c403480c1d44490400040b5081c41c02403260b203804c070740e41700315200380030300c015200c411003090b441c6050b04a00908020445402c11040c0c0000315443c06200706095a403003001d0056003480d028204a508000005e41188406002c0c11702030a14010310b808445d06009010000c0c48661 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 990771232 1250 990769982 990770003
    0x6060306060b0c160e040b07111e010506030a020121091502030702010b0306070e011808011406010f09060c240e031c02090d020d14030c01090303060902070c170307 72
    0x1030060402c00d401543c0c0da0304043c41000203c02d0f0058555003903c085506401070729030582d82e10742d00c3d060716240162480d024050750030718401b80000c0c01d100201008402d1928084000d01c41c51845017500c5e4040d02c0c90b070182d00502c00e40320150f6070142885040c821030b075924002c0c00444a44c000700030800c0c5c0201401030242d2005409065515030020360084860380e00900c40b00048004140e11490140d41010120791011101084e95001c1c0c002c9004e1180500f0358680101e41c0d80400a023503600ca403c501c20240381c0385c3c1c01c0104540e008208100c2e40703001340c54204a12814460050005044110b003d0810405940c540c5c89244028034901c400c1203001c141030000d00008904641c0e25001000f0b80c601401c0e4050242015042620a40b001c1d082c0c020840d403010417280e001e01000c209020425240c10816101070b449644040004001100d446000090f021a080c2801411a5160b03001100070741d0040051002191a104115060320400341184845a00c014500341c40c40c0704800d4002e000100c50b = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 990772482 1250 990771232 990771239
    0x1210020d06050a14012f0a0f03030501080a0c03060209060403230d111b06220303021603031d01182c01080607050a020304091a040f020309030906070606030606 70
    0x158116604641c07054842031402c070340f9583c0d110348100107594400d00144481422185914580200404050400a082d5078000306203150601f05010941c0907195295100480e1081641c14410b10b801491100d018000f0b4122554805031485c170b1910001e0001900800c0031509980d44100f114015030b0311010365240c900a42c0b15100f041c4041089420b10360160007032040e041802a1000550f005210000c0c281d895404c0c0f034030906240030518440d030441800e000348500300c1f1141d0503000307540c0c801905c44c6002a01e14034009207001406600e0100c80b05440c0d4042000a80102c2ca007180280d441030a080c64002070360040302d00e45050f12940c0280f0307400810004901a03042501c608181d4080031401061034a80c0111000e05020300c5031241540c0071a0018040038841d00117009501100d02c103a92800f0390b5140345800b91010083d00c5c001c0301c0a0000454040d2030035202d40b00c030704c0f24240780a5045280407591152640203500002d801803100043c05400c0111960082002d1b40e48070341d00b00a503e44 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 990773732 1250 990772482 990772507
    0x91503010b09070216080f030703080a021e030109180803061011010606051305040b06072a060306150c171303150e1b06300405031809060f121002 64
    0x700956030040031146840441c0074030b00071030601401f016190085103085202d9070100c844001c001c0c143c1d90201e50038004a4144503a088420055003a0312554640341c1d41000702c00400c0316074401c180c001021a614110000070304d0841a00d41c0440216403815202d8031001c4141c0d8618042c10b01d070740b4a5460301c0340109070160002d02403e90041e500f00c840e44800e86071b505000c2119450016154090f40a0001c50001150445035030782102e1844040d4010642c0c200007203038011910740026020949440c001e10500200805401e00010907262402000000d602d030100d907500c0101c1c006690700d600142c150103a0180e46044030080d0352081c055110300c0440807103a40180788600b003050041c041d0060107207042c4141c001700314840b034004000c1071030071a01c81807070881100c4a108031815041100500d05103c0440c50254ac0b049028502441d92842808001281500b4115009201c2d0a000081c040f51f91a10400611860000e648040c03400d0848100740c3e150040307800c480c00000c2d00000e425442403c = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 990774982 1250 990773732 990773743
    0x21f0e19050129031c091203031b03020306090601050c0a02060c0109110604030c0e04021534050309042304080d0c032f0c03040b040e0c09091503010b090702 69
    0x815145506042000f41c5284003405100c025445601d42d01001020f0740e108070001c0e1440c04034100d410300d045404c1d9150481c0c41c030400300a0054000c03a58884403000c103001d000e03040c1000c0401c0ba00e011440c516110002580e0040041c08440c10083e001c03401400004080101858040c0c0087c8800e4444201e18a0305019214011080392040718182e0000a242040d10a0741e0542c0c0e1320102034440141801c0001d10310020041069a000410704008006000660010b020440c000700c11984200904c00102d080c0382c07000a81c4030003000c08008981c000c541d01100780c8203100812100401c580441c3d02581c44124041040380b0042c5200000f07110411444500604018640940602902c40078541c25400c581c3c650b00103a0000441001c000d189542c204481c0c0c0c98100c1101d00385040140004040e440c507000f54000608040000030f042c0052084841c1282d80b100d800700f0034a19003540d050100b80b03c18009803241e4410400c102014125960030740210036110ba01501c64822840c5c00c100081d62031 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 990776232 1250 990774982 990775001
    0x3060307060e0d0f1b0e0a0e070f090504020f0402040b0307020d090e070c0f150c1101200c19151a06040510200109050607021f0e190501 60
    0x203214034000050002d01540414240100c020580042c400342522840303142c0441041c11140500c542940c1050f1450084418010707000700e0600900c1071500c07680c03d20840310003403443da4495005200401000d0200e841c0300341030390794105012645803608d00c08103001706c0114034503550141c0049000300d01022100d02070342c411292542150303054681c40300117440200103400307a0740c40c00e00e168000403911070040720041e0100f44038454600141c0c500391140003003801d20f000c01a840da5140e900ca9140d040d44580d464107584a61402008036002d0910280124100640841481c0902207880b80b07403120103202210300c0501894200b0b03c4110180ba0419610740d904200c910041c2ca0040b482d042418a403181401041c0081c0180c0d2505003031500704004285060f00326000c2015043c02113291858108c0324101081c0c4000010540500780c1c0750480c20f240d4000c04140842d07001c2d1081c20390001a41c40c4c0c65106030800e2400003a8a912449a9030901100301c1610526501e00091003080200c15403000300310 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 990777482 1250 990776232 990776239
    0x51b03011808070c0b0f030c0f091002060118020f04140310090b0117011e02090a0302040921050a0503011802040b0703110d110303041104061203030f0f0209130509100e030306 77
    0x91381e4852008020b1070050442d0f80e82501801d00010b441c0014000c01401c0005980903110309209003400091721080c1c800044038016003181c0010040069004c6880540050b1940250305010910403a26007034000c51250300070482c01c41604400300d0b2000d01c80d1a6511801d070000740300d40e546a0a010070441828407403c000c007181c00f02255000708040c450f00b0244a0314500d01c8003800780c1c1c14411130207900010074403941720844000000c0141d99500c1381e8502a403007003030000701112103031100700340d00307051081e032007042c444200500021141c2c050f08480c1541c0c0207504909421440c0b0107108000d0040382c100302d403140c900050800c240b64002c3c0031042030072a6041100e0f80c0c000f441a040f034080c60380001c0c240075030b441440454002a54142c44401d0b07254058000100c40b642e5100d120500c5400034001d4011031b9540003511802c2c4818011503190005c94901545020001c0f4042400d50070400201c0a566649102140e50f6200034440007409505900c0700b84821019a1401c0380c0360350017034415521 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 990778732 1250 990777482 990777503
    0x3060901050a050f0d0c1509051c1703090a06110c07080309010f08060316060507060b090c040902070c1a130e040c0510020102070204020f07110904051b0301180807 72
    0x6007403a282c4580400c0e108040c0a596882c40c00c00140014901800804c4440d10440d400c003050706001042d04034400521656085401b6142c44244802e01c0303142d40e11041240003a42d484d0300440c11111018211005011445950391b50b1105001e084c41d0394071100404640c00d10000b207048107032201c05803400701c60841c10394801c19902c0c18640e82e030f803113210411b50210703460785400c1e01514042c6c0400e551214000d03060760044062010101070a400980050000c504003180c1c034002c0c02110721407001100030503100ca03041410074207403d12403805075115000700d40b42c00048000801c140042a0001001103a5090071141150403000505420078028000746003011000003849903a100c0042d8001d40d040903824141c241406e06012141010711416429507400300441401600d8a1006060340203010038110344411a504d005414034045084aa21070301003041400701054000ca80400c60b11011000c101034882c4000c00311303014083c60001c00b0415240d410080c028080d011000380358041c0f04850b040b6 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 990779982 1250 990778732 990778739
    0x3040f14120c01030c03060f2903011a0c1606082d040609080c150103060e030307020c042d0c080c130e0613020d0b0307120302061f080d0503060901 65
    0x901001e10036a001198401c0070020080e5000c3c0c0d11500c0100007900e0003065007a128200166020404e9202001c40c00306240250310f14541ca0080c10380440c0b0710b143c120b2a5502d400d0402010092808000702c5000c1d0000d500c0c0d070030341c070200028607009949124000311107584a9003d0003d020441e6000008540c0d01c4000c0200e40d0101ca0100380a058103504a036117803a40e8842c1001808052001c450380c40d002c05c0350b40c02030f110401000141c4d000c01d0f07800034140d605629104059603045409150f82d5442030091250f023a03004203141c0103421040c2c5000900010481402d1110303100d44401d48106004c01d03039180c40e51542c64000c188134403400d4070b40c042641c81c4e1108402042c1b041002240c43e9050ba00d0013484880701e56414141c00100060a05800032100c007a040201da00c0170603d07400380d0399215540c50b040d08041c031002e0005c108600e40d81720021807986002c1d49608004145140c42c034a610351803480c0c07641c107603040005009448110307910405403c0011782107034020f465075841400d1040000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 990781232 1250 990779982 990779989
    0x10201020901170703020418050703140c0a110102040b120a06050a06090603051b16020f0102070b0d020706060806040c030302010605100f0e03010e1902010e0618060a0201090503040f14 81
    0x300d00c034040c10303035441e1040c2480400032440580b003e000c00c41059000c101c001480900a401d048040c8c6d1312034800104c44c100500080c0464400c1ca000581500c030401c03c019800400900f40c506000c4c2a0404122420310030500b14028400d03504120320710000403e600c055020700189492007400500800c0101507100c0d0200a440701e02c9204500010b070100c801401860700c01d03001160000d02c00c14900107110040b4003060703a19000a00e107030f522401501c050358294603040c612150602001c0c000350020900f008103005a40c8100c1404848058000403044104551030703105100910106054620b641000d10b000540751033144001e5006608180b80422f013480c0c45140a09826103a4995080d061030420050790100d65113201c0300d0385551385001400d4810302c140a103603650313204000c11000441d8a840054248a070656503d030280c40240902c1003004084610603d402004031081c58807400d94007012400f4026a20000340350f40404034000541e880104081010390300c072540c0714852400c0070b1050 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 990782482 1250 990781232 990781237
    0x10603090b010906030b0601201920010e01111515090109020f0a11190303050a14100605091302180909060402010804060b0612010e06010f02070f210b1503060601020102 74
    0x10f020500300c1c1b030210340d496000d0032050303401825409030344000d08070800402d42094506505000100110601c03a810002410f211b03d04c8520350380c0480204102e808002026807102520b241d06103e00605490500041041000313400003054907006020f00e000b441a8501201c0c020a050140b50864004610f013a02070095401d40c8a15280c00d40c2044c944c950102d8840b00c01416080e01e90103500303081000d80c051206c601180902a1314042140d003407900c1001c0c21529512100c643d810a000107212403000d0760076108049880502d400e6481d005a10001141e00c8800c0e140c600c4214400291907401c103503039903158800c10504481c9052150703644101c15407907100c00c8600030700140c03143c0001800120300d0f80c03244002001c003402c02400c006040c072003100454000e802c001c3e80950343c101000754542e0f120307192007140d0255101600700c6034030b41180034a0000090140030007007042201482c582005400401c203249810041c10035043c24022500600300a554143c14040e01030580011041d5005008 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 990783732 1250 990782482 990782489
    0x9060c1f14130803061f03090b060406060912060b0603091005060d0b1303030e10150f06051b03070609060c021e070905040807140d020f01060f2c010603090b010906 72
    0x2901c0001d2000c3d941c43e0400d078002055540c1c01401c810001c81c102c50449000780f1202102c3c6ca0020315a00c15007001e000c588402070500e40704034102041440020f40c01200c5e04202c400d440608070301d580c01450a80302070541c0280d4150042400b200f0070201d001d00042000e26021500c03410002500c0d25030a00c81380c00071304400039007200380410100b1074000065000c111118024980040c0c5101e580150134180048000d2400704140c494108510780180c1c181d07a00d0081018407000c125842c50040090a2030044181c5ca0701c4080d18402003503c0d0400070710443d26000e500100400c6440ca041c90024000c0003850700540040c410f14110201e0980c042800140d442b20a2004101d61441c05810038007806000340103d40b412001e02c01e850000c0c0340510050592920240a0809025040402071501200140880152f810324008128001039410100103031500850303e605519001e600100040b00050034464618405600002d0b1040c3e00d0707440701410a124076103030710300359a90300080800d07640d0901 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 990784982 1250 990783732 990783751
    0xf060c082a1e0c0604150210020406050408070f030320070b04090207030e09070e10272103050706092306090f030414190801020c0714031c0509060c1f14 67
    0x3105000b65106d07600700e1414600c242c4115100c0034602c92801d402e03a0007543c0300c500414004202806020310038031145000d07001114084d100d2071300e182c60081c8050880d003440c1401c81e00c030070344040c5440014840500074200e000c1484da512980c5a60a000a60004609a0006001c00d1803040540382c442885130054146a8034285841202c10810840e05851290102400700c4a40ca000b40012010280300026507400144454145070a0910030100b8580c3c3c0e0b24480235030034043d54000280c11000380c51000340c100e903000a0561080c82c154407500c50742c01c0140201481c01184420002d000146184100710034815100c1011070800cbd181d940e0700490103495408014501d0302c80d441d00308001110001c0703101039021810543d50300c1c1c0160032684101d1080c600c582200d6414000105509420005e800d4250002c1926101c2c02c08000b05001d0143c00360030400c1070000b8410041d07030ba64801e60b6500540700081e2029100403800742086441a002d001d5070240c00d042c5007121900418000750311403120361 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 990786232 1250 990784982 990784987
    0x3030f0e0c12010b041b090f030c09050a180c1e030b0103110619050d050f010e0604050720010506090c0328150b0909010f060c082a1e0c06 61
    0x40c0c20480d20307010803040c02c80559130710b0610150700d0307445018070074060541000e10010300501c5e0900618100d050b400086190000c0d0804000140000d0704500c101d640020000400392540d00c42da1001e0168401074502403507900d45c160302404030000c0568100c5100b42c40302804800340d0a10544c1160b20741c4005882c4034828801000440d103000d0308460317903d034010304141c60050040441ea0180d039403411904001800462400103517450752080702e4110360020310710700c040e44c5400500c03d441203004008500641e00d0341c001c28071b842e000b000d103290401545c61542110301100d1101500030300e0100e0304c031340c440c5e0f40d2075000c031701c0905444040700e00070410003c000948543c400016083d0042c80008403603079035542c4104034268045e004400029000c00c1a100c3d40d03500040d82000b01941c4180c0dc41c8030a104183c41c10040180c00c010760440340fa6000703031500d444010070614943e0014001104903c1d801440d0b14004600402003141303c4102c00c03194044a52182030540b05541d4906c1024007034104004 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 990787482 1250 990786232 990786253
    0x3071203031a03030418110f042d120c120c05010c080906121f0501022a040905060601080c07030f3614010309081602131803030f0e 58
    0x641c02c1403800d02980d801001d214840702c2d000c2840c0d036015600885040c2c1103544040030000c19401100101c850400121782400711010701c0103924451445802001561203150070451001d02c1111804c0042201e5001481d83d40c42c158100c0741026a44120740440140e2808981109045240c129081e0422080f01060341442c0064688002151041e600b07503c007070200c07001c59511b0708003d1400341c00e41844100341382015054902d010143e00d20500c001c520200c020f00180c4d07400140005504a80c80d8049007092080008501d552010343c407050300305051001000510400081d20f034000c00c2c0a80c2d4078032082d618244216102d0154120080004a050052285813403140d10341c03099a5400c1c402c02031802c810390b44648544d19100d40441d00d55071100001300001505c165402d54202001e080a01180c0155642c0d1030140c4500211484a00300c150300c02819901c40050301c050050048400700714070842034a2809850307881c0c80301103000a0134040c08210442d014040e18078520b1070138009003c81e205 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 990788732 1250 990787482 990787487
    0xe0a0b030a03110c191e0b0f0910050910030c0c140303101710110d05090a0309150801121b080127030c0209060112090b061809060c090d080403080c060603071203 71
    0x1b43c115801860b061110210f01004080003c06a01200389107441e40c80c40b400040c020300300040e00c0a2820b02005210745041903d40650740700180c0f49030304d40000c940742a2003060350b001604030005030141d640704100c0040c0c4d10b0000001c50240955524a40d016941d03000640b00000542001c25210341050021400303135040c41c0c0191301c1c024840c1d0350340d5042c1041ca0660004840c82200c420f5455400344803d030050581004075900036003c10041030b0700c1c084c40707840003808440041c4038110003080a1038841040c81408945201d502c51090340860080c2da03a41d402038060005810121925031540303164109503000420b8114005515403280f2000503195020099030307030401801541070060841200044804910800700d8003031040b540c0a0383c500380307202407081c46042e503140403882004100a210410f940010602e902410140c030340d1340e8480580c07001c204c0449040c2401403480b0070200b00402000314060140c40381c0c0b4050030441f08140d441c60101541c5900d43d106d420384480305100031070003180c07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 990789982 1250 990788732 990788759
    0x60d17030c120a0b0906060f04030b1302041104080610030b190f020d020406020c030a0f0f08040f0f14040605241b1c1403010e0a0b030a03110c19 64
    0x421800c5510b0a00000d00101100002c0031600d0080d03066443c05100e01c1c130300d04006825000710081d0350681c109a03005c441c1a03000d104900000d032a04502c1303c0000c08040703d000541d00d03074581c050402e024410040418020755005400707194050f001d5500001d80904c401c185002c1100d801c8042d2074a60780b910450b00584c001c00e06200100c2c01e44481e0b0108405149000034407aa803400f0500698561804800a050102014415109800400c03400340480c0f04440740c41d01d0550014800900c0141c51318041d4000d00c101e900450004a80307039400580a2030455406044882c2400e4596442d1880400c1000301d521500405a000a80301003110035240401c01c110b403400d046405561801e20415201c8500c1001e0900000c01c6520004031050300c040304c0110041c8015007420881d51030301d0041c1540a142c001400744024005546000036410b44075500b1280000758082c007910a800c40e03d003401026110681c1c104400d03882202465159801e010382440b03000c1280810010f0710a00b00300da00a80e00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 990791232 1250 990789982 990789991
    0x60503160509120f030d06141014120a060302010905040e1b030102211803040b07030c03120c0c02090121080c0c09070e0f09010303120c2015060d1703 66
    0x60805103450303001c80001c0007813041e04201000256210b40c10140010240c0315242c100c0303070b601d280440b039119841d03d405944500160003401d0910118200c10000d00c090300030110214202d141220502406414992240040d13034001e903200406203031510107200075601d80130034142c004d5020950b1001c481c2c552180043e200c9000400151400b0303040d80c1c8040f072995141407001034031000482442550340842c2d201e0101c90840b0000345060610307000030f0040384c1c020b8501c0a070500440c46a40e00c10940308159090f100b01400f402000b4020300d62500401e1518010022401103400e840003044580c0b601c0840b0400700702d1210b50b404061803566034000365030031203c050301c51b81c421000c1c0340b0b5607940c466113001d1103a002c643c4c46841041e03a1004221103603244c1c1d00154000c540003c01400807035440413003041038404071840420701c0099030500300c0340c40610016426100743e111104140c50380011444108400c0c0074268484c241d1100c408202d006007a0782c4000700b86190f840c4048480d0034040c1d0166520 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 990792482 1250 990791232 990791239
    0x60a3006150e191203081501111203040813060507020310150b0d090501290f010c1103150a0f0501151b140102031303021c0e0f060c01020a08010f060503160509 70
    0x12a54a43c290010000d0000085000c58010b004029a00240840b047e107002000d280404a10364524040d80d1541c016000741d52070728800100042c1400340080440704440d0300343c808405965503854004085030081082284030f4042c007030107003c840c2e40500030152458404160f01000d1751500a58400950005002c0c1c403901d9226141e480c0440c00a00c11166991140340c1c2d02410740b6034040303110b400d5441d2101d445102c0d5410034090121039900ca0040c1e40035030b40c02114402220004070001c4d00d0040c03c02c81d04041c00300701c0000c000e0703060b819800c07001c0750307140e0071030144204c0c0d80f20404a143c0b518041002000100140201300007804001c010f0748895004401c3d08003441d80350b440090982c1c0c01103920400154810111800701941080b581c40d5000c0c0007221040e4031250604001d1812003070500140c440d16083c50909190782d00e042c2111640e440040c02156640f405074006440507009104000303000082a01c005010f500400c00c991188001f4000789001010084051303e20343c04c1038800981 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 990793732 1250 990792482 990792529
    0x15181303120609090b01060908190302160b09040e060103050a032604032d0903020f011403130209070801030b0606070c050306130b010b040302030705060a3006150e 72
    0x1030841c0e4468103014003110000803c400c0180d0070245c0b0080010392200041001c1c41c02c041241c40c0002c12200d603150403070110110780710b41504003245880b4042c1e83d00413016499550014110180200038807041600b5a8240140c040e00d802c0581c443c4001d22010b45030350405801c80000900c100c940c03103081c034015540c07444c08040d0300142c4c2c1c8480c901210102c0c00b10b0b9511240c0b0800795072004200c4500030b4408031300303c00358110303c40080003180d0a2100a00170001c0d00a0407081307a00680900e040b2070b40c4c41d922503440c0d1900c502071602101072a01c2c02d90180c00402d0101c0c1c0b1840c46826943c3c162074012440303034500c0c3c88602c20302034107511514094401d900410b001180329541072000601503200c03031010301c1c414146030809a045100692102030a01000c200c1040103840102e400c10449008444e801c5d11941c42c1e00b000d131007081580341ca545d4414039001074500140b07040740080d880c000b008441040300c079843e42c0100c84405404c440c3c01010070030114940c1c080e450034410744026000310009428 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 990794982 1250 990793732 990793757
    0x501020c0d1707050a0b13120e061b100c020102040524120a0c1715010c14070303120c0926010f0c0201061703040e071d06070b15181303 60
    0x91030f80c010301c1e4215565085041c1c0d0205109581903001c2d045004030345610040b140343d0b0b403100e044141100c0c082091065143d1030400d2659400300399607400d88121000e8603841d651204203600d03000082e0509684a240030a88014a48144203840548602500511070000e00c04021004d4035018084a014191f04106103007201281c40300e03807030141c180d40402240c103001c445800741040c3c07140200740711154188410018a40e08140304035070410400c4c28811001d140d05e080c00241c070054036458919910850000004250303120304140d46d824030301c20082001882c04030080311009240d1154852030301c0c040d4002000308209492070488280c44100001d081c40e0350102007401d0752024052000940d555120400c0159124170014001c400c0c0100a1440d04d130420001d903442d600080c00e000700308104503202c03400c102d10a5101300585807004203a9511024141743c510380c400c0b022580c1c140d02c030601c0c50f000c032060300300384407030030014080c111a201a5580f00344104444144815050341000302c01c01008 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 990796232 1250 990794982 990795023
    0xf0901060324050f0f0c0c010b03070b1b0d0e0f0f041505042307030c170c031801021e0d150305070504140c0328051602160501020c0d 59
    0x1ca1600c1480b4502c06a50300000041400c6032001440030708000700350000c01c0300580c0020b003204d50010840c04455101c1d49111078190042c0141e40b031182e01482020804030f284120302d030103052020305034110307640006460a19180c88040c2540014041203100c11720044904c0c000c2881210300501910740003249000740c002509545d850740c40a0081c507070141d01400181860702504203101e12034800081c28003040d400c20520b03008010140002c040d51845405545403041d015090801c0e411510b100403030403e1844c07030200d9481951801c100351b041d0b180708031400344103009595a00d070300d580703060500304006201c0400c030740d01510300482d00668601280303101c60380d02084c0b03002660284000381411801e0100740801c03184411041c3c40b43d00480340030041d4100d0303a0401c80e584000140e050324440a4031980b8145204800320700601d1080c201400c008200d41c02c02601483c3c602282d0803201e5030b00b0154046900000540525801608000c400760b0841c00e198602010f01c0340326110081d4054890b8800 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 990797482 1250 990796232 990796253
    0xd020d0c060221060a05031603080c010b150c10060b07062a170a0207020603040f060912050a09170a0605180d0206070e01170f151e03070b0309060f09010603 69
    0xf50856180ca0400d00c200d03401d01e44441d901800c0c0039002401d03620b0301803498040000152200404002d00055400034841c0203410081440d44050802c26a001040e038407a6002c0c1c112071b211242078460020f10700c0d050100380c000e003411035605100191405038561107101c054071440340d0040710b00300481c1791803000288180380d20081d035140b6580c2c0300c201020042450300382e04004d08074600c41d0380140a1940583e0310b80c0d0449421a5003c903e103200031101d45410400350446000c09040c01d074010206a0302039400100030002150542e0702e42c05500d40707810b0030034849480511415415400010010000790070f503400681c000b040300d84038561041c40e1007800c600e4648c2e00164580140c00800a00c180d85400c42c15455000d40d09003442100444540c0846070340c0d11004003500c00c1c000c020702c08542c0d900c0c0441d4556240ba1000340c1381c11101d81d404042c00c07104458202c40c4901a04c200a0005146045601628050218200508002d2f1140500001c070210080c02407071480d50303103110010005100c0c01c03d = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 990798732 1250 990797482 990797527
    0x60806010605430f06020d021207030e0d030b03010605030d020a1a071707201b01020c061e040e04030e0a080307120302030c0d0218030c030d020d0c0602 67
    0x11003954a944020f241e18024001c1501d0085a89200d00303081c581e00403c2c81c80d80101c03000c83c10b01580d4403003903003000e225260880700003030301c2240b0000c0d0804841c4840d40050500104c0080884282e80300c014040301143d403034a00e0605a60030895540c6010b40c400d4204e103d034410020004a0642e48803070000c0d041c0340080901381d01581c03120303d00c0d05c1048031044038450f103036105030b9008140c0d141198010b007214181c2c1d620034503011101000565520300520390f0300354039801100142d00310042d0702034031503407802440c40c801500d0b2039600518600f0361001038804080354010b82228141034840d8518010b105241c04040c00c640d505004c00b0440c081064219481035000750780d20140d1015520a010004a1a0b049480e1a800800c44500071440b40f415104a0541c1031400503540e1f80d94410002c3c45020f0031448810b01e41c00010444119200e01c1512100080c040b002e441d0725100074020141e4550840d00300cbc0c00560270449401c0310350707405000d20741790080c042c3e440035151800e200300010140103001c6 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 990799982 1250 990798732 990798737
    0xe0906030a17031f2103050c100c02060a0b06180a081009060b090103200a0b040e19050609010b030403140325050406022802030a0c06110a08090f040608060106 70
    0x4200b11280a1300c20050420700424001d0701c404605000b0305000d108866031859822103024071072402054811402c49040012020070b0360020501c07031660402070321810021500502c42d10f00801c0c4c01400754880e003100a0f4004119924042410742044141c185c0e034104117500c040701220000700b000c0c0900000c003a00942d000e0004030b40b20781c0c0c60704c2c1c0112049a0500c0d80150100f00041c0005145010000350100d1601c4010788101440710004070100080c0d00151200600814000b4510340c1c40c80f00036014880c200b84c1d00880c240010f041800319038080320b1040e480f54684004000c2d07949000c00858220f0b0217841d0414a0178096408804594000d440702110181c0441d007179800e4100400ba40240c540c5149042c0d440c03e031a080000355590201501001c0c101d05420040c058421003100518040754041d06a03004001c0390b0800000110240c0301c1c0d84040b40e0802c070000110040801c2c070b8041c8591080714203060800107170900014607044c6080b2a00720341c1c0da00002c2078500d01046000c1c020640b6a = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 990801232 1250 990799982 990799987
    0x307020a1719081006081302120c03030a021b060906041203020a061e050603060c040501110313060f11070609032012060703110702030706050a050d110301060f0804030e0906030a17 79
    0x32201810344e51a8410010410080d0600000600f015140c10207990101e5414003217890449186007010004866203a15100000e00a080c003500801e03041940c2540000320030321009082c0a1040510400b250103600c810f00708014064a8003021440c900b0300d019104039110708109036943e0b8110f40c42e07682e00394030703010b540e251080302c2200c1c03400b5503035100c14154042e290300d041821840c00140501e01509051110400c1445120745041041e25900328206e01c05100c15aa100000740c049000c403080c120000b060b20703100d400070110005c0c018040f1841c0c2d0b500c00e02402d1a40e155000701c0084212042c0c4d640318000b20801c030303541d00c00e4041d0280648a03070261034513040900000d400c45d50400e00240360400e0500c400c0c0051b03940454204215905420700c2d41d0b070f5492404044a10b4450340003030217205031406c001c00e20401038420186050303031600c4c2c0750101c000d0f2005a0a44200c0803c8030b005002404500b8103203032504210240907008000a0202c4444001650312440c8050b0003990394601004007 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 990802482 1250 990801232 990801241
    0x12140c010221060316031502070204020d0606020c060435030c0c0f0a0b031308070203071706070302030c03150604051c06050105040e10050c0d0908090301060b0307020a171908 77
    0x2080b074480d0004000c80c001c01c40710000e4590110403100512014012021038803011581080c150111613501c0d500500465660000081c000001d02c058028840140300d0030b01000074505214044906452300070403a07810310440c1440000c0018500c040b04c03017071a0403401d04c2c181c140c80700300043d201c0200420301600041d400c000901030041c0244020512400d0101e0081040d400380c842242e8021400340c4054091340814206601c691181c2c1c90025018410044001146000c85074291441e0176a213081da0103d03150a1422004d0f404142e500c1508018104041420b600c0400b5407442c1d40600070300802d08042d5a540003850b03015801d4400080ca4100512113000c010461081c0c5001d890100c4042100178110101c0d1561944128281c40705269668089003003002c9600030707101d041c640076000b401350110a00c0c0400080d044501d00c18001d40c2002d801080c00e142140a99206030490b90041c0311035069500d86800e64003904400340340141041155415440c801c180034652544907490b50141e5003031 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 990803732 1250 990802482 990802537
    0x15130302060a06260a0215310512070503120d051303021507090b0f0703030f0528110c03030702070f06080c0319050f06031912140c0102 60
    0xb8011803000e450700030180f2002c00010030680310710102e158849443c02c0000f20f160720300458000d01960004c1180800960300c1524001440c0c0e4200380602004070000d100d48040781951040700355005585404d80901c0f540c10055903d0404095a0044911086d070701e0020030f00700a89200e5030000b0782e00c000345003c1115440c1c000c2c03507044140800b0001d01c0040c5510020740380d000e4070303a058040358082c90203c0c440750320912142c8058441030750020b40d1000140070b6009568488101100440e04124001c24820b01d14821188901003011200840342c01c4207079060461080282d07545c100b00c2e51100801c1610705203d0190540a051070000c0d9500d05150301d000e031508882d54007070070440c0b00380c000602625a010003000d41008101540e01d850b0b445403c0c420900d070403000b08030524640341c8010410a81598295140998820f0301500c1c648017000d040c460303402902d4000a0400d003d0017441d201114400c040031131212000688490900d0b04c11070400782079900080e58581c1e1560001e0314000f2085 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 990804982 1250 990803732 990803743
    0x30506030f07030819090b0a050403030e19090c1b0507050a080d0e0d060e030a0804110a0e1308040312020304031209051e1306030308090c0d02130c0215130302 70
    0x3035070310009140c024556503c19106200301d0000f10994885400080e880c10f004541d490058000c40300d555441e1100c03110000c0041e0410b02c41580060300d10204003150341850640954621568442c941c010b80c103005200020382034903025001045040f00c5040103d038541409214918441c04c0034103040c0e86003004102100314550802d8030b0701d070440307122003c580c1c0d0041c0101001c00000c1c1c81c40003216216050038401000c1c1490310344400c2c00001002c0c1c0e41940d124102e035200e9031088c2c18401c9a07030710342d07418070400c40c0307150207450704c550f000c1c401282e0001030003c5038091885c814080b040c5019143c0d643c00101e8036021004201580c03011605004108001d0a680308424003450a402080d180070001045d6031002c0d00c441c0d682c0c0150b80f603055060348074010200c0300010328501c14017a0300e543e0b00d8000c01200702111540c0c0b1038041c10518402601e0181e4001107501c0e001031101c8648171201d154480105601400242907208800303002c04544c2142c6d808511030f6022407403991030110305040207030810 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 990806232 1250 990804982 990805003
    0x2a0a030f0c081c080403050d0603150f0c320408060403021014062e0914090112031215060e130507142a010b1008060d0b060303091003050603 62
    0x35004000600240c42c243d10603504240000d1030241207030f49507070500341d601e03101d031000c2c000034581001d001005002c1005241c03030a941500a0400080d8408882503046810b41202c1100081c1a1004100800426807c0c4241070040080342e803441c007031606034420664440c0c2d00c1508180c01c042c04000c14141c052100b410451071003681805607080b52000c00844c2c0c0001440117108003081c0b101c00e80001e06080d001c02c1c1907191380709204188000c0482c041c0070b001c860700c11003640b030703c0e41c0c80c1e0603079182004458103040360303102484100c10b40c84a507800d03102000740d4002c1c000c00070f40d43e05424108603848070704640140b07407545030300394141c0034401401300042c11f80384014513050510040c8882143e015054817200d02d090035050b5100e030303004c2140d018210000300e040404413484450b5229543e4046d406090f10050444001689980200d0f0540390b03880d0845682b50300218001c0c1c0390010810000034244d020034000c003030703a01e0448640001b400d250019180c44000940d500104030380c81c01e0400940c001c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 990807482 1250 990806232 990806249
    0x6061e050306040212030d050703270507120326042009040312021605060105010f090b04060f030f0906050a0605011d0f0a0e07030c0e060703022a0a030f0c 68
    0x60034800401d59806019100034025804e0b2680381c0c09881040c010b4441c084904503050295082c000d00050180102000c4070a20100d44080a1a4220a81c00420031303039510601900a040c600320341c4c0e42803040c2c0341c1410340030f0007005400221034071030f03803040010100c244c1188240641428246000184506a0350700c014030440680c40a00341d8500700f1050f40542c1c54540240030b80d54019500c0007a00416001c025a07590625580c0104000810303120305845003a43c4031440c0c07602c03036141224844510300c50f0341140c1c042000203000e0140310310845020f401d060f040100303950507400e1044c400c43c6e006410540d04039550310f0a001440318907000780c100800007481c1000d80c0309481c440c1000311407982d0107401e12406c084810680c00c2e44860249034001e092030769150480e4a400d58001c2d001c0c02465400100003551203c040340580362032070555106035056802007240f00700311410f0640c0c11340c03041e2109403981e50320b140c82c1c0050340d185030000b005180f141c0001300d03c9440600d040000c070185038121250 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 990808732 1250 990807482 990807539
    0x30307020f21160c0b0417010c0f0c0b1017061b030106020d11010e01020c150f0c040b0a02011506020705033003131b032003060c090303160606 63
    0x40250148203642d021140003050078012143c038505070b120f20501d41c0c00610415030110b800204948420601018404140001e100c0d01a840908440034810038500402080804030480e0200780b99104099014014082180c070094845804542581d141c0001060a0f4420030030000c2081802800d044801c1daa540c559055504003100651240544034055041243c1c207060301200c90025002400100d445500841d51f074246041c440f611103011810f1031010f9a0300710089100b81c0e01a11020384241d0406a2481c01e081c2021110402c0343e210b94003910840d900c506070250b0000d00c00035010001e1045800a10a4a10301001e142c01c0c14010f0f52003048480201c010094803031408900e58110b44040074a503030b500d44c1d0302c241581c885003604101800f41ca02ca600c000d000001956042c40035240900b80514968441d4207546101d103c00d0356541c6c0d0143c210402280d5044152005081400e4004003605d040004014507103000c1181c000054420b90f480c0c1c0b10401018a102c10115031100c1038406444 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 990809982 1250 990808732 990808783
    0x1a07020c0d0602120f0106090b1602120c030726120901212d020a020d0e0a0b030c1803061b0307091e030b0612060406090c030203030307020f 62
    0x252185010000e0a000303124094140e03081024540c110303408481100c060030418204260314008114090080c1000b0401380b0038003207440920780d4281c0d4042a11401900010380d0303280d082c4561000e13000c1b103107521881201c51450782c582c0c0c144020006002200000c0350803542403020310301950010503040d80309400c00c41c2c5540100010b06d04036034461100303080c01c0008400d046041d0b0b0009200303c05a048180c034010480195156511000500840d407038024451030507000b0005d8102e224140c18040943e014440c07503902903002d08007109200100400e100803083d5142c031921100d502c1202d007003800c0b240c0090043d489074402c80c8000340c00320040e00286081c1c542941c0c5140202500310f141103200c00040b0015900e40c4c8a6403046000d0520070301c60b2600e072180004418030300896404102d98031581e02002403a40c0c10b148580d803d044d00711500074140d544980e1101c10040c8003144081c4c0d00700d41c50110100250302c041008602410055000701007511030010b220703044c000e0a44441140b200300f00701c0754 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 990811232 1250 990809982 990809987
    0x609030d0f2a2a0906030203011a060d0b04020c07080f0f120d0f0f0f0212060118030f02030a0807050609160302090f0a09062306180f1b12041a07 64
    0x3814040d034058108401105501c3c1e4164401c1c1c200074151110020400c0301007046209604008100c91080d0001d022550020030840005862452143e070000003d00541c801c2101d0b0303810038111000003a100504e001901a0002c2c00e04080741c1140c0415031010a0300b280d210810040180d042071043c01410859900e00c11158640c03107800d12665000f5208d00c0603108801e91a8030014080784210400c04ca005900c4500c880070b50030119000200f40429800a26594001e48070190748001421281c0e24072030455039200c20102800005030f0301032003401070380f01c0080c5c03100c2e005100c03850081c00101003610704509550b26101d94036200c1890000356038000c00050300c440315001d4009100a00c084c0c481d90b52020110001d01548030081c14050405180c640500b220a580e01e2080c000028125140d03640e01701400b1a1000e09440000b000406400281000641c0c1001542211301d0890400504e600e00c8601111a0010340c0003420080181003480b08003c1c7c0c000c5046800360722085030581c1c030300d00311901 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 990812482 1250 990811232 990811307
    0x130926030705071a0403121d0c010c0f0f030503040506090714130e0d0908010b030f07060c080f2b0b130b01120e060604060503070f060e0609030d0f 65
    0x1c1c4000d015010039100f00304800560507580004003a00c541e0b16034039007820000d018111084041c212a468007407400c19038001c0444100740c50345154028248840f0210044402000384071040e0340300190703480030000040c59144100b850f0350090b50740700c0c3c480c105810310b10709104000d0042406940035001c1000389a29200c144402d01a0481311050004100d07140d81020f00300340002c00c00300e40143c010641e400b036040700142080c0c5803c81c00802005007241c003412f9480c8400540b910340c551120b02c0030800305100704506103450b03104104541c1008440140c2070801e8029400c868040600040700140c04059402d81d82d800b1a8602c40a118190420000c140e41d050071803e00c641081d01d9031b42c0341441da4050010402003042c2c2290070415030b40001010740d19440f050710303030600c11420000c00040620780060340030300303032680d1520200010b450f140c01074030751f41e01980145800c040d044c81540000d641c1030001280700c56007030301c071081c2641803a40c00511078031882c00391b6991a06011500d54041e2110390300d = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 990813732 1250 990812482 990812491
    0xf0a150305061f080d021e0c2d1509010210141303020f16051c050d050a0c0206040e0f0c040f0603110702090907080d0207211113092603 60
    0x500910128244600444052858000301c20510800052000302e42d0300156003070b6010680940042c200d07400c0f0020980b510b0b121100c15a00101c64552268030082040c48240d6100586950710820a840d27030208003200c000d1800124990f10200f03e981d10740d41c040c4580c411100249800b0011243c601c01160451360000d030002d0140403101c501070041600820802040d2070b0708008840680f182e2420000301c40156000301030107110b40d4140079880308109640e20a08a41c032101400f02c1445001040b10302c0e80101d10200c080040000c00c4d90090b84880000b000648103050617900c0d141791500502c8100d11004e06071340e1103150100300803c0380601303916800f0180ca00c40e280c04580348018007401041c9028102010358808061404e00590000000e60001100c2403c4140e404041c4006416a121a5180f24480b13281c02c14902182418085510a1044600c50700085040000000104410001607289484465641d40705041404030814a00100d143d071140044241d4062540c0c20415000c041c1 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 990814982 1250 990813732 990813751
    0x501050a020a301505150408060708040c0f03030305090d020a030e100302120c071208040809091305070803040f0b070203071a070f030203030a110702010206041e0503030f0a15030506 80
    0x2248580803141c0460b9410f81c14000302c07410300424085250b110100032081c42041d12030080d00039580403540405064404442c0741e400507040c242c0d107401050703030b4001004201b1180012080c50101340d401c1c0b03955112002d076001c0e6500044910b41201501d10302481c8a070b001c0300b90b48c44040c502c0c002961181181c1010340c010f403051800040410742c01e13400b038002c18116540301441d031020090211940c201803c40d10f4084c06504c0542c198542099070340090540f0b01a1802c01d042120300b0080c2480080c16403c410300003c1c0080030310054a845007003503100e410940c1e00781c000240800c1805400c5d0403000103048981d45552800e00780d07a0000fa03603401c0074400c0c001d0325184c100001d40e40c1c800c1c5100b80c400003900034a100c011075410386002516544103c4194090074907060300d1115445007001030300d920560680003400651034540700c1d04a014140e00b0100a139004041510000031010300185002d02070301c440074006820158650070941d644140744c50081300741d03d00201701040300000e04641140342c42c0c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 990816232 1250 990814982 990815027
    0x7030c02030c0303010305030702010207050a06050f1317010c1d180603030f1803060a02030103021309050c06072303070b010b0a02011808030703060e07090e0a20070501050a020a 78
    0x1981a811400b610036072452900002c0000418403002100401946100340c1c00d42e4a02ca4440040000c0d441d0280a14800584107108506062081c0e0f4020481c2c50107499401e24456a220a041154418a110340803d41d450f8500c1c00600c90300880314988111000d030300003c00c40c1076040401e980c5044c06034000c00600c9240007243c0d494030309204403106040e0150b074441d502d801304480d402002d0001c001e0716010b03220f1a4000390300840144281d0b410703207500030400c12003001406000400340c030002e00c06942501690b80c11602a580320030090410070300c2205020f412880f41c0c0307205203800418650100352904100208400100741071001419208002d4610b5107850803144124010007000c201504004902d070340d0306042c094044091445101d480d0790600480d0385030003618440c0c00c01914200b01044d0060414040c01c09001c0e41e0301d50085400c0350001d00403140c805104601000d00d03a5134124001e0004400b41480300c203000c0c2c0c235880b050800c000d52400c040b020009240754a60042c00c44140100f = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 990817482 1250 990816232 990816251
    0x30a0f020a0509040308040c06020a0f11040605060d0b030106090b01020d08070e060310051201091707020f1305010e0708060a120303230702010609060f121e080a09060c0b0703 77
    0x25a901e603000303058040d240200c0ca280c0740c81d0190105a042d1401d450b1000001d000081c0c0601c00103103104000c0d848103515240158a6523036030174842c10344007000d5010b038480001040c1a00d034400a010700e00c41c008000728a0304e5221050500f12142c0d80c000d020351030b0074150880b80503600000d416494020503e040d400590702d0340703030440d101454038035183c1d4460f07000810300a00020100d00c10050300c0e8125100308040940303080c0e550803100b2400c0014001c1015024001200c40140081c1c0b402d140003a01604030340c0046c4001425696400c030980050907601c1c00140b210b010740c2d01600b50711880310b04000d506410302200080902c0310a101d21180007104101c4541094481e0300905039046280190010a400c1045580000c0c601216004015880c20200080c0220340b405401c0c100c42142006c02c030994200208041c070007407816403e0f40c0e0410f60202d964980410385540e0003941c1e0242c005d890300c440005900518030400e69000204200250f21410081856044050f811100310f08002811101 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 990818732 1250 990817482 990817489
    0xa12230601051608180d2001020f1203090d050f030408071110030911030a11040507031401062606031c021905030409050a0501121e0611120106020c030a0f02 69
    0xe40c0725075042d0544104848020000504090006407141c9500350041c0d42c102001c0c0441401d021b680641100310400c000e00d80960030a4401400c00c0d030600c151032541130340d0400c9514190908900341c0000c1070010030041341d10414040c413070984010f46801450b107220065461032038000684003a29100c00040c2007020031104e408000f141e1200a409584200d02c0340101078001d08a005050f0752480e0311500300318540c41d021134601c02095001101e0460840b400c1c09000c0103110082018041c10359031200305044558100c1c80c24002c2684d6a220783c00700501c0317184c0786900407050194160040c1114144013065401140b0458504002441090720b412030075800c03032528080310062000302c0c0d1242004018008080020b00603110414006d0040d17444040049044503405d1040300482c443e03441c6408000382c0c034250b0403d003040c002c100c52000c100060702c1e440101c0340e894480303011104c80010915400704e40c0e00790300d6004080741d00240c22240702c0200401c0d29416500b2000b0214803100078448119034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 990819982 1250 990818732 990818737
    0x160206060a03110a0512060703050a0e25090501032609010504060c210c11060309070515040e07030f0e0c0f061e04030515010806041a0405010b090c0a1223060105 71
    0x200034401400c010759482095140e103c10340305000028282000180d140310103006008411600d24000c00c0d286034371044680301c40c0c0d82c0c90700d4500010702d442d900084652503406150301950081c2c101c030050702e40d4041806411014205190f81150083c40361224982e0804140c800701c0da03880c2850046a203c1e4540b8070790107922400ca6103040394410040101036640948088050791042c5240811544176a0810459002c1210046c01c103500121f0140600d05008a1400a0300001c00000381003079107030500156581c000f110160300083e40c5001d443d410100d0740c01180b04c1d4800e50006414245521004036003601d44140704140a12030009c0c004800d840c095186141034034945510a031159128602191510451002110500549000030680ca80b0120b0014006c1c3d40c07061204090030910500309085400081003590a550b9410790900746481c1c0c145203c1c1708070841c205196032144800e41c00303010003900d08502a40d0381d113041520004c2c035542c169040121030301030315040780300c0e0344000c0102c2e11032 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 990821232 1250 990819982 990819989
    0x60115110a06020d1113050609010c060509061510020c040203100504060305012a081306060816060306080d1b14370305070f0606080d08160206060a03110a 68
    0xa120311030540051002d103501074510031404c1c04007440f1025030440c00502d02e00554000b4800c0301044503080100d41b5000c0300500300e150040c1031100d030300d00c2a038940c43c6c00c40c1c40444500003103402a20412082801c601c1444005a2048a4803104645074110080d42c035201c100c2d000340a2a0300002144d1148020b250580082c07070014810b1125a441e4074203140a0440b031030a6001c81050720b1b110224400c1240350504031110641d4031044240d0f19185491000360400781d0035200346541e01d1000c16240c0040c484207050009464404080074508440101151160703880002141c0044000c1c0105590041015503406200320301e90180c02c1c0c035420440141c2024a400d50014440c039440d0f1720040c14000c0d04841507480307190406c94030129451200c038105140c450001c0028408202d440000741a20f041c4e00c2d1454060640000e03019140c080380c600d040605440000810302c1c20007006001c200342195142d00e04507501c044d0155082640c046450400e1600008103804180c0604e00640c1c2c4036002c0c030a008 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 990822482 1250 990821232 990821267
    0xd0f0e04200714100212072106030320010612020f061306020a110301050c0409090f0b07030b0a14060a0807030e0102030114100206070e0402180424060c0302060115 72
    0x100d06962411410600040e0f00700b0540b4014622044a080f41e40d1081c3e032014015030910702c0c00c0c0da4801600f01c1d511085142090741b15405004400c941e12124070031200658401d49800c28205034003035130f440081c8900c0c1c070540d900d03a04081c0c00f40220b1070480c1c0f2185000c2c0c0d041c3d8142c0605100e010004400f805101140b0a45030078903880020101d6002031040010b03030082600a0950140800349400d0714011640d146440f4010041040300345070a0b070012800c940111030071001a6416592280103600550311840040c2e29010081b0152801d2001c8100905a01c440c2c0000514032101040d020b00903d603001092040c000d002a1004c0d000380c00404160301c44400841d92036843c0c8400c4500b004565550a004201c40d06004402600002c0d08a00803522034135901440c4a0b00010013002c0e5201455003031111500a0b20100c2c907885a00400012166114100903008806020b0340c1c406000d50384140e00b00544000301c00c0c04280c007c02e4090645100503805490806059000c4d51242d1030b4001d00b824 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 990823732 1250 990822482 990822487
    0x20a0c06020307090f0e07020613232a0a06030b130504260c12160c2c070e06071103060a050906060d031d011b12020d0f0e0420 56
    0x500f40c0c0e1140a18090f502112600004151165044101c46d50102c03400c201603405200030501c052540b82000740382a1141c1000a90400650010156960b68a0070000c01e40c0c840314501e40c0d0320b02c21030841c03075100c90101e200121200300800001c03150741c0140b04100915503a80880d41c1c450321450b565001480541d035003401142482c2c5445401f05154010006503002c1e4208200d030541107410480d012840f0b0750005010301e01031503640021030352120716421030401c0ca1005400008112840b00070040c11032074032082070309180507805003550301225690003501c14000100031030a5040500404002015548651200e0103443c4c9030451060880b00d280c2c1c903203e08010851490010381007607100d255544240d400a03144d00051000c0b49600f0b120040104e02000c0c1011307242c10f82c20124403114401417402546512300484480c8000e50f03440000e8400c0c007440d1281d46c0000e6010428251440e1040c5481112805c050000500d034143e5400810310481d20307000041c680d15441ca5140c50008070401440303a = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 990824982 1250 990823732 990823741
    0x121b04020307270e070801061707030f060b0d0e030c071809020913021201060b0409091a040311010c0f0e0d0f06050c0403020108060a0b03190f060b0a170415020a0c060203 75
    0x80f6605841c891040c1044080001402c003074450882d09049a00341d07160075103258111000d03000f20340401170218003016580c80086840d00030340d0040d08020219008a1551000d00144807000e0350780d1001c0d001c040741c0c030401405c24039000c0007d5101c100d0741300c003084411586c0c92501200203884002400ba40c0721040c00280310f41109551880700c403440c401c0f16460070b400c610f11703c03803403d9841c20b204030080c0c84403c0c003003080811195044041407500c9248a8800d4007272107401c2c01c0c1d460b602944e05400180c860702040046005c244103864628106082c41c0001c103d4800b4000d000412004c0100c0c041c040c1c0c900c216042048060110708581c1d440302051245240459048116130010311090b4001429080411100d0814964a40a96140f020814074566410191901202d42e128240c010941e4450405201c055144584005060060382032640c0d0380001000810304003060020200300c020719424000010000f1184c0e2000007030038070707000d1380b07600c070300c0400391040320b881000a42944e00020420 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 990826232 1250 990824982 990825047
    0xd020c01110d0b0d0210030903032003061201060e16111b040b01050f12070c050607020718051603050a060504020c1005011e14060403080a030b121b04020307 69
    0x4003144400c0b00320400c0031410610030002010940200a500a03152003d00e0342e043c0c0c801c1c0c0203d14454041c0c1408107500911a0f0142c03001c41c0640c0070307040320290120510803a86801c01c0c0b5030303000b03090060003800701a040070042060707040007408820903000480c045600d5140030f00b5001170a20903050070b5400106540000020610881084621403880c01000080f02d602410517100b2031001210802e0516151030b800c3c0c0c140d0007020b070200381071000e9161200c0001d02c0400200707208900c298040c05002e403601a040d000400f04000e00780c0b00c14204004c02c9080d20501c0816030104603246408101511030080341001450345420040c3c105000007000103d000c1d002900c2500c59050344030404c0503a903506210482d841c1e402200a0074012890401c1241d801641c0550344140402400240307415a0f039030725401207501c81d05c031082c0032035283c80d00510705290810100050094a40152480103c03103a04180034020f140f18551207154044040344001744105a000e84910103440302c0d20159409a0300d0 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 990827338 1106 990826232 990826237
    0x302190f08030d14040f061e0e160b03010302090a0e01060b0c01140105060f0f0c0a02180f130803011202010c05010606030b03160b0f0d020c0111 64
    0x10a603a40032529000003414124015582c90140d500d0640c00c2d01c88820303200184443e101c04100200d50340005010701503030720000010300161717401c00e000e51100c1c0c2d200300c00c0d0159107071044046110000041e800000840d007094210340a5854404840e5448240002504040e0480201c1d448050781e8004000941d001c00001c600306484d41019166a049900c400000ea034442d514400031040c29802e55014003000e8030a5440c041003191404040d100e003200c41c1945240010300f0042c5c845040c407901d460540c3c01040c0c508121a10a0503401d0100156049114110b680c00420811482d0075807004080c0d52104045065038a00225800d5030698070034241c1c1842402e101410001f4001e01c9600301502081e140014034074540018145003d61440e007d90071000c210704240407031040c92040d00d51542000300360079551000340940101901a241c024145982010750210f40a0a030101 = true := by decide +kernel

theorem cover : BRFrame.Cov 990647482 990827338 := by
  have h0 := BRFrame.cov_init 990647482
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 990647482 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 990647482 ≤ n) (h2 : n < 990827338) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
