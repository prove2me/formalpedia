-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0520
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:13:47.166004+00:00
-- url     : https://prove2.me/submissions/2e043f76-54f0-4d7f-88c4-6b009496121c

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 93345324 ≤ n < 93525180 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 93346574 1250 93345324 93345341
    0xc090102031201030521161104110d0f0b03060c071101110a03080a0e01090206181503010b0307021506030c0108070e04020c01020d06050415090b1c0f020910080c09101d041505100306 80
    0x14070100c4e03944ac00c0700e00c004240e8070601c21442c65940d940a00ca05405007845080c5406108030301030007076400c0000300350003107010b03c10014102e0300c0c00609000c1c40e0b030302691500710810203130b00a4602215160801401c4d00004888000140e41410202c40d000c80040c814107c1711580203000302c0c01c2440c0b401c41c009140f000c000b40150044081d680c1c1110741231100340a14000e0980b80c425954901d0302000082c10b10002040b543e50b4072860100340903182da008a480e501c2e002c000e10300298103540c0e080b405c58100c1070b40c43c05650030510018102001c4203064005041e1030a030b080701484515500d42c10b2008941c450f070005004064508011300041282c4e410240d0103500c02001c4030f60070140b072507585007103501c0c01c441155601c1d4581e0846003141440458160f005014a48009002d444d00190b20b440328891032496115032050310004510071980704911000c1c200c580603030f030003580d000e200603541c1d00da0565043c4d60006044220305d900040d0741c054140b14807900b50030704c0390480c03840d65004058000503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 93347824 1250 93346574 93346579
    0x1009090c050306100f060206010b03011707050405070203070b0903070503031b13090204060e041b0c03020f1c02060108070f150302070506090726060c0901020312010305211611 77
    0x5080005075aa420000c081c0190903001c0725a044a10300300700b4442c0211107a1024080d500400c0040040e60030040559045408078100e4507140310080300b007541004200d03080030358024504424050020b9001000e08a400e108079140c0095846000c0581d07640c2c080e240f8024155801040000c2030242211032222110001200d02d5003043c40340740060440343c038203170082d0a226902150800145a010202246285d001e8030200404400c524081002d615288201001d0060021107801010302c200144101c103450701c5c00f80c030500d54007850040210202e00301102c006109082c000b0441902c045485011a100603c21049242c40d0029000c04400300703800d80428554280214400b03d20148103080c0300d1100c0c0405030204904028202c5a9a00510440a0000640a1040444600010495000304400c0d141c01d84a50758580102e142d0b101e01d1403408002012500008200080040c01c4d03a0407414940b140e9071001a000e031401d50764024000340b11950420b1a100cbc40c01706000c0c0b40e0150701400d01 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 93349074 1250 93347824 93347843
    0x607020a0807120b070e030d05160615170d0221040b070308070224060d06060b07030305041e0209040b19060816060302040501050f03090705040507020c030f06100909 73
    0x126803400b4205603182c0d00c0089441091604001003228110000d0340c4074010b400c20030116000200420351b0b513180041008240000043d00e01c80d558088044003524583c07048050007048589030007082102994807036203403115880030184607812170100c1d4807145001c042e801004200183d0200c55440d003401c4032101d19010307040102140340340426008240c01402a103c4c1c01041c28164002840c145d0420405068030100030010523069501441d51a04120100c80b00c3c907240441c1d0030702e03200400c0d5550101200d414001850400c05404d908103d218038040c100c0d00d6444101712018900c0000c4404009501a4090001900103040003640d203400032440c0c0c0c543c0403203800d064050411034602e0740100c51142e111080c82c40c00300240a1800000d03010518040d41014035120001c1c2880c041e03144e07005000c860100005030007a0b0100300c400000e000040042c0030908040d4800b81d00c409503190228028002d54002e00c58409000440501501c3c0708103403a8007880c58030f030002000b44610101110302049 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 93350324 1250 93349074 93349079
    0xb01030f23090c0307061101060f060f081302090403110c040f1d0d09060f02010f0203040b04110d0506060402220b0417010507050403120203070f0305040503070b12060607020a 77
    0x20078414401e14080000c00907a540914401540789400010504007595120381c4441d1442c0e100420801d00321007160070180301c1050005e49180c00341c20290010114008110360028600750301c07500d4101001182e448100306912003884140c03224a82140c0070350000d20200100e000607228a801c4803500011405840c5e03030401890000b0300380c40d0f442d40c0741603503791070b08141c0701412026554034054210a20080446800c5030001804118880c4aa9030500201e0202400b81500030340010309400000e86046540340380c03501c0c1a10041d00207440503900341401041507034983c10310355040d10515400c080141a1a40c40324100070203135210b084109c240d400e010055540e1104d01e40c12070009800700107801911241840f0b20101c0c2104040d039203041c40e81c1010240401d1a40100480741074941011610700040f02441d002c3e403461240d81002842089199881300a05034410003030400d44d8412801d4600096aa908002c9180a000300114a0b090107401140091030b1070f030010700d055132001c0c10a00d5030703c0c1e = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 93351574 1250 93350324 93350351
    0x9040b0d14010b0409050a06200a02030417010c211d07030512120402091803030f0106110703030813020f060a02010c0206060a030b0f0414030705010902040c02010b060d0b0103 77
    0x900c051000c0718005004032012204040038081c454105505940c100043c56958442c07a50303900880c180548029554851310b448820380c0d002200b55940001c0180d540d50b00580002540e9600c07a204000001c3c0c0d503e0042c460301c50307040c02090261951650b076104040040f00030301012212002c128107440c0e075a1606d111568580600c0c0d082203090400151950074514184541445086240700c00c2402e02008040150004104940d400c15016241c1100b40d58031404104078041c883c0b4400881848040100b102440c0700da0240b034180d406a55032212040407440000d980d07000340b0b010080204034204000381043d601815440d6400c1c0c002880071a41e205100085001a4000c01a010040c2d44075400043d00d03680401c1a280c0100c4183c5181c031055241d07890b6542d0070710000d401d190030010305901080078040c15650540c9285072140569540c9e4006103081402081c0c0076000700d01503800d02180e0410a0f006128140034288054143d174903048030130040800074a02e400a1505150341c1d02103054a11 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 93352824 1250 93351574 93351589
    0x30106030b0906341725030e0c06070809060301060216080703020105090609030703051603020901080c0603190603050105010b030402040b041b0f140a0201050708010902030114010509040b 82
    0x20340c090340100c000c40c00c19103011030400f03d0043c40084c090030300183c010b00340d19070076000c0340b80205808040c2c060604e121004941c25201d81d070410701886100310901450840c0160180c045080d150340c1c120310750310140320076010b84c3c03250324050603035401c40042014981804401449070a100e1015a8603092584000906a030005c0e04050f0069000518081c00490200c030100090010b0000403c420707469903000801c03a1107810007150081c00046150340762500c08000d81000f035980079041d40c00e5400010311a00d14901381c0d2000780d206181c4000006000303c400318480c25882d0380500040e00d90354074078000038040130000c106d9641640d03841c5400400300f802071040e603000e8600d480c252542c03030610f401004169011000c84c1c82c41140b400340141d24286aa99056903110081e05210b003881d40c0c119801e84040321040c07850342018000240c0b00704015410b50203284907215580b00d602d00b0f039880711701101c101c1c0000d01400340c8007400c22045c40090f40c01100982810310380180040307006a801004076111 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 93354074 1250 93352824 93352829
    0x70b03071116031113020909010b09040c030b1509011106090a020f060a0207060311040306050c0c011b02031e19030605010e0f090c0309030f030705030103020301060f23010e030106 79
    0x1418580341c003075524030600c4802042e80c05442060070042c29510b4280390090880d005030b108280d242c0c50000d00301825019030b03401742d00040044404c1e40e5034260990841d4484201d0600c1145005070220b82a802840381807050701c00904291072401c0501030100d40da6115880c0241800006080c0700c6544c003080040c24419803902c000361144852502c1441130030141e10002c2c0e449804244882c00c249070340022404100da01524010850407003020320030301d19202c1ca410240402c6c1c01c1404000090301c61000410400d000f140082240c40c0003022508400c15404c4c5659005820070046588001e04022841082c08100c0324074500c1c1c0080610030084080030382d0f510802094480b041000150703000014424100b50543c0c00c0a0000e107070340e000039802c8400500c807083c201e5010000c0340b0036003000c206442d10000340c0c284690fa0303800c002c100642180c0003444201e2080d03003826004a02041c80c1210101101c134030100d1510803000f9006083c081c1c410200899040120710010808266001d0051800 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 93355324 1250 93354074 93354077
    0x30304030f0f03020c0606091f060507020906040623060d0c0f02010f05061c06020d050709080c01050703050304030509030a0519170712120603020613060e0d05030318070b0307 77
    0x104003078400001e007095400c074006005062041c0481c030040780f00880c45541c40310040718681c104d69034441d4402c0c0000c0141c418030485660381c2d240441c2c11500300700140141d40c021030b00c00107556170b82820001a01c1082c0180b244050450f101c5242803032640c890303900320f0f03c1c0060030746007403007180104082150308040d032000005100c0400300100725020701c6542845207004d842408079150000114000d00035000500061410352401e001c244041941076881e02c1c00031180c18005814801e1004141101c2d5002e00900c500807000300d94440e602800c115607810344d02d5240c16043d5562030300d0a48081d00074020b402d41500540e040c00e400901c0c203028400c0c161a2008424003414154100560081c2035021120410041003100340040780c090003000520000b549444400808181080c1029010b1640000d40000002c1640d560458002c58848166443c80d6103008008804400b000ba40f1810340c80060b210350400c0000c244105c440000b2806446e1040c000c9940c00b0703640c1c00f101c00e41903208607070080 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 93356574 1250 93355324 93355337
    0x210706140f071710060e0105190201050702070611060c0702061309020d0f090b130c0e010801021905070209041b080a050102071e08040e1503030a02070503190b04020418020303030403 80
    0x205150403d0008221401d520305068141c60901074000888510740038400900c001c0001b5203080b80c1c4a80201c4200000780f480480d120b802148003c2e0181c074041c1d0750440540a10540841e029114100c2700002002c0d9000a0102e0f480380b0740200081d03800a032069030080010408424804060001d60307000301501480182e9401e40100e207030301110604001c1e0303201c40c0d04240f212030100e40403c020680144100703084450a403414600fa0798a40c1086d40402c460340d03d107a00004480c041940a4004684107440c00a428480c20004403014451004025130146482d4080f40100705000c9283e0101e249201c604007841c0d032210f44151034400c1d030090403540b583d00001c42030700300002c10380d64041e0018204000060145940e0303840101d80118000d0001d4940d030746000074020103c000d02d07400026405402c0d25610701d92003400079143c08060007802c2c081d03c5000100a148040e0701d481102058000b51003031007a856513403c00000d4586400041e2000c403044014030f01598091004500a910944412 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 93357824 1250 93356574 93356581
    0x150302090429060c0c0405130203060f0603100b130c020111070c1404020901120209030703020604170c010509010f030f060f0b1b01020708040603050907170f060108210706140f 77
    0x4424000d40006043e001d000f09016030200c42c480045c400706085401c032404501070b542e5a0380711906000c052806903051140340140203507076030f4040440f0300602c070a906450780d02c0c000b000c001096401c00c052040e04203102030140041c9010903030000b2074410340d510004c25000144481c807800d9801c00d1a007950181055a4100007186400d651651540310039a410340c2414214000a013110601802c0c00101a800040c556502e0340c040c441d0703c01840d40207110740e4039180c40b003060899002210400c50b6191288a2081a0380d41c040c44c161003500c00140e440002201805008030003400441c0549803902d03440b15070200d500c44a00d0030f51030162041c0700f12152500d10000e21010210b0614a84c000664410841c3e080812100411038060b00c9090030045542d80b1030304201803601c180d5a2003d0840c0c00c90f00e04a55004c18040b92940803c21410f08891640e42c031422207a0701c620b0a18101c02500030450070300440c451405014242d420b00410000801a00008000041000c2140d800104e91b44035400c1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 93359074 1250 93357824 93357881
    0xd030b0307090614010507050313090c1205010503120c1005161209030c0206090f090a05010f080c0a06031104080a0b01060f031a061b0106030b0103120c0503041503020904 75
    0x1100014070b150641400b07000d20b084440881e0410403141d150401c4030000c1c04c00c09025040085418446c0020501d0800503920322001c0c0040200c080441d0000c2c2d139424019051842500440b4107a803030090151a20000030a0040c00e103034080c5c0b50b003840e0360103180c9c0e02100050062107118803c0c181610314400f0b00d4420b0754000d003408803085003c060a464240c0c00346c04203520803842a40281c1c16151190b0307801c41d034800108012000c40e40264070111a5040080d00f2200340c0095049480780550244c00350307103440403e038596400d40c0d0700d01e410544e611010002c0d50300c81c0d0890403c5c00d0110280d186441c6d15020326604200d003081050340c2a0440d900104403c40c1d200d01c844402100c9440d0401202d80c100c2e9200d10044000d04410b4400e82000c03550380342c01d03201400382a0003859041e00802c5035075924a8050001c5809200580b03110350300400c00f2101900403803907000c010350701c00b010318074181c184481140c1c00c1910580c85000c0590900a00340a501c0b24460f00a9580342190301102d0126114003 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 93360324 1250 93359074 93359083
    0x12070501090b0412080706020f071b050a14040203070e1c030e010309030509090718030609050c0301020a05031308070602030106050c060a06080703110d080403081801031404020904060e0d030b03 85
    0x2c84204068100802c102810000b00350b001a1a40703c40c1c4190b03102100e042010203401004200c04d14108001101420003078182c10304c1c0300b44652903a44030a01b80c1d455003003155180c02445080c081c104c00350034944151605134015540b021650400c0d0801700c0c503074000300700b00400c44400120803903032500c41502490742051074014151003d19050049250075030b80100b0303e00076142018010704d00f660120360580e005604501403040590310100020343c0d64140030000c1c051018040c0c03500d020310958081d941c2418001c03180004c0c466241c0d20b1030f54035a003150140912250200791400c1105021000000c0c0303c900086000b080075680300b45c1c80d032540c02e40700303802c0207005010081c0d4180790020400048402142d6402240d800c030031096100c4601d800800c0c0e84218840c8010105880002e020080000b48006404010421301d90b00b04141400070054007200e05a0310f090b41d503403002800180041c50403080d541d034410301c10b480c040341340c00c040c183c1d8501e40401d0191200c0800d8603601c2082c440e080800 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 93361574 1250 93360324 93360329
    0xf040605060a060c020409031205101a120f09012421050d031802030a0c1e0e04080711030a0302010b0114030f0703020708041206020702040e0d14181207050109 70
    0x1200c1540440c500303075004d815505000c3d00240038588034401041810b028280f00740100712209000d000c00e10b8540d00b4009050540d000d01c0c0e00d0858001ca00c1a0045000001d0741e03240d01c04440003405a40ba00422082c21071070060102d41c417992074a010000c03045182031825103908500019a00f542e0520b041601d10720290a0706025a800d200d0703a140200d200051103c48510705414001103014440059040707162001d8406034240c800c05041000b0800c94141d03a4023150050200d94542404c00c5005414410a6214002c9100303241c0d00441d000c244050018140f043c89070030300040302000f090210b820702090b80425070160f55a03200d01c2244e56008001212805040700649107949410305181c614520701074549810035601085840811a40b002264043c100140301c130602500103107020b038007030351004204900a9040002d00d4643c41000104015100215115468110030007000d000254000f59100120b0103080005844280ca5072904c030b11400d6000400f9043e91401c0600140c000c0d005503 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 93362824 1250 93361574 93361579
    0x20415090609051012031409180f041a01150f050909090106050405010801020c03070b0601020f030d0c021246030203041e0c0e07050d060605030a0e06070c0602130e0f04060506 77
    0x8480e4140041e90150741d1f10700c021100400f84e5256101c400204180d90014074401c5020042081070210784072601500920591062400ca840080c02e081040c080b030f8002c1c410000f080c1e1f00309819000083c02019154040c1201c3c1c13038010b082c42d0040740002c162250a60f40b120700780e55111400d0085003060b000b103601610511000754948401411300382e5807441159005001480d003e404500c40d40e100740815070100c28150b040f070303407a440604416030081c4241084a409441120301401413100da02d42551500b022141f299401c90380f6259028511001c0710302d400851012703001d481070400404441418000c141aa40140c80346810b02e1b000c5a00440c1d010035404c2d00096071100303000a00d03008100c60507900c6413803280240c1d4a8050003600d2601400802c141c542d810300c28003098103948200514820041007000f80f04005090240030f071220801d541c80000240300711900404100560011b204c2c1702807904ca601c6045a40b00c24903840013a00f03968041256110b84107000c00e00400c0c3c0242500003004 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 93364074 1250 93362824 93362849
    0x6030f150c05090f0406080a0308070e01020703120305070c020a0605090307090b091803070507120302060703140106030b010c020301050103030206041a0f042901030c050102070f120204150906090510 87
    0x805601030124041d00f440c0710b10a62502c00901e640751210b030400d000900750001150300c081500d250140600008480001c0090b421044203d42d544c40060310404a0745c01040102c983c850500040300501001400c1c070702170280740301c0300c003005807582040000200040e5440c0d68031141000105400c0422a41c00803000c2400c1203d06411035030f8000e40c0c150840441c850106141e5000405142180100080900309019801002450400c1d260408880511903402e444846e034809000b0307001c507499080080c6141c09220014030641d4001c0d0302500740f801050500d04516261980040d00b5603109800441c016001030040c07008125025401d66190202d519140c115840d085030344102c0404003d00c00713428103150780e0311f0741041c80100000300d40300d400c0f02c1d540d85050768480c108402c82a51030f20507140148901840003401c9810100441d059880303025808906030119020440a401c503000c0c01113402d0381100300020005282d200e000021300d00084040f03800c0c0b9080100d40140a050790041261160 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 93365324 1250 93364074 93364091
    0x10f0803071515180c140309071710020301090204060f0504150e0607020d051b030f06010308090604150309030e0f01020a06050c0f0a02060a06090e06010b0c030d06030f15 75
    0x50361101c403103902010301c0001d480400000d900f0401d9800b6808070f555001c46251040300920380c0c2d04800205180e41c5c0301c40c04404c4510443c94018401103c1100051b0000e51081c802209809207002025820301c2c2101c141074000c4800030100d034400c0e0f201100581e070004080141ca078012140c01000c601030708115050600c0d1507450909148204808001c03c42403c00c0105956100810b940c20b540c0c0140488454a80d0383c6001780c0c0e2280500c004500c1154071242d40100c0d45400988a110b0f0103444026041903482c554030003601f07070007654520ba0f028406200c007003802c120810f4011104110ba64000c54901c401d414064030281154003010b0240d01c20301040307415641c00040c8000b40c95480080020346a0f00c0400b41d070f0103400b0b10140d00b101184005014201c1903800a1164050013007900c040080d955251446e508482480b42426010b03004100104000c14024004c1d1420500c00c005492802c10081d281c0c50071140d40c1d400c01c40301c440352400c0d40c10070301c80c01e00c940a5a518044104202200 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 93366574 1250 93365324 93365333
    0x20f0a0e07050309030412031706040510030311010b0d0302060f06041104050607031e020312100509010b13090603080304060c0e030c040c030b030a080304120801030320150c03010f080307 82
    0x40c4010001001d000c000408140006010411500141002a8060858002442c000340f041c8090461441c81500520118241d46468800c081c0258400150034600c14695030b41074441807aa1003c1d443c0c655071720404e01c2e50b04c0d01c880d1050710090b0702c0707680030b40120715040f103115035081c0000e803441d0300451601780e805125000c214121000e441007243c2060310340080d807600f241c400221307010303403203210000c840c0a506981d00003015101e00844003181e8080341d07540140c40700d00d44e0b000f03200d240d900603240d10041164030040e200138120b074460301442e00800c9868150a07030655400350720846c1c4103440002000180300852107000c4000404d4034010002c4050840042d0f034031200c07400c046203d96610308000942e0b6000341c1c040403110002805840030014681400f90190b04101c509590300041e00a2a42d5a184550981c5058036031640780c2d80200607286005440c288100c5501e418184102d0341d41344c09865000c00c2c81d0303208100078035a955496040054001440780307a0f52041c1e40304e502c00e20880001070b = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 93367824 1250 93366574 93366599
    0x60e0f01140703051f0605090f041e05270312060d0b01271107020a120c060c06111801020705030a08070f1a0106050c0c0907051804020d020a020307020f0a 68
    0x200c0646008507003911740103030740300921036101911074601045020000d0f1030b94002c8007521841200700d42e81e40c0c4d0038040c0c030180b000791000c00103000c0c50691100042414005164070442e04210705404060405402000c10381d90010b10340d01c942e00d039610201d00044010a00c0c0e4040f40d01180a503200a0550290b9072200c1c0f00580602a410318640749110150b2500e020010188011481c0e200038080090b011460000319071002000781e00a8001820100c4d10300d44800c03207030060b250b01c102e04400141c50404125050806a18201c4800f500e40701c400c01030903c40c034081c0050b049522481140211160000b901d000807070761006d80079420020303500e000b0503445c07015581074175000340c1755101030341d46440c00c95200d114914102010380541c60020510320384c044050584c070251181100d1440220000700108504129000c6c400103008101c030a00050903100b10807500b0b1000b40c8090b0038515903c425800340d0300301d420501c0041c0c1c00460700d8020b51604000d107015928080d01c0c01d20302142040d4803054203 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 93369074 1250 93367824 93367831
    0x9020319060222140102070612050c0409050108010507091401050f07020612010b03072c0d06060305011a040609020c03070b1b070606150e0a060e0d0b04060e0f0114 72
    0x4031000380300804140a4140c04031a48249003000f00003418940b02806a841e64441c090461110501c2ea007400e099400083c000d001da0309603032506003880030040308400207400d00a007481d1082208cc84000354140e8507024013400f0f480008001b05181ca8098001490180c031544403c4c40d940c00004031200d140d8000d0121800980c0b00e00306566030300460300210301c4038403032050303c1d5600c945131500000e80c0111020107503001d150f0303507030b03a5948401104140c130801720b070a5291074003d11112071211940340b500c01c110745030041c45650045000ba17540d8440c03034211000e41c10400c1d00e0a400411449561500c0c4c4100005000620b10450070105065a50303980c0e13000d0110b0080500e41c100c00420342c105580845900e44507000c41e4030a43c0c6595501e4090080c000714898807045240789154102a039001d00550003000e04064004605030385054022500390310307070320f000c9500f102040c0c405030086580428158030860061001040505800c90024070b4107000402c404c1e00c81c0d240c859101403911464030850b80 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 93370324 1250 93369074 93369103
    0x13031d0402040308030a0603050d0302121501020a05100219080103050601060309020307080601060c0c0501030b09040201050307030b150c280213060e0910061413050c070f08030a0609090203 83
    0x409144040440c000380b10302d0300058215140403040006000e025007055081d20300c210165a044160620254207a000b91380064540343c445e8800101443c1041d41460f00040c4144100d0700ca0b45803d803151030034094584c209030740c01600025040f824501c0007108018003d034602e0007d0f815859a100c0f00c1c0c07151b00c1030040780d04050702d4860240c1590303400c1140c10068000310342540c9195a40f45405014000903241c01c40740316030030180c00520303580a40300b65030503144068400c3d0110383c0c0f40d030b004544036071008003c00306255403205450f14136151030844c0005080001a850740c1c400d440b1840525121011350310a10080501c1c81032000100c461588003503161b03041c0d41c0c5c40da01aa0301513050025107003079000525021441030400c4140040042e0313000310402401010000706440d404114181c00b04040748941121140f2804c0c0d5101c1c180c0d500050780174050740303003640c2000004d540e040e11302615040103860011002c8240703c02070b480b40c072070040102850b51041042130099030100e0f468401d085c0a044 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 93371574 1250 93370324 93370367
    0x90706080c07020609060a030603031b0807020d060f1a130b01120e010605130209040c08090a030818070803030f01080703030f050310030c0810050f040809090903070507060905091303 80
    0x2c00c40d04d0348015200084001042c1c0c5860b0128540010300a212510040d00080d0000642d414180400a851a043d60b0065503080c5040321680074015004400c000803070360595181d8582c00340d01042d00c0303070102643e00019040500444101040640b80360801403c03a56450080fa8103080c1e078020405600442450102207144c9003826480340c010305a562041e908404502803034220402e0035401840d00001c211020001644408001c942c2c1c0c2204542e505029480103280c2c0010902030001c5a038840322501c0e03d410010401c040c03142c14044c403540b24039101c0d4808010703c004902d100c40201e001d0410040201411803440d00c0040c0310750072080710441072200c00000f0405101e107186011001e99004103201c000305548800c11640d5243c0d40c0d8401516929140100c1c80401800810070f010b150003031449800c0440e42020400074a0f4041c180405e10b2004110000c00110140080e000070040764580d01d120500e03090520903c1c00380203140340c11180103109500d002980100c50071098064034108034 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 93372824 1250 93371574 93371587
    0x506011707050d051305011802010210090611040608040507240807030f0618060807030b06100903051006030c06210c02010216050d140708190c0f0309030b090706080c 73
    0x20345051142c001c096141c3c030b09080c1084640c1035604400783c0e080d4418802001a60080100701840740c2120b00024016000795017104000101a00400300540c003c81002400790019280070f0481c0d8010360161021581a00c01c10046c00000e000081c020f08088030303114001e101c044142c2c90480e101c4021035052120307010100311140c1c442d030301c01c09a5950300c4c04200809500c0d90250b0759102d40c0f840d402060242452004280002e0100301002120790101040d58540c0383d10041040c0112110444801c000c2440030020109002300710302104200e07151070006000782107080c0200710a035581c201006000300d42d1451180c449032102601000905051300082710369408200300e000e8400c0c68141d0031707000c4580000c10188400414950303005261034440c83d0200641902c602c0340c0d03000b161806000c040f020701600903c6645074014845d071041314500560401019910706504902da00320607400540300140c103204004020000e2600002ca140080402625051000703040c1c000041c580503400d98045500d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 93374074 1250 93372824 93372827
    0x807030315050d0c150504060914030307080307050319020f0304060e0f031b060106080c0f0309012c0d03020f0403021e03070803030f011203090b09011110020c0c040506011707 77
    0x1071402501004002d0b06582640341004840c030002c90050807043c0e0b106075030f4043d4071030049045804075803d0b034131814841c0345070041110581e501e5010280d01800304006050010312101c0c0110710a81d8180c403916200d0038800800c5620140855481c0d0f0814410815400d0985001013a00d500c5031784814081950311125104500740781500a03c001107101c081096103010f5a1001c102c6495a8040c04598240ea601c400444007000161401c0020003010005c1031080e200440084d0707840540c3c01c0012683e8855102d110410303081e40c83c8401c1c0480d640340d640c28180d282c148900344c0081d94a01d03042d800c0c1000b51807100f0080c4210701c4001c0c461702d03d001e900031524440000b41e04201d98014282e500042e55601e640307803640d0003215080b5500d0030740b10000c43c83c614402841144140c03d503880d005a142020703091700c0254011031a00e814400e02000c00003400070100030103c03000d01d00c540e015032075031000008607217480b83d80c0345090300c9603051800b0031095986c0600c0041580341001d40d0400c1d55280c4880 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 93375324 1250 93374074 93374111
    0x1e0308031512100209040e010b06030103030c0503270108152803020301051005031e0d050f0904090302030c010c05040806070509060d06030303090b0a090c0603020a0e0a030605040b09060408070303 86
    0xb5041407805600c1400100440d2a8003416450409441c184001c400703425815088070030790a030080e4003160600050000c00e2280320710328140fa10035401c1340c1c54614071403a42c03005d00b039031401030361240c000400d2320f0720465a000d0700c1c454110015200003e404104d54000400e90f240c1c041800702c080c0c4103120542405004400030000440d000340080055080100003814500100c2c01000e0181c8650142011201c0d85138124000040860780500f2010520810441d01540040030650002c5428404d0b00f0069031140308460002c1e01c07a800840e60740a0101c042d5007950b591010300c0c014008103100401154070003082c02d0754440039501d801c40c0e4403114a00001d8060054440c40b5030f1891030041c02104040e0036900045a0178003880100c1035030f56581802c44150786086100802603410708100b000401e010381c020b0b080017601e50402018451001c8041214003500364000d80300183c4034020b200a10400150041c0c10550743c0700a03200e9480d00e80c454501d50300c6101001000c00d030340c81401d00a034212091 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 93376574 1250 93375324 93375349
    0x280206040312180b0604050c0a0206060d020406150207080f0c03030f07030315140f0607050d0f0207081f05060105090a03170409020a020307050d0201020307090608131403041e03080315 81
    0x252035010494007070030b08880c0000122a010300131031418002c21354208c014802d032000c42c400d0303500802e5150368410611141c080b4410040b038010303031250b0b8045000c13101d44412140048a541c01048651f10b8110300700d141031628079000a554200b40c00186182e10044100e9469000c0310010325500c4a843c40c0440080c5203124512055040304400072030f000241d500c02482e110030480315000b481e05080d0402031984a0001c00908990140e100010071a01409070f44012120074015103005690b191348032406c0021001c1410003103829078008283c100c0b502c0c8a05a00140f003864036034140a000400728051103110700020700700d8180d039000c0021500680e0110b0300900312060041d91102c80040004c1d41d20f0b002098100c032680244020b104480d40f0510a0342d00c540d40781e940320804185011002d45010320094030482d108184000020701054101b140120740d02000e00003181e8603454030340b4030140100310342c0340c18241c5040342c0c1c0200701040400381502e82150914403d45d043c11081c00001d158442c450 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 93377824 1250 93376574 93376601
    0xb0417040609030303060602011a040506030a060f020d050f0c120a0f060609050f0f0a270608061905010f0b0c0102130b040f090b090103080906040305060c280206040312 74
    0x140100d0381d681d1200c06902141e2003030300c2c01d010b4151603039010780c00d81700416400303401c451038040380015901d0141c05c00c2c3c0d00280d0160542d0396010282d02c0f10020707a552008058403440e00041c40c22b2400d42e40c4d115607540050508160305850802080d070140340d20030000c0340f40d141c01ea060042142d166040d48541c0f29904500f03c02c00034140d46800c0901310000c2480f40074807545020414803901d081c101200000141e0007088804100e0802d8070180c090070045100400c1a00f1581000002c40308030300c2000090000c1000400c150315110909000b583c000e00740280f00350b820003004101c82c5440902e0001520050b14289896804000d06540280600050030031131245130f0b640060940302103070081098481ca081016012911104040e00b5102c420200035088421070004202003180c10700070740140f40c0010000e07803600d0350b130b43c8441d0320341481034404110300c1000182c00a0050340420088a803501441c4500044000182e000785d1118002000a07050000e04810b000c41510240e011512610a1 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 93379074 1250 93377824 93377827
    0x60f04140604230619050c2208010b1c06051e0709050907050a050f1e03070e09100510080703110a0c120e0d08070807081210140109030b0417 62
    0x50503d00115240708030200c20124222920648503200801c18503c43c008045498240800d180c01c0c5500070080206030402c030500c240031744040f91282481d2486091104a0304065090510481c6821241500b0341d8510959903055400d81003009000816581030f049100040c0076a10f0203141c00303103d082d400860303c020302e401c010001305980000d8864151403043e00c001c02d9036a038038079080e107031441243c0803080440e50070f0101008000c1c0c1d1038001c001050070a0020707844207080d1107000400c0e07002070b40d088012903041d04005207542484030b0419031180c0c4400e04030b88007920701008100243c0c107031031182081003103843c006100140242c0107488603207258040d06946d294011002884100040c20844961281c065200f084602c01c200c5240041c03c000d0620002071090f640b45405a40310440c111455007040c0004000715500401508060410f103c165103036140100c80440104070a820000342c1e00100710b4000c1d0542d0b44140f05a00740c81c0d0042d001d80064441c1d0804000b1b00d1880c010040c0305800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 93380324 1250 93379074 93379081
    0x9030201050f010f1a0c011116110406141c05100b13060b0307050304030309020301020f04240e060903010906060f030c0e0c03190b03060f01180509060f041406 70
    0x141544094802c003002c804001c45a40ca924540c05402028460f4139000d000c17030381442a00d034001c01c0040104005000001030409000c02403c14190082001040d001c28030b25404401d102c0250201c11400c1c408480c108003d030f0820310100b402d01e401010030340c0500c0182040600381446000c0303080d181a00082182d414008a2140e03002800c02081010b0080501503203d40420805015140c25200d41046080c01e41c1e8802070701701c8407604000e00c29010161900c0244000d80c0342072000304448482c040c1915a9582050240e20994081880c640c0321080c0030a4100c0c2020780c0080b804654807411602d03d44d0318004180000e003d030100d800c003d4140751425000048203003055942004a0384202c41c1c0841150395034402104c4604201c80e007009020b410400100c03c1c03106078036586003043c2030f45000540c1c184107001191030407800304c9410380d054600500512001030480080c4072680314011041c8030340e1900c059000d4540034060003070480d0103044400300c3c0422501846c01409285c000048812a24 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 93381574 1250 93380324 93380327
    0xe100c0c081903111e0f150f13020105070f05030d060506070f1b0504110c0c0105031b070c0e0a0f110403030504031103120309030307080f06030a0210031b030608010b040203040b011806090903 84
    0x400c407040c444094454140c04c0b00c2182c84c0094078500c034041c0088c00c41c54a0b41c0d000c80c50116a03081410490401c03030304205c0300c000980402c5901040600850007180c44110100e800c904480c400c2e0002845a0800e0042038005040d01c40001d04d495030106070a10200d090044643c1058010340286500c0742c24868800f001c00300010150124542500444050440b0320005660390700c000c0ea0741d20944140603003400b44040f030100041c02440e2003203030841a5995201402403003013401f0341d1765102e601c2e03c0742e0035070a01e010701e8020740b11030708009a045482c043c5140d401400038401e911008002c013070601c81131916550244600b242c81c0b1856202c450390b9203008000107484c0d620882c1e4084c04191000040358400b121606071900c01c8401600034a15040203030200714401d8038004c01c5204040d05e4100900c1c48070101d41a09000301c0700d0362004111181862102c0f400e480c004001c050003140b060082202150200b04020304442c5904020001900c0d110394400103480079800c002c11690401d0018070806 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 93382824 1250 93381574 93381583
    0x5060a05121005090403080603030702090a0902010206070513050d020310051e16051b070807080a17030601020706140d140a0c08010303021c0e100c0c081903111e 71
    0x1074120052401c580d24040422240307001c5005507504819010001000280286402030300302000030704032803d2110a0b400114200022502c0220741510b0300d0300c0c0411540c0402c0b45503000750320b50400c075080807101943c4c242481c54031f200b2103200d00d0b0005007030b00c00e54405021a0400358000c4500340001d10b00302e41440021040c260065018102041c00104275494803ca0814100e00541e52a442e03c500c0c0080032440307001505d00032046010717500d000108407004018050003820008080c104400041c20500441410400c0740030048000b0002c101c480d03a1f0118125050380e003141800783c0180f030790745000441d60254180349411980381409440d03540c07a44111180c8101c40c40c400903c54000c0a9070100e0304207500388030040c05680600c044000306d6804c0e0760300f02e10001d0380b483c0000b11b10b540c00700012110300c0743c08291004101041c8255041c040e00900120141c90300d070317006201c280c080302401e004200c605100a800c2020a04840c0e07400401072017207042c4450003105c182401103224003420f407a03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 93384074 1250 93382824 93382837
    0x71110200403050609300706020d06090b120c090129032703070c0b1b10090c0503070f12060209040c0905040506010309030516050118150c08061f03020405060a05 71
    0x1036114075290b04002c3c40012202510190038403841c17001400f290b01006c4004d400981d030481d0441c0d02031141c0707001c040d1148112001480482e40c0450a40311200603c4200b011101000740c3c950003060303010f000ca072203101c0c0340c40c1100c1c041c0c030b10900d9425598190f000c00340d00314025002401000028440f4440c0d4080b04c03002c5845040070560380481c10305048507668841c1140003041c8421018040210103501c001611107014045e00200d99200c6140e030a0382003c510f040156259581d4880b0035043c004d00c90305d007802916060300100241c2d8149032410791403620310301c1400888000100a0000c0100039010759498102c040c01c00e00901c1c00c2158050140d0305140038040c041d03840e24000a46540c0700c0c1c003176091000e825499603842d0407207404002040354028070090fa1190340ba9080050806a10103042283c18007500c4122070854440038003a0a550740400300c1400c110149040c0003566403100d100140245041d030b0704a102e8403005805034064080c55020940c0b0103000310f090f081301a08a03004008 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 93385324 1250 93384074 93384091
    0xc0705030c09040302060a0902011206060203040e100303090b030601030207021503071107060c060b0a030f030818060c0306060c011104060210050619031506030605010314060711102004030506 84
    0x5010000a082c80030b802c1c42250003070b0040e8442c00219a00000075440066a40d0040c504818070150b0468840c0544201e40e01100042e48005020002c861a000c00d55030052885003c140d0401d02e1070b100100201d089003d031031003285001020402a030300031350444010680c05005d402100e0f419032400e455607001250300401180da00c400e46644460301140c19400d44200f5120242e040c03030030b625524024514036140e560040c4401502101060316a508040010f1096450921518142c60140c141d141240b000c1a0303103501003024410401166015641e0150094a1350340d160366a603200c49024125500210860000019001c200d40b9030101d1689030909110700c081c01070b030302e4000c244035504140d00d050340c0c40710340d8216003480042c0b0700003c2644081844640411074940780e488130400c488080c2c0c81100c40000091070581419010700059034400490306201c1c02c0f401030301d0009511100c20400040c015551354a044031103101d000180244031801e00006030700c55850385460703503441c8020341d03044c103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 93386574 1250 93385324 93385333
    0xa120e041109010809063601021605070e04121103120f060f09011415190c0605010b031003060c02030f07110301110a0504030b0a06120b0610050708090d0204110c070503 74
    0x600c12113002585c20701440341000600147c883c4203810f140a5443d43c1d401040c0c01d0250414600401000d0020300f040290341030713203010040b00619181b4940201c0794081005e605000c1c0802c001702e00395800f078800810701030800040d0740340c003059400c0c01c521642043c4a910440c6c0414042c030004136412042c8640c500780c400401d007200507000c008100f0f10900ca95496610301402041036810404003101986544540b11030800e148125050051001c43c0c00709000200e0900c4802c2c14000316024850044c50026038007807550400d0b11003080c3d98440b07404094031071501d03410800d1480b442081142c1da10300c0000e94054454105180c201c18111121500501c0396003440c2d4507004501d1031608540090301c80752501c82c5414616a190410390134001e11880c00390b07a4079800010301818000c64079404520410000c0080c3c41c0c40c0c2c08106440c00280c01d01ca0400c00c040c040c1c01c0020351810b0860356000411900220642e0451000901914801082c030044503004107000f600754500040403025500e0880545 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 93387824 1250 93386574 93386581
    0x8070e03190611040e01031a010609080628020a170c0a080f22030507030f020c0d08130f080d0f020102121812030705040906080a0201020a120e0411090108 68
    0x1640d141c00e0a4285a20085244680340015100c1d5002c181d200010004941c00d00d50781c0c1d810500503080982c03040c0ca00d42004c100111502245204550240244c2d0801020280c02d0098581d0346801c0100005140c1d03401c1c070b001c01c40c09400019402e0492004000543d9111039520000b0550003070b910b06c90050002c1c96020400d42d00000059401d518285e684440f00e80d41c400801c4048400050003100c804644540d42c1100003d5515106504600903141c150f961109480c000380b081c01541030700021904030b480c1044241d40d6034919141c6858224201d50b4589100d4050300148901a600040d4502580350002500d0388000c0340c81c115001254685400b00c1c020102d0036800d074440c220700010b2105403a00000c2c041c500c010000001e103e07680049400c04200c0c0c0361818419401a41c5503030108001040c1040800c84600941014103100005011402d00d41c1d40040e580c1c20100170020030259107803840307040b41c81c455981190702803c020811300c001940003140d9185980a40b80882c0010300d803c000 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 93389074 1250 93387824 93387829
    0x1410110c011a032a09070305040308090a02092410020c011106100909080903010e280c090c050d06030c090c0305060a03020103020319020403050c0918060a0c17040308070e 75
    0xe40b100c12030040d01402c22803103954210300003030344410858005910310080102c400c2d29402c969034856155a240050b0341c0c1441d0070040c28448000340103004950203100800016240c0e40b42c819001500b900004002051280c900c403910300d900101180c008141c4013903c2e0803250700042c1045940d03020381364030088480311f0908030b40700c0004032960400c1d030038030303034020021138400340c0c40140c010b8041c402031400c06442000203070075501141260003060384892801c0c1c504030021056010381e50800c0c00d89010406061766102140c00440c40307009441030740c1c1e80c51011064080d0040f1a96202501d03402c10003581c580c6008210000d43e03000b03f07810710349442e400e50380d414000e2040d28043c0710010500f54055180d580110041e40c8010100303808000503030b151524460550011700045e510400c007410130700710200148070844100919003040a240704040c2d803041800404c4098000010076404a10f05400b00b0702500c2549903084420300074040c070b03000c200c2070640c01805075028280ba542c0e02146111034004 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 93390324 1250 93389074 93389111
    0x90408030a06080d051e0405030102030f0411010203070308060d02010306170304150804031d010504091107060e01180f02010c12030e0601050f03030a0315030b240603131410110c01 79
    0x6040e0081401080a91b00c100251103103450b000c0380c41600c40f40760544440100f8207a80043d02c00601211035002030008105100d00c003010203107c2172005508100b11031310700421072000507207581c0c00f9035140c2006a041d64800e400020103026802e000310881280c0d030311515502d43c803d2045182c5019001003a25410303114401e540d0207140c0503903919400b003e54160840031400a000071134140700003008005500c91103401102007403450449199146da2a50400b0816241442030030752443c3d151164443c800d00c0c62400d8034902075040440310030b00c2289407005949001d5524006040c1c4100941d07003481b5168107400079100050260180c07850f0342d03039800034418614803000708a44c0c150000d0014600c070920980c0001d001410082c080440280c2d240c481e48800310007501c0409541509103041c8900710358684d070361103440c00300380c034480e2461070102d072a420928076804c8018240301c2e041c084a09203800402c440d0b1055081500b00300240440324406552130347c00408040425400d210b00d03a40c090390500f0 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 93391574 1250 93390324 93390343
    0x40b13020607032f0c03070f030812070c0203060a0501091b12020a021e010c1b02030309010e01030b1e03071706060d020a12030504260718060302090408030a0608 71
    0x28007071410204142d805a401440e40d07201141e6082d03612001c0d95040c010308a000d404118060090802c161814083c10704002e07513500b1030006002d44060410000c0e4068048440100d80001c1c4121151901e080440d0641a1000040e41c0341c420f82052104c02c1000d680b105042b109800401c200c65542c14090308551407981e0442c4001c1f400301500000002641e400a0142d01030038419103403030034600344e2560700c0005040040b05040e903451840c1c540c0660080701110804c2c804035401c03c0c1c00c1c062503002a61302d00c2068040c83c10040c80c545c03040f03001d0740070760003070040300703000070102d40c142691100c1104040c00304403115840381c882c0d0000020303139030b414a44094403440c04d80054100c40d5200c000348050105817040490b00041c4001d40014030b09105400b4000e2a80729560386170380c1e640351080200d4400ca4200711114000340096540415250028400040b02c02000c01e00406035040200c200040c41580c0c0043e40000c00c0b2803c000c20007550070008c5100b1422240100502901c420640d50b0720803452 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 93392824 1250 93391574 93391579
    0x1c050721390803060a0f030b0702010605091501050915030a09020901060c0b04110d0b0103030e0a1508042406080303010806070201020705070b03040f0c06020a060b010f1704020402070605040b040b1302 88
    0x680d01000418804402554011405031103580d4081d9200503081046e9141e13401a030b4105200b0b8240807010ba4280580780040c002214698400d003480c0704030900c07241c26100d240b41800000100944280c8810b19a070010a598607004d6440386081c600c0388014210b000c034228450b410460000c07c3d52030069074241f400c541c1000003080c0b00e584564901003940595001ca45c0c2c4501c6445030301c00003071031481c64180a18826510310288000c1c010500c000c000098205144000441c8401240c4a0344500f88640c029003280701c440c40c030300c41038184081c5404200c1d100605682062004644440008000c5040721a07200450b60550b603608001c074202e01910300001d1080d00881c0c410004040003201554105000300001a54404035030340d6001c3d15800780d403010015170000c01040050004030b10660010b03210a003807004064095460040000e640765004008030308945007ca015500d07140d065035501c0b0351208080005080c40c0c103008081c038a0031642150a100604001041001180348100800e64013 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 93394074 1250 93392824 93392927
    0xf010f0905040e0a060c0908120a0804110f12070609090203090c10140a03050103031701061b030207031e1506030209010306050702011515030e1c050721 67
    0x302070030403002d04032500720f0110611901e035403400401c160b0310500170018420703102c60018a25200210341000d99488005080e910203200400107260010b100a910550003102d01c80c0c91010384000410100340c101e9940c2d0050300e40c0d141300554010014050342502d9050b10703500c0c0550740d1915020140c0c8001c4506120035042141000035900b0241900301859049051584410911a21008294101508540000b80c45030010018950000b240c0701000c042ea0801200705d42c108080641004110744031030302c0b06140384181c00c080c0343c428030400b00510390001440d124507100500c00541c07800e140a09a07203c8400c484500341152a42c03180c0d1084a81c00303044407600342e01e9521044000c1000400c494103554846110b0550024401c00c80c001822100c84008060058100020300f11a0040c0d41d0807150342c00700d41480d001c801d540b00b04199a46036864050f580304841c3c5401d00000c440c00c1c10820103640100280005d580e000358001c14031001d840e40c241070b501d003120722410250502d00004000700d0741 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 93395324 1250 93394074 93394079
    0xa0506090405040512120a0b010e0a0303140f030903090a0f030b0406020d02090913050c01030c08180a1401052a07031d03030d0b030708011e0507030f0e0a020f010f09 73
    0x6194009690050044069403809102c841a031205a84025040e9411200a2040010400b0305124515000300302b0302c0c20700301c46075080020542d50040e5000c09424810750144141468401408540c00103400c1160039840341040c0f514507980c1c1d0040d0544501c5040301c0d4001150350880351401c08102c0c1d400088000c03003600e940d155400258080102449569002c22444031140c480c840c01034000c100d0001d24401300b031a2410100c4c200501c1c14007650405040c061080ea003240c0c4109016001010400034251000c103400300c89142000c0d110b0020007040d03a43e040f01044001c198411071160b45040c028440b00488141c041e02c991000c5405040d0036801403007002c01203442560010605552405007003884c00500c0000b0b49540c001c00140c1d040c0644651081140e401c0c244400c1004000d048000d100c0c000f40d001344028419180201c3d060415503550000341e946100c0d411005271102081e00030443c0320705041006031681d100e103c00760b005030600610b596043d40300301c8803100301d09019901c140c252030 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 93396574 1250 93395324 93395329
    0x20711031203160207050d1208060609031011190f0f020102040b0a05030403030605040f060311060a020c060f0d140703050f060f040c030905030a080103210503060120061008010b0a050609 82
    0x2843d0480320740862050010100f16a2a2288001c28442c0900c903014110005150010159640149954002c0c1d000f40700311007050310002100041c800c002a008111104402d03180e0340c441c0608241100c98000402501c2c020a40266940003003e4072541c5d41b82c2c45030803c01c010303401c0c3d200728400d2002d015820030904c00070611400246400600ca80f50114031582e50340300103000d4680802c2580625640c844080007040b22001144820080507034030242820781c402800394613000c4168007540205000500d00da40c01580e9402c0756504040720a00304440414020340d8400c3e030074100c039440702003840d0102041c0041ea5040f256481400010105400580301c402480050f04140c8070301410b16460b18007080000d142400500109102952400035545c51400e2080c03620111415000c0c40c2629105035030a0b042c2d2003c11258031550030b00380028101090b002014061aa003801035800e0b00594040c007480c1c800304140320341124500f000074094843c01200300031101c40d4911078554024810081081d0a0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 93397824 1250 93396574 93396601
    0x60212011a1e0c0f01020301050109060e090f04150207150f0209150d090515060117040507050f0f03010c02010507030c0201061217040e04060c080a0204030f0b28020711031203 77
    0x101042c9031501d04042c24aa40310b46003007034810f03001a090750003100620003568041d40c1600204224545200011501000310f0340561001e00b05428001c02c84002a00f402568881c119141620300c07421035036181c2c1800d01c07608130100c40b03400e80b071980e0400c0301920a9100d00e00030748004640c0100702e221006208900c401700382c1d0000d100c4800c0b0984408103500032a0080c000440b0038000503141e901300345090000109a41c0300d08041c0040e070701303052060001281e800a03600d0143d5074260f40006080e0820000244141500c00e0402c0d4590308062016501030b5041d002640550b81c0c80e10244119164400c080e0300381c41250040e04040054100703800b01040304032406012810100c00010703c0d15031603d5071120b440b0807c03076003951003644808040d820140e10400709a400b80183e07800b141812304503a82c9440c0c100103503a01408504802c13000c18900a2074400032140096900c0d420507114504071a01c00103034010140564039403920507500b030303502d0801180010420140c00130652a40c1e8803042c482684 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 93399074 1250 93397824 93397867
    0x1d06040905160303020f0c01020105040b0a0e070302130f0501080c0105090f04090605070801031a0c270616020405010e01120b0a14010e0108010f0b060406050c0c0904060212011a 78
    0x5480341c5105910030107216560b1501550080e40503002c181260310006240100c50080c0074110b80c981820800860104001607402c000e028001041317009a80542914010090704042e40c041c6920f118000040799560005010100003017003440541c1c0d9030150749855120b0921100c0c0820020024015149002d15072459038060081c400608401c15841e81c40480c1c00442e001004682c1c00d500600c1800b56001035541c035086412000100ca00c0c0040c42c0d40c1840c01508144c3d85c0820f0860407101c42c206c15814944000c44015207140e403200c100f0388000c1500801e800c002d0b030080d841e0074001314507000c10300c0180f4140e925440320b8150880c07850303690a0b84620020000d8883c00d6035459a8890340740a081c5a5000f0041c0d540c803c48503504101e0f11508451000c58400e42c803c1c503021070164543c03600c0064804480d07180c208207841c1c40301c2c012054140030054403802d5015400c131003080700700004c0354042c0940e201c01e00d00f8035200fa80c071383d005010404280e1140350306003003041c40680300d446021401d0f480c2 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 93400324 1250 93399074 93399083
    0x90a05070612240305120316120e0609010501090606031505010e0604091a040c020d0c02090703060902030103061b020604031b020414071106060f010c141204031b1d060409 75
    0x120904200d09400c00040340c442c0c0f00d14095881d00040040c031200b00101c4c6000020348042c00d1850814100d0745070100494800c440912848181d0010b00e83c0c0603910511140840304142c400d0f510307100740f04c0e600030602402400d12152604201040c0f4902c2482050502c2c40c0c8042100d00003070a080041d01d41140300020f06520072410040070410074480d010382940503003908a04c3e4051038403141004259100000040c0071584004401440ea0342e0050b400604260141d442d01c000340c581c50000c50150480703170441002280000000010400158440107130900c25022181c0b40510580c0102c3c0ca49c20243da010b400500907104517850313804a140c0171011944010b2000600c806226a00b0104e010110384031004104003030000392000c00300f0b002843d41f0400480b030000d80b0f00b00f01d40c0040c00280d81041c0141c00b990400c5d004c1e4507405420402c0f600f0b5121240300d22030716160f481c0f5180f801c580c00058505100b45010360b0001f00a2a80354003440014280c15520310190f40d41428440202080c803003c1e10b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 93401574 1250 93400324 93400331
    0x10c080606090d1e060515130c03060906030f02030123220f080d0608010605030a0b041703010f0303030c23160b090706030b10020c151e0909090a05070612 68
    0x18005140100081c040c078032100b403600701c044c0e07050034844200c2d00b00408100030008195082c29050f41e515403d200041d03900800010014200c440032402800c0940202c40704500d00a03010007448405c11014103a41d1084000340a00c46202c50101c080c0c984401c6081e0311000d441011410004d0183d080d00022210344040c40c0d05503409444424484802450541e000c1400040d83c82080050707016080150070120020b011041c40c01010a50300d080d010000ba012a4660001c60f0802c16841510001042244100368803561258560700c1e0031f14a07480100c020902c0d0284080c130a60186003440114030652424000104603c058006258000244050604c00c1c1c1c2d8804800030351034550f00c6006a549200a11b142800c02d08041c0484441d4403130244220000742c0e04000c00c580c00100030b84030440c16501c400c050b802c41d0046c20341030300446c40c0c5100910100d00306404050400c0e0301a144000d4226001e00507600c1700b040d040d132039450340e01003c0c04541109a0500100e030061007204042c0f40200c1c0d000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 93402824 1250 93401574 93401599
    0x201080a020f04090203190905060a1109040f0e15010303080c030406140103050f01060602011521080d0902180f0f090a050a0f1106030108030702100c0b1f08010c08060609 75
    0xc2003a83d009400034140c5179400f1052024030b5140741c0c1c47c205040c070f00701001c000ba041c454079038941c0e03150000c0200d0341c16521056156550f030b540b5401d0341e0b083d207409882440303844144801c070405030440030b10800b043d100e14025095000c642e810018100c0743c0544420302e140e2103180404107103a00c0100700741e0303440703480e072145120300d40941182c2030003140110050009905050310090030340e1641d0384007608581c1031441100380070b05904080800c45412808243d02e203403400c0c0d0700900051082d6005080c400303000c12500400b015a40003c2c103900c0c402c89003280c038000014260191b44605584952040f11300c08000762684089000caa500019040200d40b9000c0e8a40d48240c42c2c80050b00b02100c070003082a2a6604120341d09070042c1049800703d40c400d00b03541c141000d61b69603008503240030b0700c00c484038030314180d02d203001d003035008800c4d50021112060361815403040320180e070800360035500344001100d0000310f000040c4210111000c0715510600261100c50400c600758100d42403c0c0ea102c800b01444 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 93404074 1250 93402824 93402847
    0x1090f020909102d051c120e030d080106081f05060a090305120f0d09020f04050c090a0503030c150411032b020c1c140609010b03280201080a02 63
    0x140c5114051040e083d1070154100011140e44561503101c08901c01c2d50a24520410b4480c2003c2c0403d0310301c1070f203030190207074540c034101307420460f0b5140e025011880700c4410702080b55014048040000040e000c50701d19042841088460020900c03c42000070340c5400400ea01d040e42c400206082a4890080e540c0241c49500040003580303e00d00d00c401050642000b00100907041c080b5025041d00d00c1d9155091113801c580d8503840784a0306035100c1c515561240d0681c00c550312014500e096000c003070010803075890071501486075984141440d511418900d1070020301464000102c8640d441c203007014201e51442840d44403040b020147c02280e0803242c0e0985840103440c01c0014500e00e01c03042e0005002031051982104a0b1034209091004540101c141c0a11b41d0b01c4188035242c0c2c000d451100c0002c00c990a013806030580000711307104e030800d010794000d0207843c1d001504113041845040b0156070030300307004542c9150509065446041417900c04884000990701071100180d000c410f0000251910729202d20 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 93405324 1250 93404074 93404089
    0x5060d0e1209040f1103040803070201060f06031a0406030201120b01030e0d090303090602060f0106111014150a050d0201030c02160e0103140307030210020901031103010e1b0a0801090f0209 83
    0x40c1030380703041010502205a1070580103003140794080344810442c2c400ea80203029107920004101401c0b201c2c0000203d035035107100758400c0c0020305280c0c60280d013254881e41e004000d0030006250046452412815120300d240038402c01044a90517103924802c030401003215009001c070a0300490605d1343d52000d021304503109021803011003070b56648a40c402c505514025041e4143c80d000f030310440d88440c0410108128041c07100d8107444039402c0075412009220f02c0d15140409400c81c1030981801c0a840303601035061014643c1c001c0c40540f01ca081c2c0f11320005c09100c0310703003035510507aa401a10100b541015500030b80c003c007201d0042d8130507201c603100f407108005240070f210b62042000c0244100108148507034940780c6c201c403c080c08041c6103803100c140c400079560550781500c0000301f58001841c000b00c0e8004d900041c21403901c2c02009407a580d48201c0442c07109400c13903441822025020882e008000b00a0407521000815100d410541e400d021b04400144000144090031aa0030084070013031390b0702c100c0f = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 93406574 1250 93405324 93405343
    0x11010b041103060301060803271c1b05010516080c1608100506010309050a02011404170102041e0303020d0503062b03020c09010f031e080a0504080c010c020a05060d0e 73
    0x181c0042c1d682c10103405250840701d0b6030744441c0f0160005d11018a0207143d074624600800d280040e40c40841b0203110014283c1d54820b10b0140380d900c00312819038100501e01e02c1c2051580443c1e81a516555038407001903800d40300384c281c10011017110300302440006103180d0240c074102c800001142c082c04480e0982043c140e00b240c2104007103038080d00317003200204a903002d1154030000a180c203200d00782440e43c4a82d583d5030072030b40c000d050103100510720300144d03a944241e8008003039961444114020203a4854000c1d0b116001b062002c485c2c004000840000741d416184c1103e40c56401800c800d0000c0404131101d4101800650780301041a011042c01c900514048800c1251260043e000e07401520b406442c1c0280e11910700e00454645004100d1102141c40e1801180d030400030340d00c00301e50360201500303000c101440003d00c0e4070300120b03080307103c00c0d400030203001502d4031001214042c0e29032000544d01552110002540022900b00a121a0800d01e02400303030039003501000705901500c247d08904055180 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 93407824 1250 93406574 93406601
    0x20c0d050c06010605041805040f0b07050a021b03071707050a06091e0b1c09050304120c0e190908160620040315020a120e070e01060806030d11010b04 66
    0xc140d0792007020742030122500401441c140701d4541032400304801003805407500d040d43c220790b079030b4001406d01c40885580044140d100c00031460a10f040f0700d02910f640c208507001c0380144074a804002c0c84a400d403541c9614101c0040c001c4c00d58a14280c0c24001020111440ca00310780285540021181c940401420242005031550700d0b0341c9050543c0300c2194010aa561402c0c0803c001d4204401c04121003180c0b121324080100300441e1400d44d5060000c0c001c62240140240302c0050001070601502040480d5584600c60b00c020b8951345e00e0300030400040940391800344002d030103818400c204a6a0021030544d105000c05820090000c8d017070714140318030b00010348149031141d0f10324010580d580030901003820b041d40d1070ba007000d045840703669402c0300021010340030703a41c0000c81c1e40f6014000d074580e00005240301e1044c012507800800e966210581c0380700b1815951603400000c6012401550003602c20000030380140742503140c8004c101c07040c1c3c4244d00f22200a558801e1000340b961902c0c050141c122a02 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 93409074 1250 93407824 93407827
    0x307031a010e06010302070c1a09060301030c08070605033102030607081b0a0503060f040b030601080c030d0e010806011202042310020706051b10020d090c06030c120f020c0d05 77
    0x18810704019102c0002c142a041520400a10000580c241d04140540e04000b440d11000030810b014880e00d481a50041d50b403081e0040000001c00400300c40d2071080d120204151f07028a070b6200001c1c3c80031b000943d10445035001803212400e0f40528503411190042c3c851400580006090300882d0408900b5160400060383c030034200041c405010745c0d5124130f0040c000106203817180224004103d800007414151150310f0307800c40100e0310356964000c400c031018010160b8400b540e580b04c42c15030b10000799454030300070301a10700030007161805007418039441401a100e070001a0f50795401107a132864182d00074001154280130116a011402c01042803c0c4900320030312081b22900420440821800c0c48032404550000b101070003459880000c0d900010400c0c80b5100f424034680000e2420503c0062a5150851000c075081041809903001070a495019103a104403c0784c58190450030f49080e100403a000c900c645021003090000c0b42d000c101d0402c9644401410001e401320700d5803c0c452464441d40c0014030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 93410324 1250 93409074 93409079
    0x1030b0907031508070f03060b030a020301021306080a0204050609090628060e12071e050306100302010e0a060504060507020315040813090c140a0c051203010f05010201290307031a01 80
    0x10120240d8000e040d0740d000030710030170345042200b841e0f114050000420007034458600803640d460030009060340b5a4000d00079511034040f541401211b0205119210000e1009030205a01980c28401c450954030044c103400d16040100f000e002c0094000343c0516007040000d180c101e903541e031030075880134441001c07150f41015514016004150312550a101d07413182c5544c00c924110290b000805000310340c010050038041104a03030000550b1113041e400150140203a500304444450746070400d1050f68400d07202d0071010b00481080c07141903c01c5002d40d0300880e00c10007080c003c6d14058005441c000344000e08a03008118000340c00d00c00e01c101500c08444440c40071032042d4000d42909181d5000e06559401008030a03003c200042074803c4c54035003041c0c0d810b4001140038030a0301c62020114155009070803108181e4207a4880d440c26402441002404100e010000c01d8035881070044d110403040110040c0000c174840d01002030034501d2081d0f000c1d41845448000400280f0780001d0034400000100141c40642c03 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 93411574 1250 93410324 93410351
    0x90d020d05031201080c151804090c0b0c0d0305090c01080105130e0f030702090c0c07030305072a06020d0212030a05060a03020a17060f040201051e04050406091a030304030f1101030b090703 83
    0x41000080d00ca8000c001c0c09507102d800d0710b4200c85400088102c50102c0cae001101d0074003506e10f800a401400c0a60310005907440401000500010051169641044140c1d10240040d0711905007420050005e1842801000203140010400c00c2400c00c1e043c0008007540007800c0180b5040034101c4a01c140d40000c42d9003401d600d0a808480d910610340f000c11840c2407130410005858151900008003800720114590045c460144010303100f0320813426085980511907110316020304a640320340c07070052042d9a14400610306c04600c3c80f1207a012024403a045071030b40400100505001030400380c10010320640000560f5a00d000c0314001c0150b564806154041c1c0940c10303050060080c00100100c80d50414440142d038031130104c4250002c4030705000402d01402c1220750f4203109036801030380d00c00e007410030100305120940d0090305110050000240032410100502d80c6900a030b12000d45400000080480810304600e005032141105150014500c00c407000019440c84c03043e14004000303903807203069504c42d0 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 93412824 1250 93411574 93411589
    0x1011121201051003090c03030309050c1002010b0910081b030c0612010f150806010503040320150109060605040b0a090506030c0d2d0207030315080f070605090d020d05031201080c 78
    0x306214136060211400307580781c924881046120040c1015035816110703003801401d120304400140c00a01907441d500f0b010130020b020b8030842100c079100d000d00c00082101c000204013080111a0070320301400c03200031130086030458510214106501400b69410001480d0740c3c800c0245a215019181041300e941080403c4201c0041c54101062802034004003409450300a140f0550005091070019075981c0d80c1e02d0300302c0d0070310780c0501c0c1074104108181c880703c0a000040741010030b592141042200381da07642e076031201c2980c03168410000845d030100001c0c080a080c0000500c004070541c2081e003180c83d55034000c10000d41c01110200c54010300400d4071402c0410320b002d00b400c3c24140080100300c0031000d00003000e8107820241d01041460340001c0c14400c1501a401c00c0500300f180c120150715140c0d464003020703140e4260303050314001c5000b01d52010503101c1c054002c0c0e40044001401241c50707403081d0382c03d000c0090300340c403401d8640e4401442003140262180000341c0c0a8180d52003d4140710003d9001c0c4140c9 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 93414074 1250 93412824 93412849
    0x11508070207030309050d0201120509010c0e09010e070503040212060109050a0b040c120e01060801020f0903070e0408040b07030519091502071d0a1e0e06100302101112120105 77
    0x11034020b84010404294000b1003d819640c080759000c584d2011403005890303a0040d000001d0703030181440d08000380302d44190701c410381a1400391594600344580c0000c00000050074041c08844244880101d00128401c0d4095a4060b2028003000d143c40585880300d0f00c0c16100760b000401860300c0700100101c03e180c902a601a465051350300380080c541640c0d01034076444010000c4070b4841da0320b17070242d05000c101750400401814600001c55494181c6002c00303800780e01684031a030080c8102080000d684054a407520700c180e4114020704d0500f41080c0e4507a079290701c250f00903000c00c1814440c034801d114007903010103842c0109844440045280036070901810f1008a0000150b4114440070046000300c03000e040c207040c61000b43e031000c0d9030b030701403100c80100b4035440c240b184a103c0d44011041354210764061b10410611404450389556841d05900496600e808002d411003002e22180745041c3c001c1180d4411042000203461070340b01103c0307980c0550341000010004c0180700f03500401450410b0b4071040e29 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 93415324 1250 93414074 93414077
    0x21030501030503090420040306060e090303010e0c16020a1502010501060305060a03020d06060e0717010906050d03080a140c282001060315060e0f160f0908010501150807 74
    0x20640c596102d6035281d0180d000d00d02c4c025601c8100c8880c1005440340720f490b2461030541c006407203d44900341180100094010083c0703c200842c00721301950300003c01d0700d04a4000396460703100e6035504040e0a10755004400c20121004015580388011303640e81440101406000481c00325001c2c0c00d0f00f0086c2501c40690040003814504001e00405817521302414081c2e9070144c900c0806c400c464034160f0300800750b40d030110420404e0f0000340f00f8455840482c060500030f0300141c9071260707621382e8070034002c64070300b0302c40c16034041801804900001d0186400301e17484203117000e0002c2c0b846038081d104802d10388201c03000040d804000400d250800c040c1941c404844000311740d6061140c208138005441000740c1540310303141c0d45003004c52140303041d000d40040300034541c414800400140b141031242c1c090842070154a04003000e1500094110b40d100c50422300c64520301c880991415500c10081da40a551061600c0402107100c501050703000c0b090182d036008280b2070b0280722240344409001071001e0f41c040d08040 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 93416574 1250 93415324 93415331
    0x10506040e060105010e03030d05010806010510020c0102030d09080717090307060c020303030c033c09032701091a07060501150503010b0d09050a0b060f01180b0c0a020d2103 76
    0x4200c00320010b01c0906407a002e00342400c800d449040068598014280c5540410781803d00108419501044030f504981003039030020540340384080c0503a101c001c000c070560b0040c0c0c4280251300e40c9400d1500098841402030071074900c0c149094540e00b41019601c0112400c1c0304000412840074201040f0100c0205028035111061348610707400a03440744009046101403040110100d610b101011803c0f24000011b480d800e03000c480c0c0b00c5030103c0b104000300448800c0c3c840c80c00020316000030200459020905c90031800b00e400c5010701080c5922030b10b10404504000008001140d542d100c160b0f8006403606001180e078035100c9074500b540c02d80f00160130105880701c8803c00004281c2d001010740303041d240b051032000d469250300d41041005003901d400107040307481421414024007454400140c00b8410a584030354400c00c600c40155910000303082d5586103015401410803c40c5000c4001e0150005c541c420345c0c1d210811034000829484550303005451043c1d44500e42c494103201202c0910b9240300504051 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 93417824 1250 93416574 93416591
    0x9010e0603040f2612060102010b030703030903030f0e100333091a0108070509010216030305030702060a0c0c1103030d020c060f010504090f02010c030c050d090e0c07020d0323040905040501050604 86
    0x141c117010b01100d85508503c104042901d583c000c0d04400450350014040b50001c0380d0701d04004007540841d2005402240c1ca102c0741d11081841401c00079050f13a0040c2c42c0310b00d000307a100012802008030081c28940710f0341e01101c41103080e10038044e0040307074146600c00302813840c00c155480c000c407a060904142d455002d0701042c4560b0340c200100c035502c0100d600300f05490fa2420001070341404481c2034210011541003c021080640180c041d6010345403d50840c1d000d03a42d10400042280e04404000300806c04450800000070180070304034120340070160540342410b00341030031981a608550f00c50991500507504010320355003003901d4140100310888081c0110140c6860714505042100000b0381000541c203075120515008442c0ca0710256800402ca030540310940100811060380d40c000c4801141c03011012500720261501a00c0c42c0c1500145454022003040d5010b0f555a0282c542061031881c40082030184185454040d00c000c180c2201c0100b990300e41850007900716280144514485c501d4101003 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 93419074 1250 93417824 93417893
    0x207031a1807090221040525030f0807060506040b03190302070906080a0b07020613020f03010b10050406020706080903040608090703080a020a1505160503060613120210051e09010e0603040f 83
    0x4034105001c0072310032504601c03910345000c860300b40e03144c10191509020903d10b6081000d8040100320342c40c028901044261108402c010540b4064040640d2651180b0074003d00071030800c400e44031803442030048030481a40c03070722540300f0754800d9402040d4a40205004206010489920962100706440031301a20302e0505515091028641070282c00741c3d4180e50035070900e440c00d50211114090040c0480545d050341100144198064010301c2c0040c02132400020b40b860003000342c80c0c00b4010b1348010354102070a101007203407d504002e01c003100c603228008000012a03611342c000c019a051a03030240c00ca00314141086a24000310b03940300d6000130301d00010407810488000c8c50034584946864001da4a48481002480710300590303803200c460303212134000082c030904007265200c901407003510030081c000c000b0482036030329010b50311402050080d2100c109402102c0400106500034050405071a400c13811400305001e0b801c200c40c1100c915065421400070710a82d030009d603020411468203a90840101d120 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 93420324 1250 93419074 93419083
    0x903030408090a05060d150b0a0e04050709030b010305010504030207050f0102030d2f0c0d0c031b0218090102030612010b0604140a05060304030c11010207031a18070902210405 77
    0x40a41003880216100c1070964aa0300c0c40700080000a0400352030304503060485008091301100450a1f4071800000624403011005951000c1d816859214040e82002c0500010301030040c1800b0400c00c5c41e00380400017940c02e4054a010314010400080e2625051402a1070484260001e42c410520403400c2000c0780e80c004116038280e01400404603041c3c04402c0141541550381c11a520705203182e01d45c510000d003146010f071101003501c0044901e01442d1030400c1c0c808000c84100600055555030504000b03d0303a990409013054070140120030800981c00c14406003036801e03624851140d400000b444682e2512400009004400340004c0150546202c0041c107144240c0c81241d04a280700c00340000e4641c1d80700110303402000003404280da2450700d45402003610310440021035503442d56004a01c2c9652001070701c1801e0701c0d070111183c1524228001256003001004002c0880c0507110300c6030790f040345001c0c03060310010000e4560240c0c9540300d403041840c410055402400f01144400c04120104c0c0d00001c = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 93421574 1250 93420324 93420331
    0x15150b03011211030d0c02040b0d080f07051525080903180f04020a0e1504080604060207060b101d06070b0a02090a03080a0c0201030b0d030c030f2f0f06090303 70
    0x640b24200303201a150000031891032484865040c020701007406140b6820610910056100f00c60030021a02e40c51700304410500119001b80c56128144055190416204020407101e8010803c0b00c0800c0c02070300010426800c221000c6500b514002c4d50000c150261031120704c800712840c24415058036201200c241daa02401c3c103040c400103803074440040b09440d40c0e20030501c2c2c0070b0058001d55440310340700c40c0a415070340c00e030200f40c0c01102041524003041d20900c2c00e41d401c1c1d922040c0540b6007601c81c3d49481019402880080d20f10710b0b62490076400f80c0e640c41141c44a6100c181c1c45601030000f0703101103800700001c98024035014120802250000602c3c407201c290303000465180c0107031903042c1c0f180072410307640c40fa8200601e000c5000aa880e00030742c0000c10a80600d100340e0303040c040b1070303c0207041c8074580700e410070300071701007242c43e814000005d0056101001d2540c00349001c850100c42e1020240c4030010403511681000e4000c0d1070020440400d10901c120030269000511490404201080c0c0c0da00c03005 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 93422824 1250 93421574 93421589
    0xd0501060e130203070311030a05090c01023004050603090a03020105010506070506041202030c031c06050d0201020a0201030b060d0c091809020108011203230c070e060a030807080c0a15150b0301 85
    0x40000c541704d0181c1c1c004042024929010350f224500500c1c540018070302511120740078800c002801d08258400a400d95004400c0104610b5030440110005010756213400501403034031040c0004941c40c1c07203150195100340b00c00c81c01403000040ba410003908440e01a040140244400c101900c0841c1000815540050b4412005d510082070301c5400c80c11405170440381c17007090000140c403100c15114204039504a490b401c0c000c0203441e83d22000c00600b1440b05200030301603006508004050343c000d43c48115442e4010b1b200790306d0104c1c026800c1044585102420010860000c8140310b500035050011a442401c0102000311499940019006400521440740c14000b9201d4a00400d4880c00441a5541c8a040040c0f6181d5000c0700000064010100a401c1485021000200c47c266003500710300401d40075002085490a50b11502d1555100410075120f12a040085040c5040e080200c03211640c000c0350302e100480740e1284c44805441002e0204281c000e03503030f001484284c0401044a0455408 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 93424074 1250 93422824 93422827
    0x305010f12020607110301111b0309012a0c08150a060308091203070803040b0118050708060d0c080d0c020a09060506030a050a0902040c120e01020f0f0a020f030f0d0501060e1302 78
    0x161a00d150380c861700d2040c80703801d9420f004856540c2c07810b85000e001c2d240c05101d0f008030310341d1401c0003099903401150000c41c0001c0c91a1a90010300325089040c081d0100c4000d40401c80342c500d515950858180c0340e004c000103521510181c0c00d02c00d40d10407480e400042034101232003501d00e183c032140c02d00d00030700c2c039014807236000d0440c086094401081100e40c816030103d402c0da00c0f40350505241c00f48060900c164515003074004d42c90b083c1840c040c0300d0b251181005403180841d0740c5400c03003800031003600b070001100d030103072100c01c0403070b0b03601d810040c500340c01e246941c4654484555205100c5130b100305510480c038a50a011003407007207550b06010f880d030206d10700c0b100154650f160b034040c001501380188081d4001d840c1c4880c44034002c0e806494400f0020032000e05003d51b00c11906c9031401c03071280840d105034890040c4070301c1c81031095910081090304010710498807000100003419040d03a10000b00000c84800000d91680720003503c2c05a80c1c0180101d00304411210008008030f01c0483c8021040c2e40304650 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 93425324 1250 93424074 93424087
    0x903120e0a0e0c1306030c0206160507020604030c05040c020a0b0103110f1306061805030714180118110301050d060906020f040e190b101202090402190305010f120206 73
    0x4410350018001c01850031010b265090580b0040001e600400b8110400c200c045008521039029000d401050442d50740103121075a2602400340c40d0b408050246410031004000440150f900c54010f00003550280d80c0071040c0c54902001c22044591412040c415500100d0804005c2501040c4850449412610088051510200103a0349895003008150301c1865900d0070f4150f1201c0358050010b544581d03d80f00300c188000300501c0100303000b82c420380364142c4c0510024080c0d10f40c5607070b01c0003852a000e403000040e516604d01202c1d111034241c0245480c032800003007001c03454190b405400c04800000d02201d2565040c2804a1844001844090001030300c0d55003040030071010758119034094034807855964440c0c0e01c413030103400c142509884000c1c944010703000790b013040c0c500c501c540c480400d0f00500c42c406521403072000743c0d62020f107a040362504941c24441500c85480b60300040a60040350141c1481418000b400503040301c406800c181c4c050101d4500500540d84c6031060100c910307030115200c1d81c07542e1 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 93426574 1250 93425324 93425329
    0x30702010f0608010504020102060f100b070219060c110103020708090910080f0c040b040e0a030c03230a17060109050f0609191701050f07030504020d020d0b15010903120e 75
    0x22078908004000345407150001e00d02206601a500a6200743e00f81d5900d03848070090a400f03800e0a81f0743d411903100c40c0c0700403c60301945100400540d0b201038420b10f9a080c80440c0c84d000d000c041d600420114801d07403144402c00c03036980c88015541d00c09080440c20401c0c69168810340e03020b00c6034250700034a01c00c000700c1c000038860780b04940203140441c00c43e2907006203109100d1f00d50402c140214007442c10308c1c0c1039480b146407074000e1801744100040184000811518215403c082130041641401801c440d148503100101c00485900030100b5030a643c0d035681058001c0001e543c0c0c004031843c4592901c01d010142c0c0c2d00014480c01c580e4101d4085400100c0440010030a10540103915031000c003010120440c20700807030f1104101c030480d6010b20041050174045500740c480c05c440540100c605400011001070103540229041400a0640190b101c0540d000c078284501c0c544c0c00790703040101c0c0300400c00c425200c1480491189000c2ca458041c0900c7c40c2d41c1e200c801380000b0800d1040c0b003c1e40c4010052078 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 93427824 1250 93426574 93426581
    0x30f0411040924091208070c05010c03021c05070c0b06041104120c0816210b04050a0210110c0907140f0711041802190503010c050d06080c060f03070201 67
    0x840c40204200201000b500d000265542445406151208060000b4541142c6441841c104a42100a14441808094007214118801003001c0c0500102c00b502e9000b2031001d200350b504a6046403401a52041d800240100c00c030400510101d075181008100100030b0f51015250310107a038004d8109115403500b4000402a100303004d2598030141d40424009520070781100e030502141d0091201881c0c00743ca60701116142c1c80740c90440501e1a104000800c03e44c1e1928000310b0000c00321506440044485135115494904d0503101521b95902940034082940f414101030203050f9214141034403c0e03a100c0b00400d0302c1e03200d54102d00e4880d480d00c000003200c1c0c6d03000c0c0b0581649038000c804016a58161051000c0054110500c16030720101c0c001c050f80e50600f4144a07e040b48001a100c0e04c92440c034560800170107041e90550248240101386001401d92000d0241617650722190b00ca0a494000060b6a4000c540080d0b2100009901c82842e02e4019201c40048904800c0c110f003c0e40c0e6280e80b02c04081c2d014 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 93429074 1250 93427824 93427853
    0x3081209010b030d03060e010f03120503070909020301060c14031e0f040e10030605090d08060d05120301091a09330306190e0703050d03180f050c01081605030f04 71
    0x44c000c10306803810081e4942d101d901640c225149070b15450362130b107440d24402e4a4a0000800802c201c8051001050064016660020507894045151030300c0b80c0d140400d9800c28be01100200d51694094010003210b00303640390280484038015030800c2c240c080365104034140c0c0b132242010f507600000d032b8000d02c0401000311070107040303041304202d01400d0081c007040c3c1403240c070311080e503143d803803d00850024940030841002c110b080780d5075442640c4400c0200f024040c42d1000c100d0315441600c2d54805101500c90295000300812a00003e60800450300e0b0700700482d070030340c40500c01d100d600100100501018460482c0c501101008004402c0c1414030042c1000004123482d85480f03544100b040b60300a0f12003546010342c07043d00138048810030812042d07840e0134900000700260890024004928800e60146411070104242d42161500584440c250700880070700585a50304070302c420480a5800081c40b0b500070200d20318450148030506001041c502024111038945510701000c24280458201c0a001 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 93430324 1250 93429074 93429079
    0x303061c0503041d180c091e160e0a05091f0b0309011b1701050103020a02010f0e0705191406030a1d0105060415030201080115020307080c0d020105010b0403081209010b 74
    0x103071940c441c4c40c4113845802c4c003000b20106419120000e01d2110001c04544848405e0400038145140a0390411401c000010648554041c01c008200030054604514038005c482041401c1000310814038000d145500307030402c4a0140c0c86103601002291590940e5a41c03040440000c000c21107103101031500050041e5010340c51131140801030002026040d071054030300742e558030400131040d40102000d0381c0302c0c080d41202c3c0496075403c2004100765400703034004207040d003220300c00040d4030b808213541442110001c2c01c0013241750317100744028000c03400c2a40f20510300c11a8201640b00e205e15180c446050b5036002d002442c058800400130a0b00701140c0c2d0450300c005102c580c400714044040046c0f442c020311007220090b100300c0c148072502028061081241007980e4060b502c202e000e030b0a01d8207055039020820b2840302144000c200c8040440c048402400300100c20170003402e111011000c0c000c0c05e442068200404501c2e003000704000080007141110640c80c054003944209640d8250210b0040c030389801da50b0b8 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 93431574 1250 93430324 93430327
    0x15090303030405030a0e0f010c020d06020d0e070f080102030c0a1b1502210705161e03050406090506130519090e03040e130302030a140d020703090918050303061c0503 73
    0x42040101c045c2ca0b54403c16510ba40c8224040403c000d561303e19154514040742600d404178025040400d050361019003e2100036280154822850302210910498160f454110981c04e01c8800b224400b580001e10380d1600a50650900031000140da200b030540200c14016440d40d08040c074442c01010544403a0440500f0242c2504804000041e510442050340041840c1e0440081c2c0000300c4802800342c61550b56060611100c03041d4101c80080281d003d64014070208280d04510055034101450b05100e942c8698581d440c01001900000f15500301c0c80c0b26404c10700c1525000f440380c861a10403503030203c4820300a0051605641c2c800c8007984c00203e041400c2039100e00000c00000000e00403101c401000c81c140303030307950b98039444194084100100160420000c403626140306403104c4441c802c284851620b4039040000d0003040341e00c0b00c0705c2100810540036041081410b140314065001094100b605041001941c80b90740724400101094895039070140108a0300001c0e40b181e130402ca901008a9 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 93432824 1250 93431574 93431581
    0x309030b010608090c0406150309050c0301020a020f0f0106050f010c0819090f06020c0a0911120a09060507320705030f0702090601140a080402040e0a0b04120207141509030303 77
    0xf0115681103861107881d10407408140c44908081c49228110303904828502c820017001c41c8120060010307400143c07800d20030070b02030032030b665820301c0100514204c0d80c00800f81000c0140e100c1707040402120286074180d241c044100030b00e40b00c85102601c088002d2809900c03240e500d2402105901848801d48144031079140b061903e241c1201075401980d80140e2412805507035007000701c0c1d0f139102903501107400c500b405200b00038051598021010aa40c00003910b41420b0295400b80084407040b0748580002c0c0c0c4411250082c08140d20400350800c5091800250a10140200d5041d0440442c00ca1a100511907081c1c40d4100132107054580311548641601d9480c004130355002100c0e00070003000d82c45000c034000490002d42c02408403034844800c8658050404010382019202080014000e9810540360b2480204510090040d503000511890300c641d594181400c0c14070000d449500003000b550710415081c0441c8070316012401c8030300011603d8040000f000309007286540140c2c01c40d01d4140c4400f1050 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 93434074 1250 93432824 93432827
    0x1602010e0f0109212703200310021c0e03070203030f1215060304120207080f060a06050928060302040f1b1d22090302030a081e1f05060d02120a0203010305190309030b0106 75
    0x124047c42d000c804440c0b4441c215800311040744100100b8030b404144100790440582e0f41e90300b18144010094003a0390600b51950040b034119030141400c0c040055000401d215500f90440d000380e0019030300e080e01036803926a0800300340d180c440640041d1407200c50103490700c00310380300704047cbd40542942c1d0161890681c0c41625141d41d4141500c3c034562181c10404041182e04051403040e200749031a0300c00402c0c10310201ca500440d01e4401c80710318100d544403d40400035803104d010300752a0081d100800110507d2a42d42003410103d0203151004101d406648201c0180c401088251031840c1215051407a51301c5074404418034500d40c4804625505080018091680200c00f8103290040c5407191101561a2400f607590344034080201ca610504000103d0b80030384009145031000201c003003030100342c60380b03400026800e40c2041c0002104141c0024090048000c0c5030101900814981c00560442d4159a54507450740341c4080c43c500005011103581c014140b0500a440041d034000c560300f03185503100d480 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 93435324 1250 93434074 93434123
    0x20a141803011e05090a03090512010b0301060f030b13170a0207151707020303010e070e0d02041a01030b0a030b070507050312040309030b070c05061602010e0f0109212703 75
    0x3440161900000170810b03503011034455105613055441d14252070a000400264410221900e0015036072119081001e441c00d120302c4018210580508045914502d8900a0003d000780140c1045501c100329400240c1c80d01c440402c52107a907aa040e8440c81d10381e1049180c4175050b0301c200400e4080d40d054821254000e8080c4c1100c2844a08000250b41c3c1e190050b0781d03e100c203214901000c651a0000740c00035104405002d41d440004050742c00c5141e0742c0c1c00060984000400c4414408020980003850b9038140c4618a500c86e826140c002d0b00f80d2a544800a5a0000400f100c09000c0d000407a0400c00c2002c0c0212070200b00c221844c1c07003903801c060034014110b40050004039420340e00c29002c603848074090340c040070071145d1003401041d44d43d82c2e83c40b00400020200700c203103084d03640741c0908c0394400c1410301c44c0706203000b10503000003170f01c80080c28100b0301c0c440482c50420b1118880030900030030640c0500035800d1008440c0c12600c401c10f17110320034107100c48a40e001400740c07680baa556401e003030800078 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 93436574 1250 93435324 93435371
    0x7060603081b03030f0403051305101206230f040204051201060302180402030307120908030705030903100b010503070302070c050a0314011b09060c050106080d09031203020a14180301 80
    0x500b03034150150300b8503140d582c4815105a0a40c600c90400900042d2150008280d050078800c000c0013819a188049001440c0c3c14041d0b1000ca040e1840100201b2018400c00c0002c001200c51101121600200c01c611400c20980003402450001c926981649031601110300400000c0c1694041800202c00d0500130445808228031591150290145050119400ca80526001030145180404c60307603d40480d01e0491007410709001010034001080c841c18070140c104c807401003000c0e66441c4148001c260524414507a41c0901070300e40780020720940d03030107000c0c0c9610040c030f414016611002030030300c2c040e10107003a44401e030300524034480131041100d0005074940620074903009001044071000c1c000e0b88900d040c446540000c4d01701c13904104041c13059060400d4207002d9000094840e44981d2004e08120410f13001c003011801500007082001040308485102e0040c900d000c500302240d001d002006428114042d410b103400105124540f503644554030303e060310008000300f0130018048400f481200c03280 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 93437824 1250 93436574 93436597
    0x12050d21054210120903020a05030a12110408030406080a0609110a021005092d03041202031c020705042a0201050612070513050c07050105010e06090703140a020f0706060308 76
    0x102021803032400c1000210f00c8001d40d03515010240340619039103500505460300160308500c600c038858000304100740010843e0810903030f01d40b80040200c80000040d106101c40c1005505c0040004000d0004044103480a842c0325190211090312000303051009080150014415030b803030300c000f010010f04150020b2a0096294081d40c080d40940c8149900b1644211f628070f041c1d400540c681e40380610204841400045e0b42180c65030300d0404050724a285070001d402c0500d00004808847d000d600d13081040411050b040d0060040ba60742c9544000d40ba21390a125060181b0b40b01d000680944c5040c000b1081c200400c40054010b20300d82410007406001e055441c2030290490078042d140c00c0c0004070314003054a40140040301045601020074000b040000d110500300740c014080c84000500a015141c02401c00c1444200e01d0b0401008001c400240603000405151500380c050b8540c0c0c02c24128a540a02c0100005881d030140303241c1041c0701d00c1810001000b0310f1070b040d408003c000e104006060342c003034007 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 93439074 1250 93437824 93437941
    0x120501080115031514040803070e061305010f050d050901062103080609040804050d0809031204080604020d02121504060b0102030a14030a0207060612050d2105 70
    0xd8400603400c0390303525180309455042c008000c3c8049041403c542d409510414000034010340b001c4801d1301600c6050318200c48081c0b0002c00d0107206640100c0f0803103440000c5400c00d10f08036103087c0311001c00a5601c01c45050000b40d0304400d41e45030144080d9004500302e03013014040340c030300480c115008022501400c034616100324a0b900429408038105540a13a2544034440c1c030361120700422030106001442126183c504200104054840414018210744100d5200f40c46071122400c150404011564140700003e00f4401081020707c0055840d4010303405440503c11000fa40c00400e91240c1035030601ca6291085102c10407604540f40005446030b40135050070448480d0240049840c0c0c440c4800610015003e000711820118802008603006601000d005103030000c20b64680c4140c609951202e031441c01c1e80c030411018404240450603030010a0320b014440c41d08900c1c01e40c130309008841c1d292210690b5410000d00740707120b0b04100d2001d00b000c20903814640c030000802120b100c10507403850002d0ba405d = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 93440324 1250 93439074 93439079
    0x5061c1d0d110d050a051804110a080a0908030403030903020c0a0f14102a02150703030e0c09070309020402041e0602210f07022d100e0d0210020f0706120501 69
    0x2140140c060f03403260342d55a2800e60442d00c1191241c01a910fa084141c40c03d02c1d00110170b603103500c15400c00582c00d2522544074102224003404104000340b101403031500b050075803070004e4207241c1240d522541c075050008039400541400ca1070501009402c6812412510000c102005200d4004049514207480d40440798802c200f44900b0a5a0306103950104100d50301401c481c4029058640c01c552031400340c914031001680004040b80115601e111354804000780c001c05043d414000c1d00e00d83d1004e04000c0080c40b50081c0031840344140146201c040544d2404400c086503940e404480c028842c080041912480e14008180500003610440340075120350180041e182005802e03986c3c402c801505d00d642881c2c0200c00314007a40d404144103e0b0320141c03d00320a042461490074140c00c01103007945000c45107074000184003080e50744a00d00000d118400c8400e904079503484021061050b4180d91041032081d010300e00b07038036200d489200340c40280100072001c20910390115501c02c0e00c980c0042c0601607030343d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 93441574 1250 93440324 93440357
    0x405010605130e060a2007201804080a09030804031109240607020d120905040e0712080c12030c07030909061d1b18030c03030405061c1d0d 61
    0xf150780300391a4907508810b000a06003400703035204880042c0341e08410205008103642d0041e19901070501280c00441864244828a82e88040c1d171016a0090b50380c0c003000c59044010034480b40c001040180a01800128924210310540204005542c0484402d49070307900d170326119048180c0056440d005499003c00180d00302c101126501d140f145c010392000d04094001c080c03011548c00088140e80001130f041815002600744405501d00c0c0902d66140c20045051408200a8071092181c400b1658049101400018500c100449080d54403203100c030f9940800f4030189040011044910240e06404000c02c102010544000e104a0780709a48442005031621440c42c21120719000e200d03001910481245800d500113104e25400580e81001d281e400d030640c12001c4615804411440043e421400c07090107141030800c115a2901d604401450503d030600001c111240a15280e500c41c0401070303c0c0d4420b04005950160020784c10f8505211154400c080000f0751340c0c0800300703120000030b14a005900420 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 93442824 1250 93441574 93441581
    0x12120405060609060d06020306060f041d0702060115080604060f0303080109050c03160c11090c0405090f01121b1d01080c030105070806040b0f120105090d05090105090409080d05040501060513 84
    0x1ea0b0000e0080f040d1802640f641b030020b400c02010310b40c002d501001202c410244000c01b0704000d080744903000b942040e0030680040226030251901080d5840301c401071196982c2c00038421686039491800c030360159110b00010f400b8085540c0a010001d906103804028550301018041c142c8a540348240308646030049504002d00c8200c074000f5000381d41d002e510008601c01c0525410940c05000084803080c450070025145510035285100d40b140001000c000a00340100c0d204d5100e416442c181c0400e602d0590740c00003a006055008009110305c248001624840c442a00041c0c003071091502e206075500c1003460004442800b5002c40c83c030598880c0c2d401807a05003d101c6c810302e11540c4000b41504c2e01000c2c0800341074843c40d03080d440071042080c040e65841761085900600380d42c4c800440d160420b003132100d05240708000d0710300401c1000c01c44202c050360000e0440302007000503200010b00d014141000040c2d4000c40741c400c07400e00c0c1404140400e000d4150441015a50221000306030481020807d2084 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 93444074 1250 93442824 93442831
    0x309170a020604091109030616020f010e0606010c02031e03130b0702010914030c030f01020a090e0702031c060e0703090201030e01090f120e06030702070608010f06080f070212120405060609 83
    0x2c00401c020a0101c0c03203468004402c5002d2114480341800c0d4550300203400d020f01183d5406c9115541e642810f00c4030760411512864400390130081000101c00d06801d9120f4a00819450601c00341e821a074085460400c40704080e010402504a020000702000c80d031246c0c400740c480c0328070840040c0041070224000c0d0884561075816115240000d03d0840d11002d4003c2c2511825850b004040c00e145140d1000d00c607a4404213600c00006030303541e1100c00e003e0802507141e0000d2448020f250204400b5075000000c48003c40030720014203011500110b0304901420300b44e00402e590080ca4028008040c0d01074101e507251a2007600e003070062801d1195000e00f20703505254003030b04403e0041c0402003c2400d21032a07007013400c49440c10014202607000400c0985e442030f1503440060380500c2c1c0400c05c4641c000c0306907000d4621680707400182c034a0810010031914014100504800c0d0398030106003c40d00801141c0500c41081c00485d45070303001c40d54240c800c020300720b4007512140100e4001610500e000c0189912 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 93445324 1250 93444074 93444079
    0x207080d0311122205030403020406090204081203060406030f11100f0e01050f0904060605040801050705070b0f091f02040801050901020f0403080a02120708030a0e06071b020a090501030309170a02 86
    0x10100c071480d03002c0d00400042c4c1166445089031a006060400b0a0ba801c2041d40c0100c004503030351461403041c481100c03107643c4512102e51040c40240b100303c0c0c001c5201161908005095503c0c4d40300c1d0700002c0d000741301aa100a00b0b582d8212094000c200c000d40b211155010121962402c420300002c0c180d8500402130348020020304002507044056010344090121400030700403543c10300e040d00000c02c044911039004000804c0c00070800f044800320900510303910110900e0b0050410103d5035624409e1800a407102c1e44801001c4001200c5107410007014004403840c1c617403071150303d14101c041c0000f9030090180048a5003003a000460a5105008032080795041c1c100c11403802e03146482d5803500b504829000021402000817400d590703040c5002801070603004094181d03403814441502001c03507000c803680f2491500300c2c0301080314650f002a003d401d441400031451b0140a00e0b8400502d030b20001d40c00c00d0011301c3c9007070008000e255000c030801c0291001c401410180340d105d01c402c25600c20b07103002c000390f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 93446574 1250 93445324 93445327
    0x6131b0e160302040f060305010f0b0f0703050313020a0e060f0a0f15021002030106120b030a03080604020306030c04024003060f0608010207060903180b03010b0c19030207080d0311 79
    0x6640761212900c0e00d024074410301e801030030180c9a8544d4040c501040c0d20000019450307030014007100e41c1c810740d010004d1070719541503450070f42038488a003004e0040c441d001d400d0020201c0015042d0000300c014200e001e44c020005501c131a202e5000030421941601c410303004042e042d0000c1224104200c1050a03120346e84003813078810780f41402001c03c40f65110114004c601480603141260000740c0069070107880d0685076648480c0b89a01400105c032651401e052203a4446107408001c41d400c85042a000381c0250750150703030b81d40da45020030f213003a001087c829002440002c41c00c1444101d80c0b402100701544000785a213260709448010700e50007000001d070b5035645000030100000391095110307000c01c6100380e130003041c0c1d00d03900e480560881c0c001d90019140c054580301036908055000d0442c52107010151000a461400c20903010214001402240c8035203030000344032480040204201c0c40040074482c9080031841140c42d00a4584605100b007900b248140300c4038100090003405130190310b100481c40039 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 93447824 1250 93446574 93446581
    0x9020702060d1505090f040318050f1002011b050304120201090302100203040606030c1806050a0b070f080706050c0717070f1209080609010212090a08090105031806131b0e 75
    0x14010404081d0316a400003403d040040c5903103840c0122441a50445551102c510342810050070200119422031441801d0300810310003079441c02c001c0c4c02c180d9401d17282c026856441440990042850b200709185660b00300007490340c81a8460000c41c40307903100303000d00e000c5405007210590903240c030341d940140903030001c0c0180111031429a000d1a842030207050081811035481d22511440c0480d0f402040040d40302c017502082110090180100038002541c90748280780ca400a03503552401070f0310006120007020301c0e03154180440001542c0700340303810601c00c02c19810480844c1019501685045800030a02c00c04000c034100c04030181c80710107420081b481c800c9146a074070701400c0030150a0036418840c103014003003900b51042100a124064003c00140d44885284c60800340d8031000b061200c0c00d600076034030f44000a076490b0999040d5002820400d48a4940d1015203601c8100c240500350b06201d0001041a07000300030400640c403502500a00d6050320f403400300888524220f0107101c100c0300f441c0020 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 93449074 1250 93447824 93447847
    0x10f0203010e011205162c06010e01050d060902160b011d04061d0604140f0703020d121101020a09050a09021204111c21081e0406140a05040c0902070206 67
    0x10035054612805c1607030254142002106084406500400b61810140c41c0025500340f400990015558007150050101e26013017000800d00c50802e00c500303040020114880203040600d4200101030180d01d02d066481d040144544507201c0a940307820b03507080314031000008054820b1003000b008141c06880d40c1c00f2a030b80350b44409001c0c01824509000c80d2418482221f82d0714010f01038140038a10400e844003541ca0511031a515010800b00c03000c62680202d40c00b003005a40d000c0f102103030260700089101e000b0990100544003181f1100e081c50f00ca500019054100da0390003d001026203100b01c2e5005080ca4940c00010100e00440e144441403c0511000c00c011445000e81c1c0d101c01680149440d480290107450310140500d000c40071a03401d4648000341281541c002c0d1810310040300e5203455020341c0b510005100d000314000b100c43e2102c00c1e010000c642400960382144400c04200d180380070300360920500480c0200821602a240140c0e401c0f0080b80d907212600880381c125400426503030400302034500703 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 93450324 1250 93449074 93449099
    0x9010c0201051903060306050a0204060c0b09010b030d0c051009050a031103090d0c0f08060601090311030705060408061b0c0d030b0d05150106080a0b011b05011d030a02010f0203010e01 81
    0x90036030520905026540701c0ca1a1040042014201560049612850352138010142c4801408549100780180004d00807180d005c1904a4001d4004800d007203942c07a4068113600400440750f01c039405000c0e450300751007401e40100d4004504e92203403003110010340c2d02e611000e04503506454000c0640d04190712003030200707214801035000203800f2000d4a20b09003c0c80001b030054030005e2411141d01e4040c4e03030104107c00300000641d0043c414070000d051285058000208002218040109214940800e0002d15142000f0fa0300144c20301074240c0d503541d5102c0001a60b1404119020051899070080140406000c0400d03a5441c2c410b503c02000e010a0ba02c1d804d4003e003901804494204000041c07000c0850402c1010031280c420480b4922500e504101c0b008125000c010041c030000c5080c01052400d41e68002016025503980d440c000355459214a02240581100f10041c56404490585401e070380c00044020607080c00701d034000304064000d00a080069010920604200215640042001403000d80 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 93451574 1250 93450324 93450347
    0x503010308070c09020d0b011403010308040b070f0611040503011a090117030f16020918060403030c020a020306160e04050103080910050c070b13090905060a0b0105040314030309060c0309030901 85
    0x40c0316544641c403050b10004982145004c8240c49447e40d41d4000340356040210580180110398030b140c91036055450310201d503c20391140000d0b035440091118103114181c3c1c840d01e245507200c50f082c00103060042003404650803074080c0d18440d51134240024a02800c0703078080d944a210180c1240066071074103801e000d0391242080480b030307a40005c00c0b21b0b0440c2c2503030f20010f000200a2200f0071254042c03c0c0140308004400400212403800581d80e5011034503800604141d100f54145008258020f10351000c070f0428100c448003c0d0144201801c1c05540419080d07958070b40c1c3d039640c2e160103002d0885002c11041c1d1b00284809880300004110140c042c0c14103c800318680303440c034200b951a109845070303014a0300115174013561a4400c0803078020608580040400001e054010090012180075100c0076100d120103454035200d00da80d00500801070340100300360703001190040c04403140181084941a201e80c81211201ba29004260004030b03058402c00c2528080c034082c80066003405161001074400010b81d2 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 93452824 1250 93451574 93451583
    0x51c061a040e0318090a110f070302211e070212100f0b01080a090c05060703050a0e1503070f090803040303090e090105101a040b0f09041a031f02040509040b10090c050301030807 78
    0x454030170070ba904400340140201c0c40700c1600c040d524422420020b0800e990504845482d855154548100c0a0138406880b0006801200e075482044dc034120100c02d48103500340290408640c6403100c0c00c3c00004144c01c90b603115100d00c1401a1b00040c0c2c0c40300112444948502d010442c80004218030049503444400705a1048105080c095114000521150441c0900301d0005400082d50895164402c0c0c0d05664690292650107043d0b0070401c04e080136000040a403410804601020f8525500c60132142e00100351000640b9503c1d0349a040088c00d56407103010359900703207443c04042108000b0503c41c0c00c3c0320311040411154007504043c42c10240c44001140c0c0c528941c8244404248a1460b00080407090a2401c4107541c0301c000c0b005000c29108601c643d4846008000b1a5421580340421884070000d21045211000c04150924500901450700001c2e001954982040100003148400c07a0081e21494030b1581000d0740c0700000380584180050f510002041440104000340484000d800000e01c078 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 93454074 1250 93452824 93452831
    0x71509020d140d0206060604030308070e04021b011d03030403080405010e070909021002010e06070f0c08030a02070b0c040b090f120609100c0810051c061a040e0318090a 74
    0x503400007080e00c49101000e9520309508402645104010480c00145800c28006400c161078030000280c05406188000303018019186c00041240388200400703030340004020300443d1900f52a5a55004200c01210402c441d580383c00c9440103480c02640e83d0314204054040218a1030b5101d90301150300400161088039030390f407211004459280140300b008043e204c132010000703614041d07004210705171001740326040541e450325050a6440e1000700d4201c0c3d0044560500c00511081c0c0c1b54115103191140c84040c0140c000401030294259041d00200142d07802144d9502c200c0d281c401012442e445a88a030180c000c00070018516142080e640f4940308500042000c813481410801060401c0421a440c0400d40c1000701000403045183c070030396800e510b0314075017140c030b03440e00c0600c6080b000c41a00440e40f01c0c0e05181c2e028200c0e806140c041603020782d844030081c032005480c01c2c90b0080300029a401d01d40702c0c03400e0800041e01c0030b100000ba503840da50034940c41070031103101d00c040c8001d4107400340003c20148c0d02c = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 93455324 1250 93454074 93454091
    0x90d11030409050c0a200d11150906070305060a120b0a0e030307020604060f0b0934020303010f0e07020607030e070f0e040c050111030403120201020d0501120b070e060715 75
    0x24840e00740324100740140700345c2c0c070741052000030304044c00c01d0004000d2040c52842e80b034051000240301b0240c0c0700681480864020016401854003c02c10800e01e00da8050204110380900d000c5002c038042c440944040c0100d40b5075a04110003044e9a010380c001070030b050000b54010030284040c140d00007000034000100d205500c0202410b6510890704403001d80c0c030000c20b010030411107101b5600840002c000030400b1300318040004070004405840220303081201d4156540b800d610310721403441c840c0c0401d000e496260a002c00651030340c00c02d00c1525031500e440b0400003040060403a00c18807825655000e001c250b03548040a4008000242c9006a5403040b88008110b01000301c0a190240446285c04030305071038a894242003604040c0c00c0f840c10804a9404408140000410307107056990103100140d0b2000f00d8a4100e009010b0003d5503a911800d01d0000911f01710a07040703a01d040d80c02804104c00381c3e40c580c2003d65802c4c0300b02c02d900c1c0d0010740400400011031155841d000c141d50080002103010403 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 93456574 1250 93455324 93455339
    0xc080a1b030201050603151306020c10060611060702010203040c05040203040f020a062a02060301060c111c03121104060e060705070e18010606120509150a0608070e090d110304 77
    0x80c0e405422070161303550f0410702102e46000c000b10069406103980041062402c104009440054900b0041c400764020031074071001d510504c400c2e521050400313010010700c2d07904d0400030300c0351524000c0740c0c00700d0246c000440c010728418003c42c2c3c8200c5d04800581e0745145800244030003584010300990702d007102105480011707581c18030050004c0c15140e40340e441c0707100c0140a01e0b50031001c0301c480d2107040c044118010016100d034010b0740c0c11110300e400c002160b590141022216540301020659004a85082e4070441c0c0070b501d246000954041d54a08181039a42060174040b03070300746d42521002005c24041040558451499070900d100b000d130440b4140100c0c0c0c1d540928161054002c401e01640399010809260b1003140509051140040280591803600f50007a010001600c181228aa03d4000080e01004200705503084142401031180991038815200c40082c40c090181c0c08560203200c50008400080c54101030184001c2d6014150402c0003260555201c202c54030004c615000900002428a = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 93457824 1250 93456574 93456617
    0xc020d021002010507030c0c02030a020f1816030b030313031509051615090f06030b0d050a03080a060501020c010e0405101509080709020301180c0905030a0c030203010608060402010c080a 82
    0x1c03400b034001141c641418000075099621801e03018042044860a150150750002660070050350142c3d544181c0eaa000c0c40811610080102c1e48003400300d07141d048c0104082200c05241e10048903540c104080c0004404140c1c481c40790020400b400d00e1036000074004100c031b0403824188400241c00c0054984000d0362164106000382d1890900229900d00030082a403d0700d4154805001528260420034108014007184420500510042550f6514000d41d20f8540c00d040342100750b0000100c80d00c10800e45001003d1100c1200d0b0300d0201402c02000046a50001403034100a1005031100c8080e01d100e0b03400d000051000a0071042c0ca02c014000028110903c0302a246c00a00c1542da40c1c0b42039810124810701c2d00c012944064a0380744100010040c072522070316240b103e4074942c0004111031320041011034a060311900819458024528400200520b40b001c0d801124402d0700280401e6580d0b0350120780b641022540a4017080c0d0441207140081d001d40000c0003000403a041c414a5a00001c1301680407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 93459074 1250 93457824 93457849
    0xf03010e1501050405010b030a0c14040b09190b040e04050703020a060503090d0e0f24030705070c080a05030a05070317040c0905090106080d0e06070206070c06140a0203040302010c020d02 82
    0x90700407a054410081c8500191030141000307503010300545d4581140001079200040c40950b03031554aa04105160780f044107980310b07402c070424030262030356151a08040181e00010090344107864001601e01c5060401604504544c030195540d41000d10b0a03050746150f280061045866000304000800180d8402400700050242d07582d415459284c4407a103140b400c001000b120091005100caa0811641c49a800f410000c40136038001c1840744025081c00341c4c1c1e000c071526151101001004000c0001da02502a0105034041e03e040503919a403000b40750b840f04009240940711790001c0110080d5603004230300404541d4441d28221506005800d13444040030416a1b00311241200c510042041c2c12641c0103940d0455400c3c0000c104051410820b40c0d03542d0f40031405001884041180303001c003959842c05442400382c02a1800c1e582d040e03249002c0204020501852011a10085410038429550004d8460a0007140c00441c44d0a06603001540e070143c2e06107080360310018018100c001a141d69000828 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 93460324 1250 93459074 93459101
    0xb0901080105041712010b071a01080c03070e0f0705070c1a0904050601030c090e07020c0406140102060f010e04020d06060314070501110c06030406020904020705030a0c0b06090c030a0b0f0301 84
    0x4840c2001d00e00f04e480e0851504040c01044800e00c80903000c902039440090441c1da050b056141e40c3d9000d450200807150030340504001e4020039100014407484085507043c0c4100d000c0f03055501c0d180e11800180f6a12105490b0200c0786541c0000149106000710020940c0034003171003151050690700d80030360306101856110380881c1403010402584c2801c26029442c1c2221003404c09114000c906040100320008510134000284507000118254074001e02c803a801e444406441071003410744400c24240c04146821000f8018450680001c00b000f040c140f01c581600c1000c0c1d000c2100d47c40b19000c101c025403403c64180e6106589074800000541d5170640c1c0d000041c010009030480c2450320001602041e903090500403d0b400c42c0703c85201e80c1c5e0318407003201e9101c0c3c1c0c03103540140c03286040c401040085c02083c00003401c610000819902c02078101d4545031900e840303030011000c50343e0b4440510020800643c0d1940c0b1800082c00480d01e0464140c0221943e010003400c07091a401d92500041e00755803c0340391415 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 93461574 1250 93460324 93460331
    0x20403050a080a030b040c0f0c03030e0111072a06030e1002120901050106050f2203050f0f0708010b0a09020a030b22180521040515030712090203030406030f0b09010801 74
    0x100f54036054081d900481404480410011307104090140c030341365440108400700100030740180704060203035018191102090008021032040c240d044ca0b2194003c9070181c42850440780c00e08075505075071300c2038610709a11802034400b445c9881c1050f0050608800003004500815850456038509c500c0641091b0030800314011150800c15041401c60b070341030b00003104000c2d081081c0054060790768110750705002080800300c0300701c00c420000050300407070b9000107111303020310090100c98580c000343c030950003030403081070b1100b0a950f1000c0c94200d6025594060f00500390070400c00507001264040e08080b041404e0100e8808071450009804002c200654040e0720105140183d03100751034406e0f020081c158078051003c0242c1e0784c440c00d80d80d503840403600644100451f0403442c0001c000c030580e401008080d08560300001c444885008a410480c1e0f000300086188458400c641051302860380f403950003030099840c01d030500700104c02401408202401c0c0640301e03002c403d1103841c0c03501000d009081120000 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 93462824 1250 93461574 93461587
    0xf0c080307080403120b0303180a030611120a14040201050304030302090d0302240c09092d040b090604022d130b1005040803031306180b0f061509090901020403050a08 73
    0x1707010321080b50000c1c14032501d00f07006e80b209620b0000c12220840e80c0c9511071800e04000800140071007016400050026081140380e0f0024000c0002400d0060218040b000007952249c030000210745244800e01c0050114801140140d4001d400543d0007078003900d00540342011201c0451038131002002c044006922460b03111070030003a000010340590300105520340c2241846984124213010389101d0a201d4285d500200d072444811a01007a0300320701c00302181880031000306040e10074820484003943c00f21194800a0040e80d00813031118421607000300301c4418041c040b5000c2440b080e1803031007003c4000c0725070803c030400c1c0e48040c0c68004603500c43d1008a0780d17940010030300c072841010b8000b000c2801428041804510000f0041d40e0f07100c4947d4110400c0d190032400c180025001d02001c03425164842280c100502811040340d611884115100c04000c0c1c030740e4014421110030b860074a002c0400280130701541032502d0303c007860300b2507015030015007041c0d01c1c0c2c4c86a904010740440201c4240d100000e42 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 93464074 1250 93462824 93462827
    0x80a0c091a0102210c0a0b01050a050a03020108070e190305030304060608010203040f03030f0b04060e0412081e040c05090106020319030b0109120f080d06051201020405010c02010f0c080307080403 86
    0x507000c68080e24240e0149110302440080e42d00d414000c07801403440326030104003108124200588901c803188208036081080c4d075007041c45056500f8080c041c0149440d070b502140a0602d80d003030b40d0032a0341c1a52400320350b0381c624008842442103204c050380d10010111114424001032141c12002d940038102030743e601d040500d08242101d965901c060b000b03900501c2000041100e0fa00d01c982d43c250981004240281d90000400040c0f44e0146015031042c64090301260500e00030501c54031a40c46064103248004401761300b6600d082049a55034a448011a000d10700703d4855000d0b45c2e0010f100707604032100700b5140d0b000604d850b00c00360056130041c0d202140484000d081c0900e400c04103292400d04000840355480024508403030b600409200d044058804420016503402c00703d142a04a03207496242c10050700d54030040c090501c100e9118240341940c2030307200e10040c400c0300c007103d05c161241d04e1803440039401541d400313221610314001d00900c01c250001003030051000f0741c42408556500759151078140350 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 93465324 1250 93464074 93464081
    0x50c010b041a210d08040309090614040b0906090606090111030a0323070f030b1210050105040c090b0723010c23120c0d06080f01050a06170a0201120204080a0c09 71
    0x10b124070b5240c2c0203c0d0a80e04180d01068081c030803042132400200e103030f40d00d00b8242d8140413958400c1c04000e01d003000014185c0701e5035181e00e50f090000c650600c241c100b40c00c10090040003e403021a030003030b18040410450f1030040002c0181c100181081078087d0203072420b5a042d60005064a030119460750100038039001c540c8040032100d04100108071180c2401c2e031000b040080562035000c2490b03501c0d4507144844c2e42c0c1c80c03400517200c1030b030707000b1104051480100500500802c0c8a40381c0503a082c12680301101c0d00071ba0710101a1016111581d040035010303151713010301c40d10702c2110002c80ba205600d020b020010a0083d440c00003010303101d45812003004295010682500054a20401001e0001000100210b400396402044201c40030780c0f183c00d00c200b188020622035101d86118400d6000d00f03038880c001034010341d20031000700380108120341d03807039202e4031409200741d07440c00c4160818000b160040d030140d90071841c4405406001400c00d511072103410314040710344100b615560a504401c2100362070745e00 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 93466574 1250 93465324 93465349
    0x4050f060907020a03020d1b0b07030c0801050301180803070c0803040605010f0603050c090f0312070605090d030603050604030f09090204060203031503031303020d0218070f0e0603010f06050c010b041a 88
    0x3c0200981c169684009448204904c18402000302012003090790001101030070714140d8100c103418a00c0d06081c50050020306448045101146590000103060714040c458481045074080584840100c26910440140e1008140c80d00344001256940041035683c0c0103544960b10441000403d54140880211402010390000081504100c10400c0603035880f01039403c88072050710751288800031400003d092602c103900404451001052104c107100c03194110a000342940010f0303070768507040c0310350071400e40300c1c03d000c09043d40d4000c0300030074000703842240091250440c5281c401200341d20f680103a016a4480e90101005a0010050101d4154610105400070a0460003540342102c1e1071031008002e0b08912019115000d402c0441d015511030000b00c030344815101e038504186150480c40540008103084040c00020314116440615080c1030040340d043c6c40060b000002840e1400c00c00310b030326501500c0c1c0803685540310740b450001621a40030300c0124980c684070090010b40c03110148256100c850 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 93467824 1250 93466574 93466577
    0x70329040f05060a1e051509070c06060b0901090b13080307060c0e010c0b0105040207020630011211040b030102071407380c070e0108030d050c09030606041a04050f060907 75
    0x1c0020006165170001c114001071031020115450303a44081c2d101d4103400a903145604003190b901041400369006918800c0244203040c2041060744071000d04680d80500703103015002c1a41c65109000d00031604002c1c00c9021034689280240c903441e8807080d41950000c42d011249503856040d04030055401c110034100400c0286041c60010312280c5409100074818072910f4065070b8001525010b5444040807500c0d02e2804e580024510b240c80210b520140b0041e141180d40b8000c0400040344111603426003c05603604aa9113481d40d40c800750421008202e40e50f00141c0c517650030802c000010f032544c0c00310311001d5034000c05000068a00003a14002074040c41e901034002c225182125000c0500c519810706000034144030585800050032094640002c6812414808060b0400010b011308000002c0000c2d40c0754403020702881e210743c080304a00340100512154150003800015045061950015241241c503500010741c0d0940c0402041c02c07610705541d8400440c107044100704890030420621074008195 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 93469074 1250 93467824 93467831
    0x709060503011e0e0a02180a050108030703120c110114011503060f09090f05120c011a01020d12110c01020d060608062202070c080a020108070e0102070329040f05060a 73
    0x500d19006030a42d030941e40183c41e0740e0380d484020444000304100311010f503020340b4400300300c1a118800346410300215040d4001c107061030001303e944440407064507056030f41511002d103464111454000541440e1407000100b00f0901101150340380240107524401c48461035041595061554000c01442c2e0b4400c42c105250a180c8108200f100381c1d10030100f01c941c2c101d40010044070a00d003650950300c26620240c8648aa02103d45044085c80700910445c42c9000080103458419411850a01d00c20742500380507030002149480200c3c01007644165812040c4000524441c1c401d09480300d40d040721908040d80d83d070102c7c00e24202e184610504002c3c05107414000868038055000072410341100141c0d800780c18240d900a420f503600c0c1d8042d0707542c40b588044120b120980740c204040c1d561f021030364180c0c0001d0020001c240c0c0b540c01407003807100c1150103a0281c403680d400c50712502d11040e007400e0a1442c41400d0080030180550319000075000d04d01c507460600e0340502d242040307803038114050011800f4615 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 93470324 1250 93469074 93469091
    0x903060f0709060513120308010833060d0506090a020102060603010501030503041205070509131112100e0f0105010b0910090e011512090303020d06090b06030a0b12030705070906050301 81
    0x80015850085400703616041d55204a80380440c000282c80d40d00c03103800c900b00030300c0c6e1008164000f1000750503a8145002c5808010040052244400c14111a003010070800101c405000320320f00d48050348000050034148101516070382c0c16103029000ca601030345a4124a811500319079043c08440d400c100114024000d550543d195242c507031285104154540d14200a117100708001441090002d201c000d0a0300003600d410354401e012803c102d041164182c409070001d00c52450324003080300ea20b191500040030329000c0c2000c3c0c14010040c2c1416603815115a1401c2c01900710b00740950390107000000505500c0301d00303000500096882100602d802d010b5440414405500c1c1e002030307141119100c0550004251807940c01b034400c00112888510010b0904030034209264054005050b840b6000d01c3c2001810740d5004550210b840180c81c1d80e41c4040c003000400c0144641da000080003013002031001d92410034421030589180d1000200300c4068200705000c0007404d81c5441054002e00f03007540240540017 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 93471574 1250 93470324 93470327
    0x1503060604151707030b0f01050a0c11040e070b04050f100f0c15020d060302011806020a02090a140702010509060105090f0403030c030f0c0504091b1205070c020d03050903060f07 78
    0x518002c0c40000c400550201c0d5025104a06810150181e61003004060401d00d5000f400b404100e588503005020780d01e05006a54400da0885030490003550390b10721504003580d15218646104100580d00903201c0d4081601120103022541c020484581c9441c0c0e1980b402c41400860800d0284243c402c0f003401d00c071101016080740002040d204949088140100c0e540380c03000e40c01a1850f8960001071011400d030340015a158000d10540e4003d803181c0780c84e210082e24030200c80e105805110010380004c4912401418600304054000308000300110340e88035004000c058000302258081c1c0142c0d100c406016203148240b01840c054023007612039194510340b2842c010340c4070a0282006041580d40c46031400c03228802c1e842115000c0902c2024050314400b81c9005000b600503001d0418141c2c07606602c0705110b101c010b400e03d00000b5607141d2002581c007050911000b0b01000708103a09101c10224110b0050b80c4240c403549030144203496071502c9009110a162130520001d00300003c0000410070f024015 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 93472824 1250 93471574 93471577
    0x7030501030b0c070f0803070804140d0203121009090b011d010501050708070c1e03020406080c03070b1b03040e0a0509010e0c12010b0d06020a020f0307020f060702030c090c0915030606 81
    0x80f140b900305540d648002c2c60700491081081c100074141001c04410300104ca03a004a040c0e0003a07010741c14a041c05684e03062843e03240d8079841584030151384200014100500b482c508254080c80049102409a40d0341c00c20f0300075a03106450455440e4034000c014441001c0c28400c401c0607802c0d0014a0450358146000603200d8410b84402070201c04010600104012961084001a18602103150749000b0003e685074003104560004170300c19402d080022a40b0500002c8900349010010020025285001e44240c00f039400a0300c03001c00c04224a0300726040140c204028401011844201501868419802011140f01818020069052940d0410031400001e10125281402c44100c840605505011801001403055103030700020813400101c10300050350301604641c078440d02928180f62020f060aa01c9104154000f540000551105401350904102500502e48041d0031203104442d00303000108040c4040318480f41c00c9400041000c49418030342d011030412101159000d0035410b00000250b800d = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 93474074 1250 93472824 93472831
    0x3040501080c0c100507110a0b0105061c020f180609090402010e27041b15030203150303072a0b0405040b010c0b07110607140304110a090c03050a0507030501030b 71
    0x40181e001d0200b5603181203502142d085000403002c450030940300710f450f8800b80030f0464100b0017041503184c0c214242c2c6400304032602c0c0035502840002070350782460100f01d05a0401c613400040c1525900300b00e22581940d20040c01c0e552241d0719000d845040070001c181c0d03600401c101d054012038051082ca88540c80b03100f103045d045542400c0003048203000b1130104044520a1a81740c2c492035068440d8039a01200c415110b0080f4000d030391094129203401040c145040051150310811301600b480301d16100d1081e0f02071500101202101000c81400300300080c59900112002c2d291b05078800c449c0801c40310041c400c501e02040c00300034282081e1800380202520b0189101d0a0700807500d6410250342d980c032a401c1c0800b802d03400f29605c001c904000c00010441c0c8251007481c04948038010210b00514055400c103200480c1100c40c0c54616a241d560361024815001c0170b41c1d410103a40040410351600394002c40c29a40b1b05503800103428035240000ca016500090003000c2414540001400400c0d50b10210750392 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 93475324 1250 93474074 93474077
    0x10060306031203090204020c01150e0f010503030301120206070f030f120b010504121403070b0f01090204050d020f0f060d09050c10020c060c0a06020409020a030e0d0e0d0f02030a030201050f1803040501 88
    0x5107201c2030700104010340310300000705c1029441d10031a2031080c2d500502b0f46095511004c0f00032156a55500070580c007200c2030045c1c5030b05500034001081582b0030f401000c10020700c00360595050044a40d100d9000c40b000c0b440840c00304003e01e4041d0640c039400429003601c11507c410503c640031900b00044d0480c4694012682c25200240e0800144240c058201800241da00201d998901d040e090616200000b603401c082151404000000d281d801c0c0c1c000d403003c4d681c000f0307c103410100300317030b0b08001036070450b80e2105402c440c0c08800134a072542c400d00a040d41189201d00403074503581c0e514040b800c084400160b41d02c00d80310309001060566001641595510007602c1c415900c030030080c002d40c9070440c5118000c06042c000a4041526100f903009000068401e4400740701300c4180366074a540781c2c254a0100f400060802c25a0b404601d001107035a0405e0380506a510030400c055008a401c04942da03e0580140c2c2d101c40c03c1c415860031201800ba0710554003d03a4102420700100c0c515100d1150f48101e030b0 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 93476574 1250 93475324 93475331
    0xa020a140a0305060106021e010903080a09240c030e0105041a071103070c0e0705090f090604060b030901020304030f0203040315110d0f05040c120c09091106030f10060306031203 78
    0x50664a400159001542c3c00c04112140307503a40310070081d03030f481e035507005070505202809903e0501d2105008001410707505850781d0105680700c485e0702004280081c816110312110a400c10007031310303d00f0a004030100340e142c004600413204010150a45414a07295080d507854403040002040d4000352134001c2c480325041c19040390321919030480300c03080c3e003101c503200f180000100c0d94200716441041e08101da008042c07828083d88d500e441500e450160018083e042044542c0c00702c02460f10440f03065122000400c00981a61260300c1603000d03400854030070701169400000c0c0000d2640003d034007001175041d44021840c10341960b6501c51543d900e0040d54050985980190f0742d003106400c00c0d075821007407071001080030034822034000004d00020b0700c055505403062034000c14a0044032540302c0d48250040c40c1691124500b0000e01e00405103440c09541c00c40342091010020381d12200214080c050240441540d410000100030b0404001d0b4005030505180c950208005104c03000304842c818003509000 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 93477824 1250 93476574 93476609
    0xb0103060f0e12030a060e09030d0905070f09050a11040602031204020a0312020d031a010e150d0501032d330e0f070b090306011503020d110d0e0a020a 66
    0x980160a108044040b203001c0ea4030400c40308040718001d144100e0810800b40a0345940703004e152600300d03050f2103007846600304004080000c202c0744c2100140c82e100d276007254000d90355401d0700200312166420021750251100300b486504501409440d40c0c11020040e803a14040c40c0045c0603681e48a40041d440924003000001429076845003424402180c000e910899100403c4ea4000d4441120b8039001c800b03c5d00e0803090320b506009140600f00410810703161124131400d403100300319101c1440e901c010074107001001003030030038106802098020343c403500c1085003640d8041e04519000309490341001c950600011100702107101ca07050b44c8003041c111030f12110030402502c41c082d40c17120680b00156203641008411320100c00005901c10354408143c0c15101980d455400c0812584550200e05600d680900010300204002b01340c40b500d48542824014070307000003183c040341580c0c1d04c600d9003251f0303101c0403035551010306e214041c480b21010804080c0070405166400140c2c8031007280150b07140042c41d070406 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 93479074 1250 93477824 93477851
    0x25030b090307080f1903060b030c0c0f03040b070209010815010909020d02190807050306061f020a061a01080106030510060806040b0d0605090706090f05100e060c0a021504030b010306 80
    0x22500303140e803c5240c00e5901c140c003100028403070380220b28010101203900030130844107101e807250100b95030b451881646103454207810201241c1011043c0c00140c01694080300d010360080000300010074144180c140c451015004022080b40140e02568080e0000d41d101d0000c40704241c00b885c15501281c100085007152400820500006170703000a402c400c141c00c69171007002c2c10004d00d400311500c42c41102c00e419200c909158a03a5001c0d01c2e0316800501c540c002c0780e10b5242d104940b8012424031720440e007100243d44c13540c5003640c10600d079107c480e1002519072401c41d640005120302402c143e003000c1c0810306217000c02000c03a026510820042140b1030020550303a544941002c501c001004102425074000d40c10314100400080c0c0c3c25512902c00c01c000080c0c0c007401048884200c1e10103203500da030658a07050902c0140740042c0107c80c20041000c80344a41943d5144c054100e00c91010010641c1103100d1040c88941c2c1c0085200714405c0ca001d00042001030500d40869054075031042000c038505820605 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 93480324 1250 93479074 93479077
    0x30306130e06040606050406140303070f020d020a030b04170a050d09020a12111c02060d1505100e01020601060318060b0f030a0503190914010e030a08030a060825030b0903 75
    0x280c18030380d80546403e0100f0b000c25500070000f46e8070125410024a40c0d40d03480c14103561003481c41142c00d07400c00c2c40203101055080c10342000050010b0f05070078600740035900045649102c3c0d002110000c00110902003403100d0201c0741c9000da10314090b03a614046d0426170141c254010348619001c1561184100c07030854840300021402485c0c40c628542081c0500d18020101890800001e4055248008080750b0341241ca100440c04035000707000d891501000a442002408840318803498000075040c00182a88a115240c2981c21066403a03005c03801c110000281007280607030050f401c050400b44a864091001d1a0420210fa8881030003d000491203000c9a5a00c1950b030015915008400001c401d100d8044020028840000700302c9181258598041c0d4502a4500989140c0c2c05a0100300707180d54020a06481126070040c126045041ea0340c0d5007000c0d6038030490300c40f019140c5a8800b080101010005855000b0084413004228a90121010900036503840b01802100c11040460f59403c004d20 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 93481574 1250 93480324 93480341
    0x52a04020c100f200a0c140a150606031b02030a0f110a080403050d05030405100e01021903150914060f0a08030703031a0409020a06080c0903060f04061d03030613 71
    0xb802480700c122407000d02c200074040d4a14802804440c080d0007094051078504664643c80c0c651203d03c0c07071500980b1243c0c01c02951000354200351203207a1400010a070401c02c41e4140940080010660138188070000303050321a139180030031800c0c0181d020380d19070725001300944000b070040b4a0980c804200c40c41040300c03400244204030300303280030f01040030050110000082099074010030840d07502184180040720f05110840e400340241d000304226000f8121241c00c03802c85020b1400001d4207102c00c20080d02d405100c91280c400229588010f1310028400311541c1000502c4056070401c41c0700c4441050704008034004103140d108900d00c1070300001c142d0320034920101401a032412a900c0b41034926010300100360200d40c40c80082103002c4c00c0d145910b8140212034000e5400741c030342c242d001d203800d038260380c40c050150104c07000a0052050300c1064808101c5070313101c0c0464000e00311f0b0905140c02d01c40100c03590b01002412892592841080148000081b260020401d5880c0c031040d40114261000070012103 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 93482824 1250 93481574 93481603
    0xc030902090115020f0304030f060c0c080c01050702060702010e0309040b0105040e090d030f0c17180307030306050405090f0703120c060f0e010e0c0a0303050310051507052a04020c 79
    0x8900105028400c0030f042e4503c07201680803540e9824951070340e42c5d641d0003640b02c0144800d80804280300040c030190005030880140382000e41a0b20807075640c0c42466084545c046103103a540d00e0800580c1503040000b5130304400c00d80020032001a03a4003003039480c0c2c030412417858011500ca155078481c1b070348503504840040c045509540010304046448a4035400140031007000641000390141c032220480c4035006c040a41038481d42502480819803035940040108490398004c42a5550003d20806000a00c07010780300388d400140c0142440200400c40d00c002d0510744076640800e0400e1510000000c00c40300341d0b40c000031802200b003615401103c007030b0700d1240300500e050300340880304140e1100c0b904541b400760345410080c01088040f01d10165205082402c4c00d80c040500001080032078084c000454104602d254251111a21080400c030311802d07540d0403070b8074150009030010501c40280100031076200511410f1020b0f056255508440c01c28803820284190b500007190708007240100548078160109 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 93484074 1250 93482824 93482839
    0x1406160803010326071103010f020c01060503120403080405010804050a29070c080301051507060e0607110a050c04050910090309090c0806031023012304020712030c030902 75
    0x500d00502039820070b1008607411080484510a060002180c000e180c070000041281004410786480d22000c0c0070200060f095562600314545035a424001040285c0980e000460520b00d0301c1c00f854a0701c0a4070103c615116001d10003400024400011113044420919000c0c5c856103a03410880c0c1480c4907002d0082000312017101d40c02c50501008208c0001300345a000c18512907441401c01d84010840d880d00809200041005104616102500c20514101540e0300d0b41090056a280300444205170b481d0000b5600000c00c001c011380d4406a6421245210000f0b40300ca100180d841a90b503030b10300f40010344100e86600009079504000c0200380c4d00800409130a0143c0007160130302404991950044500050805186418443c054500340d0b00990b0080d008180d407201c0341d07040da0001c00c1d428240003601c95802c0014034001c800a032006000e8000c01c640800400d0303060341e180d140d00a8140615010b0382c0144420400b01c0d1004501c000d19004505010800c10f0101d17004400801407100f000b0740c480c00 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 93485324 1250 93484074 93484117
    0xe0c01050a1223010b03070c12020a050708030c0c0a1802030c090d0b011401050c0606091e0c040501021605060315130f05040c0f030203060403050a0212030106020d0206060103151406 80
    0x4070150700c1070200d00000d508029a40c89100d00c040c11b200c119514004a030486e0300383c80014400030381f0184410140e2041e1402424079907102802c0030000c0c1d210207030541c00071480e00480309003405003055010080350403100031841d14404e400c001d000302c1c86c4d1301c1e811039000c00001c1c030891018048444810740148800d14150851602d108112400e00601102c0001d000010080c0e5008a00f111030607070100004001c40d80d1044200051804020008590201406503180c16040690000c600a10300c8070300f0f4907100c6043c90002458070036004000c88803021161010031541e01c407001121340007041d01100341c082c101940302243c5288040000240300915101148984940643c0102d00a030700c178030041d08500d41c2d200c80c401c074110030758080658550000320210700042d00940c0100708480c0c807030060b102001090083d40d62190800d9000b1340c0980c00c43d00344030145640c103000c0d4662000c42424108010030740c4103101030820000340140c44442c2581e40d1140256a602400ea17007045a40442d450f1000c00e = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 93486574 1250 93485324 93485351
    0x9100e031b01150905090307110612010e0403080708101202150c03131202030706050a11071401080708220503070f030c140a0b0403030b01030e060f07120e0c01050a12 73
    0x185012640c842d43c0b40d01102050856503401500e010320b00c0c600c0214104100f40e1500e2401d2004000440ea1000e000c100f610314140030158064020070150a80ba060b43c54507040140c9420001410b01c0c040120100070046031200c40d00e044c0b01a5814039601005900b40c42c80458040b21854550400900d40810100e1502600000400c0780d07c41d0f00e280102c245913036825041f10343c0420728000b581908041c50030b004083c030600c0640034452040c58a80d41e106c4625210b64202600c64100f0a1a42204d00400485503001010540c00803240d1500326000c0c5401c1200b1089030201002c48511228907200445c00e120080041d030310610b40001c10113002080c2d51a01502c0f90300d484404079071800300664441062200805c281501d1900102c08094950311b40e40d04400901401d516a414183e0742d0038200b4510700304100f136510a424200d4103101b1401c1c52140600900800500381090a0030082c02d54000e150208041552000a0074450740b125551001507031001ba0301848142081c0c90000340350b2605 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 93487824 1250 93486574 93486581
    0x110d0e0304060906020f061308041a091017011403010213080303060a08070b07030e0a08010219080114010912081603020307030e010503060f090a230a0c0809100e031b01 74
    0x19000c1c3d8469a04081d078030b06003aa00c400c0d450300300248070341019000660707400096155814480c40b0381d401c5841c0540f80d50071406401514001c0038100540400c1551a81c00c02811202001d8070380d0408510740c6082d80707040240e841c01405008120401c00714134840e1500c007501591990310140414015a07030b100c0300c0895a80d0030844090380f14861340c1c48000791800b4085400700c150f4100350304451402407181c50070703250040020b82c89034109280c4800028090401c0c40500304041c541d80141c102d01c000c1920041c50040d041c2c0090540411041010040307a0300b00c504c000c01c840500980865080c42803d20b80080d00030310490700c8450405001c0a020558040018070400384280c552078003070500382c80112032a0000f1592103030007500300d5245482a240010815a0001ca00000071a101500c280c500300810003c0385070035458bd20000620181c40203d01a042d146c640c0c40c502a0058500207001560f40c010743e128081c095a90707448005690031050080300c882c10b100c2c4c10f0403e60507000500b0503008 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 93489074 1250 93487824 93487829
    0x3100603030e0a09090c27020f0a031505031f0b030a23070e04080c100f09050106080607050313330b010e150d090b010e07020712020a09110d0e0304 65
    0x61080c10f0f90110712644030348100480c0540002c5840c1082c0d0400d07c1e40c0d00100307051003000500742210000140700451364001400302e90405100d558845101140240030360b2102000059142d10105040c0203a07200010a812228112800020000e0160482c2c030010401c0344c05054060140c0c0a104040c450690405001c04400e4980e00e00d10007880c842540e00d9161340d0141d12400001c10000c10003146010010f841e1084220081c1c0300c0c0d54450b5000841207400740c3d2050360718192100c0410052240a04c100802803426402510322403400c55802845403100604510070383ca525004003043c415000d0b040a94203039030750710607030404d03100386014010390088002000055040107443c03001540701d5225400002d0000e404003803032028a480c801215004114500100c0b580e800408010a00c00c0300c02034001c0444d00034038011410403600081c1440a80e0700017140c2240d0702174401d40181c480c108200d044940320300c400209061800000601d903c9000ba2600c0c02c03d0506450441510303000c8020000c = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 93490324 1250 93489074 93489079
    0xc0b03090609061e16111b0a0b191b05012a0c0b0a0507021908180a1d070306090c020c033a031b02070303020d0804020d020d0203100603030e 62
    0x100d07540d860040c2203a03000d210311840740313041d10314003080b5841c42e41540f1071008030640c1421074101188041452400007100316003940b605412007502900c0c01c140d041c2c0d101501407a4a624905900640e0110112005003042e4013004448811203c04d043c45410000d40b555008009008003403201400802500d204101e864500b4001400781c42d919000b00b802c20b50700760744202c1c154055a613100d1031000404006001d207080d406141c0c1d0803800766411a00000c2105d200b01c09041c2c0320310503451110030190f0007003503250190f00e5140d0b05114201a0040d0301c080c41d04011000082c0d643c90030011800b910a552000d03401d20b01380030b400360340c807a0082154101c040c001d50489000c0710b0070103070b9440160488042862898120400b03414010003581c0c0d400d9400e145400d0100c4d80207185c2c1045c0800d4123200740c0030070040e00310180a0041541c14001070f4620841c92a04031654245a0000707400b035440b1520003446204201002400c6440900090380440b860031030400000e640e90030f0141c100c0340302251551 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 93491574 1250 93490324 93490333
    0x103030513050406060c02040506040f09080301030c080d050d020c07030b040609060b01050f18120a030807120501061e02070e2d100e0c0f0d0608010f11160c0b03090609 74
    0x51600f003034800c150849000e0360b22007491078200c0c0c00303000061502400740d94105880f240d02c0810145140035039628181708813100ca03925851400d00e05111201504000001d41041d24600e800550110030b5600e2002e40794001a5280421201c5500c0d06100307a000500422415041105000c0d15510810200340602c909000e40040d0200442ea148540f100c9107510036802d00c21102112011f1300c13030703401140e409010715260020203401140b070031010a42c00c03000554510200b0038199071000190120100401080c001541030200240c03404064004d0300c2600300c0b04060301d001881c800c00040b0010315051891450508200350001e007000c10138204c00540c0c9036a900003810088a845440b07202d80e10154001031200c0c200349400903003110152001c0c100c00b0007404900440d01c804001011241468040003031501c1c509424103003034540d40f03060142010f1130001d0070400006600f0498074941c8010501c0f0701907401915200e030700340901d50801850041d001c02082504c10000640781d015041c2c800859 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 93492824 1250 93491574 93491579
    0xa0e0d110c010c031209020a24020d021f022206020c04060506030f060d080d0c0201020304061419050a110d02071a090c01050a0c020405040c05190806010b0304050a0b0103030513 78
    0x41d02c5024010310004d0010707010102101c65651a030344451401c510041242241903075815501803c00c030011540007100886a00c0314144540410804d0001c1200340050040508140012002c681300801150f02c55500000c2c94440c502404004002d52290441034416081d16850025070742c0d00c4d50b003141c034002c1e4903025000c2007915150f410340703201c2c4032103ea0021550340c0c0c40c02071050503010b1000403102c420043c401c60f02605c0d4240100c2c8000c0e5010741c00144c8914160030302c0002d0381c800154035800a2803c0080c000d0000108041000c44400480c01044e65101c1c056028010709501850400142010940d070402c2c511a4000703001150288650524103090580d8170305034182d09440d00c40350740d40b08140c140c42a5000300082d00c40720340b042c00d00960b900000c0c1c001c2029244101c0f001c540d03001040c041400646007411150b05c50300704440015142c6420102540d68840381030040740451a070110000703041000802c400344403c1e0f40712035156810750b50ba2070090010707040251602e58070207081201 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 93494074 1250 93492824 93492827
    0x60609021c0e0705030703140105060a030308151c2109060203250c080303090d030b030c010804020a09020703080108010b0105120402040c030905010e0d02010b03010203090a08030a0e0d110c01 84
    0xd45001205076684412965880324998006000d68032007001e19000d51500000c1e103030782c28441d040003540a0072545440b00c0c1210f1605085034001407000388034180d80c08003440400e5100820301da001d03219071800c1c00d25015170000074001c03400302499150707094a0340341844200058081020031071040b0a04040c400030f4540e00c1610340c0c035140d000780030040c0d00034085451445010300e2086950300c40d00310b072038514400540b51500100c856800c101c009502c00428001d84400402203110880d20034903080001c0000c2000007919001041c06103810010044046010365640c0c0031224001c0031842001c554410091401800e65202445422415481c00500d144194012411030b103811041030f5101c10640d84036405c1000070101034240c1d1f801c0580c1d0300c4013880000d07024440d04803001e01e548018001420441002802d441c1c43e201100d009034018014410701c154002180b05030103901503500c03a182c0d031369019800b009000f120b9000351039200740d01c0000c140360380010380071584002081c10b540700c50813400c00 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 93495324 1250 93494074 93494077
    0x21c0311010903140d0f0f0b01080601020a02060301090b2205040209010e0402060406030e031b0c04180f060b03030c03130510020d08220c14040b03061e04030302040e0f0406060902 79
    0x600442c0100e241301124408000c02000810034018001a01c43c0c6088072010481d916100090300043c0e44444640541d80c210800c258810b0092006106009055000c140c41c0d000600c50654004c5d115072031200c10342d8448040c2100c800c846104021111710050304c20010740000d84042e806800300f00004078400030300460242c402d40d00901403e2900c3e14201088000382001903011102c2d010600031400ca0910303e0394030000308030940340142203840250007000220303484206170448500c800e454000029400b01100c10205811281c00520069001c1c04641948a0320340c0707000160000003011010ba034141c040304016600244c40d80c40720400200c80c160f035208400d10700c0c0030100b000900060624100883e505c80d038891010705516074184a65114420500b458116200d40403241c0c207c00e6150419109141340d8000450041805040c001c01c201b40420203040304081418000d80020305042c0641c0440c0d008120003080200c943c6455400c454181c20306542c01c071482420000001100c048600 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 93496574 1250 93495324 93495341
    0xa0207060507050c030f0901170a090309150e0f1c0b0406060b07031227150c0207030f0f0f080c0609010b27060d06060b0a030c050a0509040e0a021c031101 68
    0x80083d8a0080c0640340300d11b9640204c20080d040100e0301c02d4902046800340b2403240142840a00418010003d1030017500e007841ca82c1100c50040f14040784ca0504d55030102c401c1d0b242c1881525141ca000c803c3e0400b0078445031004000c4050b8202c041c4001d01042044460688514080c1104116868880c0381904045c401c03400050300040c2884400c1140c3c00c06980001c030400501221845c403966010780c91541d2285130103054540c000c1e403d402c2d07075110401d40510f4a9040740c620180c01c5040c04c5076039903d4207040040c0c0107400402407886003000c020143d001d101c0801d402400301e03603c82c15210f04003030f9100b10444014060707500f85103a075209800d01c0e0503801c0080d541513065000c080c201d00f0007035001c0680102241e0740405e01c400d183c0d01082603842903801a02403203164554810b202000542541e181e0034084003006010032406825a81c1700095581c050000c40b001b0907280320703031800c4d0340c0740c5009100c01940c007020003c900003611f02941c0c28000740d03600c207855030310001d45014001c2c6e08860406 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 93497824 1250 93496574 93496597
    0x20301061205100e18120301031713080111030108011a03030306010f0e0d0501050105010810030302030a050702031c050307120204050307030b071e180806161107030b0a020706050705 80
    0x8440c40d486034090ba009079511203218032a00310016501c1c130070a4064031040d42c154201c0102c1150030404c0c21401e20040003240d10b0306540313034507651450740c60000642000c0e04c0c41c0d09410340030500605031400d1103482c40c0182003040c000d000070a100745144490364028440c040701036113004242ca0600400d0120200340c40401400f07141159140c0300150b402c14070b41c42c8003408005018003124620b81c2d82c2c2d0020000d050240c8000a069070400d0000f500c0f031000605280204000c0e00e10410000b40d00200701c0d99062581e140c455102d04540c4040ba00c0e025540c2d00940c0d0540240004103441c0d40c0c0b15000e9481000140c1e220700841035000305c600100e102d217001c0c094268010103001d20208484035010f6070000d003240f8008100ea00c1c150300300d0114000c524030f2038000416130013107008039a00d051030000182c082e400141900e070420012440190484280b00c40c24409440c5260b28420014415080110381048a603105071500b0311001d8020340c00305604581e114a00804036220f00d1164040ea41d122112 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 93499074 1250 93497824 93497837
    0x5030406171f03031b0b090706080c0f070623090c09060109080a0b0c0408070803030402270403112d010f020f030106050d060306020c01020c010509060601020705011805041d1002030106 81
    0x2540c5084603164201c80c2150a94138841700480001403040c0c11032032107080c041c00944001420714100600040000d420170440c0700c0d0903c214221006c1c444201c50a40c0e41c4980c1c0019080e042c00700b00c100350100c2c00d0811209403000010406110303030100c0c503410b0402080340c001d110342e40c51000658450426028071007140e440440c0e2a0005a8084a0b464000011a80c5503013826034032000b40303203010080d80019481d900040b0521003103090105580312028824030003003110b400c00d0f400303c0c4c001410050000d010440040c081c102090400d111075807200c56004004580308500031101d80b46d00d00c1050f4108a40d6207000c03107400710103569100351154448807050103440d61f4a0b200b01192150481643c41c0601079841c4000800034529100070426a0400800035072200301c58002a421074a0003010b01034142c0180e801c101c050f030780c0842c40c04261403090a00340b8064066aa80f11000c45050b00655001450b00301105000c00001640e0380013440224119091001c11402d82c3c8141d0000f0710843c80411a07 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 93500324 1250 93499074 93499079
    0x50117030f0c01021603020f0d050f0d18050d030c11150f04111305060405130305040510030f060803220f1505130b031b0708030402061605030406171f 66
    0xc40e00020708040c800c8200250411314204d4404417544410300301180940c4c062071020750441024404400503c0b01810724504100701c0b140504218803903a00510b0007527035501c00c00000100d18503c1007402a8006040b41c05424050f1000341c004c048401140010540c03400803018480e400241c048928000d0702090705007601c80ea800700642d95005003007107c01e10a591004092501d450410036150302e0007000c0400e05040180c2444210340300a40054113900c1758241c1e030004603402c031040b41c04480302558502c018040105084009000804a490001d824814001000c1e030001014005101c0a09002e004a00c043d003000d601c241c45a02c80c51120340d104280400100381491444215000315040036490106030a81d072811311107050b0012600003034048180550110700c0c03c90600b8202c1c43c6184646441c1d40750719010041c2c0801040240301cada03000034036400502d07030817034052600641c0442101d4540c1d855003405860303002100310b001d110303075180000100880140e8100308040c1c800140700744100d60 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 93501574 1250 93500324 93500347
    0x30c0d020112020d0c0e011d060a0908011109040b0a030c0605030c0c0319030b0303040b0f0c011815050703060501080a09030905030d050d0606080403080f040201140706050a05011703 80
    0x1040100140e0500003100400301d000b100500007081c1d0484407281c00544501542c40103008001c2c0034200f9030401004d11002d95111400c414000e00301c080450b24140c9a4603041c1e81114941400e410600041d42800c10131541c004600024114880c000c039018081c03c03000c04140310141c103051001410b0380d041a00100b00e51409903004580082c9101007440c541120b0000703841c6584d000c0b0800203120002c5121a28000e90b252140c252855000c40c09186860716240323000d0954020a0301a5040490024034403800c51800d40c8080d059501084a41004000030b081041801c990040c2d021501d9040800051016100c0d1041701d0544105031a000b02907200e2031500f500074606140c0031030511004520109407582e080041a801c401142d0f0380c030340d032000310304c0c04002501c809511201c00d120b90700083c00300094019045551220074000000c09980d9240012519080d2000e00c4902a41000070200184904ca8109c1840b419005609120342d076a903160700e000c0c88062103402c000a030001d104025092 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 93502824 1250 93501574 93501589
    0x11040516030c05310b18091503070b030117010b1c05011d030702042a050a021501170d0f0e01030f0e03120906070309030e0405060301020d050108030a031406030c 71
    0x4842c0b45451404d049107142c05040000184c0d02060403905811104400e0795114035001020307010b9825580e003480401c4481d54030b82420b180340e8501c60301041000428030b056401c44100b2030140101255882c5d5075804101d445c0ea8000c0c0075844a401c29110403184400050241b44102200506030150707010251403098002828030728116095500c484034426003241a49880084040070320145070b854101c1d10410044a81c00b9103800561b4a242200b0144004400250b00d001d182608107159140c1c3c0d022000c0742482400c0100082814420001141d4079003900660300115210750704846419400e0241a180300c1407501140740000c40100e13550145500c290000e0000071042c1c100440d4040c07601c100c20342180c110300c0400e0322815400382001145201001400d421200c107050030400e83c805030320b005008075040b400b00c0d03000b1030b00c403000300e0075075102541110482c21380c1c940704114030b5848ad41e203140c41340d000110b090000707420001e40c8140008081d0106010b01c000030000c01c00704d50154180b0000 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 93504074 1250 93502824 93502841
    0xe100e0703020f01030e100605040c020a020307060c020102030c0316020a05010512070315180504051c05190e03030a03090201120b0609040b03150703020702010914011706060f0706020301031104051603 88
    0x1099256a1b84c019481d104110703420300b0380740b504808500c0c281080d043c8000c882070042c2c200700f1940405486005610040707045000d68a9030310b083d6450036500d000507032644c410348040c1c410380c0c03000060017080411818040140548210b91541075103030b0b25801143e45001d95560f0400041c615004a0702050203640258090084860540e4650307544252510300d460782d0300c1050381744540310010401001410b01c00c82c51040c01c0c001030b00200202c1c1da540140123010b01d1805111042040b416180c2c901e010350301c81c2c0304a01c07000b411242d9030944450000c010300741d1813004a000c181c03c00280300078000c00b80180a6003490182110b4105860f050411001d4803a20342c03242d41602030070450068400c070010340144220841d80f005a9502603520004010301010340c00500301205004201c515a81c3c440c4480041c80c00310207040403d0345235207000540d507108107187d81900c000300082c07000800680e134010b94100c81c05004001c4244140800341300a0b600300304e645c1179544554a01c0d94440b540240c0c8076050 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 93505324 1250 93504074 93504077
    0x203150d0507090e07051305010f03030809070f0303021f0b01021207080405060a11100b10080702010b03070f060306051f11190b1911030a091103100e100e0703020f01 73
    0x2d2a0b40c1d90302c03031411600042030070798181c0c009407824000c40c00e0031405035040703000300c1000f0840c079031605406941c0300400e400000e0801c0603c202090405500b001013102401284440f842d0145d03803440c02a58130382007201c0c010700341d100c08024030060241034450024000b0060b0050000c00b000040074040c241d10440c41107a80c414103000129550300e50070054802243d103515240c00e040790259400e0325000780c000c4098407050804540601c0c039196001c500218030450b041010281e203402c001603002d407803041007035130f010b128070900011440307503a9141c0b400300e0301c40ba1020401e481d100d03018005500c40781a41804414a007443c180101403142c0c2645e01c24440711003c1e1144041141403042d0120036610040d035a881c960b00500a40c19440364100400300c50445c03080000b01d200100c502401d0100034494040d690341c81c88940d0a003d01c0000b40c04150400034141d0340350b103c560100c80d0090010408501f81481840c0720b140d40d80c481031081401c000d034014000d0140a02e15404c001102c4005803c450 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 93506574 1250 93505324 93505333
    0xb01021b010f0c1b030c090501051c1e080310050102070e0403050703111603060e0102070201140f040308070f0308060102070e0109020a030e10050103031d090408030403050f1308100203150d05 84
    0xc6240c441845900c13100c410344469000b480d60a0040840400e80c00000100e85094010803c0e175541c41180e00e8485509100a641c042c058204001b0038070380c0980d90b101c3d42c0100182c41041240c7c1c03900445c4141100c805210a05d40c56200482c0e482c101801008068583c0b0f0020402003406034000d82180743c801e00e0800e140d280701c040c09508040d180406000c4000c40c0c541c0070700412a486c01448a031190741002181002140d4000810800c0b2030401c03652903000001d1030700d48000c070042c101c801031a0009461a9034104510703203426100440e1800b60f0008070385c4c9002c6901c540c0b0208002c412120749000070364280e424401814000d40c01484601c00b81540c48115002400c400d00010540380310441001856603d181406000d54a980c1140c00308840020989a603550352440800d0b00650084c1216881e41e403070385419100c5100d403103914401600701042908038000d00c03c0c040390645118406031104c41c0f01580c44141640000e40b400c070184460f003140b00e81142000c940c7e9a0005010708200d9 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 93507824 1250 93506574 93506597
    0x11a0403140a1b0602060a0e1c020309040c0e09010801061802031e0903070c0801020307090303050f040e090f0c0f0a12050a0804060302040906050f0105070f0c0506030c0702040b01021b010f 83
    0x40c0c25994200440e4444408442c020046240c0500c1820f5002014034000e01a07101041d2029442d132009c110240c25208040c40c2c400340b018400c0040e182c00c4cc02c007a1041005041c00800034100f824500c0b5070505c55503000700041003000c4103009142c119050401d40b40360f820110030380b050194100401c0624002494200341e40c0c0d400903009140d005408400c05950380b05200d0a00c0121500d00390049140c0f6801001400100c0741c0c40042c0900f241d40514220b519141d5280c02110300e40304961113480e0901e1000e0620441100100f001d800074419030003215045c10459080c00390115034010036a511044240040001880d500e03141c40c05148a0003d503208218035546250b51074110390405d00001354042024015103500340300c0c0c60090714080390210b44014050000800c61b101d10580240701110032039044c01005504004900a454001c4c09562685002c20398100f075904600d906a20031810050302a460b94000719000709401c040240381d0f98240166401510307460a03070300c0200108060700307038030 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 93509074 1250 93507824 93507833
    0xc0f0506070c0b0708070801181107050f070602010506010c0b0711010908030a0b0603040203030403080a110a050c01090b090916110601030c17031c090317040614011a0403140a 77
    0xe1034410318603500d42000701d07500c50504591000000b0001010302c00b8220901c40516000301505044940b03040e814030010b2030302060b060190050b290461500e5038041030541c1000070104008104a07a01000c41d0707202d036a81c1c3d9080b42038a201340c503000e010500da200d440000c5650414440c1c1d02079102e007001d0300301d5036913580500e0864440b60800c1d00c4120b004820b00c9000d00380c44c02403549603d0111400c90450a280e0002078480c8030b54031006102c1d1300e0000d07910044030b0040c900200c1c0c0284440c1582d5010072181080703600c03a0100b203041400102084000f19640803002c0c140c07804540c02400d41101540c2e05034034000744200d0411b1100034803803550941c02050804003c083d01940c131500020344014507040c401c84d0729043d00c1c01c040049420520103941001880360001c600c07400104008a04003102e402c094138002c140703000d24503110a2260401c01800f16603040380300c61f41c0d58080036519903a03a4002c8589100007684064035280e404003c1040403442c0d10080b4203030056040281c45914945542c0d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 93510324 1250 93509074 93509083
    0x507110d03030905010c0c1e110d0602120f04030f110102090a030507080c04020c031603050d0f0e0609030a0203040b03060402040905040c06020f0102090906090703060806070507021c080306010c0f05 87
    0x40c201d0000c0e454200e60f1080113002c0c000e00010b0300c0d09040c120000d500035585e1521000c8201005d10ba1101c0c0e202115051100a1101503817020b4040c0c4400e0321042d140c1800000395200a250303151412414020a004400ba807090034070560701079848d016101d00d0000107c82268801c42c400c141507409003d12186507503141e00b0540154800e400401d41c06140450080c20a0380400c20503100f688103009a88030840d01000321408078903003042102048045180030344240c015031240c2c2800c50710701200740f1409049a40540640b0b0070200446229507580c0c00540da507442084108030058006210400c00306070300c1000b8580000c2c0060000d030800351640014021500110b4050329107115440301001400d07014440c2940300c0c81007200035440c0c0301d68103001c265124005801d10b40031754039010001d14028481d60014002d05584025540b550030301c0440140180c10007c01a40308042c040b1074484034030301e1160081c040305d5004144a0031907450384010364200741c0010050703d40081c0d50401c10b001071000e11 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 93511574 1250 93510324 93510349
    0x31205040c05031903120209091305120a03240b1e070501020a05040612051e04150501080d0e010918150b030a0c080f06090a11071a04120807050901050711 68
    0x40c00c0350601301c0c6081c0104400070080c00c1c101d06a204000e00b1801d520360000342c80e400300080c0203604000b48245045460003c80c0580b4540f01312000c01c951803010b038540c1082c11051652130300718294424101404084211910038510501c808001c0c1001100718004002407040c0010f18442c00e0400030744640d400c3e40d00c0b542e500c00005100050a00003143c22460360002070103a40020001403a04801d01001e00c616103c00e6000091381000090802103003519203038071100c40ca8414800b40d603540107100d948030040c01e1000042003900301c1490080d403003410030404940c1300c203001c1d060200c012400c441c020a02d42c2410b18a102e500000401c058040200a6024203e0524000b07800c0c841d05000030301c801c8018190401000c0050280b04959072502030780c46c1c0054074180006042c2050b0811104144581100108a020340c030350092002500c40c1030303061145005204559440300c2030681140c2924003102c400300890f50900c1600038652092016241007442102085158800c4000044605913200c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 93512824 1250 93511574 93511603
    0x50604090f08030907150207050f0406030f0609060b04020f03010e04030905060a050a12020705060415060503010e1506040e120918091c02010605060d090503070f140601080703031205040c0503 84
    0x8103204c1202010030181c0000c05916070b083d0302c407502e5024020f44420851003000d10070b0404428000241d03865510100040d0f40c40605000300103018a0301c4000303410740000540e003152a04070b00154a05260085603689c040256005103141c0c01c00c8000c80c49408050815402c00105034004500c0b03841e448000c0559034503e131555a11085000002414550702c646642081030045c081c3e440014000100590040d6012410705022200c0e90f050704000c10096110907417560800c06050780002e80451040c914002c200341d007500c0d0369120001d12050320100c6035101260b0740001410243c01005c0009040b100c2001821840901120241d0381c00e00c0c4415140380d2519042070300030402c000904109175181280e03130b00081c414640b82400007100f60051031405250303d41c480000904008050048404455201038140081c94046c101115003880803003101485118860020030540740016040045030343c076550306110301504450840203405c0c090003c8505009520700031030395580074410308401b070954 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 93514074 1250 93512824 93512827
    0x6020412140609030403030c06020307020f0715020c091608130503130608060a1802070602040914010611010e0c0636011403090601090902131410050103020913050604090f08 76
    0x407558441c1c1041405001000140e00401c0200000b81c0c20a04841407107400c07400050302c0e951078150a07418814240003144031801210404103500d000054909030200e032079421a00c2800291084c000103c1e001c3d43c1c019805041c81003c0e056041c86070b02d009a1200307110215046407012a42c403a491078200c10a100e4503802440b6051208580c0b2200706a07002030215030b041100ca251a140800030b542014581341500d03000120f4805100b55501100c0c003c11000c00200070030341c580588915030900c20302404d00083d0100e1405040010140a4002d403103a1000150940041100801c82035034450007001805a15100c030400c460007829001e03481080c00c80c4445411014004001402d0040340c401c2840307450001d000340a440b40700000c24034190307000340d0340000d0049114000110b8400300101541421130804050300001000a00203074010140584547c102940325001581070b03000d005d04840e003000c40714912005e000c1880d0030298000d0305c003502c00a01160300342c032810092406140195083c140 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 93515324 1250 93514074 93514103
    0xc040302010833060906041e050102030703052b02030a051906030c0e07140d0204150e030606040f0b0a0603090b060306010602031c110406020109050f06071b06020412 73
    0x308542d02079030016012100101d8000b10000f10710031805003506030440d110040f541e820711a103980c2d0482d820500c005002ca038407166100360b940c1141d000d17140300721040031100e00700003000d500000076103041e198140c942e941010f91031419a8141c4050b48a82001c000c815840c40ca0035a0f200d100850042c9070805c008982d0346400d0452041100311f540b020100c4030700c1c140040011500003900007060321243d2000c21459110f102085580035410707064120380610025440d00126407950050040310400328003241400d5020383c05403030b40790f4a4415150180c21030340004a42d442c1c00e9010ba403124052050001e5003918050205426001c9a00482e01195460310752400f8001c03400d00c8184c1c4002c0440050109604122000b5228001e682d6684000796043d5459030b003030b07000d5400410400301d01004583e19195502c00003030280108501c1a143d41c05060b54240400c440850b03410710540ca10b4030ba1003840c18000c200380492a0070824142c0301d0341d07401c3c8008101081180c42c02c5124078040c01c419246100c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 93516574 1250 93515324 93515327
    0x603010f1a030d2c0315011e080105070509010e03120310030606150f050f0702191d060609130929010602030702150a03090b0403020d021915090309030b0c04030201 72
    0x2a2981003d00340104007252507101180c100304000002030705141c03040400000382c0882e15000d004110014003200e02800820b99030902c510b030b038000c0c01c0314001400013950b48450382822580d00740c51960016800f0000303011654010b4800440405024003282c01c040f1781d00c1c800004942041d02d548032400c03981a03040044c4a050301605010300050060951040c2c0e0058001e8802442001c180d014090081029403200c85040c040e29549500a003100c00d1840d026007203021004d00d14003904c2d85031584d40011f04907001e00806820f110300d174040d146031700c0d0800c0c0300100104030400c00001c4200b01c0d141d9100380c0025010a90024040d108080b0421821200340080c0ea035003c1d058100004550081c007628026907078810070440302850218049a9840d00c8001c11005403802607000b40100300c15106010825600091881e4001d1f402d0303098495100b0200b401d502c00d400e415001900d91601441e03440260b0640c2e91009a12511030708006443d03507580d0742c501c42c0d0700c54121103400000030040340030020355 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 93517824 1250 93516574 93516583
    0x303020705041a0a03030f0c0b070906030513030207050f0a0902040b040501020d08070903030e150c0a2d021908120909010504090b0a0b120a0803180304031a0603010f1a03 75
    0x40640180031140c941e003c90206800b1402d03403102a081141e018155999640910350780001e25811009428a41c81e0541c00901071140fa41b14102c0000c2c5040f0010b803464040915405825034142e0203405024a0035040095200410201035030208001400080d40c4000c1d2000340014800e0f0482c032a201c6145c0b00019040141c0c5e40380a070180a01e08d401c10800300d40c01036804042c1c90303060610600002446001c160310784510b80c3c4052810b50300090340501c41c03000040c0807113414071a40d00389070540c0755189544001003a10316a0030f4091b048400400061405281c0b0124410501800008242e41e0341d01d058508841c0842e49501c08200003039503226400c1c524117541c050002510301740a054107070769840c8507813300200310140c0340b540e41803e03d02d42e1f074800403460702c5421784408071012020f5600b0410099482a5418107525803400c0c0002c00d0f243c40481640c04694201e88000d48001c414044038841c260000c00031640b40d5a590f51600c0340145521501c0108120110028040c01c1c284061600c0d0 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 93519074 1250 93517824 93517841
    0x30d110712030203040e04170c0a0c0f080a021201230406050a050f04030509010309020405010906080c03120a0f14070803010306050f04080a1101150305010e2e050603030c07030302070504 82
    0x403250300c41d2600000c40d800100700c5003280c03030040b1160f0850340c4030705040203a411034150000c9075840004042400364400a4202d11541c0215009622650340e080002c503a22240e128259442d00314440030f0015242131006007460f05002d10011500c810002444120000030340b25000700c407143c42d028041401480d10885502001e030000801c09810b1100c2940790005c4010b100404105000603081103030b0b44281c00188000340e000d002440156141d0030f144000e01020f0040d05c4140c4212140d044407807030000b908100107481926042e250a249070002c03504071000c0c10391001413001c041d88000c1c94030202c400401c1401e02621034582c4a505500c0c10b0f106489000d015840402c0d1003030b040c400410901412203040d04243c1c10091800c0c41c210310060301410007401d4440300700c203110900200344a8190400301d5000c8200d400d5480100c98030031100722503440f80030152007828603000c00d00701110450344847d404c42c0700141241d00380000072091614100070f0350401c80041c0c101035003c010500701401400403 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 93520324 1250 93519074 93519089
    0x5010608060c03070903080d150602010506040b1905010e12060a0902010f02010b09010608070e090a061a0f04140a091d060c0405181003020a09090308130203060a050a0209030d1107 79
    0x3d1420104030050080c06517010103130441d03400048880e00159290700c040420800d40545c0c80402d46c4c0ca550280c000c00c4201c41146c0181d04210700d03c1201e181c80d40d05030f5840d481d10f0030255801c0e8204801101d0b401c25007900036402030f602c05100184c60b41c00304401c40c851190b40101050044075440014580c2d0038020008056a04280b185515a40c03100d0032607054400601e03005605503290070f82151034076030501741a40c2041001041c091810703813031303041403064510a8444400c10340b0361466546a5101d40b02c1c0c0c0c1781d0703070903810b210601031141650191460454000c24100e41131340c6480d000021140da100c00904150412120040034090510510341c0c860b404a62045c00c007450680031640340011444030003001e0070700b40006031489401e03090310f00c05190060301c4841e281d0303113401030300c0f004000c000000d0f0003282010000417500a402d004520740e9541c0500030b000c0c26128018030300090007005e4206c00c40b0540910810402d601d04010300300f9000301e81e81d14907540311161251642840e42c240c001d1700 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 93521574 1250 93520324 93520327
    0x204030c050901053a030c02040c02150103061808280504061403181e0f07030f0b0402030111130501030f090308060108090f0307030503060316061202210405010608060c 74
    0x30995990600313407a1030700d60b45017842c40c5a65542613859403900e000354640b1603000c0c1350820482450380c00700310000300a01c00d813810000d5a42d480002c0c0e070381d42a200d8444641d82c030030713070014000508503401000b0f841900e1018696204250b54500400380c010400001004480d04c01c03540f0306034642c40305400410360300e0810901c0c0ca402d020340107044912580300b040200c4070020100c5c0c005604e5020f0716031b04c1c0302d0b16000e46000c00d1820441c4001888541403a040a201d03400321405032000114022040b00c1d031080040c3d00038a19692107003c7e1400013001030743d040d561280342c21078500314080202643c03545803001005042c1403400140c1203608192071240b000d460700d020200000e030440f910343e130441402d00302022259580c142031880c1c1001c4a0b104c185601020562204040c1c20902550040d0003c07010340301406030401c03000c00072407840d1013a20001400741042c080415943d50040042c0c4224584c510811070a000c0c074490300340415101110316070754451040103021018055a90041e01d06805075 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 93522824 1250 93521574 93521579
    0x2a030106080601231e0403020a06020a150e030a08190501060906030606030911190b0c010609050702030c06071407081303061d070e0601030b0d030207030b0601020106032301020c07090204030c050901 87
    0x1031320301d070103600707080c14418001c00c040d4101020b005068800455004105810090f11110000d40340d24868808540d0307000c0b0640c001008880700c0c020309100645074001142811040e180482c0d501601030040310700c020410345604001641d40c0181d03406090243c4689000d540b5007078004048440e554032503002c242c5842d400f64006580f1700b5009041c0d880803039203951a01039505c100c40d921600c661090070585000180d010314007406402080840d00c1d284010445a9a450b0099807a80702d001884129a08103038000785405000b840c206c10310140410300d803400c088466950021903407280802c1c54000c68442403c104220944c081c5500103207041402041021124030166520307240383c010600a840e010000074800d91080d030003144410402812000c0180c50341c00c000c0d44401d04d0b0f020a60300d586a1400082955005008000031a584040341c0201001101411102806d100054100c47c0d50200034890f50000c0403c02c0c1d5001d44080c110041c7e48500d18070b403040b004e080d690300c001d010f800007e004 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 93524074 1250 93522824 93522887
    0xe0909030c0a020402090f0901090b090f010b03060118050613090c02030c031c1e0c0e030c1003050603030c070305031213110d0c03020306010f0501080a0509062a030106080601 77
    0x10342c1c102e81c181c2d0096203542443e000500c000000004440d00200200700004643c46203410880343c0201c01d403001c17980f030b40320003010701031600c3e0900803081e000d0403c001003240342d482810b00303500c20264500740f24102500da10001d0407503480761030400c02803010350a0910209001c1e115000c8071780f6041c0000e52074010901d034210340317034001c50000032209407c910f4030140d8030340b880c3c011160040800b03c66008401c103041085000308840c0791101c000452201d00000d05082c00520320340c1c041002000107000034021030f000c07000b4180062500c1d4240c0024808c00c4032805040201030007031032246001d03540340d020b034075810007040000619092240c079419446002203034202c43c0850b415042520700000c580b025050100c0640300e02e43c0020b4042c0b0030140002030403118600001c0c15034809a81f810707019120780000800791842550340642d941c0203403000c01c082e02d601615109212003000016201c004e08038007141c41940003640020003260503c0100002c0390792160f8504140c00a599011904072001141e = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 93525180 1106 93524074 93524083
    0x3023c0c10090e0f0f010b0a0201020f0304050c030f0a0209010902030711070915121e02031606090314060412030c020a05010501120218070807030c0e100e0909030c 72
    0x414145000505090300601445d00900c2c2c140e400e110400605502100100055641c00c0001d4400310649001640c4524056005403001d4000701080c1814820100040300d0702d43c00966080005130303120960346040d200300e46070043e103039500d10b0800c0d203140000e0810b00b10b0500c10000001a004d403c0d800205052502c05291010b01360b0755030701111180c40700d00c0c00822955444060010a12002002d42440d6000404440d17116040030029015042980c001000040d004c0c1c005105004103003280080641c04c0c100140f5a6240c02d1300c07a00c000b03143c2d44400e8410940c4038550040000c3c820030400c820079410030000c01065941e45540e050801124a04900841d847d03a50b070400c84021081d10340c4a0011034031a15129610302600310000d200f40b0b402501409402c813502c078003584410030008203080c842d0b21061401c1d202c1100300b00f2249002041c848459204209910306d17a4400306 = true := by decide +kernel

theorem cover : BRFrame.Cov 93345324 93525180 := by
  have h0 := BRFrame.cov_init 93345324
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 93345324 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 93345324 ≤ n) (h2 : n < 93525180) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
