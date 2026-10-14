-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2487
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:51:48.310798+00:00
-- url     : https://prove2.me/submissions/3981827c-2546-4894-92df-37aea665c6f2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 447122302 ≤ n < 447302158 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 447123552 1250 447122302 447122311
    0x50a050f07030c0906202505030735251d0105130f02030a02120c0313110a030b0f0108010b011403041104020c2a011b0f020303090604062303 62
    0xc2a41c1410003850303020304000000d0400003224030109807146c9905030301d02030848460b443c041e4808080104109100d441d00c038060501540600300c00c0341403100c5190f088e5040200103111400d6640c4a0388501150f4690051840302a401c2d610715014588821409040e045031401c440340c00080f000825000c21610a05001e241c01085080383e8a0802009483c1d403074403401811207a260348840c0c001d40024030085103d0800c5803801a1580c605a44610905000a05900c0301500030024040f407041084c3d54204140e034000302071074482c170040c03011032512005a8001005000d88409220a0282c504026030507a1100c000810000c2541d200441d07148020034031507051400e081010501092400701c2c259a450000342c40580340c204115203541c98a040d4600b1442c4880c414095010314000108554014840910f070032001c02e50145003080740400d1540008228882c1658408115202482a01c19a400082c00f07940c031140d40300405403024000b20460f8041c40c2201d86401510110002a60b024 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 447124802 1250 447123552 447123557
    0xb04031b05010f0c02011b0b0a053103090f0303080f1b0901110c031507031a060d1a0a08010c020c060f040509040305040806071e03291201050a050f07030c 68
    0x45100a51003a074051524078001c0e4100a0780700252a03401d484011f8110800b8030412044101c1d1030700c080040304403000901178102c3c05406501d6100340d6034444801101a034890148a048004180360a441400703441d8020425011001000404e158106160511403100c80d0300c1655a40da9511180c00e40c0d51014203a009500424405081c49520803441258038a001404403142d0381091000a450460b2246d9009085800c0104202140340e050043d246a031240b0484444804042d03400510740b4020901201351580d40e0340c0f0351108090b2030141020b03100c40042c10f40580c2c04c0e181c4c8246800f9010802148002d481080820230241c10a94101c0303181048190446040c03604107010001c41c21800740003542040700c2840040f5841a09102070fa0054181f81c664140a814a4408280948484041000b454039002d0301c0c00300ea40b03440c051030755524003242008030781528100000d036195001a0880c0070944c41d140070049000840e03171005020b109894040401562101c070308409035000341041e05d00 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 447126052 1250 447124802 447124817
    0x11010b010516060f020c0f07080a03020606040911040509070501141213020d06180c05060703020d1b060e030a1b110108151008040323040527010b04031b0501 69
    0xc1c1a40044403400d032901c103420103c4c00c518280703026030580e0010b841d4104240c100d4013032088098000c0045900400c08403025144102d80d42e10041c1d101c0c0801400760740240d0311b800702c000420184011003160b0410052080100d824803512259882000c0c0c00b17094003050410071101021540c50058031042d040000074203121f44d46d540e504400392520190100c0c0c0140e5480c44100c00101c071805640d483d41c503041e10602d08413045080c8400c07000c7c0310750302c0700340600420080c580c040307940410000320307444490400765a2030705030b403c0340d4030642c90b107500240071141360003206200b000012001b891f108400744d84080e0004161462041d4841040e03e004107001d003000110800d9500848680b944004d82c0002c6101c2030b0302c2034010030004042c0d80c9410000a266204000c2096004042032492041d455000b440800440744040c581d44a0760040d18440d01e140141441e900c941c20300f1500d0502d221420320146540c2d248446100c6400034002200e94603041d118900480801c408043c1c2200c805955150 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 447127302 1250 447126052 447126067
    0x12021b0904080904020c03270402030f15030f0f010504110103020a1b1e05031201210b090307050a0507090b010302090a0303030203060d02031603050606060903070b131e050111010b0105 81
    0x1180f40c1c0204030880c1c0058080c40311501c54803050025150214205c4500c00d000841c10b0319800303a50361010095881244140140302400d400e001201d50700c41182c03c8800c0e98003031007000207450000001e802e06c2e101d00c07a4004c270258071281900140c0c00380784503184865000690000541c10390055520301000076502032a01c0440780260392883c1e1001d0b00603162141254108803179220300c1e00c1070080564265200140842001c0b00103500140182444108802540c40030312910401005403000078200d217064070702041059038148116000a540a4210b031084a030794606242c07100940d03c101440307180b402c070700b019055009000b200c4048034010600000a800d44e503040c2d000350009400150444410079840b001030310308200d103043d950014500d2080c010714510b840c91600400070500750041000b8440b981e5075072800951401615003600959460b450b42c1400803480080135031251003261549200d03204256010a070300010f6520aa0b16a504100412038a50070707190810011f0380094000c01181 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 447128552 1250 447127302 447127313
    0xf0409050a2d2f0a1107060e01170c1b01060e070c0c17033f16110705010503070c06090f0c33030f0504050c010e090108060a090f0b0412021b0904 64
    0x200809004c40c101074410155448800e880d00320700340c1040000c595100c010032002d41e0099480b4003c0154040d030301c442d41c60000214140b0340102d1452600c220846100d408492800b904036401426018481610350303c0d01002c01009644050303401d0b91038020441011a00b03e182880350301000303036000001c40c43c1c21170908056013011420750100c0d6013602102d12404100f0000d0840800c030030104d0114441504011420000d01c000000c80c0009108030150010030707001c400f0450700c0031a034090801e40d4603540c1c0e290741079501c0f6603002401000c0d1460050728808005181d21040e89490040030040d16807074a480321200ca5070188036044007001c08440049403546030345a14035a11103201d10380803a40d0300c4080010700c01e44005032002c48003a0044007075002c05c0e50303000e61006001e010468501205501d03100d1000c1e00d4a0703024020610b101e484a60440c00d0100902120003503e074042d050b0a01480d0a0418460391903005000d8001070244d448041c12840400021210102c0000c060b030032075442d56640c6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 447129802 1250 447128552 447128557
    0x9270607021f09050303070804030207120f02060306030111040f091118040e031c2004030b01060804020613030303140c0309070b0c071505180102030f0409050a2d2f 72
    0x242c240150715103c2080004205201660240c40e1540310303d00c241c101490042e0610106412880c08024000c50640c0030038030945410240d985c050b254a9929101c44022a02512441c189103050b400e000900140400c11051810202c0303248610422181c16008102d03100d92041c00190740452001910000a916050340854500c810700001c80340f0304014000040210040016681e03400c42d40c0d810313118008100c40c00b0749407000e050703104000d1909080d9610020804010b0050504226401000a0841d02d82c401140c40758481001145442941e07840c0c000c1c01b900100035009101c940006c0441d0024104c9402c2c5d900429a41000e000d103d0300f05414011150444410a03403248130307158001860710122440d96500315029a9010303138850454500301d4814150704181030440d401048948c06810a101c151002d5903c8808081030b15211303100d42030301030440c00340400c24107004c406c040c4e400d0000d1003038100d001482140090040626007a8021080703c0004d44083c1d001d030820300c04481d8503075071000 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 447131052 1250 447129802 447129853
    0xc09180a05120406180b0f030705070c0b04090f0605060f0c101506090b12191b0305070306080115060810090e0d090803090307090b040b0927060702 65
    0x1100e100041648541c0d14003003028040c0d44501da00010b00f808a95880302100b034104904140c1e903401c107031410000460718490700c5d14614409102102007203003e8440d00885040e0f503040201580501d4880511104942c450f2042526180c940410003000300c03811300440d4201e5000906890906041801224a550084040ca040c5004800c02c500c0050481d10500c084800c1540c003002c500340c10188090841c001507000440080c5003440310404950000083c2c070340c011502d40c00304004154140121020705070b00803460f00300303d500040b107092255040e400144a520309640c14040c480d0748090b16801c172084032118110003014458107002043c01106c40503001289910525401da0303943c0b200030203e82c140049100c0d45e070010002c151050b035002c0c4008025040c00c4000d0740c034007a07135500007030799400040c0319403180d41782c46500f03005e55541c0700e602000700003101802c100910f2401c149104441c0d02562010401c42d014070b10b185403500c0c40040d0031031140f140e640080107440318004a90080c000000f4 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 447132302 1250 447131052 447131101
    0x3011e05060f06030108060105030601081209010e01090b0c011e09030c0209070e0603010b04141215090f0f0609010e060708041b03020604030302010c030501150509040f140103050a0302010e0c09 85
    0x64141511020700940c028186c80e0003a040a5061404050400388182d11900c010382c05610080a810310840484091090900340705a44402040060300c01e520f903640002101e01002c00c0307040303081406411030a01101054000c0c20340c4031118a0031802c0380c040440260001d04401c804000605100324001c1d00405141012048860440000360080e40260000b0443c0746011500300f09804540d1503403901c09104840350720000e2001d034880da58641c05d181d074481c0003075100d002103014000140501a50302c0b10081c1500c001c0041c8440040c1d42c0d07c0c01341c4001e0920341c600101190040d20100c0d03600d001d23503a01e550b052401d40f52521850315200e04a03c00c1c407450011890004016030340c0f0780007440250702c60b0300046a8800b41d0035000d000c480050b405808103100040391030707803030341d0303112003150b0b00b102080302e00095540008107044000d009a030050115422100004810f1040004004402e03078840c0e0300a101d90340300300e9a6180c852a80c90400c41c1c0200c030300c00104c0c0e244413651100000204076403 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 447133552 1250 447132302 447132319
    0xa06240e1005031c0305070c110405040609150b0a1a0405061309021611030a031b0f020d14061501080103032a03080604060e010e0a2a0207090b03011e0506 68
    0x800020b41000d075449484100300c0854204c04aa040e010b001c1c8903480000e80c20f08080c031000c0303926036030706003120907048510907582c1e040001c08101966100290b966040035800507200140c194070401003c0703203c0c81600c02d0144070400506041000f0104403449030540c05241440e183c002881150b0304071186503d48504001c902040780e1700d4034406061070010081c1d002d115100a41040c1c0800d8070182801402038202210300000702c0c4c0c000140c51090000542790030051112410940c90308003000c01d00a500010000c000c07020b0094204c4403601c0d40051506503051611001c00002205585030310660118407a0801080805d00076198801401041a81a1a80240d6001c40c00c40300e100701c4801c50110b43d091041c4003180c20f01d803060402405005010030003d50404400700c0c01031000a181d4600d0b10307201c0051036039002c820902c050705000f01c030f01d00c0c00f4140d0038810041e4176038096001d5000300318030b840c3c0d04c149145014080d00003c144980011030311100320070600340180a0051840d50400d441 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 447134802 1250 447133552 447133559
    0xd0c0e0c0706050c03070906020a03140d0b0a14010206070815090c04030803240307050913210f02190221010e0307150b030114011203030615020a06240e10 68
    0x40f4001c0c41d208100c42c4620303941c0c91800303c1000d4401403868004c0011540070007206d10010341c112054007010705001714666200d2203030109000140c10201c1002ea000140f000d00024806144441c50b520504241c0035a03c03e0781e16804210b0f005082140c0385400710341a0030051003107040401c1c00d20f030085600000c1c00e14082c1c494036059990f50027a80d04c0b90f013055181403940d058004100203071200714012001b0f06181481d04002403242807024201c0c45084545006031410004407000ca00f6201d50150084192a0480700e0054150342c401c0442e000075008008051000c0307407414400c3d03c80aa4020034443c030002c0c00403240810340407409080181c565a60750310780d40f04401000034141c16031040c55036540c400c0748500e95000351f40f54880c20328003d030706006c2070000c0c030204608039a054501068007201e401e481c2e414120040c254503400001e004c141240003103803441c3e011891200e4240144c01c1031010001c40c8a5002403071a584035581042c0e02c03803000600400541c1010203802080c201d036602001c544 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 447136052 1250 447134802 447134813
    0x2090f1c05060601050309030f0c0705090c07170703050a0302090111190201021c05041206060f06050408061819060b10030606091e301101030b0d0c0e0c07 68
    0x360502901640003144540030440c0c10040c0b01d0303025600b0b180160540c00d02c201c1c42076481c01824442040c0040124502e882524100482d0b070050070000d00201e180c0c288400c0040f466881440266000100c41c849010082d03400011030b00d100703a1590b1a20b02e41b16000b0400c90094001c8001607040004142089400c3c2c02c08000c46000241c518a4818940002c0c4c030000e440c10900034007a6210407103042c040d000c6140c0140c240e400b22003480c80700801707502d0b03d850b1041c000c112a802543c158580740f0008120746500102500903501c001e41112001d0b204c81a0007070a10b10b40b51078815866101804030080a010b00c840488054402c80c004901a0151800605801d00c55070507440040d540d00320070000550b006910000800540301c440422508000803030089810500030380200003860413005041140c04200c11045101c4001e0f1181d1042082ca0100600000c9102c0c143c0003d06100450003240b80c00b0385090740c0320740d01840882100d49000c40e08000e43c2d00080c041040e0040a0114401060 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 447137302 1250 447136052 447136069
    0x50f07060f020d0c08061f02070806270a1104020c0c0306010b090118030c0501080c12090d080610080610021c0e03150609072706020304030c210602090f 67
    0x141032070710140c3c0700d034041e20340c140888040300480d40c10042150140320060302c90820f01e510342d095411180419545c43c15050340750070701e0baa00400940c0305400070030401d251200424106951403506000080c68041c000a650381707a48a80075184841500ca100d54520f450382c020706030404ca9000b901c0c0360749054400070b0f061210981c000308041c580000c0881c0340c0e42c0e000034000c042c2d9290a09514905065840f9000760003c68092141404460f00105000352490307016915070700d044c107078600414605101d81a07210003080c1e4904012520314804070340d151410342001c0b80394410982d07c4001907622803081024003d0603000680c15806841d62200202e0012020b078122601513840e01c003030b0350180e5014180b074180c0b18071b030014010908009004507035490811468010050303160105c01c204011074800c6920a03080c2813840741c02c00c2c1ca000000d0054011024004582c094400300c01441d0f030f036000781034100d0044511340c2c1c280c07004500d184002603e2035028203c3c1103009003820b120312441002184140 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 447138552 1250 447137302 447137321
    0x3011b0302091824010e0409081b0309131e0507080906010e040b130203010b030610060305010911040513022b0509120306040b010c02040f050601020f070302060a050f0706 75
    0x94000400a2207428500c035214100704203240190114680441c02d1005282d40090030061340351005032000090f84550f41c400c00c0e402c0d00510401071560780c0d01d040e079a00e500c03c035418080e1003600c003082c0580c14001300582e124030801074030b06001404002d00c40d0000f8800050014010710b401101c3da03514800c141b040900c0741a45032522905420510b4a20340b038200160f2001d40c0081080c0d040000040b45c044400345c10401d100501c81d5020b1461001a0140101c003403005e4251042c1030400840c10300704031000d800c507a8580c40c108050307601d03043c120099907403601c1d40500c91035080104220fa4101728410301c080068070b04006050800c100400b85030221801c8070a0025003094030204c1c0504410300ca0184c215504200400c5100e59508030402c2e1400000d04140c49943e9860022100346d00500861302e4141d030040c001c020a003000348840340103010583e0010300510410401e0010f0403400204002583c3d001041c2904042c42042d0458843d4080f94000060480901000000804900446549 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 447139802 1250 447138552 447138557
    0x2040b041e0905011505090d12120c02010b09040813090921170f090a080304050a031119230102130e06041505060a14030114011205010b1803011b 64
    0x14a040c00c041d8003503001e200e03041212420310b00401003080c00100b2091305140919800d1241e251088500041c002499803c03015244480041d100d19030584d100807030150521015800f0481e20042d0b000803800ca48030324400a07000b94840c008107020518041c040c150b241458500d1020003a00c400c41482903d041c1c4000711070086c99024000b6190410036411a02c8128914000c8140071a00903c003841600141c0500000c80c0c01001207504400300340300350410550011000c0750b4908007840c0040e990010f031801540055030440d0030550b016004190a8044004c0485c0704100b00f2040d201d4601ca40340c5600c00e500b14850110b060510001c00380050401c4c5110341103418689882c104600d481040300400d403620491400c95110340c01d00d590182d8070309a440030b495054840b00c0454082d14400100042c0c01242200840001010f60381201c6080d2407403000e9803010803a141c2007814000b500c0e400e014402a00409000e24414510030765101802800001c0010569000305e208141d154090002d88000 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 447141052 1250 447139802 447139829
    0x40606052806050306060304020d1e0f02041a030303180a0c0806040b06060901050a08090c060f0a03060e0c071b170d1e08040201050f09040f0f0b191802040b04 70
    0x7281404404514000d064070309015186180c20390009009110061009114403183c0e41d0f031206002003c3e1010120b503180c0501e100c0d030000b207400c10a8105800d00c1040744180e040c4954100301c80c1210001481c107440c085d00640c1183c9600045041403502c0403201a031a125003041c0202160819283d1030044c5840d2018040a007070034140100c000d80000c107114056172040118085999000c800c40f444240c103440c1a0710303183c407255101410700880d03001140d403002c000b05215018019440040c442c080054904002140d03079007149001a1038100d0f2103400d040400d00251012510546140e0140f540300d03182c03201c4540e2104108810f0022041c0c2c0003000e46d0055141c00400740e04104c000d40300c652851226071900304c1c6c050b00144281d0303006100904000010411074801306070003060b1081003500034010b00450001002c640000d00c400c41e01582c4040c2080e030306034140c1c03c0209042450f000707002041c0742043c1c20a0041c108841041c103034034120075401c00002800302c001e040900058500d84201c0003 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 447142302 1250 447141052 447141109
    0x90c0301110c160509010611120f12090d050304120e0907020601050406142407061803140702090403051c0f05060f0a0b090f0a0905070f110705061204060605 69
    0x20720703003802000080e041c2541203000f4003082d80c8517002941107612a147c60401c1982c0c0240c4182813003c482d0181d210a2400714500c61080c0a031030140189942e01c00656400e559050700095940c144c003040007011074000c10100300410030588a1a81048150801d00c00e02842d42011401500084070340740c0060708034000502661a10b4004c2c0d600038042d0126a201c81d01c1100001030007000301c2c1c05182144030200f83d20424442c1d6000507552425080030003001050350541082003201d049075000c4000510400c2840000000c882c2551452038015140f0344050b0380341d607001d503055480881d02c40c2d60304c80402000900119a4061428400ca089402103603a080203001d000e0203000e50400309100b1b8000c02001e102c616094000c4e40c082542c00c444118045c0c0c000303000300b024400241c010704401400c050410503410f40104007160301c09035a554803011009990003c549412040c000c440c3d2145c0308100000480440c590b149400034000c91000940982e114005083d60510601200344005c0001c0d090 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 447143552 1250 447142302 447142327
    0x20d0b1c021c1709030a0203030d02030702060610020a020111030d09050a020f010f080f150402030c031618050103050a0216050d0806190314070801151a21090c030111 73
    0x7a01203001e81d402d01e10091507661050310009070004a50000704011804068a40d0b003008400d094980140549550b000c0c0000860042d62040303c1900241c864840491403d080c050002d07404880c007980613000c81206603004440110140468058920042c414444021428440c00e114030f4480e0004200d1020301c1d105025054030b007021601e040c40007224035504460b070004032940d808440c10107910b50b80da803440c1b038890f440c882d03a40545030403a101100300030f03c0601c2c100c0110301952424280b9285100602401c440c0342d200607049000043c043c400800641d4001d03007040b5000743c0d80800c0981800322494814a42600c880e4060b14168000b026010744550440c450b1070f0061816035108001e0f10a185041403402c2491200400848581c04a02c0c108030091240c4005800e11030000c0c030000c41c00e10050101c051440c040c0b9a800b03124031031300341207680008040b5007150100a02841d030407614020030000001000705952060b0141054000c2d6130760b401c1c030402c1d41107142110f02a8691441010303c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 447144802 1250 447143552 447143569
    0x6052208070f050a050f09220b0601031802031c09080d0315060e031209010c05101b02013e07030903231b0a120b090d1d0103020d0b1c02 60
    0x1184c0100422036007030080b903e0301021600301080070f540120141d02e0320300f81c65070850f01c803008082c00c20f5010000e100811407164101801380c103099a05004c0121540681c044803030401c0c000a615500030071006005480175103001c02107403c4c504001a00d00d42d5802c003142424815404800007940e1044032401d0942c1c1c0015140c00340115142121030740d240c40e404070382e40e5180030112810702c51021600f118680e108401d8407848540c8041501d0011031460210405005001003407405c04100d0f0350f40e0091940705104601c044007501c0a1141150320500d08410009203c100b840034551030f41c61071140100b000d00003410b805200e591600407452842c200200c040c00c0b440c4184c164400d0003508001034600006451040065050803815582007c6000464034060781d481170050941e89488003081c8824160b03068070800104080e21100c0119a88c200c0703100500b0881074540d51901410040154800c3e40508500c03078641c0c000003030f4010400c2c005811003030002c0c14001c500c20b1403420002181042c400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 447146052 1250 447144802 447144809
    0xa1e0605100b07150f0f14090a05060420091602160b030a05222003010b0109121b080307050d020601060507030c05030405040207200904020a06052208070f 68
    0x18100c4180e061946400a9114144025204c140640511020084694484840d04c1404881085404c000c20030b05e00c041e00150780081d881460110000d038440c1c03000300340400f8040e07000c0d0282001c0c3c0d940390b45190700e444034a40801c030556001552001503894850216010340600c021a4140806651000340340401013040d0303080040d0100c0d800c1103101003100541f0f40244810030007142540e64000c2418a0071003204502401542482c400002d0208450f5040c0000c201103c6510402c031100f420300d07083e03a5a40c006140010f000c04c404116041640041000700783c0324917800000200030311000c201854030768100c0f200c0c507040040c500d01044004c1110204503e840c0c0003a086561601802074068011703080050f09101440070b00d0001c01c0420320844001c1d000c0100700719111580c50800d074240c2090a280754429800c4100500030a24282603c6440380e5030040251000d00e05021048860b90840660350441e8510301c0d18262907030b00344445080c09040789138003c002147c508810b41c5451441ca62 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 447147302 1250 447146052 447146071
    0xb0408040b0f1e04050a0e070e060409060513054003030506130c020d11100c080105011106060a030f0516150201230c0c0a06180c1401021b01020a1e0605 67
    0x101c05c000d552249186c59049400340c3c55003d98030f9076218402c1d2a900e444010082d44020002004180030b416540020191442511030000c28010044010211201550300001c844042c4000c1c1100445009813800c1340000410121000d0460f10038103c0310070704070041103001c40c0c0c0380d80801c0a01d0400101c802e19140f040c2009002c814001c91020b03440300107041203901000340e4200b24000303001040001489000720024108100480c1ca113004103980020300410340018000d82c00c034501c0d40780018245000c1d410052090340e0300b40c41c0d50795500b409a8510390444450140c510400d80d5000b040760710500030036405801804d56000c0100003402c41d116000c15041484043d0b602d9252902c1302e80c4595800b40200000642c0c4900501c0000e10342008824001d082500703007811034000c15a00348090003200d12800203035074600e1b242c4159848030587c1d4140c00d03005910003450101d01c0210080041591007041c016900307902d407980c90796a01c40e13120010084c0d8801c45040c28004200251158651101c1c40c81d = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 447148552 1250 447147302 447147307
    0x3050c030f07030c090b0f0a020f0703080409051003020301020d050108010506010c0b0c070302031207020a0302070504050123040b060a0c02120c0d12350609130b0408040b0f1e 77
    0x9003032500c4601c014194108050b903480000600038002c60418000d001401d0282d03845a41e01d032411106903012151500050140d440d5a030608440010220152503001035481d0074141007003030075402010700a22848104038560000000342e01c003071005100a490350100420b496052408a07401d54202826407410411840601d8011a980c0d1403401e8002d11201103a079590142070404038554081c00c61141c01d000324400502842540000c2d450342d510f403094007510640b035131742c204200458209224541079901519802c820a00c200000c0c030444a100030000075501d141000404c0003034014182c01804110317051044010b618011648800040b5298010001041040007050f480d0011070030050010031400c0c0c0c42a03038140280e504009010001c410100100e4440d400c0040030405a00540d20100403640407400074100821103602c034885170000b101d040444d0307070b0380c22000d40d90090040d64112024000030440c1c000f01c2008144605000303529586420b11902e80e502c64500903491741010300402c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 447149802 1250 447148552 447148561
    0x20011b060506041b0903050712030e0607020103090c08150a150e0702101103071706091f09090819050a0f032301080f0c03010e0a060e160803030703050c03 68
    0x4a45501016500100115580c0c07240c40115024001d0b00d0b40c40c02c0c0c501401c140c2200c00b6035000710014122401081152115681e86c49060b0005043c4000603001a0740c4ea502e40d51a0b0800d00c00801c1000d1040c9000200c9940645400407030010f0b41c1c0049040c1e4104048400e0702542050030550001072140c1c0800003101704010f1480680000d20070a8251010400000d002d28024000148035514890701030050040c0c0e101c2000840d402150004003040c0140d400f00c1071408024101c1d0322400d00504401c01c02d03150f03c0740e8071042c1191790060300c3d1604030101022a020405000d400d202d107116a980075100c0c60b05851412942e08103803d0a41000424004a50f400b0b600000c1d80319000007a050000e5244003021500b40b08181e40d01080c40d4031703800e0000014030710f8000a12104651010700503684440120b10806080e1141d200c000c512a41c04960b0b81c0000c503506611000e10204224115055044403032413030219060f682e407050b800303071304044200f001054250054a601100182c051499442c1 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 447151052 1250 447149802 447149837
    0x9070807020d020f07050d021c05060105100e030d120207050f060604180305090609042307120c0905060f0c0a06020903010b010509011704080405060c030306040b0d02011d010201182001 81
    0x26100761803007141f13022060015905c032644004440c42042d002991909168140a60f070381000703119050107a21004491601e8500c50819030300d00d044000c1c003a00340c03007150740d130304a41602046a0b11003030540e0800c2441d0000d4410046441d01684410140c109890040308110484800140d4034581d100394019017400a540407081b07401c60b282c12561151208070fa200464000c1c00403a1070421034030304685801e180a0a44801503216218a903140e203190200c001d01d40d0140c66000c1900c6006ca2001602030007503180030000703055039005414015003070030b8800b04e001e864042c007503000b502d0441d03000800300c0f840d003001e01036114070103004e003040303031801610100003042000c0001c00403c07d84401703404542040100030803500103103402040e01e0745034601e505140b522a4403d07603100c3d00c203d2501d60322001605280c0c0c480b628140d0143c507614043c0c4103002c407031201e1181c0c244460f4110f541c0c85550000910415000341c1d00c00307001d5004e00402c0311940400701c41045102100505100c44500003640c3e844 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 447152302 1250 447151052 447151063
    0x100c120503040503031821092d04020f120f0907081513022d0f04180b1b0409060612110d0902040b061908071d010305090c09070807020d020f 62
    0xc02c030243c1e145174071040104e0600382040080c0c50700740c505047c901041d41e52643d102501020303408030b50080034601e10381c078003804200b00124840207540c0302804810b003628140e4040c03c0c0003010701d0003641c5405040703295082c102d00220b0303617940a109140240404940100f150001401c95100209201c140c0e80360000140c040082102d86034142142961045444005e050000b280c1080680340030001940041104c141030100e41c0e50240c0d0340100c0544040c54680500d80301d600159128801c6c0c80da864483c1c810640c4001c00719800e0000110901464059900042004100d0380740005034250030f0030310003052a55484c07440d00c00e00d400c06400700c1c03030410400c085480303084809400250241d030f82d10214016080310300006034466408180e1015003010030036000604c031443d030b41e0324625585038101542c0095414240345159103a90b44400400e500036440300341c0000700c1070100c03070001000b00000b6507000800ca900ca400103103c3c80612409c240c04000c0101041c132a0b00251464500602c01150b481 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 447153552 1250 447152302 447152311
    0x10e0d1202160501091401142e090507021b060f070203070329070305100501051308060a0b01020f0a08071b15020f06060a1d13080f0304030e01050301030812070e100c12050304050303 80
    0x850384041d080c90000001c5d128003403443c2c142564079027a95518100348004250843e80000540a050001c4450101462180e841c000006003414108942524604940d0308601e03000c9030180f10360080400130075115170a0f1041125020348880c00c1e85540c0c0240c41c110f91001c0c00030418541000e040c41036001c40c480504059450070b00c0c0154840400c900c104090f0341c1d507075101c80c201d8082d1a0074400115640c0e0048654030390203030201d645101d0807109503a41d0380e410b10030103032000d0b00034000034000038400141c031401c074100b035028000580d441d02500700220503c8000f0340090782c421903014030184001c0c480c456200e401101c030440824940400400c1c007003d032001c1c2c007030711848610003d80511644810381c0000750b004901d890301ca000c0301e01d490426500c1038070103502080103450280080e610030380859040c0c0e640400440d05204c1c110030160041d07040945004180203e201445d0641d8480031000e01003201c00f030341c60303030404543c41c01c204200d1050305d04201c003040010002c1102080700002101d810 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 447154802 1250 447153552 447153571
    0x106170906130831060f09030809130c0302130f0521120307090f05090103080a08090a0618020406090507091a1606020408060603010e0d120216050109140114 69
    0x25031081c2d01d0543c0082c416130311003107803040018114003141543c0048a111015105031000790700c68a80609452005142000070006100381c2414000241c3c40c0014000c428070152940c2c044907080d041c4502038911400070480040d030b000c64140144141c2640b44030003000440d0580c136125080c00c002c03819505000e28583c209101d400c0310103d84c0c034803c1014040200d02200e00c25101c1c01c1c02c440040c0000c0d540c1c4601d10406020002c04181c03468440000360480744e101c0c14071440c0025001c02620841c0c1c0007000d5180324004d400078035003c1051405620b0f200c68081c12011401c1c00d0030320403c01290070784c2d04500c0c044c0c3d00c0e020401c00115000303142c01e42503c0c030a0b4129107d41003900342602d002d22036152480325000b0f600002e01e0811045d40c0240054440c041e040d03070b445079100c0b000c1c14200c1e101c0c8580021aa4030158070440e140f07008825014050408038005482e0a0f008880c000140c081c0030710444050303640d1143c41090240c0c480d2a04c0c01ca0351120001d0264803d04840c2d0400d0b2880901450b09 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 447156052 1250 447154802 447154831
    0x204080316062f160b040803090d030606231b01061703161103030c010c09060f0c0201020a1203061a041d042112050a091203060602030d1a180106170906 67
    0x44100004c442c02d02c8140c0d1001c0e0600b014075143c0b40404d1103070816540000d071403081c0ca881c41201e601a008900c16103907907035100480100380140140314010b04180485903001d08005445100741d03800c0901109041410010408518095010014000807002014180c1040c07241502c001e451034109441660403010040784100c7c20b10002e030442c8030b0002c08520540c03814900030489604a0524800c4510075115402c28008142c42035130403482078000203005800022160000a0207003060660440c1240350028055861312401522052054a9240c00107400b0804100c030f0941d0006000c00c401264140c030750581055550628a004803401c1d07800c1410000f40041ca046105200706002141c400b1010302080c10300656120082c02c032a4070a40300610a0100c03034244074001d0041c40c00302c84c5903900461030230414005810060000346030700b465500c0d0401843c3c405236504c00c130340c001c99809504210a03e51401801801c90960015900341c072072135550400107150404203041e980000c24400800 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 447157302 1250 447156052 447156067
    0x201181a092b05010b01030603030c12031b02010203010e0601020109020607030507051207060b100e0a0509040f020301091a01080a0210051602060a030209010e030105011a07060204080316062f 84
    0xa40d11040b540ca00180c591080440c1003030041c1100c0b0341540140502c00030040b15151000450a0781c01d20700000e0040303100d858140f00020b20700c04961a00c208540b6000802100c6507482e120040d603407a10000041c1c0d004001480780c01c6854901581000c0c090000b044004016801702d07040f4000c0c408050240400805d81d28140801400000005014030f000242c1d61049894240700800c2d07001c1c1c0f424010010054100f059600540b0460b000000042001e2040392034201003280b20800104200e0310459002408401030302c0034010720b50064440d82c402c4599003c82d0040d80300c000016444020507511103458440542c9403004144001603e901d0100d5660403007010054400000d032200070b40010002842c410065850340c06401c00c11000da031130b4551162032b03a003050b0a039402800b40c607003a01c101d00d100d520010074050041070b90a20815000d8203040c1e0307894000d4216007001001420242d403889140d020007901e0b20030f0301032600d4001d100b20f41415100000d101c411003004200d01d002c40002070b554 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 447158552 1250 447157302 447157309
    0x309011d031c0311070c0e16140913050c03060910060504032a03060b2d060702130203040b0f09032b060b040b040e100e2d040506040201181a09 63
    0x36000041c211040d9500c95682c46c4c100300d443e102d4440c106054907194081184002c2092a9443c000e040e556074441c1821402d4813000c1544c00103082e96401102c0f011450060401c0d40185445030607072803030039522840c007101400034102d4014480c400490441d40b05112964020302680c1c207598010754212860102c6c01c182d0454a00c0309000b549030401003083c00800c00a054001000780c0350240c03030500703191204e101011801440000000c0c0b02100030b012300996400c200010748001030000f0b20051003841a01110300c103d034015542581d00c000040200700c01c2d9038010403015004804c0c84011485d01481c10302c0500714420030b044060000c0386c1c441d00f2032007044980c0c200001510441140701d599650701c941010441e841440703040058408803000992151034243e50604441c80c0310112420380e0f81d8041c0e0744044036103440140300e007460301c10892803000d0540c0407902c0c41184614002d1000e030070140005004440c07040748900c0ca003c0d40c0329061080010400070007510314071a040d410380311603144000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 447159802 1250 447158552 447158561
    0xc03040f231501030606120503040b0a0504050d150b1f030b031e0303010e1609120c0e09010e0f06010609050f0d0b070c0c050402070f081612020309011d031c03 70
    0xa10952046031541e003000e11948042c18100c034803c5504203c89030f0307503a90240644d01c045402400517002403004001c030b8103540e40145894280e03440d2480c6401c4d141c0002580b6860202000c0d85c20b0100c428001e1000c5100c0d1060510607401112404141086180100004821009000205911900720700a662820414411928070281c1c1441b072079000708500780d07130301d400910400488241d601c0c00b290013408a5402c00702104003071782d03a03201c00e241847ca8003900c004090b9003c8409008150303000500d0303a0720076002400f400c5558004980e0b507c441c110359250002c4040c0c02145a00590010405c15400c0f1800c0c6c03044880a446200c206603030350f00041c280c82c2e2440405401e580c140d03030421460036880f465610540b480b46443c1d41c0802c2d00d900910089015030314005043c004071480c1600410303419405401021442d103160707044200d9640c3c2e85c0b100c01519084440c0984d00115610b0781543c0c1090003410045d40004008070010320f4040000e03682c465602c581000354180310003d444a900c617800 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 447161052 1250 447159802 447159863
    0x61d010b0f0702121c020307110904020907050310030c060c020f180a0b03010f0507030b1915030e010e070305071802030f04060209031c050306101e2a06090b0c03040f 73
    0x14101280c0707117541c001a46961000a04031803420a11902d03c5c03062034030903141030149801070300000b5170344d0b41d15200f5940e507840504841c0760880c0c016000000101f4000d4007501404403555080e00594030780c8103101c00319600c8064a40300f02c00c02c101d0700c0507140c13601c1c050300d5200c1080d03000400d5205105000c0790050815005c1e0001e580e041404001e40700c0e8040d0800c03007141000f03a541c12000c50b04004c0804111406028501c8680540d00503000c403c0d02c41e810903041c1590130800042c41e01d1041c8045842d1003982d910454054220b000100001111080310100324520030b04250303e07510b44500c000d01865002403000b0300c116408500c0e40801d0f1410400700005020000080100c0202502e024100f60001ca6600748686501051160154440c0100d0026444500d034000d0040320a40f4054680d00b8004103884885001100e581c0284801504550202c030702507940000c442c8076504000d0b04a0f40002d05001c0c4440e000c009200001d501e481075240004d402001c1103041045140000740480604c00 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 447162302 1250 447161052 447161083
    0x310050a030f03020c06030f01060e010504080a0b010807140105030604020d1e02041802070201210227031506031908070b0108150105032404060e01061d010b0f070212 73
    0x140120400402c40030002a4500035021a20805000e5003041170a120840b6580c420031804401004000e01070f8a110180040c14103041e070929440d912424a4501c3c540429140c014840004119080d001d11090000e404003158a102580d203410010b00306100250015004d294005000350144849920003072480c40044802d0303a85a10032a8214040e4202d0301620000c20300c0703c41d4100d12568203100316852241c0c1a1244101aa85000407002200403899120f40c11502005000710f0b0b01410001d240307502d8900c1084686e410450001e051400080d22003017520080f0740d00510043da80d001814150004c44d05039118404034252a100c45103008611004144001d003000104603800e021a008900701a0b0040440c1c65a90f05e00c20182e4500302000500505812085007104084884602c207074018003502001c9903140d00b401041e130840c0c0035035104030000c00494800047e8021180380c0a4010040011120f0428260103940701d103d110381c40c0300030b100e080085461840c000b014040d0000451212 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 447163552 1250 447162302 447162319
    0x50c0a0c080607031104051305130602040801060f1205071203030e0a0b150414070e0a05181015140a020a0512040f090e0616091502030a0e010c02030d05031005 70
    0x801c19a0b0380e0760301c00d03151900031034102130156140f002444103450494030010180400d00744150300035001801d0181ca1481d4050b0350300c5032500850718034002040101551000059800e20b468842401184203400c00403540008000d05004610300086080a95080303c5404c00802c501d031034150001c0004c1c003403a00d0070740034545041003404002001c042c4030b01c480c00b04c13250300d1803150400c20084494540700403201c1c2c03e20b0400b15140602c6501003109140019108900154a0f41c00140242842803040c003c03c145000800040744100a205070040c1280703491804103134542030380a054000c8048108154140c04903036130340d40c64400c00c804040b1a4000d002e4554454040d12800c0b5103500601420071224031a08001990345007034031958044048140150072591140c400c46c0c50440030a4055000b0440040d00c00b1440c3c8181c6c65000d5141300b0150015503850b2100400641100903a0036100c0c14407215155290141c0c034081900030f00c2451030b143c056502d50b940001c0003029039198100d2900440318 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 447164802 1250 447163552 447163559
    0x20315151e04050406050d0c030308150a0e0a0c0503010807030f06020714010506010e0604050307090b220203061003050403120519020d020715020a0c0b06013005070206070c03050c0a0c 81
    0x1e0310041003610000d59013804025255000c0c00725401c40c140300140301e207260000c100007080c0b08164043d000f20302102e2400c101c0b020b00c00065130112003600034421a05810081c408002002d01c035900c810085030500e03600755850200701035142d01841c400500842d5008104604001e01903040310411944103413041540007101410600070001114242c0c0071410390390310003e0b64a0140107440490f03400400a115040c24038441030081d200510140703801c56400b441031528016413204200310144074100c0140c40b031424400700721490146c80e4820060514080901c00800d6109025003001c890082c008503c64540340000300466640780b48224a80d4400310f0103501c80c0104d40c0091402da40a13059a1541d0780300c6400d500b0491003035440403c003048640d240d210000d81c810010030340c884014100010340c03038440741e0030240d0f003c811101c04c64506d680c002d00070300e9200d0034030030540c10100302d01c002d000748d00d42808003609041302d02d071001e0240100800e010071a035904007c2003140d260320500400c0b00c10368 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 447166052 1250 447164802 447164857
    0xa03050f01120c090b03032a101a040e0c09010b0a03050618041b0f0f03050f01020903031603090503030d0e01050901092307080a030804050706051314061b070f0902031515 75
    0x3170100b0008c000e4000c07081000c41e46c111501034180c0c010389420240004950752410040181081100a00c3d2401000c2c5100c15a5445000840c000c00c41d80f5041ca60743d001000000b000c8481c0100401c6c46100f404214100742403583c44016813082d40510241c400c905e07186008068408503a00400102d0303464440880d5090070403d03444210f92082040f1816412860340e228283d0040c030714030340e42580c01404501070490802d014004054000c0c00e080403420344036000b2170300b150710a6400400e0191101c1d00000c4e45002481034951041c03180000b000114001d50703901c60200c40300c08480440e00348030286809118000e01c0702900415403c82181c0e2401007500e1701512140c402c68080e19580500d03c40091914080d41c00c480000030007002040300c0798200700342030032940311400a40c1d82001381480007080034041541d4102151805800504985251803540c18008019030403011082e40140140b10300302e0000001c2c60310210381124031902a4400c01c480d4195400ac0002601d030030040c60690020045 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 447167302 1250 447166052 447166117
    0x6011b080d0e0303090604030c150c030203041203020c120d1805010f060e04030203220e040c030c060c2001020c1503010f050a06020a0303110903030a03050f01120c090b0303 76
    0x104807550074842c403801c001c0c07115140d01044580404070781000c00080d0010384581c2000c40c179203100d5851203002c004c0e10048041215922040c000200f82d00100384801e02c07010031140300c4007200c0e520b400e51500c94039020344d60311307640422545070000402180d50800c0d10b00982001010000064440803400c0e043c3c101903018002d00c1507140805454400007044200c6451411407150750140c0085141424a06422840500790500420b20720305210002c1400650700c80e14a020394001c801d000798007411400c160b41904555800341040c0141c1e1030319440040c00941004540d01e00d040031420403051045d006070705000501d000360b94410340300791515041c4100003000e141030702e0700c001e417520030795461380c050040d04030b8030340a981c0140c0d00c06c1800d0400640329801090803aa9810609070419007443c020a145402803483c0c040426211030803c03100300f410314002c3c2d00401c0d1140c2c0b80d5181c5010f54a8107400e80c1240d0007038a031420f03165084080d017500c0030801c8401030200c403003106100b2030303810440e130f43c2c0c04 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 447168552 1250 447167302 447167317
    0xd030512010b071a09011b020a0203060106030614221e0515130b030c0a060518270705120406020909070c03091707030b070e101d040506011b08 63
    0x1400c15800418502d007070405480e41d1a43c081c29000100c004000c814081e26001042e4811540d202c000c0381800e8207040400500801441d0010714120041c1d10405081c920141c002c0d07010549400010400d000020080407d009000e541616207002c0d0a0181c285148103084441c101504000c0310551002880d4084600d4140070242000300f5281d02d040d00e00400494240640c0c80b8240d804a5445594568018400c4150041c02c403503c0004070070100340460725950050300880c1e0040748400380302201e01c801c0140700c04126011081070101d407409040c1c6800c0780520103c40b405210014804074041d504076500f04901003c010a0fa15142c0f801c0c4000e580314030486401104910003140015004008441d60280c3c141c07a55200c15080c400120351061800409900380d2050305800400f003490700d80c41c207004220540d20302c1c40380e442100610a1b46049010000700300060b503800e080d044a4118001a8841812100450b83e80c99440c0102c581c101e60081c88030104034084044030030041100001c0049 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 447169802 1250 447168552 447168577
    0x11203091d07021b012c030111030a0c0908032d04030c0303320a02010b1201090b1e0403080a060503010212040b07030905030d0b030f07030309062c0f0f0d0305 70
    0x520103c03c030119a1120300c10704c1ca90100c2c000000700c0d44802082d01582280c1101c450010a0000307018002070300b901c0c00d0b1610310041c038100006002c0241c0035030007010035810450a100410750314003586256070b03210b801c42d001841004a54a02e104649056901c400092807210450f2560f0312810184684052407000303d010070301c11403412407280d100000c201c1c14030314041c01900401921004030101540084241310455607200c401800310794072036444880c400000340c00011424014940740c22141d4001d000700362001e1072002c800718070407040341000b0f178044d43c14901048561100c104140c098000b50300059810350010a06119a1102601040c071460061107865038a80300c00b40143e0440746d5030400905550800c100c444082241d94000c4450100e001c2d0444070012100c01c481818220a0303041100082d124080401070715511102010074500c449050010f901c2c40d2010b00b0f0030958403010784a00617000d80941c6c1e2141d941d000420304502d42e0144c0307074201e045c05034036004019503c42718000c0203 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 447171052 1250 447169802 447169813
    0xe0603011409030a0c020102011b0801090c0804170d060b03041203060f0506090402070c030231021809070e0307140316050d0305030c0c161d0906011203091d0702 71
    0x4498031010741e41c0900300080c0594980488240f00700d61401240d0016415592100100c4401a080000b00003881c00240d852008035410202c1c483c0940d84038100310340411203d00113000120300c14001140c19040c082803000e40d144640c191000c064029544403841682020041005000c000f521000000e0000e54040282c503886062260380314600e80a466040541805260124101a4018407229009089801c8141d960384d00068500c4503000031401d6481d2890303900c481c1003844030107940003015642420f606200460030001c14521002040038455417416000c41e000d14040c441c52146040d001c0c056440c5691124003840c00c011652604600910603555020340742072015040d44141d56000303111a40043d06038404942c181c001500c541070f4804104594600d0510420011218104000448a0451601c401034080100201e000c003200c1459408011020b20302060150550760203c028010390349032810f04035100748072504260362070a680c088102d044004816454414210b5a003181c1 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 447172302 1250 447171052 447171071
    0xa0209041415060a0210020310030b100b030402040203060d151a0303070b0103080f04080f0c09181f1523060f031612050412090503190b040302010603020a0e060301 72
    0x204212001c64045182c00506860852640f81407002011290100d2040703403000d4000e0032401c4100d9205840114440000d43d00400402590041c4a0751000e5140d281e04003052034403060041c0c40c840103000a2290350700000264640d90f8450700c0d604a60f401603541907007011441d8180009101104000d1800f00172000f649a451600100700d4520380da00503a4850240d03c3d5941d00062604603a2401d1000e001c144070100700654100b010301c40f0100c0320700041480d1201c0c2000c1c0b01039101c015041072854644500d00c0c2e441000c0010326400105c0d042e255070000c006804504600400810b10090f003d0501d0190004840303100d07841d400200604003a0012261f03001404005440c4104650414003031000d20002d20884080d4025030056032050410345806821030079624101c0344201d8003207401c0c10620039011142c030780c040385050203404150b000307010481c10a40f02800c0c8510380300b4020200c018540008003018401c0d00103000856020384588800d50b11000c0d080452700041352114040d62805a4aa = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 447173552 1250 447172302 447172331
    0x1b0a080d0c020f0a17010920032a28140d060507020c2106060a0807090906140405100e16181b030603060b03030f1b0c090a020904 57
    0x6000c5030040c1d00d90340c1a461140e82803008210086419542c03200010000003035400b04828850100c1c9007080000036129039503d44600d0070b940000041d85a94094440c589032910000760440041004121080840190902da045402020103040d40c10a01a552480300e6483e141c626407911801c5c4c001b04403440d030f1580030003841c4c000b40b0192141d002554204d848082040ca0740b080f0381028a51054809107030380500855100482a000b03010890740b40900000c5c262028440c0d5034029500300c650321a900d14041e443c0d540d92a203806000d1182b13549103402000c00660f5404000c0c6203966800754101864517042032070b2520381d48400c190407282082080d281d440c00108d001c00f100009004803044540c148050a802c80d5420701403201d0741c50313a8050054920282c1e00b2100d0060300d103607030301060140c190301d495020780703034410500390003680140029801c0028003019520202d0744403031070407036041140c100d291400b080002d805801840840900c404901580c0003050b098100b55018400050201d041 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 447174802 1250 447173552 447173563
    0x7170102040305190308060d030207080d0525150b01030902040e0303100e040b130203010b130507021603261201030308010603061401020c0111030d050f0a060b03160e0a081b0a08 78
    0x5d0010348086c00262403440c00710781c075030851070003841200c60b6181c8440c030180c980103105603801c1c0494400314200450345c4000c040302c0d8843c000500d60504200c2c1580d1010b2007100b0100424641c0c0340c550079040031a074402c2e4084443d150b00280280000d001881d642602c0368426112072003440e6080f0000f103202d8074900310b41802598815002c000513514021003070b11408001a0480e491b540350004400c2c01d0ba910070301d080c6040b04407100040c407800c0c80c07180a403404c15604183c00c0e80d10b100e58003c00c041074a0311540201c100140c4140e0386403031041c2c101100284280d10311b070040c02c00c0b00d5001000741584918964162443d0b41c0341080302e687c451800e0254400c60000641c0141d020100307010740d5501c142d0a0140310116039040742d090001d040e12210940340d0840e0401c02c0003030400200044156103000c8c7c10000c0c500f4070940c5145040c1581c1082001050403405400e0207000b01c0300c044aa215007010200410110040e51000011142c040582c194441140743c4140705c0101c0114030342034081507 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 447176052 1250 447174802 447174853
    0x108070e04030519090e040c0509090f07030b0421050433120e0f010504050c010908060c0a17070309060c020f0312040206071722050a05040e07170102040305 69
    0x15403d00744590665072110184c60712440400300030f030305440001c0300181e208469004074441c000856040c0d0601060200c1d01c24002c01101071a40110b1480e2490f0740e0109114050380d0308110341200590f0b86d41002e500912003107000c00c111400085500d01103540c8000540240d03561409030113003242480b1010018206984011015042c604452007522400b5490317100c203490481001140041c0c010054500700b0b064400c5130103240c0d445a0400080040034020a6252442402d050800600340425140d0320900240b03048180000014000c2030b15024000840300510100f194004600e0b2854009000d030501800486443c3d0810f400f002e502c81c0003040d0505403503403501c003d6040400617050340d801844c01402c1030340c10001c2006038801040d4041043c00d44a01d805100076540c80902441c1d92801d440c040c0a540b505032919800d1226a030780c850444c0480310304035400f00300c40040050603400e02400d0350040585c10038106400b56020810b40140c82140c0c064000c1d9103009800081018400107010b4 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 447177302 1250 447176052 447176057
    0x1b0503090306180c06040b4e1b0f0c011e091202280f0219050a0b04081e01020c0a051f0e030301030821040b0a05150d03030c020a17030108070e0403 65
    0xc0b0070070001c488d110f200220120018070a520020300c0340c6054008a01c00e80105141103090740a1911054028002ea60410914101e10400c405120020380080c01a01e5403000b452100195040e002c0c0000d4100c40c2e1342c80c3c1c801c2c8050150106c042d1020300100f60741402200c1c4528222100c00792940046000320030342010100008070180682c45000d40b00e03402400031140d202c1d19902c14805603c50422200000701d20000388968213041000304000c5540c01da0044a5602d01000140146c01000c01c0d400055100000c201e1800084502c445002e03010f51601c0d02c19910500d9048000e00c0b03000101d56500f81001500e200c1000d0850340783c0000c0d40c40104a888a0754010401080002c4980b0300926040003442d80100052003101c40301107031208288e9040d50b590060000b4003e150000388241c90b00012521000368155005801040041d007a149016080c560303201103524210b80203114800c0030683c0301c003804208107012106403495400a0090404a12804001045821030004031754040c907050f8 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 447178552 1250 447177302 447177307
    0x22b020a080312282c191101120507030603061a0306010b0f1c0605031501030f030e0a09020a0210050a090b16090f060f030c03020a1b0503090306180c06040b 69
    0x5151490601c0c03003492001003000140840c100340080a8842d034030805e95054480000c41300d0400f1501d803000030300704248205030840940b0082c0c004000c495804469804001c40b03640318007003401078814001e60044403966904100404c030905034141d0114061b244200010403280702e90306140e140d038488498680e50954803910043c0440103a10003e402c1d04107100c1c41c002e1601d4000341008000c01425443e802c01c036a11241e05001c241790500007001f984000080c920200d41c95612405551800c0d1700d006400e0052481c0d90465944400032000090145039600f913640c0c0703062180080d80d0b000049440500f892510021800454aa0144a162030b41040c290451611808007011240c03043c00126428840b00321400101041403004805c000c0442d5100d00c000141c4100e40501614018a05041018410044c0e2065541c008000003520708013081e8000c0321064500d8011324500c41c0880d10359062040e08100540000024a106600400501a54004200f640a1194a0007140a15510300340706 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 447179802 1250 447178552 447178561
    0xa09051302010c02030c1809060c0a0509100207210b090312010302010f02010b04050c0307260109090602040b1216021f05090a150e0d0c050307030507022b020a080312 73
    0x640c4200845134001010703980c8905403c030008a0800f003045038410400311520070080722500c1405016441161000f1980c43e0221b0070400502d10720401c11003d101e000900450800f541c8204260743c0580240a000010b40c40c40901c20020b20181800413501d41c0188800104840c00200030b85450030340502e000c01281e42141d0054035080030302e1003c001159a1130501043e15a0b03180603803030003203540483c6c0f0340d641e0074149001800404481190300d0790084170072010354851414824241143c110b0100081d0006452a08502038417650b401356583c0c40d00032070111414207603004618040c00700250701e002c810303403007007010398032080c403250340c44400200c0f1903020500c144207422040d400b8012500b50340b009807141c1da40c221741540d00f003e4141016510511b025150008020480f500380940c100762001c50410b944041d41c038880d940004080040100705001191a41c880d40845400300c00e800b20150b500324003046000768902c4005074498200d51800140304003001c42103030a07070f280318004000c03990b48 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 447181052 1250 447179802 447179807
    0xc010b0f0f01030513050d0905130c0c030e060f0309030417070f2c13151503150e030705010e070501080105130b010e1908070807050d03030c030216030206060a0905130201 75
    0x8000b401c1d1040440034244a000040d4144081d10120001d86c5440848c02c2c146000d0111001c0896400701c1b13240d01e4408012a0241c0201c000b400c00c40e4103180842c5035000800101e0091b024621a010141030f021041c0b00c40c3c110048084c10943d80940300c0c918008903409555a40d03565940b08880c191010084c080c0300005504004044501c142c008003040d1205c41010f4105225007110440c02041d0184000010040c14400501d6184490704041c410b880b035512819411361003501c0000c218031078551618a01100e40e070042c0004003080d20a494443d5050b082c0380d070280c910b80404040c18001c0c140041460b60007500030034141c41014140401003000480440700400b000301c11181841844c2d4480940c90b510000303042d13826902e451080343d07283d02d040744592900d500740d0440c51140e000040280082d03146e07180070a049035094600801c032070008a000b9002441481021000c0f0b0002c144240207054001075120b00031281a18140701030380d50381016400701c1b0400d030760302c005050107401c0010240d031 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 447182302 1250 447181052 447181061
    0xa090e0903040312030c0e030c031b031c091d16030b01030f050712050a020702360c04061704050c131d010b011d01020606040504150f020c010b0f0f0103 67
    0xc4a110803289040e8a0781c503a40740f00030003100760300002501c4040001e0040d80c05031a041800c0403d50080c07081411982c0003e0319409031540445551080f140002e50301e076810012404a902d46a031401041e04103408014a140c031540500c1c1c00c40d11a503009603d46580f03c0c03454910034810402c01e02541c0e00100070441c080c21808080c3c0d030405403241440701c000d8003544222030049810b030b01c07640d40b400340014604055031401490110007510500c1b4041c00b40c0c45480c0c8501e0400858460300d100d0440342d10029072810600c04030341e403d0741900380420009050000050041d01c1058542200c0c41500354003c1482d03600071140184a5006050001458100080c403000c041211100108109240e0306807a000142508824280303691100d113016040d5800c04040390140c12a40e48107420b0211010003c1d50310a0b025100318082c1d5650780004040c4800342c5400411646690130600c04c03204540205030294000c491020701a51909010035946d01d441d0088038032490010344440346a000110042d4000c1 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 447183552 1250 447182302 447182311
    0x60f0816080a120203070b090c0117090309010c050a06020a0c060506030606030a12140d0603030f18270903090602060c1c051321080a02071110201b0102030a090e 71
    0x10f100034031200000451f50380580c1e100d0344a02000b000c2d1604842d000415140e000e9000f5220716845000380f10300e09501100700d40043c9400e003484c4100920310b2034070624008010b9800b50126102040312100c5c264404001501c150040741e0078090394940302d08050700da00d0103982e09545623101c4190780001030303000091080020317407a051a442983c0c04000044160f4070219117400b400307a8540040c01090380010440400c1652440c0407139200c83c07206024400c169090298245001111001c9001e8500c03992020b445500d55420a000c207100500c2c01500c1690940540c1d009802448000b070a062414000e8602180100c410f420b8172068061024000300703405041c1e074120200c0c0302c902c6400704400d45c14100c89a01807191010b0203242c0c2003c01840c6034405001e05000074010080e80011401481985a50000448a0410a00e06a9810703030b0f20600342000c14064194040b0280c5100c0c101007550814014415545035141003110012620380c45207500d40700120704002c1c0c080c0444101511501d500 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 447184802 1250 447183552 447183557
    0x215030723130308040f0f0b0a030e010207060212041a06060702210f0d030f0b06070321050a02070515070203070f0f0b0f0108160e0c09010c06060f0816080a12 70
    0x2d00008001c003020300c000d03681054814440c0094208212110306041100400400764081005420043c0d031380c45504c180c420020400d601d503c4107070720500e401c4d41200c1e15543c2c0130a085541d80101c1c20804d40441d401c403002d071658490f540d05c980c2450349155285103e0b40707000f0501d07858550740d80e003080b805426043e08500c01030700390084601d269100704400f454400350380b0010290b00780710b4080281902c204800c182e4104d4108281080b032600c1c0c0106880304180c3c5030408090001981d401100007600c20711145074070302c0c14501840581d4419500a0014a00403425200e0550301040707601103460081d9407801c0140d20400821010400703091119414038814096540091025103d030300c030000080d00c041c190720400780c00400a844c400c00224038080070703100310701610300d21b0100c03a130b90302c0039000304a0b103200a000140b2000d01d0b80b2401c1d42c8040c480e4045020080c1e01e40303480c0c0703030504510b4078001d841a03407040c2c08480c070340c801c3c02009003000c403085200100080d0040755184d0200000e00f0203280203 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 447186052 1250 447184802 447184807
    0x3030c1809040303090506091f27031d010215010b1308011103010501110d02070e1008010e0a05061f0b0d020d0c110706050a0504050f01020a0206040303020a0215030723 74
    0x40e40d101d60006001c0c5001e40d40100b0304162604107a03081c500081c1001c1a0340d88107001c400300c01450f045801c80c0c40208080d00140326281600d01500c0808140c0b40303c01400300d980914000c050304042d000b0074090b80e8540b60340d00044054010399654601181d21940c0c030310040010000b4010030b50003080450010200613181a0740e90281320700f0740f03102a156150104c3c000c0014081d9581c09104069815074100080c9000d000c2c0c0100a07403500d02c0c40c01054141c00f003a074005051400d000d0b101e28001c25101c8020860040c2c07490010b515030051007800c684600924021030703460030000c844040d85003075202e00b00311910326100168280358001640320344020303000e00a55000748024828007014415a03180d07a15601905280d140c01d0048582001040c0901031209900495010090b20700f5194250b4003103116400440040c0d1401d000d562000358030800016002c801c1580c00b00d540d041b9035200b0784200c0d40300f070b41c00c0c184502640401c0b9403983c0041e281c02c9840b203042c400c580c0300038003000d80780482c0392 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 447187302 1250 447186052 447186097
    0xd0603050d03020c01050c040506030f10050607060509010c02010b060d02070c120b090706050a02100e160612150501120c0c0c270204030f032115031101020f03030c 72
    0xa003007850340c061034000319902064800c0400801c0c0142a402400b2507174480c646810200000c03d14003000e40402501700d120030000c0d50815102c0c84c0100985802003046031a180d07503160810290208a42e00d07156542411a08400907005002c0c4400401009007031a003018070ba81e112100a400950341520510548180011040d51030588281c4440c007507030381802c2a1400040303543c0f420003180d0020040010401072801078a601003a294860810340c000802c08424080305c083c0342c0341000880b1241049810000152140c22040c4071100f101094414401e40307001814403070364640d42e807003043d0102d8841c0c442d06a81c1103a40c0e000c101e05e1001f45c2400c429180759070301d03400b0105506800444404101c1c464030f148080c00520741041d2500003890651a0905542d111600c10103680320040c1400b00c40e10f0100616031a225550340e20203c804810800108480e00b1400380c0340e0144029074584400401400c3c1551000c44c0f600540320a800c021813035512030b41400c5202e98010f400742ca001076540b00000 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 447188552 1250 447187302 447187313
    0x10b060a0309060e0c01080c130e0a05010314030405031005180d08010f1406161509061b033606020c01020714060103121202040e2a0c0709020d0603 65
    0x20800d0504954000072542c20501d88007040701c0304d6000c0001550300c90f40c0501c5040e079002861607440b4184051451701d901005400111403000e903040700780440000800c001d60500d8660001c2d04a9018511400107080c1e0108a65103a104030b002c0e058060700f0444800126a203140c00064001c40460340000100010340c403040d08005a480c400b10000346054010030540101030303074490182407510030208041c66002c0010304148030712070488002c0c007000d0f00d0020910000403102807809101c1c1c8401d01c0700e0f440d60f241500040500040d0070310902d113040ea4254605110748035a07600200243c020700301c0d102078095008003100d4032a102412811020074007400080090024220f5400010005a20f9030b43c0e514080d81c2298400020542c10b43c401c800401c080303001c5400300e00e550081424042c0b100f100f1118690064030842e004071055007640410300c89280a0000b0840b80a801c1010100306040c048035250098811301007141110b60011000340203840c241e80c020603542d4110200000c001d941c0343d680 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 447189802 1250 447188552 447188557
    0xb0a08090c040c27031704030203101404030e150706050a050c0a0212030a0906050f180c0d0b0a02210405100c08010306050603010b03121b070302030304030311010b06 73
    0x40000251002051088148080040107840a4111803c0c090404004002010030303c001c0071003160805001c48940046000d80c410300d01964004074860760991241a4094440d845803004038080d201c1c1c4507011207107880038451004200c0d08400741003040c1e20b45450440d100343c0400546580700079031018060440441100500c4011b00c2402d01103034619150444d003084840040024966060401601400310750100395001c0300059802804d403662641d04803280144280d00340106258540001d000100f07650340e101610640b000155074903404061b010454489800b0000c250700446100c003001e0002c1c21241c1e0303007a4465003040e001401c0c120115903c141404244188501c500460b005120038040240507880d6082a12001030150181c4510000c004120500c00a04140d580f90301198103940e081d00321250000d0000d0446003800380e003034a9803041e6804101d5041851b044c0785d5100e0000c510100d0003004903038000740507500781032860301c068071600a8946150000d550300d0003880307101c0c2e598101 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 447191052 1250 447189802 447189817
    0xf071e020705040b090f1f0306181211031b0114131a090c040207050a0203070f06030b030f0d05220303090e18072601020f091f0507110a0b 61
    0x4081c11481c0a0078801140c54103100940202d804404000030001d03148080c0c0d40000038500d500b40304000100741c0745040f07451504010542d80c2400c40c14110b05100d8200517101710701900100502c034920000603203000390110090107039074009000c50b071000c100510002420149040010401441540062440020882c1c010450105140300c41b000d20140040b4248420300d4000180501e00b0480e0b146580c8208004405100701e40000e006000c2007404e015115150360702800319222152144c51880d103549443c003a802c000391070040440902c8c81c0004110b00b1503003c01000d014490aa440c04940c0340d402100d00e000b201c0c1c0070360f040d8200702e13040b904420010b50080e070740ca01c106130400e2025505402c0190500084034441c2c0080d00c40354102090000442d490030800d070f0b0aa82d403018913216268182d24550303181d94408100c4c01f904000c0f41d07001740f60203041224203d0340f800d003c884c201060b8010311440c4001032000c1c0104c0000070410028044480c00c0207001210442d80e5016010040d8024030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 447192302 1250 447191052 447191057
    0x302120a17030f07050315190b0a0f030c09060c0213091a06030c0108070e01080403090803130302041103010612020c120309010902130e0c060f04090617070803030105090f071e 77
    0x41042001e00d020306280c2e4000255145c0f09145041c40e030410b02181903900392261080411a4114002caa21640100000c0140c2e0040d030b80c840030f0311600600100c46012880300880d00346074403400c51a115000f407106807181078803600b92140399502440a595049000b91a8055131802e4400c0486d0343d1800818940016098007034a43c50f00c0c100349030802c804a04d1041c1886071800600010320780181001079484400e19004240d65a541401c90321032096a100e13203164080050b28402d00a0b0300e010101c1503d000b5a810f100d0011549445242e0340b1091090381c000550108903048001104d0b0020240a10418129002d8445807000744a040d8020ba5604201d0782d9102e84040850070708a403100c44140000030100545040d00300440c0d215500c030740c071661080c4000104104501c54150540d0042e0416980400040d52603808000e1050500030410b20144205040001d00328000821a41a101e014000e6403250304c134801461843c103005092181403048032245104603500ea5018082e4a54255 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 447193552 1250 447192302 447192307
    0x13050708060a200409022b09050f0a0819020a15090605060906010822060c02150c04060c150f0903052703060412020a05070902030109060605070201090302120a17 71
    0x260421048843c8001c80c406044026110b10403c0e84145081c0c4045490882000d1303610002001e015004840c0140342e110110001500041440c059501c4506214415803c49041d210000d0010707a076210751810040c0044403c2000c02c1c07407101c21800201c044151401121f40d001055965050340071401d00705c81509a549e5514001802082d00405070410001d136569041030400c0b0700001d140c010002c0504c411428916401030b0b01060260b100c40c2e809400c8182080700c05d5141000a4076034070002c0e60a840c074140c280106180d0088202100c0840396191620084805c940c2da407002c00480c03903000c034485655140c400400c09902070080038515880fa503900e545c2c0381c1c01810711547c158240c02070600c62620b00c5907041c5468400040c0c840d001508080d01c0c0804200300312049240480481c1c00a0031402035142c0090145a5500914180c8605420900126448000442d9180074200000c3d0005406220402c05070500840038401218904241c40241c4800d8a503910045211110a5080d0000 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 447194802 1250 447193552 447193561
    0x1020f0f031801181e030803160206220f0228050a06030b09040816080403150605271504021804150f181b050702010f020d12051305070806 61
    0x20ba10444091a809081220030100d19a03840540420f050080460302407418049140300010540301000856101e176906a5910b001659110000d07401c2260f00094414440800c80c208031004e0044848502c8102101504500785c48480c4266001003090383c003d18844084803112800c0c002521180c48803812100f1681d18250901c14011566032240040501d04980a6200d9607090003254100e50030008160b260304036251101b44018601c00c008014080000e000030421218623004116113601c040c0400034544d84000f400b610880c1400100c0381d035500d4070603011180f000903a0f51303900036001c0c80c0c000349002c403040c000c10100d030b10100540c0c0c10014960401880352910740140c000110b80320f50b50741142481e1100c0960075124600030790000030814036100d81d255040303034040b8003026510b42205804000070302d800f070007562003a40144c0c0000d025200d81502c0c07900016421407a83c50a0765211111501c90303032014003d1070098a82802e01041c08114404100104407910161202030302510350f5060 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 447196052 1250 447194802 447194827
    0x30b1914091b0a140d050403120e0703030509210f0c03010608010b030a230d031b0903050606060d0b060c1c02120706090618080d06090203061e01020f0f03 68
    0x78000e04a00c84040b640519100060948043d541031911500380620802c020640c1041280182014510b241d85002c080106050b400800c0351041069503104005d050184503005481d4802408050086801000607a040342448940c8101c2210080c440103003c03944c0507126401c084907000301c1d4045a0000070300c004140f800380704010007410a60000c00c15103200303d0100740c45040703529000c1c01060f03803080100303107444940700ca80c2c55007040b05043d19400780300d21201130020029020b69000340050040c0e42c200c824051882d2034290782c1c203e80142500c2e51a2420042d00758440b1717844482c1d05d0b1300e900c1c1c40c3c290b588276140a4100c4040c24000380000000c0621849401c0c02902c040004662020000c44071906085046030f01c424cc10840c086130406e072504208002d01494085083c9411003d00c0c0e4030280201c3d2030240030300ba1a081018400140d13141e4410041c2c1c003069414660105901ca8907101c82c00078480321500c84030060060310040300c0c9c8100b1050038016007040130044c03900006804941d001 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 447197302 1250 447196052 447196069
    0x60d0912020c0a050901060c15060b450d0204020c060412020703030804022e020c01031109130b0301110d02090a150f080a1d010608100b030d030b1914 66
    0x6100b0b07140b0452451401300042c0c1c000304180300e070409211004100c2d8050100e16000303011150a164414410f00ba40c6041845241c0c1c454400400c07100c0350300b070240010000c20b04031400082ea112014503d092480100440e04509914940340d10003034040f08500140c0702c0c1e00142ca80030f03a01801074a1546440d091000205000d80d12180454014602c01e01c0003079000741d10036030001d405840402d1400d400c28001101031540c42480700110203c261044d8010782d0020300d050342e114007a030703041c09050f00004418007980100b140d00e5a005202d202c440c1e07144540c641c000d0f40765260040000c42c0310103103d80c4800c00e03a406600000c14054000031020118107100102c40000e20a03025000790700c0f146040010600340369060003008000d8158041413650b0301075041000308040172041900e80408110b422030080c0307000e225910150040c00586561403800741f0513101d00c40b0015001c0c0c2610b41140400b10020602c40854641c0840003240710f032000c9040801e090701818200103030001c0d4082c1c0404004444 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 447198552 1250 447197302 447197323
    0x10f02070f0b031503031c0b0a0906180f1b0c060612030503150d0f0618050609010603030909020306060a0c030504362915030c0310060c05120702060d091202 69
    0x3d1b0700800490040c180e21803680c04d04043c61420006c0e00450810000701182c1007a842030050070705203880864000301154454100040f01ca0081002d0048a00c1540c117542d0046414456480c3c0300b4842043c0c01c2c000e007105e03070348203100b400c0026080d41ca444803586100107940058001500c04000c00144907104105104220400c50f801281307060240d8510940340c1032224020a00380c1c03166140740f03800030b0342001a1309080c0e201c02034400500d0440d04c014000d108620040e000a03001400018280400740700312809540301800c01c5240940656007501da034400c9841c1201003100030480040c219140c0240c4124064810110000b4445c0200e168040820300030a042810362802c20000c1c122090001101340d03401807e030030303044458800400906403007640700c102c1032101c4e07000081010f9008460015403145461140b2941c282d0f8860b20200c030945441c02006145500004140d00484840000342a070244003c040c0c0d8500015080740b1419035406603001c82e000303941c1c00b50b03602c141c0d030b0148440021f0 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 447199802 1250 447198552 447198559
    0x4051501031e0807050609010f14010b0706020f040b0c07052818110705031213050604390f06030e070b0d090209090d0215070e010f02070f0b0315 64
    0x594155182d0b0400b680340c80c1c46810440b9440880396080241840035200d0494124095480510b480301c000b40c060808d00100c004000d00d00f5003031420000204545a042e64031206040d41441030302c2d42d80000940c456100e00c0b042c1c030401d0000280030318a2100a1580c881d820018110240c50308007030011541005480484241e82d00c2001e61184038084900c1e03040310b001580c1c101d01403180c0d05100c4010410441154226140001c1c2d12090200c000020114a03260f401100800d686019500c0798808281c07000510a0700814003103800b0484c202c1ca0034403840058214038081500e9461b2565a003441c0d031030100003010043c1c00400030119908400c0b030040040d0308060019400c001d800355101d6206005a1050000225600125541e585d00c2440f51550180c0321902034100200403a580d0881284040014419801e6a001c4190541b4a240c090801c0d6202d02a04d0103680c0300656841d0f80308005e0504500ca9a000001d941c003500030200c00034104d0703800c203070365070700b480310508000e0039001003224007 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 447201052 1250 447199802 447199843
    0x3150d0807031d0f040c1206170d09031502090301111603020c0901120209090309041107120513030b1e070e01110c0a03020d08070b070e030c0130060b030f0405 70
    0x82c1e2640c14102a10b00c50498001407041006c80080d40c2c807201c044c4058500b18079242002c141000a5482c6036141c035801c81c1100c02840e444041211014841d01004100c64481804a245c0c3c0c1031076005888a200001c00100340800030498801154100d2460301818900c4120103109058050004c011007100c00e480649442d03041c030412540c014541d1800a0254024400090b68440140155614090005c2050241841a07010700860f600400c4098074480301d2084035000c0240a4411107008840c2042007404c0a861a2550100b001c8024105031584507003201901604941ca07012511415041c2c03602442c200e20000014414600c20f04410303aa540000c1281400395105194034080301d9040381c0d404418065490407240d60700600c1c00003848090002c06004a240e081079840003180303415811252104040d800458000b41510081051448101048130304a4150184114414039800700420000e5880b0390f2210984c3c03003100d0490341c00d6848410310040100038011b51a541e02e04402894 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 447202302 1250 447201052 447201107
    0x8160c120b063d05090a0f0501081003020a0b1b100606090e04021e06160c05011b0209040605061815010801080303071d01170a0c030e01140a0203150d080703 69
    0x110780c0045514903190186840d140c0f040d18a126400725441c44402422081c034903a680c40101c461240d4500899011034560000505100d00c44482842180d800611140d0749900d030014218081d803040d004103014181e490000c0d03211503010030141561103810f000c005102460102d00a01a5181e40c0004500c0c011000c240000360303485035403405105200c0701048803410f500700000750f00c0c1d204a00c7e80c01d821001c0903185405000340c10039014102c51081c0c807100b1f03c1103202c42009038030045a046c025401080c0c000400c01140043d40540d0340040c0180407000180350030a44d090340304c041200c640350340c02482d0f0b1a0980550344002c05900400c54040210300798107060401070f10700c01090580c10141c065030100c81e025a071040700002c2d40d12402020401884c10705402c81c0024001048005000c24100303c900c0e084510305104034023032020400c4020350710780c44502b4100003940c00a03050f200d038081e00c001c041c02540e40312300b00b5244c2a4411110780d40d8442031881e02502040301d42c440c50040750f603d10b01030b0 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 447203552 1250 447202302 447202369
    0x30f010f0504091a06030f0706080702060f04030c140c0d050a1e020102100902030a0b0405010f24030816061805060c091e0d05010c050c0c090408160c120b06 69
    0x8201c0c0c2840a81034081344c0c1c0ea450200380b8043c100d601c45036042c854060002505608401124003138540e66003605c51660383c152030010701e0b074421f503001000501e40803c000c01003030070410162401801201900c2c15214400d0005884940da60020b84268001164107000c002600d141e40100200034070001c1b100707180c61703000030752a0500c100700c21640c2d50321a509601155010300c036184540390310038101c4202e07007404e0601d28004c1c1204050715005070314000700d29004030104007070303428450350a100407000d076400c43d52140015003021090000c12000e198028001981c40e0040238010399609a450b007600320305080c42407800c031004d8505c4c4141c3d4420404010982c903581034071408030200300071031881641500013082d0309071412000540903510f80f1101c43c442542c0100201a00f900000c21121584000b074200301c0411002d5600401c0c1305c00030400e10b030748281000300e8282054080c0b210340c40900d03520f10080e18001080141119420381c40c00800140e45402c0d80c00114080b1400d00240c102c03044103145 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 447204802 1250 447203552 447203573
    0x3210405190308070c060219051b03010b03030706021215030a020603070c02030a03081b0f030f06060408011a2b0813090e03190206071b060b0402030f010f050409 71
    0xd2901500480c4450425911403804840085034068141c030794801242c108100c0102c1c036805144014025144480386c0c800c21003440070401a0060080c0104100c00e03024004020289903440c0d4143d52079500e85640c03590240041d00385580220805a503a1803042c00c0c140d0301c19030041100412044441c0b07079904640340003071015405a41038520540d0703078480c66000d50b0003101c44d4a0007580351242e61881c01c1019408610340340140401075001248440c0a81d410b00300d4050a0046032070b0400900c00541034401d400d020326002000a85840e2034181c480c288142596014540c14a80c80b0340101002040d00700b20300e1000c840b06080050110b50010300c0210b580e040740842c40940940d0740824045e0802030450062001403080c060100304a0342c5100c06192030303411900e00030b45a4800c8904a140140c00464041e1280c281940d81c00081c030f5060385103400702208a00191b6495a03101d25481c2661200d20041d0b0251030305814103001589864010030203c4203e070401400b6070b040c090502d0004541041 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 447206052 1250 447204802 447204809
    0x60305010e16060318020405040f03021902010c120e0d08030f1e15040f0e0f06100806011701022104060b011107060c02030102090a030f03020d03150902070c051905032104 75
    0x1004101901700e0f0101002c880060343d800780d80146003000303000802008a035060201c42c0f1035002e40340c107441c4c0d00b0000c0001c4403c102002e4081121010401c0010704601906003400401d41000143c859600d4003154400c0d54180e811107846000005000d070b8054400d0380150f001c1a140c81e90300a0001a140644083c030000d458041020b00f507898688040e62103422008450503280310403c00c07445203851b007030b42e103107444da050700d545004481c0865800e01240b402502990041001030119910b412581341060007021200d0049541c00d0104441c001301501c000000382074400c90350070181c181824000708507103900d8400d030f040c8070f408960000461808581c81084505509096000446500200340a440b5401060b43e01c50305000020040100c107080300c80d0100d01076400c4880c550100d200550454030301c610921100d1400b594208800c103000c0c3c00600080b8400c403104201541d803603000c9944e0010340c2d6004ca8145e04010014041030030200045000c120400e0302c0100c42c100034200580c0c203480350b0300 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 447207302 1250 447206052 447206057
    0x60403080c0109060f020d0605060c03070201080705120a0b01020c032107020109090f0501030b0109050601051207050c070b031f05090402060a020a051213080c15091210060305010e1606 81
    0x40d201c851000a5020442d00f5810207414002030b1185801c240080d80441c40800c0690701c1d00202180c6c80c20b10f03505907103041d880d00d402186030004c250019200084014006800c0103420064115840c1420601078026414030001040c3d10320a17900180c1003200f0740513264061350002c0007640d403084005c040b00031011401d00c81c441c1d542c0b2041c00101c8880e00a60003d00c08241414800d2840d44900d0388201e04030390003a0304103030030791740c0318118881039801c25600f181c000b0302c0a100c2001c400040310b10181c1c000000c1d040c032500d41081451607900300030035a44068000039000c41000613a001c1c60400341c00b81001502245480f6081c00005155104090b0003e4003c00000c02c14040c1c090082098901c6a07402c44205d0340454141209000b09038001003c003100c480366402c00055003080050750b0510311000402c246680d5105040080c031039001010800d6114840020181c0c018805005803c1c82e00065407011682c6030460a0050a6800c2000e03608034685c00042d1520501240e0f113144e00a03220350b071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 447208552 1250 447207302 447207307
    0x5120a05152709030a09061209020d0b070305060a0f120c0b030a0c1d0f0123120414070e0c031b27091b160b0708040605090c06040308 59
    0x1d810510060544600300d80200b4503040700311a0014256594400b107148410819081d9500358003180c03030740074000580022a803030321824419a40a1405070014807544070000510301c16a4001513511480410181c0b0565030550500403003945c103006155110009aa00760b401a188c040044228821442401808800c0180d00010400032040345002441c02160a0b40c40f82801940fa46c010032104900d040030035a080c2c18880440e0040d441080c43c42d800070004880464400010342d2003514007154890040c0005405103030a2002074050003a5403414035204d41245000c2c83c1000c207080f6800700c400482c1c1e0200c18200f01c00c003800980d0f0380e44100f0094030b15450ba240c491000d0218580445800c101040219500c1c1c0d20081a0070a000300895405c00103588252090a01c400c400c000d44c1c58480344552102e8280000c01d4541c0101844031600040c110280c141d030321f8000c08440305460b070384001201e4000b80b20620102e80909908101018042d0413303410020000f01c1903c103510000b8400c1401 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 447209802 1250 447208552 447208561
    0xf08030906090f120706110114160903020316030c080a0b04020613030204050f040b0717010b090d0507090207050d170a3317030301051309150e070906050105120a05 72
    0x140c140c203400f005000791035110b05030081c58015480300b100d40190400500c0360303020f1005030a01400756034203070850003c6451f8240c44181e01081034503d0714024500340056510b0020040c1c404110040d1110140d014990401e800c6244c84104081700740e01c0701456a01c580104008205031413903640d0026030456607541d50f00880142c011241c01c2039800658810702d40020040d10709070b543c2101d44900d202d0f0101e41e40546c1c0310711058401d074036800384440e11001000014001500c11600515003500c00800200c180484c980c0c405e454082c458000c40350468001c5441000c200c000c010307108110003142491005404940c3c126811800000c0c03520121940300e802c110031075079002c100007807030820841c0401c20184840c0d0b10001d1b80f110f01d01c0340c0503040b82e408110110950000c0240e0303043e103000801801c508032030008610040c0c0b8100500f510503d4440d100381c082e0030700f540300309061401d101000d02203080c03410740030008698080c0d0109061007410028056910888444141c0c4245501c800041d20f803036 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 447211052 1250 447209802 447209809
    0x70f140a0f0e041e0309031104020a0804080309120d0e19081c09050d08090709090305030c0711060c1b010801030b0406090309120309050a0b0a0f211b090f0803090609 73
    0x2030184d18006107514000c0100700b41030b030100b428800c1d280142d0601ba82d0040c0b04060204922890350b10000080f641c50210300001e0f250001590000001c038100d0f21040601a10465a5800107502c1c24000e07540700040d80705407505103c0364000c00f00e43c0700c1980c180212904c942c0c2c028440d00c00034403815886420100403060b0940d0240c04116004011242c0c40c2440c400701501c0754a06862110342031183c0c81c40002c0402950003031000f05030b45561003908603203605c40129081c0d00000c1048801003080c09011005884034406071040c400000001d1200c141c1d8001c0c0d441c110b51400e401c581c10045030400600103e40b5180e0700315000741e0702110006000490303003400c485000f05c5811001000c04003a0940c0c09241d80020850141e40e03044070102111541c0302c000c0307052441640c1515011500e82ca804140e458081c10010600c0240105801c800e0451402e0b030340304507400c81400e035103500c120044185d10507031300c594900050001161010700d0b8034201854560b59014480c4e80611480001500030030586 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 447212302 1250 447211052 447211073
    0x11703040f06050703080a060f060302030a060e1e0a0c0e010f021c030902150304051f0b0303040f0e091b060c0c060d0e1207020a2105070f140a0f0e04 66
    0x1d000c0160440760b82c03251002050355011250980001303030403401058240300c85105e03107800c0f00d154040b141403541c40c0038000e03030194100620380d0142c150b527010000303424084804d00030f1140d070104240544040300c80701610291240500701d45800d80c680085184a1500880500c1102a00f400d003d90b10b808022002c85c81c0c0283c81c0380a92040d1a04500344822a4050b0807840d04503108450395070541a08083e19581e41c0012200070307240da030100302143c03548000b07e030200b84141c1c08170b1804100300d00c0745004a45103030b00541c400e0141100a000030008600c00308aa20b4000c414140603100c40380d100300d220160950a020030074851a0009900740705e20108200050b61214080c0c0b42c40d86424000060900810100da1400f1340c0e030048481084090322201d0480b444558010000e0560740e0911f010b1340464400407168240c0345180c01401c20104078108488001010758a48130f560071070820f0881105a1852401203014406c181400d1100d4141421000c040d01e04214006240f99100e00701350740d201 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 447213552 1250 447212302 447212309
    0xa020609190e060102071a04121b0806060a3c0f03050a0308011d240904120f14032e06050408011103010e040b063c0a0e01170304 57
    0x30a4520800500b40c4111060207100d18001d8007034500c20340d9103a01100301d00442842501210504000901401d001600c803400102d010b0400706e504070350101d0f0f07640401089a048407030b00798440c07c00c200c0c0e50701d012410100507018a01c0b484001004000f0300810790b440172900d0500300c650110a101c2d810441e03504d0b000c000e1000100c2c1644250350b0b410f00035101c4400386030585c00a0302000012030285070704510b00c81d40351500d1b402045c0c2503403444034000c65442c0142076041505040405500254ad480130502d018034028281c0c480225414080500740307410f50900541032042c030320254000d100809042e2a4068042d8255010a02c41c012001d903040da9611004100289811000f0a00542c04806401074031401c0c0003c0146400300780d07400302c031030109102e038036665440840050b000811140c580d41d044100545222142180d03984050b030800c4007000d03580304e155a40c0014042460b04101200d0548a0954240520508140c92440042414040c03d40d42e4000a610030398415402c10480d0010b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 447214802 1250 447213552 447213589
    0x1a010f1119110907030c0f030c0c060614030d09060e0409060b06040f08011107170d060b0d0c02070e06010206010618091d100e0d031e0204060206180c030a020609 71
    0xd503107884940c00c2c4071031129600600d0094000b8412900034411080d40e807000b070700d0300c0e205000c0d504011005800000b007403804010001340c102000422502400b409003c511051351203c0f00e00c58145860400c00404010401070050b41c100b01080d0008245441c086e01914003140600d024100380b0086d082104030030750400d4000030000f40480200c600d0b5001d8440700c00c020311004858407281c000340d015445006d00422481041d852041c64050010306060000880c00f051880c1da5403544022900603042c0c010001b038490000698087d41403244a028010401117088030f801c0110000356070f042c05010b00b0040c0040000883d262010044524000b0003001009106000c2c41041c2502c1c0021140030700400c520610103842c010300400c0c0940300d04682e201307008241c2a0700c05e003000c80183c03140900844002000b8080c81581c1e280900041c009130400e90020b180a0a003101808441e11440070180b0680c2c1181c6810501070b600851020030300b640484510340c0b55040000007944401014901208 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 447216052 1250 447214802 447214843
    0x19090501020903060c0a08100b0d021c0501061206091104170319200a1a0a09060614030c0d051f0209030a200105070c050d08070212101a010f11 63
    0x2205c2d0030003000381506886c0f5510011503848001c0014101400341c06190403140e020b04c46141160b000e40c1c050403a0000410f51030303900702e840310300031002c035142a00b0035000500b21103000e01c50103840d07000700c074010103613180100310100c00030608130800d000b9800307044012101310074001c4440c0c500300299031401228544202c42100c40b004003800304420807056603842d1008080b4954042c0f40810b240f10055000034124060210003030540a10a0780108034200e403a40d07402e004004940a4840c40000d440e440381d82c0d9040030b0700c0b80101480d10054458a80c450101c030820b031030005502088845c070001c074041520082145d120b010802a0207566001d58241c85048100010300c003421075008007038680c0c07200219000c5411001101da5205580c80a044004010010441c5080403090290503d0007038201a0514600ea8000b030143c0301005151040b903804021843c410030524402d6aa000400c3c40040201451120001e0004107480c180d150602001111540002c40c09000d40550400749170030940 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 447217302 1250 447216052 447216061
    0x120c071a0c04051009030506060f040615050d0510050105070b04020d1703070e010e060405011107030b0702070e010803190e010e060f180f0a0302100201090b2503051909050102090306 80
    0x7079030b500180b158500c90801440c0952a060294150b1001c0c0c903000000f0301000e60b290340c244041011410355150300700fa9900000102142c041c42c800c100b44000d07645113556007800e4480e0005660300a040c10300c0900034000c08000e180c2c2c020084640441d030146120f101c994070b40c0001420881c0c0300788040d020081040d2658154110038004601c03d50682e06c0f0510000f80c2c5200444040d050007880f070f0f41050301003005000c10742c000d80404000d24448800c541c01c040e140c0d62400d9502e1800e64072503016074080c0c1d2081c801c502401c0442809045504029801e0041107038a00940e80e022800290034032002142e0030308035901c00e090302c581495010344401d9441000d141d01c81032551101291b51440c1c0320b03c0c20000c80c1494070100b0b98002002c01404071146c04e00b550204400c5541d64810324003036640c1c07641341400013010141d210b84200881c01d02807884280034140d40e0511070907480c0c1c0808051030007003041030341112420713120380506000700001104a0fa600d012402486569412541446502d0400 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 447218552 1250 447217302 447217321
    0x150703110403030c21050405060912010c020606011704050a03032729040b04111c050d090b0a14090a080102161406090601060806060706050915010b120c071a 69
    0x2900c1a101c3c4c48418007a86417084051038070542203940340e0014008010810003841c080010f0031185c4002030038140452650707150796017102e108454505c0580c00c00010002590b0300011524610110340300000707428946035403100d407500d0380c0a80060078540e64003052905070307039001c61803120346014a460414070025824158600c4020b04c6400c10a000342d48041c0c40355181b000100c6010366849020118580c8540c4c2e90202080000d403200c0703402c0341484000170f106000300410041494046d10141000600c4100010440e8580d60021408014208000c0748504d612404002c00e101215500340d40b079a100388002048840c40c1e61113400158000308030448000c0d00b100907185850702c60301100c0e0414004800607034540710112500c000c80c0d0803042c0100a118003a140042d40810020081c91030804181d95960854005440c1503a0f254000c1c409021061424003406000d0141d41d032446003030001c08840d031021130340e004050383c00e90803000c1100b80811031100041c502c4d411003682880c50070716041081e07 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 447219802 1250 447218552 447218567
    0x90812010906061d0904050a0b0c030103021309020d14070b07060b040e010b0108040818060301080a0b15150d060e0f3408040203120a0e0102070e0915070311040303 72
    0xc1c00c1c1660b00d4141d001454900030725002c07000f0705260382c5020901c01018100840307200300410a0b95180500c0789400000b440d58600c1c684a03245965000703460354154010710403410004c0d2581d071161880c0002800269a84040b90030781140e10a001004d400c080d50300090a00b125580008840034011510340100300c400d40221040c01d006540800502045a4100b403ea0707001003121303804901141c002c1808a001500204610040071507803107034144c1e00c1c0b0041511a0300981c070017a00d0ba04043d00560400002c40085030b0000c09400c8208074401040d00040da0241580d20b203040046400940d502d100c5046030040802444070342044d40c001e280454510000580031288640035200f05102110034902c81060b04030007819100700c52403411090352055580082c0944241e034184542426801d2000c210b0b00100039006c43c41d0b0b2460500b400d54400a8176205203604901d1800740c2c0c0710708000811400040e6030113070740281d4001c0107003500c40c0c0505600400010003046003022002030b001c814180c00c800e0 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 447221052 1250 447219802 447219809
    0x915020109020f0a050105270307030303140a0e0613020f0a030f03020607020d020601050d0f050f0c01030b03030c0d03051e0106050a090608190f0f020d09110d0302030d0f09081201 79
    0x141c80e071000c40343d08200810301425000300c0d40819004e1100c3d01c081031180803007290702c4042c0d8488580c0001c4080009280c941a548114002625048095112546481b0060b0442841030041c480f03d40064506611000001e040740c1c098800501070310155500c0304c0290b201e4500240c612800c07145c40b400d1008103488201c50650152185034003140c490341c03000426402043c225400b4141907402d080c10403c9461800c9003e940c0750b415046d008000c11800d1120300c6c424142d5030010804481e442001500b618085074605209400500030a0318012001c40d0440120a80d850001126520182e940b610b000346095941001190709002182054111004102402064071500c01e03050f9148000c5034201d100711a0303003210303002c100814640f01e00030390041000705101d0200030410100f800002e80498224250b040c02d01d03900d84a501c000c4c0300e80c075907050100394025200b481c2180f0340ca48021350340384259041542050364405203032191a03c26803001d40000d501004503643c5141140d00011403660a00 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 447222302 1250 447221052 447221059
    0x4050a150f052e0c020d080d050a0e121806040807030605061f020a17041e0302040e0102030906070c0c050603090d030c0f020a02011809150f0603110306060307091502010902 76
    0xc3d6840c50044004810010b10203440040350450203101c0d5040311140b840c10b030203d8000300030b0b00c003950000f81c4180180440d200c503000c0018180c80d2801800d030655041c070440d4802504460801030010115008544540d089480d9241c0880200300200700b05200390743c03107a02540078895011040184d0f0350450b40c094a0115040c00c8a51580c40f40012141411103034480940d1140c8010300010358010b160303c0c844080204440e0409541c0c00103049180c000c040b003038070f8556202c4424011440c2920861152a2042d402142589028901aa55520007801c0f00084c040c10b40010070401070301a19804c05428094825916810010005999603000c2c030701c4203005c41e09040000c410070380b04012000007030805900038420500f00340c005440e80c0b151800e1600b0380e11400c4401240701c018a0045014240f44400c1c0407420394509140c003c00005241c00c482c0070142440c1018008030104020780790080011a1b185c0c0d81c130303100c0c154191110110781e440f03401c0f0400c5140d10b5119007501035008411081c000d4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 447223552 1250 447222302 447222319
    0x50f090d081b0f1201051c20030f071a03010e011701090503160308060906030c010309080c071502070608090a110d152702060d020702030703080726090a0504050a150f05 74
    0x400402140f80d41401307282c600342c942d2841840c08510419400d00784a000e03110402c01603a26100802d0501d07000d2891012b00b5400032808200c041100b011407440c00544604845c10355051611203d01c01d00c040c850045080f00301912450307102403e605c4944815400001c8a80e83c20902d00e02000c1119100c00641c0420940000603419042c80207082c0e1090314014082c0502e08a008010340003400e0f4084140e551050031300224010f0710007000795402900c43d000b4814140d0250b035400a142107415009031081080d40381c10322006d40400218a00000d511003040e0078102001004a0680d440c410780152240203880c0012103c2c0d03626501c5590741d01d440b45001304050400c00c0000c1c01030303200c1e00fa00941011040101007848000c4c0d40c00340548a10007001d9403010f80d96601c5001c5250000c110941d886040d1584e100322000d0036407403046003c0851440c50781000c84203000030742c04a0b0079103e01e50003a40c403000064070848041d031046004010441e04010002d03219083c0d9081e941c0a8040e06000b074104 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 447224802 1250 447223552 447223559
    0x71206140112050a0620030c070204150842220c05091b0a031a01030603020603061e100e0f010c080f070602070215090301050f090d081b0f1201 63
    0x300b51603440c0940e049001080000030940d5080001d16001c071042488050040c186525243c912004500031058004455210b00e207a0040000710f604c0030b0107880341120154800c000c402c001049070804004010800e0402a0b81c0e12070102d03070040260345441044204203800040c1c056140707801e9010344580c8401c15a50344060700b03441e660140a400c050401d083d604420040e27458101c07445e95110a01e100468001d0810301d6043d16107400c040c41d0200480d4035562549849507403500000c24181d02464244140e038030b986c000c900f6501c03000d00210700500751010041c0410860303c01c0758804078005030010711071440aa45c010421384908242c248500440d0307061420562040200910182c1c1000c0e140d86410a051641113441c0d002c24421107907690240401009071340c03542c154404408034917001c6551148001c0816003141c0c0c0090180400781031140070f201ea81c903800286400c00d10b0b000d0811a42980b958861000507400002902140b0100011050700605401c0044d10940c005402242504d03602c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 447226052 1250 447224802 447224819
    0x120709050301061a07140105090714061e0703020114090c0315061c0f0804030b0405010f200a0c021221040317160204050f0601020712020a03060e0712061401 69
    0x101d100d520000000441440c804c031845200906515110307400340d0300520314044174242541e008a40201075034000e0032082101042012040507d008110390451414625000344580b400710250712004100b000306103c400c050003503011340c88215400e14012094a42442c1040d07842c01e07414025802800b44c0b0605281c08251408018010000241815184030458000c000103500d00c6a040e40c040c0854820070001c00c949000a001841c02500d5103103651406081290a482403511200100c52030014428441281c5616006802c950011419994850b45400322070660001038082d601c07021103100303103808840c00910f0407140c1c0f2800b91841d40103498024007030300328010791001520096141e013901d41d44141d10001002c1181c4500422401030206401040407581d0480b011003049001b403042c402c0039a010000100280b802c148420041c2d101903000c0382884505210040145886690b2401e8a00083c40080d000d05082c1400c41d900c2c205509040000c3c0c40e441c02003c00c0b10101500205042d40c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 447227302 1250 447226052 447226061
    0x61008010b0901140f180109050714070c031707140f01061d040b1e1608010f0f0905040204023609010506120c04120b09011107020a0909050c06120709050301 69
    0x5280d0500013014245a205000e07020b0390315103a490b1320140e888121003611140725880c1d40079100d811030004561800344800340035552004482601400c00b404240c00007003402c5558015a43e1040b10540748500b201406215801140c800900454004250301a042c0f0001440302014078154000d00c00349640e0082e80b84841c000042e00120001c0b17890005001c12107540006030001c0e2070b0001e020804803021840b12032180300303548111340002c140040380300096000180768058908014081e00c1c0500e8208200c2a480ca684500103003142c8a000003001d40d503455041d5103c3c0046000c0307130004550212080b8054000101d89558502e0084001b92540c1c1401240b4a05940300640b9152402a0302c070900e1114200042c6015641d910800012803080c00300c514481d1614450b582004407400e12203c801d0035980603000b83e030745499040c0071001c0580d8500d210102140c0420600003121821801d089040c090701c5024160000b40006403501c03040e05070710060b4860780907a596043d03c1c5480e0000c00d0b0985 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 447228552 1250 447227302 447227309
    0xf0204060206011401051b0d0801150f03110c0304030c03050706050f0306060d11041d0f040f08070303060504090b09210414010e1003020910052b020c061008010b0901 73
    0x50388800014002c1300a050b201e55a0154141801070414500b0301c900e009088038075180710303090703000008079849580e00030310001c1c05456550040440020b4040c0014a0114055520320800d44c031020b01c40f8080301c050080326900160002925136943d01c0c0d00702075035400800e100440d400d01c624030000510038401c802b52801d003d07030b28003c54550b40300d00c0100622038010140c5084203a03038400400351200c80410080c002007021088091107032070000a810503040c401056105410b80fa80100000200c1d8080324a001d04d80c0061121b454200303d040481c01420b868015942080c50146400c06101501000b144184000c00450703000c5041c0030034004418840000b442d01664061100344507074401071000c8140618185003901c0000502d82c00240002040c0802c1c4001c25030001c2c82001e0b50525a00804640c0c540381803c03440c1c081c581c01d00c1414006008083e00c0c0c80309070400344083e150304580484110f40d82200c100d8a580c10304c22041e244002082c4100603096117003194407403c50424198540c102d = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 447229802 1250 447228552 447228557
    0x1501021b010815040f0911040617070306020a1b08090405010605130e060103020906120a050c0f040b03060103020d0c031505010315050609030c09070314061219020a05060703020a060f020406 83
    0xa43c450a4034000c40c81150402070f984075031a02250f5170b091109110b8044554000d00301700e0802c90344070040c0001c8450503040122500c0c0e5a1210364545180000c55400f00c940c0201c006a81d4010746cad108460004000d074014401408629500080c05180e50141c07400c03c60440c0c00300450b90f40e5117820b9605100d0310786524540c202d200b40400c4802940d1100b0ba50291060502505d090010000100e582c2e00032800c4000044496050083d503420328070615500c008803d10f418680842c608a00c403440c0142d11483e00c3c05040040002c429074400c0e0180c4914404c3c164052080c808050001f401400c3d0030480884da400903ca0002000d605c0f80c05103400c001d1900a1440e0b455007001c00707004103544043d84164152003409108226500c1d4040074a100e5515583c0004e444202481681d51009000d0084c0d8800c2c8412100640d20200210725158a10419800c50300485868400710301541d000c1ea00482d405800803c05074181900860b410902e18800e0104204031440700d03081307000704c1c0501d0003480b00 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 447231052 1250 447229802 447229817
    0x3031d070617090c04090c0b0a0507170901050f0304030c08072103020406091701060e010803071104090816020112022101050414040206030403031404031215080d05090a0e1501021b01 80
    0x4e9040c590301032424a4046c1810203d0359031076801b0325107950300110174140000d01c0043e4007028403c0400c00c1c00641c100c0886d0107407030709055000080150040ea0f0310605062000400f042c2010b0003282880da0320342c1d1001030151202e5981c18440c0d101051075800a4810821541c00b0781128131038421101134031403e40316022221304000400f15580e02400d603807082596500d030045018003456002c2e500905601000f1580c41c00c103490400080720b60346030703079600039800c0440050001d5400300030703203001260b4060072020484803800100c45081c481000c04040c2440042c0d20b0302e6024403150300000d05214104105003a980c2c400c1404111480c0c0d551507000207120401060061400c680250b070420300910300450400082a21100c80b1b260588048000c18812010100c081c00280501d03150420342080301c40c1c4261414400e40c6d1183ea0500343d880c2003100c00100c2c0042555104141005080605108030342840c00d40502048a4031800e9404c1c054842c0c0c03003000661089a28034511800c0341a5902d18 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 447232302 1250 447231052 447231073
    0x10e03060a110405210d09050a030b060303070b0703150807290f0a05040e0c07050d051c090507050a0b070c0b091c0609060f0b0f0d03031d07061709 65
    0x1001410a1241d4442e19031040000140c203660340d141d209084c0b0740b22411304e81d410750440300070381c60b04010145072014013240c3c0780d041049075540c5000741c0880e500220000310315950540000d00314807551138024145a40da1041c8401c883c0c0c190f0021310702002000700780714410348440d840307603490141c0d208409a06104008000c0400f801c1c00c852a611829110a02d042c034020540d5840c00e41c0144046070005100840c00f00000700b0b00031507844e0052000441c492402c2169102c140d00e80320700d2803d5000b8090005042e9600000183c0b001d2005c92003031408200b40c2d440c502e085504c0714500d114840c03003518821400326072154881c0896a08a500c0381c038115109260542501700740c2c0050800d554402002032150480c034843c1d0b10a0207183c0d00c907a20001d2420403500d0000304407814909100e504901d8042e00e46515103c240b1540440b4804803120140c00c410307460700b100648144e04072140c01500350020b4107200400000c1c80c800342c80c9181c403648620250112280c07500d407421100031150341d00c50340500 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 447233552 1250 447232302 447232321
    0x5180307060f0e0601091506050a1b0302030f0f0706050105030127020f1002010f05010b090d11060705070e04030e030d0801030b04020d061803111207140a02030109030e0f010e0306 79
    0x1000640c2e071100d0042401e8114200d1241091026484405c0541e1224006a00907042e117035060044c10090600c141001d100080091481141d6015500c1205c000054a01410f00800c1a9400c05041240456441c89100043d044075045440120384103410720f0000f08107403406000301c00c409003000300c60061034003001c61840c9900300e40c14002c3e038004400301d040203616101c00b00310100240c0c0d10b0300046440d42d034802849048460590001141c2d4109000680e1645d40750341e44000c01c1a00100d0381c10004000c80009000d520881c20b00030010b02c600d00001400704040d01c0710610490194403642c425040003018103850342d0248081c2800240c1e108010b100107039000c284250042c0c00070307159074140d01c280c0d81c80108a650456980301d40d030018a0001d0105948940381f40320b1a942030f0040c2c0350071840c403094034880303000c0e40030010044907150413004040c240400c640010302c0d80040c004e1107001d01c0781c20301812283d0071074690b07406500342d0b2148200550003501c0100072414050020001691a100c04 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 447234802 1250 447233552 447233561
    0x6080c030a0e010207080901020c0a030309091d07030c050a0b0418090f2a06020a11010c020324150906090f070c0f05071706010e040f0204110714010518030706 70
    0x41d4070006540d1800124070240034805031200903c03583e0b20594400211001902d444038040b902ca01c0f07040c500c03405000080c0d004802c502110024070000c2600150004d529111144909a041051007420340000611415a01c0c00e0111503060312201101a19421b03034501522550141c0c40d440001e4404020b5940f440750700c00403d141c0907452000b01021242d032111344050744518082030032404580d540a50310040801480103004c00d00042040c0b0180c1c0d500c40c05445121400039043c05912140c0300c06645080c00399800312a60380950b21001c0c045020702c402c1c01c00090322170302d049010310402c04185041085a20b030141c01d0050502915544e000d40a800c2c036031006241c1002c2100492001c6c00188e01c5020300340615100f1005010602d041010112201c0c00c819814801a03000100402584d07035100c11060304540c0140590b8626100c1d80080390144c44904800e18084100043c080140b294004505000f070040310300912858803010705004044400550104954104110707039800501207901 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 447236052 1250 447234802 447234811
    0x50403120806130e0c090603151b12040b070306090e1b1306030f140d0c110102030f0c0a05010f06060f03050402131d0622140c131d0706080c03 63
    0x181803080305203070fa8008161810040d025245500040004646240031014194440c406900901500007581e0101c2c4c8205006400c0201611040029030b141088600c11114034101240c1400760394201407502241c2e0f000101ca4000c0004e141c540c0101e004a2035018030321403500c1c003000400d100030151740159410f210823503c059100c580022100c8881c841d600644000f035004180010703010003c0c2c1481d02e0314600b8552101e110b90012805031140e03d40000114224039002018181c2c03198010005034a9486031104c104100d440204042642460002e01608100e01c0780000703000c9841003640650036178986004000204048222482d1140e1003940202c6c1e102c0c1c0000d1200c108818120901001c403881d08460450345400c0c000c1040e402c40c802c101441d0818440d1046100050300c0d040a00190284001d00502c2c003144040481c0d51140c080000c210304030f100030b10100150603034200c0358000b0101c3d00070300d40981c01a00ae410001030300205581c0116047d548580800303076158038101a403540000c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 447237302 1250 447236052 447236059
    0x2d010b03071808030c160b0301120302030903100c0f0212030a0b0301020409020f030709080309100c05010e06070e12030412111512010e0105040b01120c0201090f21050403120806 78
    0x50360780304803500e103520b018000c240200140d03070b4410300412000d0501950a0b01c1d0300f00208103800c101304000c1040d080340e04503104505d4600c0546c459150403030851088540f000c1d403510030554117104c0441d85502a1241101584800c0851140f50005a80754400140d1260503445c05100007043c01c0940c0c0c05c072030340350440140010314080d11200040100c1c1c00801c01500c980a020080094150704a8552130140580d200294101644100011940c1c4118101001040104d510241c1040400d4005031402d0200900b9100d0529210300300901100b20521000d20905104030701c0c8034256004400c40c0c0a44a0310003104040110a03203078040d00c4030844600a070005003100101e5003810444026000064a5100301c0205515140c4064070145040e0001742c411480c0c500003061030b0f81c002040d00c0040b5401003011a82741100c2106034010642c1101c003400d074006049480042001d0070400c5102c1007055850a0403c02c00780c141229a030085000060081a00041c810419805190025408a0000c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 447238552 1250 447237302 447237317
    0x406170906040b10030c030809030708150a0c030f0c1d0f010e060310030b0709030c0605042303030423130e0712230a1101020d0c0b0a060b030705032d010b0307 70
    0xc0d80d880d11051540d41c1f00b43d4425601180a151a20b0140b02d80401048888002c10b031900420070301c4da256a801400d450421946c80002401450082e00507644050502404208100c0302100181c00908003003103035641c0145507080320900c0d03c0d040d03010a00128040c0d6564900f20641d400380486540041c003008006080e000300000001c5404010034881e4040780e507421001440c40c40c0c00c9503100040c0d0012001d0000502061110780090540d02d4450004080d48110915080c3c000c28118840da40001c0d6512003c0072518203811001d1030010706401042e50400c0044507000f104a0448540c0c01c800a91500b280800f0024000d001c0181880303d4016000240081406804603101d00d001c401036002c15000841010709012841351030003468002030002d0208640420320003031200320b041e8001031502c527500c40884c01050041d8408400392241130b01007607070790818850190003a00304680426904129220420400b981a584401c0810680ca0b4842c0140d01780b082c0c0a541d070700000c02a0003003240b403 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 447239802 1250 447238552 447238559
    0x71e0206071b0501050f030f0601110d030207110303040303020a170409060f0816050112020a020a1e0506150915010201200408010b01030203090c0108061c05030406170906040b10 78
    0x50344000c18407107100b05074086221100701c04940200c58598042814002e0502c4544d4034825034500312a407010b25211610400d40c1c03a9801a240b28043c080031464511602013011000d94040d40144101e03801005860a041c01078010141e45e072040340002001a0003c0044000103000c1310b0484207020b49000b40d0b5810a900c41d603041003214041e510001c892003000c41e04000450040c8400701e080182c000e0b04100807800c10002038400130040d5102c000c2d540c0d000440c50303515442401a1004144c0c4400390001b00240543c0b00a5030304801e40003500e007800303440003140043d010080384400003030014010100c81d54418811520300720801380350394159502c43d12484400c1403482d541069200ea10401292141d0030301c43c1803801c40d80440201c0e41410720400c2403103442c0c0e000094032500c00200740b07001c803440e6841d8004280316800d11000c820210000c00d00a00410402001801c1a40c80750b9403480700760340c04164032401c8540d09030b960756a660000000f2401084800c043c00303620a0703018400c2098681d4 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 447241052 1250 447239802 447239809
    0x50108060d0b04030e04050a0203040f02010807050c0f0d2d1b02030a0516090c051215031609140408070611040503030a05090301050105030a0c060f021c030f0b09010b071e02 76
    0x24100d030101d000503000413450905d0302e4184100c2da00014142d50840c00c2d0700d410342d2444490745001d903000c0e0510003c01d0000782ca10703104030300701c4025540d19001d0ba440f1440b0481c0c0b40e0794500902ca0b8100104e952160a140803004075001c49a11004103000c60194907040d000540c0d85880240c3c00d01c0390802c0b50044040075890411440004511035070080800300f070b00c0c131814a00071150f60030a141d01810b060040419903400350980d450364070810845111500e80007003800c0d600d40380b9028140c0600402c0c4c120030790248084038441c02c03541024000c3c8440450a0001c80003020100c500802380032051000a020401c076078003801032100d014091a1819071a0700c0000c0c590b81140f1507000000b04005401c2c0d030b05003000e0041d02c0c0105415402409078151954130000840614020001006982450301000701e10070880745040700c0654056440708100e102000300548441031048240b18140141a00c4504000824604a800e40e04840703003801ea840d640d00140c14625107109a080c0d89043c14580941e4 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 447242302 1250 447241052 447241073
    0x10f09150905100512090c01020721020405010b1207020102040612090c1806031e0201022a18010e060d02011407030903060e0706080f070c0201260a0606020f03040f050108060d 77
    0x82c4549844d500c0d03c1c102084031541c0e40c0018082c42d1250048010071b141d60340c0000f041420385000308035800358120124026484601001c0002e540942040e0000461040c00001000d140c18041c00c05d541541d20103606a080c4e2045200f0440018021301030000d41c0c44569120205003445440e00c50105d035078880c2c003a415802c0c0c8240c00000180c0e1009c041003000a140c41e181401c00c1e0b0340c6500f0045506580001c1c1d2641d0032600384c030844080c11000240403555002c3e40c0d08403000000d10030343c0a800c040b13607072400040c0240255820255000080341c024905100d98a47d2660f05a40d90202e4040c2d46000411700d8020010481c14030809050100004d2498061940c24400d03600040c05014a0724030001c0950310040c1030400500ca1610074400f4441d0b00401c00310102e83c080c24151030040740038098440d00c111005d801b2400c540032405115003c151500450102c032002d47c01c54011304c090350710250702e910452048070308504140c0800c1209500681005034010002009000780d40303040d031245076000 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 447243552 1250 447242302 447242329
    0x1030e0d030e2b080603030c030406020109060b03010921110a08121308030a050c04170c0307050f01081f0b07050303040201080a05040203030d05040813060815010f09150905 76
    0x380c0707445000a02c01420000390004a12580300c1401c84980903510350703c4032880000070410845941d0000e0b485841c10001c44142d2401ca004490b41c031a0f50f44402802004d00c100105c40c5281400580c51092a0501851a64942110007032940160485000c22031002d80c5201d801800042c401e9401d07107007018050701c0d420a0158292a565011801a44106000041c40e50404c01140c2050402240c04007099a80c088a14103000031a0b0319540c00d689458002c40d070046003529031100c4000c09408000c20a0b6042c0f00c0d007901211016900c1f2001c00204000d8000824001914800080d004a800790b50160118080c2c00189a500e0780f41e04606200354802ca20642c3c06030b100105020440d40e11811080d80850078440411803030502d0b50019480e40b00c1ea010700034041e03444101160511085e0001c440e5201103561210341401d594502c043d1181c041100c03a020520507164448800e54080c18007255a49840da5510044030b0402d20b42d0500b68016480003010060300c07003001701da00e8417240c2c1c45c000f10 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 447244802 1250 447243552 447243557
    0x916050901030b1513061d0c0a08010611070506070312060f05030c040b0f0306070c120807140c01272a0501180905070302121005150715090b040218041a0601030e0d 72
    0x41f10400480360340030001400d80d8800c0700c8204501d1911030740c464551415200c01c1e00d4590354504082860901d801c4d0319400050b0302002c0040e011080603041708107181022581312040c4019651010740b00c10f040300500c105074141d003102d81c49a0b00352920760302002c2c0d9103030018030007080c5480803000b080c60018201d980c1d00220726180000424006410b8140d1340e618001d103003221142c40d001400800095200302c0c084030120010032104001c600a402801121184000410365080300000c3e881031050501003d5030a40d030300a002c00b9200c0320090000719a002070356081011720b440c0500440e00912260742403542c2413900b40010072070403024043c0e01d00803680c1d560096103500c4100c100c9e18000001504100c03030640204e01c200042d4907a641d0710f140950f840e1080f04e8841d80e190400e00310014505011441f00c91a00b2450400c11403503080c00e0b80118001d0761b904480006035180305240c01420f03140a8685155590156100c0b001d0000d0254808010314021424000b0b00030385a140c000301d280d80401 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 447246052 1250 447244802 447244829
    0x60e01060b0c190f0305030702100e10060b04050603180721060501050306040c0e100302040608030d060e040503090409030507050a0c030b090123040203030903060916050901030b151306 81
    0x10350008128040c1610807010f601243c0422a60f0380741e04100d0381c0300d4000c091150104c0020b0b0128000d000424003d01c25540511407051400c3e000368580b81200d0a0410381864050b02280c82e094003400c0d6425118090030040ca149c4420f10707031802c42010480030034114030030070201050100e8044105c4161014000b000c41c1d00c1512490288103464051700082e00aa10400030480861581c0c510b43d41251080744d8580701ca07071100324051440020350341001e5042810000001040d600000c0140126130035907074208412130310359182c241c0502e01910041c03ea940203211483c4146440e174010b0503000e11909003a03141540d250764042c00c003c090fa0007036070b150b100c3c0381c010410b00040454003540800494000c00c54800440307050450b228951118280b0369400100150854a04201310317010703100c005040f20b0b040d10701004210b9a94004000c40301007844440340000d030328107099030024141c940c000d80404060751140d1413080340400d2080c804d60302c00321007152521142164801c010242c20740410508 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 447247302 1250 447246052 447246067
    0x1e0106060f1d122a0f0d030e032509110a120b0a03062901030e07060804050a020301110c0c0d030806040209131505040e1506130213140111010506030d0309060e01060b 73
    0x84c0c408400303102e90f01480400002c201c1545d542580c407010103030b0508158900c443e50030042480c10702070310b542802944101d000414407043c0e0440350001c443d00d4600c14006401c08006a04030b80c080c40a010300030030b445400451091030103411030050b0480181c0321184465980d21360800b03a541000c103080c04155a0448103020906110503640916000c4c00d0901103640c0602c000c9640d4082c9200c0c0404000107103000c13604014080c80813048140e0018028800303640491480c0d0001e0340700a000c1100342c0710391a4102014202018030342d0307181d5015211501c0d190390f013500384000381d88810030696000a2042c400c1d85040241d2141c01ca00344980d011301a451800d03c824802254007281d03460141e42d01110700c0b0b0500000c80d01407664010015201e0035465000b01e00820003070b00600c91000900280700c28049001d145080b400e61401c0300903030310384002041d0701103081c2c02c031b80080e92015050b800c0054401c100c030380a03411500095101b00c2000520440c0028100d00b10340d141d41101644180014403030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 447248552 1250 447247302 447247363
    0xc060f080103110f0103020c0d1e020f1e011b0207180515011b060615080a1e20030108150609100303080601111e0106060f1d12 56
    0x11005106a0414411650440c2c40b800c2ca00410a43c18134411306000e0b2842016034469016540300a49610490b2052403a89d81c026207442e51105543d000108211111000c1c90b100280d09101d034007100015001349040b405c0780c0c1c0003084003140c02c801290b40741c07a040d5462800c6aa95503101c2481c40e03002e411202d09041d03201d003000e00081640b00d803481c103100a00c0440b019031006003880316001d0800d00c01e4035941c20031481010502840c0500054a003440005200120102c0e03541288503640c0e4001241c0c0d2400070140403603e05103601032082c000c000c05e0740040051360348040301328559184100c0c0c04419007806821343c0d90090f04416581d801071580c03000c85156602c0c580e600124100c0e4800098a007031000100c1541d1103200240030030881a01040c0580d029a140c10308030360f401130907a4000b8070b4803040664004405146516250328001c000185107114405075200380e100341d520450a00c4400245d85c0050b449a40203e6202124080c80e0001003403c011070641c0d0400c080301500090050100d0 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 447249802 1250 447248552 447248567
    0x1902120304031b1a010e1303021207020312040801090203060c1204030f1e05040509010f0617040309030204060308030613021e070204230a0c171f05030304061119080f0c1005040c06 79
    0x141442c4e0340060307481310000f50040ad00320303041c00d803e4586503190a55030000034a061a1602424240030b40080c0100c3c0c00750042d04140040390080d01100c4840c1c40720624690148070b09801c0b0519266510080303400a0712454246040e0441403402103002000c00640300d8030800c1c000010300200700001404c100d54108441014014015401502070742482c2c41400b402111340765040b8121000b100001804140c040d94460000c3c40d00980300700820b940341e02d400d0485070f0007924141c0c1300d504180001c0c100d031fa4160007110700d440b903c07020191149001515071651070b00103070000c0b0f074003603181c1030a5840303107450a861200d0540c142c81c20141c141131010038003082380c00414040b820000700c08607640642141e00752541c0c118111004108109050400c4105500ca84c5d42240303900d8080020005183e9a21100131181c09400d0001c0c0d891084000582c0c6501345007410009004c40d400317004000c4100708400c047e0881070400c83c20348011040640e045411104101c0b02198601007aa5040c801250300500 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 447251052 1250 447249802 447249811
    0xc110a050304061218060501050f09090706030207021503042613060c23061902040f0b0c03070c030302100f050603070b21010b1902120304031b1a010e 66
    0x290554496944400740c0780d00c00da0003880c0c24001680403408000c08240d00441000190840805541d500c0f450164094242803051501c580001c6004130440d00d001e49409001c0e4141d4001800c066103001010fa020350080c04090340d2004086041c2106100c8400003103100d079224103004665500f0b00e445890b41002441d46034803803040c0c02d02905078488031103a41541507500d1820010f14902003440d1000d080c0301c1d80d40700d03c6500003219090440301140040c1140c0202114045040741d5403103090003100f00d0017980300e200c205a80c004030401030011144001c0200c41c2c40202a20302c0c1415075150b1071100341043e4400c40041c2d020540c1c503c91221644941d11a070510414140704900344800001e1707070f5070350302e0042040910000490310b410810031060b101c10324841d522000c4256035100000812034201c4080302f0030303160755030101504e280d20200e10054051040c20a25055032556202180d04400403040040d100d81c0c07a080800104500880201d44482180c09010f515810050b14600b4118040c2 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 447252302 1250 447251052 447251087
    0x50c10050703080a05150303070506070905030a0f021e18070201140105100f021c0507020310061a0c011509091406010f06050d0209060a020706020c0904021f021507030c 74
    0x1004500082e409030b03d990308802103140102d456280d0b2031500c4001c0640c010703116818400000c0005c02c200022500c00c4c80303401203445d00f0944a070349034141030b1506c40b002c400502c66800084c0c83c0005261a20080040b250164084021a500c42d000724507064061891880e1340301062081000690382409003503a03a60100301c005032294546008282100110200d80b824440c82261a02c141d900c04c00c0b000c0e103607040c0362a0300c5040e0039000c08050710f10340c400902640613005e25289103002440500424080b1180106100c0d0980c50f6028001000d802603456030700c4954072000c0e8841d1f00da007040c4880b000b0b04020000004d98046d1482d1a1101280c071038030440341034110350010459006030641d820122110741c10419a641507140805009101d1840010b0b84000c000c81e0840340d66030f0010341602910190380071030381101d81c844104a4464411180290f10401c2003121150019130307000398103102ca1050045982c2d0f039440c48204420100d00b1a003450000c0d58905100a800f80e10040101081d141c4070f = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 447253552 1250 447252302 447252307
    0x110a020d12060f0f1401050f04090f0912090608100e010501120b1e1f0206180c030105070f090b27040b0a06110c0a0b070b130503040f0303030c020c0102070e150409050c1005 76
    0x2340d0156000d4042e521814035001c0d0b8500f81041c1c2c0040075080181d4099125140c001141c034200000350160140d4000d4000040d8108c00180301600100f1102050f5981d80030302903030310fa203841c2c011201c5904924030b000605403110710404003600c3d1005038028401c0034990303590000e07088100740041c0c03c0012071410038406070f00600c80b40c9179801040c1641c101320100d0100030303407150202c80c0c0c900c0c16035500c054603007561905c406c00050380d5001099282810590791100d400903900c500788404e5003e0303a0507021441130903050581016184842078140442e0152000c10700310303111400074588011584c0a00c012a2990b128084400c4c0140800d11401d20708480310710381c15042c140b6031110760050b00c1004200710380400100d0358000038001e1600d400d50788101280c3d600d944030300741c041c000801803000b100030900b02202d80c0c80b200d00104456010b04c5060f8005c00f62180b400000c0f01001030040c1c03043c000301c400b018802c2c14179110b9000f420030485c0a10020030400c0018014048050702101e0701a041100c00d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 447254802 1250 447253552 447253567
    0xb0105090d060209040621020117041110301104030506010e0c0f0c0d030609050114090c090a14030c0613171504030206040204110a020d12060f0f140105 67
    0x307618401000c150000401a1a040c0f03040215005042d142c2000a4240d0028170040502e80d03041c0100303401e14070030380e0340c0254213800811031849900103540084c02d1154607000100e560804025400482c0000d180062071a0440600c0310300d1180920200b40c00203840e406244440300c501d006e01d80b411041c800b2a01e1a003031541e11501e4549206006014031405580c01248074014035105840c003040c81c00c02d1207030347c500801100c03d50303c0c00d41016850200e0b007081d10019100b401c80c0305440c101c0f42028100d0b079154002c0003c00068603001050810202000e000b031100750b80310780c0c131658040c240c540303030400926070000c0c201440c00404610040c81903500b0410700c0030421135481d40c1c408071403100c0c0707111288040f2030f5041828444500718131103405103030300100b0060607400105140180d00a4070100a18000d48060320068420302d00d02c080541e0005200c282c0c036611945100701c601005807400603856480381d4011018105079840152000c406c0300f028805e0740090544003600010900b03002e07191028 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 447256052 1250 447254802 447254809
    0x5060a05032806020403080a0f030609050105060d09020a171e010c05042105100207060e0c010e010e1c0f050d030b0a090903181503060503062203050c0d120b010509 72
    0x114030100b6030781103000b401c0307103000c0050b5a0140c03400345074002c288903120386005000800107a080128040000d09004001403030142c03610515042c0d91015040030314007258031484101a0043c2e5404030f0b001100082c000800b0030001200060100040307000c0e150000c81425030303800300082e8845000059241180c0e203044940c03c0320445085031088038190160003551580d401c3d440c03010b44800342c0349000d20324041c000d43d001903000740041841903d08000403040132014075a682c042c000850302060140c04910140d6008001012041030000d0907250800442c810030380c80b00504076411201d07142500c1209003001000c0c0405800d030a521b140420141242c803001072640949440740b03620307656882442d902410f100d1f1440d004549200e0300760381c103241d0741c031110301e898000c40f56102800640351040105584c600407640c18000d01e4540d1004080c225072602180c4031417882d040403800d0101c100103c03a000c00301400a40d040384e0098554000c201000801841561070900e02141000420080c0304011707907 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 447257302 1250 447256052 447256093
    0x5030f0601362d020a020601060305100306140601021c080c03070504080102070c050f1507020603130213020c1e060708150301060806060f04020f030c07031403010905060a0503 77
    0xc200740d01c88010b40014146030700c0c40300d407a0b01e020603810801c40c02d052510651040710f0300420120081c095050002c6000c08038001c0c1c044903001070304504010003809101ea00440c0d000f12440b83c0b800002c541e66540c1c14120350340710f0304407000410018108202d641e01032221450700302d0001001c0d0384c007546509000f4096078008120a01c607520100116603204d101e101641c0140c00c0f00b4000319a600e185080101c1c0c40e5241d072140d144200c4451f03413048500c0c144031a03210b0030b2080806200d0300340792160f42040803542000307180410030414421800c0c056600c141d202032000d80c060200580d00d0341d4840281d030424030005101c0000c02400c0001144043c1c00050442c1e001c209481c18660320386500000180d815503800402da4558242240840c88007404610613005210844a026109401400303010a9010b006407801c50600207100003010520f04800402285201c1d183c0341a0402c07101a1480d002d030020307088820450703680c004001250410f820f0510142c0001c13170044c101021400381d5400f040 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 447258552 1250 447257302 447257339
    0x1090c08010902030a230a0e0d0e04020d02070204021c110a0f0507050708030a03020c0f0a03020706110c06030103142406010c170a02030306010807140901030c050d0e0705030f0601 79
    0x25400070021740c03100b5096200c5c80c1000d83c4000d9412800c950300402c2c11620009071180b0340e0042c0b0b00b01180a2a050000350b00060304420380300c00448420b00d00401009410002e2424000c030b03000c01a46005a03501d01c0100b07000c0d0b041e10b411035424908019514115002110701038003c2104218460880e904080d076001c81c0340d06841c0403541c41d00640791580c24104140d000c00324030311002c40c080012130380603000350003003404040071118aa405d042c07800750307100460100540540c10000040c800180310743e01982880303e260088555032104200450010b900907802540d4220161a26101001e41808418403038002446c4101c40a0417101d0344081c4000040c081d0360500c40042c0d0b04404004501d280c2803411401802250744403120f0303c41c0a526036008550321400100d0045c00130b6821401090500111600d205413a42007100d458015402801d505020f00306020b0305001d80140c0c840c1600403410a100060081c04070380e4a00800d05142a07180b0002041c1d5422039030040c4000031280b440260079 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 447259802 1250 447258552 447258569
    0x1603051e0408090d0b0a0c080103080a111c0c060c0e280305010f0f140106052712010609050c04031a07030b0315090d0519030902120a050a060501090c0801 68
    0x240d4441d4505001c0724070a12200a42050610300080103000040b43c0c01c0703208a04419080c012078604990403250710509000c010030f00d03001400844a2644074100d00201c076203028044a00c80c1803d414280a80c425040f42c180c00645000341c818104201030240420b154110f050125444400b4000103a6600300601c501c0c4103a1140c20081000f1082042079100540d040f0000700603000a03d07074407802410400d038031410340074200503100020000800e0000d0407100340d03548131410301c1520060480c500005d00e480c0c1030318040d403815020080c5c1c2c41030551050074411000000300c581c0b40545100c240c5d41c00605030780301c0384d0060008001003241c480041200c07052180c10301031550369401c015001011110140c0c0c3c1c240c481d041402e0245524042c02070302500030082107940c030005016080302e02c0d00c41d440400c00720612509001400c0d600940004096a00c01800700050f5040941e000740741030300e41c01054510f9403040b4480f034240140c4c1d00c680b40c05003454030745c01d00c482601d05002030f02c8114103202d2180d5 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 447261052 1250 447259802 447259861
    0x429070f020c100e0301141e09010603290105030f071a041a120f100501200136050303060108070903120f030c0315050f120304080105160305 62
    0x164428840d80c03110b41002410302002c2c901841e00103006944041c004d901030f603c3d141011f104d8081d011082c80c8102800103550700c0109015181d03440c840c00180c500c104039900e850b0702100040500c400040344016503410f9221a02e8100d000100200d4103034041e90003a04040503142c2140c00c04181c1e8400e9480c09244060380140800b046180b620850b03000a00c1d0114051506000c550307081c005213203407509030700f00c40030355160104401d045103415203c150702101d11403c20801c035400340703c40f85045115040001c40e5980015881da00392134400b040d1510600b101d1500d8064100003c0c000d04010308054641c41c050400da958450b568030024100318103000d44100011100781c41420380d4000345901c0700c5d887d5103424000a0240201c41a40e0344e044c0801d0a01c019501c4451092144c030010320b1204491280240c50b01d8107003c19111000c00031908800c5900c1625000c0700b041009100030038502d0000a5a86002c0e2000000550185800010117081509000540030380100d03420f90a02c028100c680c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 447262302 1250 447261052 447261077
    0x50609150f0408010b090a06050d0b0702030c0a11010f0c152f03040b01090e0705040e0f060108060103120f140a27061d09221a042907 59
    0x92150280d2510103085240c001804200d007070041d0401400c810054a4500071b94031410403040c103071141d0b03000d0f00c0c0d0085101180c2c440803c0c2001c00c101d4020340640152440c051010004600b00320107044107460030803140210501c60f5038030003210f8080603c5440c01c504030301c01665501e2084586240c100700490b44600e04a448c0c42c41340406ca540301403500c440d03040c12954040001a09400c1140c00743c42c0c0c035421200019540050b0700904e0400400d00c2c025280d264140820080144581400c001c44d41c807070400c555000b00400c026641c042d280c0318008105540c0340d85000c808480824000300704102d032402d0091071454000d14040d0802115240d426100c24005904462604540100845100d880070280c0c0004401a940b035066454650340c0f44002003070304540304400303a90408001d8125040c14001084a220b4210105503c070310300c4002031240704140c407041d02c100320749813041c41070815110901042200410080d0500c500060f2010000110104091000300c40140003500b0301c0300070145507 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 447263552 1250 447262302 447262339
    0x803030c09040b0907030f060603050403021c0302090d0c03050c220c120203180c0f0618121f0f2009030a061d070b0405060a140c030313051006050609 66
    0x148025201401340903851a01c008004c3c05050503078494840c981c504540818154441d0244c244a07036050b030000c1511030030041c05c0d106030a110780c84030003c06509100c05011560340c021301d540080d010b180082d603842e0642c1030060921541c00101807299501d0700260b03445660200843e8015200c1e01030014060031080c40c1500e40b00040310410101030310010401480154007451790104020b204129901716440340284000d41d00c40c044891340c450018004902100040303420042801c001400121290860030032080c0b9040d2029520602075840022001001000b4132510a0003420307000141b040600c144c9041d004038402c045a09800500061007241c03a480c00c20000036110340c880410058143d0840300d60802118070031a2102c14017031a10009502c0c1c040700c080e541914401080c1c5464242440c4003070310b031480a0301c000003d403581031001c1881520300f880070314440c2100c4009904c07062100c0c688070f404c02c1c00403040302904074941101400603440f090f00f41c408000007074421002c501c0012001 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 447264802 1250 447263552 447263561
    0x10020a14090d08030a0f0212090d0906050f09060d090303090b0a0216020409060216120905060c030a03021b0604050d0917100b010306172d0303060d03171f0f0803030c0904 75
    0x186c01c2c03101e000140005203907050808480c0b080f00018140e480807194442c044420510324454030700090400e01c00d0f4884c00070070310014001518000d1140340b80107940c251060941e104a4000c0e400700b640c034200e04082c05070300089a0b80c03203200700204602c5c25588200c0f40d01d1a078240e00020f800360369101c60319802c00006e42d0481d0b03c0c007120351318503040c41521840e00210442080d4483c90001d04030311030000f000d06100c000d071100b107000700b4007039400c0200d4480214001d410007050459040380800c03c02801c0300c000d1040c24001c2d4010130241240059404011b45585d01c541c0c01038192a1140310504290b01c0045a84280d00b2011000807130484407800040b006018180c00c50610034040310142400790100040d0010b1601743d0048605055282c255005c2446515011140380d135041000020031929200c00b484031b000e8841d040080402d071110301000c1c00041d0071185408441404040c00c0e00d419404011540103000200c2691107175030600b084140c6070300000d4071040c1443d401207075800160303485401 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 447266052 1250 447264802 447264821
    0xa14190f140406060f0605070b0f040305070c03080c0c180403031d03040914130201091a0d020301090203090708070b070b10051c0b10030b13050c0310020a14090d08030a 74
    0x70101500d0905003465002401203120349108a00da03d100010001d0040080d50031858100c1c0c4098890b9803654104c04001d20000c0044041000400c0948005a03849113040e01940c01140c28035101e00450f40f040c0d01d00002910040c1c130510010220049000c0004003065016a2524000c80c0c0da103c079001c08081040d68141d641c0d20340c0408103011481072000d900c08031209180d00008031281d15403c030001c1c4142c03100400070340001e6105400b07021030616616503500343c0400202031880c1080c01c030342000407030700300b038002d00610303a0000f00b48040c03030000300070784400f400318070b006401968944240c10740d00d8800e01800510100d90100040c0307a120708000450001c050181108030290700c250805030344440707a500210b03030340880d120114401c031403498404001d5a80c001d40f280003d0311100e99180c03075244143e608807154170640c0c0c032120003602d05020900c510510082c000d62a02413031170001c0c0401c142c0804d0440d41c40710501403d0700d2030792411007990070345411410740c95682d1141c16181024003815413 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 447267302 1250 447266052 447266081
    0xa031508010c082508090a050604030807020606030610050d0201110715180819210206070f030218010c020a030b040b040c05040b0306061201230a14190f 67
    0x9800c100641244041020380d5980e0340e1903540b901c0b54658061044035803204001000941c4000c01801414800d0b0040115401c440004800b5541c46150071403ca804500007219001440754041d0100300c1b2941000046000c1c11091401384007032840064244100c0d03101e59101070146096901911850000040070010340340c00d5901e44841159240c0614101000140c1c07680442c2a170320322010b0010705031108500038184640101c10040c4001d54443c1090f16001c5411490409502185d06800704105c2e094014081c54541990301034a411a4101c40c6802e16004003ca480641502c422400078013100342082d510b0901c0d03500200d01401c0e82500020b040d055805c00303120a0003a24100c4500c42c40c840c081e02c421f61600c64040c072041e9a000c8074610303010b0340600045080c502c3d21584940d01c00c0c2050f000000c650180110601180300404542d100c10b0b0380460038403030755000601608402d4515400040414100100c903d0b00c151118010780700c200d81d5620469002083c107822600d520030100 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 447268552 1250 447267302 447267341
    0x6060f030114030c06070305070b0a0b04020a03060303080901060305061f0e0c030a0f060503060a200d0f0b150a050a020102040b07081b01060605070807080403020301050c190c080f0a03 81
    0x6041c4200320681002005100b8422884c0d00050351030050112500c0543c160b640b903041c00e030556224010800080c010452807034860591583d1516244050650581d00c0c4e50081119032840c100541031110151506455034189081800400d030b000810343c1c0c0000b80c0307202039000001d00c42c5400070300040a03003203040b8001d2040c050002d6404030001840c015140e0810400042c0d000b10f05c4038085401c14401c094058001e43c1c0029101e68140c2d03c0821182d4000c1c194600300c80484100c100b65901452080300b01c1c03581c411107007130840e03100e125100020703a054600c8466000d40d40041c10850046034501c204021000841c841d81510070740658004000401030355840d44c400c2c0c5804543d5810401300e03030080500000400c118664140070361402c84c0c44940300d080c41c000c0b03242c941c110203601025041e120300404000002c01a1800d01c10b41e4454000002403030b03201c00d8664440d40c1c040802650080804c03420b0744000c4042101003040f6040502d80100c0389030344100982065002d04020b2a02d0410100403 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 447269802 1250 447268552 447268559
    0x71103100203090f0c04151215050a150b0c030702090703060312110105071e030c09030507090e07090b010813030e2d0a0b04090b030709090507051e1806060f0301 71
    0x265a1540c4079800c0240c0780a001700e2400c1c03001b02c46101e003405101d021454420003081c0d000201001d602401202100d20128011040b030b010b4800c1520000b09150741d842c44445074400d440b04003000391401c000040d00d09424440ca0540d80d009120005c1c1c4500c5500c00031800003802a4481d0340216445054240074400050000c1e092001f1050034001a50030800029032003841607040441d902c40714000e06e081d020503603400320001c06804030b09d0000d02c000036a0220201c0d43c00c0000ca001400451404110704558040302c034204012644003c004d103080000b160050781c0c0200595501c60710329000300e0a07000d40c50600300e0340d060040b00c0c011f0304401a0a0350f06005408a01012408040c00081012140207041400f010020074800e1508620003030100340403000f10b580129415040007012540d1050f180c43d0b4620031554510000c40c0c65901c020340420507410842c03084034840e0402c281000c91f2413040c4003c41c962510304000010145000000107d540d0365040696407010103683c41d4584a41c0c6 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 447271052 1250 447269802 447269821
    0x6092b080c1e071a062b060e01050105010f020304060c02010c15020309060601081006021903140a0908010615050319110a120510180b03100f0b090c03010803071103100203 75
    0x4420f00645070501c080304203180300d04013160750078000c2d80f001d888022551029404010300c0781841d945421042d0382c0c4140a0082401d5000340150982c0000000401e54035002c00500b001083d402043c2c255003042c8003c03c5250307044110a00d80c40d8080c2007425200b01ca034a046c5205000300c181d030400c110b102200b84244403030f00241c0b4900c198404e803107a1a25403185450054203034501d1040b1390050744204480d400e000740b4009806040da110741004142690000a503842c940c125500c034800241614070700f008100c10902074a4002c0900315a0550b0811500708000c006220045c0031404440c19159240c62441565001d2100300b50200d001039221880d200c0010141c00d080c06095150380c0c18a4007103821004001e0720001110851550000c205a100417018043d0099520f42075043c01425050008061280590b4110765217440000488608400c01c00011410203010860840b000340014403002c840003044404682d04411000358a40d1100002490101c0b0000c0c0050b03014000704c140000c150 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 447272302 1250 447271052 447271057
    0x130510060e06090907020a0c170a02120a17070b0a02040e04060207021302040b0409200304020904030e090a020a030c020708120d021c020304210c1103100504030206092b080c1e 77
    0x9110301c41d02c0000c20354a641c41070202c41e0274440140250400300f002d0b4014a080c001d400c02000302a02519148042a1900c4080c80303241c944102c0d04840c0066000200040184c0c401d900c03890300c3e14114141810304080b00c41c6180014402400b281e80058410103540d2aa0140001207402440c00d540d600c0d01d0b002c9000481d0070500c2201203540c01d04150700361a0000c051a404500c0c40c071601e032411035403a41c0130895442c03c00341049d02840b668007441c035510303100c03210118444c2c9850840580d594007031f610028119107103802c9803402c40d0081c800030301242c400031420706042c0203002881c2e51912501c9403200024800c0d40d540e02c0440490b004440c003d1455030b00030354803942c095005090207160204542c0041541125001c000070700a1044100040502e00b17039064140d0054101d4034070303180702c03124501220790660703040c4c0140e8420403c001c12280100710034142450211820b59031151038900040d06c803070306140c094044c84903c8000501e84180da5087c1c9200352020f40302d4038451503040c003c844071a07 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 447273552 1250 447272302 447272323
    0x2061303111002090a050103090f062004091508010c020c13020408010e0d1803080f0307030216061415091b07080d0b0a12050309090a020c0714130510060e0609090702 73
    0x103802405001886d58024030507490001c0d040003024035080601e40c1d641c4001d0008020f07402c11803040c00302400b0380c0c20710704c000343c809030100c504001178204240303000f100402526031108102d40e041c4861500c400da804181c80282150680c0c03c4001c148907205070a0181c01903820040c6150f1810245020280c2c000072801c880d03940c10785403d0f401c0c5440c84049598440580000f4000d000b00300080c492540600c001503600c00c03141c0c80c0050514031400c410080c6144003090985609498441108070080c04803880e039017182c8030840f0a10b0200251740490a903d40041c90143c0e2080300c0c840e03030782251511100b00c0d0010b0380d001d601141d44403900c0c12030314010021180c41a0040100c0440450f0b21025400781c005101d800034011030138204408100100414010401d0500da5003d2040e40d110110400000029100482940c0c070420280810300090107076600e000364550313003000180000c881040e0051700c00e60f50b180c03038685421418000861203078410241c0840d0001d46081c1080421a40425000701c02c = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 447274802 1250 447273552 447273559
    0x41b090512070609030818041406090a06050d03121508060712021615060308041511030a091208160b09100e120a0e060f04030311030301060206130311100209 69
    0x10203090300c01d002ea80381054010200030600c1d1900601c00b08140c140a414244180307242000c1043c0e1000115068400e101540700003442c040040c0030140c608440001c5d0300c40f000402c200002480e0000042101290500c040c1c14003100d002c10480c4000650003444a034403a0f00808910a540d825680307549080403540c1e040029501c00f070007110031241d0f0085410200c00150040d2101d078050702d0700d17410032b428040c2e516949580c51b1400000542f900000c0c100601210030b45100c50448000c0c054003414104c505407085420070030441e10a41d801c54186000d42e2103508680d0200b02d040c1c5810070480c45150b5420043c090385007122000c00141c054114482c1c00070300d050320810000452100196110b0b0f03410780d0359981003800c508059440341000741031100e0715454030f070008940c41c2010420940c01140f0054202200050500034590000007060060700c518004500d99850304038003d4403100c0280c024040702081e44900c0c001e06200380381005081c002c0d102902e4140c40da460a4500035400280c00900 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 447276052 1250 447274802 447274819
    0x90606041d0a03181e0506031e09073f05030d020706020d0e03270d020a030b010504050105063a0c030605011202040f09090501090f0b0a1503050a020906041b0905 71
    0x1100f2482010350100300e094418507440301070034401000074623000205403074060f00181c1450000604c54240d42d82c0120188005011034a0502d00758a0805199556150340036084015170b0061443c0f488113696215441800d0b201031a0a034030b40070781184140350940403000e0004c82d282c400c2c8001c42d0700031312448040c11000c2114140122126440c3d025103c00010342004240044103111207844480e260420f00620000c20076569500103600d84003641c00903100003e0b090014409030070300d44503a60141a00b102c905080184100501d0000000d0455404804503100c1c110f64401026040c91042611134010078081000b05c0c00f8020010a02c91258500203000714418084500c064400c56081d00d0340c96103c070320a5410726234010090810440100c070199600c82c202e1000c0b50780c90480201c1c00d1b10030200c4c1481800d100c0030b481d064800040e91507000900010702013002038000a80203865950580e40d4104950b58a80050002d041039070b810b41c2c10920b00104070740360700e134000510010743c4c508445611 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 447277302 1250 447276052 447276059
    0x60a0e0a09050402010c15060b040920090a0605090301020d14071d0a0e1806040308070206070311042601020a050408060c030601090e04052b0314090606041d0a0318 72
    0x509680c41514003030701103a60000c92001080440e8101e203070162051f40041403460791114504080e600c41d42c4070303907141c642d540a04c0c508110020b21001c1c3c0c1d104100c8005007000c40c60350002d00344ca00c070341c4900800e118000403240913036202034041d1a1519200a0b040015110b84205400546812a00800000c5220141d0486590044000e84400c2c002800600c1e05d6410442e0454080901038101c010345447c0c0c03e8840001241006001c3c41180f00c0e0b5180c5906090003a4080e2500308060180310515080456010790b01400c0c40030f035011542056140840e05480c8100884812001c140b04201c0754000100f5900c8650418014000c681004c01241d00030340c0e42d44000c00e0103010507a030217070000d080a10304000300c400600c18950458040e80503036483d500e280030300301c0000c1c46217414a40d01c07001004080c0b02c89600752194004102c0725401c02603881c076080d4150703500c48100174601845142e95900501101740ca005402000c641494200c881e070700c0e0b980c00e001d88003950742180100381302c07100400071 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 447278552 1250 447277302 447277319
    0x603030807230a020316030c0507080a170a1b060e07050a150f0210022b0504030f0f0c0b010801090c1a09040f0b04090b09010f0209030c041a060a0e0a 66
    0x1640ca4404400c0c251002c115031541900c12907100d8200750301148810702138010808001c5812083c801d1294131440d0f4045c0e6245469400c110703c07030380101010380145161101242c04440d58404145146000c1c95039402050003c0c0da070661003240c4080b40035640180303c2c2c2044825400000151060400c03190b07429901c0c0104811902980540714200344403400b02d0004600440103040c0a101900580e0b42801e454034001040340c20044101c527000e0006021a0307640c0300300754108148106524020b20142c070381500c02030513a092000c8071400300041e140b402e26107076100b400c0c00c0110796409620300005580d1020018060704c014181926403256202c0001200644a082c4803584d01c0c81030000c90524040d001000020040c2214007522030b81c4410240100da0703034521619103010f00c518404099070408406c01821500307101010301002d841040002d81540c1e0000e40070010729000c032808075404070034010380d100440c01803085a40044010460b00281d50300805078540ba080b05030f500721072455451551 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 447279802 1250 447278552 447278567
    0x6210a0c090b0f0d03020a080d0f050f070203091504080106030b0108070b2115090103141c0c020f0a0312050a0e01081501030506030f1b0111071a1c0507030603030807 73
    0x21250300c60420b10343d071101420074007000c00c5460300a0058804800c082d407074081aaa104103503404100daa07170b41907510003241600c540d030b400c0400385c1c0341400f4074035055101a5036032140307565141c03080b44208040d80c0b44400180441c0c0c040c0202d00001d2001540d04d2502c110015002c0c0034011842c094120003280c1412001d080e940b03d504009045403007202954400c1e030305800007800f000c440c9028070040309502e0316601c00c05402144504010030380005400035071400e00c218400c128540c2d03961184005001030b8072204401109404840d16446810240b0004400d807800e0340c00200b808141c405070000c49074211000d0310442005403501c10a0071883c01c01100c210030700300d680907080c041c030041405c0d0651190b4410f56020401070b0455100846695a03980782040c801d151240c00a40e049a401c0c1c1c42d40c2c807180500381c2e50b94400007080d0440c01c000c4407407100014943e4498482c0070218003403001c2088070074840c01e18140640c041041d8107021f440100030b40b14500091b00807031800f0740450f1070103109180 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 447281052 1250 447279802 447279821
    0x40e0d1d03030f0c030d0c08090d170c090102030715091202030a02030a0e0f220b040b180405150f1b030910150803160209070516080306210a0c09 64
    0x61442c000741250034a01e503401980e13209860744400d210100511456100782440c800254459140c1c074034118481a140c400008075072400c000f00402c042d0701315440144425003000940c03040e070f5111084000102e245008001000d031440301000e10318a01504140d204200050256051464400c001c12040c0d9481c0705038060003005a00403c07060350418852400e181c030b6000000c0200407a003031038000041054810b807800c000c10082000c0761581d810014403d403001448185c034240140404240003c4820b002d07070902650220312040080d0401c0800d20900503c510300320481c00090800c1d4846942c40030040301d1107440445040c04441c001440641030302d204103042c030300404030911503264030805040340e201d400003281c8507000c01094801081c4041c20040c05c5800140e51f202c402401004480103000e0800418000c0c20000701c805044040342244e407403500702e800c0c540e4036200c0d40081441802001c0c03501450140c400c0f04443c0e580c03000300d82c400304940035a114580b600d0321000031400b101c10540 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 447282302 1250 447281052 447281059
    0x20405090a0f020925031a040c12020d0e030a08010e070c02091314032214030a140c04060902030a05090607020d120f0203071101150501080a0b0f040e0d1d 68
    0x101030b00146801000703a54003104141c06083c80e0003407200c2d2540242550350004010a03214801d0b03040482c07803205d602c0201d44084405002510000e04090f08071a6001c500c484800e800003040e01003181950401d0344410a1003040303035aa05900440101009000e020b541d075440700a001050b0040d1040780703070b40c104540007002000c4035103404440030144a5407020485080180c03400505160030148090800804807881c0c20542405101b000e61807036a881d04050794001004540b0b402c1520000340315546154440980303640c01c140340200501c0d08244491b8640d00c1070901078040f5001c070700303500654004c540046080c01283c5811407000d4480c10115030000041c1d04c042c0c41d10004500c56100d0303281182414500242d0000c5980a400699000314ac5000c0861a200e0804540d61402d125030030b00f0750000c0c0703502d041391400c040000700030180103820004800e0311108203214a0345c408400340541c42000b4000c00040412140e05030301e440780d0b00c2400b0301290100103a0740b185001d02d00c80040c00c16004 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 447283552 1250 447282302 447282323
    0x1602060a020a0c0614160201140c070f12051e070f030c0e09070605090112060e0408120c031003080a0e030106060e0a08030f07060e0712061509090309060302091c0807020405090a 78
    0x1e1004903420b086c09200382d042101d100455020892942d00404411000703001404915017040da060410080580c045040050040395401c0807841c003191180325044007480e50382c1e44500081c407642ca0507400d60013003650030380e44040000400414500801c01c0f20551a01c645903540d40c516055160106441030304d010650811031050150b105400610070514a401c0000d90b071500e46800503070350301040390201c1e114007001512a07106050744403215800f80c001c0ba216403035850690b412107080c0b54113100040201c40007041c080d003594082c031000f0100e80c1003c0c000308a40d681c0d90b040184401c000e14407003400b801007080040341c98100030040368240e01c04015804c1c60202d041c0c1d242801040c41341c4601986000c0e01c2e030301040d0300225880083c10a8002e4401040c4d100d039510620040706280d501c00100b4914201c0404c0c000ba40083c1c4940480d00e40f4100141c40d410082e010035610046000448241902c0e44580420000110040c201e07050003540c1c10410355940d40c500503520343e07900f0006070404958 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 447284802 1250 447283552 447283567
    0x110d0e09060d1a0612030c030421030f2d09050f0d02030a26030a0203040309051e150c030a05071a040206030a050403020102090909010c080702071a1602060a020a0c0614 74
    0x240c01c00d40001d0007411402c211745418032140d045412000d81400e55400004081001402c071601c0d02c1aa50f022142480c401c946655014011801d850140301c213105151807244008004000e500a07044107186000c1a41007810300003c09254040c02118411400d0710f000c903159041100180d45a213074040d000380b4954005480f0280002581030321000e03050b52130f2200c01c03c40c244120145005070340f07030034001d0f07120b040500c0c003c1c00b10483c0e07400150040144d000100d0007107002504100081e00e003034424101140c1d01c0707401400c01e8400c0d01c180c52254440040c0904100b54000d00420109001d50512424482c2006c4000315008003030390042d40c460790074400305400e03c0e1182d0100350060b00c03074000107142c6940340021030140c9504503040020741c0d540d1040c22040701e4201c00c085074818480d2000d003000c0c07410403001c1030000b400703000c0c42c86d0010000b05040980705800c150b91071401d82c00030422500c030301e0350810095955041a8003203891181c200d80c00560580100500c954440e8080d0509080810 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 447286052 1250 447284802 447284843
    0xd051c0203090f070b030114060f040303081e0c04051203041410090915170d02030a0f091a031e100b0a050702130203061c0507060f110d0e09060d 64
    0x8090503801943c02801c000214807801000b100d0024043c0155a540300c2d0701d041aa040c041c2e00c1e044080d40103840401c00006400c945100310303806d43e68541841442e58461401c0142e10400b00c0c40c14030b8041025805100300d29640780058802c070751003203a200c1615642104642d4690080e40324000000c1410482640c0034a45914603d640d0502841c2022a0585c5c419011058580500c1011081182c9120600240e9038144c201050300512500504007050600c500a50b46e00c00c0308240404c100701000c240c5501d611598400000384520350490b590600741210f82c50080e48180c81400c0c1d84030081d644100101d000c240490f04c42c50b540c001041c40c862801200c40b0b01580070b040b17520100b200410601c00103030b685441000002d104070b2401a1a482c004051001e403035181054004402d00e81542d001c0014400140324040e1742d0286012000145005002d690116807102c481c0d0540c01340305c2c032485225901c2070801d90841c4080300c60304081e460300418031894804203e40038241c42c0d1b41d03a00b07950380043d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 447287302 1250 447286052 447286057
    0x203060f0a4b0c03060612020a02061f031a0a14070c020103021e180102010b0a2304060b0f0307080c0702130c110102040602070810022b020f0c0c030d051c02 69
    0xb9500070003000d0484002c50780310489041070b0b00391021944c0d40100340036150784010080c20b444a003480c214038011440c14080d5486500400e12014181207407800509500d00e58914801507a1001000080224005000421200403600404118600f22003560400d00e0304400c940114030780d45448500d40503e400440181d4001201602c00c0000e100828440c221464010300d2034101c80200710f00c4059520000a00351100c95107054810982c0801c2402054607811016902c4903000040b00c001d0083c40011170050403941d03001c400d0044e000b08002e80400c0301c410095103e50034655030305c8255540c1900c0040d0500074010040d4004142c3c0d800134102840b0350740052000348442c2807507040d6080942806003a079005410000041c0c00c808401c0014502c204003051100410301011750401d29451158440c00b081101320b030b142c0d07003080c0c207c1c91a0a01c0702d6044400c00d94888529079070710306a244020350349110450049009104141c2074000c010f11a0081d00c0e01d0042c0320b04228546e805030390051000c0d4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 447288552 1250 447287302 447287411
    0x3111905061c090c121406010501020705040f0e1204091107080a051e03090a0c0b04050609221a131406220507020d0807050f04120305070203060f0a 65
    0x481d0790f4800d040c0851540801c8400030026840c00c0f4001016501d41105000440c201d10021548294010b00491b070b000304880055550035507001500c0500420701c5005000202c07462881c5024030302501c1c04a40c920f00051040e5122400144009101004c42000601c81c80760045c1100b50188002c54290344190000d0208901d03894244816030002445919241e005481c1c4d25000c1d841035584008012809028800400f0b40d00c800904003450103001c204284280c1e914680b080d42c00c0108007185191114400410200642d8200a440700c1e44001e142000c4010f403000b84140c0074049603e403400c226014030601040304205055040e1a07010a1001131030103245c40710f940c1c2081501070004800d141c03045500c81c45040d8014400a9039042014040b1a00600003004009007000400c405a05070802c5904542005903d0f002d6900303242011100e50041e808025818090b00007481002c00341000c03614040c0c2c003c1141003241d011450394030341c0c0034510080c0440707440094240e00c2c1c000c29580c00204010 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 447289802 1250 447288552 447288607
    0x40303091a0c0f010209010e094503040603050a05040c053006100605160b18100605030601140f1216170606010507030806040b1201060311190506 64
    0x1050211582e090802504110304070703840e1740c0468080280d41e845201084420801d0f2003a0a81c1c1c00e00710310132240320140c0c2494000301e1920003021043d82c1c48801d5580d00c403c010310381c401019100380007216140d0748148030320000207040c10040b1305c1e00304081c40303018000c544c0030300f480c9065031900e401d00c00d541a9015940c0f4a103d10709009041484a402081011048a00113880319107030003008448503100c903800c8071040250501906005910014119201d56040711056040e079503158070701e2042000841e480400c5019007d40c200c000c00f5103030000303000d46104030103403502d0b40e88070350800e14410b00000c1c4081d801501111403811074140b4182d0808030300100360694440d056140c204910780c0c2050380c0a1051076640b2080da6a0300c2c4010300050380c100f0004d103402482c0450a40340108a0707140a0300041c4503075a6a04182c0782540c0745140034010250010080c45195924146440d00d0030302501c07603600a48101c14081742d410040c20890007640c000074032140c145904c1c01c041800114130703072443c2c099 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 447291052 1250 447289802 447289807
    0x30b0f1002070b0d231b03130c0602010c1706031209151318110a030b3f070305150a0b0406150201150f290a051b03040303091a 56
    0x11140e22400081081c85414070001c1810300000030900713031581510305c07040c0d0a21000400d0200d5541134903c40807860300e0b0001955101d44070306030410210708540b0001410400030301c000045040d0190071070207030301c0200d8907200500d940d4020900c106500440f0802c0d07064202c0e816640e4801c4078107000d0091020080c180c80c40c281030304003004066501c09030901c0f00c80c00031800100f03c00312000c003a904808074007071000d00a0b1400003411030700c01e001d90002d4000f81070300d9014050168a4096007012929001d030090030507450340952501b80000d2010001308118070800ca40d01d0303c40400103021003101e920000900d0110340b021840302c541b608c050240030a00340c03264184442c81d80ea40c01007001500d1900300000d40503d1491010b403c5800441c00030701c0d4403468800401c5106c1d82d208102e8120f40c0031a03903c0d08110300c001d244d4801e01e40e2040420100c0f0b400458291040d5a02002500a8200841c00e900504913440b0029959014030302c8000d0004070031040c24003940c07082c070010303117030040c0152941e50 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 447292302 1250 447291052 447291059
    0xd020a1733071812050f07031110021209311b020601030507030605181209011205040203150a0207080c0f070b2701050c030313060510030c0302040e0c030d080106020d030b0f100207 79
    0x5003083c00a5100b650f512511030320481700761a04600c0c4092803c803038002054954900cc500c40305034001d218641c0d101d0207c029044280510360f00400e0507101c00000c0c0d0703616010080c0300000c0203000100e4640302d0703543c0a0681c00489400015443e05a13034019005182d001d2542d0f81e460301411005110359405420b20a641e01803d004001510605001d0b100c070a0700c880c07403500010300c203141030480600050b0401c0f042c030000d40c80204101c40c11040d950034510107070303481850b0389001e0702c58003100408801c40000c4151801c8000b05c0e01c40c21107100f500560f40559620058400c090140c1d410003c14032089035645944000d0844140c41c0801040c18001e00303040e80b90f10054159041220404118203200c101c0700c040050b18492694031490f01c40740a80d000d411512068500480c034000240141d0340e0300c00d01c505040082103901f80150004044a00741c9d00b40c2c9000400c880828491781c00544a0300081810b8913001e0700802000c054060a40031408440004200100361168140c4082d8001c104011 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 447293552 1250 447292302 447292333
    0x6020a030b0d080c0c09060d030c0c170601050406090c0807030902180411151908060a0f031202060a1a100c06020c0703020a050d020a173307181205 65
    0x1882c60203030762031503260f04c0c004403140d003492000280c40e40300e60207403c03c100750780e5a005000180c40703030189440c1c1d400703e41901c1c00301803083c0d990f0005440801140b43c0d00d9100f520020b4814142c030415038040c010076946d040c55000b0386100e0600314000c1a0400001403815100f0b600102c29280020014486840740c174451014004003940c05403181d6808184180640c10550100890310504128031480c040101960420700c03800d4003051010807900b0004141c0564402c1d01d40000703010254980c0441070f07a0f03840c010444040f41d040803409800b5502c00141c004001d4407400c4014203102c542d400b003000b500020464100b984a0b1003000b40603001c1586c1c00401d0f030307078405480780c80b5980c80286409821401004101280380e44510302c41c1241c928000c0c010780311440c2c41360071210b8500121220146111040e418851072400058060703121680c001c800741440000090310442038092041c0649454800300d83d07240442440c0544d0103111038041084540c0326408103902401101960702600194002 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 447294802 1250 447293552 447293569
    0x110a1e050a150603050d0206192d1512080a050d150f0513020c100b01020304031b0501080603160302060a020c0d0f060509071212090504090c090e030c0a06020a030b 72
    0x200038030941c3c808090007048010400e85100150f18001860309261214007002990f00900c2104685501c40da03803c0b48001c04100c0d04101c00307140803400010448002810002440c040480440c1c2034141c09000030300d214044010601d030f54204403481d150801c008003c2d68254081c0d40c0c08164242c2d103480b104800755054468070041c1c0810000d1003031407460403042060300c00500d100101a1441003185100c41480001c04100800d01e46002044461107040107070300b036000f40d500140c4000c210301600d07084226642d0f110015124262110125502c40c0c20505688040204800d00342c0d116000d030070f102525010002d400032102a04c1105d610114000c0401c03403403100888200c1d0b141e00c0d404110001c10141c1c1c001c203540000d24a0052500502e0160920049141ca150240c1481142140c00c030f0b1440c89160b0780b00c05818054010320800e4841c1c9130030640020144034803601c0e545002c10810810901000300c85021004d00010702000d04240c940e00c0081d40a8400541459a141148546034079498070 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 447296052 1250 447294802 447294833
    0x41b0602030a080408040506160b0c0f070b100812040e10030506040308040213020406020a050f010e060115201605040203010b0a03020d020d09150507080f07030203190509030a110a1e050a 82
    0x40220b8416914039100004100182c00e00cbc250708403d01111100c4401e16050310f0441d13802041c64003080d00c881d0301103a444020382e00607040b01e019a240154501c14514010001c81e00e00390710120241e640c0c01c01643c484102c90200500503049139002c240030038450010b894019000508038281013111251640072030340958007180140c0c0203204010180300003400700b80c0141c900d460092001205028103640c80c0c000501500c7c0349003145130b518001d41840782410080c81421010306400e1042c1382d060740b680c0d4080101c0801c0c1c0381131031002c000c9410b003001d009982c100d030140312055007010314500080e400394014844074010981e00f03214221454190b40280b560b403601491010090135070001803101039410090058060140f08800e100c4100412007070194072040a1a00603100d40f5a07101c1d0510000000040151b01410201400803011000c07004107100c042c5515440f0030840701824182c1c039424084009000c0f2152051442d05070f0a81403d4014102d1007030080d5628580c4a5980900d504400c44 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 447297302 1250 447296052 447296077
    0x103141f0c141902012702130e3a0909020705010b1507031101060303090605071b0b3402041e0203040f1203021801270e041b0602030a080408040506 65
    0x3a118059903130207120b00d03403203030001ca1809420b0740b110b2108403144001020000703019055849007003401c40c80301d80c050605c2c030300c45405691039404442030503105007203058030498484691b05041c00071140300040301d65150045ea1141044a4075110340d1000a411a0a055415548071140802103a680d2954a03644034061060191181d0090a000340304500300ca1070000c00703070325100043c00440d401500d074104503203651416a80d258054500884c00d4082a900440b0703252241c4000f1425a004a003d845200c501c0c174250341115105040b01464840340300c1c0000c16542c0b14030254005810980c011441130410041502c4041d500d0000c41400c0327030b004440a60f082e0049242000410900031035050180d01645401c0d414044448000b1030219004e06070349041c890703083d0f040d0b130003560400400c01a46a0b82c460a10740903685959011940c4c40443d070403150b81014a41580c802d03011440008c1c20380f0050f60085041c8003ea034016200100080d205403903030b0005106c00103041e513440b0300a1000c005043c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 447298552 1250 447297302 447297337
    0x14070c141512040230011a0d3519020c010f0c020d02040207120503010602100509060f1803070f050d020610031b0b03090c1318020d170a080103141f0c14 67
    0x190b6500007d10b900000181320300c001c4c035031260124206000c9489501d0b526650440c0d0860700c480c401034030411000402c803821f8800314a4080c9101c410300d25044d030041c10380940d8020700b2a4801141c2008180002c24081140c1d031a901003d400c00340c910b48007043c8054401880c20440791120140c6240c1c520104000030800401844490b41c14040c1d0140c02c1007400041c403050410040d41500c03020000c10703040d40c040140000540d01000f08000082d0540e00c103055030707a156000e0410b442d64100301101500d1034811445100030a510004e06140f003040003c0d81c06840b241113903210414042c05040c004c0c06115040360202d9080600001940950b50f0200201160031101d024054001e076a070078552503240c0b40504d5407210352042c004107800c840d07048a00b4001002c0c0391608119a030311150352000c103060086502d142480e00b16040b507060300c3c060700f00d10919400c0030303505c2507682aa011620300e42e4480c00b283c1001150558104e246511040d050115140790b400d5400d90480c3c00c1030350902c100e075551 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 447299802 1250 447298552 447298571
    0x215150d0312023601020604080d0207060618090b010506120712020c070f05091b1b07030602070b04140d02190f0b07020d03060b040b090114070c14151204023001 71
    0x64130340b4400b2101c428005003c040c94039031183e009a000760300e200244030345c000849204121041d4032010150490a01a80103100e44021040050035441303000c80305541c0d120000304203450203d040d102c1000344101c1d408a990740e0174100f00c0d4a902c8134282035400d15000d0200300403a04052160a0180c5282c143c1c1016107864082008030307481c03000c2c122041141a24078080b4154910328111400600012500145251465400e40c507104241c0c1c030140042d840800e4010801601e4210325028500601c2a5118601242001500c80306841100d90160b808811580484400e407002c004219025040e48640702040340c03036080b048a400c80d9a040181c00040e580c0d4501a01807240b01e000d020769280090401d82015a261068451015568144842401c814281d010740d081104c090a5201c1c1c049444159a400243d0f00c186008a02038803a90f1400300c0820000903c405448510070010a216003c1e103d6400340140012300b1083d0031140003040880944c0c19811400071900c04108500020355070300c4 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 447301052 1250 447299802 447299887
    0xc120c02120316112409120f03091503010617250f09080c090105090912071a0604020f071727041104050102060106030e0c100215150d031202 62
    0x415042c407610030941c02c1d00c040b18601c01e00ba5100d1104400710f650b075580300c0188000444001f80401c440700d0900c0790380c2e4040c10301040030000e081c0c4500c040e10b43c4400c2c2e0700401010400c9010902a800c00242580040c118005540f403d5641060f180e00c0c4a0909000150b214000301c6491450b49004c0741c41e681c21034010300c1e0300c510790324010481440a8440d00707040400003200000184180743c480d420040105216110502001e4070b5020f22400c2284d40e40b460f80340620000c2c4441c2480d0582c50340b070400180740ba040c02d00841e0048503a0150442c039009043d40d0319808038841d000142001c07038060200b1075110b01c1109200424400c0c00d0400303005050000108019100c80c110044a04401070000b0482da03600000e040f41550014103001c5401840d40044bd464484040340d61503008032440e880c86122fa402003103d00794084420f00d9424682e55080b240c0001204c1c01000301c0e0800c400b00143c9000c2403003000c04014044a000e4050701d44404014060458034104800200d140d200e01280d141d240c0703 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 447302158 1106 447301052 447301073
    0x605061206060c0f1e0d0f030c020c03030a03060807080a1a041a1315060b0406030b01090504020f131406070b1305070f060f0c120c02120316 62
    0x1e041c0c4c9006655407020030701d10f8410750310110050485800c0414180c0c102c4120791100c0e06181208803044006144c107c44080842c050010494444d031350900060403e0b041c00d40d800f04e031031810a691700d0709102c010f130b00610a0340d111640c210009808a000c0048003500d0f4040044aa9624108402402c5203195420501c11040007002107440d060300412540741d00034003007030943c190741d03950307400c201d980c42d01400b5140041400100f05080c031070740000b01529010b140c001d102c15910804601070307030424000c11001d5038003c9105000000724000704001450911407100342c07031400c90040780e080d108450b800f0b0080400d0740000707000034030112055210543e01004072143c003940c48038140d1003c0c105002e807100041070341d1003842c502e5100d107400340c0c12540c01400b007581046c8203610640312452040703002c90304040001c0c0d0f0140c0800c000c0c005080c0101c1754000c068040c0f2110307e404480a07 = true := by decide +kernel

theorem cover : BRFrame.Cov 447122302 447302158 := by
  have h0 := BRFrame.cov_init 447122302
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 447122302 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 447122302 ≤ n) (h2 : n < 447302158) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
