-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2674
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T07:24:36.875981+00:00
-- url     : https://prove2.me/submissions/f4febcf5-58e2-4bd7-8203-45b7db939f59

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 480755395 ≤ n < 480935251 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 480756645 1250 480755395 480755419
    0x1e0f0201200a05100605030d1b0f0615060315030804030b090109050a0c09050105090610030902040b060a0903140f101104030c080c040e1204030803060f0907090e07080105100e 77
    0x741c144642240140b03d40050728145440c400020240d60054020038846d8128000c1015401d0f000ba0361040c00209071442248801082e091442c64020101c001804a50800003030705240481c07814004180e5030180c404210710820152100c0251009000040035440c01300428404910740048942d481188003001060400c0183e950505120350040100d88080304010144041400c502515001d0071302a107011405140c140700240450708034040220525598145070019501c2d2900070007a101d0000d446213070381d5941090003d01c111035521003030f54601421301c03468940e298040369061a08005074001c1c80030300f10000540004196081e07826414040403c00000019034140b8480010803040740a0404c5096840501050b29203006c40f00c00190888440000105114000d540030f50782c01c10f903040d80300c0d541c14002c00d8111031059000e941c454000004c0110b020b03032041403a0151550070303004140d80c2e100e11100f601c04070300a001e40e50707010005c440512112885680401c045900050020409007 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 480757895 1250 480756645 480756707
    0xf0a030509030a0f05030a0e040903090902070203010b1903020f0405040309051504050406031208070c03080c18041407020d030b030c100507060e1b03031801110f010c0c1e0f0201 78
    0x2148183c4c200c070f25801c04111664800e400a0036500c00340750035a03041c0599403055400030289659406036200d000d5000c41e141301952001d5001501200c005016100000300f2000003d40c00a018401288039400140e81e0b48140e041c1401014041c60740f50300c074025664200300030019081d2541814407000754050000185541d501d0107200c2c01140034140f401216007154400030301840b8010300c0076040c842d86908910000b54411885c6521515040799a901c40c90350301500c14002c1028040198410704000200c681001c00302402c6001e0340b4590211017000d40c3c2c200b802e400b6185000c0c5919415040175840e42d01a04209600e0600e10b229440c1c207519001d40d542d070740c000720380d0041191103083c2d1003450041e6004810010020004108500450070030803150030071219200c4410f0315071304004501e100c407402c40000700402c1c007031500e18800900000c200641d00415200600000380c4510484c641d801c02c1001152540707081842e009100700050200c6900152040b521340d22418880d40d84400e8040024 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 480759145 1250 480757895 480757913
    0x18090e3003041a0f0412020a0c030605090c03011109040c08090c1e04050a06030209010f0b0306040902030a0807050c0f0d08030a0b13060e18030a02060a0b0a1a0705010501080f0a030509030a 83
    0x404a207080a9440d0500381080d4502c86d03c0e480b068802d6510026003440820b400d900c21408403640301e103011a4581c0d4640303102e410220348540840d099801c010900e0344019502025000c0100166030800803002e2000c4110f401c031400b03503031200d5107410103000b2009508040301c0c55100588103201c041040c1400e0804501114412120114100d641307000c02d00c11458003240003401007044074000b402c50750030612020300504c4013916142c0f01c2ca0343c0c4e0610a046480601c461900d43e40c20501c2942c84466600703000f6110b094000780d0301d200700108000316070be5140039400c0d510302640041c0c0c15070440e07541c01c10034402014110340207940002d6804038180d510140c0c3c020b40d0041d107c00050b286490401c81001c80340c1c403100104214a5800610140c0e201941c00182c080d8080740c0b044001c1044001e88000c280b042000f90451811140d119076003400c00102c0c0802490b5040c4607100801c101d07130342e130048591501383d507424040250b0004421440400e02c00c030003411406070001c041d18001d042e40d81c0c4500034 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 480760395 1250 480759145 480759151
    0x90206040b07060f02181c0503031e011e060f030b030d0c05060a09020d0201080c0d02030a0506100201090c0b1305030d1e260718090e3003041a 63
    0x56030000082e070b00100b0280d80110224408580c605601300340754080d41d10000b041c100c11542c000c2c40385050b113400d6111218034a43c0740e541c029058903a00e00700b510040104245100c60050b086a00c100001175800490041400e1303280c1c9004602030b194100780084440c4001580724a01b0540c40700c01d6070441e42d07000e200030418025980c1b1401c810219a2078a00d0030554010203101d00d161411880c000547c4420203a41803d039424a00012140d503048452811405a5006244000c2c0701204020405015a00c020300a05044820726820481880101d003607030002d000050003c100d0b9242000001a050007070300c005640032040040494440010030b14001240c1d44d88000a18500045050465043c1c580851072040e807402000b08d480380820492a42e4040340e21001c1760001d02e00083c00e0b42c0c0b0440e000c00d444030a82c8801d9500780c1c2d8030741b00140504000622030310503000d02c2040700c085c00103440c0781c00510003c00000014000c54081d031440e00b500000c05c00e48024844000101c100242e015001c0d01c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 480761645 1250 480760395 480760409
    0x19060207061b050c0f060705030403030206070801120507050907020c120303060418121409030a05060906102106090206030c12060402091c020f06070c170105070f08090109020604 78
    0x314500d4000024500346030b24540b0790a6241488011000c50804584040454803c0e1022101039051002244035486103050180190001090110802d43d001c11070a000b01d48680d50350316166264030312413042c0428180001c08a0b170110500308031500b82031190540c84411401a92682280300780131803058507812800c2580e0b904000108003251410b0311803c000042e0301080c001c41201e0340d43c0d4402542c14005010010311110b034039074035060340d00031044814054015055a60b480094034110f651402c0c180c0d604407003400340c113000038484038104890f80d003101c040b02e500d0800c640c5600d8a00c218010b851f10309450b078503120350001c1e015072a280000c40c083c4a1048541d0740d1110691207950b10050040c0005202c1d1b070042104280540c1c882c1c0f02400c0e14040b0382e11221210006200158040c0308150409422403004030341d4405120390b0401c0d010440c0c2584d00760340c01e010842610306080343c00458400c0042030501c2c0c00203002900c0386000c25407055010000080c4004260006000b60b0000d501a903 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 480762895 1250 480761645 480761653
    0xa02071a07112e05090d0308100b162d06090515090703020d081e071704050d02060c0f07060201020903010f060515130504020f1c1104090c0c0b09060f0f10090209190602 74
    0x200c0d444270700c5200e01005244640e026800c000002c403000001c02c84e44800581030fa2406503e07138840032078202d0401100740886500012180c2940ba00380e0103010f103540181d0301c600842540c48644d509800c0345e03a1043c05810050f2007003604682c01c100311a10481c2c41901d00c51024842400901204444610003107100a112a280d01040c607013880e01c0b020000341000c481500340800c200b1500da4010b0300320402c3c0e0450f60691190a20a52a4a41480d06a16103000e1050b04000990702e50103500a01c81c0386825802400750200e104103400640f0443c0c86043c0d0810b40d8854200ca1100d180300241400b403000881580da078540e5880000c06907009075145144507003001a4012138003000c141d80203118440300b0401c1c000c1d45d20314007440c86640554420030398a41d40b02d0146069991152007488100c035030040c04120703d42031415406940320001c66442019801c01d0380400c1c030b003e001c090300c0c902c030301c03003900c000d801c0c40e4208040d102c0a90400d18000b5042008280486030042074015990007030308281d8014 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 480764145 1250 480762895 480762901
    0x300702070f09200309030c120a20120903031e090a060f0818030408010203100905060913120905180a05060a0503070b0a02071a07112e05090d0308 64
    0x24441081c59102c420010301d05001c08200b40c40b0311001244110200900c681c803683e808403401e0461140e890103004a02a4150398510708004d80701819814800b81d482c100d2000b03000c03944049002038590301031002e80c00b00328480d103a0040000184600e44028040c0ca040120000c20030800d00600301d5801b645802c08502c0d40910305240c03100304024181441c0c04130452100000c09441c1f404040d00d008985035548854501c45c1d00c080044030020a03903075008640da860005982809014980210680b07241018082015071800c0120540101481d13141c541d440030389a0307100b400c8000294909010f01905030400140d40d6101041c450aa41002d81d00c2d03000741c50600c10140480300000e004901c10031440c40288074079100068040280c84e481d0000325921200084140e1030841e1315031101100e1010700d810000c10000e5030000c3d040043c0b050b40c840920694000410151401d01c07202004000e1700403800c9074107514444103100e5540340c5402c0491404070f07001c0214407100041c480c1540480c50000034 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 480765395 1250 480764145 480764159
    0x6050c19230301050108070e030106170a02030f0d081801060f090504020906190308030c09040c0c0b011a07060b0409060509030a021c08190e3301080330070207 70
    0x201d103105050012920710340c1081d001a00149000d4011800c200074030f420050f45032425805080503010700c005812807444461800790383c4e422014002c0740a03000b4103d2a119008002500108801c11612181100e40d2005a4200790a5a108034155a507403038600c002025081742ca10003025041030800495103162a0042c00151040034000d00d0082d2406103002d005103510394403100c00c0da50302c15405580d13034513032881149180c0580605554841e20306480c00c400550001305090506200c0c0c4c40106907a80c0e07814407480a1b901c80300310031002480400c181d0b80020300661004440c840014000503005a0035102c1c00c040321411601000c003540002803034a00b80b0307010031000c490500303424412040503544040040c28030384043c0030b10100800e90051032565420750307085090460344090803210b0f8500d43c2c2c4840c0c00d102211031038015090510445001c144440d070044c05060700c006100662401400e1071080c011031400c0030201603043c80c0d088004542c8546289514040c00b40d540c01401c1c00c500f4462 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 480766645 1250 480765395 480765437
    0x621070c060519050f0606030a0b1f090f0e0c071e050a110a050609030c0d0c1508070905010c0317060d170c06091507030b01050c030a030c020106060c0503030406050c19 74
    0x40a003002014030804c00e0507628201103952140c907036a40410140c0f043c401250501c107642f01801c803030300500c0d5003170595103070712050300402c5804ca10030800d01c0076078942c040b00d14210103440003100e03500108101c0740490003d100c901202c0c1410310200c039a10031070385c5441c0d05210316a1411244181010195045071500812500c050001161580d103000c1000000030f03503030300d00b00c1c0302c01e070040b0314140c0f141d402c0c005841000c000a0064080040d00880c000d50010140403003103482ca0041000d006011407254440d4540022683e0b04d03440701d02031141c0c0d450020705e00e140010b02643d8014800000e080c0014251002d2440035255245074503140c1c1c6c030324056182807150040c42c5603520b910507070020030410351295019410034010300b400a032842407680101e03220311502c5840c800c0c5120024040d40f041c0c0d4180d000e41c22504941d80204034064540c101126650256080a400340e40140041404914960b0205030400c401201c0280742110500e164816083c0d070080744c0001c40c00070407900d4280302d260301c = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 480767895 1250 480766645 480766651
    0xa02100c030b030309042304050102030a060e010323070b04060c050705040203040314030910090f210c030e06070c060801030506061f0309050c091003050c0621070c06051905 76
    0x81400d11040000e240403a42e45d000e152401d17482180c9610000d1010300790003114035034116010094081e54038050a0050207948161245410b66207040c00020707115a084900505072a4008201400d0580390400d254040304001003002003401461000200401484010030080c4940e403960360322224942441420314010303074000c9004c4c1c0c0c0104100800031780e0002c0d02402c0709a440e0b076402e0b16500c5841019282c5000d50741c41c81495840c2c40b145d03c050144212200320103901c150300c3c424446401d03915603d0103032000060302c2d000c100c50b10304c01d000003030094044d0301030703280007611607802d2030081d403281d50340350031554000404158140018414484244615075010740150f540103510060b000803808130800810018040694810b0500c040080a01044541d000700505014090400a403403031040c03266031008554510405038902401d00b407120940d50300c550401c1e07000e01c0780030460010360b0304007a009054108010320002c18000207541e9103d158055513420100380501084200880d003164806 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 480769145 1250 480767895 480767897
    0x1003061e091125030507150e0609010b011d1503010f15090f030b132a06110712080f03070909061706241206060103181a18030a02100c 59
    0x41003842030b0300401c0410b820f6a240c00035201281d505040c02d0880d80e074002e90301c00400148403485601c000d80c4054010345510b410000a40d01c1702c0d00c4000c0c0b810700702d0309000c03004e60114201080e004507940e140c011942d180e50001d0241a10088801202001c650003608160704034402c105c0113110a100c0203446188841d918105844180d003404018400e04840f84001003605014130300051105a1000301403040e41c0d8010078028850091a18143c640b0b017900100d030795181c0c2d0700f0100042c2c4d98440c0e4081030154403090050110135080010a002400c9041d0080ea1152010000340802e01382c04c0000b58415003050380e41a081e941460794040942e07070154416645e1030014541c101c2e41c0b00b004a09181c001d00504110207503500180d0300c1880020048000a81c4800c885445200084012400b103200e108241ea017080141c20071103200b81c0602e5800009489280340e02403044680002e58420354104020200310101942c481a80714555440800316100603080414100b549488501400810104c1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 480770395 1250 480769145 480769147
    0x7030206100b0304080a09050d051e0309090c0a05040b030a0c03051503151b0d0501090b06040305121c021b06090607020d0c0204090f03081905060f1003061e0911 71
    0x50b000004a1500010700060032446000400414042c040c0f11404003d0102a1507040301042d07030f00b031464035003601c0505841c80b4107046204041036030001c0221480210001c1c849070143d15100c03104075194021068801c00e200c42000089124002440a9031184030f00754004a803035403100034000c050382c001521107003500c0340400d50a41285d80100e414446e0b000c003280340b08074943e10201c400000388040c10b01c00c03090000c0040e00b20404022600101c2c142d80c441c140503c00703c5120418444a07204510003e006034100d00a031707141c2000c00f40014000c0c00c80611144145000312013043e0101c0e0700150404c41c07505030413488000002c00500c944da43c05194040030340300d2490f080310f001e5101c1c000040381e10100f1207081e60741000c41d5116480016042d80000c5410134401c0140f078090181001035801d500c040058041c2010030346440e01505200e0328001c0c1803000140c01035014022282c4110141c001070540b60040401c0e25000200d090700000407200640420034984208603045990700c691806001e10 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 480771645 1250 480770395 480770399
    0xa060f0b0a0c020303040e0c041a0a0e0d03020a150e0606190b1c0f050403110604030e040c170106052a0a02150c0f0318030f0c10110d020106060909022a0a050109080703020610 77
    0x2801c20400307400c0d14410758401d01841c8241c901207050610390c1c42e00070241501d10303820000088481c3d00080840b4124021515291500f404000201038440d4080d6400381c83e0510a0000301c0004000e06110014080003c0b40402401500401d0302c00550f4803d41c074594031000c20080c942e100b0720300e200e08d04400001d4215802c00b41c030010314015401100c14043c0e501d815107000320500c20110040d40051001c0c508904c0c0d6140c0c64024040c0e070200d00e844810080b68500c0c2a0f21243e0f40b03284401c485450001802c89114550034840109070401c52808003002c207201d0f400503070100340940e1071610810b4014607518201041c160a0320b500107800d0074084ea100301e80755050180005520403503040c02325422a208107418104861803d4000703401445401030511500b05030b80c0541080041d208a51100481291180c100030220f0041d00e41c0850b0150503041c00300c48448080501004048240d025500c11f60080c1d01c0b15802d503035000b0030455880800243d03907028503505004144c0c0256440584090541c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 480772895 1250 480771645 480771647
    0x2090f040f0605100503030f07030215070507031805190302030d03090f060b04022101060813120f111204050906040504080d0f0f050c030a060f0b0a0c020303040e0c041a0a 75
    0xd00144020041c0f0382e078501040141c0504804800104001070403255907134520580e40707071990482e4100710094825842d1320203288244071002c0744030f0b1102d0703902c007810003040351801c80c0c00140b424030140084018480201d8242c40d103c042e0070000340d5841c01079807403500e548113261801c0c07032140c0d140341014640364031000040c1200c8003a038411030b004400841d415014030005030007441000b18881812112010b014001c030345202025048400a44800c080c1d95582c00f200c88074802da050004046c42c4008642d521194001c8074074440c00350f541c0c40d100d064a10710b500b1203850301e48480d8070140f0f102008102001b075490144580350348090151010b00040c10241c0e2070301258003c00000c1d80d1b5154a079001200410f101da0f210070b588503440f10040c416030402c2c68120322aa80103076203544503282002404100c1a854406200807030b2811350003135103401c42c0f02e03400711624a401c03c0c0499040c08108400260f280014400e00e01508008001d25901e516041414600c500e1140f03584141030400e00119000f6 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 480774145 1250 480772895 480772913
    0x20c010207050a1806050d0c030c05030c090a0504030e030f1047060703120b010201090c052403010f0f09050408041205010e060114040e0c0a0501140c0f030702090f04 73
    0x84a1005201074081d9a0104c6040500f04580050b90820304119aa0301400405164a02100d003c3d5048a498503150001c0c50703280c504a0400a804c041040d012442d40c0d803841c0d01c142e6000d070083c500840a140c4081c0001c1c1000c250340503106585d8000c064424017001c03544180006000782c2c004c117902c0f12000306602528aa07140f61007840080c100594a42c00d100684000007407218000c1055039101a03614001c3c0140c1220714541603c589041ea500000d135005104646070580c005100713581c403034a81420425002c1c50480e122214100921180c0d03005092400a0342c040d0820705952102c80b810700c100c0e40f841c401d1a5001c03200c2c07182030506001c045500e500460b0199462040800b42e43c05141c18142d0251440c0421004944105000002d4071460701058003088001102c0501090410782c440703e079242c8001801d82e50150b101300e0204560b44c01440c042135041d0911114034140301c008840141880c00b0b090350702c2160741000880404524148843e00e912960355012010941040c1d10f600b804 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 480775395 1250 480774145 480774149
    0xc0905030d08091f0f050f060d08160501090b0f1e0112020402090306070315050604050f0d21050304020301150e160504080106180b01080f0a1814010c020c010207050a 73
    0x2c0c440400d002c01d2180b54103225041001290001142d05141a0440b00c40200119003001c1c2d061860030022030055886c0d0041503009450082c010119440c890301c405080b90b00804091a19030041040d040015800380500f500f03480c010358800b50103241801e070701142f02c0002404808405210a44100020b00440c541c5040d500502d058004003145071000c940240f08403003885034503206100c108074500764180c20000c5201a824412507009170f0316014002903001d07a010f05917004107a0745040070b075410b0031620070074030a000c3c07030190042ca900b04a070701e0390044e91500a100003500c000100015800d09010320060b1200070028a00c609282028100840201420190390b44013501c48507c2e40b903124006030303406809e440303008001c8280c2d1180b803082c0300850b46030030883c0c5ca4242421100f0f03543c0150b410912030b03441e0320600c000e15a941f0707820748000c00d806403180c14050214058400442c80c0854002641e0391404000145968581c41c0a441c00d4420031002e0b04642c80102c040c445a00c4039103e0b036007 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 480776645 1250 480775395 480775397
    0x31305060a02060a09050307060501140307050f0117040611040602060708130b040320070b04170f151b0f0c010e010c210212070c0201110613020d020301021209100c0905030d 76
    0xd0605c0c0514280381140b140c10409008103080c83c0c00460607040d154041d038070b10700003101200e5075503035a80300f031148000d540c11101e030100300683d0380b4080d1064a1078019034843c0c400e000c0080c03004015102c140941e0000c0c0c2080006901c581c0402c091180c002e142c1d00c0e003000c00d111a00700100040c0d030340c6191100004100400b0020003801041d01000704000598013080c01a00799410079442d0810400f20760014481c040103144640b11064030750b2804540e0421511408010f04030603100b0441080d18540c1c0604030010303001350b0000c030010700084200500245008540d002e41d54204509510703086d40d0402840d880d10b83d2503d958020550f40040d1198a44c104221202c1c40c4518441a91002070040c59415095550b04e1030401c00e020b80e006540e007800505c02d888400c0b60035107190a490b901c01c0d040365000394002401e519003000d0300d810761240e42c406100800152070401009003803a410001928209260b0344103407121008d000046c000d850000001d441c000200d61315010019035140d0362800058 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 480777895 1250 480776645 480776651
    0x60f06050a18230607080d0905071205010c120515011b141606050a020a0f0c0b070b0108010e010903170612070e250e1003020912031305060a02060a 65
    0x1014941c0034448440324018150100ba10b4250f4440344050071280001e08402c0070105000003841616014042d00c1030713a60409019403c024107841d0101c001c01d1240c4082e11203105000000130540c030300602d000f414a210303d00101e9100191040900151330007030050b4943c40c2010f0400c4001c140740140a160140b09190400c010500f046078102041c00b540382c05031106103025122030b02d842001800141010525080c3c1803c0c5a54400880751401046911070040c2c00c4110000003181a80d11402d4060f03008440f04840e00d9520358550700e081c0e1022200f21080d40041004001e9840c00303120341031820504500078003155803144d4005003070300a9030a40c4c000b090303055008a80c5d41e895511500854075452412500182e031610f490b00d01e2032b4022910725480010200c5041c1c0c0c5044038045c0500a4031403500c1d000b180c0080032041011001501c20000708240d0709000c41005540d031410b65401e500091000b8541c4c40f024801c000500502c1900814010b5408011103541940e00007441c0f90b015008034400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 480779145 1250 480777895 480777907
    0xd060902060405030321060a0e04030e1f03050a0e030405280e041506050411070b040318060e0a0902070b061023180a05010f0e041113050a09060f0605 66
    0x7240d500403504000d4241c03002042840c41011088054040b8040042e0b0384400355841d00b0400114801a0084004030360060000c100002e005048a5004030001401000a10801600c00c1500500d80c400400081e03216001d11002d2012445007200750140c640c051031402d42010045200c00311020744480550201f00311091048292184c5940a003507080c03000311490615080c100d009110b041c3d02e616440740f40540014281c507162056070060b0165580e0300b803c0100f5030b250049400002403054060002222031800b800d071903616000080c09081c0c88140e0300c0417500c010b0101034a21900845249441081030402203800c0400b0a5403000040310724132100c040b10201296090740c180ca840312039a000c100c41d6034100160700080d00844c001c0c2c50225482000031020030210140701e102d03007400300f498400900300952182440f5240c07190068030105e01c1039040f0311114496070040b001c2203901e21031620f040c421850440070210060440c42d2042c001c5034204454070300103001a100d01d9050280000b08 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 480780395 1250 480779145 480779149
    0x9060118150302130303030204031718040c0c120f090f0506030115052104140604170c0a0c0f030506060a0b0412060b0423060103020c0a0215070506070f08070309020d060902 76
    0x1221480c07046030411000f085d982c1e203030180180d007084c0070441d2054180300d04014103020210958900411080003040d20a407400c0500c0002c0c036100c0e40f03410410900750900400300e031074a401c81c05140c00d180d603454107144040d540180025420f0b000301c40c4c1c00240c20b00c100000d550320b400b074905540e1419000d04514040c081c060700c16228141081e0804108408011101c410651142c0e1181e4010100e00109403030f0701940940312201141d0080c4611b2092400c10038141c0c044000c1c0510f400144103d6103203101c240c50300c2d02da01405601400502d0741c00e9805004001d402c3c0903c580140043d15100842c605124100400d030066000742d0740c080d016525a5801e0046e0390700400b00301e101c081c1c410041f61410300085a01e041d215507a485002c0c200c0404164154070074400c50702c03020409005054a115540c1c200882071f09004503140c000c0c0d5080c003c0d040460000c2c481e20303000720442d840d100302e04d8085007406481200c00130003031010302d481c00c03c215015848a210514000c0d0b840300c000a075502c85440 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 480781645 1250 480780395 480780397
    0x1020105150906151c0504201c080c150907080a020a060c0321020901020d0e1c050705030d1d010807050301030b090a1e1112070e040f05030d0b09060118150302 70
    0xa4590172007203400e405400381c200035440b86001d240214401c4082c40d44044403801710300800000307075421580300140d01c043e0080003c44115218440c0b10214030704001c4c01806407400c0d440c0c03241c540034000c2c030005100d00800e0811005008207404d070042c0002c0b1803143c0025040e0409441001c040c4901c0706904410140300300540c24469804038064202082200004802034001c50b0b4494017600c03480301c00c00e04040c0202d0840011724002402400303082c001c002091000800c03c1c1e0100c456108505001c034140c2d406200145000a0640d40c4403c40400740e2020040c220b85120854103100c4410b047c40503040cbd120044070b06503038103c0361001705500e40804640c94400c0440c07028002c0c004001a40c52a2403004064031400380c020f9600c0240d20006204010801440383c07030401055010b20800c01c0b91103081c54040303522030b015400c0d40321081c0103a1220760942c0c1c80003010114869840002c0c2c01e0a240408800341c000c1d10a1800084103042c0c18184034418519001c0c0f2009114860307041c4c0d440d184650 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 480782895 1250 480781645 480781657
    0x30e19020913120c020102160b0d0e0f0d030902030d030216060b180c04061205010b07141219090b07051b0d023a05120a09091a0102010515090615 64
    0x40c1e04103584001c3e0380000c04215081c00124018040c01c2c6144a007101b0001182c001d85103001c1c1340d81d2414140e040210020000c0d010b00c41d009020765100480940c4041c4211140700d400342d1404120040144101401c1034040703030030781b0300340351060041a001018807010100d44a900c0301c40080d003030461100150095808004c03c0040287c2e078410894400c5810000d80200c446d60384400041902c0d24200b00191482401070003000358003484000085450124040303e41c41c00d03042542d804d00c813540c404660640c0501d4030903009041c07a0303c4034014268040c010070010082040c0b0309040290710b0b901c21351601902c40100085210003a00c0400c0d0f55540d669202515600030517100714a0f800911080c65810f15280c0040400700c4d440701041c0102403514100c03a200c0e800805001b08d06225860356a00307400c0245040e0400c41d8540740403601888500c104003950300c0e425039842602c8000b00c00207081d184003d0183c1800381c0c032548044c3e01d607203801c4182c60700050300b1150355140000304107913141680250 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 480784145 1250 480782895 480782903
    0xe060a08120307030515030a110301060906050d06020d0b03060c04140108011202041109100903020f0a030b0103080d1b050d05010605040b091e041d160303050d18060f0c030e19020913 80
    0x40d2580003040b88585040304002000d07030007800388642d160013720031110107110b070b640c000c0720503442040000d230117074000d048110f8aaa00010311340e004402007403500008840000100b940040d003400803245584400ea403854007443c09034002d40c14480405035000d031200c0000e008030f86400c01c03a8221164030b001d03503042c203402804079851808001c80c0242021014130050740505160b281a00d41410090845800c0c0c94102c154800f81da442c50340c0d2840664089010840b015507958081e914030700000300500c4c6010300b142e80b07180e102c81c4143c216108958060340701809000c02044100301180c1140152400c81108132160944084142030826501252504031540070740740003160840380c0480d245261200c07101c0005c51704080e07001212194171801c0740c000030380420350a002248107000d2075040002c2c1240880c489003c0c120302c1d0754961050740c1c5103416040c0501d4a0700000d40d034030350b030510440b607000c1d00e0a8024200c0707075440c0c1010036442c44030540c040c0c050200640050104a00c0e410020744060380 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 480785395 1250 480784145 480784153
    0x50d06090203270304150f17010e0f0a090c1401050904110307020d050304151e0e1e070e060906151305040506042904090c0e060a0812030703051503 65
    0xc030070040351451020044008140704141100026a10f000094409580754100240c5034524145025144806d080324900100200c800c9044890500000818020401080c40384601c0c246000903101d864402440300001342c0c6000c1300c201c0412040081c1404680c0b0f4014101d5201a002004035a580316844075681c015081c42c40b1100051509130040d44030720400d034280c50b15101c0d0084219100c0c40259005000e280707801441400286079a4441e25464210302160b00324241d0004158041d202c64032243c10594101140408802480d0a034001c0e840b020034010b40051410300072100c8040310041c3c0345c00e00aa03140303000200750f03484407180907141c1040c81203c41d40b1350750048130741011242ca0b806054001e030305005c00300301c0c1410540500888030520b00b254038140c0c10700810348204448031001080d4821b4036100c0c040003081d00c1c00b050780d01420140084103a1031500d88180146031007242c0c0400050b910605c60321400f0900e9006482d0000701a150208240d150340d1080340e15441c04070402541809 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 480786645 1250 480785395 480785401
    0x20a0b0901110c0c03070510090504020a110105040b01080c1207150c17030114010c11040e03221e0602070b090f0418030801090b0a050607061401270b060a050d06090203 74
    0xf40c0000d2903003180c64210201c1d012251110b060008140701c20031aa80401c8042805000358907060f0041c0c4444c00a51520341c59010301c000303c1c28251441030301c00b0343e51002c02500605c0f101a0038807450400d14425905216108600081c5a96407000341c800c40b100c120002504005141c413030091900c24581250500c480060082d40c200002c0c1c1c42880390300c4405c08180c80740c0382c2d254098140c1500360394004003541d91b0381c8400c10510015026202d94901c403800100040f451000c41003060032603000750843c0f00d00c1801d0034421000904e141500804008082c111001c124a513030004098055450080c0c016482c4c0001e500801e03040141c0042641d401802e003604522540c040a40828a103400381e03844861030f99841a9840c220b440a40303c0581040044400b80001e0901c00000c100d6680309032400600c10412084100800780281c100da088a49240c1400c003044000e1a036080e402102c003281049080c1d41013000070001d02c1190103100500001042042e0407884690080006240904042d580c80c5 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 480787895 1250 480786645 480786667
    0x1103070207140103050705070f052803030b09090d20070b030a0c0c11061803031617090d0308040221010c030e19061d0d2d020a0b090111 60
    0x20641d800340000b00280700d0742e0b0280703661080c017965020b0b8040d520380c01d02d0300c8030a45400000d004440700581c5c2034401ca117060f9000410f588010b61131955515400404e94040b464020140d640401205205001c1c6605001e45918003003000c1036201101c0c1060021408a01081400d4548100304c070052402044e00004100e15050019403080280d03036030070000407500c0981560300d0f08a504001e0318101c4448804e40c070a041c860000c0200300c3c0d1515210400318112030000e4655030015200c002100c0c002d45a540c1009508050341c100400040051800d00d0f40c0c107004584031800e20040030317003003040c040081425519222550010701c080788400f0031100c4416010607000c3d04210340501300182c9410144408154080798a034410705079203542011002c1c0c1c903100e0720003801d4000e0702580382d400b10b49040070000c041003040c292075400303c2c1c440065050040c80b05518080d01204120700843c0b4001507801c000d5800300e080480164024441d40175034030b40010140c014404c15010070a10680000e40080c2c80c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 480789145 1250 480787895 480787903
    0x50919020c0109060e030a02101e090f03031107080d091a04060603140a1707080c0f0a0c17060a05181b0411160609110607200a12080d11030702 63
    0x159000b95000d000001d1702c102c0a96036803140c41e0368440160000c401030002d207001900500c500101545585140540e140d03000c408031144039500b220a00a603504040c10140c150060b00a403120511000c1c1c140304250f11780240a2044d0740395121a142d8450340501044612a1748107075a8203c0010000103142c1403409070002e0859000680d90061901000e400c0031000142c3c20818641c05071081c0c080e03480303c0905106940103c40e00f11a1300b1018041007210f40300c02c102c0c10091300c010100a05902005d41002000308400f60030942c1c54030001303082000d0300100040c2094000d03140c0c43c2c00181c140e40381039084032003103560706542e001401900ca48400f0b0a02e424540780082e20304442c00c000014510100b180ca92043e6640c200c00565422002008183d030f5910007070b01e10b0b00803030340c41843c038080c000017030456402460200e40c0034000d0451040f000c05035109001203250140c852400701401c2060041c002c00c1d6441004101100001c0c00e414180b100c0e4020301390003402003039881c4e03c0b4201004040d4a03 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 480790395 1250 480789145 480789161
    0x9080403111815010206150a0e04020a0b121914070806180a06080c1008040f030c050d03020c16050102030d09060b03010501080c09091b010c03030e0706030e0f16050919020c01 77
    0x140309410108001e05081c041e0b80b00c0d20800100023100c1c1070318109041070203000003041680e000c030b4074200000e9000d401100500211a0040b001d111919010900c00741003100c000900c3c034201d150840101c650000f9183e900d03040349032130801ca00d29079105c3c030000d09445480240324441340040c03005d21103201e480d904000160350141d4203a4041109a13020b00c05082403d03c0c0420024800f84081030120f44100400100940030340340004140c4540e0703d41c00d282029002d000e41c0002d500003941d0700b40a100317010610300701c4800e5000d215a5858000000d569005141080040039039800007142000140c0c2d00c03c00c0542030250090250350707542c010b095150290b050856010307108600000f4000c00f40410114821445424160f00103c003007001112144a031560440a255036071114419010341001020010300d002e0340c011400c050390202807801d10301c1a44000034240d00007000320201700c40d20000300d42628400e0303031100c0081d81d4040f03080c40250b03e0100300300d00040c80029154403070823040d080001c0f = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 480791645 1250 480790395 480790397
    0x1030021509010e01141b150106020703020f0603071202090102010e070e06191505070201091205070f0f06140d0207080406180f060507060e0c03030c03030a050a0908040311181501 78
    0x4190f007820740040d104002e0400030f50180d10002c008803424160750081140c804154002219001c0c5140e207170b890006d034030a800440250340302c10410001c41c0b4114074004130034a010b4070081c1c110b040c42e0402612100391070703215901c0f564000c91540300c035900c01d5015505541c1441b086030710042d80c890504a004605580017401a039058105081408581d40340c081107819030515501d844000140c1220180c0081c0c1c0200c0c1040f0385090001800c441034941c050000e030051001e8030703e076444d103107100d8404100c90340012070b890f075a4002044140e070819a04119001d5804016039101d109200050003031060081c0100826000318020034420b51000400d005814444400225152600480d0011300340c0c0b4802c07400000c00410555001803450b410515000e400e4104941200314000002411600419505082a0b0021081080300100350103550303008001c8102c100720311003091304d4009640c41030780000f03446583ca044e040d1805407901c000312028510000714900e26401d200407919604801080118 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 480792895 1250 480791645 480791657
    0x1219060e0706172a18101818200406020f03040506070f05120f120f040201050415090b1603030f06050618040e010c0207050306103002150901 62
    0x301d002030003000468041c0c51900b1007002a513031402c801d03800d0100d80c3c0140b4918198450444407169564101030200c1045240d20b01e2049081c4405000040c0130302c0c20000e04000c03114120000006190b030203101902c05e44002c925000401d0003d1401400c0d04c01d0b00070000300c0340c02000100217070408001c0c000740c13032069082d600000c41039841e090750703805280544ca5001d88104007030700008241c40308501d03c0034864001d0b00c078a105141181e4209410846140d211000001480380b6002030542e05140d011113103944010050030250002840c9008602801415a0006042e0201d25004429060003826140055660b40544101200c038a00c24000308902007410024160b28202c03150248000707946010b40f9640c14a000584025948038800c02440c0c0c1042c0e40e8903c500480a0a0144809003070568009002c1549004241490080000d080342d40c2c0d40099581031144400c2d40c0c2610b400001e10380030390101e003a0b07181c0100042400d82d05000307600003220100c0e00220000d81c4060312900303100f42c0b541e03 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 480794145 1250 480792895 480792899
    0xf030a02010e0f01060807090c020a05061614040305070b0c0703061109090a0212070f0314010b280806010c0303110304060e01060605210702120408061603020c0c1219060e07 76
    0x140e07082e17840600840031aa080a402480b01c140254001c94826000348100c54480c501038030f0701410602c0c143c43c2d04481d10b503192000c19600c2d401c00c07001c00350400700303224192a20340356458040c0c4502da28082d01d5140640042d040700c000c2c4081108101540c3c004070200108450000c02e01d02c40c0e0b0100d10483e025a07c4107000903403186062096071800c0ca4904441c980560300c0714001c40b66800306040c0e42052540e200e038110096010b0000c0c50f0301800c181180b071540c5100d40b00303110580703080e081444030b220101c02540241042d030008613190455401c0c240071000c8045481c044c2c02420880d4003e060181001c41000b080c4000c40d000500041c1c60b03400204091510f03a02c0880703061243c6605200103540c00c0e81c40214683e441d02006610000510544072009949a440c0c045688a544060800d83c00001800b8032190034000401035528036040845c5001011081d50382c44481c08885c4a200e0458108101c004540901520351070140780c100081d4403656618001d80140388005041c14588140580 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 480795395 1250 480794145 480794173
    0x30606010306080c0f01030626010e06090312040203030f0d0c0806091b0c03280207061d060304020a090f0204031e05071809082709010302090a0c020f030a02010e 71
    0x201c42c1519580000707440c884402d5801c0c440d591480100c40750416a0b94903001032003502250703200c1c9900c950307011280401840c40320302c1c40c290703804000325800c0c1d50400f00030b100d00b0000000444100b41c403e000040302c9990b85000081c2503001c1c0704220351070448005402e0540f8260f9600070100d4031400e45401c00251a103000740042c0c050101c41004a5030400302c0140320b08201c11002e003403d10042d1007220b2801c0100d01d074200395441480b1a400b540e41c050446a05050340611110010f030030035240803a16418202c2544119050f0b445e01d25014040020202e02951541034825014000051080c090b00200c800386200a601a110580700281403038144c0c1031000e03401742e80e104600d400c84004d103845414039000242c5500f030b100862002a40c0c03445080000307080d181c050329440800300303206c2c041007240c541c8100c00612400c01181c85007440c68014070042c0d4600340c1060b00b02c50450720000c3e0403205e121050b07103401803440c0020451304c4081041c910150781508100d0b0046995425100881c00d19a0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 480796645 1250 480795395 480795401
    0x703060f03290708180712030215071803170c070311120a0809040e0f06010f030b07050304170904020906040b091008130f0c0b030a0f05010b0f04050f040207020319020306060103 78
    0x280f103000003814240800c500030207089aa4548445900c151261103544800038107141d903190380224056040300d0f0048815200751007400350300103ca414007070b00060315250f0361a152038150100a050148115a0401c008031080c182c8950304c03080c1007254801c0d0b8482c1041c0020241c03c5909900c00c10790541840b0000602154000690343e0081107142001c5408003000058808021401c03640c1c881c111000302980720070880b0034024107003100156005801c60422401300350008201c0310501408200b40f04c000b4038142c480e41c0d1004152a282521550b5140004000e40706292910740d1043c00030070003185018a907801000403071800c554460300d0600400b410340b80402e04075009028503407040441c0d00030800e00968181d1a5114001c051740140c0c6905543d1060380054510125041d13070380c0760f5107400c800184207a501411103075280c14200807001d00903006910490007401d00503243e007604005a9100c40d01500c0300700d68014140c1d0355031040c640100041c9552168243d11a110b501e002c6001540a0f02c = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 480797895 1250 480796645 480796651
    0x80109110f030a0b0d0210030207030e090f06010c140706210b0112020d0b09090303060102060c1303030e0a121a1b0406030b130f09021f050307080703060f0329 70
    0x701542d04590700c60b160b10b40100b020440107900410719011800c0103981350013541d07002003031948006840c0c1c031031820021711031410a0030441c0641005000d2001c4c91440c00c1e00d4031750100c800d2030400ca011042d40b5081d038010b076540e40203503628841c2170b2000c102c1d25000002c0c800459416001942c480320f0324013440301a2155450540c3c08144200110040b1203e00d07001440c40040385040401c2e450007020100d14281812210f40c4407541012080c096a913905101c1c13540c01103030fa2540d180c1072014540d031201300005540300040601004000d0300204e40c0b100641c080040c6040c000b801840341c56401c10902000c07000d091f40415100d80c1c2c00284043c1e0007000400c4510b100041050305060038039800342d0003031140c801000d901a0810043c01c11012050040c5070006104800c0803900304101d1041c0406080c001c2100071801032200510300c003041e8000c0942c0d502a00d00e20748561070b500d41d564281e0040440e60070800150541c403101009100000c40030580101c0702c40c0404034104404007501d03c0300e460035 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 480799145 1250 480797895 480797917
    0x16021e0a121416050d0f0b071101050f010e0c07030903050d0f1106090706030506040b120f10110a0c02010c0f030f0f020a03090308030c0c0f010b040c08071b081908010911 75
    0x1001050013603007810451a600284605080c1c0340c2d00117181c982d038070721590444066001030584103180c00405001c0c001c4d00d401001122100b402541000000c0400d250001c041817410800440c0080c1494400d810703002c0115000b800f941c15080c12030070001e210307904000c640404916800c407104107581307001078100d1189100101900181381000310480c0a86806000715521640b41d98016615680c0c154080a842010f500100030780894a4111030820b0a40480d4051651420b20000d441079228022500c0e14411442c1588a004c1644010388291507010005000c42188005003c10540c00000082601c180c036150b118031141c0ea4071040740d0390341d00d201c401400070ba01400d00b0800111070394041e54101c0c1c42c1d400c41030b0820b54440000d80c50100b00761011038841e034489482c0741c502d0400d841154841400b5251241d5181381c020400343c1082501104100100e003503020220600110b41e0640b0301d4010703048001d241e000500000101010001c0c090010224544070740b455104000c07c0c00c0355001050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 480800395 1250 480799145 480799183
    0x100801080d08180f070512030a0e060a091814010b034f020a06031b050304050c040204060c150203090d0507060e0a05030310090216021e0a1214 63
    0x410340454140c42c01910740da4a103020b010840c1c0d004102030200700150000c440041c043c1601d45410040c03403980e5882083c00c141c20410540d40050303070140982c010b0301c2c2c041e00c0241d07403865035120840700303150300b80c1c41603004401f81c50602811031440e400003003071845444910245a41c0f568400a1a440241c9003d500500080002c581e2400240c02c1050300b4034070040020301c020210300340ca40e036590152909180c1410120311100c00c61828041c0c0c1005003850780340802c1034607881082c641500c2c58500c41d140c2807000c080002800c100b420000c81d20541d0b4041c1c001c0d0740b2541d4640b4040c091560038581250a107003410031181e000400c51003620f20074214040108030f54000c4040030f640550100303501392121364940069004c00c407400c103c8c0d40c000700c0c400d00045a0302d03e4000341d00c8170243c80981200c5092401000b05484024480c02520007894040710100704120840108110505030080004c4c2c0041105c14001010b40c00b100c006902079000366946c00e05840c01c0c008550319100050360076041082 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 480801645 1250 480800395 480800413
    0x70f060f0c050f031b0118032106090615030e0607021c0e09040c0e07020304050a0b210106032012040809060f120402011101050601092904080c10080108 67
    0x4800d50705501c0080c02035081e281c44900740607002e0b055902a82c110a2156402c00320752640d10300074404e030310050305031b1003000e00190440c0e40e0007405200c00510044103810951a110004951a4014401041204410841c46035030b07074103208000c5140740d588004039103040c407030104104020602d94882d443e241c1c09400e41c902040c60040b25440e024407420f04000d403002d148152900d0700070150f40900d02604078103503254130341480352941d100700402004c21500248403c00480c0c40340d00e0341405981682e44c20b41e4881d480080f07440c03181220014030307500c5001c65000020b051034041e44400640c06031583d0017100c0d0b22441d4041c91072885404241c2e548218000b0000e40030070040c1020300000c1c0c3c4024011494401108404150307500b017280751440460000050004540e08060790358145031440f0000d2043c0d180020000c0c0c040015841500754110041d00e000074170025290210302000c08603140162201c0c0c80320b2459948000e0f14040f94040ca141c010001d40d82c0d030040b10b07090f0482e0703094001000820 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 480802895 1250 480801645 480801647
    0x21110d02010c12020f0312090c010906050403110d0503130303080a02070c030f080c030414030601090e061602030c0a06050f010e04020307060f0302091027051e03070e07050309070f060f 81
    0x903d0742c101070f0702107018081800140c403000780014003000710105180d080e40e0078000707151402c1c000440e23030361410320141400800100d5002003c5e02d0440350002c01c212149404003020440c000c001a000400c90302002402045c06400940d068094078040d03514544103507180c000e00d404074841d2030400b4141c180c0d000e10030000181c220281d854968404e010703190131b100303035008214590b40003034000801d280940310304403040d410204195401800c900005000b80086020060703210314001d0000100981150a102da56a0082085a60b40e106100841d10240e07a10b00708000100001c3e03d11081c0c0d55880c0300005003070500b05060901642d0020b02515005280c06410b80c0c440000e2110718052580138848000c4994400e2940111443d143e11903603042d00c00c81401c40c4e03200048844801060804a00c1401580c590060a522003440500644035044145001074544a05075001c5590464070b0380400c42c1a640c0000a1350185194104460106442e038030b940c4c00d404074601625000901d5038000031b14107 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 480804145 1250 480802895 480802913
    0x602071b120204230c0c1b0f040c02070e0109022d0f1e030103030f031503050705060a0302070b090a0c0b03070f03051f080615031507031521110d02010c 67
    0x80e0108880d1104814088407400d804ca800440740441490310100311408200c205001c0b5201e10900e40d065890380e0702903040040d0486c5200c0f001640165681c0366103281241c02000008050b00d08008408000c1d0703903602112000c0c0d801102d4803101c50845105960221688400c0e1030320b0100d01405c00c505104240c07420402d030f508540903c01e520b454104542154441160046000c1c5000e40e0b1110002c1c24020405800d035500511100d203004015582000030034000b14580c4107852007190031a5072140401c40c100d0107401281d42c09072040c0d140c0c0e810303c43d01140014003804854031480540d203003a40d543c8485112400211507000c0400c04600070b480c01c0d40e12a40c030441d88a412240d14802a0701004131103820701116030401e5140d54003601c01d22403403100303018040740d00c108218001d10011018540171991114061304240c00e0549a811250034409201c20300806084102229824500307264401a008c1c04000003d0720803a58500115005042900b44c0055068061311015140c5019555050704 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 480805395 1250 480804145 480804161
    0xd110d0c0e100e061e03100e130b060102100513030801050303040303090b1c0f090209100f030206030403020304050d08070b0f090a2402040b04150e0904140a0f0602071b120204 77
    0x7205030204000e481e45c10718510400200c1481084045d00c91400107150140032180b030304104603d2a540040044480c1c076400c84000241d44450100895240c4800507031401c04810300049220b801c040130001c40d10f200e4070785502400c1c000d0703450590700d9a8800900d91139101d50300000d00014038410007808001012802040002002e82d00d070300c00070224030b80d00340c120703042c14884514251701c0d003500344203616100600d5a000840d9803031000e0803030724007520000c4c0d41c080d908c030003030180740301100003403d0500910a9400424025109500008151510101960284c001150048140701c00714001d502040c83d01c07845501590020008880b190f15515146a80c80143d15a9003030344200408081c40c0c1c0307001620041c00070481e4107881f40d080c4500c82900d085480f00c454204504295040303040ea41c1c031401c2d40d4201d50410480d0070750141d850b10aa0500c01c040001400c03c2000010032410800303076a0087c0761042c0105124020031003504550840f410b010321038400141b240143c0c02e809454181c0c01000 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 480806645 1250 480805395 480805399
    0x50f07030b032103071806020a110604150c0314180d2f01030b0301090b01050d080d02070311011a280f0f030b010b07020d060c050d110d0c0e100e 64
    0x1640fa00620303015242c40d03144035018240c0c42003c000d1210300c82d045100244444e200c080078150460030260300070b66450b16100050141b030040101e20102d915480102d034003030408500318a080105004001d030900030451801c4002030b441c0482d82d101c00000f00705841180101c01903c18540304488100600401c01c02c1058030100d2103a44482c118181000c036003102c00340803402c5402110320b1f150001d8115008100024042d0741000c40c010001003005c545141914400c076005100150181071100e1180141c5600c0c5280c1c0b03200084c00014550021580c0081c0100c41c0001d005003a05140380e0340c0556500b40c001c83d04210404007100c21084440c00d0a21540801e01c0d01c2c0000d1561401e0f02c03500d0082e00c0d413002040d21b5600780103005001980051340d0250440103442490b142d550707404140811500000a800d0580c3d8071080c1c085140300d04110740c40903848200c1840920564050f9143e543d12050301a100d040c6020b2820b030070b280c0642d901010260004024a4441c003400301d00341d41d14800700c80815 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 480807895 1250 480806645 480806653
    0x4081618020903010e07090615081915030c060e090606120f060102010b1e10051303110d020d060b040b04090b0f040318030503130b04050f10091224050f07030b03 71
    0x80c0c5c0b0120101b103c0d40c02024036410224445103892841082e140341c1c040801c00b00140c2c1c00c00c010000300c2e207031085064408551170004060104e002005003c907029040248070f44200a00091b085d6031040c0d15004099044a4001040c0c9501040101a1062150100301500d00000107521a9440c08820340d1100e4180008031b040490303440015440180c2d041d10008585d90850007219a013410301d05443d0720b0340c00e42000b514203004104a00340c03403a49407200408000c02840000c1d1540c880010401036a079014204800342d1203140b074401d0140441c502040e0269240c01301049007482c0a005480c03070607070031404030040c1d529104000103070032100500c10780c140044c1000b0740b441000b41c907986200560090000d152078242028980c10315040c582c0c0801c00158080c007060005698030b58a50100c50320441d20340490308072640d426500c034503550340300c08402280c41085405001d81c445042c803a141545405c450001ca51807500c0003224002c1e1040703c45013005000040c6d40078000da02c07110450400904035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 480809145 1250 480807895 480807911
    0xa030e0604091d0f010b0102120309210309010b011d13140c18040b01090603050a06260f0304030305070f0312050705070b070801470408161802090301 66
    0x81802c0d50506031420900d008003e0350031091190510241441051002c000e010740f6554000003565a0290754500364403000010100d00c851104206d10f059008000c0c4104416003134540109026400c125440000f950901e501d582c1e81d9031161000100c8030051484640c031009481e81444012101d02c40f982144c2617664030380810700807500301901e21800d081002d0039612164a48040c001c282c110f6200c5000758101030004429a07004880201914080d04d4005580c1d5111401c0b02d0140005900200c0c00050450000900301c0c2040101c0c0028421801110000c01020725142d0b5688103900c8050001078040c07143c000042c0c8008e240a03c100e0085c41d0200c8140441c100f20400ca44007910b100001c1040003803181d081291444001e030303005036a070902a58175032401910340344820120072600b812b661803407074004034920a044101007000110070352646241c2c03504940501644076014031011845101456101c090304041c0c840141c840429000850b400e03c0305a138400780d0800601c8a6141d5258110 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 480810395 1250 480809145 480809159
    0xa1b08011809170a020102160c0618140402070f0f0b01061106010807050f0102030409020f071707050a030f02250303030608030c0d0e1503041209060311070b070c0b04050607030507030e0a030e0604 86
    0x43d0b160307000d00030000080c4036462b001018040034604440002c10186a01f000c101080d5201c40e4030003507220a6034050f13035070802882d000d0340c00002c255000b01001c454000e41c01c1803118005210703040e04c50350b445800a03503101c000e2040ea124024401c40c50303036900c11034041c0218104807030100c4a01c9018011242007a807600c500704c0c10b903040f51201104107000400d80505001c003c00485142c0014102001c5c81c1440540f40d1035140d5003420400303801c2c481c61440030003945101b00100c0402c0c505464560740329424030081c08803102400c0c8403e03000242010004900c110002c4225614003541c170006260144074100166244520162155480150310f00342d4003068828078011441188142000c2d500c11029041c0039005900b141c0081007098907040a01071b140d8100001c507005150000b26403090340e510141704031005040804020422400c0308240403c0000015159000710083c0c1c409201c981e80ea0703002202154880c01c0550f80c3d5620181608010900612048a04c10409444186070940b607001c = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 480811645 1250 480810395 480810427
    0xa02090402280b03070905060c06070e030f070902070b150a06083105060a0b0a030f140d050301080708031905030702010902060a05210603150a1b08011809170a020102 73
    0x44108003c400c00010001e5041c1e01c01003040240200700c07890f44c1003007a43d0326066600c040c02007900003840f80c0010840d40d19501000844402c1140c4030440c0c038140d84440170b41019401c0040101c0783d910341e01021a10071802149100c130b44000c090b0502d403000d072a04000300d5a103d070207480c43d1404084109003482264090902c82d092000700b00c4503000c11002d40c504503107444002844000010315003d01d000741030791044200c0c0203ca801078501c0c1d80c2e1a03001e0034072480c08103025a20704494800d84002420451b0000099812598008203542ca01a6264103041e103e1152384010f543c0780b4101c0c2a08107003c2e0141000c0c0d50004001e02c000150400d00b6030204005a001c03c0204011600100304048911030070320072502c0007203401101c00c4140c100f01b4046551000c841c007503003620060349000104140d0ba554410425045568890742ca40c001080c0b004c3c105450030700a40818481d540019203280c6100e024a24940303070303c002040300d0065020645946500a80c0070036046540070440b002c0d080b04000 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 480812895 1250 480811645 480811649
    0x9020901060e122b030f05040605061806100804051c02010222120201030b06120109050a0e0604020a050111031b0318030a080a081015020d08090a0209040228 69
    0x1031540c03820500d040741000700f40b425071204100e4960248400102d02241c92000e48000481c41c0001c00600400080a50180c40c01d00d040c00340c40d502d05003c10040c0480d5400c014041d600640391060a03441c61104a011448203c0e15039800c40102461042014401e16503140c5c8580124151000d0707100ca45002c9040341c10948501005170340110f240d002040d0003020201642a007803a03003007139140c50003051007420004400d010381410343d01c48503a01940c4036403017210300d9142a04001c1810f507071510059401000c0c20351f551060b50707140c45d07030780c07440a80e0014105004640042c10191450b20b0b01c40115423400d80202c040b40103000c103201459800d0b001c188881c00303c020700c10245454400022080c2c0306100711001c501d20076806030000c8400700c1c08000845145426510700700c00995901603882c2c51103c0d080d8882c090f4034100070b4008100e80d6021518220150542c0c0c0d82d260142c0b181034001d5900c540e00305000c1d51061011010038010f240415000e20080f0081c0e482400700e2004440328128040c41d6 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 480814145 1250 480812895 480812897
    0xf04060302120d031805060a09031b030c2001081308090d050102040e130c09020903070f2306031e1806100806070c080315040e060c04030303060503070e190902090106 73
    0x40c00000310802c0e014010141c10200d0205e442014501c3c603194030f5525503000e07000b40100350382c400900e070915214010b500602d03402c80103403480344181403400528120b02e400c0d0a42e03219031004d42900d4980000a80c00104d020141c0d03a075240c60710303154038010a50343e5010080720821820401059551200c403d19080c0301c0c051000180c40c1c500d061901850340300020202c410f289042e01c800e5000401d001c0c404010307075600800058907826041c3c0424902001c2da0401210041e29800000e660782402140d80f0000d5040401e203000e002c1a0800e022080c0001d540e4038180f240c0d603854040e45030355000b0115a0241c4000b01d644d0702228080a0941000000c1c0c0304010000381440003801050001c00c09260800028541200c00010a464400c1e00d4017010707091485c3d1100700d040340c40303440c1d035185c20815074029900c090301c080f424010080c0703406038024030040700400e08001002480e490041804000c507041c91900f62120350b1660003400301c0f01c94036491455203075aa03e8480c2d0150300c3d40090076002e0003007 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 480815395 1250 480814145 480814153
    0x9060b0a0e01201906050a05070f260f04110f010e040c050708040b04030b1605070b060607020406060216090204050a0b0717030a051905040309050120010203090d090f030503090f0406030212 83
    0x1850500728140c0d4401031222001c181808c0500000590159100c10000300b2403600c03004c4030040055a003078030101e0318048000030703100c1c1d420f0107800320b40b4011071400356200391420352031036080c0e03401e016a4035201d1821601198903605041c4803402c041c1c00445103040b092501c1498000280d0b00e4400942207508a0741403210046801e104010303030081900c3c0c00c0031040c10140b03050f04600400401a115191004003041d030361a0124800e504c4280c00c0c0c0390510760040c41030003000d0701c0d101c00a540c1e00c03004116000d024000000010a9240c40c4212403e40b040940300e512814100515082c8a901c220b01c1100c0f01d20041002144c050801c101a5000d5284200082400e0510014061104c0c5c4e07400c2c1102c50b400e28000622000130b03005502c21007102c10038281000c02020701c4c03580c1041d220301d08000c0340e08c41d4000002c010020b0404204040340003441e4440c06500768440f0940358006940d800700074a83d43c0108031180507403400d004620a85000200041450f40c2c0380e07404a41f403e040c41d0121025030784 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 480816645 1250 480815395 480815443
    0x40602070201020606032a0f2d0609030618160e06310e030912070510050c07060e030c06040605070309150f2d020709060b0a0e0120 58
    0x30b0f0501519030003580c2100180004000d9500d0200940001120b51540c0304909076141c2c280d880c0ca80e040004c80d54010000d8950002240e80c16180e42c000750000c1c8940e84c0b4485010f001c03441c1420960303014400c054000c244559400e61352000792a52907011b5044c0c2e1041d4007421041f000070b201e00b20082d00018501ca0300c14149001031151850800400b00e20354008060000100041e414026001007544c0e07401103448426040c4042c114413035000b5182d0407a0007c12241c00c18a00015103900302c80c0b040d111004250b00e0031000f25010b005d003036a217040c03a40001e80100082e0b03100310343e543d2f00000300600380c8010f03a50f10f60010309581d119900002c0400c0e00400c0400900d6007212020b002015504030b04400c800c0ae00c50000d1415242102032000e1044102e25000c904401000c14802c1c011451110900a00100b2010f9596400f91140c41d44040c248075000c24503120302d0007910514080c540710070400f001030400555803501d90b4020600c2c00345c483c0c10101058101002a0315502c1207010122041e00 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 480817895 1250 480816645 480816647
    0xa0605061b06060402250c0302120313330215070809101a1e03030301030812090d090b070201170c0c01060504022d04031a160c0c090507031103040602070201 69
    0x340081002e031080d4070502100c1c82d681c81c035207100c260843d01443c101b05001d040d454403640300303030007908003a400c0b500305081c021902200000800d040c1c5c81220781c07603040594514030381703081c17000c0c0c013020704810340d0104211a840c900bc2e44140116403164015500c503000d4950311100200000c680e844000742804040c0700000d0014030202c8000303807030004103005081c11005002704984261034030500030001107406600d100e000031098003643c00008c0c04c7d43d650756075a0810004540200c14850034481d00301c8045091400300150010005140391690180b4610340060020b00360803400341a81481032240038194100400c01005205620800500b515144110038190842d569a00668005c520401110b00c403900300c00c210a40140e140f0a6801c08a07104580d8510785000e0ba030320041881c2c0ca8100950b006c0140a0b0700765100b84405461048a003018040071a1481051040a414484851011300c900c80301500302d0f075400080790801040d915910815111154000c031811340300668041282d138119 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 480819145 1250 480817895 480817903
    0x103050601020a0506010b0306010513080601060305130c0909020402070602120711030c030904051008060c0406120c0f08040305041d06041b1d0d02060409020919080a08030a0605061b 80
    0x102082c402440711212540d5080d0303454006010b00c0c3c6a0000100c0011030130381c482c5044800041401307219411090350b0342800360b507941007802100c0c04a070421780040d501c400e034010b41083d20340e0000000c017081c0786800c5e100402003602c0300c001c2e030b001a02002203201156031030008002044049040307200515146a004100302400100605907800070002c400c20580008103590800d84100ca000509480d407410301d580c0d0640e82c4c1e0001e4480d0151004100880c100000a0803c40c2d00a4590030309580ea403164130001c0f100107030003c1004c2402405039203581e41c828102030f90312030310a090281ca0191110300c035030010761304103902814040000003005803905282c043c0500c0d07001c1e03492054150700e85056002c1d10010090310036550215038120307a0a40e999440201540e06138010f008142d03600d0729500c000019500114101d40030302d07003000221158a034590900806c40d103c0101828400c15942c2d100030b450f0b4005050020b50b203840d0103001c01c203035440c10002d01c55840001c1c15001da14804c1401c036810 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 480820395 1250 480819145 480819151
    0x41107140d080c07030e030f0d051803120a0c170301090b04180c030b0c070c0902030108010b0109060f180b030901020903070f080619020c010f0f1107080d05070519030605010305 78
    0xb00a410302c18000d980d000902035406443d030505062542c841d542c0e010a2401c0c85c90358800c07009201d06152141c0c059044001050710400104080b01c2c0a1309071424036941d500f008811490500c4104014142c0c10300c2613550002c1c03a4420901060f2004102c4108545a0003c2c0c0103081803940d540401c5c001450315104800e220300d00c01101175a000d06a450351045006188805800c2034105e5001803100d000e010116140190706c100300c03080e02c0740c0b1901120300039003003409080102d41c071b00190500d02c6d40c0654808021a506956142045040407004813892644010344012070007280c0004540d4031039032030245109042c10303000107854403001c100b0541f07011025070003033400340c100340001c0c06140b00120b6001d03402400408000c101c25000e05e0100002c2c0329484640c00d00d946032041c80c004040032a08040c5281800c02070505c2685404440c41296100b00701c0010b1000400700f200c0c030031038000d9070007103903001949007810b41c00c10900c603514129a01030340c500c0000180d60342c01e00f03200c15070b094403d03590 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 480821645 1250 480820395 480820397
    0xc02030c0721081b07150807051c150509040602072102030a03050c070209090705010201050106030b2103042c0f04080913062c010b210402041107140d 66
    0x4640c080b82e1a071801c1c20540058040c048090016a034003074100040030212252508000300d4181c10385d600c1025000003484040000020300c92000300e41428031400a40b150600c00320f40100d4214144140030f80105004901c0200f001421440001e242d56080302030361145009800c056643c098510346082c0c1c0e9414505840e1094201d40c10500809a0000a403440d04a89082c000784030303160394081a94030f00a07828001d5118000c4800c00201010101d2210200d4100380c00900250740c0b548026070684903140000c94104008030584c03400c1c400c0380b00d004400040c0351000e892030284c0720f42241c0660702900905203101585881165900c5643e0014994000c1000e00d1401d01030905980c1e41c0b4861046030052841041c00c1a40f83d140360056034801e00003449010969000041025a80170000724131947d201d1714103146400010f10310f0182d608a03840d403256034403014041241c9000103c84224090f00c103030380150b035400313890210803004001050407a005004207034034005e0b00307080e80e4034080301003103200c4c = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 480822895 1250 480821645 480821669
    0x50303010e1b0a080406180503370c0c240f0c0201090506090a09020a020a02130e060105100908010c030b1c020901150309020d0c050a06080105030a030806030a060c02030c07 76
    0x10340084402c6050781c0d1002d4461a020025444a041100c0500302d1710a40044580c0380010403000c001000000300b644a408040000d21401004258002041c04660040612818501070054188500c500b401d00301d22456841d1541030b11030100c4104020402160118601c81105e0309090503088400500303212024940501166604d50008180f190036210b058080c8801041510080c0d0b034150420f005450300300011501c2e003d0310301000f951012100c100368000c50800c04017487c0e08466010380b04c2c3c1c90b0080c171b008105a92800003071111056a51800c0e4080240d11000840c10032401e0040070f01c500a150b40100d102038052081000e100e20000910fa240d10051000034016118001514110307400c680800300409080c05055003d40742480c0020360011083d0350010400407204910000d9400c00e80d211602c41c2e49460058402800038003c0d603615620075803200b130000e482412259071042c406800e82d090201545e03a50300680720f0714080d260140e000410041c0154904210301d03402000b0107d051 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 480824145 1250 480822895 480822931
    0x50106270e0c090d0b180a1a270a03120e0a031206030c2603030c070816020d0f0b07140f0d1401090c020d08360307050303010e 56
    0x180c405449030784200c615403000300c0300080c00c02d2454010b030360001902134050301040b6250719101c0c018550496643c0c000858030b84100303516090014407002c44d01d42c020150005008170f00150300950300c00a14894801e141c906103804204060302c103035445210307107000070002e1440500e005045154072007801c2d145946886100034440701c0010f295455140c01d07091440c030003c40c100c003000142c030007074002900e04c0c50305200c0060280103680c03c02c040d61a003a8103a01450b841068681d40320b00c000d940004042100344500404594688008e000c080200e02c140003101010303030701042c03900701909020303600c4144150800c01401482c0c0c40d41e9a00601c140303404110700502e2043c0300014000c6007000d4455880100320030001944560012001040d0034030311078400e41e501d40440018012034180700c1d0050042d003607111042c500540c900350040140d03540c05808040300d11013001301c180c2001c20208210134442910035a6070020700003080c9035800f90028540d02e40c103000c0303005501c10010b00003006031061100300e = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 480825395 1250 480824145 480824207
    0x70e06040203090a1104020d0c110d08040c03080d090c08030711100203040b071509120905040203010b030115020a230f07051011070308161a060604150c1401050106 72
    0x1e130500c0d0341c4c1c41620400741d0300750003010400a009052190400f54a420010101280c0240803d00b001190300308640b040b82003542c007150041c0c0c040d100100500c004040a00001d003042010f050600100030002540c0d00082c0c4035030211300c0c011340c4a9012500000365520034003080d4041c0c26003d03c005d80341c5240c2822003980c003c0d62445240308071104480d02141081c00c11007006d4a191014201c0002400f49036124146007285d115800030402c00b040aa000000305800e0900a4904a0340c5400ba95030442e0710b41085d801355001841008070860048181d40030009041e0784107001d44083d00c1b401c1000c016601c009443c0303040c02160017100280d100540420041e501c00030031285408082c42d05120000380036902e9442e01d000b5800040007078202003100454816889000000300c0c1c05075040c8005000c1c0701d2a00340007440c06444031508200b04000900401d0908061030113810400d1030300b040540807945412001d05900c00d07a001d80c59465100410000d82d101c205011851024820b050100141200c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 480826645 1250 480825395 480825403
    0x406180602100c030e0f030406020601150509040c0c0501141006020601230a15050a03050601050a0e0402090a0905012301110303010608061f080106020709090b060f06090d05070e0604020309 83
    0x804180b82d507182e0b410300441c148681c2100f03d08403003000441c0e0031804071041c0c0545a4003e8040e1100510420000150340000c1140c00786400510351111441c000450b0107020141680000800c180507940101000080c024407400829001007840e1050301c2c280100c040c4085040750f44200215400700005003c800e0004000000b20440164600c8010f5215404190310342d0f2240d0281d8049104000d03000e01080d00080213202da212a650f003082540d9920b001510b00780556030f600e40001d803400f1023050990070145c0c000c11645900070122020030b43d440d94010143c0c1d4098000d0700160100400d05000c8014440c112200c030142401e0803e0304000720407030203075070303020502c030384400c1100701408540c0a445454007950187c0c4800c413007503014001c181e030150040100b0700c07440b070061040100024a011035403090808075540f00203007607841e442c4d14041202c500940031419900035400c201440d810f40e64800c00d50170180c0314bc030240c010340786045c44110038500d0041003180660700420070841c0401d0080313 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 480827895 1250 480826645 480826663
    0x81b0c2106130614070807080105010f050702010807030219091401140f0a0c0b130b01080d0203070605060609030304060f030c030207020a05010f030f02041d061504060c080d110406180602 82
    0x20300e03004007090380b609144001d41041c041e40c5141440400134420480d0f030158100b80714403c1500c94948990f40c4400445a200b9868101c400042c018410040103611940b08c4a4014159140140c1000301d0000c0b00f122844252244101140c140c5008010704403040a91401004003428402c21010701d0f1800542c0501c28441545602e030130020300d00208500400c6440d0401d03802800f0801c0525001074030000c400412031040d642c80721200b0000409650001340502c08516940c09581410303259a99130002c0d00000e001c0692026090185001a80b4100060030007407034a035894800c1c81c1826403002e03040b2446660031104060040054101684803006020101c400a00e0a00d0010740c00c0ca80c101d0042013148904a02c40d030000178005010040c491400c0002d0800f400604803603100c54040083c1c1e40e030a080303010306120051100300015030140341d0400055000702e19682c03074511229003200486191524014481401040c2400f2440e400200703602d88000703441c020718906041c501e02070340c4c03400c8036 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 480829145 1250 480827895 480827911
    0x91a0607050a0c090b040b040b010f0c11100305190b0109050108070c0215130605070510090f081909090218040f1404111002150c07081b0c2106 63
    0x502542006010803084180b543c120380f402c0c00761500d0b440290090104d60050178461818200007503078900e0240b20310302c007400d01610382008240303a07064290b80319040841e042d90b0181e207042c130003a00c3da180c140009180c81e1007070354005071340c2c0f07003000c0d001d041000c215111205562901441c05080e90b0055000300179600242007983c03190340c45880407562003441c0e800c000c2d00039650350f803040c12503800302020700300c0381800140c1c902606071200f004403854019090040d000d03501c00e883c22508440c1981c032621076503004004600c03034003886482c0d0a41e160b018009043c2d145940940e0b02c001103500080b03100240c5415981586001e943c0040703100116698085c881c82207039907181c0209200110360001c1d401003481c03850780390189030a04044010780003042007140603418507101c03804014400300380500d04c45081c8602c100103440350010011503803c40c020455400070104120180d841d200c1ca0f4028100c1c400100605204840205102c08003441c400c542145000c81c24a015000340301061441d030044c46 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 480830395 1250 480829145 480829147
    0xf08030715060b070c03030201060501021b1507020312030604110703080703050a3206040e0604110f090a05060f060a020316110603160e0d020a03111908070807091a06 73
    0x1d104500402000c40340e014003003000e40003450400300892404d00c1d00c2100c0c060b4000304209590fa17001a83c90b50715840028106111090211450b40750820341140401000c0c0c03009801c02d901c550100345404500342003100c100740084100308803407501d402a52055001b40c1e500303904060355942d02801d140000ba00c03d005040d1a500055039000350340c1d00c003404080144251104014540104140c0450341c103482440c400710032000540f042c10b05001e03020004241100410f640d5503107885100d0340005001003103134000300003081040c5030394850100500414650300f001846041c110204152409200c8450b4005c00042c0001c00300d0315004004e8171041e101c6164650003440403803a05041c008520301000768444400f000340940c03400202c1c408110b02800c1c0d104e00c00c0515403a0b04101142100380002075109900d4142440011006c1e01c00050280016105540080300200d81c40852001c91300b1060541d03000308800c0250000812030100100403c4204020400c50f8613500310000e014456078602400d0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 480831645 1250 480830395 480830423
    0x70c08030a0b0117010f03031101022809050a0e09060f04111e060a03052202030d030b060c010501090f1103010e180304180903090e0f010501081b03040f03090f080307 73
    0x1000d507130041070544061850401c65178584c0708810860b2482d000940001d01002044954000148220f8050172001c040c5507405948a8501e1070080418215032010060401000105501ca0503136040240144009550700d40c6407000c000c03403030301c01c0c01010852440b01001c1800046401e051038080801e100f0340b008942c20300c4003540c420350301100d00300c520f0b0003650004544801a6059128030b00030b19050f010503161800c6442100600d00b1b01c5c0780041d506403c10800255106d000394080a07600b140602406d00706000d14191b2402c6800980c007040c4101c0e201e03894480288803511486004024084405003154102464000c040100401584034403035001400c41b044c035030800a030b800821042e40815402e05d5202c0d030100107410f03807000803804261081c002040044009030701f94070400312142e08130020381c40c20700110744051001c1c05084142c07120386a1030155002201c0110b209501400082e01c0c5960585401082c0b94002d44c022481c031400c000042c8800000441218500350f00400e820603181 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 480832895 1250 480831645 480831647
    0x2070b06090a090f060e07060918020901110d020a02090a1e0f0b030a060b0310060605092803080702090c0301050a09020d06050901080609010f061a070f0501140906070c08030a0b01 79
    0x40c8030f0308098a0701c050508a0010407020f40c0000c10301d6022082601e20301a81c900d015264081203010745078103164114804d1408004543c0030300000c20341490201512440c010360300e41080f004a03845030050b0022500303401582842d00707445da00895650001c104480c003442e009203005e80390040c03048501c1e890750755207001041da6030804407034040002c003078400c05000741c50494000d018030b80703010340030740581c50300a10349583e1840780e00c04440050701e41e41d181904407820000340e0304a2440da0140a101c401c151a860002c01d10104065842917291503070b258401d004010520500a004040c0d0040070001403000e03442d00040d000454628103000b5880c0e0401646040c05012182c110035008894000001416a030004003d4042d1030f1980080180b200b80301010005d441450040030350324030343d000c0749200a0803c1c0e002080e130903003d1a01c40148500c00d5840c5401c1d181d16000c1c80c40c070704401409108120707105000a07034004d0314900317042d007000d4429980c0c48201c5c00000c05000c80150742d2040c26440e0307 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 480834145 1250 480832895 480832901
    0x60515010e06070213060f060807084c1a0732030d02030414010c0e0111070915051206090d0509190b03090d0801050918031606020414010302070b06090a 67
    0x16441400c018050340740c54128030804503080d23200b02000601d20401007901e20f4080c201407402070321751850107005004d5040d0305403522003085041007803400b40d0140d106001c04e00004c1c1c6c851100702004580c6c000e103180100c1402c071416030046022810b5401c00c003180000301c1d202c50b01c0c01d001c0d130080d4228880340c03122a091011418202044407190100107400444558564001c41c4994854030030701181403c07004010b803c03901f494000c50040303554000000c69640c00381407440f98515040c0101c0752405c1d01c40d90b42c601900e821070060b2043ca01c400d40140550b10b40b02540c0c0d4403220400e80109110700c0c0850029036121500ca0940092203400169070410384c86070314908240c200c2d42c05400f545556039411030780b2568812640c070a184d02803001d10368480d131b00c200d03c554101d4900400144031038a070000c10f22410703200840c0e02406844100016001181c0301c100301132681d405803500580321450404552070f12940d5401c1503040603c1001010300140c44800d0031500038001741d41b95043c90791040a00740007 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 480835395 1250 480834145 480834169
    0x40e10030501061d1513110f07050c011419030b060702030102120a06080c01050d05060612090307060c08010e0403180504090f06060e0603061306060e01080a060515010e060702 77
    0x895400c001000c51904101c2c0684d003180322440310070810780c0c1d0b1088800103c0420082c00c10342e00410071601035401d614640c0118465020609406280c900034521380c0b043c03507005c00000c46490704006540c82d0f2a40e00111003510050805070f1451a0070f20294101a000100c01070030420f05a80340400355454440105a070030003503016008559500444080c01c0c464881240c1105080b07080c90300104504101080103000000103846071401c1c03558000803400905401040c058000c2c1c0d090019560701e802490400e4000c0c80c0403009517a84403640e081031010b07100c00c403403000c0600c003032000104951800100c2203548542c0624040d0000c02100356548110422544090f82c01400d03d82280140f2144181d40034640381b20303550401c01c07255030b107803140c03a01700c011228668503401c13a10000d03000e0136410088100145c0702d40c07800244e26468600304000204213170844101a07004d1511642008810321078142c0001014024200139450700380000c00f406104400c480c0940c0022a0a0003103480381d42510390 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 480836645 1250 480835395 480835403
    0x301090e030f030103030206090c030309010905011407080f041e05101b061509060906030b06060d06053a1101051b06090a0507090903050702040b06121602071a040e1003 74
    0x41d0b44e59503410025034174201691150303554000e09186803801d140010031202c20031410785414600924040065580c0400b2926504038201c040141800181c8810001d00c42603451025154030385041520f1104070060154007132140480d04681030240d80c0d200c00c00d43e8814100e40c50248030005500d156207601c8040f2220003014141131450740400c800141c11940c0079504003203000c10016075510000030950300f00d03101c05040703100f0150204001d03080c803c1c0240460182a407003c03902076030760004503214885a200a405020210141c0c0c0c0c03103e41c560100c001081c15007003510180d038bc2d091f180c1c0720703401a03035450441c140f04000416203e64030800340d95004e801309600a440703803850030000e010384414048204841c14000d000c00030402510b03900c15540990f070140d507000d08000c0980d0900c8010168071601c00c2c1e00204c00d210b800551012900000d02c10804600c8503410004c10f00c0f0041c2c5006001c0d002600d03041c0107649080840c0c0001000d5074106d4144041c035031070a860f007902101c0c080b401e0b500064 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 480837895 1250 480836645 480836647
    0x7020f0a14031005040b130314040b090a090e070b0c0c18040b0c030f0a0911040504060902040501150507060203070309140304060909090809400c03050c0301090e030f 73
    0x41c10302880d041155603440190305070b40f449000c0003030030700c210341d803c48004025502a1011824450040100060141c82800c03c0202520440460b9041c0e07089540141140b10000030003079100e08003100040000d02c0540c1040c0400d9042824841c0c07920312502900c0101207000c14000c1c041d200810126400700310260095080003144141c150040400310740580c1c0c264a2403020440400382c203400c50f841000020308074091912403020740e07405490490025502950070f400d4403280f5603203d124140c00b0314031030140014100740c07610610094400c1640420b850b90380039242c2140268024003101c0310f40b58000c03401030396903890010a0703000700300c082c40150a4001038250161007040000003007041c0d82c1140c13104502c450707581000300151010318100400101051000d8859400d01082042800c488888420800d46003004d141740e07072200f00f003404000990b06903401801e0490787e02c950110311041d80342c10302092402c0d601c03a240310710061041801d581e5890511442c1007209209545400310010017071 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 480839145 1250 480837895 480837899
    0x4050d0b012c0c030702030d020c06090706021b090604020f0403050a03180f060309030905030102270a0e0f0403020a0501050f07030b03060402130f090606062102041a07020f0a 77
    0x1804100090040c2e004004503011101c035026000b9401c89040001d0201c00d0301c940e5140c0d04038003015000a03000d9815840b00b032080e100180c2e9180003400d00585000b000b407000d40781c0200301524210341039003c0402d5400400c100c0044100c60510301c80441019103101c44c9a4075441c01080c02423107481070a10010700041800320070050007240f100c4916019940310310401c10805038020100c0703034a228900302c01652450800c100e40c06500070400d6a40282088105031743d41d800070900ba6480940c1402d4205003460b1610040442604111400c000664a4031007040c00d2482e00b03e03c0c0300c0081e0149080001c4a0001401c0602c200300044585e43e00c00002e0119040c1800002110041543c4180100e030500d01071485604001401c18480c1d5001090816807403c0304010798020100d041c48900d4441d01c1d0145800030a116001d588002c04041d580c0055042c82d0394118201040c4196103486024010001000070810083d0f289525981c01a80203944000324070009031100604819203400c06140f07040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 480840395 1250 480839145 480839153
    0x210f0302011d010e060a09110a0305160f080a02040e0a0f030c0b061c060513022116031106211f061106181212090d030e0a11010504050d 60
    0x3400c41c8942c40b0041d01c4040101c0b2100390a0302d194880000751680481c0004032403082a820041500c1e0040f10699001c0030345801142081e82182c1080d0f8442e40102c0700143e540c13003115100c4004000e00c07a03880b1062800c01c007500c5d03207680c034203100640325a40782e4a10203043d0385c0900120300d02580c84a00018050b500385805016207900f0501921201c0050380042c029040450540501d041d88407000f41d0001d00d95030fa004001d08000e445c0300c20300218215600010707154010007041e01f01100b01c18418002510303c5413441c102d42c50f00441d0108a610301c040001402d401c05131968940100c0321180c03644041040c1d0000d1801200304003080c0000902480743d554034000340049050105903900f0301d07994440303078266211a009a50501991b01c2140003941000e0500414070710010724009582200300c81d43c04c1c4080c50b400c4004105d0706042040e00b031040b088002c00003890640342509091200110300490543c581d0140040a0300811800b00010000e80c03103603085034081d1000808400d10a00f450074 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 480841645 1250 480840395 480840401
    0x3180706090503100506132007060506090106030e031617030a020c16061409060c0604050303093901030b0a08010915021e0c0a081801020d030e0601210f030201 70
    0x11a8600900a075400007086920034000e8622540d0040c00200d980c00c01254184014008101c0c104605072980941d10403c0d504500127000c11405404003094900f4840204812a074043c1c1c400030605280004a82c01c4003004000d0354048800e0100d001d00c101d2050a0180090216011307418003032000000304071405005a01800c15484d07407004030390602c1075003a0390a11090080c011032003c01e003010300281c8894880d03402000041c4026110600f0f0000c01c0311494500801510b08440302d410200030000c4200c020800307002d414140300a0f0544407041042664010a008a028041403c2011500806074042d4010b891000b00180c80c900c0c000e543c54848078003e16200404a50030300c4820201152441e1a000352140e80c81d0300c008012100301c17042006103080d070040c642682940524040781000c18000c001400d010304110040f083c01049135030009042440c0b851b45042494505180c1510110000803c41d05555095154a0407500400326000500d1459035009100c1011402c040d810158190 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 480842895 1250 480841645 480841649
    0x405010f110c15010f0b071109040f02100203190507030c0f05101508120307021504050303010608010504140a0b03120408010f05060109030308060120030711010815090c0318070609 79
    0x1000e9450040383d240314507003e03190038829001c03c0800d041090100f4a4100014161a0703c560860160f20701c100780810b43c1c5032130884042d1603042d284c518100941c10450091100c03101c0903c0914038202e4515a802090030120000804008000c20a502054001c0c901c075488079030003161400d4802403d1910650b58808812468105414100c1090101042c071200c4816100c101c406024400741000003004580c10041041c421071141d460b490f5240d460b02000c90740604c2c021009542ea88d030400001501400040e40b18034080c03171811441c000c0c40050502002d4009001c4031011032000800f00000749890070741449215442000031b0002844c010540c0070409800c2c40e10740030700080d035500005448122961002030041105440016180d40c80344a032191101885240d15034841d1724141c1c650300d99000080216403d81165400c0303c21981c104400c1640240311203400d8035200d03640004950801c601030042c06070041e02001060002c20320840002c0003ca000c02214001651400000c2c6101028 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 480844145 1250 480842895 480842917
    0x1107080c06190e06040b09031207050712081311150c031215010518060412061a0a0b07080319051e0c03010b1206010210050a061a090a030b0405010f11 66
    0x1515032014554083c00350010f184862030240041da40c80b034840d10300803000100341c2d201e940001c102c4500352440080d650340c010307501c0d0394501d52101010303d0074420842c210249030090100c05000c228400102c00292a0302c076500c4600058102005004107041d258401c80c040d54031030020032003042e510f00001c00361101c010042c4c0d0102c20350300d511b030900003500142c082440c0050340400001200c045d08924078041c004d0007a010f136141545d1003501c00411207010360110f03250760311500c107130024100800103a03007440c2c001c40f20130344207903c2c05c480c1c04942e11a06000800c1c103840440001c0824021032001d46501c10005824003403481c1284254041c11402150300c4050300716900850003914400060380c0c1660309540d00e84e071810603210b4a0300081b21004240038114881c92603111403c124030300501c1d00403003401d03002080180c1440c101c0c0c0c0586522611100d01030809002c091160b5a610f90106c044035004541c8461513201d03400e009015005030140c42d4042c905244504124041c0d0381c0c0200072046071 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 480845395 1250 480844145 480844171
    0x307110c0d0f02190b2107141b030918010305100207020609040b0f0406170708120406030b1c0308060f01022103061311211003061107080c06 62
    0x406040018031054800d01600049020b1694001420b06034515881d83e800c0b112855070b40c0351356411044c0795a20a4080c524a00c0da06200040a020340c4041260015628141054541f00507100e81c007550082c1c814411f40c2e490324280c072480c0e0b05014000c40b481200c000d08083e007280044401e0b030040501c01e110445941c0300d40307103000c41842024030a540c00150300030410341c81e040540c001c00014111440f14150b119120042d00440d07940c441c801c21000f440c40100c0e42c0c6100d550a032a0604101480d403003003140b50003001028071404c444000701c40558015040c002000d15402020a00c41040340f9440130540d00075504820616030440c120901c5a54100c2d9010039400300d01d030049895001c011030010f101590b1003044042d18003004040c0d540210064a0a150080f200f0800b0041d101d019041c087d5400380080c210005402c408072001441031180c1030b445407410031145101c8804030602c00a0b01c0c0c40d6983c01c07817290003080312080720300e4217805c41034168a580c1810fa030301c0d40f140010350343c607624825 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 480846645 1250 480845395 480845413
    0xc03031006170f0f19020a0809060105060906030103150603051b100504080616030f02130f050402040602120c0c0409080a03060f05010c060b0f1203030406050108011a0103090501060803030711 84
    0xd0b02c41d01c07144038039115a2100706a859840d804000900d0181800600381200c03420050340011a101400904901da6140340060030142e00303c50070404181c2126005a004101070503076a02d903941100c0c1140c1d80803a014440c41c02e075041c054010492070700010598050840303400140e4200880800143d030303085809902410721050191160300c1580309208040e04044001203d10300110b5001d0f101418908010a0117140440000c080b42d2040c0031400e2801c0369006c040c170074644602c090714003401080d1002c40c940b40c20b060000c1d64441404030550036000001034030810f800c2c801d10400380b40c03000203401801540135910700b48800e034000b6001180081e15100c8001086001106060101c61045c0c4614800c004d00751a114040d008000106820000c0522800d1803a29403182c8682c1b0382c910480a9912400c0914146040d107006034003c103051783c14201c01c030070005228070314960705402c00d00303000620f45018030f44103000d440c40340c1c8046014000401000241a00001c280c80c4500c01c000554690310 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 480847895 1250 480846645 480846677
    0x6030501050901180207050a15090b130f021009030b0c0301082103130206090a030308010302091005030c10031b021c030e0604081b070303030f0501140114030a020c03031006 76
    0x2c1000d108044000040703a900740010400d036402002103d0152068a0010000742c032030a44016074001100a0160b99125100c1840450099940c01504d0703100304200c503c3d40c903110228000111000039100c3c80700303805144a10f5005100c1c1c0b0001750f81c402000c6c1d1703880c80c2080c04d0f040c030f13500300b4899044c80740545e2400920318142695910010103450040e281907480d0444030318050b0141e404100d0300903404000708009070303442030106802540f00780e07500700d011f42c1544184a411b03400581030004140308010240402e40e0301281050004100340c03941070704d01030328500031000b500c040c8658440c2210601c0c01240d07442d0b03000c204241514004540c0090007111800201c044584020050070316422000210b0001026400204020300c8945107a0654500ca0141d19040000e103600c1200441d40d18002640544440d0007101c1c01403c11100c00600005c2c0e40700007030075034810080e54000914000001401d101c189038140e881c00c0e000501100e4692500c1416246490030707600808000c540e4800c803950001c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 480849145 1250 480847895 480847909
    0xc080703050c0a1220070b01060e061206010507111309051c09120204020405060406020a0201170624270301060f06020714030309060315040b0f0d03050714160603050105 74
    0x804850350b00d80d19802440030404e00205010100c400740c1034180e03021480d9585051001d080440c0c06101d0103002d81d45400d20213071511007103641050003001c061096002c034120380c1c00841d80c001c0007800c02e545e4602c1180381080c21104045c60305940040d81c050402281a07039a80700c2c500040c85102154450090001c50b060310000d8240e440000802e25541403004030000f0312041c01c0c5c244058005410191514001041c6401135040040140e011a10030002d66a02c480a00d0000020361601101030a0a00228088000c0c840809050440645a08554001080444804a0211015580710324030752025401c004410403580b8840d600b480d0002ca070051051142604030b41035a00100805460f1642110465903c0b021655050106006c04030f1706441d000c005611515030201c103400c0048040d42003204681490740950b00500c0c8203a0210001c4d20381c40341c0e00388000d40500708662070f40018a41000504a00d10700c00c942d900602d03c94611514403241c80f44282e40f1992001e0219a032500148200 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 480850395 1250 480849145 480849157
    0x60f020702150f04091808070302330c070f02150c010e0c01080f0a020f03070905130b0a06050708040503070602030304021201051312172805100b0a09090c080703050c 73
    0x1405004c1208011554981c0e001940700090500442d2100c0c41d561500005908684030075805604420381140300460024403410044003840d03c128080c00203403c240c400320300000c0105452480024140c1e09005008020070001a402040030400740d84070034100c04560080920140c884d0b08000c01000ca014002c5035031407245006950702d0701150313103e003040590007078044c1c00c10605940c200031a522041002c00214820541500e80d024000c4c58442440240381002118040b1145041030419a81c0e0300d144040040b1034192800350307111440d5003013250151050f0f40c0314650510491900048541d000710107140304500840e0740d24103800d42d43d2070b02030988208a90700002c00807043c941000103014403d50035071070891850b05490b10741516081404400082d211302d00010002c040100009215840c0001c540c2c461103130034401c1e420a58080706895421380a5030084c0c09001c01c84d55005e44c841c0d59148003c028040f400e0244001419020f0b082000a0f07a880d000603040000240c405e1015504850b0 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 480851645 1250 480850395 480850417
    0x516031214121f142e031808030106020a2906010e040b0307030b010311060a0e060a050408160315060b030c07021903140c010c0201020a120311040602071d090706050c010603060f02070215 82
    0x400748a511800b01e0007020008102e00c500b035121f880d1b2501043e6440040c601a08081c1c000700041c0499007800302803104012920001c100380940100041c801c80b400d12900124282014940c10150100180242203040d5800d501407240d079200005221380c000c000d504990240706030000381090041402040e22910241c2e0000c615602401846414000028a000d003a1840c00794241038454510901344030400c0c1c44644910010741080c4248140d410300200760740c00b000f00410119240c42d04440c01800020080c044211012541405540300e00482d92000c2c50824a00c1030210384034600f0325034a0480c0022070050348120780f5030440075401100b0075945e041d0160020080c1c4061903403030964211940340102c0c200f42c0c0380c1114403030000040d03010704040c140c82d4000d0110745081122504440001c80d1555a1039807056060011000300410103406480c4c03140b4001fa030b124140c801050140406510003001d40d4900342c01e0040b07071001580540103c501c200c616180324400c50080006600404080c99 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 480852895 1250 480851645 480851719
    0x51f02030313020f130e0c04020306010914031e1c020c06040306180230070e01260601030c09050f0601080a09030c0516031214121f14 59
    0x3030031030402e44000804440c0f004003000803585000c40482c03240020701c50132440594075548019401d41c42448002c1c02a40b007581c0071411490b010303000804800c40d41c4507409650070440c04030300713550f2401d00010040080d61060f039100c2c0071401392441d668040300050114060074286028561610114090045c208014501c0303003080e04588828006108100c1140002e510b800c0350840140c40742c1060f2206004030b154110f031048140841d600000180071201a00c68120403010f106400d0304151040c190f0709000180321003007406603118400e54048e45003c20840c4644000001001034032690f03801a030f400c1c40c0043c02261034100205c00c1e1250150b030300328045200503000425000881d07000c0d0700e05078001d01d42007078440f086840c0d8908003040584103c0b04107003800024410f00c042c1d17003145140b809040c41c21079aa00075510703c143d83c1e8003400c0f11004d201a01c0501040310106440304100c000780076059003001c0e950703840710820355094016619a0103108400e28440c1c06070795404000c0661203501800c5 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 480854145 1250 480852895 480852901
    0xe10020d0e060d0902030a031214101a04090603120f1b1410050a0e010b0a06050304063216050705070e0a02131e090b03100b12100501051f020303 64
    0xc002608200054a1041c4da0f8124041c0940d80401011a005000392110100c0c10b406244a0050361811811442c8100400040c001031000d103c0210044071310b41c1012404982c004024800d01d48540c0d84003a907079904003035010091003001d0f003801c0d42444268644032100b8007440000c1d9000689450048005038840540c50045641c881e80c2c188030b113050300244c1d2151078200340c0c03010458005440140c105070782e440b0181e07004034003480340e40200c0e80c0449040e41114038001c0c1c000c2c0607110041c40100b440c0d454100030910f05800c01c00000000703003170070b0100c100c030b012920002403d41400c94400e13407038135400c00c0d80d09081806803003241c0006400034041c2c10310a08000880302d6211000e40b203c1d044030783c204146c0e07502c41c0328a800c9501820030034001c1c56080d0000304082c0d44444880c0c0242e450303180b4040c0300f0205940d0000b03094a0b00c4c0f07400d07280441c1c1034500c103002604800b50044070101c1806034491400f04054960710850681c3e004603010030040a00d80ca5007101484500e0901001da4020404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 480855395 1250 480854145 480854149
    0xc0405090a0b07030608030a020105060a050909070b090609060a030b010e0a0f030b041515030303051f120309150e01021203060901060516060f05090d030e0601140d060c0e10020d0e 79
    0x18035580708101e41000326005d41d03280600c03442d40d03001425000c0180d54840a00c0303003c0c0381c0300e84410000c12040380c0f40703d007904000300d2007503c4001c20300c9009940d86002641d80c1458a442d026124107000c001c1196880ea190504040e0190040c0209680000c0106054514900d0700354140c4059548400810140a0540c1e8407881220000350054a0065220314900c610109030f0081c00704403140b04c0b90980d00686549400303400d4440162002d2205403a182e003c60841401e41ca022045604808140c21a24034600742503483d911a50005e40040003058424480c2035008548049803030740030b0342188c452515061090030240801c0e1303050795100003010010018584540058507030559103500410400810303503030785030032652407a08803600c2580781c200f04844888248800c5084140034203061140c94001030455451b81c0c414051200c2031190682d60a90300c1d220030a02204003030b03200c1020410f40c00401c20244c00010110b04035131062680410a1060798804500e40a264209464a841c21104001 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 480856645 1250 480855395 480855413
    0x6150313030c06060b040303090b030115120b040c03150504020c3a020601030309050603060d0b0c091203070b01061e03180b0f06030607030902030a080a0309020d11030c0405090a 78
    0x941502005601200b41c07000c5030312807280030020700f46622031994861451501400e001115800300004020500040185a145c200074600b610342601c0c00341c5100424554000c02401110a89a049440d040303400e26802d4045e4084498020080b4080030016a030f84e0410040c0c0c4a26008140c103500441c00408039924a004403a16242816880006906c01c04000e1000c2d48641d842d0100164000c1d8010001e0540000a000c040e02040e10b8840c079600d0000c011a1545114038001000703540b2000028011a01001c01ea03013148030010514020414581c80c51941c907000f010003a034180c80c010000040c00c50190a542c03520700c088014000c0800c0d4021003d4009000700103d1103aa00054404400052803600c4210b00c42c00010b0300381550342c04d00800385441e04c44c00030f0480081c1468400b176580569800610030030340724de116140700c0e41e420001000f02e010b400c800200039040402c000304841003182c400c074220b501c050241c0490341c0094004080200380d40302981c8806458200360030010125003404 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 480857895 1250 480856645 480856681
    0x3010e07050427032c03060f090304090c0207030204060b030f0a0905030d0c0305090607080c12060a050a081005070804080708180916090f0f0e090c04060b07020405061503 75
    0x28903040b0350003401088140480c522524110009014400d18031180c082400080c0f84172003880308401c0c444120f0001099942001034111420040d81d100091903040b4100300701c038040d0400c10740c2030082264041019503503503aa40000c0344114104a80494080008003ea9101d240203a80f40e00d042e0312120f1136100240103410b81a01c541c001040041107880b0386004041c43d903030107560002004d24205c10868141a0003500300401c2013900d505000001e00e500c000c0d02c001c0c07401c081101c8400c6c1c40d4440007500d001600d038007280e0080f011110000c0c0352040400c0d07810400303c4a190078042690b0300701e0101ea0040d0101d40040c01044c0500825010030200009000c80a1320000130395084a80c210004194102c22107040c6040402c403000c01070000e0740a0070b158010201401080d20340e500302009400d44c074210780100710000120070002101c0e00020442801030510141c02045400d84075040005e0079805100160f002d542010f0103d805801c00c03200d00c8803800c08400d100c50458071141c1c551034980b460b003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 480859145 1250 480857895 480857921
    0x1a03070501140403240b01030603030203340b01080f030705190503071704170c0901030f0309030609050606040605180a0c0908061311100e15040b0a020f070503010e070504 75
    0xd0201000013402d42c1454a02400070520b50944500500d191174107940509000d1410107060110400000307800000b542d40341041301c0011814042c02e950b075004151142890119075000101e009002c5c042e034807002d603042e2200300c0c0c140c030120b6488040c51962881120360041041d4442401410a9150740b00b05110b254810400d6038544899a10b03070001c2040208122110a4030009040043c1c110215031420100080c8016040500000c0c1c00220302290520020b01b00c8401c1d2004101054070540c40500a194480c0c0108447d510504105983d584100d940c03030b000b03d03e0507a01050500e003c55a19011000ca0041c4c000d180c0c0d18bc0020300040c1c2568428601408a681404500c95a05004491040b400d59499005840c9030b13042c08034294282e0346100f03001e94120802104000c0d804096130840c1c840980d48195803902d0707001c1d80501ea1040d80e108424401c0003182c6090303266808103603142c3c3c194124088941c01500c0c6d40805080760041e900704281a0b0000d5800c105900301600800b04801d52 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 480860395 1250 480859145 480859147
    0xc0721020c190501031a1e030d03060605160602070818011d03031b030c15160908030d0504030c0b07030b010807021c030b031203130b160c110d0221011a0307050114 72
    0x90400466000c0171680c040b007c07901420140c0034070908040010892140d200e00c1d0034065149828800380c120b214000d503c508040303840700b000c0d0900425804480d5140e41c015401503440004107100c0720a29403980304540018254011907001282000a180e111100100650311340103840680841c0c1c0c1c4240c01108000d800241f0074050740e02000d10080045446140d40c41d4610300d441441802100d01c0c086400b802d000d9090b0007485549000004d845113512030b0707140010710707841714117007a50f40000110700103101c200500f041140542c0e040e001079071440c000b81c8810800d502da00c2d80590f203804460b40c0c214030703501795034024118103807081e04034480c00345028013995001d500b481094402c640c402c80311000d8807501c01070540b0800c445040030345d03800500d400402c410069105801004010003003000340c00380000390b407190010f0f5a03800c134441090380c0c01080c4005440d01c0344900b0b820758450112140c4294030f8120705100154020828107090080240984010750030400103403a542000c03040310b5040d0034 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 480861645 1250 480860395 480860441
    0xa020306221e060b19180b0901020d020a050c040b010c051006050312070b0c090415030b0a0c0215010506130e0921070b06090c0721020c19050103 64
    0x2410300c10290070101c01510200310304511400c52007a0340b076142401100c4600e0040c0c20094484076100303170749501007018036240158540c64000c07104212407801d40513048064900002e44400040f0003001100004c0c0c09660140d040c100c0181e84030030749510003800603081900052524035065020180d01c42d8141491404030050303803201850100c00200481e04c0980e80c002c2070100380340030032000c64110580e001c01c91801d407003540ca0082d5054080c00d40c908580e80894950351a03590383c0c12600c0d04860410f00c80c550303159242802d82c002401602c03007406051401008902031032010440104a180e00c00a401c940c0c1d1810f018032803140c2c0400c102005401c210480414400c0a00c04102e005095440081c400c1c8014500b40c203445210340200071082500c00c100d03a10000d400707a04403680c4000704980c0c26070243ea45800c0c2d143e9501c50140c00401c03004160310382cac8252141001001426400950840d44446030702e40c141b00388188803103417954412200c2001044658480d4001d0008500d1003602460122 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 480862895 1250 480861645 480861679
    0x12050901020c1e070b1c020a0903060f1a06040f030f110d0308040515010608190e150103060b03060c07170d1b02010e0d0c02062808041101030c05030a020306 69
    0x103000d0f080d8a202000c8924002400c803c41040394a021388004525980b501400e000d03d0284103102110002283e83c01286600805003e140c88100450f0061420303c00800c1c032030f0380c4a008100b41c1c2c60400c02c0e907080f0103500102d82004020b903015604d040c0b0641310054110f8942512420b64141c04031214440900c40820355102c0004021506210381c4442509080c41e00c0e02609004030010281850042c2c0001082032581c4000b0142c0c12402c0c00f6030050742800a4150302020b0101c1c0c8030014181c1c481c1031005c20180c1c007039840d501e0481c0d002c1c083c10030600714000300b0140c03644010b842c1e11046140a00500b130104513a002070b1000f0705491540540f405881035500410783c4c10700c1e11010030041e00821424a900d8081c02180c0341c41c002640a01100c2c00c52200180c40f82c542d403103004e4081c1501085004a0142c03000107c1c00715035030044124142d51071828000e004200840302100c518241e02d131210b40d154000c1c0111801441e01d502c42c1170544d03035118020703002900001c14007544000300311010341c050 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 480864145 1250 480862895 480862903
    0xb13060305070f05010815041805060c0a020c030304080303040201120f18030e010306030b1302030a060204090516020d0e090405030d051915050604060f021e1c050a12050901020c 78
    0x3184120702a025880c070b0030740140c2d00340410b540300c2410b0151a004000c0828442d40c0d0401c0420800c55000074480b00c240d00308081340317075004002000303441010280b064a45042020300f60b850210350844420400350001d0540701d0041c1d215000c4c0c1c45e481440842c2c0150700819543c2d0b5141440ea100003000c4503c46040c000341c80403000c826820400104692003803640c05410303d52040c40a08091206034955610103140341002001141f814120300b88400c1190b4040c04803106c1c072500160300350344680e2180c10040003004103440c0b0228038000700181c5083c050010913803120840d0740385c032880c1101d1845418010102c40041c003c841c2c50108110440104140d0300c0b07524080d0324091107454003c1120079010301140c51440c0c0e08010071708120030400083d0758200c01c0714103403091458240100034403440b00383c1c40c0c060864401d40b020401c0300300750401d468000600e40d2001d101d0f25414075124401d482d086c1c840e0b00c6004000000214070013801b06000440f40c100b5900051140b0005180082c03c0c05a42c0c10 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 480865395 1250 480864145 480864149
    0xf0825080901120e060105010509041404050d09060207031205090402041d0105130b0303031b071205030f0c0a12090512071a070305130b04171903051f090b1306 70
    0x8440105484001d0b50b880303412415003820380d007001c020301c079455000941d6076501442020304000001800b50815180e079005441c40d0340c0391018000035410149011600d48030101d01e80350000c0d801a8000941c00e01c009150b03c01c0b20b41107041c103401e0b5000400c08035042d6001500d0690881d03001c000000d02c00c5040c02e650200203c1955003c0c001c0c0d41804100311141c00e40d14003e00b0400d08100811105644c0402140d40025140c640004030502c1e040e07118940380951a0050019440810843c4506410a000b14801c10b00800b0a28540d82d1b81e0102c1c00407402450071060002d048100c490303035000d110b5841070343d00380d000b1f004841c00d10f8188248200700ba07005a6044402e85400303100a00d04482040d0728a07004585070505020902e040074405c200741c1d50361030010309803c1401010400703200321045039070484101c081c1200c4e80c80045411a0307602d011b02a082200103413600001907007850340c44028640078079038203401901031403420076040040c120802da243d0303110200032503100092115104240c0 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 480866645 1250 480865395 480865403
    0x250b0108010c09090b0102030a03021803150703051e010302120727110406020a0b04080c073203070b1e04030f1a010b07080a020a02040c0809010e0304030f0825 70
    0x5019200e00c02c0040400780781e03600c04001c0e103050503541c1e200c0d40c1e00402562680c2e901880c0058072400a4141f48075490120095a9054054213544100403480720746803a114000a072410300c00b0380c03103100d840071400440e80c1c0213030020300b1080e00500042c0b07031801c1c000c641c0c6400881106c4005446501980f1491980040c01290854081c80c1d403101c1d0340c6500a081c203010001c09107500b440c0c07804002035201e8130031440083c00e520704040080c04001d036150a8610301c9810008030703180591160500400310300642901c641501103240c01520400300d0342d06c1005200341c090041e01076545441c411030401d4018a540000d024400000340c0940c5808801810003103000d4034456442d030805013010034090600b030030900c0c4000300140050082280310b104641c1d0b000e0b0300a8601c0e1740c81031000f44c120700f40702d90f89a00a40c0982003c0382456035035400340324a40290a140c00030440300c000055810b90703a21581c44001d0021444031002c0e80414014801340006501e1440c4000e01c040001000f0400b000741020100d07 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 480867895 1250 480866645 480866651
    0x6010608090f06040b0c07020d0501151d07022503170a03060b031605070804080313030c060c052a061603020c09012601110d20030606250b010801 64
    0x1406a03002c01082d50400404005005070742015100c8412000b002803401e01074500010b0900215224180b1000701c031904807008010394618464005270361040d07445400c40c118000c290070b1542400710202c0364013851194004150041c030501c20242211b55115244411b400d201400002007a102454001c0980c01c084c0d49580e21819410060100d4045070031688624005204004000070a000492000c00003820815240ca01c2413600302011b10803900100114000894000c0780c60100501e500c064a114074018102d06840380da046810b110b00c484003a2443d484110307140c0014244400c5071b040506001c40c42a881c02d0303110007042040c1c0c8609081d003590350f01c3c0100c0d082032660522103d10890b03c12a444003082d490845407000610f090050f41d403102c10780105145000800754000a9060b90351840340d61900f1803002038200406261541488040000c0b0006680f807080f0021a403088900070011743c100743c0c0c95004503001443c090442500140206107100110307109044d8076008011900000c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 480869145 1250 480867895 480867901
    0x40503010f1d0303040507213f0f08061309050604120905220e0f03120603010606091205030c030325090b04060e0d060c0201060e1803070b07030e06010608 68
    0x444642c4404a08034500390f0814001e020000301d0100300c3e0700488500c0c0c1c0100b001c18450034a50590000e0b540700040041d900c000040011007840c644250100340f22102a081000c09800c03071414403074511007018000340110030703051601805a444035801c1003010b0140d80500004a0441c0201c52224505030780c40d6108070300304410452040380c09800030405103003034003035585810046000e81c001f1000c40010700c006548113020400c00c503404162024070003000c039082c1d1a8200350b0030b5203980c0404000f0b40160452000241c160405014404c21194141e550300c03003ea1030640e20740e11920002408581d00e010030811070908100402c05540250300d040100030b142c01408400701903814000101c03006204500c0d8041000300840010741d0201d880c0c038100201102d1107800051034140384480b0050903503107004501246d6035030550103482900c01004040156481e5000c10741111a040b008800c0c8652081080300000b46001d44026000030f041e080108191075450016410f190098201000144078a020 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 480870395 1250 480869145 480869171
    0x1e070e0403080f150f060c030c0d0908210d0209030f071805070c020906010302181804030f02120403030e01090918050c0d0f0609030522090f1404060c05040503010f 72
    0x203603002508407428050300c044003c0490000100500150b100321000b003126a11a40c09000300d40b427800c03e0406441c80c801c101d2030b020303181d00e0076801007201c503104510103144800710800b40c840031a94543d120500f0854080031100c0a0741c05103007401e030103019028030b001c6810000c10002c4017034014205401c142011440410086880c003e00074810020440c401e140541c407403070043d1750003200030f280140e610020240d0301d21541690580081d001000d0301c1010030115030414950340210f100743d44421404100d42812030f80c0f030300c04c00e450f04030540042001b00700080c028040f084052806042a80d021a03036000c00c0300403100038112005103808803814440030044103101c0003c000004440044030420319032191409800039850090000f40d54a0786141418095400c0d11500070310100e01c3c00c2e140c00691101580700840c3e21a0184003800d00f503807080c80c40081d009107600442200f0885d03005580d5501e070480501190711204003480701c10040404c05072000e00801900e2404804085028032545003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 480871645 1250 480870395 480870421
    0x71202030901030f0c0f080402031c020c12011518151211030d050d0f0204030519050c060702060d1a04020d15050612040f050c09280e1e070e040308 65
    0x4085090a10304800503205a0f045446d4001c11604e41c60202015515440845c0c079011010140c00f1a480095140b800e1803940001c00c140c0340b0300f00b038490313025600090010074242c0700d20b284094a00d0540c00c105100000005464541005400c0008a40d030035000440b00100000c03500040194004400b0f440148941243d564a00e5102a03004082078131b41020300500c94000c101c40d480c0d80d01e89607003505103803203041e40541d03010319001002e8500c040003c4a03100e00003244d40718204e0341070250404954907468504165001c0d9034001d40564902070074141e075840106504040e80c3c0d220b01e4024411040c80d2100e00c060300081440440c001081c42d030081e00303003000074899440107200340ca040001c900500f892401064000e540000501900b0b0200d141843c2841e8119403110381102e00e41d1700308103c0c0580c14600c1c000d0310307400044101106032280850401d44401890305052580301110202e80301c0c8400304104545042c3e60283d0341d40c2a100c07071800ea0403100c16241507000030070781c409004d03007a03d03014 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 480872895 1250 480871645 480871661
    0x503092a0306091203130501020c070b031f030809010305061c05010509190215031308180907050a080106080606130308030115260c0408030714060705090307030f050307120203090103 80
    0x20000346024081d040003945070f80b00003051b00c010302c0320500d041e200f009000d40503a1420b0341d02000f611030013a12105005c01540044699080401c4280300000d604101c2862140540380c0002c101c078030300212074005401419014103010340201c040c0e480c520507110380c000501e0726980319000104850030b001c22910301d490a81030320052800c0101c204140103030381e080b1544800c082642d800340d85a650740201c1080006500c28094806880020a000300c010b5000d20380d00c00010440e00c06a043c0c0ba08001100e05004044110000c01c0c0d500005110203801940510380c8002e0041c6100d252800102d1004004c0e11f46500894070000040011301402d03401c5540c6408003e0f0510308035009019802c149a0004044268408840e0700280130603880402d1030103c030040c0c54903401b240e90303a2660745460102404bc1200102e480d01552000c00c946521540440f4904000100281580c0e03041da12007517014203050700200e03001e200c10015200042d03080c604408078080750750055034840e0003c40024050b40c070b0700 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 480874145 1250 480872895 480872911
    0x714010c18081f05070504080d0201020a0906170402040f110f0c0c0616031407020a03050c040f0209030a110310050f040311030a1e11070f031a0403020601060503092a0306 75
    0x500b98030f1030076051a00380c406103140300c0c04082015100c6002c140c6552146410011243c0100301a0340f9141e5015001041ea9007215a03808400540c2c80301700b21684098480d00703105540110010501502c0c00750492034250b2a015000244251142c000110319440300711040e40109000ca1a01c0c118801404031404004080c0d410a10341010a0b10100c80d88902c84001403e0161120010281c076410f82c0c00d071040700703a002d480030038185d407a400e01541d514a030751203903485107061070254107070150140241c4205180c041c004010348001681c821825605d50840d858141c41080b0b121a2088031900400c2d010301c01c030004aa0700d0f4202400c004100c1c3c41003035686034150f8002c02602c2da001d98044902c2c2c610004004041120307070302101048031520308082521005104410700820515002d0316004202c900c9114424070f41e802482603030312907000803900038000d43c01242c01000b200380107900030340d4420032180584803990700c10080d082c6000c0e91440800412071030000b8100c682e060400003e6000006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 480875395 1250 480874145 480874153
    0xf0501122108040f14070b0c06090c0619122c01050603071202120a030206220c0605031003080a080a0c0305090c060d0908030a0203040c0506030f0601050714010c1808 73
    0x260702024050b0000503100424a5070300c912903505008001800034000c180c0720042d46e0342c441d580c50803002c56400404c6c0c2c80c03107a4000c10002c540140000118602c18603409050203003410f00b01e00143c140505485640001e02603e0349984090120610850010345031031500d108202880d10300d050340c6d0000c46014504c0c07582c0b6007014081c10360380016444048400c2410807512142070b52000c01c00046d00c880c0c40c06040c0c460401d00c081050340101e1400d2003004e200300c6054030340614610003001070b400c0d0034010f4290840c101041c821305108800560340001d0300c02e511040301d9500e50320070040703078031001114001404010600008a01c9409003e52150442c41c0030b00003800c141d080c1a031185a420002449044009042500913100750460815281c004101d241c492401481c498040c3d4012107007150b464500040104041c84c09105480c003844070ba401c1300301255030b28001505c840c0e104400a45542d41a13080c05192588240100100f100c59a9100345444c440141c2480480503076801c41c0340e550300 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 480876645 1250 480875395 480875453
    0xc0206090a03080c1b0607111c05040905060f0d06060e01240e0f040c031b020703030503071407020904150f02090f13020c01060b03010305060906060d030302090102010f050112 77
    0x83d2110040d500940741d0394000360795114001c2c8075015080003040401150040d01d0400010035004065108001071300d2044c0e42445007180281c030b00c90700206100001050041c0001d118082943d481250712890142c5a82078400c1480b00180304075150181c111880740d140c0030103110711b030403a8120301d00500300c102020381e110100c9000c000a48290b201204104010071482888958414104050210f0003410412420102c40001400381c5400090043e040004a0441a5652000030454212a050b0307865030700710744450a00700c902054981900c881450103000c034002580d180b4400c60300442c80b482c803030032034007003c400d07000240c8804400c15044076106020740d180b40d456080d00815064421603190b6000c1840b0020780009000e00442d1580961902c0c0340414111400d00007941681e0142c42150550390300c42c8030a540c2d50740100d40984d0041440814040024001e4003c0c00c0320450500003c120100d00c0c160701d2045030b8099000ea2200746001d82c80030103104480011102c40c44d924407407104908 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 480877895 1250 480876645 480876647
    0xe0f071806051003230a0c03050c07030f0f050403060c110c030f03090f040e1914030a0215041a10151d090402060403060203040b040201030612050c19090608010c0206090a03 76
    0x20000760743c007414582c860110350b02001c01503880351083e41c03111410301045e062096000c030042c41e80da2140b201007841e0001040350b035600c040c140c80c48550315968460800046590854040e02c0e020b801000340300c030a00c00440080d425009a40010400b951501425240104810719024800d2840c40c003c0d00710707880607114610044101c80e151075080c0e44050004201102103801070a102035074a8403800740d131b0348030341c1101c0e91f440c10400200e0080b014240b0304100f0350302d0f242d00c1c0e105403281d06002d030740001c0b1044d522180f440007070b40d4818041c1a003507416035450030300c010303183c0001c403003910340e84c184668180403010040c80140010920303458112000020b9503c01079420f005003001500c60b500d0035000504641e2440d088402850b030003482591641060328100203601000c0d20102d01003402c00d940803600141c0700c1a9400e06c5a0008024608a82c400041c008003111401600f080c280f640c031404140c0c0c01c0c5034003440d0010460f14000203220040d40303a00070f06040c0f0203021009250007103510b602c00b103 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 480879145 1250 480877895 480877909
    0x6090303042d17250f031a0601080f0106120b060d0501080d09030519020d0c030501020d0605040c0e1003060512030c07090203090d0f1b140c060a021506040e0f07180605 74
    0x190010310346110240c02c00340d011804c03d0265402044d501c0a007850102c10828600e80b1001240d48085032901c00b0f4454500540d50300c41e04070395094a210210004100b814800c4008441d62400d50500040710341e10a404154242e2050307001c803400b40d403070300c00411401d00304002090208045142c0030b0b00c01400e43e61401e03280c41c115500d54180448200e000307030555889080c00441152b205640a450f070380e40e0301d0014042d4109040411540e0b1a00741f0010702c1d410580030750f040e0043c2c0e9a1b908005024018100440d94110304007110802d0781e00e0201140700d80361154069201c1c3ca102c801141ca844907803441528085181d00300c00061401442800340c060000a1650000303010303801c08410134002441c00b100e1020380342012076201c0b030600c0000402c1c0300c60300f100c882d042841141951100802c40e01030242611a0f0300716800107034000300743ca0704c3c1448100740240c3c02c207038010004038a003050030840ca440c04d000350307400c1802600940c004100003c00404890702c0d00f000810188009441c00b000a505 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 480880395 1250 480879145 480879163
    0xb040609060f0e0606150904050c0f0307021605010207050a031e06050c0915120106080a020f041404140103200f180f07090302090f0c12090c010f03061406090303042d17 74
    0x25034271200400d19180c515402d41e41003140011445441c1d240441000350f0b00d031034031210000c0c191403003440030400b5480410f58000307a1b0390190140075420b00d50390785c0a0380110703d030640e44c105d06820352101001504c140112405801403102c600d442d41c40d45010400300c0c154032192440c051a0030404442c484080b0034000e0704680150400c100c3c3c0d603440d000c070100a8803d04641c0c40c00008009000f15440c42c0a0454440242c4e003654100003580301c904605010840c203000181280c40707148400d01584600490b4040c1c4918040c2c00321224003810008110000c0344007044440165081c020011000c2c11f02c1e00b4980c3c001030a1600180c59481c1d03401185003c1c901030110351000c3e60403070024000c99101812960303802011400d4000030b00d40084040d4564807020341c0e00c0d00045d00c4680c0034181c43d00c207001e80003d541145c440001010798480402503242d01805886d6050300041c04005154403000144401341c0491001a80b503080e070f000b21800102143c4c2c2c0110769140c20010742c0041021000483c054 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 480881645 1250 480880395 480880399
    0x2118060304120e010c0515010303080f24060405042c060c040e040c1d01031b0506090f0f0a030c09060617070c02120a03031401120305070b040609060f0e06061509 71
    0x10f42180c0c040100c07200d021489024005100b0f0b040c41d81c480040d00c2072228122070007036840c0340e40c40e115000e80040c000000d8810034041086242c10340101880f440c4401c4008070020101883e01da44e0340d0100381540c48581c11a030b0f070111002810b600f040320104116200300c02010107050107151088000d18140078600881c8013680d840d400203400c20004403422005003032020030300b0400d4984000c6400007100700f4002200d1790520b245180485418168a030000c0d594021300c0315051410b5081444601d070400710b1200d6200180100e060b6980d150300000c00051401090704202003400c2801c00015030b0459031200e410059400586603a00c80d0100400780c2021983c07400c42c2000900780001101e0180101c03881c003003030250307902d00c0e000c03d90560301200c0601c102d40030541c182c4c0c0c0d0b642001f00a5407080303c0060b000c65000c000d04800554150300c12640309118060002d184442c9840b8001110541401c5909140e907564034100b15800402445510800440b401e02c6a0f10600d081c41e60a0b010b0030700309034 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 480882895 1250 480881645 480881657
    0xf150d020f0409060806070e09060a0b031308040b03160503010e060103090f050105190f0e030f031902070f0b09010524010e10020c0a1202090f09211806030412 70
    0x755100d000c1d03000c8400408031800c080c81035a4840400d561283d000b0384820010910000d458281b07410a9214580b0441d00148140f0b5030f289007003615a081ea100400c07002502d07192a11440004821101800140418590305034032441c0c148002c80388443c02d2108a01884400d03c010002145000041c0307600c00c07000c0c40d010a40b15414a0840c030403244040009200754289020440c01e01c20380103144802c20390808050207580c094050074030803038040724181103298000f04054124580710000458110780640c806840c0000981c00d6031049800044003202c00303d45207503504051200d000042901720706084000c10450500c4541044040b46108a02c003000b110540c0c04501c9030300400b465410104054003180c500884800001d40b03030010048800d10440c6014008035420f0170b24041550b64643c05440d08200f604c5420810220ba85c0060200c081031080640040ad44202216105090b40303804086e25150700c51622140c4a8072120b5500d940992018010400800c500045805a04d02281800 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 480884145 1250 480882895 480882907
    0x1101050c18030115090c1404080307030305040515040803010608091614010c23190f08091f03050a05010503030717090f0a0e010e0a0203070f08100f060306050f150d02 73
    0x403a0240410040713001052510760b8000500c1c00194000c2070704d1030702c1651000341920481041400354012401a034501d03a00074481e00f8002802540300c550040c0c007030011100380302030403e8802c0095400701d504407034011021004000a9400141e050b400c2080d2401904502c5c0346045d04803840d1802c2d1103485151424141e07078184590007000341c40301c525007014035643c1d0342c1d1454500500fa0003202d400004d0b541318582c02d9071130000d10001c882003125407000600ea1040ca01d921290400d4210200007070703000c1e41040170b40903007101914014400e4103e949010940b4501091200119172050f840207021303400801848001500c24442401e485810100c03442e117415240c00804c2103088401e4201e50000c0e5425400705000411103003550403910711802030b294565421344180181e01050752507d01140c00fa5441129090041c040c10758000d000c3c0341031a44450352001100d290005691015011039034a280501541c00c180d6404c03400c003001075440b01139002d4048035940e103030702c0b440106041580d808115 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 480885395 1250 480884145 480884149
    0x604050a0303110a2304150924020628021206040e0c13092d0605090c0f04051e130201031104050d080a0306030c09060602100b130e0a0b01151101050c18 67
    0x1a18047d10760396084009020b2070403030240619041d4020000c0803c0e141500400325895125482d0000485901410443c1c8480207640014100c0681c0890395001071419410700e81c19030b1001e8441358081103528100c9003040400d00c011120388000c0c00320945c00800c1c44103140d0f101d42c6403104518440c3d4500044012031410f000010100b609400c85140c20300364a1805610203002c11422024042c0c0c0f0100000d07101e201c40c041c3c0c0c410075125042d41101c10200c0300c06561409501845d0300c0107507032000400411017820300700c034044412136110700800c5001c10382000b5964184a000c2c1340c49403903030f01d00749850b0030000026412610140700902000b00010071f1181d01d03110390801802560f1144220800588070741461029109900406005118005902c1d002030480d00034103203ca9000380c035214004040c03081d03c1c3d01400c070b8040024550300ca0002136400048421045c24000c0800f2000c1d400c441c0480324008000000350740d42c18000340c1c1803c0510409200b80b03030455000c490440000d614406d12900 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 480886645 1250 480885395 480885397
    0x90601030b1915120c061e030f0905010c03022218020a0c0b0903041404050402010c02060306011b0501060518040506010e04020a05040207030e0f040c2307050604050a0303110a23 78
    0x41e036200700d646400f20008248003440c0603140050b00c102c60600c0d00350340b81d240c2140c5545c000c0d94410080c4420400c4c2c203141794000e034410302c08222540c0001c6107001e203a4580e00d00303440c203120b20350300080d500044201308403948605001c0d00480749103600c3c2086150021994444003e125810000b41d4000b1307802d0322207401001c000320341d1740d8010503041d454a00384000b02d4a03600a03100702e100d6100c2d8058001020314107032188500c00d990503118030100104a400340b1003240c0009107598141b090003104014001c4802c8030b2140f105100380008074620f81087c00340110141080501885003038054107100000d0305c00714005054400588848450380e40e507000041e0300b10566440309401501c00189181032503032209411004660543d1060054403649050000306c3e00304a0444002480051080444d01502901d4200c2c1c500d8041000c2c1c03d0090588031941044000d5500f21002c0d8001c498560030503030140240086040301d200903070300b0310600d1003001c3c00c4210444207014607071003001000082c003031106c2c1c = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 480887895 1250 480886645 480886661
    0xa05010503010e0c040e0a09050c041806050a15171006050d0807150e0303060102010c05030129071e0611070f02060307020109060e2b0f0f050d091a090601030b19 71
    0x95100c101b01c0c10b281507100000d00b00f41c00d068941d401007007594021403c05009480d40310f92002030404003248292078020040030041c1c400c002c0c258461100210809010b26083d003d08400d51815654038002414940b07003142d0b82135450341403800c054041009076101020003698907044442c142d5501054030f000c0802d40e941d007048406a902e03004081100c0e41001028601c90707c002e800030499610341e01000d8409000912491109656141c070503461103907c05400b2406800300f54141c1c0c10940961350381d511080d0318070030061800c80d910803200103014107400340007004ca003c40440ca00d810001c1c0c4419465210240011b40240b4000000c039075000d1007544000d04150300701d08200300c120320b4640c81688a90190a203c600390140119401910060180201c0343ca1500e13205c920f28203840017801c0d60301180ca8025a0180710090100c0c803d200c840d13004140320b140c40f4202a00c80c008120f00c0fa030500500c0642816556405a0018000100c200302003540200464246c4002c0600c02089240540382030 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 480889145 1250 480887895 480887909
    0xf1e153309040303060302030d02010506060306040e010e030f030f070306060e010503151f0e150a180b0307030518030a020a02091302040e0309090705030f1914100f050a05010503010e0c04 82
    0x20300100030506606900c82015039100308d0644000c400c407a5000c90a840e0140c074015840941080801e015140a500004404403103c001154410391100b4903400c640203000c1c0b082c6032180000c100103c2c01d00809440d40e2003001070804005034ce080c4640205040340160712681400301c0000800c448180901c155690000c0090202145407641150f240f2034804140c5c0305400310383d41d0030321149a071800740210340940300005200303400c152643c00200c41e12005040d87d0402030701c1010300820010318041c002c1d0321442c9140c83c00b2a140c200000d1255140600b00111442a002801800d81c810303404188607483d26012070314403a460319000600e0403001c21b4080025446880c00d140b49552040c0803024001d0000300321100d03001079440c107109031a107100440b454821800e00000242003004144041d2021894149000405680503008a000e41a09480000e1120700c0070404008145c03404c1414009800150b0310b681e01d103813600d8006016404103014503031a042c0d5040000d800b2011090a40f0028204 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 480890395 1250 480889145 480889159
    0xf08011220040f0f05070507021804020a030b04030203090a05010e010c170d09030e030d08060a06030e010b13050402190609060503180303040308010f0807030f03110f1e1533 76
    0x16010072030700109071184e42115490305010004040314024400c0e07698490f0050503103600c01155103c01d640784400184100e070700040900e4044081503031215114802c52081d002555900d802e141000100c24060f0300c024104818070103070b1015668014620807203150b001a2545240c0203049815102c4c0c090720386107917007486c03502420034181940038081d030203400d4003901501c20300001d91100302e41101045504a402403d608800c000341413096000503124440c00000248008510b4005100000c807040340d2044ca646a0b0240b00c01c0d40380c0400c1d881c0390300040c64507008031640fa00c440a04600c44501c030700c900340840800010725203020010f105104540c94800d49950b8541440c000e81209000c0c055038607905e4445401042200c0f000400f40103403500042c68408210341658104c692102c940348074003090103215a0748840c03580030049112000380d152000e4580c45070028002c0d1801070130044082140e6400801d100c82005030312400c011a16030302083c950380c0300c079030703450610340c03150f210001500400 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 480891645 1250 480890395 480890411
    0x50d02100c02030f0d030b1017280b101d1207050d0812090705032d100b1e0f0f120718060b0a08062b120f0801122004 52
    0xa030204018401041d161410480e214803002032048101031001c1d1400420b0046a400584600003070540b640f00c8411800700c861900c54444080d40b454510844480d403e80710681d00b0010314cc9203022507000807091410640d40000e02e1030b00d01c01c1480890304203000300c41c0070b80042c60080080c000100a080090003080080200e07243c0b401d80f550210040a0050660302c4c041a682000031600340b01302d030f40050080024004036014200700090b5607a00a003400c1d554150000c4418045c4000340e40c4600e0344000081da03982407c01e1200b08419065403511180e11341032044500c0d035a00200a040301d03015900c0518080942c030105504042c4030821901070b10880c0b00000c0e4800701031079013a41c1103680400520078a039958540798810b005400101d0040b40e40000000c445080ca603400f044944103540041c0012907030f9400c040e50301001600241c0b840117802c805c03078031065004070101040d12080d142c50885585040d81d003908a4400c648000c00034414401a0000d22404240704400064010000c01400c1 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 480892895 1250 480891645 480891673
    0x6050301050408190f050d0b0423060f0a0e190908030103111f050306040b031e0c1215160327030908060603030406031d120c060c04050d02100c0203 65
    0xa00b004c40000310410011607080d003c0f51107603031081c02259590700c0b50390401090380d10b0000503155104150b900300b9030380c3d04d000601040059100030b200001610030030755820038000b400b08002c40c01c2c206c0381c0250603264041207988030802400303030700242400b504003000c034030518080003424200b02c1c050508500400048207014942e1008840c1c1c1e0300440c0c052902c0300301d001c0e0103603803010108816808180c00b0700020300b40d41865001215044001410369a480141000e02013400b03242c030540d600c20394020b010b40800c43c2000b020740f00428415a008100f41c005000c54409258402040e85405184030100035039a24041c0e0004500d0a00c5074941e211000d030703802d550b03441440c05da070802d900003041040002203265004c24504c0c0a24400b401642c41c4c40e082c00000d4010340b031052110302080380044d00c00d15025405001500d4031020244005588031000510301d0b1521401038100e50747d0050402007044140e4a4072403403980d00c1d50540b81c02500b01071218042d0380c40846050043c0d058001d4400e03100c054 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 480894145 1250 480892895 480892897
    0x609081201094203060606030e1207113102071e260c030406030209120c0102071403030c0708010b040f0905030703051e0c070e160e100306050301050408 67
    0x1846480d80c003007100440070421114a02000000460552046a4100d0000010600c00820420f80d60040b003952a525654007003114065072203080042d58400814410031400d106e842c3c20404051403242c00d10403503440343d100101d072a409445c410a8104031004260284022000074122000c1c0302c1102c1300c0510f010301d0042d50040d1800c8a2000b6008100c81034102280d05e0016400c0d004118500c0c01d1000c2800d183c41d80f400080d15130000307482800303004030540c0100020006407895980250701e0750f41100c14003000b040303c8010300059400821134041943d0340024000111070b41c4248840703a20302c3c1800840d08610529985440e140940d000120300d00c40e05402111f40a1410340e000c103d80802c0041c1c44080307543c18400202030390010056034003c688100040c2001640c0c01c04660014400a51070600179407142c1d007404600e40041104000743c0c4110301c030b515403004004100400c14415000c005203c18220b02d1814800c0c0d40380980c8070407052095107d40d014101c0640200114100b81c2025442 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 480895395 1250 480894145 480894149
    0x90501050106090e150105030a15140901081c18050d060606080a020711040b120a141b01050a0c06061e090615171b030403050a031104060f05070609081201 68
    0x1080030b0040c0060780b40d13806905107129901e00e051004200c141c0d440111101d41c009001c100c1c0c040c1e21034110078054a1401c40503002010801840d400040050050245d20704058ac0100e116400201039407030711a1503441c90003e80c0c0407e16090100303010301c0c00c0e0303c0310a18654000540041120020004000942c1c0c08003054800684801c01503a80310030855081c0d20520700c0081c00c480c0441c540401906141e00410030040f4014458004076182d03a0700d552418070001c605940c1801d8481e4992407a65052000480d0100b14026240c8151070281c00a8824802c03da0b24070200100c020340741c070500c030310f0342d0100c0701604c8442c7c459580130404c0ca6203908804558000c01c10031074600340300040c041140202c10491190b258540041d841100d01e21740240c0c00004026155071951151100480d512800c01544114803a403600b42d125010403074010200c03030182c0b007145008c1e80f04202c00c0c0403040c3c00c10340b0481030110364604039958440c0d51620801034014260003d104c000045201c0300c108000803c4141 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 480896645 1250 480895395 480895397
    0x3060516030e03090d110f0621070c0c0506031308040801091401050601200c0402070f1208060f040c0207120602270a09020903011b0302031512031209070306090501050106 75
    0xc8290b040000860b200c2c480c808285500c400c051440d200000e04a800190951304002d080407036001152000c41d46551003071545880740d1000712212080c003040c9031a071741e41001062800607214030302c079a00e01e0205d020900486200d02d6000c000201d40e5404035102404142d40315103070030744a50380e808400c0d0107028481c808542c1c0717403048005440c0c481c80500c03840340303c1d00d8160b4602d44400800895115400807210091041740130702e903a03883c3c4640b141c3c00108495031203142242e90b06c003902c1c280440103c0007182c0038010040c141d81844461355a541010340c000704101d8001950100c244c000fa03283c004070307a10801d0b40c0c40b03040c16880107206942d406000e401803035958a05460907159114909031145250701a80407010000031301140045030301a0040c072401174000105000f0380000d203140160140c5c02130001903000001c000c81540507503c4020702c0307a415200e8215a12010006030b450f4000c0300031001c0000140000955907200400c64140118ac101c2010001e00e01305080290207030509014140c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 480897895 1250 480896645 480896651
    0x70c08011a04141515072004050910020f070501050405060406150f060c0204022203061a060306060a140318060114130b0301020d0f090203063603040306051603 70
    0x140c407606240c01520030001040c0000ea09aa0b502c4e071038042544111103c0c1a00207001d42075039401001440020306100b070084d03a10140314211800d190380301400d50310b0b07454000d41c2004248031340b41034009041200101400d10240c2c69140c286011021400b501d0f01c080c005609000600042c00f0012070100e004a010300ea00340001381d00300c048480c500519204400e200801c654040001c41c3c490300d4500d96243c402000907140a942000d05014500c140360754085800c0100820005c1084a2041070401e543c03c82d5840c8500700c610000920b940401840180107960000b10100140d1180d9601c141c00c995604403591a41013186101c04001848038030303013005100c0c03c0d0000c58110030002003200030713410003400580c0080d011403940000d48078440c0744680564090000f880002c400c3e0182010109a1800010f40300206004040c609180a400201007910f0341e04500c4952900c0c40c03440c5001c805199004580342c0c685403202d1310354411980b0280511745010207010710584c96a4070b041070590655024 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 480899145 1250 480897895 480897941
    0x61507021e040c05122d090304030602032712070b0405030c1222051c03030e100c1d0105040b07030c02041d160f180e01020c0c15090306010e040503070c0801 69
    0x3c2d11b031060150352601d4070103c88020241105001c0f8182e50703c1070168080e00d003401d58940e50b4805070380003900c074141d512440d54041040e80c1d40c5601d0b141d404483c0d810041c0350f0002604e08000c5a881210340c0a0001c030102c2e800681848010811200c1c8040303a41d04407002e45500c240c007022503030425454810110640e0681c102032510103001038095903001410300d0315000d41c1c0a00d108010300040800ca00f41a1200c40d0f03641014024418441400b8041070003040da6800c001000300107803192001c004003143d04a403030030945e90b80320080d14251560f4102455841c44c0e981410359400844541c02548030303042006245c071400c03480700b10b044000184001c1b00c0103122031240e00c1540e610540100d06c03402d03903242c10800c0703c14991004051000c0401100141d040c5103600c3d000d09a84c001218521160b000058400103800e2440d80b2080200302604031601704408400000c5d21008103116420680d880303400400c5c18810f0900c203c1d1100c40d0b101c078006180036921810303039010340303450320302c0903040d6046001c4 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 480900395 1250 480899145 480899161
    0xa02160902181c0501060b04090f1103060d17030130030c060c201c08150123031302131a0d0503070c08030d05061507021e040c0512 58
    0x35508040d42d0700031602c0031490142d041c401070301690030440e4089015118401c0c003243c400c5c85083e014003144141c25035114280415181a941b5000e503106c011803078084031003103031060141680d03005101250501303880b68641c20841080100040c000e00c48100000c000100c0d00d4503550142003170032201e13001111060ba5220314012a001d8008080c0201c1d585803001400144260f100403219005410702e071100c071010601c1d00441050301c4c0043c2c0c1c5c46a101040d41d00307490701d0b641041103014405142580003450b00000e00c1c1030040d04d003000203060010184000520070b0200300c8040c4001503000603d901c91400c00183c01036a01c5112040c2e0256212072019024036515000d076108102d60500b50300c1d28004004144087c2c0d000c1c400d42526180020320018000070368108200d0010103450300119114601000300030101c83c40038202c1c91160700e0303c03034081840b04540d03070544104c1501142c18410f2001038801069032101d005800da9802440e2500088269400070701408404501403480300c015598001 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 480901645 1250 480900395 480900397
    0x51b0403050d030e030f040620070b0f0a1e02010b090603012702271b031b030907052d0a0806010512030d0c08070806010801060e010f02030705030a02160902 69
    0x5030403500003018030b0590038004d400a15255810508072450602040104001034100360007610001e5600700310000d514200b20503026400000c07070302500b841071030b00c0c107030242030311920740b80090080000c00c00000302c60140144c0c40e0110050084003d003a545010000d0081480d544103a1240d030107140800d8540c1070501c40c2c21400883c5a01000c40c860b86441000c0044d000b222040340e000300440c0113100c4242810784082811510700c0e00c2c12200d41010f17840e074411007130131410a55501c41c0034020030458681140740d01180c0c1c03003c040c80c43c7c0d0300d40710b04070305034108105a0000b07038100e000d08444e58025545860904081c2c52451003500200344000d00700304403030f210b5101d10011580b0010042c400d501d05170700c9580703401c1c00c950110b910342072222900000b9514004d0784c15020409003803c01812a81004660390311100928010b9020340c10032001030032945c4044e04140c1000b03030f03500f80c40300c01c03a00810444a000350010100c0c0d4860b420480002d580d010b8841d80f07100d905943d803800080f0643c1d180 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 480902895 1250 480901645 480901649
    0xe040f022106060f04061e0f060c050303040f0f02030a2103050615090d0b040501020d050703050601080f07021e06070e011d040203040204090204090c0e070e0a0311031f051b04 77
    0x2801a20b042d45418040000118010703c02941c032641d00d040001e00160170301c2a1100f01009140c616600c07604c4d00e1041d10b809044c0c1d92211040c4120110100000351000c411a540558403c101d09001c2650307080c10b030500031000c04025010b20440f0080e205100104807000c1081348c0c00c4444034150352441c2c0044065500a441c4541c0158000008564460240002e0443c030750010f85000402d10780790706c95100c43c14007680c007544c01303960004040005529601410754840d5460805204504140c400240f030f80c82d00500403400712032044041072800340300b840503012840304007038a0b99041c844880550303107d16042c0ea41001054a04540a00325405426650b4485020102d10110a40000c1c180700182d4001802268496601c028050050740d40e4450440c225000300c5034110600c0c1448110043c8120180ca0300301480b05d54558417606642d03e240200a50703a205889800301e900c00741c0424500348841240010094a43e1116070b0440103581c442031280c0d80107011803004210041d400b101341d10443c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 480904145 1250 480902895 480902959
    0x30b1305070909150522031d01031107020907140f0c010c0e1027080f01060501090b180427050c0604030804050d2102030423180903040e040f02 63
    0x4511300c5482e000ca95031000c1c0d80440a0324900a070300d00c40f00860107800890030750840c003044156074281c603010480b002003840c4000a0030208502a03529410b61541d0107540700082c0b040e41c1500002c0e2002e031191512200003010620202e85650702d020a020544d00320300300006243d8645522001054032070695420701e940d01900d451008660403100312107440c041040074800345032000c1103004503000080914020031404025120341d140350180d107401c1d00d24650045042020045003800061160b0088640c508070389030348240581013a074041005030002d190310501d000d001c080d50190400c40400700345031151041055174214520801000343d1401076000141807102c05000500490801000c02c1590501600300e008080400315240540c0305020446a801070b08007280c20000342c0807440c0d8001080441c60b541e403802c0c0784180b0201d08140311800341d002c441805000492103403032003401140c1c081c015000b0011311500c0c107402c1810310500c10100c00c90280d0006041c030b100014000300c400c103214901c = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 480905395 1250 480904145 480904163
    0x71a09041a0d080a0e0a090f05090610060e0d02060309070e01080312010501110a05071401021e060c0f1215120c280e090703030f090605070305030a06030b1305070909 73
    0xe943c0340c40d212038001a43c05400e011300c844c8084003a41d1500c03c0c0345c2c0203102a0b0700101d10100415a001e0694802501d48221507214006105214148411050075100c0c145030000c0e0004140002800c0c44034850340280d0010800028024440d502040c120169a40d1421010041e46e8420660b9907922540e034031144e14100f0707000140059031103203035040200801d402c00c98400e01c0c000e44605040c0000c40d03018010050f0a041c0c46082541c0600060395000141d01340c0162400506c20038549502c40108005c40766039000481400c20828041070790100c03c0c10301c0b080742280c50b03d002c031044540e5075503207103d200d100460810002c0d030000164182c042030000d89081c2510302d1000c103210b40c425010301070030741450444001050040c11195041e118907504001840b50510f941030242c040140003501c901041200b1800744034151b0130600701c4019640c1031401660b00e0f940c10001c1002880640c200404652201007407140c821840c02c43c01404038090b10503655980d03540c00111049074184100140a41e82c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 480906645 1250 480905395 480905419
    0x1081203040b0601090e0f0402010921110d1502030405010501120510110c0109030206010e060928020706110a1806090b21040b0a1112010306020c071a09041a 69
    0x250b011030310340002040c1400201207844021001c0050f6086900042e5240c0082c20403081d50791218401e802003050a001c4d403c101d1100e00f941d0041c0404240203081c01c07401085d40d803004d84900c404410990740180640c008208680c03500406940292801e031095070130b007000402e0b88007501c1c020f11a101e6004004081c1941613152081c007038040e000740580301840601072088403803000c2c051341c0d10f2944a507020300819810031302a40070300c1d40d0203094075010302c90400405c2034618a148818039950000c0c0c1a5050402e0410740c0c80d0040d00c80d20740000c24840c1483c412081d0719800001400c42e05841c0d48418110313481e03090203181d40000314810180064990701c420003802580b440100342c5031035107501c00a00300c4d1a000d108121a01c065808641d0400910100804002c0c1407203041c40344003030320001d94a00b5003401201c805401040c0400380c04558006072500325441d00700700c0d5500078201220078a209074211803810160745c1042e10100e010314103001100c01d02840c07a202011131004001c101e007030002 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 480907895 1250 480906645 480906653
    0x15030c091701060e131406090c120f0d030204140f030606060901050d050403020309090915390d112134030b04200309010f11120108120304 61
    0x12a140003564655a80c0d0f80100d00c1310441c0c0c441d64401d503104402810490b65a160410703640c5182142c030703205a00020284084001d001c03582440c0034808a482c54070f15407420085a08095003d032100402d4401c03017081c3c1c0000f90f01030b00544203e52181c80a40440740303031041401132440c5038200c101d5240d00560f00246481c503250014001240040c03500310b06201c2c15412407001c580c0700f6102034002d640045040d5411b4544100100d92041000c806001c0429903c00d005a032003a01030900c40803102282808540c1415080542c0045250407010791201e5056490380b20195002c0711014a826013002201c03100080c10604403000d60242c8101c200140240b404c040c041780714040d02da810281081c0030344040146a18152480001d60030541005801c00aa00a011036421405940c001e904048000384542d50408a640c116041100c4a5549a40d0300461900414031440a011414584000c006203007003e100500b4002400c01410484c80e42c9850b00266108948903200d019a842000010001 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 480909145 1250 480907895 480907919
    0x904150216021302030a050c0418110c0a0b010e010f0323030705070303030c0306050f090402040b3708190602070c050409060207020f0f1809150c0415030c09 69
    0x40c8a4281000342400d4a550004003083c81d001d540e89035032600802400f1003000248111504070b414a003d040c89d003031900940080e040e400710703951050550345100d1003000c030042d20b044818810441042c1d45080186251a500e40e040a0140b84c032008a0311001142c0d260f90615128241c82d00300745a00d0082c00c20441410f40204001c02d15921404240651000502e0812680c006544a500d0200704014800d100500b12034555010705d1048480d549030708080d44503030400703542042d015038010030220000300210344401d85143c034002049404c141c4864403c10340200421450342040614a0415524880d10f941d07002c032409c0c95440c0a14504040000540c00d41c02445213034480c6030680c00d61951440000c00301e4201400c283e440c7d540000356030703045203032000d046580910101d80089490b2900030100da0000000700844e584559000f0201d4000301c4200400c90b40481c00c070218a006260102c003010040c0c109100b02c41c6010b00d0200122420740c02402842207642482d500c0d452020f1400d82c601d156 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 480910395 1250 480909145 480909157
    0xe0c09100305060702030a120207172208030a030506040603111207032102010b010903050606040e010902040c030b03060106030e06070f0509090a0b1201020909040609080f0a0e01030b09041502 84
    0x80c8000e40e4000000b41e402c1c003a075449186160082d507100ca0050360040d11034140000000100e41c03041107408006807818400030483ca001501c8540c82e040c100300c0a1000005c0e40710000e030491103840000030301483c000010074014900e80d40c1441581c440fa010311041e101e035408024012194081508500e04080000407c814240011510820703a00c0d01c0328524a07007986124099245407035a2000001d4090240710344210702881c02e6a446440e5441e07031900c5080103400144600e403940700c8089214025085105e0568004004100303806010070301070000d20960144600a004000c000904280030348034012805050380041c0c02103a40f80c403000c40c0c4401c645504201803000c00d0204a001d920b8444290344204510b220010380c00300114200702e5030032000c070802c81443c0e00422013400503480d42581503400a9105402141c481050b1402c0003030790080b00c4050210182c08565003000300d40c005100780c20702e003080e24108a404100c41c00e0228054040b00e0141048000b0b0040c80c0ba40e002507801852 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 480911645 1250 480910395 480910411
    0x30708090d0c0e0103110d11010f02120c01020702120d09031b090c020c04110c1e0718050a180b06090402030f03041e080f150a15030b0702010c030e0c09 67
    0x141c44000359a0003440c0c09aa8002184455203080107000b00040c040040c0802c50044404604c94011a618200c40b01d0030211030f01d040001c000320100e80540208804020351114061141d16000c0c0000c41134000d4100c4002a4400d8800c0420384500003000700308c43d026014680e6445201038155110a0702d800c01e07401064444079180c86000488402c0361040020050441c0e0107845881c10704010403090b103a030a00002003420081011000401001134411030700520f414000e85150410300c1c010381050b80303d50107201c00039203600503200324802d04e030b01142c4a02204401081444c0c50f5440941d000c012940c2d0050561500c88003141c95840c0100d510b950051005044403a407440d220240c5003541c00503404100406032124202d90541c0e002e1a510000d084800e0040c880346100b80d82d401c2d9525000036040382c0000081011030141c0300503801c500d9002d07030600c3c1a900c03101c1d90303440e0a010028084a03075000552070f01e800c820196229001300c00515440b0030041000c0c1c8110f004000c8030860141c4820 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 480912895 1250 480911645 480911659
    0x30a03090c170a12020c1e0406030b25020109030f080a1b020f06090a050d261617010e180c0409060b1801030323090a0b0918060303070809 61
    0xd0710b0408540c414100c840a41c01900c2503207403c4c07801c40c03103548461402c1c9040d500960186c0102d034480b450b20f6510201c04a000f060b8502e25040070030010034068201921409000040162101c40c1c0b24003080d0380d20510000c501c2503c000101203080b40c0541e0001000251101c1c20300c801184624803607a0083c0c00c681e00040d6160754120002c126a0007981c80700c000d078100ca0300013070000509210959010001801518000e00c450340d03080c5d00e5100005420051058920007888650301084c0411018038084070000f001d401c11120300d4400030400b03a420400503030007011080c0380c8005030b038129040b145040b5440072a82c030750740490710305010340c124544c545108001c0c41400079070312030180061803409000f0020b94100c002051010800c62480040300c800d180400400c00258859111281025001200c0705000d08180440b60319100c0c5104140d40039080c54400301d2500b00990090007980c504403030f10179200c40d6201500344401d004840084d495003051002501040d4600000c045801e4020056 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 480914145 1250 480912895 480912899
    0x1e0c0a0b34110607200604020303040b2511040606031802040b1302161110051611120106081009260f030c0904060b0304120c0804090e100518030a03090c 67
    0x2071501000b00c0b1124002200c0803005c0084800c40d04034039142c0311844014000301c1c074141d00070a07600d11440c0326020f00031078009000e075155800d4140c44c40c056625042520f0000c5c0c603a04009101c81400001035100d14580540000ca050187c441d020f0000e0741c40f1500080fa502d40d8082200902ca04d41320070b500150700011801c0501c1551004200c26200c500c030140060100e82001140c3d414218030a902030f625034104101e01e00e0704030003680e007020508001ca02c894502c92614510b803012035400b0a030440c3c0e0010307075850312441c1074000c8800e44da2054120340510041c0b10041e400e4641c5ca040c080c0c007500124107580b01407000c0c01c80d003a50805502100e2441e00044008040850340101c4140340100c0d00404c0c004c40514045c007410005106800245007103080a840ba400c03c0c2e4031075101c1c9810702c03012100203c100310400e4262002020044c004100418641c00000d0701e41030000b0f50501241e192000048440c1d9828109040800f05540150300300000010294000e100e12001070300d0810f030090f40 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 480915395 1250 480914145 480914177
    0x30f020907020709060e0103060b0a080a140307060203010308031801060b091203040f030c1401020c09010b0703020a060203072a05070e090a06020d0e160503121e0c0a0b34 75
    0x178210007400785d540da8904640c50740c18210111625a45094840d028581082249400006100d031829810291000c00c1d074284104540c61071140f040020305682c0040000010b10005001952281c661070022070070340c00c1c0600040742254501c0c00b40800fa12030030304c039480c0542000700c002d031422183c45049900d05a22344040c40c2c42e0850301d40c070460362074010344003d0bc05001045100e1150031400c0c0000e04200400310001030b10028140035488003410081400307014903100308141c0c4030300c0303400074411513503814000304c02404c03055410801c03000d044103214000c2c454217040c90000c0241d600b2102607c3d0040c10300544055001e400b40a03240316218600c3e4940120342c41d4801016000503148000401d541c0300c0c40071500300292480340c950440e040c804108243d890100b00d008955600c88200703559020341440791654401203c4503845400d0012070350f40b401013000145540500d00890f01c0080690301c00d0412000c00e01c40300d10100300107000c150f40e14104450b100e03070040100c406041910140c0c20000c4 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 480916645 1250 480915395 480915401
    0x120e010909062405030112080a180e060a050303030610050702241b03030601020a02010e030316050307020a050d0f0f03050702060309210405280314060916030f020907020709 76
    0x508500d18002a24003e581166000528481c242c00d0141c115854000d0710000c40900c02400740003024000742003000c3e10703c1082d1034416170496540d07041030a500e5203c0c0701d020303040807a4400d01561f0707216000321f0149400010781e44140401406401044500340c021141c41d04180c00484c1c002944102c1600c13060792450908120100150f141178481204c800c03912060243c03e41301c4c45054008009210041e60301140f480040c03074081c200b28134000c038244003180c42c40c40750380c407200381fa00c0401203d80c040100201c02001a280201e60080c480b40c3c8a804103c0012003c86008040c030700070b0101000000d088889060009010742007a07820107060745c003c2031080c0c2c000c542c0d550300c5e80c001880d0044034503444035084800341c12158640e41464145804501c01c000482d0300da140c03019200c425640c1812084112401960f480880d4800705150350204565409060382c40c0c403024014503501480000141c5050000c80760445200022002c154007480300c8824041c01e20b00450007031420110b59580c0d140 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 480917895 1250 480916645 480916649
    0x70f0c050303280e010215040c08011d0708030a0504150909020f09010206010b0301270b0604030b04110d0c0303050d1104060c0b0c0a0905013009140109120e01090906 73
    0x6007408115200300e00f0000015003034605200c001800d01e41d5a0b680068002816044140d82149580300c0b418542d80e50f000644c000c02c03d942c00c107204044480038040900d8403031503484003283e4890b920b0ba00034585074000c00c800c6800140c020300040103010090142d86000d04c2c0c1508042881d16102e06020087c0d03401b010f442a46000001401c5000d540d0400203d801403501c40040740c15941000c9808500308401a820b6034141001c1821101d51640c580c01140c252000070a020f5031590b4034130b80f21505100031a0b003030f9a01c00d8402c482d0344482c00c003915a2510305601c4030101080c2c1c0d04555007940c05400000244a6007a0b032031400310340c046c86250003030001c1c118503169a0080b90032803800248140d0002c00d0364048640034008110540e070420301c4502034130700034202030345109408144a1601214881c7c8410080c401d410007071841e03007007903100303500e01e50103030f108002000d000c040d4042c00d8884180e401001c0800500c0d11801042c42643c5003c90800b0502d08000900da8a0282d007054074804c1e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 480919145 1250 480917895 480917917
    0x50f07050d0603120503060910180e07080f0105071806090302010311130306021305010e0906090601050d02040303081617040b0a060509090105062b03140c030309070501020f030708070f0c050303 85
    0x20b02a140c0340908c04968804402240700e5050b03810001300c0c9032040700341d4a900704080d4031601603d80c850001d11801e4041e22032402111005c0041440c507038041c04003547e00f100421015181800089520f9644905550042c0c64103802e0320b24540c01103004104158207a54000c1e002e001c009039105411141b07000550081c000540c40300e90080c42c040d10514550b0005040c04403007104100c1a13154041d1b1250700840440f40320541d591040c0c0140d81503c42c2c400710020321031001070040205600940014003645042c142c44c000c810038560161a1120101502c418454030b0382c0008001030100ca20742039208156090108005a58002240b01680c09a5044803965103c0c42040507078140a203d40c1e0000e2203400014042d41c02613220141244a1900064100710745407003801005921402102c980c454050100e030340d02d180461440b9281d18440c02040c0c0140101c4206200307005000050710b5113039130041b05052808029643e0403616a198140858900880e101c0000e0a03070f805001501404001d = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 480920395 1250 480919145 480919147
    0x915040f0309050301181721090703080307050403050706090806040b0603030903070e04062307030203090a0206160b070819090c080f0703060612030e22060b070203060a050f07050d06031205 83
    0x1d529210351528041501048030b40b205009500d020f6004480c0c600007050807034009602346e1181e55910f4248029074101412140c00007080c00710003a4800d00034401c89002e80c043e00c0d100d035105c46088419044034402d02c0401c1e446200030034042400e0311085500008020112440c0c032248101007070600c980b6900020074410880104018031055016a40300880402d8685043d50000e01c07205001c0700d00a41010b082607808400030311901010030020040c0f6800914282d01d03a10240024400c1040500088a03001200c40116410a01540d001c60007085045e00f80101080103403441d0008180302c0e0005d5944002003040001d506e0385c02d00881444000c0403024000007400c0d0b04203541075420030f92111a0304020f0712800304c0403d078099103446150318101c40b00d041e003a003051040b90000d030000003102069407508070b00080c0000e5000003002030610a50640c0c030f09540f1080401d0498034211044200f18880d000040c00303c0b0311403c0181503510000d4000151a030701d81e12040d950320000d07028403000c02c2c4 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 480921645 1250 480920395 480920441
    0xa0b010f06030e01091a19060b091305090613021c03020105091b0a050108191406030f0109020f06070309180914010e1b06040305060c0a080915040f0309050301 70
    0x251500070b2040d80c03400b02009010390425580ca400031300000c0b1783c0a2918107084000318204000d1550f01c540031a42c064001c0c010a5121100e030880ac0c1c1c0510074052140f10000d404001100e03040c000c15100d034000c0d5010b0001695080c0e43d04032501400340b0126071081c00c1c1014420040380042e100c912480c000e500008103031516000d217900e4446108010482e840181c420500990388400c08070301030307a500b071800100c9600c1b901c41030411140c07901142c0314041d080c100d03401c80c0f5400d0030324018805d071002c404507044401c401080c20308032041e05001075048001880030500500305400240501d80c420303d00000d21035038035070a018282d400c0b035801010b541c0d16024480b0901c40800a580a01f000c440020850308030600303429503444001c60078014451354075070240e1a1640d0f0720717001d60f0000d64103c810345c0c00b18500034202e002141d00410200020400d5840440c1d04500300040c0105802c11100c520750140c0c80b15129124102c0b00054100c003081250100032480d0348007801382612280415215205001c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 480922895 1250 480921645 480921647
    0x90c0d091a0c0f0f1c1d07050604142106090a03020c270406200d0510050603010e090106120f030914060706091514011d06010e010e030a0b010f06 64
    0x8203029010100484040c040303c031600062408851411008a2086503076640c4032059003000c4407084000301ea41031a0404a00d03140f54409040b0308290209400d8480880c4c0710410008980550300940010407103000c2d8114060130521440410010b81e01c9030324203c452041d0a40740780440856a01c6086d801c013040c040c04140e010000d40014660071070700f161518808003583d41000d807010b40507586440c2100041014004581c2c88100500303011a40c002000d030600294090700c0e8026040380c1500c5142100081c0ea01d60314281e9101614001080503265919202417030301021030240c500d400655175407000068440c1d0421641c441c90784541110b81810b04a0300380600441703200c1d8024550754002d00070513503a40e0745000403542d185a0040c00041c1983c01c41c149047d04c403601e01c005c0c00d0750301d01d811a20214100c8044400e81250240d15800c40d40d082031070303003058100fa000e0302d0f00e50200340b00c501c0c0c00485601900810010b218043d00325030b00080345031181410342c082a4000922000f44600501c411 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 480924145 1250 480922895 480922943
    0x5011e09050c09220e1b0a08070608070519030c0305060a26011401120210020c010e040b030c0d0305031e04050705010c0c08031c060501021902090c0d09 67
    0x51061410401041c0361500050a0510030503800b24810901e0800c0c00b000d0700c20240d1504000c000e0b0130340401940001003169640c402929450000c1824415000c1e091407420a07040410382e110f0038043d12440d03217411170980d88407001902200c1030010502142c491609560b0800807180c00301da9020609003494080642111006801c40f03008503c0d10900744010852080c500820800c600074000100c82440000e45c0107002c0300c41080189803c0200004d011003040782085075041c021180c880c0c0e46620280244e070307180d1003960342d5400f08100c100030059078030380755021060011014045c0e820213001000003640b03010b5040d00c00c602003800403081c03141c00c0c10750b01210403220f07000584c0b01c85a42007a407542ea50b42c0f42103100d0b840c100b240c40c3e0266020008900d40340c100800d592412240c540701c565003000201c00d045403855012a1070a5000a6151701c0055555040c2e14248001d014085540d02030201d502401003072165540c00800508140c0040c2d8412085214020300015048a421854140348 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 480925395 1250 480924145 480924149
    0x120403031809020c0615040b1f030b040603050d202503050609010c1b03090e0601051204111504060f030e0c0d1b151e03150902030711070609060507020604050405011e 73
    0x2031031034054085020384070700030406082c208149c40712000c0c04001c40b003180075001c001d1680c2e4101e8241b01c00041003240c00260201000c0c0e65441d030030b4541c0c085c241c1c00407901c45040f9031060141e008601c0c00042110200008250500c0a40754001c556182d451b40d0740742c0402a100c07229103a40d04c0c20700c505c2d915800107420b94104840c102d0603c2041c1c6545000b409910103010b4803030f21a19440100c0c900d680550110f4283d2124400507c03401c2ca0f050404070f000c06080003199014440003072001c0e14814104013110261b90180e00e41c1d5001c4200a442100186a0056040d407680705440c07040d0714030b43d501c03914410703e24446c403c4021100d5075070b07480404a0440d03078040704a40803503406800c8040d401c09200139500c07003510402d40c1c81042c0704100310023400407442103c001d1030924074081120940d940066106200e561590b105000e6400501640c9800314820b40002500041040c00b050f441100107282180c0010f00d4641015203600c0000c007101c10a92144a51614024410288425009003c00 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 480926645 1250 480925395 480925399
    0x1b03050601052b09050d02030a120204060f051b01022215080105270708070e010c03020718020d0f0e061e0a0b0d32120403031809020c0615 61
    0x820f00c1c421542e40080314610302c00ba240c4454400f003040007076505540c4200841a008400c072694900c0901001c0d4481d4001c0b642d600001d000c0303070800400c1408c140221001c44409540307400c0881c03030707000c0d0440f22500310a81440b8070040041c40b8010740002400a1303c0d030100c400307070322010394019000c0242900802d0361020341ca1007130000300c14696541240e42c070380c1194025114015031b8124903001c07150003040451b5030069001003000f44160703d41d01c801c0440c0310396815102d90708400314010040d500440100341c0100141d00500003401250800c280c0207501c4441c1810144c180743ca00040d0000b514403800c0720310042a510388412407900c10070088142c0001c01c4a62035900076510805900d50300b00000c0840c5801511204001303c507850f080d2140e526143c01044032004d44030b00c044034061100701b8550111420643c194400d80c22500030170751b807140b48110f055441c9810306d1070754103580030f08003449a0b6000941c41c4000048002e02c0e03000514042d00c0c500040c1040e482e203080384901000031000c03654 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 480927895 1250 480926645 480926647
    0x9030f0c0a08010629070c0605040303030612051c2a0c170606061303080a1d0103022803090503070302010509100506010507020405150406030b010302030609010c1706131b0305060105 80
    0x301d41d10036079402c11469545c00d042c0311110404001c1c01c0070030344620072004004005403100001c0c015030050190090f288640d5060105503a50701d0714485281c0300d00d00280c45600301541c000702a044c40100110541d03514106003828802002070302400100140c1e1600d05800e420040c6c00c1081109071602d03004c1c00551f2440010412001d82d060b6542c0d80091105005800c002038404c0f20b180591040302c010340d131003240e45582e542c1d40c0000070014581010f0740b040351060364001c030b03101c0e40c001e0094030740d40034425a40044502d058480b060381d02409200b408281070b41d031100c0101058041c001000c07054002d4001251909041c074816152010001c1c0252525251000380840d503030340442214010750b0119000318007a290654500412950070118075445883c05200004020800d51064120b034000c505451040e542d20110b2400d8820710b5605a00223008055140182c1c03520842d4950000005890b0b0084013041010307507021540da0840c21211082024140c60005034540210380d0b2140003841c00e1 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 480929145 1250 480927895 480927899
    0xf08011a04090b0112020414011206152304020c0601240212040e0a1407020a0302060105040c0c0b07050408010f020c1b10030e01110a0c0309060e03060703050c09030f0c0a080106 78
    0x10f240d0364006004110065000b1081c071015517841d6000704410981c14044100d182d6912001d80c8403440c00f0090884049007000100042095862445000c5a541011040821040400a0003c1c40410200582c070950074008040400b03400c020f80e9002c0c0c02d101031800c08402d0407506c051032420b02e01c502101194410b1803010b909000650507070b4112480c0c4074408015031544c00240c00500b1030600300100580c00300d002c02a035540e0001c2e40c82240b5000781c0980d45183d03200d9040c4025a0402ca81e83e1002c60b50320040c100000e21a42c888a034002224640710f0b0405444203003040c01e443c01030410400c015004543c0644000007803001c8030520390004144c054102c00000800c10918205003440b0a041d40c4018190410b4820340085400404c1c25841075914110318001412a1140d4242580020171100c008102280500f501c07803c0ca16005006101a58551004070007502c0000c0440304083c0c014000c0b0400394504012a6100e105050060101310b290070040c043d0320005075100400c0d0780e0400c101 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 480930395 1250 480929145 480929153
    0x6021309110403060c11060c04050406060e150c12070b0f060609010c080a0c0f050714010f0e090709090f0e0f190f020d0c030b0604051803180a0f08011a0409 69
    0x100d404481c2c2c48040030420b980718031700580728600b03040000d090034002c42c0200b01005801000500544808403401c004540d00c59004482404601c01c030b864200c0d2005404a210304c00740009851410a50300c21985050388000801170710743c2000f14100c550b03402c642c040c00040040b0841c80355200c20203940044c2001840000284004401c01016003240b100080100c2d07190300c5452100079440d0400c80c400307464455881c10542d101c1161141c01f40c1c901103007400c2c01c0c031580302c2d1316041c4000300d01d0351710aa000700e4488100255002d02810754070520480d110005036940700c0e40118003010f8014080005e4007411140c40e5420400504408869504000410744400d0361003031740401056004048032120300d01c03a1010460300c032441c1402400a4004070400410071540181e01e601c10903090b5024099901e4105088007041058038142d01d042d04180004500c1c1d1400003004442c8087c0148403881e05551080d00f64064111a000b02d40580d4640d01841d8030003441c4401076800040c152070401480d900d64039 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 480931645 1250 480930395 480930397
    0x31107120e030c03070b0d05090105010e041502091c21051218010e060a20040b090d02040c030606021513080a030b0a06030c0206070807050d0c02030c0304030602130911 74
    0x160110a100410800380942c0d2030401c15658014009412242e1030390f240c030780b04441c90f040340d4400750003d800c00002a16a100c18054241203c02c1245210b449460381e83e2507844080c42c400d000441554280f284040e1a51407042c3c80d4410010400d1202030001e680c01c1016003142c2d092003d4840e090880c00c404106031f40309085545482030403903925401e40b5820a4035600180a402016440d0f0a1050343c0100360804559240920107013141048640d084501d2100d003d0b8800f0440300c0c02d000b040c07008022000010004000d01e00000704454120300403640018211029a0408000a40d59220500405404110310100c5404030a0402c0e540d00e000b50381100c806180d803030018504080407545040c064083c4d08a001d040c80001e03e444085070301c0e02383c001c0041145294200040c858540440e04844c080d60301d0901070400e564907186401c1c5448580c1005d014040c1c0302c03c0441c80204021846030341c06001420180d0301c03680c40507070b0350102580e0380b08410820380c00c030b00e0210b8a0140030380408540c50f0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 480932895 1250 480931645 480931673
    0x602030d0e120f0408100b0310020a21020c0c09010302060703030b011b05010b13050402030703110a0e0114010e0612040b04061803090302040c09082805150106031107 73
    0x10408502503807a000c85605081116816040c2c504010030101a407030303440e034040c2081c0ea0701213040702c06c0f243d18503400200b0780d1080c80075160160000c4090701c1c2604070130f030000c01c00c00c401c604150401c00440000301c0054024440340c039405c185e010030311682c20181840340354a0240c0498003600194110340002718180b0440750020b0605a84200c2500703540d0040341031408441e4815400c54003544141440344c0a0010002c1342392140a0900c0e100441001602c078850007186c000d002484a10f080d640c50300300342000100c40d0307540329840103070006807201c3c1c01220501905060081443d06903500300050200450070701c40520440090007814048203001a8440c0d11540108c0c1c400d100380c4071800e00f20003e100030f224001c0e072090b10300c0010003819000182001164820b403001c0000504845080700c0f5210580107a00c09900314905608803000222813602c6182d820460307011070300100d03503a4940b074030711b103200c00c91882c90289004004060301171003080d00686000811504e0f058a607038662042e01ccc101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 480934145 1250 480932895 480932917
    0x109090c0b0301030f0308070516020904020301110d0e07080a022b1a0f0a060510030b060c01090b0711120307050c0c0909100f0c08071d0901060806010216060203 71
    0x46124505205100810000600c18241100d96a58407420400c0e2001c43d00030040d000301e4248000b1032600c0c1d200340110340070203e8110504a0001c0d43d0303400c010000b034000d0010b903490340d2911141000c0c1140f65008081240c4686400a00c20420014481c01c201c1294484c1b003007508615418000343e201d50b641d000c030041500c0c500c10701c030b905c00400d00b9140b440d03451350107000020b1a4081215090085007842d000341005002c2002690f07958428405031021401941c0c1c010122040308000c050081d009008601d4000f0012400c001d945d800311400c5461542c82510401040300034014003030341241101c081c1180420140003c400105200200382c0b001130010350030482c2c00500c85500440a011220004000803c6d00b0703210704007a95001e680703180c0381810440310341c6001d2101a80103058800c030143c0340c5031a02d802c0c41c2a925100140c54480004d044013440c0d68043c3e8021030f8581e1394101c1076001e84015140c0e400d83c0d052550009150181c001e03003951400000e50001d01520350004191106c107890 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 480935251 1106 480934145 480934151
    0x80f0a0215041e08120406140702010209010504031227090c0e0a0603090c03080307500403050f010209040e030a1202090d080a0807091d0109 62
    0x1c1501c00034102081048820058183e9014542c40300380503001d05401c14140d501e5044080b50201d800301c51003079481c07501f401d441c07034900d12007a040340e1030340b000718140801c00d00082d00c10b224500002c2d00c4111820604032803984030703459018140705401c040d40514110786480c1e03203190442e40503042d01d5034245401d0f40260703071284034006242e42c0b005100b030004524200099008000c0034000382d580180310b0b078000c00070640c80702c01180945c2c01692005510200500060303c404c030740301419201d0005464605e040704020900108404d407800c4404402d084002240901511907035000400c507002d0003050040c400c00643c09403258034000d86013800509415201e8644074820300348031102245505040701e5074016198007400403001c0188c011441c146240d01c1d100c040e0741002e40e248000407001010003807016480949100203000b120460228944000314144602c4e1050003140c0301141c1d = true := by decide +kernel

theorem cover : BRFrame.Cov 480755395 480935251 := by
  have h0 := BRFrame.cov_init 480755395
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 480755395 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 480755395 ≤ n) (h2 : n < 480935251) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
