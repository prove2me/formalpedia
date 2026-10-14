-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0646
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:55:18.127201+00:00
-- url     : https://prove2.me/submissions/a0c9e510-1d53-4f74-b247-8c390cc90711

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 116007194 ≤ n < 116187050 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 116008444 1250 116007194 116007209
    0x1608070813060806041d0705040e010b03071706090102030708180a05070b0a090e01080c04022104080702120f0c01031e0203270d0906120e0307050105010503060a0b1e01110601 77
    0x20a01c4c204050100341c4581404403d1840d961031803a01070340030041205070071344200b40c40024403142034844007409014a40303c0ba0fa054000c000c408036003107842810200b4100886000c0390900e4030703410741040c01c13403000300c800f04006081240880e440c00b854030003010044080b503045802c5c1e00002d403500707414240035a0200100000028694140c2500601e9100c010000140c4031101036240100043e2a03030032144000303100350344c0000e61040c5640c003001c454112086c1001580e0340c030720305440c00207019441401c05a01c2074004941036522200006602d9151000100c05010306a80b004015805800501c08034000c0d04080300c10011018110b1020707510945d41c1e40c11411071400954940c80600c40005040e5402d90041d8500101c2103810021220407540a854408080350603030611200521420003a803c40d03000028894041c483c5c150007090580e8000c40594405480300c142d60001c4811903030301950407c40c0c24280c0c3c0710404000024071039002041c140080d904040c03820042c01d06600760003264 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 116009694 1250 116008444 116008457
    0xb0301080a03140f160b06030d090306020d1d150a02040b1207020c0301020d090c060809030f0901020c04020a0c0201021005011d04020301110a110705040207080d090c030b0c0409050a02160807081306 87
    0x1401001c02861f9003004098028180c02000300c038000341094110301002c3e05450300042d000110340480d50019800d4900790341c9a000b1440e030261410b072200035400750210a05030117004942000400d00c02c440840c0c2900300e00c4c0d403a01c80c003501b21130f01d45000103201d8019400703a106045610340b82800105040568803d0010744480b691401410765281ca400c00010028403100304011200000100e5660001075902541c4034219000100d04e803565000b50182c215001088041c08030380c0204000b10050710036002d0b1074a12200d401070504440c024400c00a0001e5000750000c4d440f5201140d19420a00203030000c40c15000c5d855041e1200c1d0303c600d030480002a400f1529000c07440040c0300207400791000b100c0543ca001803d8031804910302a11003a05102070380c0d0049039003008440b1051200959102800043c5171030100d142c1141508075100c0c1c44103440c18000054a0500c0034801c4604000103407442c0c000000e025102d55899800c5110308a4020310100718a02d00203028441020040240b5541c02 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 116010944 1250 116009694 116009737
    0x20d021b0d2a050706030603120e061803010f11040510050f0301050907021c0509030d0c0f060506060d050a060302040c02010b0f37030c0b0301080a03140f 68
    0x481400219032820419000040c051034110703800000903201035081110408211509091003480e0320400c1c00041542c442c081c00058502d070075820505c1128080c60220003180242c1c0415101c14907007004c05640400100040c405005540c05140b40050000c0e00010320200c005280904503280c10042030520b200c042004c1000b860450400310200c9824504241050a42e0350300b101c040c001806200d2296203641e00250115100300300181e45c48032031403aa101440440400030380f65070700041c1e442c0d01074020744405160150042c00c1600c103950384862035104009064481d08014100034009541c824410420600004160300429000d06403104000910a10758410081101c09414101081da41019507005059a0300003003414030b60810384c3d2480e03510035034076103c013080106145001e85061102691080900311340c903500701582e1044041b082010b4980114600d03d020900c900e03181580329107010400a4411554007414082078480f0320b003440001c0250f641103401408a042103e48101501c = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 116012194 1250 116010944 116010967
    0xc03061305010615170c09040f0c030b030a0201120e01021309050a0f110306010e1f0201140c19050c0c1f081602030d020306190303020a0c090c0c02130e01020d02 71
    0x1c0ea00205a011090240900020300c05840e60ba000d0885a074000345c0000090b00c100081400c468103044014020450508088000401807104c0031594001030f2400107402440d00b8001800010b258050315603140c41c102c0e910650011704422503024800c1d540a100064079040503e10311409004620004603042c44d14007075920803170ba41c0c0119041154204080e40c44c0b43e1080c2c1d41100d41044003172900710004240c142c0481c0f04942882d51442220503480c00d40600d881d410340c8000030403054150f01c0c500546038900320344504c0c014698a200103640038403200c18840c0c09000200b0700e0351540301c01d03219107041c1700001890081c0e20b4864481da68424130300200c2d8071640015840e6200c3c0490703154060503c0001d000951380d01a03040300507102d039800808104540d4400318a000500502c884101e4031f5a200d28000b500c4000380d40c012149582c0d8000c02040e042e406004080940d03e1503a01c40e07058224603000c02450054081100d014076079612144074a00000303000900d541ca8501d100035a595991745034 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 116013444 1250 116012194 116012201
    0x80303010f0303110601050d0f060b061c0e06060102030301120c09060f15090e01060c02010e030102191205040b2d1005030705030c03062707030b06010801090506010c0b090c0306130501 81
    0x92074900c0d049040144241d5440400c8d15544c03d4200f04d000c15201c060b4500340740100680d03845281c1c008004540d00c032400b80b400d03a00c1d10000320b100c541800202c401486a982d43c080595201780541c02c2400103000301307901000010f82450103a445d04042c00d85d110603400440e0303501d40042d08001a0b030a428000060344402c01e800141c064500032011700c2c130300000310118640601841040001e0402001c05581c0b141160001100c0014021555003c01010712890301c010f211600e40420720443c0113850001c501d00c10540301d039801030b2358800c95030b594803061824039051401000350f84680000120000040d4a2000d1007410900240400d541c14501007501d4452968031480c40386d481003004a80030749010500542042c40c910043c0814885030403c04002140107140c4891446211030000c10b200380107005c035006110070f0302e070b083c00740e40c8401d01c41066800880b40710703000c07502e0920010300050340c160516a1096000003a0307001025050006818581d0036102e07541d080600c0b000400601a00b0311 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 116014694 1250 116013444 116013467
    0x120601020a031205070203070611031f030c03030503180d02060402090a1e02030717070e0a090b0603130c120b0a0c0201020310120206090d0b041b18020c07080303010f0303 75
    0x10801c034012550024118002480000c0703003641c0780c3d0081151a4000c009070b0b840d0540c49182800400e00c0314101045035081141c0942d89884a040c04c3c2001064545940d003d99800001c109070490554905948962024211070180b268044103050b402c1800d01c03181c0c0001e1707007590141c440c2c0c1c2054010855210405801d2149440c0303040601600e014002c580001c02001e010005607e1b43d55200c0d09440c40d0341c00742070000e141c0011200300030400354000d1640c08250012240089065203807030300308045030413140c00d040d003001c0100301080c0340750f0f2840c0b80444040d200e605902640d5403144d03004240081d4101007195404001c50910152210a0049980c640042c0c4021400d41c9030000c4290800c0d00315103d45540ca070810444581076480d450115200c0740c801510074480c0700105c0c42c01c0b259007001260251042501d40f6101e0f0344440e2201c4d00d00c000c607003103807125944010104400d00000d5116182c00d4109108220000814210500241d1300174810702c000c03948081c1c91410080c019a0703821 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 116015944 1250 116014694 116014697
    0x120a050f06030102090d06091406040b0118023108030f0c0105090a0201020703030f0212180f040c200708070801090302150c0406050c100501150f03050c04030204050c0f0f120601 78
    0x5015a4500d46c88018080078001d8000801042e20782c075900b0710054100300001030b000e80c1c1c001d0400f008240400070000c18100c80b48d204207440000e0154008508a00602c5403107054285800401c0c1e44803229107489030100d181d15a03200070150f82c1c51004520b16070084980031403081c40070840c0c00d08901c00b1b105090740024994003503c800c3c201640000e4466601d8080101417000c0081c50000361403003001032880b01c03040e04c0022561b84800190802c0f64100741000b0f036100d000c254248984500700350049440c103c0403901c070b51030f094021041003c50800d40c11905601e0344501c040000d81c102e02000750800900c40c00f0000a0800b480b402c00a04000040190b040305060308030510404522150444003142c000d490010b442d41c0b0030440690a00d0380701500300021504000010070880e441c0c240d421241409519007180d0ba060828040c1d050721422100a246100184410070140c10305822890380040003004003803600e8181000c0948541007a4164040e522002c120a00344090300c03011590844001d = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 116017194 1250 116015944 116015947
    0xf14040203030307050c03130609051f08061e09041b21120302040305012a14030a0911060d0203060a05060421020f280b09011d010203120a050f06030102 67
    0x54001c00d640e48000b8040f030742008000540c000b40b4400901c2959164009200400c1c1516983c0d80020204541c5009680c03060303201004140c2c11a0b20108980101107240c1c60701441951180d0400c1220400c280c500150340c0d240d610039811540d11004644c1c8998482d154101d00010001d200d81480da000c2d0b00900d56000500e041c41e08258000f02d10801c410764011540940c4403241101240a4001c1e030f400140b0543c2815030455408292014000e118003c5000d96250692201d2045801d0440c1180400001c5402c10108542409a4020303412550080d040020742c1d0001102081d590f904c40d8911000c5c1660103c1401100c0c07a1918042008020880700181010304000c40a02c02c031111990610b010815a041e110854448010b40031980c10001c058861400000d03070004440d0420340c90b016980080390340f0109440d016070702554010181a901c005005a04400f10004000403220041c10362005102129000c03007201c19035031044808030008030f404d0404980d400c05a804c080c00003403182c1d00 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 116018444 1250 116017194 116017201
    0x1603050601090c0516060f060e040302010207060b011e050306030708070b032d15030a02040204120606170705010809010b0a0303050c060702011a06092214070504030b01030803060609040608010f14 86
    0x41480c3c610120310f402c80c10001d514801007c3e004028003c2d98442d000c102d10420402c0245501940903180b8140150b205010025140d401141c1c020303035003400c6020014600701d0550f0300500c40c01c041d56003c907010302101e011646a0401c60b00c1c01c84103900c0351302e500b0030000800c001e0800c041a1030341c0b02401d000b02c082504006015245080704028480e29580c00880090900340d5000c0026080f080e4000e48115a03460300d0f60800840c8920700301c030079100b0740e0400d000090315012035420212404c8100000e408414100030045500c803802420244803907480742c41460103907032004001c1c00251320a1b201c7d19990f46000f4486030400a00034440419079140c00b22a04045954000300c068690b8210f80340c1e4bc0c1c9081100024140100301c2581d44034001403440d05484d0041907510040d0700082c161104d1a40d40d980c2602124240f040340401000036420380010070009140901071904440000e14207818a051000801c0454540c1c1d40b18120aa44032150464015610322801141001c0003000c05074078503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 116019694 1250 116018444 116018467
    0xb060d0e032503170c0d18020d05010b040e0f031b0f1203040201030507050a020c010e0315010b090f09151e13090b0112020105041202030a021903020a1d0610021603050601090c05 78
    0xa86c100071261292910900b4042244c8240d080a0391030380248604440f4106041081c000c1083da8130043c0124a0000c40781001e4100182500c0d5608080c8025494104541c1221094a8494910a695200f69214040e8244003031040700c810503403100742c0607100c5c40d10340001001c2d0740c400f40c1440d080c05001c229070303100950301140403042500300b070900c455407114900101f0303e40704050000240309046440081000003a00c2c00034403030b0980444080000b481080c040201341d20099070503c25003150020780c4c410780c0c24080da58883ca140014140c1d90400c805601040031488004c0e440203003680e85066a008001c404000e07a809800d50b05854a41001c03c0e80c00070b001881035000d401d1044c0020ba019008641d42040074840f003941c060f0049491042200364160a40d81358002244290703080400420b0190804280700310f20135681e078001200d41c49400c10304c5064403040650f1000c6000d20710b03211503140d000c101c407d4021071003a0f005001941c9800d40800485194035041030800a0810000b01e000 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 116020944 1250 116019694 116019697
    0x10504120b040311030a0804051b010203030a0f06030b0412030509010b0d06050a020d1509060501030203190b130c09090501080c1f0c050d080103150b060d0e032503170c 74
    0x1d40c407a6504540c0d40312400e040d500c030403200c50400c031503101c00542e241710180c2c0040c907940a103100d01d08548203481d0b080e2050400c01c102125160040c1d00910029668048a42008044407405c101c0041d44586a4890038425003003198203981e045412902e150625501d0321405520920050003003201d65142c0d0001102181d401c94003900807522000031a80000880d41100c10004400b5010040c14400c5005210748804901c0342c419010316051000400c0d5001e4000c49200b88854616600848094199280100b02c031403030b11a0400c501198401750b024142c0b1908000d80160f4a9808080340b5120040050700d00c140c01542d1103400040c140c245c2074840b803090400081c856080d4070700684130014201c1d02c0400c0e180014210344142e1420710103071508210450f068900035880c0503034900789440d012080d02c0c01c50200e190401d038100003015030b045e000c1d409a41405490388c1070b03914002d8552080b0600a8160550201c00081149144109504a1180c002c410b8000109540d686404900040706 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 116022194 1250 116020944 116020979
    0x120201080f0405060610050912070501180509070507150504060e010b0d1703060d05030301030c0f140a06080604020d0f05090114040309050108190e070e010b070b060f04060509010b0711010504 84
    0x107401b40e40b07034070600c80c1c0039200b078455000010f0710a10f85020702c016032a0b0f45e04413a00c10140822482510440403082407540c81c4181ca00c0981000d4031900d030000c0c111001d910100382a10b4400030300700d0418405a540c06442d01860259002240b0f80344d04190700c908481002110900c43e0f1886140c010000740c000f40705050301a00e15120380d03240d5a60710301082110010300760007802c9020000011042000340b00c0c1c00d600795001c0d40743d04803000b40c540c09030300d101c0b5406102c40c1c0c1d07200b03840810402101348141005980008003400150420724020020000d07150341e004040d0f400d648604c100302d031068092140008201107407442d91b0325030038142c5000e0008502400703024104031401001610b11940300701c0f0705009440d010010488003402c1a41280c43e0038050003502144a11203000150900000f81038501a0350040080c8d000c3d5100e9108200c220303680407038070580140c1c541200261940d07600348a18020107503840c0e215582d160303d141001c40d00c0d40070100941406010b00017030100a0508603642c40 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 116023444 1250 116022194 116022199
    0x403140a0201113f07050109050601050a0513090c08100b040b030c0105030a020a021f02090f060906040605030a0608030a0504090501050d0b0a0b0d0605150a0506070b060108041704120201080f04050606 88
    0x302c54480f5a25420308500d040e51070300e21341d400040d04a00700581580324101086c000c03c255441130762900b040041c044a18841c050340550f28031084a04012694014025544617600d0f400f5401d03074030b4041c0307400d0010202da40b00e180ca9170b07440d54035080c0c245400340d04070ba0300c8201c015110604011002030450b020240c80c0341354465001c11410038042c000c00c45684031a001040c0300b0074000c952503008029601a6401601031095030300b040d02c90341840002c3c0c82880d030005007600e042a00b020001c90b06038200a2a40d000151200c500042d034100034401400714010340d80e1150380d502c4c10100300710140d072011b0707201c14001e440210b4030320042000764500300d402c603020200c0410380c20309207400030703c0c0c900d40104041c200078030300810701540204600748003000982c00c1e0364880f0030560b29800c1100718040c1410240c40b45007c0700008440b584076040381a0700c140b00704030b014010043c001a240e021380180e041400002c96018102003590f0300880c1d8290301442c041d0302c0c0e03065464207a82c0ca50312a83d01600c25070 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 116024694 1250 116023444 116023513
    0x203040501021212161403010b0c010c0c020f0f01180303031b0c030e0108090c041b0207081c03090c080304090b09060f0d02010e0406080f0109030e030610060c03050403140a020111 79
    0x84401d104012080c248001b440d92103403a561a8180000b0a501c0098101d15560ae0074440c407c07660b01070781000703d120760003c0c0014402c14819081c016940d03184140d450401160940c69100d4411740c0c000c0c2009940a80d40c00150900d80105000080314005417440c2449600c3c02c848001a070b1240c01c40c5160f00084c03038985540d8484c0c48910b450101c4006856030303c141032049804142d07000c0d201443c01c019803903084448607591071750b207140c480386100d044142c040e4079003220400b400d00942201c0101441021100c600c9035031985140d0854101d078000540c819141c0c1000901d9281c405030f01c0c3d03080541203810000495031000081c02c019031111b0004d040c0300f00c51084000039941c2e0307403114004117500c9059806c8000000c0c2424000e040c102c00031008a05101e42800e140c0c01c0c0001e03a9449a140100c6a542043c100502561490354511044080280c10800400010307107600407084280001002040d403081180b0001d04001101e00d105625507010040780724403c041d403100d080895400b581e502c0c = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 116025944 1250 116024694 116024731
    0x5060405010e011a07031b0501200a090308160b0a02041d090312090c0a090b100c120305060415030506070905011d0d0f0203030301030302030409200f090d120203040501021212 77
    0xd440c040380354000301d100711f001c070181c01c0280801134001038200303109141103201400c01e03143c3c03002c440e01032010b507040010250202400003d2810000f003041524000b0110004051650b440c0f4202004544030382001c0d070040340070444490040806544a44411440016440c01040003642c900943c4035150139603d41502003100e500c014050060303001405404145d02e941c0f501e840340f01030085001414086c0240e07015003640b86116140c0c8028071035000080c0380003035074032603000c07809402d0107800c1c164080e42c2c0f0003100344039280004500d401103100f0b0340a4402d5103440d04010300a10f149601031070500038800c00d8822542d620409410101c0f0080703400c4840e41c1c040303003062840000c00b940e0003501444000300200502d41c00101801c01c031000c1c1c207400e00462960510100033320b84058022803600c0004c1c0030f03c003000690b54015008100e4090594410512252280c482c04c9101c5442507000d43c000041c01e1140356810300510070300d13642001c0341c50b2406c032014406000d2013500803c116a0300310380d840b05 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 116027194 1250 116025944 116025947
    0x1206060815160917030a080f010b070b070e060301121202060705040603090f12031b020102070203060105010807030b090103030e100305220804080304090b040e0f10020c0a05070905060405010e011a0703 88
    0x15010340480c030340040381340c0c154110700f540e40e40c4030051a20100d210280040ca08491070031709141a10303000f03000e05040616550b01c0c6192407002030070f40428011100c846051750745808001d14000c2c80300050b10006600f103801e0070b101031140d0481d8801107400420030000102e4100d4201d800b02c0d1200c2c940002d60800a0809040245480c400103069000301f4030b2b80350074ac9900d07812000c1990700701c0768110b03d00000004103908174030074548001e4264114000401007580200f0405503c80e400b030502081028401c00060031002098102b10041403036151803400501307000c2500e50720280b00381010004d900305000c551440c1c0b160046da14040b03440c0d403030940b020050020309a074010710a001c00c80e600e450302d500310341c0007404460000c0c60140340340403150640000002501e0030050303a42c80c00741040b0b94a1500c1c46000e0760014402d4481449034810120005808100e410000e011038031001459050044c20030007070b0b50741039101200346860903005001c007001882071042c210071034030031316540c0b41485d190 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 116028444 1250 116027194 116027207
    0x503060a03080a05310e0906010b0d06050d120207060306050306041106121003051c080a0e01110403150f0507021002070f02041e0608030c1e0709020301120606081516 73
    0x29400140d001d020030204614022520000303401484a0191130310380d06c50311500c0284000325804411540b143c40104083c1141c480140740e0314504200120b20b89884001107440341c1d04200302102c6a100c05803c281d401030b418440200039150926003408110300c0c3c040040e90700c60300500051308a00000800700400da4a100c12039004442d45440d4000c0b52400c1c05043c205210b1911040c1c400703015224001d00c211031042d03145030010260340c0303852900392101a0000c004048141054000d07659810313800b41c140344841c000c1c1008503c130340703280680006122000b0302965440c5200603c05401d10061002154021500326440180a1001612818a41071007075032403621010285d00185824041e001d40d40c00401204000c0103104c00520803c2d80c0c88903601d0b500d10802c5041003050700304c907651400c21000668060980c940400440f0758003902c1c0c0c1c101d10104da00c03c1c0c0c49401800c032440c034205d04100c45030081e8001441100b0140c84a030070054620820507000410f40807c807036214000c1102c040c00342c503 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 116029694 1250 116028444 116028457
    0x21c0b09070e0721090b04050708190213050709050a080706030e1c08070c021003020a0206090604030206070e0d0b0709031403120612011b020309031e07050d05070b0a020705100503060a03080a05 85
    0x6e0768100b00e0308142c14940d88a08090160210900a9124140081c0401c0c05103484590340941018403019060035080c00800c0040c211600700704690b50002010341e038040d8200d015111101c0075084107480d0040c090b04840400900c4a50b03030700034a80c1030300480c0c0c9071190490b8188017418454a01da550f91000c4a0300c00c210b0700001d41c480800410b051040354551302500e0404070799003c0714069241c60f880325503a644112402001030340b0940004514074030480e849041804050320703009107500166114032041740c00b1a00a40020b000c03600820034456600c00e2900004c1111001d1072408040b69081e1800450007802d041c000e9100500b80702041100354403100075820340a41d031800000c43c0b100025201da0240c2d082030300c24401c81e218840c4c010b00d01528241407460000081800700d140c0014400c0203c031132101030b80d050080900c0042d035121104020180c0382902d0340a40089820320003009164022080350504011007802002102d446528201c001c0d03d400440b900d85410307550104035000c2c0701c0d20 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 116030944 1250 116029694 116029703
    0x110706021303030801061d01120e010e0f0705011d0f012114010801060501021f140108060402011d0310090503090612090c010804120309021c0b09070e072109 69
    0x3595501c1c00c88450410094901c81d95445101d643daa00c000c454040c01c5060302a0b004000e00074004c4a90701510000f92100080c03100030500c0c0140e203118078215110340c030040382e0b1a0000f050045403000c040c820100506801d00b80000b952440f01b5003440c000e00040401400780070000b1200c006030b8041c5045150384010310420301807034000503894802030241400d100c0501ca0080340045000e40040c040c0905030354040c0e00130541c11940e610020020008420b040707002698a600801443d049601e00a01030105100203108a0406200041800e03a42005090b40c2540d2085601d10a903000f2404044031640d02c10081220b8026040542c01d51003100c1c3c1c00ca9000d40d0005181c00725500440241c0c1c401e03002201a0307181001100010b40b04507808075002000707105c252004400315030003944a02c04442c0080c0c03c44480c45278a08150081d846110801e4402032003480c204900080304101d034002401d480d244000b05130500c8003015102d5034110030006803030416854028038107556079210161042d0003 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 116032194 1250 116030944 116030947
    0x6050603120f0d06090605131509051612051308092b03020c0d170d0213060c140106030302070504090602090303181e06031b0d0e030d0b010c080d11070602 68
    0x30482c4481580d0082e58410440c1e42000300001d01041d291142c0f200303c81000d404250700100402a0034002d140d04400d407080340800d2607000c12584114071800740306400c2016401c01448480d640900070000e20b0180749040b0303041c441044010b2002c2000d07030a1882d440300c140c0b0780b10f8240342c1c001440d03c002100d0001a103161800d110302c00e80362030b0108002c0d080c040c0e001d803100b800700001482800110071a0143c60180005100000009181d00902180c040c1210042c2020b84a0403078411003c4107a010000007481400d0f00001e000c10301480c44004021400200304942c6190750280d180c903180c0c402c0c0c511441d41d81c64144d0a00004e03804030340617001d000341079a03035031a07034044d98455107240200328030f000d608801d20101d406501c1c4001c0e0b101a040c01032119003996288240069200e085580c079115002c0240f054100d1420280544031ba2317400e04401441d00c940081d000d40c4100c403100c0300c0440c100030102280001140171201140c520342d1180308080740b00b444809880380a4410540020311a41c030 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 116033444 1250 116032194 116032207
    0x604021c0501150c0c05060906130b0a090806040209010306051314070609060f0203070618060507121a010509060903070b030f091c0203120613020d0e060f090a0605060312 75
    0x310341d0180381a40c03c01940210341c030194000442d00c0e1440f1407001000d21a800c401400f076494418041c28600d00020440ca2a103500360401c686002d03425440313103a550001141062180d5000301182001d481d007a0b008012503d800d400140c0240810310010300644e0b5a1320110300700440103c00403100541003856002440038400820f540d809007445030f00f0000f51514030108002d40325141146226459034003d5003080d00c03d40b610300051158032101c014151010040d030b40011294001d10307201e00d0f001d07140da42e09040c1a100351416582642d02070569001c43d161a017555a0b00324055a2100d0000ea0b812a11801c410020902e4149541c00140004c0008000c1113034031401500c0c081c1c484c820600903034468142c2c40d00707405404a4803040040c0984c000f4000400800d0000196592213080140481542488048030b8400c90344410288001d19840d20130102c1725500400405400c030105240040651419425082d141c3e07980e020300502850b00e68002c11016541006030010245462845694911 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 116034694 1250 116033444 116033497
    0x40f0f0608071a0301060234320315040507031416060c020906130f05090a020910120b0403031e06090e0d0f1b06090c030203150105030307020405060402 67
    0x40881c0f142d4626212000346a00c40002840140c0b0304035500d0750000c00907540700841010a0348148885985442c43c00324114011482000b4488001c16404003007985c0001c504400d14410b00c01c2c1400030301e040c03030741907860b04240e28005a4038a000c0805a0710041a40302c52034103a0524844e07034006003400c0210910082024408036070310027044661401004155512401034032007008140f8065402040e01c0c0004000f8202000d800e0700a89001c04002010074550441c034049176015210b0628990000b0214401c42c01d0126580e0b4000d1070079200040500d140c280d0070000114602c000601043c884404541007500070f801c01c460070b42904c40740c1550301c1d402c0a2488010300192284020103401d01642d61600a004558420290070740c2da5000c412034a408000c0d2180c240c04c0000c00003590380d11034482e000c00d4540c0305a070302da43c0c4548500c40c01c05285004042c5052901d10110b01130140000040005950000c200c9000d1581a2008102680c0f0030000a00038018100d29403103441d910364401000a = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 116035944 1250 116034694 116034703
    0xa1808030115090905010501081302062a151302060702011e0302251106090109031505180721020406050d0b0403020f0d120515101d04020703020309040f0f0608 70
    0xc40c1951000f2000b95221504001c2d02c0007803150501003a80c00340420030034030840764001d140d82d0000e00014604544040c80708002c6070140c01000000350341c0c1c22280080c0c801071110340214154014003641c50b0500d1240c4c0011040f0841c4020310841001400c041164002c00e860a50b80b100064400c60001d400e02001e400395009500741131040c562400202503007c900342021034410341040c5050031065210080c81880e90060f01d1a5042c809450000000140c0521200071a00e03452a0045504d003400c0c0d0803600d406410802d600a941c028103001e010f200d00c041c01c900c4191070760f9141c01c040e200c401d00114001305025000725400881004822040c0890320801500440c0300c0d608a030011782540b0015600d6006c2c0e6104a00056841407000000690315080190071880c1c0a0740d15401c1181ea0000400c03015150a010f004141e090171030f810150340c01080c03450b850340c041d2030542c500800d941d4002e48074851a001c0c1c2d4419660359942114105466110828036100784c0c00c200865615592402c0d40d9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 116037194 1250 116035944 116035979
    0x8010311010503091b03070b0c0a021002060108060403081506031e010902090d06020c100e16060206040b160e040e070e0a06080d0804051603061d0f060a18080301 71
    0xa40800048003105944900e08030b078811502c076400740c82145030005064440c600c4d101c00c442c0d4948501c070701c08100180d0040081c01013130485001841e001d101841849059501101c1e0300d070940d0400401002504400701c0c201d40d00640c18030700740c815581c4107a1800d0302c100da2182d029030003410103c01c01441c2d8022040c8003500c20034222001a50b6030385c40d408007061f44185650300e81c00a5400e40c4420000d426900603040c01038030700302981c0c01030441c0801c180443e64030308164a51603000780060000c44075910b40c40e5001e40294405801985001d850b040b40d2020040c1240c02070004c0b101355401014820a14840c0c00700780100b0a00018488441c0140e448001d80500c2000031510b42c040307990541244900400c4030003450190803222884801580c034500c0c010f1041e500b90049060684032903a481281101661080c00700252007225070b00d0f81064002c860b6003129169002409908045a00054043d40085070900c08101e000c40741040c00c01d41d2010640003000307560080000b113061011440c10812 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 116038444 1250 116037194 116037203
    0x21060e0414060912070501090503030c190813030e04090b010801021909030210030b13050a0f050f2502030c07030c14150a05130302030307030905040c020a030206010506030a060e07080103 82
    0x8408076100502610b4140540e6031408981c481d101ca403210201060143c00014000c07400060280065241c840c00c0d03a0007254100c3d03150b0800603480000c0310000c4500f0386400c6c1343d450041007510302b4519088020045180143c140800c40c10340410340c0c1c1e140c2c0c2180c440700303a010503542c9140d6500d42d070107070203504400800c24003c255020a000c0e4903202d81c54a02c2102d400030040040c940403044150020002c40d000380d82c0152039010b107112114010b008140c001da600c02c00004c0d00c404882d010104460001e0282425540c00c1c1c0d00b4010f6078401d580306510ba500751230b061540c500040b000d040e841c0d44148aa236810310300558900005001701212140d04407001825804942000c800c00c120803942e0b644484688081c0c24030007035601b244584040c0c21390880003803ea118198032034001a2951300326403411000503440c19000e002c2800c8c140922844009140020982d8a005940294540d80c0c14001c00703014510110010302044502d822190051030394064482c0b03142080600100148000d02080c1c8 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 116039694 1250 116038444 116038463
    0x4020f01020d021f18111008010303080f0907090f050103060605150d020a0203090a03051f02090a0501050306130c02060f0702030f09062101080304180207021021060e04 74
    0x5903540080749918091856034090120078207910210003100e1213070743c00c0928040c1e0715045249030240c8041c20341c012500402d864041e40142c0400c008048a0f01541002041040c100400003c0c0e00300322003d80004415820404940c1c51b00700d903034500562584040703d0076080c401c4041c10040c0e154481c7e8166030041c0020300515885030705119100c601051500031141040005078040d101541c080c00a0313049520540346001c0c0b01400099031494560001e41e040d80290341004000000040718541440d91090103500300740b08000003445a42d49403040b981032050010010380c940d51060402c0220300e01d158020024140c0001000390746000c221202e010881503100426211400002aa82440d20304c1d03501c1441d1900c44410305c42e0607080300c10307100410403000240480351846862218043e02c03851004544031454200b00303000013047e600200760b117284100560345c00760700c1c2e8010342d2015285a081040318104071140c9281c0020300c60003a10929881d2850101d08440c1d803406181c02103020380c0d50344 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 116040944 1250 116039694 116039719
    0x6081203090607050a020705061308010b010305060a06120f02030408040503060702030909060d03120c0e0f040612030e0613030c0603050f0915070504030b0906011a040b0406050d020d02070302060402 87
    0x920512098030221031079070008000501080c842c0004054008482c8152200c0300e0b641c102103081c58200ca00d94401d448010301c000d0109150901c1048040d1800346402d12240c10328001103240242c0901483d42004100300500f03404ca010390308141081120100215501d1610741040005c0c0d0300140102880707800f8004c040f444144c40001640c91202c001000c680c86922094200130419900d180c0880500c880f8030100c2000082a105445490440c3d44440c81c9648100d0b080100b11041c088445d44518500340e82403050031188424090308550504006000034804030015440c1d0244103074800702504403060100410417810ba0400490b1a0768800380690784501032290a40907040320b410503030f58440e040a000001510b10b400303820030b0013030070304a103003d45036203c102c0003140440340c84101d94040c0004006214008009038821030a905650341040d0500e8001805441a0b03c14401001004110720040765001c0e030483d110300404960031581c8205614002c0d407a1413080701c080c2d1040800d00012b = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 116042194 1250 116040944 116040973
    0xc07080102090a051806090403090302060c0f160b070803131403070308010f030818010e040e1501050102010c1709120a035603070b0c0d0e0a060e03010b03030a030608 73
    0xa13030740ca00140401140c120740d180c80c107000590f68022310035010070050410010258580c203006050f00c80c7c501d80034003d408022000c1d2440c024070f1208019044465000800200c012201500d4481e680511700c07540c1d070380390350340241c850004040014080c00c5a840c81140b14500000081111a06c0794848072441c3c3e03a24640c11008004620002d451143c0801c10f400c0c0b444400c500c04c000d514014100407518200e9034020030300721520040071620030340c071410b1608143c50104d444503004001c24402400060440080104450740180300c040b00c540b101c40115010b0303c028060380c110364000800d1103840790864640100503024804c1c9005100140c52115143c058040151000c0451241449007501c40c0d81c440d1840350a80d2004042c03020320350805c04407030541d811302501d00100130024449488684000820b410802d4031890a0300b4040c0c00b40000c015034580f60070b424119041420140c044078000c802082c050040500110b074180000107060440c650140d0241d8241c4109a0849124210403042c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 116043444 1250 116042194 116042209
    0x105150105040e270a0b0109090203031b0a050a030302030f090d080112030c0c08030415090608040b04060207050d021621021210050f04030807021b04110c07080102090a05 75
    0x4055000900811003840b0343c540c2e10f00c100350400345804010184590215107500e13940404007101500d60800d0103101e003409820a0610f024101241c002c00c1800003d90010b9a280302e07d0041c221005c0700c2c2d064810794840c0c08e00414140030303000b01c2034413418001840c0040081d8821601c8050402d4a400072680c081000143d10f0308211160311801c60036402e10500340101811894220108007450002200141e0140c4000c0002c040e80001552214103000e2060400710100a1348800c00c8440c240070481e1903440b4108942041c1c00542041054403076090420280c130410364094024412a00841d00203030340003419040c0b000e01c880940d215151903664498068120a0401418448a00c0301001616090044003042a071640440e102e03a440d604881c000e4400403640401c00048182c20401815000f5003072950000d0729101600b007e60403080c1040d41041c1407192540955034848140100d005002c08445050807010101c0380c0340b603507032103409020f5407212182900a110860700022141404403 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 116044694 1250 116043444 116043481
    0xf100c0e030a2d0f2915060c0a0b06010f0f0207140102070806010e1f150e01260103061a010906140412150506010503090a0f020a03021206090105 64
    0x2005010711140ca074076119420f0907100e80341003800030f800310742201005003c0b020111442c4030b000c1c1240681001d003070401140140c414220403040350746451041410303821a0b80341d4041c0000354114842c1c405000400d440d0b011b44440c400461241802c510203109604041d64030a40c0241c1e21990b180600711f1049452142075503003080580c0c040e000a00115035000019400c9034410302c12100d02c5035540118514000302039000041f004001018000d2000e43c0c1280031604801e460402880c40c0e07e4015805d0340038524110036020401c1c5501c000300581c1c4620130000c2904c101c80c0310719000091855450890040038070044034694a0817290421200c038110714407105c083c05850b00944940307400c8056900701403030000c084c14070700d0411002c0750190002022a0f00d40b4014a544d200805040400c0011a003002e000a41801402c0c801c001042c20b0008142d40385591000707032060880894404110144081c2c1c0000b9409002c80c07015220740c0c0341c0058000e00c141c648030000d009a031115103411a0701d49120 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 116045944 1250 116044694 116044699
    0xa09180f050a0b030a020d3909230703110406020705130905120a02010f021611030601030213110708030108010c020715080103030818100b100216050f0307080f100c0e 73
    0x59030005458080100141d450068514908e420722422190380c48e00030f40311551301c000580b000c070132054001540121010307180300002000603816000c0c014080180c80110710071340342d20940004a2540c4a500020645000d402c90340341c49640742d2102a480e0300c428003800c0d0040704110721003001d41e031090080c010100d8001029002000ca10000c01949034810081081959220b03001001d5490791407005000350203180e0baa01501d22483d281c6003049144201c031a61180d0b00407001400036940e0042c0002d0101c0b401d010001da50645030b02648440e000e8408081e00400000c03000168400b0103410440d44215154242e801c0641c58842030022111010b10010011b00e112005200080c0150641f50308030100c2d040c100900b00c40481850325125850402585031500c445c4200c00a0600b101003144200490002e0201e05210144004403100741e8400d142c0b1880b091f00c14048980c5052003a9005000101c0544180c4100a90450398504c2c6400c0a43d420398644518011418400c9600c900f1a0800 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 116047194 1250 116045944 116045953
    0x106150512070c1a04052803080601180f0e22050601060e1206180d090e04120507020d110a06110a06091b0f08010608010603080a050a09180f050a0b03 66
    0x41c0101180d07010603000d000c03290205900403407480000320801d402d05c900d200780c0c0240741c0c501544d1407005080031150410000c180145504000080d002851140d003c2001c0c40c00d000004150707136898400190381da01840e58500344110100d0480d00c0c0541080c491900c84008980f80c0f40d81880340c6110700c0402c64080d089800c43c2c030042c800700780b02c0c00101c2091500181040301c107104225009041c00401e890028105441800ca100e040100740615000038042d03050504401d454580110041900248004c207072040b070f0140ca0760031501501c180d8030051f801425050310151b00780781050324414801040c0788110100040040c0340381c8902080ca051480000140c643c0941c071b0b40c9c41da005014440f00031250070107211290178904400c0c0c99880002c00440382c000400300e02d07040c610ba0071128540c00000490741045801d0002c680d2210440c0c01c040c0191070040c0d03840c40301e02030450f0034440681202107880300c0301c0810700407905a600302a040c464400d004001d40c0c0c640404000881c2c60466003d07406402 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 116048444 1250 116047194 116047201
    0x40e01050609090f060a0b0409022110060e04060308030f01080c090403140c150a090201120603050d050d06050405010603090201021c140d09020303070f0b010807060c200409050106150512 82
    0x54401342c0c100802074115600c140d100c2c6144445034005070807984c0c8403030340842e4080c00c000c409890f0740380000f4007039020201c0d424603001000d064851405040144841d0b010340740d41d651242d520040095410200094407400c01d82e0903d41c407000c0c2845480790502c2419004034a501d040d8a40341c1c040e540c0350f01d0b0a1401c003078030f800d0b0280741d8124103e4030307065000d0070030181403407514105002d01c5480742204c0050302c28000e00c00945240381c40010400c840f480e028090002945c0014000c00b00b8000b0304001c0d4a402c448180f400c050580384e082690401d0401000094070381c3c05030080000e8502c00d80039185071684140c00d064040444182c1c000000c1d4260400e44646004800180000e030b40440c001b04031281d10b600424550341c404402100c018010390f0200c42404510303920713a80907040c01e1000d81030350303407415900500300ca0f500c05c03002c0e2107402e84120400c0b002d02c0149501c410007402420500110f0001d05105008180e28400e20ba0360701e00c0da80c0180c41c0b045c03090080310511001d20100d25182d88 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 116049694 1250 116048444 116048461
    0x609091204120501090f030e04060801020310091107050a03080a140f0117071a0301090608070e0705030a0b1c0606060f0519030902060d060306060902090303030a0b0a0b0f040e0105060909 82
    0x15003002c151030656848002d00c0105007600d44d00041c01e40a900e03004604500c440610049920756444840141d20500900c0b55507003001050710112504080c01040e0000704031101e8805104001c4000e0281c030a031441c1e6010523800c2584140b0030444050104a40070350b01d02c00c012195402c98100d0f460103402c4005202c4c0d041c15016504c1d01940303240488858503111041150066000031111085500100040201901c20300505003c1c2c0360301d801034401646011607200d203172000071f045072007400300c08400100c01020710781c04040410001840c18280189801d845250803001c800c0035503000c0d0038200c010801c0d5004801000c0015442d41d02c4a16007001440b0100d940c91005500008044d11030529402599503940a09180004403400040051452504c4402c4035207550024107151b005010704605607902000360317540807000d00d0000c02d0080e821030000704a10010340040c121034102181d0b81400c03401034030152040e2080c05444604590300c803410040140919070311140c0c00b0050724001070b483d1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 116050944 1250 116049694 116049719
    0x3050a0b012115090510050402070b0109050402031c05191b0f15060609060e1905130e0d0c0b0603070503120f0d020f07060b01030e030a0509030a0b07080609091204 72
    0xe0180c090000744240c040c801c4a010340e02c40c4d40c00240240d031200c062143c03410005030124024501100c0843c41c0001e50740c3c2c0e12030098014401e0360861590382e000a4107648042c044c0001081c0d2080f1000c5034296000806842ca03084020b9018091035074251800c0340c14054070016840f0040c01c040d644034489103950b01c01c0c540c82090f104495a030381a40c418a80ca080900595000d840e03d61070708000c03282001001804c40c01c120924a100c0e005615682081c1a0103c1c41c1e0000e0f00c038151501031400d0039a041507400740580c41c005045901c12001e0400445034402d01c205104d0b84a03000541d04c0c1e85460b81010b540390b1650040307581c541c00c40150981034600400007801c0c180c1248240c3e90400d80c1b0125007000305c1c2c000192180b1150000100c42e01084414440c00c91f0f80745003420104501e60108168660700c0c014803681805010000841500d80d41d4100420b4806030390202c01d0300014034010740003d0001d90140d5216005904207000314038584c0003c1018103440e140079070b803181054038012100100c07 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 116052194 1250 116050944 116050997
    0x206040806040308010816050904080a0c020310020408010f06180c1806020714040e12030703060308040906030614040f0b070e060c0c011b0209010b03040204021306020604020103050a0b01 82
    0x1001040002003484080c08620b00c240c0c001c1c1c032085400d41c07412140504007402c503181071081781c0c11882c05100555906501d540c20581200c0c2450302d540304424207948112000401941c18400c0c1031803000030034219001402600e0209009200351118400d41a044e03d4139400b90321101c0d60841c50146600321a544000c3d180c03441403400103006d286101020500d5141da41145c00140c004400501c420707a07840254103810f0b0025101000a080c00c88816500c40e113490140682c1814004007044480d44a81c0114014603000781c0c000381d03910707510b09101c8000c0c485440112025401d100d00d0381100e500064440d4400c6400144852403081565501a55440b000f04503d040c0000744102e003650341c41d15006040003000c0c01004015110390b0000140214040919081c0c4006485c0d4110380180c9481090318111545030460b00d4a90300c8920004010b070284403404030001c1c8603030400041729680041c545c0e000d40d0003030720708000079116106140141c0d0310100c4500d000c01c0180c83c00c5017a100301f10000000303 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 116053444 1250 116052194 116052199
    0x312060301061205012c0c0d170a1206050303160b0421050307110601060906050d0906090510050606030105060307080601020a05071d09010203010621020409020a0302030109053102 79
    0x3202510f80215444a201c16842559560b41d11002d031900d03459a04801051220030b0000d0714120020b50304881d42d94007410010600406040e01050100020001d8001c022114401441d8440441040060141001c501e44140c854201400040d117424007108540c45004003032007100e2100500d80300c03601ca42c4000741c81201c1040c41a480001c003c0f189030090b03103480c01c0310768890b40d0302e05000e8402040e00d070000f00c00c0c0c0c001c1d80000004006075a0441d00380c104a4180741491307030b2109480c4221000400400c6405800c850074110368800708900450024801d481c1e09000f005039880741c006012890100b4029640c03c00c008201159046000d1981c260340040305204444486070f01c0d503102402c08400713521a29440c03880048800b881d40d2810401030344201141c00860541d85800801040011800980ea40c0001c040a0f104e0510049804441c0540500401590340c1c802d07c0078020000c3d803003480380d50002440c103000716100717100c03100030328400940c59401208491901c1840c060820043c40d070403603 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 116054694 1250 116053444 116053451
    0x9060402011409090c07020f0f0f010f200102040312090308070f1b14031203101e030b09060a050a0b0108060103020306011803120806010c0308010e04030c060213030c090e0312060301 80
    0x25561003030003e00c10b00a2245c0c1c680c48010620504c042e44012800c1180f003118483c000320aa03072507464145180420034600103241c0ca45072001618051003015403821b0945458829076540101500140304491160384994000d0b40b65840c200c80441c0c5034000240400420004400824841c15404004c0d50095440039500c104203040d0b00507903440755001d403007180762185587c070042c034061001d10034502e40c0701300b00c0d0f240d4030300303400c1c0c0318012440c1e80074648160b1404442079001c680350404140145d94411203002c401d0420360b5a041c1d8414046604002041c00c1c800040c00000450064158950f41078441040e03588520740150302030340006007214100100c48071444140030340054917000641c0102502040d07100e885c00000c00c0045e0040103c0d040c0034141050070f0000354000b50460440361410800c170000e40f40e5150803501c02e142004d0107001d441c000704007040b0300c13080500d82808503440b440405051942d1442141d081c2c400040c0d2149054109000c209110300b01010200e500850050001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 116055944 1250 116054694 116054707
    0x3021305061306031b0509120102040e09010905070501110616051c020c06011703071401020f04080610080d020c011809050408032202130903020717030a090e090604020114 75
    0x91100d030800c01e0b110b21245030351203042003c9601880364030340110500058204000d0f0712500130b00144622820303a03001e528866140b0002c03510030341c103032000f03484016104c10ba54105062103038042d01480c0342c1942e55001d00748001840d58011070079600400041c80150526666051a008441104a0b50754007480810000300c001c80750342c65903840001d000b000005882d041a00d15240c90620141c02540750038200c1c2088017250b2200105480d0080d62114098104003003a0041b180603028900e0000e01c0c06201080c04506a4008103000c0e1141e84400c900c8901c0c6a955092310ba51a416141d100c805a04045c801e80599441407900d00710b8160580349080d0000e40d248403030300803600100e809441c5080040b040c0041c0c201803a84241440010036130702c071904200c0d81c0010700808898520700102c5940d030b50745642054000e005040007850050748500341100242c3c0c003a03885e40e0003820420005121401d0100301e15101750380c2c45000c0c0310714000610680d640d990040d2184050115070f0b280c1c010050260 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 116057194 1250 116055944 116055949
    0x703020907020102070b060d0f020603090304030b0f011d060603070c14100506031b01080a0c110105090c04110301080c0909100c0f0e04090f1b080601091407020d0f03021305 76
    0x859005280701d030300040e07a400160a080b1200030001d01003520800d00310411401082039041c1300f44003e41c040f54207a9490702d420392618518030582c0d100402903c0100200b00c20b055846049904a80705101c40d100c240842580440c0c010b5411110158442014000310320034522548190400f28811003100503202c094890003458101001c0d00340c031069881d40f04200742414107011002188040c01d0030080c0300c040d8240086d01c4030200070b100540c1d0603541c41c00451911310400c10046040096402002242001d0014680f0307410003d82150207581411884000c0030300781e40860307049031280000780020510301e01c10400b08c01405040001644640b5481c081000c000d48188d02540103546c481c035041807403012001d4280c40281007054030541c85c11920501203a095803a00d00050b6012a044002104020280c40103148a8200aa481c41030398004124149158416a07080c5000303480b0612980e1819402c82c0e90b141a035000600050301c0700c0010782514066000f401440c00000b00302e0078078907100d101 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 116058444 1250 116057194 116057209
    0xd021f030f0e060a0b0604030f061802100f0e0a0506031305010207021206090d09030302030d0c05041701050406180c0b03100e04030c0605010b0405060901140d05040f050606010801030312020c070302 87
    0x800700540c0e041902131022a01161046084810b02640c4550a2a01e90b07101c22041c15440040500b9560b10361341c10542c00611002e55800c0300b54000c05201b0003030010348008106024140c0c19101003801560340da200d40c07034600d2061040f81d00081859145076100c003048100300e515000111050343d0203000400059550380d8030541560748a038028980c1e483c01f603681a02c2c1207c0100c1500901c1140c500a001007580802155080b00310104003040080c2c0c030071411a8680706a6100c1c0d02803407003020307603050aa101904114001e60081206101d0649401d01c0d07482c03000c2006800921004102c00b042044d01e2903e8055a4860b07854104e031010176541d52164250311104031400c4001541c00e4141e80d0402c40d41c0e1080724050001000c100f81000c1c140004603441e4410301d00c0361818402e2401900c4000c0c0b000030100c441a0f050903005000c141454a000d0608600408c400c5405014500018501d94400c0d000c040c126505607480303418284000215400035841003c1054032070040364070101c0543c07035038070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 116059694 1250 116058444 116058461
    0x90d0f0c0504021c1404080a0f0e09100608010f0f030320032107020f07050118030606080c1201020f0315040209120d09080c06040302090c0409090303060e060d021f030f 74
    0x40051605940e180c60300c800c0701c2443d444417008120b00b4050001141c1d01806513100e940302810000d28440c0a054181c0d1505080c40c802d660100b01401081446580348a8250450b20303140c80f0000682d89071240d0f03020040250182070303442d094100e41040071a00c240026041001c031308c100b900080b8486400241543e10458156602008102c2e40704510800000c400742d10807103030b1024100600309180d1158540c00244206c03410042c9400324907014000541d00d00c1e0003168440c0081150698404629031070305220085144242d449a9106181113018000c403003141e40000c00700380c40c2d56200d00002d81c0e580325001c1c40c1d40e0015070034441c035103140e115050a1120309140c00001c060b08e40f41d00b48028180203090700107c03826042890548100c0d101d0005890549504035118440b50307a4441841d04030f0b0140d60310000c034035070801d01b042e8103068259007c0700c190b0744050426142903403800300740115051550f40094001004581000a800140c400011031080ea440d01298884030101368200f40c401c5035 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 116060944 1250 116059694 116059717
    0xd02070302061e0907170c031912050307080c071e05061803091c11100513060806010c061109061318050601020d08091606050304060b06090d0f0c050402 67
    0x40c0c0078010401142508100d64034143c1c1c0a071403a074a803184505840395503601c9100c07030501c2c07070100c12803050905000c10b40721144040c0444010903501c1c2e003c1650301c2605a800e4070100c01a04010401c0c0b8402c400b01ca11406075034030781e02902d44331004030603e1a0b2151005841149510a58049502000041c058651300030002483c590a002c40d45500345140440980440d070f1041044e0342c0079407128000819003a40c00400102d1503a0f842c140202c4d81078090700e21541c00340d186042a00d030640c0100103000c191303603480a40340c0c0041e1140c1e410798044c0001d03510580442c1403681c00000140140e00085d5800e8075101c5801d0500b40d00f54041a402d07040016812151001c620041c803c9564206483d000c89411a006100c14181000040d4070b03030001004000801841800042010000300980752041d4401d40c6550030580e0348402c01001c0b0b82095a044034a5401e0681c00013552807c901516815440104207515043e81c81d42c2d00b02d03c0c10010001210110044900042e5a40c0d07148083c00949040 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 116062194 1250 116060944 116060953
    0x140a03020c010b120c01030b061b0d0e010206130f051606050912011103010b030907030f0303020306030f06270708010501091e05070903020d08070212101109060a03050c0d02070302 79
    0xda0000c2d080d501580320b8140a501d5100c198a4130440004001c2c0001d5000e080c0020b0880501d40440d646128032121144000110f0410701044c000008074200040003c3c1d0b910b1030851700d00701c012038582209441c1100e0001003070b000d06000c5070303008162500c0d55200704115144801c4200c0781d036468005550214020802c042440000c0b824100300707080046a0580007008102020361201c480c0740070600418000c81d10200020b2038030780003000a01c000d15080303a4480c05500703040c0b0b0010082d5100700d8503d40a401a000080359995001441c5802002c60800003d80030004c201146580000c030195000d1034400c0f058005060300c020710a40303010308620b8102044011120854108071011300241d10f0036140342000308541154040300b103c0a5035811100c0600d088914104400e07540919000654486144140c0d080d9240c0000707803065150715082c0090007400c1020340100d82d6070095850b1b80341c2102081013400c81c003234400c1d840650300c140301003421418004c02c9111303142203030413600702140940e10 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 116063444 1250 116062194 116062207
    0x308010510090b120601020a060603050a03030f020702010801061107031703041419021504030b0f040203070801140c0310080a060f060e130b06060f27011b0f03140a0302 74
    0x501c60440701210101d400c10301c151903e86441d1494030310401944424552103140418882da20910050f04016003102e01844090b1716400d00d90740740d4082c8041100402e150004444038a00680203458900c0d80584501c4026881e1245c280c1d11744000c0569440c041c0a911804000103144940c0b04502d00b0fa21440c1075100e03d003a1508000d0390480c4401031903154030020303904130044400c05603141d405034144c8440e0250601042c1a8240d03014a8000030714080c0079104100300b060b01415420b105500071011507a203199900c20890881d03e0344a03022544a02c068005602002040c00654001501905107441c0e607944010440c144002e202003103803a1a00d40c60081c2c40c800140c0034481c007424190400200701e040002c105000c94004103002072484440c100081c98035521801500c0c10002c0f0b04501a42d40c1e40c1c0007080320421840c500ca01c085401d010150381c0103951140c3c08640320040d07601089004400719458010b458403061004404015040d0f07030290390300814002600c00b110040e200541c8426 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 116064694 1250 116063444 116063449
    0x22050609070e090c1c060e0403021507020a0b090705061c050f060f0d1505071809090201080f1b1603030b0d03021c050d0c0207080d08041a070e04050403080105 70
    0x1101401010070424000541030880d42c0c0d029095070049100002c0c6a561001d01100e040d0407130900301c0c3c94181c4c0b4a4044000744240c03003025410300c558425400e451014542f4411800d17401c1040d40d5020050b40542510000983c000900716004103002080710903481c1c3d5640001e0f90769000c000d80c012403000e00ca03001404640c003070040c07035002601c02407030382c01e81d10f00000441ca848400c902481d1040c580003401e40180442c0c502c407206000b400d100140b005280000e800b41500890002c000c050f0348001c0e07000108203011781310f031030211503059547e51050340b40c418007540b0516019012240d0854019007030614000c84000400c034072501985061540244d0382806021030700120071030f9004a00d20090030740000c0e400705e0700b440402220300c07aa10b0f01110000c8116010b0081c45111034145152620b2545256000038041044400080c00c40d682c03602c45580481d4000000d6500402864611004c2410300c0302481180d588aa118505149022041c8001800342d0704140c0b015004510004d0040c805d03030 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 116065944 1250 116064694 116064709
    0x126070807060915050d09020609040606080106020708030f0405010e01090803040e0412110c040f0b03190b312d060b060703080a090302030910020f24070e220506 71
    0x41514282c2070b01d030f13002e072440301601c031b44a059a010501903481c4858011940c0c0c80050b11170055005e001000341c907881d6a80504508000e0051001612410741c1c005510000002290000c0020640541c01c0601d40801946c1e02c003954076085060101240000c00c403c8810400f0b0b20050002082c400f403107080a00b00810344c20041c5422100308544020a40d240800029070f107810b080095800103022490303100024001c000c00804540e0502a428a440d081c008049480c1c2c2c0f000d01440ea1b400807500d41c440358564490050001880c9003080140c40681070301030403460040a03000d0480c03518481d011041c4000600c603080381001d40818210b40560034001d441c80340c06220038003036032050301d8044549c070050102c2c1c500510125249483c2c0340d5200400d40700303205841c401c203405440b80d10384c280b2205c0045c5d112401d52038516050720070080700c02040040510007810000c041c0c1041c45203034031240402c42c1c0a4a00045490300000c0c143c0010800c142882d42c1c3c9010100c0554000581d800c001c070801080 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 116067194 1250 116065944 116065949
    0x60109050d0302060708100f080609010c0c121115010b070b090c06090411070501020a090812040506070b0a110f091306030206040e04060b030303040f05060a060b0301260708070609 79
    0x65a01000e001e00000d400048517a040000d0341001d203950f0340d44200121040c91284c0120b030605410610000c0c00d124006600350283d202c2600034005800c0042048501942da002e007d000c81c845100807000160140000344280c00080d02540c51407003880c1081c010109003a03202c80448e020000380a01030010384140306800080303030f4020b4140030080c4c03400107016004480ca41440340d603544280c88111104003080314002c640c0b1500175900c0d8110140d024107405500d1107804500d004040300324051081c1c44040317a0030b0702c0e4006c10b424140b00264448586a81d401800a0811075688200718200d000c0100a880ca9412030f80c0480c2d5200c020400303002420250380780f804038190400b50f09000507510300081d68280d840002c4400e40d0341d611400c180019003003e46400390140400400d100901005c100f00705c010034003c0040310b0003520342d003030941c04550581c1b10720041c1d884140014131001c001e154043d02c072001c1c01c506424079052000b2400c0d0506080d40c5c0803019951060074200129070b04041d45000 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 116068444 1250 116067194 116067199
    0x120b0f09010b030709020904090210110601140915010201150306020a0f09080316050a06111e07021e030304170d02070b0705030301050d031101090f02090a0204082107140606010905 79
    0xc202c0b55008a0743d582e62a00031000d800c2c0d00869200700070b4446900c509600c2d5002000e02640f1900100e0160912480300340c8280c003130080030000300d0300f9001c8840880401c60050140000c030b40d680c04145034a0209003100b5411952149903403e068400140d40102450240c3c0c00160303100540040030f04842c0080020300e00f4000045020484042c010058610200f0416250800c0e60003d03d40b00b42040d0078244014210751615403a01c01000ba4500540240c80c1000c4202150901090800301980100140254000100d00304e030500d140710299118848003000d0200d904180c2c6070103030703176414040c07414040c900e9a002405208406504101e0900200744c0240010719080b00c0707407a01d644a1005000d00c03030060303001c43c20120030507200b01d00340d942e80740d05440200944040c1780750840c807541d180d50003a44981709010104124028610031a001c4031001c03002405400508102d88c2000b010040406090000501054001c2052024440c01c1c0003100c601400b55885c03301e001400301042c6801650 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 116069694 1250 116068444 116068451
    0x4120806010215041b12050a02030111090f1306050301020d0b030d0e0114030601090f0801020304030f05161e0602030709080f060106050904021303150b01030b04050c0901050310120b0f0901 83
    0x40c00707071903c0610300e8006401030f005207503a003040c1010301d691050031b034403608a0032440c0b2400303810b100303000c105160a103108400a0002c0c880020411700580583d10300d0301e6002032400548020b5107820b00785601600580880800c2c1e0569400010313007241c0201162081194664181410501e018418240b82d41e00e1414800c400341c0d43c0d00c0000349100200c9078403100207980080450400c0e8020f10300503000707020310080d02d802e564446510034041c0d0000d46085001c03440324204051514002ca0695041d0f002d66504400404015201c042451090943c2401c1d600c2052080710042a030074002584184e8840c0c0721050702e103103018600c5d403a04039a41c0601c1401d8105800500c02c8a90100c21601080350880d00580c135003440c14030f50940b4100c2c85d03000800142e0720200f003501000c400e80103c0f01c3c1c5a005d0b00e08000c0c2020640c2031105a174400c40b445403003490204440c03421503010350051038200e01d0040c0120111034440300b90b1040b041e082d000680f00c88090808120380f2140c1600040d43c403080c803130003d0 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 116070944 1250 116069694 116069713
    0x315090e060a1404080d0e060115020d020604030f0302220308251a090f0106080c0a090e0606040908120a0912031811010302070501050a05040203010e190213060e041208060102 77
    0x40f0004a800707000140418000900c00d44d0744183c40e084504030b03840c084c00751250343d41c0d01d1448452040745040860050301450418200650001c00c0c0f0070321407a0503031134020015402c098220000e600000000340c10702265901c0700d03444000c0c00310702c07009948601d4030300d076a64845202c0113090200700440f0305002c800c415030301f070300060b207004082d00025403025208060792141d002c1c840c10268543c0c2c580c0c00640c0781800001d04050001400c111814090b00d0304460541c440c400307a8140c0d80d940c42d20142543c4030102041c4a818a640701c0e40b295402001514100702d004c04008450140c00d80d412005d69071100488428040c03807d10241b907075503050404205000c5109543c02508074100d40240002c0344c440c4030003509900035011600003c1c1c2c8400200058505a42180d0050030203480030b900030342c80c05403a0009900009111500d02a9084005101030441c0d420403c61080648198010360349031000020102d40c03000034540150712901050042e803462840003010780c800240f44504650124050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 116072194 1250 116070944 116070971
    0x210f0d021909120f20030d121d0307080310030804030303090605011202030607030b040f0c03060e0601021f05060f06070b06090f071b060617030d0507030218060a0315090e060a 77
    0x41c1d403c280c0d844802484500749400d260180690248003246c1c060080d68002caa83c6c81e40a40c1191148088030020421845445101190742622403442c3c2c045900c208015004101010040c50b800940325442e280c402c0e450307503146461608103610403408240ca92002d04100300302d90007010302500700c405031035030400c117142c001941e41d540141960081c540da800c3c006c000c0c1e8407035070420300b10f00a44100c20300c03414260041c0200100103620800108210060200740c5541c40030820064442140d2302c82900080080141030003010094030080d80a046110078906503291840136052544c0185c1c034070042840c1141c1070100240000b420b024102e07540404010f41a9044180c80c4040083d040700e0581d10380181c545100102041c0c0c101016100b84050908a4000000010034000b600d0403010312080d252030700290268040c40215000e11280d8000310b00d1030b0305214000e0709401407a454041078860403c09020320305103c0f9088616a00d0301e0701d150201e0440b003080410307000400400308212000b00e0400 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 116073444 1250 116072194 116072213
    0x2180a051f151205090f010f020c060115051306031a01111b0105070b13150c020d050901031409030414090402030a240c0203070201090503210f0d02190912 68
    0x400314851004800c0036407080c8120200c0c00464041071013002107042440b0126568004607008400d19030030450317481e4001d87c450098424800c200001001c050742000d074030300032401d50000d600c020803001f801040c104e440c82d030703982000424072a01c002804410700b800e01599017543c004141e049c460005070340d0701c16000c0010b015000b0402c2000c40700f410412040101c07001e22407100c1c090000c02491091150745145003808180080c82072640e9440155158000001d6510b503012342c1d801342c1c114410115009003d2801840000e41c14500050300c1c0410b01e509001441056800c2d94072948081824420b141c010140d010000704100c80d000190324107030340041d070303200520440205070911001450150282e0034000405013124548180311085c01c2810003503498005c6e81c03050740094400800040d640c100032505c154002d40c41744c94259401074000031001c080c2d102c06058003082404014603107800c0843d1025042d11880314004409042c011000104840c03070710f0304000b20079030038041d110300014144c80 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 116074694 1250 116073444 116073449
    0xb0307020a0b061c14060708010f090506040b09070905010f0908030409020a05070b04050604020405010b04120b04020604050315010e090f06070c060209090a05040b01090216021201060302180a051f 86
    0x400b0400c85581e5400071400d0382c0c19a00002402d0300099200354100f02000b28454000c08010701211030300c2c1e441400458800d03c080c401c1078040d160b150000c0c005502a9005154050b002510104899807014085154041c0c100c41e40301c0099a21081400300350381c0040d0024010301c1c14030301030030501e0412000300d48900c141e1185103041ca900040300005180a2001d403015507400840c0401c01d860b2034203105860304821202207115503e44000411259100020380301a54105543d2180b00e118607510002d2028015106aa0101084c4400900c540d030822010342c45060802213840c0652410500549042000c0c09105607074200c00c1e1218250440000c1003580444a841d1900e0412410704201340284603441c00c1c1c1e50003c10800030444c0008058200d58022486030070300a18507a03070f5655190132800f03185070040414100308481c4c00540780034400050140c2d00b0800010f00d0710b55a500040030310514101200140390300c9020070280c04224829154413200c84445801d00c0405409803003131080090 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 116075944 1250 116074694 116074703
    0x8071a0108061e130204020a1205060a030f121e020705091614070f06050a020c100b060417030408100c0210110a140c010c11071a03150303120c040f0b0307020a 70
    0x4000ba0010840b04d440d0382100d500540115901d00301c100c802840c0e400d100340801222402d00002c6031450405d500c2c40d00480387c001082c48a0000c0d10b940d5115000d490790124002c2050310001300c2809001c1d080305140c8004940c004051f6985080180400b003200107000d03407020b62481c0d800c45c40d829001602c1c0e11402042d0040c0aa65000c1481d10103030148000c100501440d240104005011301984d006052200c002d000710385000c2d5243c81c8802c00d03501c001402581042040c0001c03c04001c0e1203078650782c11000002a01e0906890304401481d050f00302981202480c0c03244a00031105405108107078007031001000912150180503604065131090400311400c120701d0764005c282d01d03000700c01a035510f490804000d1107a100d0158000b04100081c1400903400c1c0904107000507100e09140001a0a51070074040d03038215903170021441d01110031b41c0500d80d00b5000804c601000d00c035480014034840c80c02112801d41f40d50514641c0d40e4020320a4100c0c40d0301d80020028803103000d40004010b142c1c154030 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 116077194 1250 116075944 116076001
    0xa0801061505040e22050105041b0b0c100b030102160503090a1e18180b0103051b03120703021914060105090705071202010e0a050102041a0307090603020306010c08071a010806 77
    0x717001c03030440400b26500090402d52030300b4184010400c050800e194203060740e094021240e030b100c0000c00d40b98070498070400a03aa1000280b10100302482e0440359400c4802000181400c158903100c0100b02003d500807511381d00700050b0365175540752000d0018050140007003990910f08060400500d10900c50091480042d20403101e4071050a0980105130340b100303680c03040300000d0818a01311500002c00e02045806001d0404514114108016410134850000b00240760005401c441076226500044e03003a8110701270b01d10491070640c0d180000003005d80c03080710160319140700350741101d007814010303040948114820030602611a901909584400d40c0040144e01d000400c114140d00400c440b51850429008100c14081800419406441102c005040c0d15102d021030020009007484219080d00100304414001e0007200e00c2a030245900500604111030032124a45804149801103031003290000c1ea10303400c034403028111503096401044103000818190401c09203d0b480800f40500480c00e9980c1c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 116078444 1250 116077194 116077231
    0x90812100315090204020f04140108071d24030702100c030b06030f060f0307180e0d140a09050d0c0503190305300a021306020a03020d030e03090a0801061505040e 71
    0x850346d0450300380e201c01652151340c0300d0303807440800000448042ca441c08202074100180c10745015403140186140040d14a80075880c103c010040381040702c54070b07550710f49401e0b12200322601f0548015800392106030004d21111298011950076a05080c04540405050601070b031201d84544094030307004001007041800d1543c4036000318880d003581c581c4c0c5550511070b200002403040c1b01800d0440c42000c03507500501c520901c098000341c0d110100000d0500084080d1400080219400e010b0002145107141004803180c0da07000007010403901e5003094580030005031013002145000c101c1c3c05540f10596a80c03820a0f00e454070098a50b000340c00d03450502022807000c00746201e03d040c2c031071844201460f0131008941081c5617100c0c000e40101104280007244440040780c61400082c0c0081550340c1540241000201c0c5075044001d01550801c0425074841409201859078882c181400600854800065118600000701900d10195010300e01482030401003404903000f0b03001841d50180109140107204030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 116079694 1250 116078444 116078449
    0x3060509130c05040f020c0a08030106090806060a0e070c0c060203090a150e0f06040306090b01090507021b0f04090f0b07030f06050f09061507110a06030e0a0b09100908121003150902 80
    0x440d01f11810802e0182480c000c08103c000d001a505882d000d81e2220b0b155925107007910754030f440a5814039800320f80342c40c027007014034404501c080d4840c00515207044c5610180d901c0c1c41c4a1051600444003582012481d80c106050000101c0014803c541c40707400071305038800300544540fa03080e0b0060300515503520a40640e8a81c8012030b00116400102004102c0c2e4a091a0782d0b1090280103442c07038036003040c004c42c1e1b440748009001e81c00c100283d6001c0c05900025000c004450301c90046090f0055200c03642200030a51802440c8075050068201550718038045000178200c0e218a0f030ba4541040c0b6003030b000e02c40340d210000319400c40780e07003030703402003c2034480c400003920920320020040403040c4c0006902c0c040001000081029442c251880031a80380c5418082e010340b81004440b940951200a810000c02c51071020700f070f009880e010581d041560180c1701101505e0701c070a01590314000c00500680005142a20709074080451079040c0c055a045686801510903924010300b03001380c03900007210655 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 116080944 1250 116079694 116079697
    0x17030127060b04080105010311010201020408031b070905040305310b0c030c060702070303020d0201061d060424050f060c06010303080a020405060a0e0102010b12030a0f1e03060509130c05040f02 85
    0x30000540455101c1303588200030f5010b04824041151aa4206842c544641d40140251016200442c014600b008032080804c0e1301100002e15400c218429040000344010491040c207001d43d019591340f940d0303030210390a454840c1960111100346410400900c6681e03401c0ca06e079080641d40c0000c01c5d07036035400c004110903243d40140200ae0005000b140c0a1202e501d40014510b0100c070302c81e800b03490810f2149c040c2a4200d0704203126006116100072a035181022a03074040c0b59104200a000154804041d20703101c083c652506034124650030280c01c103006920b051f04103100d0b6028110780c4ca500d04141503440340c0e01c03079106200082c18840300e0000304a4469281d016200035080103400a610384807901c8008200c4000043c1180c095480d08941d0681070809201c0341e48404280c1d0015403910343d09640842d9110ba002d03010004020405c004145400440c010010009032260f0b00801d5503418a07041010640003d0006400e4900c0d800c0c22030005001c900c04a001c0350011100040c08142c40c1c05020041e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 116082194 1250 116080944 116080949
    0x70303020910020a0209070311040536010503011805030f0717030c0a03060b0a020a02090615030c070c0501020d0f1b0605090d020c0d0b04110105040506040b071703012706 75
    0x102c0c1c85018480011640041d8648500b4002c5581d002c5546031488150100c4e1814a00160300b01e000704824400b0341041c03048a043d000100303050301e50586041001c07401d031002c50060300703030071844610040145280c240500e642000502c1850030b0f50b004c0c03d03520141c0c0d91092070b40010040b040814501c00744078545500c0c1000034484092160341741707000a80085c41e0341c003012499002c01c0c5130200c0801c2203d0890261500c03024240c00400040c00107808108070702000810b603079840254250300021441c141c030050b42c0034048603000307a40c940300a89014072100c8102d420031f2381103500a254141da0254004000320340307000c01c0d04150042152003080707004402600c1e4009012603090209002d90145d002a5415002509a080d00c82c0035480c40c040210011000b54007401110186010070045a040d074106051000141042d518142c0c1c1da00114450750090b9000031a0204041095024000102d402440391400d16030454074642c105440e0403084030319410061008881ea88001c1d010100580c0110003 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 116083444 1250 116082194 116082199
    0x7030f080f04090b04050f060907080a0f020409061809020604170a021c06050108030a0c08031005030a390e060301110408010c020c06040b09240f03070e0a0501050d020703030209 78
    0x182c4580f686400d03409080c80248050007645041c00142c2c010b248001100e001ea503004041d0107890f243e000f0308480e044400351070b080801e503882130304442c107a035240700910040290300c00110f080c0380b504008000300d002c0102080c0609042c00c5150300140d407088111800d41308601000e402411414041d1071400c0c50015001b500415640d05c4045100400d00401c04c801d489003500340325503030b2603118003500ca0142d0314900700410710a00c03c8400060301c0901650b0700842a5145800f119500c40029141c004c0c1003405549000c000460a4000c100d44a010540c4d050001300f80c0d8911410341c0142003003042540b058203541e454003004074066640a4101c8442040542c0c0100d0b1101d07201c01d5007500a1902401230009403056040e00310460400000b910110303648071031503608190341d010074040321f050840f82c0302d02100403c04c803891a210148000e051503035103060440e40c40f80741182d40905200340341800c0c148124595141001785a0b4040215000741306000f10250320b85505280c150041c0c003405004e1035 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 116084694 1250 116083444 116083447
    0x1050901120f090b04020f010f0f3905060a1109090c09041a12010902030a0308040311070f05330a180e1b0309060411060d0c0306080c060c07030f080f 66
    0x1440501e1303000340e0189000b01c0d000c002c4840340000544001d01c0034200480030407090341038004018011074076102601e282c500048006c00500d000074040d4a02000d168210621790001c03403090080030800036501000007c0204162441d00d42042c20745e00480b041c0d10b115420040000381036034006401ea40c49840050814407c8802180941c5441d0100140d82070203850041c0d201101c0c42014000c0c100f880750050040c0aa200c40e81d2411102d00fa00284181d092141c010100c030540481001400020701c07415901d503072058240800c0140b0442c0281326541490180d0b209c8000014189c3c40340d140e001c96401c078a940e14009603500b5200245290100d0704507401d0808001208190501c0403441000007800040606000880d106d49501050b6541111a0301010014000920f5007642d070300c1800e40140380c10305001407407489100b0b41d0403a5084400194132000c1c10013070664104050640208222940c9091205000030103503a400a0b200c09000c60a00d0f00301142400030620480702920303108440b59 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 116085944 1250 116084694 116084711
    0x7110303150306070f12090204020712020a0c050105030708150102010e01020a0816050327010902090a090302062802030c04030203010603030807110705090c0703030608010c20010b01050901120f 85
    0x10074400100c0c220364080d0290700001201a03110b110941040c0400e0307241c070301c01283c90010f00002011108070403030b00280c0c01c20031ba40c045030350742240090200c0e1940c001d020204103441c2c035070b2102404c0d038804d605100c82842400703038080e00203100b40d512250410982d0f400940c1000101d01505032103800c1d032140d501c0003880280096001045601ca045559078400001d66400006c031040d100485200c0d8880c80c6028008a0a00b820040d140030484061b0010403400520340001e20b00c1841511142a40c03541ca4903201c04040e01407152951240d40c80c0011940285003030001901040940b00c0042c0c80c0b940080010a008540070a440c00f441d0041c0007040710580300d14019001d80e80c1500c0301c0d800300360700340002d20500500160f41800d80700003400103025034a4a00100a0b90380110808506044c1c40351780104041000340300e080c40004881e5681d00001007403040d0304000c440d1508201000d64101006251180d0300729040311b944d0030003071800c2420742c600105030303000418144180355015410059903 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 116087194 1250 116085944 116085961
    0xb0102210703020705060406050912010f051302010e1938030108160b0906030a0b0d0507050f0301090c0311031c050702040e0312010501030509120c0303070207121104020307110303 79
    0x2428201d842038003115081a21402004100d000b2841036070002a001c110f041c400341409001e101f8064951000429101421801407050b00d1040709c0c141c3d10021900c460a05641c0e20807084144488191034004460740c8a2261151030103850240d1981d01e00650b884070049924200349a181213096400300118800b500120b1425610a05c581020743c840e9040c0c2c6007542c80d105050380f04891120382c419240517512001d0160540000b04100f048503610000000c5a4a805103a2007042e8410b0001d00306040c1844200452101c940c03610303074001ea24000c1c0c40c0000071140c41209040d660000013507108a0f06481c0020f180640d250300112030262000c2c1400c840b2604034020f49445442140c0c14000400c1c40e041c0f455807409032032501203101c203a0000421240d4020b61003103811001c0c21046d550014130317400b441e040e994000309240030b10b40c0c000420081003613410710090700504108412004881c1d043d45031890052801040701e44140d80c00004166044d001d043d0312007c4281c030074162910b0385400d00703c = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 116088444 1250 116087194 116087197
    0x11a0f120402040605010906021b04060305011a0114070519021f0903170309030d0c052104060f0504020a03031202040e090c090106050c0703062301030c0306230402040b010221 77
    0x20700724021418400d0201700c1e507003c0c281071015685158010700e04e440b5003c03e04141507210f0b5001d0b41d081549c074080403021038028010b106040000341e90000500c0c125000042070302c5410348610603601c40c2480342000085d804603241203c0d06000c21018003c14103070001030b1030303c8075000420502c0041003c684500542181c00c40080328014a007041410070074116041c00d81c4401c680000440c1c00070800710852928617480320034258150315085042a4901c0c2141250345210420400f42500850402003040014025840000c060324402d212a082580c04540e44480c1c03400000d06100c06003c0d081c40840307490f0b0560b001015601d611059505200c04281c0d1642c0134a20000d00890100d070012030710034001c40495100300d0b42c6000038020035182d81c40c0c8a009040c410b50700407139141c0d9190070b1030152001d051582d01950045141c000182d2440c5004400c5901c408026070311681010000c00d0a00755240156a000f6010f8501040200c1d003000100e0070858050100489841807100e2096195100c60 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 116089694 1250 116088444 116088451
    0x6031a01050105070f3921020612150a090608010507030b1e03010608060115020d0f08060607060905070b0309010f05060307030f030909110d0c0302030708011a0f12 72
    0x12219190340c030360300119042d101d4014003500e840003440700000000c070400e08500301142c8126221150007941e015041c010318102c51404403286085c103044c4403800b840768034041102c1d80a00da801d01020950301040b114082c29150424101c9a103001134811640c0038100d0804420040c04528000d0311250508010b020300c0c000d000b036540c6000006012180640304902103640000c0c1464191151102240c110324510740085816540b03c0be80000c1c500820001d0b14060016002d01541003030003550300034544100e0355820302c00c003c58800c00c1c02109070040d030481d401c00c00c00c4d6500b5a4405841c1000701c003400c03844000421900c640b410000e982c40340340000d907015903180c4000b070000400101800041c2c4100b503800302e5150b00200810400a4000024408950b00c0703800c0400c0265680e0145000f04c614100e5a404103040000b200d10f402d580a115280c00e03203807203080031415030400e0b100c010440c030414010000c440080d1900e001c85410000190740703050b401244800c1d40d07010301052220f95000281c = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 116090944 1250 116089694 116089733
    0xc080d0e040203040c03110414180d050a050a0302181306060813020f041a03060118111603030e030c1e0c0307031203020304030e090109020307020d30020d0603 70
    0x1550842a50714042c021603005035003000e01d407844a82142c541681204111035000da2090742c0340000c1d019500c029101130720644c140045548012103603403070241003c203030391100300801c0b00800c28691100c0d0000c040d0380b1880f94600e030050301c9046100034010054500a1060b80c04244034501d075200d070342c8940240e000d9404036500d0f1520390320380e045007040c07654402c400203501a81c6100c10790040c0c102940000709040d0314100305641660b4410200f400c0c204281c00000301d40041500384c0e00000c1c40d501410000c0741e01b0384440e030300d49510450355900c80030242e0401010036448000ca040c075050b04005862120000f50151410041e10303c600b00307070003c2c804d00e800c12039008052140101d0728022a041c021241c20514032074243c450100c0440003940018011400d01061a040c0301440d00c43d80c1540d4040c1c004940d00580c0c0e828040c07406807a00c400741c920201006030700c40c0a001c0c0501540708054104903400e0446d5a400c0c148800c2c20080d00500c0801c024661500c8800801d1040b003001810310799081 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 116092194 1250 116090944 116090957
    0x204030b090c190504091e080a02060610140705120d0603020112020301080703031101021932090d030e03030a05071403040308030c090607060f060501030605060903060a0213030c080d 80
    0x62400b030110410f5040409100d40310b442100300003506081d081042c1103071203903080e450640c1e002d07900c0400c040c0b086442903c0d030420120704100c02680400050ba0802011900e000542c3c244c81c0d0001d11500480352820501503003c6008010440c0c02c0110458011002200540320300c00303015003000a01c0603220582c0080c0301c1c4940c056007085503208030ba050b108598007070140b00b0300b1510240e600107490700d078030481e541d820480004442001c0241e084107203400c0d50f401500503660302c010000c12040b1041003012019041011088a1810084503091a42510a00c10355403541c10156040c1c20114122074050200240d0114030503400310040c61100e01c101d1070210f5008041c907402d50b407409180401464002d040001c124190a54006440e0745000200050f1400b09640d5400003030720281109400556100c240074006036825020710310141030706641042c01d152102d0f001a0303072000081d002da294580e00003851071080c90183c03a51000303160012801ca00c0b456803806621350321380040e100840011030 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 116093444 1250 116092194 116092213
    0x2010f200609120f0406050306030a081c0506040209091609030b040b01030309060801060203040317040504020706200a0e090601030e0f030310090e0a02010e010912050c0f03010203092e0204030b09 86
    0x104030f01607400c540720700c803001c13414103041040c01d5560740e001404081e0306106040c003070700024006d0320003404d1909510749410030b002109000030f810784101500e0140700e94010701603030000303440b10324005501c00710412400f0010025580c085d568188103400143c40d100560040100384109250400c0c12a8071a6031465100766989808586181c001e000346001030700100810008a245070b0f07445400708001c03110b00c030316066580002030203d9001e00c1088034081d440c0d003038180440000c11511003022808084440c948143c0e107200800441007442d100340301d459990040313003082e486503200410001c83d65080343d018050200880d0742e280c00c12120b000d0003110459010880c00c14900500c5031418602004000f90846075006551300505850354604000c2c07041c800240c6104c440500044040c050006442140c1c60700703060003103541004010038040da00402c184043c9281c001100001120003240d120717021106601d440010036240360140c0f03180c50011034040184250790201c1401001204120385035100d = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 116094694 1250 116093444 116093473
    0x10c051b0d0f0c02031c0c050709050702030a03050c12130606080703020d02061806030705040303110303100512010e011d0f07290409020a0816140702010f200609 71
    0x4044008002503002c400308a00140100c280c14849071004040d42c040890038034403001515180e090741400134618030403500c188101400743c400942440d5000b409030b4503000c0c07000382d42c038400c0040400c01c1581e10000a11642155803c0c2c6000c511101203a29060400d81448929008800d1044e2142860a80c00007003412000600d0001c407036001d880c1c4c0d60102e217250200b00c619001141001000c0c40301d9400d8110769918a0000c501c0713017940b1b0300c9031a11a41142001040d0b9001508400c1c119441007061107221044828104100c80e0100d500100d181901c1c9115409400d210b181f601440d0300b800440f00500b170310714035274840340760044003214052021405200c0e46c400380b034440e045441891086250300d562140030810480b021080c41546440da40d00702141c101e0b441152107030300054052040c4081c1c240361449400c008800c0b464040307900650311501d644144540200241131090f00c2ca50104407074054000c56060101c03003045c518800006080b0310340c540d0300484501c0390501038503a6030030306d02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 116095944 1250 116094694 116094703
    0x21210030309030b13020907081b030c1b070806010b03041101020606100e0f060309150108030f0a0507030306030605101a120a0504031e0201150f05090a090201050c010c051b 76
    0xe0790036540d00420b10380345481d03000784031030064000340b44400141d0001c0056102c1114150083c1407a948031501403604804260f50b01d00444004105140308005101c0c3d01c65040c0f05460000c00e0040c010310101c203403680110b24084440c0c1c0403200a0280200003e903503070303810024612660207110154612441c001c0126102c000c2116015400f0003083d1503010301d18412640145880000740004c0300380210800010340c29042294071031034960198500c0842d0550103000c0c0360061400c1c40046007448016800b4608038080c80701d80600b000404201d0b041414820f400c00001190412410419400d0042000a0f02251030044403d00785082200034038229000c800c42d582144042c1e03196025031120803482000e4200503000f9800c00c0840b0741207441c040c043d02e08420001042d5000041d0108000e45180c1e41540c0d540c0c0b003d9681b04e0070860400682c3c50b5140c91940c0000154800140c2d03080354401a516400b03042d042c00c0c1c1561800c1340211081307400100502d6000520605508109441e005c080e0f5103 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 116097194 1250 116095944 116095949
    0xd11010f0905030a030e030c0106170c0904020904170f07140c06090d02090a09171306090e0708060a0801020c0703020a090203150904081c050f0a060806070e0a08070306021210 77
    0x2a500130032074481c145100b90f00190f82e4104403c140c038a040c1104d075000d030175103d9940000f5404892120004d0400030704102c03440c001b20b815601158245040c0d00003414240c0000c0c000341400ca019050b2801082c030002c00c5070000e10540c000342e904c1e64040e0401d14810706148080d00c510740309402012409180041c10f07101c5048006048100c008065400d003c2000406066421001d480b1125080011420208050001100a20907440b43c80680741c01c0000281c1c0c0e400001031069451092080c07103284050103a00c84403d0400320100e498040110365a01406d40c00504103520215442544030b40210303c000440707000312603500340b040d20340e54481c040f480181c94591400d0613610501d0814103160001e01d5006009803019420903203440b2160950321800966281d0b000e07038900c1040101201c414009400c021201e20410900e42803001e40743d95002c0c00b500c080240200303030464400b544c1d121200c0c030019084e00380039145019501c3c40c20350013a40041c0201e0032000103110000c0c10661001600504 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 116098444 1250 116097194 116097203
    0x3090509150a09090203030702030601031a0109050702102a02060108010f1a040903020307060609050f0106022a131d1903090501050a030b12074202010e0d11010f09 72
    0xb801840d0900c4500100742a800482e0140020b00005003d40e0781404240d000794018044141e104001c1101d4451080c0c0503040f00900500e000c00340240076a00080c0030790b000c148901c00050b42004014420301914006a00c0a40e01c000c15420300d07052980410a14104c9021800901c48000a140b4440660b8200c10108038040318074103d180282c0b0303103600012030860190042d01e1800303103180c03600c200f62201600702c200419194024403d0140150395a50700401b403e01c00360507a0400041e5006100c03101030b010062440080c0c2c0c08002543e5040300c190007104c01d04d45e04110000c076035000d1415260005a043d070450080400c1c504000e0801cad2301003c10300364141d5980044900307020054869421610003601010340d134005103515a02c40b41d940f519408038580c014403030140341942c0910240048001c44500081d2840d0605000c807291660081800300351810150025248004034014038002070000887d114000030740c422150022031030300150f82c2c0c0381d0007400ba2941903606941900c0004070000c2c03 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 116099694 1250 116098444 116098459
    0x1120503031303031104060507030207050d0b040b220c031406190c0203074e030504080c0a0f110102030301060f0f11250503070503061b04120309050915 67
    0x200e031081e241c2c0000c0d24041c440d050010703c940c089030030240260416040782c2c0c08644009824000e040c0c040140304020401110b40407464040b0390303a08140201c02600c02008900000301150a240c050148010718203d07108040d800c01c81203090069003080148010784841044c00e2420360507039004500980700795108016640d403a18006a0fa030011701040070200214041440300400003003522200403080042005580f0904584c04181e00704080c10380c4500b1100c0c803041085040800c030f00c40c905032015020f030600140559907400e042c01c582c4661270a002c21402940aa0020000700390b90a0700080d00586400072808803810069960784000c0c0540004030300c940052800d0b940c8141100700748504503180c80c415007114041c5030b41c40d142990340d900842014041200450345401d0180304000c020440007014100d2415020a4036000701400180150764591800e02000d1004401c40e0010210341d40c415030012440c0c2001003400e4141e00031140304003a044041000801d00c1c0b17109240d2214000c2641c0c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 116100944 1250 116099694 116099701
    0x30b09150c0a0201090f080a0e040516180302090c0304031b0803010509040510060f17070506030c0f041805010608060f09070f030f0203100302151213140d030f050112050303 76
    0x80c4074a40000d07944900b159203030307091200041c0c1185001c0401e103101d54421500c8400f080742c0a420401403c02c034600441c6444200704200c10005141a5145401d040c07544089542240b00c503000103d58001035088110001800440c4902400440c843c9000c2c3e503031441198180654810388401803e006000340d40300703000600040c54280440c90304188900300300d0709107400604014003920500e80c404841003001c04801c0100301001440308030300b00c82041c09041c5041c24030380050820300014100044803000440d5003030f0949154000ca4003c2c00700c00914094100040f00b1080c0603183c00d0142d03600084a9102203241c03400d291510401440703008245015a50307a20200b12003045045007018100740e21b40a514450a15500c0198001d1000c0391286111606500612009000041c03180050600030040d10004c0f0b00e1100000da0040d654003003401c4001c54605018540383c014a10101e458020503060300c2c170742900340d4041d510352070382c000d012711150f0303600c3d00f44113030880d040000500300b5003041000 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 116102194 1250 116100944 116100961
    0x3071a010f15090302090412030518060f1305030c070f090608060f0601030b060a0804020a080d170c39060c0406050306040608070608090f060105011b150510030b0915 73
    0x142c80e11280c80340f07002005540c0e02e800142c031140082c0c5003079459951407644018039907854003500da8080d41c0440e400210640c00e05640e81d50f08402003000f01142d00240110351000d075021b03202140d031034000b406c6a031100320000e0015114011032007070301440103104c00000350108045c0203010460707008170080d003030594401705501700007079005207014105a034611900d80030b5900d160203080e92420342d82e200c503480c0c0382c11320601000000741e42004415500908c01082d166a100c0100301000d0347d5104c03142c1050319485c4001c0e409005003041e241044100b00944182880c80d18449a003200410385e10309148110030802c43d1300c41005440c9030111884c10003040c00341070700902c021500001e0240c400112907940f14a85400d14016410041c0095600710500201500130001c1d040d6201c240c40192100d940340c10000390800310b404d031030030040c2d030b80300810380b030900ca03110000303155101888000740200e2400309801e01c0b40c408180000c0343c68404104c0032a05602d070000340040c050000c0d10200c1c2d8203446850710b = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 116103444 1250 116102194 116102219
    0x280e061503100e0a020c060c090d030c050c0303040314061b1608090405070305040314040f05120307050610080d0503060f040213080307060902010e0d1101120209030f03071a010f 78
    0x303010002410384800041d0b04a003840304504c55103040400680ba0743c804024242000b40c0036010f0540d201080c40348000c02d0f503d46080300d95955242c14800c04090003858040e0074060700080490781800b02040020030b010b5900d580c000030011100903100c1c1c0d41d44040c10049105c83c1801001c0c0d840e0340500608061010a181d044485401495580d0a001c46000000d0035114205c89a400194a17002440105904411f41c04060b81d0381603e050f007042d062021100c04400107210b25032181d2440701880400030010f2003103428503600002902c10910b01040001c0a010803881010000e10a0172140202c10b44990156402818010103a5200b030f0500000c10019400c0010340420a0040583c0060002010801841d040b0700c42d000110380a0140d00000d001000b0261425015a1410356901d0004965100c2c41c01c42d40802d003040c5407800c2a0074402c00c028064000220381520070b0241100c40903000102030a42d031481002c48602e03080c410122602c040b8403e10951040d949032030814044040082c6 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 116104694 1250 116103444 116103451
    0x90301090203030f040f0e041e02060c010207110a08031e07030e0a08010501050414091f18030804021002151b0d0501330c061505280e061503 62
    0x50011822a800c0d40019040d584445451800381c90005000c0000d251050141e030001c041c068100030013072a140d221001281602d4013001c1c0807a40385407210085607106820f80c1d07218003100c402151141018640180744c0d100030034925100700d408500c0020544000401c5a0b0303602c1d02c3c40c4070151100441d18012005400801c0124103200317401c010801c00f40c84510300d14000301480000420b1a500d464140021034250520350f441c00040b40041201030b15001528100f94214001d500030494216001c09004010f440600380107400c40030a0001807540c042d5900340200d001b11505114000062020780e524203400c0e0010131118940c8001a071694003050000460f441107000e958500008482250100c3c0e0090300911a034030310200c080d4111541c80713214607164204801d80024200c02c4107101030144030341418010801c2e5100c0380726107100e24900005038000c00e40580303043c14050454003410a41d500540c10b4005803030701140c0002d0402510080c20f400b955014080308450480c16000006940c0005c = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 116105944 1250 116104694 116104699
    0x8161e0902030c0d0522030e0a0e0a020a1701150c0312020d0905010c08240d0506090a02180601050d09080c07150f05031504050612030a02030a17090601030809 70
    0x14a00103030140503800194854031507041c0c016903e141c1e50b0004000c0325400b800c80c511051620440b21503900030711411121058150500e8420b05103c07800240c0005510b80203100c1c862880420300813256017640140c05244600d031941c5c0032865446000d01d455078403d204032505244980038441700d041c041c81000040c03c0c0207151155207900d030481103500b60b038480c06600a80d9660345840c01c09215082c8103111400c4d48610700010641418000003002481c166500e209402004000000076030742d40c150b01d8881c503807000039103007646000000c242d01c41004640c02e900030024040104942e070600c85110b0f201d030605845981c03c00e441d0090400040c00400e030100ca4240c400c0000c00c21490f01046810f0040400469144484c0044440202109450400c08007444404d1041c0810303003540500c881c0c6016401d440001e402c1ea240300c00900c0e45049884002c015010001d608a1074940c0132006200c0703071441c1d41b00e2022461a141c0108500c0130101c509607180d03004a0300510004965400504080100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 116107194 1250 116105944 116105999
    0x2306100e0d0f0b0103020a0b120a020a0309020405010305060a05010807062a140a140c0303090d060b0a0306060302150307020c120c10090f120f03080406180503070209010816 76
    0x10b0356540c5801d0740189401ea0311880314900420851415036903001c0a4003050101c00d0600548101480c840f10700948011403154003c500c02c0741e124803d81c411100036070020420701c04d41d40d690410302d03181c00c020ba541018607070802002050654000541c0b43c02ca521b00d940300c5683c1c0c090401025510b13402504000200449500d44402007100c030301c0c0111940d21494083c0c00000c03520315280350003119162040303402c0d03003014400116590b404030580340c4110b03055651180100c2c080c40e100d40101800d40c002e9502c142010008818000682c2c0b01d4810b42c0c1c0300f074032080740c007207074000305848540002c4920300016802240810707010708011041440c0c2c10090401c07101d5587c1c86900284014203122001d400040c100c040412540c0c41c2c080d17410008140600d4200d203003042507214200e00c0d41c041240030b0140701505001c1010072109034040c2c41d9006001071a24809081789c41c09644a5100321002d078801c03d82ca40c0042600040814080180c840d0100319000b0180307000c2c0300a91100a4110903600e400d80c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 116108444 1250 116107194 116107219
    0x10c0b040305270415050a030f050f0706050310080a1205090f0a090207020f04270503130f05121b0f0402091201060807080d0203040306020306060d0f2306100e 70
    0x42e9100c20040b500e20440b841001070f050181030004580c030185032500c2c42c08040404000c039071107140014003626040364003100202d695040030340c0343c50350009040415100720b000c00115958090091030154080b6010405070964401c0d21540c0c2c3e081d031517400303041c11180c4a80030b2034141c00b072001000c42c5040540850381081a2000007091101c02e9407240250306e800040d280118905403500101c09002200c0400855034000030a405070401c0c4005254810704095545007031040800c01d40f20342d8030040301c2105400d511046401e0802c01c0ca0b100c0d09019071800711070284401c0000c640481302141c0e50011054612800007040050100300a203150029030130440780c1e05a45640c065010f01002450011035030074582600c582c40d0003d16800043e00d60002e00030f101520340c2c0401101c00b180d03000300e80541c5a48a2030000307602449503c45500310745140c416044904002d5800803107023150700d0410322442078200440c4245554044480319070000650180c0b0324054000d42145000d010040e140304540d16 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 116109694 1250 116108444 116108467
    0xe03010b090a151a040302060913060f090e0102032e080604060504110108091f110d06080606030c060f0a17090703060f020a080601030b01120906051603060302010c0b040305 76
    0x110140d4544031500c0c0c84003000b20305400ea040100700100302070f0055445151213100d1820a5001c0d90200900c02c00000a00745981c0d9151038a42e0846481614100881c81d03031000e0340d140c0c4a6140c45828045130900402d00349200c810b00c2624403800c180000242c590100001c445c49441c0c0f80d00d080a2401c05481c1c000c6610001080380910491080c500000c55040904007105501d00e00d40d006410031560504200304440d0210b040c0c40b51183c102d1418071030700355070184200901070200000c0008070012541d0b060300240d0350008012181690180d48440d2500418551540c001c0048550008010082d4030100b5800c0e1009102c0c91203039261050850303095a00708150345500703950740105507104401c180705000040c85004240c4800786000c6103451a2a40d0142004500a04481c10b05030744059002141e4051100020041d00710f0f1301c2002814070314070b031946c000c0c50281c83e08910a0269811200e10900a104020070f403901612440c280724801e42d95044444001402141041024001c901024 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 116110944 1250 116109694 116109709
    0x10806070e0f2e0e0a080106050a060e04110706090b010510050703110f0a030207090c030504020906091308030c1b060603070b0a090308121608060a0504020d020903031809160e010e03010b 82
    0x441030ba03a41100440c000c4040140044046d040045c05900d0800200f0103903403403c9a01c2c040f01c416040031540440c01200090080135100c040151000e0005580d10800c6401e510154285102c3c0c02075081030390301d5400707211b0b40001c078258010200e4820860240440e0180d400940310b00001c000329009166800785003400c025078840214050380c4848018000004d80740030f05030b0660780c10f01d0208110724050300004e07c090000b03890f80740034003c00d00200b039014008956081c2520340003110b0030781d6030070400742ca000039920035407101800c144400e41d9209015004206680a080300600030f0203200d05200090f0441c0d804ac1060006120582f9030003c0010800005000d00c044060007055075450f00c1c006140b0390300e22002000003041031920402c51541e80e4120030409a400a840068440c000c522603140240700b4400d0107680342c17201144105000c0300c041c5c01c0720240e40050750036a00ca91128540e00c1e00805680c0618400300d80100b83e030b21101d51040d407034540c0c80d130401000400c5505100c00401d950 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 116112194 1250 116110944 116111029
    0x7080405030d05030712021c0903050d0c1805060c0a11011803030909140402010906031a130e010e030a0903020d08190207080105090708060606210f010806070e0f 71
    0x41079020040017800d94020612a103803d111b21000d42c54110118017402c0e9a280741e60140205598688001050600c41c01c1501c1441c5c0c0d03001070030071004102000142122408420802510384030110202d0542026401d0358184a103840041030100346a41d40c1d01d81c2e441201d50814100710380181002151944078050100450294907041d502c0c50a280840307042d105141800b0415107404400e110042c0da101c41141e0844150b80b03400a0060000d8610155043c0d15140c0e0710b82c040c0b40ca104a0745c21144aa0140200701d420500070070000013030307041450f01c90007000740306000b0a0400d101000981003001261040c50700c07072942146041c8004884400c00c0c558640008010f034850238041c002900248285600446400001c0034100d281c6660103903a041d0050495000303960100311101c4070360380706d5402ca000000c400201081450842200003e1001c04d1042641d64424000402c2c49140968400020304078040c02050303002c103000d01400090602441e006074180031035641c851043c0701902c0580d06 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 116113444 1250 116112194 116112197
    0xa0305030906060109061e0e030a0606051309081c020f030a020a030509030415110109020d080a030b0906060304110312030a090312020a0203040e04060204032004051503030f07080405030d 82
    0x40300d04007a00340a1a198000f800c0b40c1c1444082081030040071340110011031040000c150800f02000000001c4a60078800c10006405100341451a030811442e034025005503003081c0d0700302c03807a0001e501d13004d07003961144000641610700c01c0103000003980d04400f580307140d003c050070013503d03101d0b602c0d9030518143e0086445405e10b0b68003280800003590316010341500074003800700440c00c00d401c08074188518501800070300140615180c804282440a4014075403d5070001c007600d0460260b410301c1949a4410302011000030302c0e02160f07544501d80182ca9500071540549040d04690319555100c2c070b0301c1411031070071b60f0500c50403400f0710101804200561150600d4200490b08101c90f00d80a803003001c0c0140211f201d05c1c01484447c070081d03400002d4030203d40302020703d108070340c075641040d030000e01c11070304090501082008500d071008283c02d85020012010784041003182d03940204032000074150254250f050704200007200103403440d07101801c45140030b01a090700c0c00d03588500280c9018441c050460 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 116114694 1250 116113444 116113447
    0xa050d15170609070e15190303050403030f020105010308090108130f061514030309090c04080303010806010512010e0601051e0414091c0206190914010603050f011a06070f050a0305 79
    0x101540da041c0107480d08810640024a00c1e030781004100008031200606ca03603440565407102c0a101d98030b0407a0781c0c0900d004e8a407504c8000d40c490a000340564000c0c00143c0202e80b00c0c1802c0d05686105205180c101d0b034010104908116070b2000440300d080001d015459001d04200040c0d02085503000115100c80c81780070300085e95820404c0e01001c401c5c0e242c0c070042003580c512594000b43e48010085544030a030480d4041c1880da20200d054200e4003860300b200c9080d20011002191a800004009058401c100c960100240314400d01900746e4042120030749441d0004c400401550405400908a4450640030808082d03810400304080340c80746491a080741040d0340900010440034040c1d941c0000c03520001e96103d280280d8080e68484000d48043c2078aa030714990090701d900c583d4041c80009502c001c07482c1e240d01080004c603020309280c0c04241c178240203650440e410042d05104072442010b47c614403902000c180d0017000300701d402082c000e9880c5800d44a030080028428031408690510a46030701d0b = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 116115944 1250 116114694 116114729
    0x3031b0c190e04050712030f1704051b03010f02070305070209150306040f030315080f0f010218130e0109050a110a140906010903021e010210060501050a050d15 70
    0x2840c1203186840140104516140c24146820180080d0150380194040b00c165403030714601285000309640c403140b45e0403440c1c0029030805600032011103076050b40c1c3c1e45241044800700560240c4041c161b030014840d90080e026003c1801041000000c041402030001604030308a484a03005c2e03030b004001c1200021030000d050720443c5806249242c101400e40149040b003075505020941d902006000078145e081200d400c441054800e81000c84c0180c510780c1030b65140c560300c84c02e066403410040c03034521041c05010000740202e0014820384002d00d5900c1031043e2880a0001071141d1026520741100010340c40d6601c00c22003850901989100a20910051000c000241000b400c007602c20724015105118008007040f001c02c00640c14030641340300710f5912083c0c0c0c0740c502c01a201c0e0032032644002e40150400419000c0e94110700d1a00b41c070001d00380c00b90380c81006844190380454807a401010701041d01401044603651040020f0b107250800d021000031942071004481ca0aa82e060b44901c103050000e40c10b5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 116117194 1250 116115944 116115997
    0xb061308100c090b180d120201051308030601180503062502030c03030127050c1804050103050d0c031713060c08060a051201020418020a030c0912150b0303 68
    0x1400034540e031040c10840e039103480300010088203540c130031840301303410224013041c0714031071104080b81a0b100145a151008801d2070302e900503070750000313481c1c000d9441c0070002520880741544100300c0d143d03c20a000d00d15686c4000640712480e08200c0078040b00c5003940d0201d601e460401c0740c24000c0ca034070303901c962500000307841c036503040800044074500310341040c00041240d2100000340c03410359451420603e0790120840d02c0503175815500344000413160800013401103080c03400005240114502494409c45480e4009100170317228281b100a0150703211410a1701c2141c417030180400118443d190444024000191030009007100340d80d5075102e5501d04083c1400c0040d207114075505400340c3d0030f0082181c941a0009890001c6034403c0c0c1c0e02030081c000d00e540c2050030a50485006e84511841061800030300d00d4814001d4100c801c1000110785410210b1805600070202c020848503c1310400d100c090240d69180b0040c2c00c03090754407840781c0c1c40d8402c2100300d0f50240b018020b0080c0045040400349041000d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 116118444 1250 116117194 116117203
    0x2e090906141308030403031e020a08040606060504030203100c03140f070806040603120e03010b04060b070209011d24100e0102060115020a02060903070b03010b0d06050102012307030b061308 83
    0x9524850164102c2000050452020f5a90058050400080c0040c1c4002a60003100c030b84003049100324400a60319441d10f8100841d54021070103008104412030700c0e04c02c01d85040c4541d002c042c0d41580518903200440801d5000801940c0c19840d002c02c100c10300c1480c0c101e1010050b142c00c00080e41407010030001310790120b41580d00610407502403008911350780754843c0c15907408400c84204400c90030340c078140c0d0310b00350420022858041c000b040205e40e00d41202d030040e04601c008a104003154000050001d01c5610746010441848480c030700151142c038840d8960001525a0f0005600600c0448090b541d942101842015036030b04e41c2d225040144000a080c040b0503040500e0309045003240c0315115900140c3c00c40c3c540c0c0c2c141c3d80c00790b80c0c14455001a140c01e46980c0b01c990781c0d85002001082d10390002002d0a043c440240d014842c86032038000580c02c1c1c644125985aaa5440e040401a82c1c114900c03c503401600320b0a0018007014a000401c581d54042010402450781c240400c1090741010003 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 116119694 1250 116118444 116118451
    0x161a180d081c05060a060c1a0702010c02061e01050904060b040c0302030a0513030207060507050106081605010f02030a12110702031b13090809150409091a010506032e09090614 77
    0x10011850008005468100640190000c000320308000504200015030000040758102c1b011b402d09103000c40002f400b0b0026844200014014200820307101d1141590a541e00541600c014080d80c5c00d200510003400e60003003040d104141c5030600c841c40d03510f680c0b050005001507a500540d50f440c00200403000d0700c0c07014003500b850070309003140360011a5022511500380c1c0d4031403600540d1080f05040c601c4c050b1500b81c02015543c021b15030220342460910901c0300481d0020707280c0344244960008181e8032400358000c0c80c808078290410307007408842c040d4801441c03259085d0003141089416004240f0b4194a030b50030710010700e0108813300c0d4900d4046940c120f40010150140501d03562a0b8541040f40160a040c90103203180144031102d0300c0001003510060f100c45003041150480030702346511000c1c41429040491303c99030340045544c5c145041100d100c2e40102d2020388194080031186860b0b4030500180d242d00c2011490041250b5920b80561499035000d1480403130500c0b0305450500c1c0e6010040e = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 116120944 1250 116119694 116119747
    0x50106110c040c0509040f0c0f020d1403040c12050714060a0c06180b130314030105031b03030415110601080105071205060a05090c0309161a180d08 65
    0xd03022101440005000700000300c00e480100b40700f0b0b060030b0155060300803040303813075400350801c40c40d03140410090307121540000c0141c1d11400904210036060ba200c1100c0b000c0e400006421404455030700c2140801180c0041c40b84543c1d070903465540c40420304034400010201c41a81060800b0803054050b401c540f445010101c0e9810701c0c200c4000c40280000c0040d07200102110b03160800c00d988010f440f12850003154024440c140d403450100f8400403617400130002200850603011014807858442e10640741620800307001822403d1800b40b9400c0030340342d03480e0b04540c940700410000c10141510380102c000700320b260f107810f84003e04003121b03141044016044145168507203c10410010f91040ca504540b0894010001301e64a4003004900100c25030340000d6000703a101414004883e52150081d44102241d01c04d54140b40c184a100907000c107024800c07548201c0010782c80040d600800b00042402c10b1381c1000b1b681c0082a42000300343c902500b4007003030f2122200400c005c2c92042c00300d4005048101030 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 116122194 1250 116120944 116120957
    0x20d0e011e0818060412031104030b01030b040606031b080f0c010c0201080a0906050123030109120f0203090907051207050301030c090b0609030f06010812040f0b22090c03050106 78
    0x1201058203a00c90401c0740c0d104010082010801c0b088180860720220800b420658050345064200400c1410419400c080040d19084200b51040051300581e004c0d6a40001c0d01c59a40c2d00c1c64851885d8004060411360380240d4980002000410030210b031101c51401380f200080452500c95031070b040c010411005019600f0200030860740d6030740300014003a120350908181d2803688590003c00014521514003c004514090010410600840c0300c040c02942000060b0f640c0d844a406040c240c440b004170040c14a00e4000419280d103000e5a441d2010b18440d1048a06021400d0000b4501007070039107015010580000b4007521034210b20103401d50120080c2061032441d45161380380d5400302034a22440c1c403200c0d99106a4007495891504850074200c005048454400700c102a280c0c5484082c41890040e21802c01d00c2d00390082d5903000e440c100c940c2c1408681000d45412310a40041c6c0c40748a203101c003040101003406d032880b181240c80c00940082800010340076400c02e005012908181c02c62410f0168 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 116123444 1250 116122194 116122217
    0xa030f0210050f0c0f0d0507050d050c0a0c06050a09051501060306230103020a03020910030b100f0c06020304110a06080906151c150207060e0105010e070f030902060702060a020d0e01 80
    0x14803c181c50300103031410030071070392400c41d80b0702c070182c41c042c800701c002042e41400240200783e41e002c000341c840803083c040e0401c095101e00644490701d01c260107905000c60300d5070b0044000b181c21a0700941e802170801902240c480190b42d1200d04048910701641c80d140b00c502c005100d425490b200381e1014011002d50720041d811b140d601d051020780803c4a25040540008441e44210300c02d406035180c02c60080c11141001003074000c0503002d4079101e964580140c01322043e000e121441040c0c15400d501507501c0305465111251520406984000c2065a8038020800c3c603111603103855071580010140c0799585141c0e824007650090422030080c0c41e00c0000842800707007200c0c44c0d2b030710f08481507000400004545d01c541d45141c80320440510f81c0d50300c40d1252001c6410403d20401d83c001e6140500404001c1210341e032a02c0c08040301c0c082c207944010006102c0403043c0340180c001d60002200d40d0004181609002c02c1d036001071006d030301c0800c003000160850f10781784070080d40000c80705100e083c00b400c040d0540072 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 116124694 1250 116123444 116123461
    0x4060e090d030212041203110d020306040b04060b0405041107050d020610050103060501050d0c0210061502070b21042d0b0f0103080d021308150702060c0c0a02040f020c0a030f021005 80
    0x241c0090101b500400511039694000c0d4400310281e0301c09246076403100c0c1091444002500215010340c00303213041c250b442d402464244250070a5a01c2c5514290030a0708040c1032200610703082e6811030310048100b1001d004900d007041020031f2110240d000300028600180c1d801c48904042d0300480c103040c200710052109a0300300050301d444103120311001441ca00d24480c102d203040c2c00340e03410405841c64000003040da402110341100b07120342d6603002c450481c0d545072207101c010700c500402c2c45080701c9101041140000c21175121a0054080c0781c00d00c1555080720700c4081240301e680c0a801484140141c0d4004000c3c4030501c80c5e5001c40a01c201011303d40c03550f25410003900c2030420704c015055001039010b00c9902120604406030001c01c0488003a610300048000e400c440c19943c140c090300c2000005030210742250101c681d1402041c02030a018500b603824032000d080d1b50f01ca00340220b0340a1140c0341c2c1a400c204404d252450103640c1744404010010000b900b0811100c40c00070129050008000c00301 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 116125944 1250 116124694 116124727
    0x303090812030118020d060609091d0a02010f090905010906150807020a021306031407030b060303160303180b0a0515120c12070308030406060f060906021507050904060e090d0302 78
    0x195503000f1482450409282407200131b1248204400c0380514114010031440d038000c494109883e41000100007800c0701c0c41c03805044019000074188541d020080c00d00065200e081c104030705d80c206040040c016a11100036006841090700700298040d6594000c00400030f1803400c0307a0202e40135081c20038880c00c1c6400c3c000c0d12000451f80190017641c4031705072004120041d600103c0190b030000d1500c46210000346800c1c1c0c51b9101440240d41000c0890b01041080c50044200d40d0740b201c0700d00c090503003481c442e50b003035011308480841c40c17040c183c600c014640403510081400348281001c1000080e01d01c0c10f0404122241d0f031481c54a4090f050341101c2d02417800c8001000380210000312a203000c1910580c000628001e0550401400b14101209201c2002070030342103072096030708085e102d049075610741c09c0c2102c480d0035500c10640184e10000305541c62449204909800c60120310b003180c600f86034400071905450070383e400403200141a50170807424450a02901d000d500381c2c0c0c64190f18107940740c2041e4014 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 116127194 1250 116125944 116125949
    0x90308070605060616060b09010f0b031305010605090702010207050708030313080c07030f031806210e161202011d06041502010f0f1b020703050706030c02010e1603030908120301 78
    0x410350b0b248003094080d0b0310941034a0b02800400340003101c0045501d406c6028152001e0614090040c3d0000030585940c600c0024041e80c10001e801421580c0c1d00700d40d0350b003400081c172081c0d81c107560792440480c3c1c0343c507401a200d00c603802580015a4850b118034206190030416405020150814400c0c811180c15100303c4111a6410060f025114144c2c0e42c0030b5400c1c800164030080001038480d010358109500142540c1200d0034040c1c2c1c42e01d901c1c1d80e5034400c1d00c426900c4841c24001c03c90450380346c8180319059001801080e40b1104840c2e10500c02440b40080702050381000c280000c00081c44021907a0050710034210101d5a8a280c098108600105080b03000d203004003d1140040e440d9022900d100358809104030491440510450900d880100004c050040d80b0b0701170401d0341d50031420b1203400001c180d0708071b81d030000040c0b03440c5152600450091401207100021552a41550604000d040203080c0e1110300440c46035603000e103503280280501442d41d0244000307801c600d01d00d103a09481a03056030704 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 116128444 1250 116127194 116127203
    0x20306071701090b040f061e090504021f020a0210050c011a0a0311010c171e07030f26010815090a0b04030f1b050c04050916030f02150406020105070f09030807 70
    0x10713100c41490000f405008620b00800700075141c0748001441e20054902001d841d0b003009611005581c403800401c1c02d54004480c0a50040c894800b5a5008881d4007001f42c491a190f1040d00d50710140360f400120301c000d00c10784000004070040342c600c0d0760590a124503091401c0c150102c880122614003c591001c9031071001074881741d0f002c400700b10310343d024041c001070b003550040e507807120206030340c0703007a242c0b500003030003200441d4001012002040d201c202100c03c11134258031142c2900c0401401100c504030320240001142c000c811104011980402d0624080c00e040005060a500d001c00000141d290050481007035510100910010906151100350800e805181201a581d8035040c183c9170700c4120301c0003552031100016030506001c40070800c0200742d841150240026120102c602e5512000007803141c5800402c0031041001540c450042050140b001d4424244266082800d2040d0740040d4011030250351200c0030004155070080000302540702c14140503502d641192100e242501a0b0a4000d2 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 116129694 1250 116128444 116128451
    0x203070201020f0c03041d010e060d0201020106120602070b06100c11030a0c061d010306080c04020702031905070608070c030509040e0f0d030903120b0f0121051302030607170109 78
    0x148018800e40444100f03c20904003d581c1d803000810f00355996000d4454252900300503001da074213082c15080680c0c101c817680d60101e0016140d100410032043c10f8604100d06541d078490000076032046030f5a44031801d60041100503140e44241c1002c1130814002494180f08610025181d86450341003446501081d403ca070034405107001c0200424584140401c010705000f5410800003125035020311104002d0201319810740d0302104140040d07098564900500c41e40e07400901c1103154030300b003541c05810310600041c1141c0f00140d951350341d003003145017408003540c95400800013400115003015903160441118a4a03014602c07280c0c034010103a009250341d4521464881e00010030814007040a11118200301c015a4040b04202601030005c0004500807004101115442e05526503603100d0407034007220280c9003202c4081040f00440349518081007042804040310740c80768400c113440c456240704400c41c600f545010485070041503e0319600915400800c5040318400751000031003011281158450030010 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 116130944 1250 116129694 116129701
    0x60a050703030b03100e0f06060a05150d0207050d0f0507081204050a0c09060f0602070f030303050403050c07030b0a05150f060a0c080d06090e030c0c090c0405060318070501020c03100203 82
    0x1103003c2c102c2003600380c2d03061148078015040d4903030b154014140e1907400b40031240e407041c035074804a4540700225200b549c40f41d45134904010342c0c00c021003c10145017000002ca49071522504100040380c101c0f0600307884681c40441644021501b042502031044c0d80c50401904000c1c0580c0d030154144120038064601c40c000801090401108000c28600154070242c2d800030a0780390010b072002480c171407040d086032005800000a03120700108441060310001c0034004585400c0d521f081e40034000c003031300480400c44100100030360641e042c81001b02440c840d041a00007410140301010a079140580350100780381c1002c407000a113a89009420b41403603000d480654451003140d10aa49406840401424101002441d81600601c81d44900c00b0f9800190040000c048001e074510358078050920701040c40e500440b58154140782800d00294800e40340d0022510701034980e8003080e010b0304182c5020f003404a12061070744078aa4144813800c0988001c1c8010100740700f034040041e0b92882c0d0140003048171940040032 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 116132194 1250 116130944 116130947
    0x1051518040b04020c01140105010905010804080a0203091e3a1e2301050106081504060b0705010b0f03030c03040603020f040504060608011701020f1804140a022502060a050703 77
    0x8400c10b250020001c54030750031013580a501809451050f1484074400c1800440d0940c01184040103640060b541d00c140ea40e2141e566201a5106054910a503c400e0180c00400d60f1203c80b58041882150b50040615a0000c140010303d0340035080360340580290159044078500214108e0104418a01c0c000704840c803904003002e004412202040000740300c030030300740284018003088130506524144410030300e0506d10f142c1404c0f24400c1c001c030700c001a9480c0105071904d446207054103440b0001000003503801e0ba26030300aa03403903209900480d61651030b00403c001a1402012016141c4d209a0140d854a0b084010054580c46540648802d15a001c90140074400c1a88241c502824000e8400c10040c0e403200006048440700740301c0c0880c05554900070300900801802500d6014550904180c01e00002102804040e040060b01c00e0308540d8404690f42e01d00380076440e41d400741030602d00c0181d85e1104c88178401c42114103140552206043c2000e107000507102c03081200c00c104001d141c240d4642c45240b60 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 116133444 1250 116132194 116132201
    0x1b0b04030314090703020f0607030c0215123c062101090302030721140c0a051c0e03010b0a031b1205100b180c0c070e01030c0302090105151804 63
    0x502c400c10301d800104041a80002103403c00c1e24001c40b9030170480c080302001c00034144100c5500600040c8041200401410218281450411885000ba080c041c0d01c440e17a07a00007908803a04089035401050040046500504030302c91400700b0307400280e01c1e914080300745484040280000b80a0700500000031014403000004100c043c05440c000e1100102e01d0800030340d660810a4240e501026034940405a82e0a40c002c40e8013072100e45d181d103080c903440c003407510781c894005074002c0340c040c0281048400010400d2003031350841c502154611520340c203003010007441100741c004545d000384c0c0360451141c555910914050b003201e40c021404c0350380c0c407060f107a00f5a80ca03940da0700c0030610b2490074014100b0014041a00003108801300410080c0c0e1086804102013400000440c904100050011403036100c0076800a0807103a5805044518a130356501c0301e03010304a026481a10540c2c0070200030703c2103151a011050061100700e62010907075100304248803c510070702200100d00940b41011124940350b913007 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 116134694 1250 116133444 116133461
    0x40c060c1a0c07080f07031b0506060d020d06020d061401030e0601090b0f060703090501080f010b030601030509030408070303020708010e060115030c0c02130e0129120106050d030f030c1b0b040303 86
    0x540a0702c0300c0c00411700081580000804074040f031040c110b006058a12800940d0040c0d80020013403a0303c0e2904000c0c00707a01b410045003640c104080204200200300d0b80d000605454400b1040040d4441c0703004094690a00c19004180c105402d140900004400c0092100d0656480036400101100e2800004104043c42440d00d40c02c01c4000c031320b8009240d0400008800c0341c5080e00c0b0748100c2d81d106801d52500c100240244448a00c082c808121107510a81c881c0e980400c0c40401c40c2d01e800d0711000034600e1724040d035100310300683c00003500f80003052080c0108205154907800804482d41002e407600c202000344641d0034100f42d900c00f90b00000030f224000c3c011b09141c0281000b6203208c40206040701511048a600d82035608045091506075106121307400031114031260390b41452554400c005010b56156040d498641d02c4200100b0560761390120401117500c030740c07102a46500611b4014050726220365040040c414050b041150301c0744407441106610340c0c081c20900f400d0352140390a41c0107001c01d6 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 116135944 1250 116134694 116134703
    0x30307050d080106020610060c0b040f0606080c040f1404080a18060e040c02060702030a12110d0905060702010b030a0605071107090f1107020f2101090803040c060c1a0c07 75
    0xe101c0441040c0c0107000c660507140b2a9003070710199942c0c0c0d843c6607100f46003886010f0005458040500c0442e0b2101c503007035002403150100200b03607141034079140141c56040d006084c080c2c01080070101c00e498280f007841e10041d031010061002c840c2040d00301d103281000034000350078840002103059010f44106070240d11030310500c584200c04e42d22410010007203e07003182014055072070091076069140c00080c0891248082d9401540390546034202203400c401ea03151100030a03074942c4a010109048880908800701c8000d00000d40201c1c0c0b0b0402d1498060042c00200a591521a40000755100403074840700c0c3c107400a00c00314498a850a080300e275081e0131141d03004603000e070000100f81c0342c000f500011021303e1204402e001081e403103460701c1203034498014003e500403942e440100050130700f41241285080e500704541d00482c0142d500302e082d0b4222850071134411f07130004108420040c42001000203003449140400303012180d99580101d142e8046000c92178122180c00003104050700a0850340301d260300 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 116137194 1250 116135944 116135953
    0xf11010203070b07030b010f0c3305010305060f100f0b0307050d0509060601021006350a0f05010f02040303020a02040e0f0a0503031506070c09020c070515090f03010c0e0f03030705 79
    0x140c4c00400400344030884500150b40361070400d00c0705210340100814280c028801c2000006c07641e281c12a0085c0300c0f810801007214101d44a601c00c9503500ca90390007035000390040c03e560300c2e1541040c03c013200c005140f07405103034402000b0300c038074a080d40007031050b02d020540301c50b0b607500da0040c192424058a070b47c0c05002c81c01e01c81001507024000c03440c135002d00710a80841c0c00d042014901c21080e6043e40c05804451520781d401c0c0109590000600c030f803d04402c0c1d0741007451207011000141840602c100a803018001c807030f00801004424810780041400d010401c50a29045980c025220b0050307400191103903031283d00051411078203010012510031110201c880600483c40c0c1762f6284d4004a590110020400d11020300c0c904050040f129003075407180b00072802905155a02c0001e40106482c0712552040d80408541b03a2a111101841c100d0041962070303c90010804002e0101d03003040c0d01e18000c0e41003408003070070a90000d91445602d001100c044026031a00c1e4007080c5540030f12000034245101d03 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 116138444 1250 116137194 116137201
    0x25030804060509040c020f1f0906020c061009020301050a09200a110115050924091e0709140f040f02030a0207170f04030803070302070c0602280f11010203070b 70
    0x10010300610006105032414005d509010100740d84800401001c020f40360070065401500c461788007810810800c40315000100344a0300d0b21100100e81010840c980994000800d0000280b00ca2503104010480746d4825807841d0706000c08a4484049803140c1800b460300d400280e01d03034507101030414a84048141486031240801034008118002e0009480c1e01d95180440042240004041c50001c0d44c0002e05000001c0d203400301c0d1050b0414070301e28001c0f0113601c410051440b5030b0303c603e0b1450040103416540382c0c0802c410b2118070351151001d05103400348031220900b045900b40e4000207000c084021580c61030078030382d0303800400c014205130320050900610010030403849844546c060503082c0d014400c0854034000054a5184920804000740700c050f0303080c0000c000142401004560000710340c9000f50925425960740b69a40c7e0198000001581000f41d10820502d1120014405017042299180071030200c1d866400009040700c6001d00f80c0c4400e0744200c0850390081041350b20183e481545e0007507916 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 116139694 1250 116138444 116138447
    0x26040501051f350712030914010e040b0d050102030a1401060503070512060a050303030f16030204031e020307030212010207030f05030f0609040309050303040f2103022503080406 78
    0xa002c55015024082080d1450744050690091000361031082c030341c001c0070b000038602d100d00030012690074805540301c8011600c10100203000080041001c1c40c0302202d105443c1c40c016000c0a019080303801e00686c581c000486980e03110102d00c980c0c1405403400100e840e00c51010440c84901d94074080c1666000100340503142d0010f40c044036401401c280002e6041e45c03a15012125440140c2c0c0d44400144144100320002045074841d541184d0020002445039541c0c4020a0850300120758a00c4640c800304100034068030002041040c5100c40e01d411440d050865851043d9884c404002c0425403806411000031902c08002503005035800078900c0c200010090303100c1d03010b5409510b0450014002074988102c25010b5019030b406048440d148424503601c681c03d01c014400700500035401c2202a0000184a44003030000f00044d080c02148080c40c02d0400c60404038101e03180d0f421602900721b4056100210381d011400752034900d0201500040c0c3c03104e80d0030040e03901c40e06070405003043d034001a0004051303 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 116140944 1250 116139694 116139701
    0x11030c19050705060903070e19050106050901021c0c060e1002130f0e0f060405040203100e0a0303060b121f030206040b0309060a050f060f010c060f09020111010203090d26040501 78
    0x100e204070122103025032102c05200f2140102c039007064059001f0f580034045140c0c110086a40040d0b071a680524016086640005841707080c0e020a0124800045000840d41d061001440b20851006025140306000400809865030702c04003a2410ba80c900307030113000300c2c018000410009a589825500c40742c01010342c104010991040c4120241808000030703501000110107842000b208080c21515a01c04043c04003511000740101c0c3d160003907041d4140c55942c0d610034541d030401d564008108408082c600501110280e4002e1031681c003060000800000f020200568803108189103070121880d00924000718960071f8000a500c80300105005c6009980c0034065440b6410000440c6ea03151240300c0904102c403401d48242020880d0140014940c0c1011516880d0011043c17506200054043e00d03010300710f6680741c00a86040b13448a6000042d9070340a81c54183e0640054021440d41c2070844403503565110f56401e03201480b495a0240c41c010b0b00c80c8115031414140700614094070326007450141d00a = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 116142194 1250 116140944 116140993
    0x30114010f061404060c08090d15060501050403050303060f03120f0a08060906031015030c09060602060603060907120206040306090c1e080703020603060609030706030b0103140f0711030c 82
    0x1c0e51071031940041c2081c821410b00720007a290491080c42c16050180880b044a81004161003440b003c020945032916030f2510110814007070815000e00c1440301d4070000999019622060411405010030703c0480c001204a94010504851140003a01c110002c40d0410500c02c000301e03c00c44c8007040703240d10741ca80c140041155007003a1340c5d8540707207a54810420410031000c0e5815a0154810041482000d54590002c80c3e240904960401711550381c1c1d40381586003a46800510405407106c41c2040701c3c0c2c0d01000a59040341048014000034981440d807159100200e100d4451080344c1300d44054295128481120041d5410520a00224165040150102641c1d201d1020b60041403850358224040d0b0700035030000c5c0e0300240c2c06028510710b140c081010035000640030540c000410012a9559030382002034000510b9240c501040c41e00c24840090200c8400a940000310741414082200405000e6106907120500381442801c1806015055107580501541c440f007522402d400c180d0b0010b9040c50001c0c4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 116143444 1250 116142194 116142209
    0x7050c090103110f011704021525020a080705060708030a09060f0e0f0d020d050d0626010c14030703020304050a061a090c0f0306060c0a0c090207020108060a050108061005070203011401 81
    0x400070004c401103506d07142144089040440180101e001450010030030f0302c01d010020343c1c1504004d0076410300004d011b903a42c0382c031440c1140303461040304604000300a40000c1c010600135098039890803011900d240700c0c4130302c010702d850750000010303d0054855226903003007a00a01c080114031907c0c1414401080c284104402e0341c030400c00195114003000541091449290b400b80141c2c03a14002e00307a0b441e41005038007103899a02e82c1c10100751700300072180340c0c1000b5181201c1c640480d2285002513003101c2c0f4840d038803420405034242c42c020407004441140e070894054580140e0361f03038a504003242010030403040104994102041000c03541c6060351000350105084036041050380b0303002c012000134402c007603800c10f00c0c100a10000347c142c644600509600c143c07007402da0b491868150303644000c2c0400c941282403200d40c00b18001d819541e202d00745a40c450001e40d6032000071400e03c40007914242004003200d104c1c0e50032104524800f407180041d2401d40394090005d0111106000030260045024002c210 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 116144694 1250 116143444 116143459
    0x60902120d0210090507030524010b13030321051006020106050603090a300906030c0f1719050f07030b19030308060121060305010e010e100207050c09010311 69
    0x96450003085051008107650010305041c0501d0000a001d0190014140c5690080410000100307100b80140c1e41d20031f540346055aa960500900f0101028068121407400441448030b0149000540c01201c240d0380c07d4141070140c0d0b5944000a803100700031543c8894100d00704014451028040000b030429280350b90001e00c4901e4540c800c0c420940000c841c0a40c0e29488400d600c0007040b080c81c0520b0300300001c0d4030b0801911031180100c26400744c0415640000490425040003015071502c03450018903500e180094001c105503c005051804406444c501c0785203a9000c247d80300d5000c4244407104003d410f052266241c806d22641d8840d1088070070002180c101900400d0524003030b44c82000b9211000c0e00d55405500750f803003c55812800502d41030600c0407000b000b42c00f2004e52003111402140c001c0c00811818214a086825150740c172685000c1c0b60b04102002c003a44002050421403840c005400584818950914528007180c1d81d81080e00250340200210034000300f01520405090280c0e030b40d4 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 116145944 1250 116144694 116144719
    0x51e0c10050108010209150a030603020603090d0e150a1103040f03030512010501031b050c010f060305061006030204080c0f0a05060c06040b0c030c030604092303071406060d021207090207060902 85
    0x15080c1d11074480c0503540708141c0700c4400c5c81c4905c80005030230302d20712604e00000c005c2c3d240d03800302e00203070f1040c0c4030880140d11101d1480c0e00c01c1e5205081e440118815070b03a0710f255030100342c040c203181c0c040e4401d801c0a10012416041d8107440810a94006100079910a03459682d00e00b0094031581c403a01300d10030303401004400403415500034040c61810860f00d4440c0058041601401c07070740c0f078000100f440d04654982d944005807500307501601c1c1c05103000d42c1c050107550030850401f000300d403c6035100805050050208001c0c030130740850b00444403042912428403106d1903000185500d440c03074001c1035000001183c4010030360400034003a0300c00c030303c941c004000c11385403142e0a031401e02040f0740d194207611080000648a04150b00070b40d9a0034400d10a48074450817100c04900b84180e00c182c0301a080d440070031494240a03070f0113401d00000c7c41c90005400e440c20203901045c868844418041d00603203142070b840d00c4940c0200200303001864520801c40d100c58461a0882c040c00c00384000741e00c030b490091500c = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 116147194 1250 116145944 116145959
    0x51e041215050709030308040c09140601120c050927010608090f1219121b120513020105070c03060e0304090b06030609010603051902030103050102310501051e0c100501 74
    0x10b070340c001d8280da25180c4c41d003072460350b044580e913500800846141c9060180000c0c0c2c0981c5028403d42c1441005042c0b40c0c61500400052041d6020640124100c0c2010600e0180b180c01804440c0c401c0c0302a80c0800020b8209a2507844400c1e64015840d44840c00c3c100010704541d01048541c01082c4410543c0c11164101200c15130740e1154422070301d400d56082100c41d100083e042c851108184443c02c0000310022004500c00840d42c5240c9004955412003d10f0800c0719030010b40e10001201c2604200114281203000e0300c020140118001d0501c08000744c12030034484c64010300002141d019105100179444044440d8481d003081c481c5044060a08440d40c0044c9856401c2e05c0c400d03070024080b1501a0320303200e8120081c10b00549181144a003482c210310b84511180000c5020f180503400150b03481950115030300100d407440c0402240f2030a601c21400916280800c0c0108032182440d14941b10402000c4c403840c1400442034001b40540b00041b007000704180417910250020703030000e007006103a0740c1310f20 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 116148444 1250 116147194 116147201
    0xa050a080306010305060121050601140a02070609090e060a050603030f0d0b010207060c0b0a050c160807020f06040b0a08060604170a020102010e0601121401020c06240312030403051e041215 83
    0x49460313234845050303007152038060b40d84050340c00301c01454603010942c0103120740e0034654840007030350005800428050205640000c60f110040c8802e400810075035919041c50344d107581e0050400e00889461750081155039400b00150790580140000700c5a540c080010103400078020600d425015010f84003000580a0040c0d4009040340d8000c0340341a9981c4e00d844400f40240340007801010820402d001007020007240c005121116445414107036580c40290041050a41030680303010721980c01040305105c0342c00700400b950541c92160801c01d42e40d480d500d0000d0524007031900160300482040100000c0351500040a102d002d000307800800803218440341c0745458007002d00174100000e118409000000c0c6140d150301d0140c16104000604109215003101d0a100c400d95505907003050071803d025141c81400c107818244a01240240303c8040c0e0b07058982d80a0000030030190a2001c08510402c40a440e00782d000300b07510404000c1955142c680c03407040400d010280096903c04100744418071400346134070 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 116149694 1250 116148444 116148467
    0x607021302041e0801110a1b060c02010c02010b04020c15130503180f040507140a020307060513120203030f0403080c12190606080907120c0801060b07061b1205090a050a0803060103050601 82
    0x312a10380f200c0b5030f1080d0740e90f26402230500000c0100d0340061002c05c80368801c1c0c40c0f0044181d800403801c26141e1100a003035628005146200d28070420903846186000140d400800e46010031103c201e655880060030381001d583c50140441c040001c4181c0d0a0360300b00cbe00342c0380a0b0760403900c01c0444488881404211882203604102290303510708000c01c0c0102d044003034115403190388102c0349005000c1d5545e500303441c41070701da0b07092070403101c0e04860400441200340416104144010350640c43c00310b20380c41841202500107001d000014002c0f84220071070000702ea002500016400e030380d5044c00102e81c1801c009410104036040c1c0b07400f4000c60414460741070035014003c00c1008181b1542032290210082c4070320340303085032901d0070000002480da90070f001d110020140c09003480e40f83e4016003001c0b0f0682d4030200c114448044c04220003039502c0d03080200443c10080c80c090010741ca03a611103141e490300b009514060840e00c07075464624100005c1c080190311a5100b070f40c00b0f001d01d03100d4000641e811503c45 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 116150944 1250 116149694 116149721
    0x70618060f021e090418050f0712150504021329030109030c0b060315090304030516081f1806090210020a17181012060e150607021302041e0801 63
    0x103030140f100707102d9a8080c0011400041c00000c0f18400300c0b40384101e0051071541128182c0103c4039982c072600c42800719400074030342031070101d002a45031b0b61811141c0c5003240001582c1c40d42c0e00049010364498240d0050754800030681002112604840030b1000c55403d00c942da01101c0c800210341882c01e040c01180045a03040e00c400e9098912a610031806c0f020090000b40c041c403920f105c3e0b0704a014000501030041409202031a82c035801c50410508041201e4440d0411840c406c208016160700040d403803010140c207002040c410b40800c402c1e040940034101012317116a50380424042031104992140941c0c03071080b038100c3e0250b1507501041e40c5442d00580013070408810604500e98a1100c20010300811111410542000701003900054101d43c6c2c40302030000080c294a003400801165205060180024028030b075114035160907074801110a15005038050701000c5800070442d10744010755800303c65011020740d1980c0d12085c0340e20b004424002501140121410000b0340080107100301000781101 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 116152194 1250 116150944 116150977
    0x1220010614090a020c03071a061c0308060a15030209040b0f010221040302030601140f03060f01090f11041202011b0201090902030705090d080405010201060b03010509011406070618060f02 82
    0x84104002c8040c0006007510750240d020841078049000500c01002c11502c69240c80e49420130b402c1e03489080d080c1c0280158002e4101560740c0320b0a00e01100c020244550510300f140841e518000880c80c0c0c1d080590101140e076440c3c854489126406070054046198140e83c00c0205402800401421888000321603016030804c0c0684541070000301448042c900400c052541b03040e5072540032a01d0644264040000d01000c11001151450f25201803c09140110000c015900303201c01940051074040c0f060380f8100e51344002c0040310201e0398207c1110b4440c84001c843e200c035a1400480e00003008440c081f80068036101003004551036107602c03440387d6078042e91420f1076070b803c0440c0c8600030b40c00a4403d03405d102080c40091501e40d41c0c01c040c104024410300c000d58070b40d45050000b80c2551a075811182e9142c1c420310040c000c1c2d44901d119541103a140c008605410031669000c10b441b4420740e4409081c580c100341486070039010b4541a00c1e4203900c60041000072440e1035120500f20f0044d01d91040f1085007 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 116153444 1250 116152194 116152229
    0x4060f0e060102070e09030d14060f0105030a0e0724051e090f060304150608030903030d020a030b1503040c061b021003060902070506010302130c09150c12200106 71
    0x30840c051944018180112912603440e502650702240c000c640100e400e51000490300c2c00101103000c1d42c2609082840309100d682007590010b40450664003102d0f040100100000e0444100c50704051030340384c0002c0903640c081d0307220300c189070b2001e10010000e0950003005003503000035840340048035405441c49000c14655114600d4000c6654044c20500781d00c403440f203d181c2c07900d0795010021030140380300d00a0499440800107950b003e0315244d0307100c940c043c0c000380030260706901c0200441c1d42d0b052403180e0059503112000c105400501c0d4120003a50802c8880015019401d685030056006900400f03800460a0b0b6480089078020083d400ca020030315179440c0c40f20b005080a888260491840341804580c007a25449014102e030000d10064400c0c0c3d10110040055060405c5001d40c034450010f401c1c400b40cae8030b400700038088003e18450500003409251083c83c16a22031408903558507403202e5424800c40c4403010052802c20082080d14010f51303101d4242c00c4080b0144105011113041c3c0b80215420780 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 116154694 1250 116153444 116153459
    0x504030f030f0201110d090302280305070516060c150c0507030309150c0c061404020604050d0602040b0d05060f0109080d11100204090903120b0f0609010203090d050c0f04060f 77
    0x103222400b4038207540d20f403d071242c0c02000910181568180c944000a100d00f92402d0013850408900c524480d160600d401000c003003501510304040f0541c05060040c0e5030b00441c07904525084203002c1800ba0ba601c02c0300c011602c0e40d4801140740640380a03015031502c0b03060b000c80280c03c940c2c041c14a80c0104108118402c0020b00907009860103900800281095442c1003410500355103c8507103510002d003280d1030041c100315182c030603803a114a03c1000328245180c6a0b0214a1034802c2e401690301c20000100c54800704202034049030040e20680e0010349e11005107d1100380a42400c3e1152445006d2444800702e4651298110b50102c455107402001c1d00c01e4020001d0b01e02c450158455900b0303003d003903103c40248010780020320050104a10000310050641401850704000d4103030124803034140510b40017030b561444c0d11000c005004a5405540350070210060340303148100b00c1e02e560040054a400814000041100d2041c0035040d60b11016540c0800c040004a0f040e50081581003040c00c1d01c240040c1 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 116155944 1250 116154694 116154707
    0xc180e0a0b010e090117010e060c1e0f0d06050901050f03250b160c0501210b0105090904050604030207060e060417241006050f270d0303021206010504030f03 69
    0x301d0103040514180c0c4055001c40d001a100340c2212110640c0501c01200d045000d1150480c001800300181c00f450400b00c8401034a4444c1e200502c195142e030b00900240240d108040f02c1e02c1e000e101c0e030b041d5a81d0a8200c03050b8041c1200e407181501c07804401c400028141040a00d001e01c66030010302524100c2c03041096484682c070b41c1000b482c031030b000804000c54941c42e16401428140301101c01054580041c0c645a0b00322044d6403c444e041000c42482026640421408118400180c4102013511140200103c03458015200e0300c580c4051001c2c240002d006c40496214000ca002e5406e030307042291180005c1e550910f412142d9904000c04100801c140d0130750310581000c1c0101401a100242c426100344903200b03420380d9240b11003c10080c2400404200f50000c0001000207003880c0f814078a00b03115102c600c1c00703001d441c50b51b092100b0013101d071141100c1114041840000707140203108111418018025009179085020190703c1a0201c1c1c415070164003a502201c5d88000c0b015562240c2da9000c50710b5 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 116157194 1250 116155944 116155961
    0x705040902060d0f0f0603030201090203100c021c02010b0603040327230301090503070503031006081308160203031303020f040908040611032502013002070f0203100c180e0a 76
    0x40c507a510603142940020380071b114001c500a50012a20341c40310f004050608240265040c04103140075000d00b800c6030082100030311010628501204881f1502041e4054040800201d5101c14000204803c041d003100007100000c01005007000102c03105845403101c1b050602400c4507000300e50b00000510801c00709001450580640040f80782d0601c1d07980e1030300d140c0144000700d440b0f42002c0704011800400500c1100140a01e20f001203240c1003503030b01041c4285092070003400c00140000c180740000c00d00d40401841d80c0d40070702169907c2e03801580050000800b400102d101d4100700580c1595071520b40100c0080c19003140380ca618061038843c0a035140808030031f1058180c00180110382102880c80d4100b01c024000c000c00307814000c83e92000500b400003000c00c0c864860404180101045a001e100032064100c5100050750303141e150600510061842100940c548220011a4184007094001502950041d100c80d90900650510240400d06901440c982c2241147c0095411070954000008 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 116158444 1250 116157194 116157221
    0x8010e1006050d020f2a0d080105010c031b1202100b040209060d02031308040815011e050f032112160e040f09140f06090a05060103080901031b08090705040902060d 72
    0x2404803245844441c14400c0391b0303030324000d405071a06018400001c2c0400f070104080d03498100101c0d0b04000010b0010b0b003c00c0c0c0302408001d401e0600210b80d40c602c1d052484c8482c1c010b50030068001140c44001d40c6c829a4040a40c40942401c40c444418107080c000e07240ca810300100710034184035640920307100a40008125a030426520480f078008515480010300180440c1400b910030041084408021618107074040010581c403101e00107505104034400f401643c60455448c00c10152500000b840c00d0165205001e00500d41c90041e444040380c580103003e4800ca044e50402e4654801102c0003561403680c1000b80428103054136100549400c2d480001c0030a5860b50000c0d440f610350b00e03000750700c40400d2000e80c1c2e41c2e80814003c0c090180200070466002e46650001c0640500941c0c4158503150107100060140002041043c05c9c0e0707029400c14042e410b00f4101021308c40160a070f0051200000f502e019016001c0c5010200e02800c03c0d008461a06801030a0540341c00e0b1310b50311010080883e18503841 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 116159694 1250 116158444 116158447
    0x70b070e010e0303071419050109020a05092701061d010e060d05032d0a0c0302120c07090b1503040f0309061404062d0e0f0607020109060c05010b1008010e1006050d020f 74
    0xc0200300c2c0c2100e6469281d004d6000011001840d2040c00600c110175085370344124400c6042046200002201d0b1141050621001405840744030540d4003604458104014101400300348079144201c1989441c101c5061100689850701c0d41c1e02880f018002040e4081c00341c7c0c10421502da01282d8041944407180f074010f50030944110940d409000a422004005000a03e04604a0149a41000104c1c40001e0780240385180c13110040f0f110750380c2e0300a8801c0e0624181c944009a403159580c02100031030313800d88040030baa64503041c81d00e10b05e1560f06550031008a0780090012400c00d215804003190038480d228203d00d800d04041080d20380500c041410200486c4810f01c414440c007480300ea90382d8108a98940244e1020b00710200b00314000907801c8140944018031081c000340c0e0740609041c0890300c550404050311032403410f045001d0050100c5168105640382400c0c91030a600c202502e04840d420711400c106512240320100207003074144688c41c00244c2c103000080d040109a40202182c102084099 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 116160944 1250 116159694 116159713
    0x60304120c21020c01080c090d0201021203010b1e0c06010905040f15050601090603140408160c030f0b06040c0c0b060123130501021606030207080c03070b070e010e03030714 76
    0x2034904480b80d5100c144403104103000b80d040c541c04101080d140380003400d00300004c0c60100001c075a5806002e21003445810a11103600569000344032842c845000c0c15030300744d070ba580c44803030001075a40300d000140000c011880340d14191038421015141c106000c90f000e0012030346000501c00c054a03000c1c3c010390304a400d1b4034030040000c4d00c83c500000c6212a4840105403440c9c404005050aa2140d0040003494140b10080130703451b1072005010f60196110703864644911040501d0750080c00ba901d0010b1103008041000710070301160454400340303076201d0b01038411a9555030040c07006892440340a1404904985404000500e050700c01c1c80d4010010303d0b1080c0d50f8201011014864055000c1074080208002554206800148501e00c050f0500780006d180c4d15142c01140c1d00e01c0307410b80c4a240b04156000ca43d04080040c81b5003211205001d92049a8480c038080c200305600d03150980d40301c2c02003800c40c09840450b5000c4c404c40803560000030081c40c2004800e8071003501450310200c018000340070380e5551 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 116162194 1250 116160944 116160953
    0x3030216110103110a02031c0e1501030203010b220504050f0102180a05151c020403020d150e0d0e060304020612010602060405010e03040f03080d0f06060e0915060304120c 75
    0xa241685010303084920400078048005400c59002070f9011074408820011800b4003500082116044040d0050750000c02c2c00c2c8400c0310008151a40b141a51405640d0343d000c0036a600300f545605030b900881c000c204101c0e141003000301400360b800c01030300050f80500108461102681c04154018042c8043c3c1d0f21561141c420785089a0001401c044002403030b0b0642c61150400d030818074060413054400c0f611403100000380e4140c1d80550074040840e418a9040002c1d10211a010f0301c000b554041d18003c80700d0a1440d0002081510b0036080090758a01282e04441c80f00010708081c220100781c950500c040c07090014080c40d5400208140e800c0039040041c01c55280544094034003d000c580d02030061070504d45019400e458070310032002460b81c03060109000b94600100204100c940c424107192361170412400010180c00b4280801807854680440081d0f00f5401c5403400740901c40031510b155056640d000d01e01543d40450b080d0980200c014000540040c004000003c61602c0604000c464100541d84 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 116163444 1250 116162194 116162227
    0x9010b070302010b0904020306220602190809070501090506160203030c0601150906020618010f05070e03010605030712030507020d050106080c09070e01020d050d0b0307090c0801080d051204030302 86
    0x1150840024030005142c1d0a01c41c1001c0d4201c100d402c1c0901d13041c5500000e9460b18050101c5000c02554145074001d42041050106004d610a0040d91030300ba801e1107180803a480c955203072001c60f80c0540040c0684201080300015144141c4800c070006050500303202041d00305186102503000b0b618a0399026a4080000e0040e10078a00000e05003981010003605900c4044001c0c02c0500c0300343d18040c049141c02051844c0e00c600300751542050b03100000081d0f0302400003200c0d8061002d10308024048440d9220100c0c00d03a00340203800a000c09079442c0e0525513070702581d2181c0035001400c919540300091080d0028813500740010107500301c00f0442e440b92404c451035940315210b940d00010142046003441e151f170617405011800d007c0e01c004e00b07090000c1c2d103031141429080200240092040b1698503a90b00401405001804449420362100070440040000350030690103d041c3c0c81c000614901c00041920290a042d5641e07030801c40002c0d85502c3c001c10151088052507000e200c00c4205101684 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 116164694 1250 116163444 116163449
    0x4020f0403050a06151202060a03141003120c03090504050703060806010e010e1605090909030d090506091501080714010306030b0f180d17180307080307021516030f0b0901 75
    0x400f03024040c94919041c0115444d5110038403500440340020007415609040c000040c41d0161403056865242010450050050340342410a803040e44081c09a00040e0003030030820350340310f209441c40b0034241190540e00b03183d040c0c000400041e00940184054100768000e180c0006036420007142c490303118078209007480000d0b00045c2a40e51f281004104003860035105540240c09403038013104075811603200078000d115990340c1e00d0040345100c0c0411016042042100d8141e2000310040040851a1510a0306c402e41031756109158411001c00b4101e4061f0b445405049a5a500081c080d0f2450840c2d002c1d45001c4424005050543e9000e001002c16410308800e4400e8a01120112461070120541c42d140c170400f40d400d0340903070700c44c2c5006032084d50010030400b6468003d8141d0071190365074042020340c4803420031440e01c0c0c6006c00b0071048104011400a540a01825000d44590b40b642c019034401500c011550203095080040c1030210301030003544910800b004021010400c40a240d021441d8600e080c3d = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 116165944 1250 116164694 116164703
    0x110d091e14101e02071b090b0f0306070c0b04030315090204090c0206070e0d080903011805061506121f0312020f0114010b13030506040303060317090a060e04020f0403 73
    0xc420703200e440a028101411001d0b1004200f0010480c0f0703480c0803188150500c40d400d940c0003459009004140400348504180d502c21204450f4540a590001d0300c0e92030000c5000380d2440040041610303021038501c0c881d007000e80e00e0343c1e881c40e40c5407036078090000b001d40160241503659080c040041d02541000000e0090140c000d40e480d480d01c0c000c01e08440c8020781762011504400b0501c0104c5070701052801403690120f808000003d12800d01e094603210b10503620f0f0303042d8600b581c05841c61003140b03240c1c5c510038000c200342c400a036298505041540c0c402000c1c01d90015040052144010403104da10760010b1507a510304001c90180d10780c05074100c04a401c1601e0107605644e04403440c640c108001e00c0c48200c0200280a1358008034045c0401a4040c000c00200d140701061701004120101c00040c0203542100403038a042c10b2508000e07008100e43d000c1556040c22420f01502104a0700088072092400a40a214483e1070030300121a86294041c951354041c0d000c0104010044c20304d8090700c0030718040e = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 116167194 1250 116165944 116165963
    0x3030f0c070f1211010510050103050c0d1a040e0a0302060a0f0608150604060b040608061507051e0606010804020603040303050402150a0315050f031005040302030d0608100f110d091e 80
    0x3c602500440c0006850a040da0502e010410243c21656070881124000e0130f01040e02d485104809190f030042b0075180b01c1c0503152171843c1869041c00c40d0749480d003001c10ba8040140d407041074101d1b6240c01c07440350040d02580c0044041034103c0c1c019031010b0f848428242c800510940c03103961560608050040c01c1c44c035440c604081c444149400d02c2070030010810a03810f40d1501c0d00d4450017408186c03004100c54800d0001148018090000000315401207a000c410394003107141045649a0f000001c4602c0c0c00d0a103c0c240c00070b072095001e4030569000e5500103151604503074543e40e0440103408014001ca030481a05800c40022465407005005000c40e103441c08600d4480000304125004200c0d442540b01c0e005105141c0c84640b00410000c11154201e6800b151680e12410242e01e144103034030459030810318bc224002040f0f08003150845042d106040107001c000d00301080d4000b0364100d01d0f04181804030401c001926054564401c5070000d108420010403a0446118003018590141c0140d0b5181c11 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 116168444 1250 116167194 116167223
    0x33a020702090a05090d14040306060b0301030507060c02010e0913050337080705030405212101030c0b070510020d020309070e1b0c0f0a05010c090e040503030f0c070f 73
    0x203080700c2c41903001c00c49800401191070b0544920f581c031803100a4240612903210040b501843c0050200c8020316040b0400307005040d900d15048943d584244000c0d182c1d40151b407000b080305480b6285592145405079900c1c09945a00c4080241042001c0c00c0ca40f60f01040341548800982c050000e02807103802c9240240302840b41c0c0901410b1a4150354125510000000907600103640040410341c10540c0741c42d0068030380d81d480c5041b80ca00300c1c42414014408501110300101c400091006205d010760880034038426101080381402200803c0c04010542c03183c0c074000340b026031605030180442d24042c034200d03aa591200b0403890101d0b4402450141419000000c010105408118440040140244520b51407034045441c40302408240c00004000000082c08014007104106082a80404400781c8001e00380070300d4141d00a211f40080792020030303408a0f001450b1101403000610581d0007502035880c44d6a0b48400e0481524000c0440c01118024003481010840c1d03030701c440b8040b51042450700e04000313 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 116169694 1250 116168444 116168449
    0xb0406090906050d14071e0f170a021302090406030b0a0e030a0e130605120a030f09030c0b0307170103060f1b0c0b0c04080111040504060501050c033a020702 69
    0x2100e8200071241030414a04225545940c1c0b02d840d505608134207100304c60030322110740f00c0c100304117903200c03d41252400c00c000080600d208805801c0710b810010a2440c00c0e0341d00401e8080c18400c103135004160304088500400b504062591000442c4103030001480c0000c0040001e041326025042074828020000030041840440c1c40350341103884041d0300640c10001c2d203080050040c1c002c0c1d075081d405664140c034071240e103624942040014160003010700030403d030b00349541340d590344c0111001d50014407010000c440131801394080d441901d0b0001800c80d4a24100416031b07040303a001504510401c2101c8000054403880c000185010b10720654010802e0a0b0518242040ea203149000d03854210f0940300c5075146070307082240020f03426884441801c050355606080740b00d41c00303558070041c0c6550030030003a00b0302c140ca000c0003002a590102c804000641d1038400444082c0280e40c08140940d000700146520240340d131000507224200d0f4500b2107003205180d416500716080c1c185101c0d01070354002c1400000c43c0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 116170944 1250 116169694 116169707
    0x1805010c020a02130902040605041107110109180e070801050702071e0501080a1a03030c07050103050c0f0a210c03050106080a0e0304231801050102060a02040b12130c0b0406 76
    0x80d2400d20003818114010780004007410800c42140201c0d981d5850220300b152a1608120300904005004000d0382c02c01009280080d48802801c4038006441d08820300e696004154010a58080b0b1580c4090746020082d1400104210360042e62030b48a00007000130f008009004e0300e403084005a000c0c214082c50310580400313410403012400c100f8088120705124a903400800d059000c5850300010580760030200c1c20010740d4884609039605800002020785001000003815821542d0a80c0e08001136074591294000c0c5008812580380086000c000c4641d4140c8160b0b00c012480c600b058400442d4001c25600008441214502c4804039898200400245420500380ca6001c42c4582c8148488000d00034803070741364842c0b0b000d07000c16140140300c2c18010700a0440c000000810141c603076030f4003c410202400004a091023518010310400c1c000030381c07030215402a030b021501e02110603030a2000d459100703010310500503d2240a803c02e13403107040108151809a80013401a00803c5036142e080c880c008290 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 116172194 1250 116170944 116170961
    0x70c0b0406020303041e020d210c02100e0a1203030515190e070203040e0c13051207060c14010c1107050607020f06070804030206070602040810051303110709180501 72
    0x21004203100c200056600441129480703584200c01c0295038801030786440c501c46070041c02030340002c51645040d08200c00b04a082c1c07006a5164210030403202190700403540f0b418032a0000303402000c0c002c040302e4480d0081007a40e0b0b40c984018031180340241c80d4400d0a46c0c00c02c40b00015030020f51142c0c2804041d242000b460b4031011800d98450380c4c11100d2060059490103030b841401c0340d50b03c0e8000014070382403003481582c01818001c0c081d0125410103100c60403244d00180c0000b00002080380000070f0a01c0c000108616011100014100706454280d0a88e1000c2c00719109a82c40e508020300c8200e9681d00b845400403445a585600c2003c41c815090306203040340c1c2d42c1149005010421244000da0789429004100c48000c8941c039665440616041100d8001c5030300080d002280032400ea01006215005003054852a2084842c5000f0540000050b2001520840c0703042d41c0e1184a00302103445000460b1130205c0c0c0350216041c00d07544004d503604442c0b501d240780d550000d40c201c103501044800e000b000803 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 116173444 1250 116172194 116172209
    0x20907090305150709050a030f020307060318080a09120f06140c040e0603070909030c1b1a030714030a06080c030313051e0301140a0b0d081801091505070c 68
    0x100c950860781c405960303040348140c0c0420300010000040303400d88250303542800b070200900082d82c260394a24001d40c03803030030480c0124805d000e2060046600d0380301c0d20a407004d90071150a0085182c07215116401140c0c82442d0310400c0080180780496000c00141d4070b066164403401d0a44141452803c26a040f2540004400d00607450300d41480b1303051104da002d5500b624141d0402e500b03d61101d00009143c1a00c5030700c00c000c440d00f04030014007815008080b1203421402023060040f2540c01172090324000e001409180c0081080005006020907001c01455002426003080c6a40940c0ea640ba54030703941040f41c030803241a443c1c810500002205010403180404141c1c000d45c1402c0030b10210802504040c01f419000d00c2c6112107104070030a0458101034543e401130002c10040b01d1a40f90100c0c040c2d403c4a46c5200d5a0801181c1300d42410070300c010800442d0003d403a01e040841c07003161880c0e142e08201070141040102103021600344181801d880d0480d03800d032a802e541d1580c44c5402e20300321046900140 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 116174694 1250 116173444 116173457
    0x5010e0f10140f0301090506040302030c0f1f050604020d050a0c020705031b04091704060503010509151f0302040f14011416020105070f060509060702010b030c0609090604090b070c020907 82
    0x400d16949440d003400000f15001140103880c200402e0040c041c00c0300260041c45004140400c0c5030b00803005102151a40003540c001d101384410301640c4e58454108100c00600303000780c9024a94031070784100d8101000034070151400b000c8415010a55006540744005a980c95500e241507903010005c80004000590240c91804010301c0c003c1140900b140003c0d011b41c0e10b0b0002581004840e005904501000406c00d907111134481500030100e800034011a070040c003000000c10b036200440b100c485a0350784020000d10301c07400d8019201c4a54901d03100e8a0081c0b40c5c00344000708075456400d04100281110300450341c8107076118030004102d012000c0321006640410480740e00e003400e103207002e1800a502800c1140c3d85a000349420702d44440b1411010306032510b4070007409250710f000300b070407402680c6030760003400f48409480400d92180c10620400e51b1111040090300f0007810700c880a0b41e405000104001410021070701c1e294002502103450000040486002c84210714002400a0b0400300720316000 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 116175944 1250 116174694 116174699
    0x50906040603020901090c03021c051e04051c1e03230105090c0c0c0a091b050a32070f1e080703050c21040302090a0213060c0f0605010e0f10 62
    0x7940c4130406000b042003840d00c68a0400c0440c2c081c0e0100c8244e00e0150345942d2038a085d819030710b4002c0c04195a903040e00d07010300101000781c20700313510101d004035005400340121f040000d4160300d42180d8021340a0501c1003501c204010110f40801c0051742d4641a140401c900d582c5c0c0d0b1115414100d00300404645400c414010b100da5100c0890450b8040c1950100903a03800d80c41c84400d180c5901008000c1c0d12565080f0b0108060389140c10001c009125005000040326a51070192124019000d000f00011400c00c0c44030b00d81000c0410341402307080013029800c0c0380d0700429800450b07980309000c1601c070f609030300007000204882c030321034035482059141c103200c0b640c2c1e416500c01c1e40900c20408040c1c10404003040d101911403080c810b0015110f01c0b280300b80c0c41e0300d0141d8503807405504548020b0b48280d03440c0000030700c60401d130b00071920b1000303029014440340d034140002600d5415002c0c0080e036114410628600015074a4400c0c24040c100400c02c0a07000d24100f0b01902d03682d00010804031510110140c00c = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 116177194 1250 116175944 116175949
    0x305090111010f05040609020306070e030606040c090b030408190e01050d0506060c0d020616020606030a03051b060c0910050a120b0301020c060c0a03060609030c0504270c05090604060302 82
    0x594004100900e460300307858a001007007901401240e254011801d1030030044c48200071055002da03540a1090301603500c50b95400000ba030302e851021440c1c0341c054114100148003481c0503440b40c0840e091324240303198100d0301c07a4454019074200315403c0f40c1d0301070005401c03400d007a1555814800c12006140170480305090344002480c1740a403c0e42c940e405502c490214080c3c1c1c0e100d10a8481c1c00c07200d40102c40c0ca8402d41c40d002580d40b04e0544100400c600c0c0c14003040c20b5140f001ca041c40c860400070340180b042e41101e0707904880a9000303030351400441e680315466000000007401940d009601110342103480d0700b800020040c80000a0741d514081c00410400c2940c2d007034001e19850020580714400058460444003ca80a0310a01c1510780d0540194405c200f61400800f000e0011000d20b581d00b00901a1908010b5035125854003000d0540400f820b000c201e42c0c80c1680140d505410300c0302032420031085c0700b804440d2000d203004044540c07008540003840241860a00183d1140e012141441141c0c40e6801 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 116178444 1250 116177194 116177197
    0x51507020703170d020a0e0a0614030f0603010b03070312170910200d0203010f0504230403030207170a08070207060f050f090a1e12031407050106030c080102070c050d0305 75
    0x1040c3c01c031400c10844a0806080543c1d00d10032411009650f01e800c10b00c40206100e0a44c10740314403808003810041101d510944c180d4404990380c0054a2940e152075090308170b0510000d00d815859922810600c07100c1e2000d01114008511610300fa800c00100baa501801251011103541900c0d4008410050001000602060205030740300001a0040343c0321002401d04044da81e10800310940003400c059858500d0380194101d60160034225050f03600d4404100030741d000440d021840400369541c05580300a400c45030398019201c0c0c2030040c54640207680307420400d1107511494140400100c0e942150039000340d289544a0361328030281803410708003400503000d009101c84450810001040c12200d84611004990100100401a0391039580c5c0740c40f003204e510200c0305450308065038240001080c404041c12114036070b5068898030101d0000880c82c0200d81c11a4500759010740d03e40c040000403071810050700c03002e00b5401c4005030380d4600c1401c0c00c400c250110f0f802280260040f45460000c07951020 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 116179694 1250 116178444 116178449
    0x70b01060e0f03070f050901080a030e1003060f030b061809120f0c010e010507021006080604080c011d03030916030507091119030212011d01030602090d060510030515070207 76
    0x520144400000340880c0300d41c14200c0c12183c052003052004140303024007412030000c1301d0b01240c00c0c25580c0e0b00e9020561301c8401c54080180440d00e01191041103242a280895141085280000740e840e5252401050909182c0c01591850b403514140402824240b03001d0f06425602c0950000500301400b00c0eaa844101044509500d6804200c007803074a101c4c3c004580c0e1003403900f4024009005941e140d80c1c0201410b036134050151043c11241c51950900b40680b504454042001d0705055940f0b88800015900c805840904d555803440810010705071880c0341c19070040150000d640300c2c43e000010720324002130303140f1045804c0e0000a0800020710300094400645600781030202d8914550001c0329454001d20038005803400c0e6002c1c0c00b00316540d150b401b0304448510032500d0505a643e82550810b03805071240c4803007001103102c0c01030000c985150020f100b02240a4450604240c0c1342d04c8943c00c860060f502a061418085410000c0c44000c0103040c02007608072a00c0171a07410580c3c0080c1d80c401091 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 116180944 1250 116179694 116179697
    0x6121b0f01110c1002030d0f06080c031203060d240c0e0604080618010e0f030d0c050306010f030b1504060c05010b150712020c060d0e010f051e040501020409091401060b070b0106 78
    0x1303a44541080c0d03c21700544a1103036a00c401440954031103150100074003094050a9031030f204650a80b98203280000780740e40d24000340d0a8151075030329440107101d243c50361044165a0078044101c04840e1170390003c26004200b800740d0000802c031103407280c01030201e0020980e0a04c944002c0c8818044e41d1303400b049071500a014542403015880031090b409001d40b0703421028402074040c182484280c11008001004000c440000810410300301c00c0c015201b9002c1a01d180740040d900130b000c1040306000380e01419411100030f11405a50000340b88104c41a8000c0e082000010b400b01810410840c00340521541e030f00c00bc50301081210b41d100880d1840b401600b00c040c00742d10132141c805080c2402486200386460f4082c00c243d030365070561170b4040064030000702d00800d10742c47e02d005c0c000180c007244101070049050165407810126680c8001300300b180080c1c015242551701f0440000c000e8128481d8400d550b00c0b48500984242100700501c3c21645103034080035070341034200000c03400107000f54034890544403075 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 116182194 1250 116180944 116180959
    0xb03041b080f0318040908070506041a0f180708030d0b0a081203040206031905010e070e0102010b090a15150207030c0806010f0b03150405070905030c0f060706020306121b0f01110c 79
    0x4d010008014088803040941080d038000303510000c0c0000440ca2510a5001e10503180d15450685406220040e0440f0042c04810002c400b00c3c1c19940c1307101c071841d0400c0e9410210741e0700980700d0340040c0c02c5520045078081c813659599034224050914055110003007d698000d018104403204020701188002000203200308400030028104604108060b0610300e05e4180c100020343e110450741c0c210030425900303071700400d84820903040c042d0303c1400741c040242005051141c003510f0390340c111703c050003203c20b52400342c52042d00003040c0280031544804010000e94020f280c690310f5030400c401021900d8010a2258210400502031816142c519108a500c07820f516a81c0340d0301e1b02449202481040e4455920130705180500c400c29520081031403c1d500d084054406083c0e00f6420082c202e01d0f514082d641205003800400041210390b0b0107140c1c0000c01a089c0e280301340c0040c0c011424211810100c100c88015484112070301d041122001c110f0032000e007844c00300c5040f00003580b652400340c0211f80c0e01c01e085 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 116183444 1250 116182194 116182237
    0x903050c03070308151c030e0612040b040c080d0e01050f090d111302070312150302090c0a0212030c180a051801180c0c030e03070b03041b080f03 64
    0x208404442940d16600c0a0325101d035640d2400034040501690213240001840d2071070b102e1841c20841c60f849101c1584600c089400e15903030107803000391070b5100540c1d000c0d50500400c0d039043c0b000041184203d00c1501c000c1d07082c1c501841c103d04a4840e0760043c0b01640d002e42041440d03641c100300c84061104c0242041521000c145000010074030901d08070b5504580002e1022040002504d86c0840d1000112520340c04490700d440d000d8200d004955004d4000303482c12a1070201e180c140c0e07201c60000c502701074448000c10f0f281e80110381c040a003620344800050f400a10000d6880c0c1c10f01c04038190003c14a8030a244d802c02d9184003150780141400360180490012242c03c241e555501000e0040c500903000c000d6510401031824200e100074400e4070102c041706a40c80c011904a0b10490302401103544441811100341d4500700c490305952140c9503010721030307801c021510b101d514000d14881c0d442141c0c0030011021040d8048044c514035485580e403640000c01804107404c2c08002d8400d40c502c2101000525807 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 116184694 1250 116183444 116183447
    0xd031103042103090b1c090609060e1b01080c0306010f11060c070302010f060b071e05010f020405031509060109020a030b0607061b0c0503030103030e060d0f0b130608100903 76
    0x811075000d80d084a081800c1c0c04000e00400341001e040a0080e20b50341380c0c0555401c08451544180c0d0100c0c0002046100001810000faa202002e024004c040000b60100d040d913511088410241e001841e903400044039050803400b504548203149000e103003180710350901d400003102030701000c6e04080c1440281c0318026103440c41101108803151507441100d426050001d01c19800354009003080c0d0040d424080d1011410700940074110449080407501450440c80e6107810f5900b149001e850a40e0a040c04502c5010680c24081d159101080d4040103035500d18003001c16190030750b88072140060b00101c02c00c1080454010030031504491010b000940c6c1c0310707201903040f0018005138000e07541c030078008501c043c20301ca5076030b0000e802460200442c18000881c4002030b142030001d403000800c0c44d8810001800064030030301c0070131951140540800c7c2030003075407040b0f0313026607138144c40b032600c5a0740d91520010380b4501000c800b00c01d83c42c2560200503060030002c6d1191134402e0b5045464080f82c407030552a0405 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 116185944 1250 116184694 116184697
    0xe160e09073c0e090604020a020f0102040f0e010e150105030601020a140105180303010b070f0f1a040b010b07080702040b010e031c02010b0402040b09010c03050903031b010c0503060d031103 83
    0x30340c21603104003008080d000039842e6400c0b251068101c02440c00081e68520740909484107044000400480c2565503200c2003001962006076020214080d0140c814800c0c1024006040a0040e206102e2009030404c2d20028000700f05030b002c4007030511400b040c007035003595112540d200d450082ca00707695a80e48443c0183c1c07411042070f000600100c035942da11103510744198003450007801862007014404a007011403560342e0000307001e4501d0b800400c10040000401c0300c540c02040318401c0c4d0b2000300c041c032076450303c645c012448640000405a100104070400a040d9510b50161050001701800c101c2142c0303a00302d444c0107800000307002e03d6035506c00c440c8581c0140762036584c1300c200808503529031030b00ca045400587c4600030110055820b16280d100f49252078000d07074050301c44002c09c903400c210070880112403010501c00d083e0184001044100e02c80d0301c1c00d0000b4030f041c200803d8101780c00881e403902d40b8211900102c240080040a00600a0783da56140502041d180c0519103049084030781c503109400c5 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 116187050 1106 116185944 116185967
    0x40e0601080d0f031d0a0203010e03040f0e0606091f080603070e0c03060f1002010c090b07050703080714010f0c0e0a03080301090905030f0a03060e160e0907 69
    0x60301ca283c41c540c60344801c1c0f50105111007410840d1440403190003d00d8560b0300040034030025402d090140c0b0039a110460019440c15181008804250b82c2d0f600400e91684000d10210b002556290103940300d48400501c056035843d445003944101c030702c07547c2c81c0b01b010841c0c0600041a914000c00c5220456600100201850b40c0c4c101d04e101c9070b0b50000b007216a00c840030240d00103058072084810b1035440c0c0c03142c00008d8080c140a402800c0443d90b5448500141801c0040c0310005002041000c1242d82c010029a180c9546113400040030500e84540c42d070300d40c80d00e002080d4510458022500442c150340303c1e00b0702244a0300a101c3c00400310701018000d44000c000411003a4055404000c0141c0240b040e00e0a000d80f20020400542c808501000000c0c0c071068140550700240e0f62450308a00550101d10601c0311101010300703030700d075000b11b0301d480f44222030300003000c060144444d08003 = true := by decide +kernel

theorem cover : BRFrame.Cov 116007194 116187050 := by
  have h0 := BRFrame.cov_init 116007194
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 116007194 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 116007194 ≤ n) (h2 : n < 116187050) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
