-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4713
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:29:59.7937+00:00
-- url     : https://prove2.me/submissions/b08bcfa6-5ada-4f55-8d54-0916da78a034

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 847482014 ≤ n < 847661870 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 847483264 1250 847482014 847482017
    0x109200f071407080c120604030e060c0708070b0a0806010207031505100e0a0c0917071719050c01020c040b0d11040b0d05150a02040608190f020409051b1306 69
    0x41e90604101d0320784034801e10b41010a0544605507500e8140d69191082c1210190003440400030902015802069942c4a01e9050712102c010307424141c140040c0750008081051584201240464144010000817000781071480a690f59000b24580040000780043c0540e03040d0b5000b62414400520294040102d104110500003025a01c43c684100031f00002d03808400341e1000b4009000c44210b01d40c01540f02844581c940c406681c1d40c42c10710036040300040031903402a8000c19014030425442440401707101d9500800c407290603040100682c0503c4030311608407502c4d4400c2d1051592560103022a40f50340b003084401304400d011100c085407280301d40c03210040003962501c0e04000300340c2c2c540e48015001c030b001600c0d41c620901103140165403036808241128070b81c04c080c40054900aa18002c40d419100aa65441c40d0380d04c03604101203102c00c107901d0b0840301301e4849500304900090f03031011300010b14403644040341d10700f4029485000d4512000d40c2c0441090108850280740058900210898485 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 847484514 1250 847483264 847483267
    0xb07030c02040219110c010207080a0308060a081c0e0a1d060118090603170304110907170c030115140405060904180305030610050304260d050f0109200f 67
    0x788002802403140da6052080a4a19a22094400c0d4402e010000741010481107910a50640005a03555400e0703102d1070215500000c085070010303102d8224280c1000c80500039003600c2e52504489e03030500703014a00083c03d2100680545440d04c0d030003070009005040945071151041e09101640d07551044c8001d080d03900c0001d00c00818050b074880e40b00841e60a0910b0b4a116200d40c440c80c002010b044103120a48202a1110407030012020850031a0301499100302058500e01104040c080d11050042450b030502008a00c02c0c81142e9801501c103100e241000403065996060400c0d40c0e81050403405560104045c1040c2d80b80c000c1410070841d016620115807154860002c40c00180282c1800d02803240c944002c8903140f0200741c0c200000d140112011074250500e104280c10484150100b2500900f40d007134040501c01c002402e8010100c051000c988440b403420060740e9190003900d07410307075114440086440c0100040e0142e481003502c10502122a81d80524414402d4205030181c500089801c680 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 847485764 1250 847484514 847484537
    0x403030507110d03030e12031e06030f0105040602120702030c060114061b070f050114160f02030613050c0301200306040b1306061b021c050106170a060c03060b0703 72
    0x240b400300320380070940241100010040b07890010003503c0780c0513081145100f920401864554011f003541c0c1309075080c1c2c03000302219030003d00b00502108058149601070003200c4460500c24801c1c02074520640c0a040096a98072110115406110000f0018021504240910f504402d00464214112107522840000803c8102c001400070b10844007400e8030314a80e01c25890a00d40d01280d010102c0700c15807a0402003965800065404104c540407000900d03204000c2001015044c8040c1c0402d00d000e0405050036610550109203820000e548118900010407661810018100842c6501031001e0380248845402d00400c44030400c2c0c8020030500145001c8000307100e035145c81d4080c43c0c548070000d0145411030503800b4080002e0013907008803400141d44135400320f50b804584c40841c402544c040e00903803808204401c1135080400c015000c450b59500c03034000052020314440e4107801035081101404001c4014504102280d5000408006050400004100607110300096070726940d00341c02c04040c1d101 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 847487014 1250 847485764 847485773
    0x3150f22020f030c03070609090e0111070803070c021c0606080d0c060b12010c080108010c050a090306150906080f3319060f15170a0b19060203070515040201050403030507 75
    0x228040d518a070141b01c4c10600080701603010000d501182c0d80110204102c8118155003800d03980c0b01c075000001c6500400400d00044c014800640d40080240313420031a5a41079070000302442c81003c13030324a1421400e0320060a100c10303446840c00801a20006180d0b030720050f0400343c4038030040100642956983c040c0b5008945440c6043c0180e810400d000f040450045c1501030240d40c401c0c0141810356291001590919000d0000c550035044e4645850b0012451596568060800c1a100c0b0443e00820280011012254001c1e20080c000e448081c0c4001c40e209040c0c1e070b18101040401001400c004010101510702e202000340d5080391041d90003549541e00f40410b10003803030000685040038035003000002d10480e500c801d4000d6424a142c001c40350028080101d80d503422a0740d0541000710f406002c54440d680c0e030742c007014004802034140c802c46a40050116a01e207415800003000d40c00008801d401c2060612424004440ba401d90700b0350341c01d142d00000c00764001c40c00000c081c46400280c050901 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 847488264 1250 847487014 847487023
    0x130e2109062818051504050306180607080907030b13020d0b090d0503010e060d1a09010b121c030b010e09040b1005090c0a030506010903061505010809010b03031608040503150f22020f03 81
    0x180000b03011a01a4141070401a20110060302b03104014041d040210301458400da480902036085400200001811602d402c0318143d006000c48a03064112404038005843e240003804000780030b00c0d401c3c0c46ca85048030301c540c24840150300c0703041002010030060140c02e10403810381d074008905580b140307505030881c03070000408045030140605c4c0320fa40c01d0030441d084e02c054004100e6424142c1c0c082d000e003000403000b6542c402c00b07400c0d94060782260702c4012680034426880351424150500d0510020030302d400c0030403403130308095400b034848042900410074991030244265000b0001668548031520780b40d81c440304140103841800040544660100e1400c0c0e1080d445500a160030a10402021000720b4100004614522805000c84c900f000024420380040c0701c1c40400035030180145252071154442c0304a0302440d000111140e40c4244400300344c6803020811210307846070841d00b4036040d080030004060342200060071101504021121024100070300c95880790890741c1510050242c040000000b0b040 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 847489514 1250 847488264 847488269
    0x21070512010e1506010507030804210302040515040e041506030206040b2101080c09061915020106080606150c0705060a02030702130e2109062818051504 67
    0x640540840415181903210034511035202c8100c40322070711030143c81c003000301c42203512a0101d2400d021400119010384c0c00c00380c0c4144503105008a40072610300d103100001840301003200099000c035003400766060610500080c0c12040210034241894044248020300740240000c040b1403040c3c0240300002c10302e400c40006940c0c01803081da15140c554101000b00d0b000f0700201c48900c880d0801d071100341c92003a00213a05854900002d00041e11070b20087c4100050060201c940000016001e050040400c90b105c00180100d881459114030003501c00a09461103500301c0419a00200284005c03542c4140c4410620080180740c01c4c1c4a0700c0d154800c0f41000c0059000c160031180020303d00901a03404002060070500c2220340d0b6030000055440c1804686070304600d40703040d5025001d801d41078490301d40b110903200c120000e080e15090340760000c0b448980140c070010002c1da048102c1c05441e82003011b1000069a4149804001c02c250040445400c110f148107090181c15136806c002032801000d81107502 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 847490764 1250 847489514 847489519
    0x8030a0f0e030307080a03051f1203120207030201050603060c2104030c05070f0618080c06130317120c0a140d060f12020f0604181d0f012405210705 65
    0x4588030981050345c401d41c80f10080030f000a280030001003d001e68090364514080c00c21a18005a07414400c20a03070b080c242d20301c01d0b42440820100c03100305540318001003040c24480d500110707080c208002410328100000d801d170a1460021f0100d44240303582031905442e09040816011220340b183c1c1020b46d0f041440110184c56401400c8001c10003079500b50590084170981c5e5070b07a602d100d0b0281100c0b181d0007414028903049422007040f01000b45001c90103021000b098416550b407840d03a95984880240c0c20b02c20300b14000700c02042c2d90086145005045030b00030b10384034825140c2405107200900c03114200103890b080d17880214141e0360540456000c240a080b01404000c0ca451f21522401c02004034804102d12648208044001500b00b1405540444170030901d6082c840f0aa060000301600100380320310620f201500e4104440c003c10068031926025120002410040c4c11081541420849440820f102c06e250001c0181c4e484400c01d200e940603c41e43c400d03180751480010581494a260706c081d5 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 847492014 1250 847490764 847490767
    0x1505030f060f070203070302060c071415150909150a1d0c100e060304170f0a0507060c0809100f020906070c060e0d030903021201200702090f0108030a0f0e0303 70
    0x4035544000980c1c01c0c007079412044040080c0c0c0c0c8901003242c1d00d00c2014001001a046080840c1b90b10b5040b00c040c0c8085441541000040b0410300807403407500e2428504900c400c10500144100010302c9810a100550140c1d51180e05242121105641d0303070200300310000c901105400a074003000d2a50005440c40e084182e0300c0ad001c0d42c46220a6550700500708000c2c4140030442562100c14003c015000c04440c02404441c00e658172501d40808184e80401c0c00007800100300308012090840d00000c4c0300708655a1200c546600407800d0100c1181c01100c020418404510700b40310300b0110000703420500c44950000031540c01100c040101c06800346c013641c15000304000c030b1840200042a900001610b413603580e000c400021400400454485c8240050b010580d00e00c001e00150405500050a40c449000082800c0800b0032103c2a02c1d29501100198208007003908011450b01d240c100c0d400401180c89003000354104920700e500c030312a400103102808060a061481940105410340248500500f40d0303 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 847493264 1250 847492014 847492033
    0x306061e0620100b13062d0519030b0609060310090501090c06090501081501082409011710051e041a1014091005101202070c03030f02190303150503 65
    0xd07000b13848241d0040d4420906a503094440c0a594411700c0c0c00c4400c290300c601a209a40f0f089441000b000540000070111100c1c000b0072541c031500d542c5602c01591000051449145040181d088580030f040e0038442d81ea244180700f1150740015190301c1d0501d071500002802159468400e0041c610000000c0120040f6400050310907001048901140d0b801c0c0c80e0700705144c2d0740411310140b9000e05c20071540031804003c0411402203020031036040c0c500d03c441003a03640c102d50400094404100b603010740001814110a000070100500c00104e0100703107410f041c0481c1c10070000807001041c12030440300000c13035050001018010b04184a1341000c5020754540740504013404070718002c0344603004450410060780380c20101030424044c140c0c402c4e5900380c074400b100c50820b42009904505c4864890401405110003040e5138010700c0180b5401d80316240c014202451071402034224180c450b001800e64000c01103000d1089186082e02111079494600011302111220400f040030b00240c000c1ca82600c6200d846 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 847494514 1250 847493264 847493293
    0x31202041a07050616140306060408100e0f0307030801170a0c090b0405130221011b030e0705100c1202071a031f1d130206130306061e0620 61
    0x51001d42d000302e044c0ca01c81d540300041c2c1244103802c0803c490002d50a4a400240c10360001701a58200c8001019649010b42e50300960f4541704024021450b07040c0e650308601201c03507080001e442141034040c061800c0bd502920007405640051103003000341e80106c1c0c0703502c11005c030500000c100c883d80003c084074041e4482d0201001040e40c0106180168036001c04102d031072401c00b01d030401c07456000f06183c4104100756032414020311000183c015540d29400058000070000b03040c0740c405552503500141d81f003680100726140490b00c1c0e21544c004c400c4000307100340465000c24888003054000700c2c030500706040440101d14142c0c8952180c0112107100750541d00713032488400110b020b00082e1590780403401542c00303d01c180c02c0b0745120b030406200d56041e2941e04151041c15840c0c0c0708140000d048008401c03500896965030101c1252001c03c142d0140c18020080940703d000b0203001e02e042513002800d280b180000d5000e000d406400c080c01020907021248480e040040c2000d03004007403e44465130a00c198 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 847495764 1250 847494514 847494517
    0xd0e06160506010b1c05010513020c0a02031902090f090a1202030408060c1b010e101a12032a2e0f0b03010f05090318010912150b0616031202041a 64
    0x82c0d6103604c48143d901a4445ca50b40c025141a40c4c0300810070b13420329406e0300d10351000394031142c800310180c0500661030000d0baa05000581c51403c005204007001320307152041017202200248080d088131443d40a10064102c0003450008280d40000d60401036060003006030301d11b0240345d00850b07007031044808100c400310071400545000c0a02a460b860002d03000f0003524241c400060080c41603504c00000501e0091f49a0080400f200b0560703406c0700ac0303011060106402d0440c03100140555400081c1f40d5500850760041002039400080b11691560880400c05807503d2100c030360680c0b40119105400000b04050b41d0031b084200401408000c005030403450b860181c00d4080b041c6110f5480d00060a984049502074a032003000200d024510b03051302c1352202d003182c8482c420307403034100102c100d00440d400c10060881809140580c1040e20440b19800c4403a05a40039a1034150040e2014480c40c1c080100480b030741240140d0505104c070402940b2084903000303015981c02000f40c02c0101e071140004000020 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 847497014 1250 847495764 847495777
    0x60105280e0903040b0f0409062403021b011b080115020c010807121a0a06050412120309020d0501050a06150f0f0e030a03080405010f090c030b0c1c1b020d0e06160506010b 75
    0x80c0c0038800d0aa03180d60f2407010b0046007000c3c104c44081003441002b4603200340c2c000c01600168504103105150504806400c45451a244d444203822a0b0f103001c0465411100d801d004000400310324200c4c01e10140d0007912403ca564050f8144680c0401080344103000b164581242040c3e01e504015a2940300b940d05d170b072048451040e40c01840250000b00c0e041380f00d40100c406548600c030100d0082d0765255100020009a520f60608066540d0711307010040c0e41d411100c0c01d07424061000801d8608182070b01004a4140d613001c0b09161541d0040d400c4025040ba40d101e004c140310342802c050442444006030350038866400780c00c1d850b0080a109008064101d070840740030340e014a00802c00002e8256101c02284c11124014020f100e190000700001440080081c1d48800e05481d840e044c1451503503d0400720000c01041024181c4981a07245060516800308000c1041c030b10040007119a0114040e01c0c1c41301d180da00d18040c90b030001c0c3c6100701032090103408801c45c1e44101121415a03491184030281e40084 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 847498264 1250 847497014 847497029
    0x1515091e0714090f061e13081f240b0703110a0f1502070804030602040602150705030105041830090e01210f0302060105280e0903040b0f04 61
    0x12000c01c0c0300c02d219006141c040d030640d40000740303007622580811500888035003505a101c0030400c894851b4806100c40c881c401d004101415488031b1200d00c22405648094208907102c1c0e10050407614080c11070074807050303261512500018462030545e4001400748200e0303401410701d1514900040c001440d500104408c0e8020307519401c840454200e419107450b815079001c2d000c03080d034841903008211208040d4540c0c100704200140b40000941d80c0b00f0303650300654410b58804d6400315081100c91380511044000030190000644540340c145c41c0a0f029000600503035004a58400c1050034031621141410703c803e400410101d0400c64224105401c14455414146041c0102500d882c80d103004610800c15944007210070f005507800c040d000750542c8007480600e2103c00c994540781000c24080c07207005100c10b009501034002e0390304003802e0100200c0c00103450001c03d40d0394455002d1600147c042481030b25841c8021207410b445c0d45c2407091460050b6004604141400038001d03000184c0c02000344229101d1 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 847499514 1250 847498264 847498321
    0x1605011a0102010c0809150c1201030309051e13020f04050d05061e070804030302090f10030501060305011703032a0c06010302030705040203040506070c2105090a17151509 75
    0x1024040703940f03d1041e03403000c4065004000003107512031140d01f96036102c0005500c8074100307902c8502d258041c5038281e0090f0045114440107003c2c43c1080700310b0308040c45109615000f101c1c21500402e103a0b4424080f01c07544140d02007000c0e050840300801b100d00811780240704c400c502105040450b03d41400743d622100f03c0d507841070007070100088000c285215031800e0b110076044c2d9a89840075000f030b40c08502c0c1254440b01907500d060309540c0c0d007a582e01c0790f02e130f0301e40c5c0c00902581403000c0a022100c0c1a0044601c10001c0e500b54a0301b0800002266444200c40441e110950b020070035400d0740350812411103000b03440c04142d910082c0000a0054102c90003201200c0c0d890750344201b440201d1000781e5001d1708640002002507405401007981b221480e02c280040342445c2a50035100c4603801e143c0900c640041e600049140840c5009034216001c0d20300740c402000230700031442c0e115695040003004068007004013800150400c100718410b520101c40607294500c10701e006070314540640d01c4580842c0a01e40ea = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 847500764 1250 847499514 847499531
    0x80d0305180715050306040b0a27020c0d1407062307030902010512061206182a15090a0914070c02090628140109060f0c06021605011a010201 62
    0x90702000b2910801c09100e025401044100c9080d8001485039401a0b01d420f00b52002e03440d041d2036200208074940130b54104ad2440308911004083c5007840070201030040c403060201c1440480ea0440207882800c0403142068402d11010a034004d400001c1c007100c0c50050400040041001c5002c41c121506d00f07008129951843d081c3c08840361031001a000131782c1442102e00300030400102c0b80d08201d00a110820482c20340c1886454500200c8544229400501c174031102080308000c48080803044003415240314040849019061114503182880b03403642108441540301000200c1e8414040500700081040c2ca4028400c0604400c075217040d01c80c1074885c0064651441007807101c080760390051002805489050410203908907000740c4080c1c0460840d030a510702400802585d00801000c400803c8500c03045c0005002c0741d100381d00c40c42c10701170094400c5003450352051803650b40c0350f448000180c90f00c0000c03407540400c4001d808001d10543c83c29000ca000d0089100008a101509034020310107201d = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 847502014 1250 847500764 847500811
    0x60907030203240c0313050a050d03140610080606070f030302071518060209060c030d0603030807020304030519060e01090b180c09013f0b0f220309080d0305 69
    0x81c0c2c200c0c0c0f104000518001141c001d84412000b10f8200d510501030755804034144d00d4030341c20120000e2040710076a00905190784d1258141c042e04c840301000070500b01e0180740280100724402c0d02814150104501e000000341b823a034428060b500c41e1904030342445003595940c900940294030408003503800215118002a580b865401442001d1075150501d48001d20b040c1d88443c065040140112350002091041121a40c010005843c03004849079020034118510b04000d801c100000e0a070fa01150410001400454400924004d204201c400f042a0714146400c00b0401400e0035002c1100702d50034155400240010f082e001d90040c80082000e9486140c084006a550f10494090b00d420009140c010003c0c1c80e0454140c0d1000901310203444220701e45580000d4603540710203551804038050a6103201032041d41d0042e140d00a90211040b42541403039103400c500300b50b204000c82040d601d40312003042094442c204007002000c4040480b1420a1100c1002d0b016010889440d408405840400024203 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 847503264 1250 847502014 847502053
    0xf010f0509210d09150f140f04080906030103031805030c1e12011806050603010903081906090c020d110d0801030b0c040e0a14130506180708060907030203 68
    0x124000802040400c0d0110b9200c520720000d5001502a81c40c14401d4003c44400c902841d040f0310303c50350f288501d0081d14040e56084806c0404081e00180c0317080c12081080b0340721484180c205032080c1140000d641c45207084c1c1542e100d003a00180d00448040700002c201038001203010000c0d01e030700f144c0d10381c4075488005041c2d88101084c041d990000d07040c6910104c01c0000103600b0480240a4600482803000200306429606444003090200c0c051a60f82000d020440c460341350405d030110000c0c41070302d0340e0761401000705178007a081940300e001105072890994200e61001000b01540501441003245500b80651a0426001600c020601c03081c1c154089050200b580800c403034142d02c80055503401c5442ea0075000c1c1c40107101d41d036501c070704010202d841060240e42c90300c0ba040070000820a40001040141c00d680d0150412441c0800300030b10078000341003ca030081d4082078400c01d0240c51410182c0c101d240000300d90005403103002c0c030806d000c450800810180d003a82d00a0f0202c171031111400040c0c0c480c2 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 847504514 1250 847503264 847503271
    0x1060305090f1c021009142a0f06070b04030905270f0c0d111308060702060703020904061a19050310050d0201170708061302071a06041407020f010f05 66
    0x40d5044807004800d4000f505503c190181c21610441e008041038410b14411034191103019104080c60408400c500c0031304003c0a0040e1003661000e1600f4003085100810a00100d041d8500c9402510286881902c6980503105280c1d00aa18120700d401c080c2030180034100396011300c9020322031200c0c40d403100c403046102820500e06003040d501000d40d41c904040d402c03100c02528007803030b6400030001005540d580d400350081c440d0440703100d140d8a23404004e4140145840d43c0c0100000d0b04010100550941c020030660b07808840307400d0150351488600c0000d001851160000e00b2503042c1489140300b52003040002e0003d445000c55100c0b0003101201c41a9043e00048644500c8240041c1042c000c0b41071914801c8901e45c0b042c103190400c0112034940c4500120700f1204103001039081c0c02002641e18004c25a80052051203008500c2c103041900c0e0010b0404850480007d0000d41d48003043e002d4807160310600c2040010b103e950030604080034001e4032807e140307129040e00e40c02c0090540f083d226034443c0901 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 847505764 1250 847504514 847504543
    0x2b0b0f240910030213060e070f0518040e0313030b0a050609070c05120a08061806030a0201030e070503031c0606021c03090501151e0905281b05030106030509 69
    0x52400010030454000c01c018a4a0340c0345681d0100040140c07500d28100140c00c0c500d080200d20f0710b047c410b03030f440302100080c0740700d042003040128107250642100489a40000c1206168901000e400c08100900b0203100711614600c03001905001c01c00a0002e000305032403007213451070070310f440703031201310041d500c1c2560180e030300010038030108050a008201620415101d0400c0c1c40e50f10480004140580d08130032212404542400200a403d01d408540c405140328444008102401e207080825914126028000d0500d541d4880301c410014041010500404c0014201d990340e0114019040a140d10f0041a003034290038020049500390012510266000108080301f50940d51110110050140b4550a4406550362040c90130140380c0c072000c0e00047e120140040090b040d40e02d240c0340d181440742c0d100f00b001625280c280f080a80400001c03e00710076005251110300c840001420004000400510f02c886003244010380116400c003010354101c500d1740d01c08000a40d0b42c1e491407500d0700100c0005c0355 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 847507014 1250 847505764 847505821
    0xf060e040b01210b07030b0306090106032109030b09160f05060d11090406081c0e030c01140c010f0504120203031918051609061a04052b0b0f 62
    0x100640c40ca0351200d010746243c2c3e01212901551110300070440d0907200b42c070000e030b160340300d20030117040412038240c01004d900000c01229155469034000035a603d080801c42003204070f103e40c0468801d21800c40a1034120002040508280d402181d03118030314106000e0000700701200150040000b0101c0088880c00f800d49490144a402c070307100104091085e413987c0d0007050043c40c4403900c1e40e00c614805021940c0c0141046411138140c04001103030769103661b0070800096500d00381d03510045070000f0265400c0c01c1010758084091031010f4140200b02d0118031039860140c0c0b581e0f064203030740c104600030360260104100030107010000300d841e484102c80c0c80f510354040c0003221004015692158075881d4440342c83d40d031030076110340e1070702d08207124542c0c020344400c10701c1d03002d000005071846048002c103041e1040f010004040c68185000340914414a0f22407428070b00d2042c076501803140c40707640b4410300315013010740e1014a20704056032000c00e40c1d58240d072010500014603814a1840845c810020065060 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 847508264 1250 847507014 847507019
    0x105100f090c09090c0e0103050604270206040312030501091107050c24070302030711040b0a0603050a11070305180a060e04050405030c1911060a140327010f060e040b01 74
    0x54000d0300c07000d03400b241005207000e800144410f081c400c2e140c00514036500c40e4032601ea40000142500c0c000303490769100d02d2816008210004280e019118540c2c14201010340008a6000043c0d05009aa1020304104000e246070b0b80181d6141c3d1041d4160f82600400704001000304489089901032500d005006910505550460b40360050b1010000701c95030318603203102600c2d206c8040098110920880c007581c8041031610800014501104100b0411755081001e401f620002a6140c02240b10b43c00a0583c1c6001141c2031340d2241e0803000d1700710300d0800b60b15aa2209444d000f0203a51080d8011a18884140300d481d04628100050a044802d9540c840d51100c100a04000040a0140003118036200c10456a95140c5050160b520003850688a00800303001d10b0818504e16182e103070505200d100d0811800c0080ca8203e02d003a02a02c1e1452225600c950380e00840c40130382c1041c0005258070300707038400040c150b124054004034661000e00109203c600c1c0d840d6071003500c0c1c02041d10010003641300d00780107 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 847509514 1250 847508264 847508279
    0x303021c050322120f080903030c1603021005040f140c030709020d0e0a06140924070309051f0605120309060a18150806010804050a230304170105100f 66
    0xf4618075001d030682c010006603c0d51360500044840c0f20320f107011801500d4020109034000710129030010599001d9491864198119000b0748141c00f0b4440121012452000900d403081120441090080504000a09007400c101c0c020100031402200c0704003100306103d0b200100412418110100a0000c1c104282800d0300040690003407400d007064280c1ea40b6454406820030888085039a0088000244c251005201740355280c000034809092680320b21a00900600b9100460304510340b0225100c2c41ea450f03200c0308402030401c418002d031803403003461103854611002d2080b1980040c4520405c01c441d03980c400610205420f00152900c05400a0107240182d0400704000d00e03007110316290182d0301a0f030b100110384501c0010707000040c0ca04039010701346400b0b903080700d10b0030b80010003400d00ea00b851402d50f54031655580400c00051040920310a002c484001c031a21811415042e401900d4886840309401e0713200185107200c11005600b404003080201070264100b00650b002044059501c3d82071010 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 847510764 1250 847509514 847509541
    0x9060b0f040207050a0b090a15020405011710180f0c1106091504021e0a060c020109120b1614180a0b0705030a08070216030b0a0f1a0103180515010303021c0503 70
    0x152030044800100001e2710022001d0484a051000140c6541c1002c000400b6180ba4003d000c030581c0d809424070241c50a103030000c0c1c00300d0394015582502c840041c044080a0a06812508030441c00e16200516035500030941034001c0101c032040b170307200b680c546130910340d100385003800c424101c2101d101003009401c004200d0300030502080c485400742d203100c80c0400c6550010350310220008510300c112104560744140380720f0081080c2c807001c41c440141130b11041e4400001604400b055425441191440d500072070224002c28241111151100c4424081421203840d18100074420900000701003901c19801095511013900400114105980c003003080d20300080c082c040900390720a80c0840009899003c1424014600c03806003a44242004140002540e50300c01944a5090814220010242a903d480d081703042c1e09280c04914002a004807135480031004030080c0690040b41407001c0311103caa50301e036048074841d030308031101000b030040c40d6260b0701314003c404800945c081022540f40c0b044040d = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 847512014 1250 847510764 847510771
    0x40612180b0403020303040b0c030105010e0f03010906111b0607020c010f1704121704080a030b06130b07020901151e020f07060206070e030a0507260109060b0f040207050a0b 76
    0x80d403809100d00640311001600021602140164000010007080011082c0b0464000020079106401c65051030000303080710202c0f511040c090301e0750207844142683d00750071100c840c0781c00503420000d2108803000a5000d80c0b0600d0b07444042d00210701d403143e00312800035080f41302d419030381e0280c10302100c841c00455424140d02c2410b802c015840c1c0b20342130060158240309000398800c8401b24191142803102a01100c8007000501d05e5080c0030041202150301c000880342d000c2c0d91454002008449840018424003403052010080c45003070070003040b810020700042c121280210380046441e0b907a00c0c1c100210080440c111000035285d441d000c0d00c8185102e150000107078850040d111941c2100f00b81310320307041041d84000c005a01141c18045003d41010926400c400268003030401e1503015190159900e1151046902000f1541c0080364005004246401404440c0300248001400c42c02c007100a005084012445413680b1460700c4060b160030b2003101c0b540ca6014014040c01c91607529100002c5c1d1009 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 847513264 1250 847512014 847512041
    0x2070b181201020d020d050114100f05040806100503010513110d0c21060b0a060804080c0a021215010e090a0b07031806060e090d2111030405060714040612 68
    0x90444610007003083c005441c40c0030b24070000603169a114043c8009031030040e4840381840d80f403071551111a03154642540c0c0b0449460a01c00441448500c0444240c415a884500180151428040300c422100c90700f41c00c55108078000d02c2a51503960408106542d411001010300e0340d003c0c6002c00e241010311f05802503034047d48401c0401ca07600e91200c0e80798031110125191500c4044140c0c810041300d03104220108405896400440f070902c0b40140040801034805880903101142250300518100b10b00b560559001d0b0500040407102c04030a0758410715400080300f0202403400115900c01c982c0d40c813900c0f90041d80020070356085541c6900f0780095000e01941e04164a038034414841441e00004652018496200025058a0700000200301c040141040049400c280c5242d0070207580306580c540030032410b00f2540000700441c0c03030f100c00408158202e15a600808000c01090190200e0720910a40340e5031211001c5a80064000340b280c480e0f8081c0d100402c00644407480003100750750090208240c1c4 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 847514514 1250 847513264 847513279
    0x19020109090519112715040f06030c021c050a031514031e0c1c05010504210306151d030601030b0402011e0e0d0510110405040b0102070b18 61
    0xd4100da081503940450783c4500c00c0b40484140d008040c0c1a2003441c0551210200d0a13041001080b14840e58200b000300042101c5000010a0519a214048040a48a815007650741e03107698a0b043c0403038080390301c0b81c0c202003803500c1ea01c424081d0020401c5040d40202d1030460255554900d4140d03456080b40340f0b1641050b40d40c0c601140684110a6140094038281b041a41c000084d001010f00e08050300380b49103040100300031410301c8080009480c0350550000c40d6200003500e101107202c5a040340202c0003815641c20705d418401405a0f9500040300e07100354018082015011000035001d88500740301d0040a500c0e02201d85507801d10a031a00d090900040e942c1c0740b1180c280c0400285000030a0f00142c2d0130700a14001d100c210742e00107200040d00c5400301824138000200e1440a4054062481598040c0b90103a041c0070401c40300b400003041c4140c2c1000300f0410100f203512040d5098219008007401689090400c03103403036000044840442c1e1403109038034900860110074000752024028442e4102c0d41 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 847515764 1250 847514514 847514519
    0x230c01140a0b0f0126041e12031b21240807061d1005210118020c0c04090503090d15052503050601090f06020303060a090b0319020109 59
    0x100500c019009000c00d09000c07400510364010425010303030000c0041e051000b4004221000010107085a86031a0811010203550750f503410f1074070b4440b03c01a80340e080101d048050404022400081d480c5140d420396082040440200c86c500c40282d5040300803002c90081300101c0180d40392400c0008120801040204602036110f00c600750801016001c0000d02c000500d003400a400c0400c40c4100614091601510402c0b20f00301294034003400da910b060041411303407000d9020074024003c1300c0d0700043c008a030b001c11201724110a10340322400c1c092800301070180011802c5120341340c001d40c1c48000400e0007030007034401d29200f04801020f21040c21145070009100c2d0003425a035480c207140509001c0e404c1f41e0404121400a0000c442c0001c2200340340035048018800c403541c00c0090781c401c0420ba401c0c000340c42e4441c8030050b00d0610b07455010348440400000701280d0b195004c0003440c007480040e40ca4001d8551a44503903010b569110704010381640c4991424079100b209584200b8009006050000800d034 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 847517014 1250 847515764 847515791
    0x50d0212070b1c0507051303060906111207030506100e22020a09060e01050f071112071221020d180b0307030605031b0108130204060504020403060c0906230c01 70
    0x40240700320301c10705070b01d40d40600028055809070550000003132401b01d240525030069403010100742d010203800103a665840808211032944003480c0c90001c0d00c07407142c55140a00d0388282541084488100080c140340104589040c5032460f940c4d020107588500200713404503014070035131000358181c020070b0008a4518006a90980c4014000d006040d5200c0c01190b0070310300090415000090b8150401070704105c2405281c1c000406d40364401d50040c40c40e1240035212000540e07003900224120440e000c4d042c1d00084076001d810358011414840d0464803864100c4841501500503a00c03285c80150300101700700a13920703214010144078600714034241e0760100d49403650034615800c1124500c021954480c800c0c440c41c0350410160002224882403048580e2400d0002051400003610749031403904000f0240301156100e800a9010340b0300074108544450f5282040c1015002110442012401c2c0c030307102080e41071140c1c10040e40307201c0001100e0035108240e40f0003101c40d441001c00a0540d544c5595521088 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 847518264 1250 847517014 847517017
    0x30e1507080d0606021504050601060f050c070b0c0705040212130213060329100b03060109080a08071a040314030a0207060c020a03020d030c09090e010b09010f1e050d0212070b 77
    0x1c102c0071a000406900b80305019107025018141010020518401c00c00001e1000a80905441141c904580b45034030307190f002da030760f400f5030302c4050164000c6500126038000c000010f0004500d16038125502d0301c2d545d030148000c0303100d0040c98070294802000014950001c00d00d59004031031010b0111030f0041d5a50400c0c100f1a031040e0001c4421900b441c604e2141c10132210010911004419043c0405007011410f0909228007445517050304903001c80001c00f90ba0242a6085c000e00000042c0d034200c6280b071415240560018904071004500340d04800b07102198a903203603200d190705490307160844642d10b4622406d500002c02c100389032a002c00c4090700081c05801400c1203080f154000b4041e44040349006070529000746003900415113001030629915500c150b0720421964240e50019819901005260143c9400c00c04650400b042100004010900d0521102103072a010340009202003071000841409a07980300310340e030000d0200120001f43c9083d07003000c0e1480780b034172044848042da00d5240c078005 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 847519514 1250 847518264 847518277
    0x5160209061804080d0605041a0118080307030921020102211309050609090316080304081e0a0e0604030f031815020109031107030203070b0d0612060b01110a030e150708 74
    0xf0080042217043d180b2403240100300142004403010b1001c1041108208141d21007850024108465151002c0b500c24203403480a0290071501d054a65914540c20b000d03148203450311840b0191100d0080064402250b40f4820065550590180a98800c403d10f99281e40e0540ca08004a080041000c1941c1070301d1503051400500803440089060300c0c0210401040000091074048540c10411000144941901301c0103440c036031201500780c03251030310709001c0028060111609400e0020f42a0b00d201d100b103ca0140c03910209030303070303901d0400d00901d41849554000c92100030460380e031468074400040c0c014601101c080c1500e940b4a041195a0003a2894814a600e615400361f5075801800301070581c40440c0b04a0302000070010b03c505480c6502080d541e881c21300c6002c60301c400c042400c03502005140c1110b401441d10310b5204150798080d0608200924150b4822804180301c0e400403202d0400114140c483d540d050303201da100a00688090122a13600255a01040f0108102040c00a900007028206 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 847520764 1250 847519514 847519523
    0x20f011803030f0608030904020a211407090605090d020105120c041d0115030b12060f070815030c04180813031a191802061204030f05160209061804 65
    0x40440c200e04002d4116000320080041e00380c1018024044980000129843c61209032001607a900051000b1684518a0040f414090702c04100c00f00c00c019154101054a41d038032290240c0d60b4403001c00c1a1028900780c07007920040740d010b000c0320b81c3d1031a10114240d1414010304005240504007584918015000c6442c00c05981000c41d040c8a00d108ae10003642500075100303408803035035040c80d21141400c100da8410070304258603009000c0741a2540c01040c0e03030301a002c00840300c16082a1911483c3d03200c00300c0d1300c03200050100c00080c00c000c0014010709000b40015000e0030104000d102480042e141c0c014401d542029852440e500144003134000300716a04000c10000282c40c1141360082184040004484080d00400c0038408490504521510a80080c010001e071098190610344040e030b294070070107540100e0100703070b4054406503100308078030540c407039034038160310340980141070301c160140c440302e944400d040d880341d100141001c070f16144e00144000c01c4403881d090105490390b5042c004a80485 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 847522014 1250 847520764 847520801
    0x160620071509170d1b02030906030a1508060f061c030c030f030e0708010605130606020607050304020a05090c130603051302010c1112151e0402060a031b27080d050a020f01 75
    0x5c0c603000035001100c1e5141d040e88061460209184c0c00120700c0d01018042207401d95a4120002c070780403040900c2c800030808402654000d01e00402038440c040800c49010b40113148411104070210500da05012000e81d040d00d400e40e0303d49081c0c608a400c12000c8440005040c0d80e031740701041400b01000094024a902000411014140014400001104010860410309018003801641e170080707007169001700c0034503049449640381d0000507290f11030f40e4007060700000e0071820b00000c45924001020414214100342d190343e0342d50f100440881c0c2040302d00a100d0709420b40080010b40c0b1a100906c25240600c5111003030801c268001080485c40355041601030b0300600c8041c0d49240d910f0b480340d5014070301540c05100c09005000c2d841d100880100024420303400012400c941c603000703602004100996584040c00480f205501400d40014000d40149014000b04004007801c99108040c084d6401c5401405200200500541e05a00404d07442d00940c021a00348090b01c1380d09104c0e1001da5403c040d40b50 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 847523264 1250 847522014 847522031
    0x3031b0516031e1115090402070317060d0c0533030117030405090423060103150623040c092d050102010e0c06030606160620071509170d 60
    0xd89652400e0b03190802d100b80d41a0340c1004219022200b5039480360503141101541d903900d4283c1707a2449005240c9a00c42e2000c140e6505041d805040340d0000031000c14800c480380c85403000c0007030042d08100018144003148101b48900e003400c4d0641400c488009101200380203015502084450610048901615010004200c03c1c3d601000d80317041c400c41e08020310300d0607003003d000c29041c04004201034050090f00681104503141c10303d44070510200c05080d00e6582d6140e00d80898540c60210350115800c0c1003c0b00400c020030040080c0c0ba02c1c1e1a409603c010380c203256400d00c0080c2001c0a12213050007a030000c0040c140200480540746000810380c2b45030002c1d0342c4038100d00c254080d500460f045a00d0200e10042c5514002282d0101d04421101c1a40b01c4c0d481a00080b0305118038a640100c41744c030310301842c0400c10190046080c10840080343d1032001000c1c03502c40c03403034001d094001d000a000038100710248c0c00c0d940c0c0001c520ba4000d51403810413248146030400250710024003403420581d220f091 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 847524514 1250 847523264 847523273
    0x3150306050912031608040804030b0907050a062c0f0a0321080621010f0f0912022409030904021b010c02060112030809010905011806050f060a03031b051603 69
    0x1508141100f105501d810350400d250407218210140021170207001707612003c41d040c0302595041c0d40055038400c081d4a203901e0510303c1d00340c9480d01480343d580600a90b0030301140e07090040b22141c40705040012992a15407a14140d400e00c0180750000c9608100301c00b4140d00d5940f1a03060031400303180114031080100e51300a0608030311101005661003003120100500906641d089003090345049900c021002c0f034544010801e00400c041c01c0210412441d1448a21903400e99821028180c0d025201d9172940c03d40800e01a40c072403440040c0f0603d0154440b03003400c00d4000300602c0b640c0088483c0e08490520078800c02083c200c1c0c0c40200d5100920b11340011145810300c017400b074068050f001d84003a2165524001101085400f03001d0001e051001d100d0010711807003025808103042980103002405a42158201e08a5400c600b4a00703071559410034001030660100d258545000300c0c00034080594030761640d10b00f2100713000c0f11121000040c040d0400140803803c20001040e440c55400c0c00c180100d0f195181 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 847525764 1250 847524514 847524523
    0x20f1005060636030303190b040f05090a03080a020406050405060f0409020a0509031c12090f2a0e150603040f0b040c051e09040212070b0c01020a0e0f03100c031503060509 75
    0x280c28401d5000304104030002c080c0019035505010204c1c80482d1a015820014000d04040300b6034280ac945803c0030020103130350000c0c114900e98000d84908000d501c81c404c00c0802d0b0b110314011000401d000700700422643c01c1172801804490840c141d0203040903140d4140c2010381c0e229030b0580700044c0010a142c00c041c0303000d2000d03207064a6444496001c0c0b01500710041c0448208202c04003605550703200740b4081c403070401803070104640d10a04151002040b44005110344681424842c608900384001040b5205555003c1d40078000d28121048240e07159404c10150f5880104200c52025031401d41100081014141078055442005e4039074502d420700080c864810885001d00708d03220907000b02c180303103030b1190200303190003a4068465104c15a41c2d0510301d0b113400203d6022015490b800110f0990350b032010f40c0070300403466a030382d40d4107030141c0303500c0810044c0c0a41c0002513616400885104800d0b00003684071555441c40d44c10040341285403103803040303841c8040c1d62082d5443c0c0c0d01c0d5005c2101d018000d11 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 847527014 1250 847525764 847525867
    0x19030c020c010801030b10030c120b06190b0a1103190210090f062f0409140702060f1b0a11060a0207120c022d0907020f10050606 57
    0x100a1000340301100000b003d020f03040c032005d0a80741c400000304a612580e880120061030304a00010b040783c2d0789640a609100481c801540c41e240d00c800401c0700c520740f41c2103995913649140c1d10800758600303001d8944078990080d043c8006014005181102800062010303041c43c3c09001c3c161040184c65140203402c00d81c540690822261500c08448002185544150685c90b081480000c1810743d201d5500721356258844c00c42c002e4441d0300120020300303013480001e00a4980740c03502405a80c2d0070700c00c0c0c1001640300b83da41001580040001480d004030440c521503019406801681c1c2281d4408050041030780b08100400000340c04100403854020100101138000301ca090086141400076151855245482d0396000208012210750f901950b5900d618418510120340d8000c0e02c3c943c4e10301a06040e640c800c42c0c464020035148000a0780c0034000300303140b2803061080c40a81443c4000306800c600410700223203e59030100d03043c080a01140070350310004003406032403c9580b0507119094041440800102d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 847528264 1250 847527014 847527017
    0x40518060109020408072303070329010506030601030c0306030b0907061106160c03030b0406090902040e0d050301151709010606120e101d011b0f17010e09030f19030c 73
    0x10801081084400a0a14100c4803512a407410f1074540005280c105030542c030506615100ba002c000c0240442e01c89446844bd00540c445041007401c2c200d0440003c200b403040c103611510600020343c60354002d82109015000503d000101c840d140d50311808085c0040d10f8840700b40c1c0c00580c0500c0b0244d003150a02402c601da02e401800f003494141010300801c0c3c0b4a089400400c40c01e441804101402908029809400100240202034980a2a0b0010400c000044e0f21aa046c076003140444a408103100c5010101035959616580c20f040e0501d502c42d038105007000400644680144004000360190342c0a0407800300042100c510380000242294003120201d043d0307626042148101c60300028150016460312480862039154940c005200d0540c06009410154201454020040d01c42102e2a03030410301030700c2d51212994100d9007254905103010841c0000c0703504c80014084055501d030703800d600858840442e46420348003005030659400c042040c40802c6050400c140c26950076010741c103000000b6 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 847529514 1250 847528264 847528267
    0x180a060b0109230132090117061305090c090a090c0807060206010312140a0201050105100323060409050d030902091e060f04150803041e0608010315090204051806010902 74
    0x21044114002c203031064201381448003c100881034804200c1150b000100840f800407005140c2c011484120342c4804800d50010f43c000c00024099070070018040c0c003498000e0030600301b40b003001c3d40c2c90700100030180c4107c849104140c9608490740d95044445d2040d0004000410129054a032003849544c59030050701c401c7d0000c502c144080c0d40d0010754241100e40100c0d00c4d1905c0325404609903280d0444002d200b2513080c0010f02e0407905034054100303a040f1501034861401840000340200c04550320060f141c0c0414003100220001503a1800401d034014800810024000e452682d80e03605e410041042079005c261241c18400c00c1d40350454050b0b503c008135156082039030b400303d280758a1640f0700401d080e00c0745e800100000c003140c60340d0780800782c400402c0200c00411625050400e80d660414420700a110101c0000d000c000c180e01d0a0040440c1d0030f90320752131880d0f400d50303542191009200d812035500710355413900e0b07c0250f6950f0107a180103540c81407a42d0540c50040980504151058010380080e500 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 847530764 1250 847529514 847529549
    0x6040e0c0901090b03041208010504020316110c0904050a050f1b010c110a0b0912070b0415031e0b0415080c0609060d110901090f0308070209180a060b0109 68
    0x20101640d8800c0c0003000e641e035a8103010700107803032a000c0c90700115040c0d400481088200941c0d60aa250310202d01e44625410b40e81c0c4000f00000d0340701c00c0b92502c058600c500902002c0078028207180300c1d0005a0810360700d5002248000c2050802c0032282581c0960101c40c40030207010051201071500c842d07050203401000320070b5810341c490003042c180300750410540c0a445818020700c1c020b0f402520f0402880c05441c0b50707031600b91046079004030745200d10030891458013a0941c1c41c001080f0f0704448840e030b88641443c0c60810f40d11030f5031903040078040c185178039005c7d40821b00d6954035410445c2c2c46240350016220220ac01884201d40808881c0c0038914581c00341802211800a440034044074211001030396018208042400380c00744000903410a410031640090200c1000c02624840c0d40a9031880c400d50b54440c0401d4018000f4400902200030420505016040820042d680040c04449207420400707003200c07581c54031030582800d95900b9500c590704001c642e40642d00b5802818600c00c0a0840e00 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 847532014 1250 847530764 847530779
    0xc091e0512011a0904020d050f210903060f100306020c0a030909200a02242203080c0a050f0c0a0b01050406060806060c1c020f01050c0a120b04270c050604 68
    0xc0c1e40c03045851213083c04000003021960b41d0249008132980c071a05031211010803613805580e418800d4080307009002000da040d400c8010b04800d45200900042c010700040c0c45199000031104006003003c50f059080480120114220780010001e42c01070f0401042000f2403401e0003444101c82d074112480e0a030400e207164040312012400c410a8000c01c00c186681c884a460081c0d251005079400205a86000300582050611041003d4400c01c2980740010b900000702c45100101201600c0090200380c04502203400074850b0800340c12030440700c0c1000c52030414400b0b05550507400144580c1007550203201d0600c10420380382c2c0c800e0b0041405032014421613080c1900030380035074401030bc407034001c10010403818110030003003208003180300300c400341300e84c0401507540b009407203140e00b2925070059130070540428103d0707180b10121480461150341c0e80540700991441103001d000800d080607407094540380744c0117142258034200c0f55800b03a00075541030400c100b460007018141c0b4950005101d20342c01d000800020 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 847533264 1250 847532014 847532051
    0x71502060f1e070203091201090c240c051e0309030c0f0d0b130c0b0304120e090f13060218030f12070b04082703010b10020c040c091e051201 62
    0x100b9645095000d182d4900e00200e28502440c241aa44000a03c40c4202c458506500040c04540990321103600c284e144c0451414500340b01c0441001c3c0001c4a42d829810b500c5150390800b00d5100300143c4504a440c001c1c034103162041403880d03040703a420000350704d4070906d030421980010b40742c02c0d01c035400c0c150488000200182c040310409000b204c0c0314400110000000d071410304400d07500c00c054050a50312444000601c0c1c0044a0445000c1070041d650410031b409624000382e0004010000140e0340c1e02c2c1d1b80c00c1d400003100601401041110701c0c104400203040750001e004c01d06501403050481d041c1d404101441c0c080c0e030078803601098200f040000c0d42c181800040f07580d01d40c0c0180400c0c400780c5862903d00002d114088120741140100d83c0c3c0080c01408044d000030842d01c04a00a0240034140803c11070001048000e910145c1e21607000a04079007425044401e41d00d5070b9043c49030308540c0d180010b120400b0141a07401c0e100080072814011031a210350042c011241c00c41c020040d0241154611a44 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 847534514 1250 847533264 847533301
    0x90403050406030b0f13020903102009120a05011b11030a05030405070b0c1b061c0506060d18141204031506050d11100c32071502060f 59
    0x1016191210070355a9210003200c4000545d0151520342e030380300a102080c00035005038113014860b01500b61300c6188040107000c0c040007000040750100c40c140c0c18a04c070604035070204051580014010402070f200b00b0090142240140c0035030004594854000c40f405990941104850300f4840803543c1c501e05008004140c0d04101d6045c100785a4a403200d0170000d00c0e00c0115880041502d10010b4030b81d250701c0e8041450003806043c0050000200030090400600e07000303104103d41104070341109007444001e01e03009260418809403210f46400c0c3c40444040c250b90b42c481d01c00d003480b4001542c0d20100000c01c0381c0003640c0054030740600300b001c088140d80000b0344102d1201500c140c8211241c0c0303001c85241d134482402448000e00200000701e05203004148070610012a511030781746525000c0c0864060020385900592045501001280c01d01050001c1b0b1400403c1c2c0000440e4220100ea90303810400144001e0210801d0f0781c4691130282e94024030f000070081001014071050b50500c82c24018121550a2 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 847535764 1250 847534514 847534517
    0x906100501210b01051b10110a051815070501021e03220c0f060e0307093804020a080f060f0f04050a0e120a08060405010605031f0e0a0614090403050406 67
    0x15041d0995004075428010741c1c00c00c2c1a003d120b0841d25500c0c0400088447d02d4507210141404240ca50040645642c05014140c101082e8100314003440d1a50001400c400760100904450401c9036a940e010080d40001e0000c403401d80d400205010801c540c5200d02d0000c01d1088078042c41c1d441e101e002080021207010031409041c01c032610032000c0014100c01c0801414175403006100c0e503641d0303003030007025540d46100c000c2c080e020381103001c5401c03c041e028109110900544031150140004070019580c2d104640c07482c1100074088880d13201c0d54840c001011912100e980d51290b81c284424007401e002005001540f14004000401005403a10415208843c5088500042c00c0e030383d15201c5005040300c0d002a500500522540010f04012080940300d84605a0f44420140d039400701800100c540a001e4500070071003c1c8005502e10324042e6000e0b60a514100b500c030b0ba4241d54524420b04000190f504119564030340405000d00340c0f181c85031010100040754031181c03034100303a00c0280851160340200c40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 847537014 1250 847535764 847535771
    0x41401050d0207021f081e0c09040906020c060103020913110909030712051b0303132405010617130f1203090804030c06020f070f060c11040203090610050121 69
    0x94201d4410b41c1501c901a40240034800c0701c18680c0d5800001e403481609a1011403011000700b400302441c040c0c00501c0201031120383e80da0f9100d90004201c160005803c882d4010745502181c400507403c0d0001d440c1c0e1204480c0201010350441c4104072480f600280400311104102100c1c40116000c002c0d0991103500c20b8803844803e0701e5030b8408500f903114802d0003901c3c1850000c0382e14900c0354007800400004841d1449644034214000c4060b407241300507518901417000385100e00c0003040c08a240003c0f50b03465031801c0f040e50340060704000141c42e400da0020011400d1000185407500242c41c0d41944200748040600c9021115030b55070000c15407034400944541080000d03008c06038005d0380f00510b201e40201245848542d28903042e024020f950040100500601502084100c0c00151110544908107101c030f50f4541415802c40709007140203400c0c0e0301030190503003d1a103a102c074801540108414006080d031880c10400d4000c1802c4660b000b1410414600704c4602c41823464921503243c000b2402012 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 847538264 1250 847537014 847537027
    0x90b190909020f04020c06090f070f03110102071e030c050a05100e220e0c010207152a050c0901080303070e041505041d06060609010f0f23090a050604140105 69
    0x141c4040c03444502c040d0098070000b0341e00b08202c4000b0b43e1f548a500d460301252070620f0312606298450050303105100c0400c4261900340005505403006480340b400c188125040d04e40d8030b50100410310b0740ca40c0e04115848001c4020700a00400c041e48c89d000d403000380c0e2205c840700e01e40808600b00030107200313004040140800c00000303180e40d14a07010001c241900301c0e900e41c10800340c40300300c0100b0350000d0881840c0305101c440322155002041e51011112120080c1404001018054442400100360800100b4000c0d1207003081002e8284e01500c80c03405400180f9070ba02001d000d120300040d0607007041003d90720900420011795401002a81006402d40340440d120107040b900a1100d40c10790000796000c0c0c1040010301c0d0000c0c90141c44c0d5a2094903c080b5a05601d0798401e1101900c41d003400340780000c0103003149500301c50003601710312000b09062402015228074002107000903185a41c580d03480c1c0c800000d08401d1464004056000b40604071041d61825191840440da040c44807a1801d06214001c54035 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 847539514 1250 847538264 847538269
    0x10f0b0309070503030d02040509060d0803010b070c09060311011214061903080f09030613030c0b041a0403080a0609020f0d0e10050f040309080105070804031808100204090b19090902 80
    0xb29008000213012039403113007010301da980e02a401601416000b980d10400252180c600219584801e64020454510716400e0201c0c1d001750303902010050f80d90500c1d013280001c001e80c0342d1145034001c40c010903603154440c55280005004001c400042d04041d42008a0360380f40c04181c010194105900300c40b0141d0118900c0d8001d20301e041181c3c4064203580000ca40505c80e035a01d0002001034040450684002e0b64030400604c45114a0700b1300a0b0000321005110340c002660042416006030144104107a072158504500e124102c0c01c582c120002aa44400c3c49035003100780c090380300a1b200d5400e00f03609185620310715050502810451038200d80d10703000c6864003803905110080c0d002c611b0680c00d00007860710900c3e074441d2410030784044000803058a8000740000d0f041c414076000703072000d075100316079515181c408680c44800d9410248080d030b9000d40c00100307510200107a1340d00000d003900150f05c1e646404600000c0b2591403840c01d000d50840d2000903542c43d8044280d1083e562041340004002407140003 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 847540764 1250 847539514 847539523
    0x1e0a0905010b0405011e020c01030b040b0d050a0b0a0903080c070804050604090e0607080c07021011010f06090c0512010603020c03070c031a070e0607020603130602161a010f0b0309 79
    0x4494540380c5800071542118680003082500d201380c0b59144002a4941c14072111001e0158040068102c0121210740c0d42c402d80001c0301e8498004e20108000103a80c0020b00c9559490800b2100c1d544005055810000e0000c912079201a40c40d07000c020466154801402d40640140241d91001002038038404100e903840c11703140644000351910b521103840300300a40c02003980303107640c0701a0301c40c241c009040761b44150340d40b0740300e084074031030076070034803d083c1d00b03102d24904801141014030000c0c40c140d01e1150400d11800303106807288800410424502201078045880c5c08451004004041040410404040c1c500a046030b043e0301d401651450074500ca5401c6014116004147c030210610002c1401410901c0c01169980c002c03059503a9203c0041c00e48420407510003e5400c40001d11040000d4078055000d580d000154a00c1d54580300c819a0f200800c0340e0103402800c80400a0320003140074007419162170406240700f8201e003101380d41050780b001d03000310552045000c0b070f1030f0000009071340100c00e21 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 847542014 1250 847540764 847540769
    0xe040203180715031113170106031203270f02090406200a0f1d1311070c080d02030307020312071709060703180209040209070c0803010303051c0b1e0a 66
    0x1c00b03403041c054441c00101070085524140400103418448244c0401c440602119100410000801c0c40146842c04400e410246190b12139910f55a454000000c98040c280c00360002d056503038001080c2d80d4141c071903c1c0e14440f040c98815411794580003000001c80c203200c000b40f00380e0111048007440d552494034402804521100494002d440f80d8140030010000014000600c03241d1180300da03110109404642c4004650701b04083d1203070445400c005030030180851020648202008201103100c3d14948200740d1095800325510f10140707208000500040c00a01c102080780e1014516500b49a10300079036034003601c070300c80c0b002c2d0f140b500110385024012090700c000598614400c18291500c0603280d45ca4407001c8406001007800c00c3d42c00b13070b24107140309c422a520560052804255403526000d1103648000100300c9001d0200c42c000034008207203a2405140218442c1e52550754491134038480510004d122111000300c581041c1e52440c00e60b41e1610b10141640c404080000d072440444000340c011100b80e07 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 847543264 1250 847542014 847542061
    0x1813050d0206100e04030210050711010e030d1503030c060f022101050a060f022802030a0f0203010605060304050a060b010e120714090705030705030a090204140403080a0c0e040203 79
    0x11403008180da80c01041d400d104402e107081c015003142d61610f1151001c0c0044030000d0040c8c000401d07503051030850780d0240e500700b00940b07001052200d00d004158215583c205031074049502c0814462940740083c00380e60325400d0602c00d280c1000340b035a0390107060330211a100030b0100e80c8481e070307902000603d0b40c140e503103000d2206030740f032080041140e180040450a01400c0d01942c404040811528094049000001c4c4c155005003000300c00f40145010031556004400700a0070150305c4280580d07420000f103030758240070300b0b07802d40c20044c5841090b086810345d511080c09480e050040102040d0b01281c4551859004240400da4440c1400100e4840f00031408166001c07a5020484001980000e419020b541400b03112108400c1d480f0208004e6040890700400010000c1001031144d40c46480a9078100d084050f02080c42c802581c00902903540b40c24200750700032014801c108c10705a005c0400b913000b07050101c080081150000005010780d01e2030310628020381c0c002000c24041085a60f21604c3d83c00300 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 847544514 1250 847543264 847543273
    0x1504060c020a0b01090914120723030f0d1506090501081b0c01200708040614160308070f141602010c05060c040302100201020c07050f1f021c0509181305 67
    0x101c440390002404100f00a1f680e000b4000d440f1214401c0c00505a2250740c0b5010a65081c00450303500c05580000612009400e00d41c0c509000380c0902e010806003001200c41014180c0340c07283c80c80da46049130340f041100d5100d4403401408102e0a50880990310540d04207182c00d1840d6503900c1c025409441004802c551a4100014441044081940001e8650b400e0945a5a400c804105500a1800707042805400c50b20100b008101d0107001d941c0507048404182d01c203900300070241404a1041508441c15000709890300d04000080358000c14182000c3c07468244941d82c880300301d820201c6030241a48842d40d6818403030000c000c1d0780c001c103604d06043e5400000c5a4083c0741140d0a2890340c0c001d03100880c02000c02182c50f1305100d0040c003e442544500c0c00041c84481d18140410480b0180d81040036086040e10704850108900070824884400c12500200b20304a9140140d150320304001a03420308000062104240e5940d0b4050000d000c540d055000c4441d82e01d88a050302c014449845c0c00800603c00c = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 847545764 1250 847544514 847544519
    0x60801231509040605010201090b060d050a0618140f060c0d0209040e010213050a0311041a092502030c0c121203011401090e1312032403020901081504060c020a0b01 72
    0x40407402003145001c203a5003030001990350001a4203948414800410181900000400a061a01c0810301d440d0240741260f147c0280c81d1581c5040b81c2088034000400d2161550034418840002001101e412205c001861594400080242c40d004041c0c20303240c02440000c2c2c840151800c0d6015100070f41e000074810032140c441c40c042d150003175000c1082e00460440d40400062186403004621080329004440c001184080e801040020300b071000b4510440ba140280303100340b54560328401d620455085148544450f0f411600900c03281e4264403003411580204410511300c07201080356a00250305441c0d14403034684100d20503041c00b01c2c0500f4044241d40100000070710703031585444004020401c0e01d0340c02807a61070381107044403400104d614071981304801582c8400180147e1404106080d68030f80042c4a4052081c4260040f145009d1a00b091100007000e0055242145c4402d00529001c4005d041000f2028818445d100300140080c010036614035101502500a1203805803055004485000b01d41c2c = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 847547014 1250 847545764 847545799
    0xa050901110a0201021201090903090b09061303060213091b14122e05010503010315060e0106030e060f0432060f04140604110d060b03031207020d030606080123 70
    0x4200341001c04400d00c0c46e000016074003106100d002e1200b0340560b10b07264003600b001d9483c50941c1c0001c09140e0005020804c41d140788a045510801442c4209409a503820350b0310702c5420070078040d811440500d40f4190035005020002e0541c40d2115110341802000a00740e840e0303042840c01440d01210312003100a0400c804040085a00307520a030004400c4e06641e0b1404249000c808014010a40490b6040005001090310415030864605282c0004244191110030010b500242a8011808030381c0f5028030007482c920901a95500c00e4840100d5a03440c43c1ca5110a82c061480d4440c09005108840340700a4001c11a001907070f602e44c0003001c0301c0a9040042202000350011034098542c1400d9200c00d83c400303c8041380060082d40c000ca00d10390011212002c00c56400d8828004860060fa0780e4104e03859900c080c000741c000d06250003925212840c00c9000a42012080c044500825280c01c0003030020303d4105c4801070540740400e0428032507191407214040c0c07007810b0640701c5038040e0403944182c2840 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 847548264 1250 847547014 847547017
    0x1015050c06041a01080303100e0c1c0605011b1101030209061603180b0304050607030203070e030105090106031b0b0a0513050d0b102108070f0b190b060c03030a050901110a020102 78
    0x8056103e0548850381d90768400c0c0d482c1e0005603482107008640d450b0801a0315080e0401507004810a50034501d403070ba008480740500003802001d264180c0d29032208020968000d0fa144020b921220190b821104603603881031009150400e60324103055020940c02103548480c02601d403192000d00c020f203c41402810060310710004941d0f8004441043361010400745580400d0303a0180740e020000b444c00380c50b041400e0b030294100920403400c018030242456802d0390709024080c05400444c00004040381981084041c160300b100111448920640042048003c410101c0c1c00f0301c80c2c00c0c600581c80307400183d040c0c0c220f0f4103980e009903448201c1000236014440e004803100e020301c0c88442030036285a0341d85032850740803003c2404804200c0768a028030300865106001000300c00d01c0345d014401d5102c2980c1e1f1315840880e0036291282c00382d400d401400c024011510070300c03030020011142c2c0381c01c124400490703640da4800103080044803501c9101141440400350445204c0d1a81d09010031744400610350300034001d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 847549514 1250 847548264 847548293
    0x213030c0b0414010e03150c0c0106140f1219150504050d11160b1e0324010504032003070509180712110d0c0909030302211015050c0604 60
    0xf07031128851100558050140300400d10409005003242c0144100c040388113440040289107184d5042001c110401ca0a215000c0903110840704403030110b64010038862440031144019010f0850105040c44014000030361078610061401c0f81510700d0070b0303450710702641c1c079201c21486030142c02d20041c0010001c01040545011503ea0b44561007920785114590759090104065141a00441804d0100c4007101e001801e46810340c51342e0052030b80c0e103202100384640c07085921041d05040100a1000c803080291200105030007403a00c50b040600390303120640c000714004042040401001903806290300c00348107440050800130400c00f480e01c1d014084002440c05643e070803580b4007655901041c80000d254500244030b80010011032400b50340e0b024050a8108010180c90b5400300100000345031401d40540c0c0300b40740c4650360160704e6503a040b2140012003c80b150b15050180c105080107444a482e141c000701300c645140704603928907051002500ca42c07080e072001d840c26010781020401884020042c4080 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 847550764 1250 847549514 847549529
    0xc0309020103200f07230705031e0c0f03010f0c0305070e040513020609060c0f0a0b01060318060b06130f1a0c120325020a0303061401120213030c0b04 66
    0x140d55400c0302440c00c1c0c80805101440c140c1c070910651041c8003d01c009403460311b110703004200c5d10320741c0090403650000424403220829404a01d00b840b032420140603903091080170f100000141c040c03c1840c0754403001031583c074602031458003640c0e0709695000d400021804207902402c000a00310340a009018280c11203041003c034903170320740c0d615140c00c05115680c443c150550108030030300807540c01c2020903444219250b522401c00d200724060700405010410b8507030b030030200404d04909189416503101d68140d0012003410b00e07100d074213401ea221510300e00311405d501840c00a03c401c45080011214001d8100400c6002c2c1c0080022848103041181c25054a1305808000344802e90103904d20201d00c645040d594040d04140f1000803802054006180c010182e01c1e11201410003041c1c072188003011b50800c400c011317442003012001b40b64041c410f01c0301504081d130315041201da0410028201000c184001601c090b80003900004100d1f107104480e01030340c0d0100e0765052103595025010710700d8116000380700 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 847552014 1250 847550764 847550771
    0xf02011d040f06090b27041b060804060c050327120a0c021e01120e011d1b0a0501140d0f06030c0f09021809060a150302220f031202100c0309020103 65
    0x10800c6ca44105019208019002540300819032210107098a4202901c100c56680080148008264a00d20f040000c0c0240d0b5a80d45910701c0c2900307080c0180c5d003e10429505226081040c40a00203000c20040e200030030703c0f4090700303a40c0c80110b06035140564660b929140d010000c01c456004a9000d044a084280216032407440b405400b08469440030050341e0b07490120f00c40e80079000b8850030383d0300204490340324480005408900640b6813034a40b610402c0c920100d4210003241c80d95003a140800150940058034110503403402c10b0000392110050f054445c203400404541208420ba41d6001100d940603c500180422550307403400c80c1d88041c042c06200c0b0141e005182c0030032202c15a2080d1400a41000d40244450000d903081c088801406014950016404180880c1c0f005800344503800d07021a0395001a40c41102c600410050742d00d072000314448480081c02008a80c010358000c01c16a43c01c0441c000300050f074610241d01d0003056198260704181400004818517400d6403000c1c6015000b0380f002d0 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 847553264 1250 847552014 847552031
    0x11040509040213020a020f0606042714030415030e060705030109020d06081506030709020306030307030c1401060e06180105130b0117070915110a030806010507080706050402100203070f02011d040f0609 88
    0x207942f03810b00414081d600160703a82411040c560a1850380500690304e0300711101c4284211401c0d544260030901e84009407003011010b51b43e0511480c140a174038540074000038180004010100e100c1031017000e00c056004249003c0c0035043d6840032005126880c02c561989008843c84141e94104440312071280c040c1400001d070780b40c0d0318001c0340e1042c00c00070041c5151140c10f41d4203680e50369014109548401c000608140400f1007445440040c10010016100c1490f1907410000780b03104203103c0000c8080405c0c01000203480706e1141140c14800950301254480700c0200480700210800801c07052280541c0c207204042d82c00c01b00000c10364624001c80854007001442c250780e6601d241d000c03042c0307039400103d2500109100c2c0340003d821440503d071007482d1040a45542680340c000400a07540c1954490070f00007189080d80e43c102004086002650610285072182000c0f051010406410f11110107039241309403041c0703a00300d185140010010088251030b0200d2800a207002c0c021056141d10b0600305 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 847554514 1250 847553264 847553269
    0x3140c1917030421050c1036081e03010b030f0a09030503071103040807031a07210209031005071101051005130e0f0703051c0311040509040213020a020f0606 69
    0x201c0c0d1086030000c034018130602c6107058041c60f0f80703180380f09207040040c00e00c100310103210180400c441c413695220700403030640408281e551003003240e14134660201d140c80d40800e003401c0301c040640895680001059840d0b040010000040510f00304840c1030b81c80c0300000214107440400003541c021200c3e025120b000c0d64402030200100c0e03102403805004140301f80002100140300705a0001440f82c04010f0ba800c0075503558010380352010a401c00c0314004000055440e04c240e000f100258032100501d4298401c140c030201a40c20f401c401c0e64a942c041d80c001800b8009030b2010000c0815003240c0700030400030751500d440020451070b03074074003140303025404e00000c07070600042e40e83d030705055580081513240060b8400011100900c1c0305810490340e4040c031821207214180501400300118001c2c8042c0c01076010301150300003448021441101071500d00b944007048468a2416581551000c1c4c0c0d18090301c9d03c1e140001503000700100c81d070883c81800081d07840c902650201d0420108800d40c400c035846a11441d08 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 847555764 1250 847554514 847554517
    0xa0503042d0213060503120a021c0f0c320606010c111201060305070303051b0f030f31090e030306030d210609050106080c1603140c1917 60
    0x300e0030204803168000380058540142550f00c004980c120000341103942c0c00200782070005480c461006035002007046c031042d42e0144140307049100b80203082d192081c12420081e04201508000d0803c110b1000c084004000c00901c2c0102904042414400704038a4109055003c6031036174408031143c0201004680c2c554080c13800c00c5111503110104a211030301007810f02510101d40961078106649682000001c00d070203210f4500070354003a5442e15501d07100c85a841e01809220700d001c401c680c0c07110f41d0000000c00084180c41c0e1121075503a410ba911500c454920b00c1164007030f445000307201094814012641c511010031000c0b101890f0f414800c5c034140e441c40301d84900049a52a07003642011002c6903545100b8a9004c010810000382c3c04507045000110004480f9039400010f801680c0d44010b0050300c6d045100c4940c000d14214402d40343c00002c6d045c140188055440040502c0f02c1e0080d15140309220b01c007682d00c0c000e281c50807104282d0310350001080c686208101502e0358083c1078590800b1406400 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 847557014 1250 847555764 847555823
    0x409060b070b012108040e1f12120905060d0f0b010e0112020a020a080c0304031112030a080703020f0c03091305040c0b0f070606060305150306101e0302060a050304 72
    0x141010700d9a04e051111004000180c400c01800c500d08116400000e03180c01c0030340b000e4800c464441c086807505007690b651858031781000075840d000c0341c05c040120a01d48c040489079503911100c403c0007000920401d881130341480e013006910900120360710030b0400c1140c2c4031000041403000c007840041c060720019200b000101246c0d9000402c019480100d5404640003402c070203005104841c21501c06403100040c0d40c010908035202a08001000c0003841007059250109000440c0e0000f10401c95104513941c034882c80e038800c0c0c10f11100c0c000040d0402e000c1c1d0305840e481220301000340c2e55106820728103a140d074403000403540714001480d4015420380710307481141e01c41c0d5070010880000c1c5003003043d9a4500e4002400304914840200a0540010003a00929008240e0750b00c010555080c0b400180d02014091004507002c4e40c4a0b10800583c0000380381480700b107450004030207e1201d5841740c0586602d00b0307500040c1d0024000529201d92990003170085105d00d0250007041e08140442840c2c1001c0700100 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 847558264 1250 847557014 847557023
    0x90a05011a0607231905100203070e100c02120706020105091c0c0620070210020d09091e020a020c09070c050607140702040e0f0123070804051f020409060b07 69
    0x14071070f0700002012505003403803541e00072000d80001010f24809602e048007100600c80070540c146044810040d0030001031201d440320b40000e60a43c0361000e0001d000c0a00c1c001824800d02408500c0d07440c1c94001d880e04039403550040c200b91100c400c07600340e00361313500454461880190300c0c0c40c00083c0705510104080d01305202c8007003d9401500d187d0400c580d40315140701c0a0701c18a50f81c2c0c18007030300c01c5480ca0703000320743c000d605d130107181c4a054500401030641108d802d500b00350340107c200c0300d9801d584115020151030074801c3c00101900c405059807011000d1500e114481840000e0529910f0b0b000541409a0502191444215561030030211000030301564000c1c09a407080001c1412140100341120454050140f01030071302c3d669800141c1525441c0401e01c840303801848000d0b01042c0e003805111610409480a4524050008142d41e604403006291b18104541c520220b002c1020038000f40d84404010000c007000701000c0790b41c040003907103c1d00c1050305583c43c01c2c0c0f00041c02440341056445030ba801 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 847559514 1250 847558264 847558267
    0xb03161106040f05070e0709061403060d02040c0215090a060605010f02060a02090103020c0d0e012a080d0b0904030e1f051e04050604060201052d2d090a05011a06 71
    0x303e43d200c1c80b1460f024030085945009000000c82c0c05031810001c644100e00315030702c90340d51303e21300000903168007591503503040d58200400801069807140807420b07081980c140e070002241440007504034141840f8076501090f4000340c10912070417020020790800400d000348d03000c2058613a24801504d446940c507544074050303041500018004e00066000d070114800606001d46003440c0000d820b0300b003041d082e94a60202d20801e28038100f5503806a0481e0302c03291903052030400c9801c1ea02e00240340071707c148401444410300094140000c0ca40b03070801c05c0c080344042c003080c1c69030610b444c0162802103c01407007401090031a000d41082d8022000002da001520f807103251a10030029001c030204c82d82044c0d030b00b0001c0010400000e003a1120002040200f00da5030000859050900003200c1c03847d03001c5440080c07081c4c000c41c03045170f40381808406504800c1d420b0800d00d9140804105010b950091191403010320032000401610740e0000c613041211074401e100030042c4a001c04020021a01e0011039550000c10 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 847560764 1250 847559514 847559521
    0x60509030a03080703090c0905070822140106030c0308030a0507050a08150f03030a02030c0c120c010807260402030105060d12050921071d04080a0e0d0203070b03161106 74
    0x2c02450b50005143d245c04505203026444030b83e80b8004a03803141180f950741d001044100c0f513016002c2d90b00405c48800c00003030071035009845080e5140300000a0103100d5028003102d02c1b42000d42c0180c0c01903503c00c0fa5440c00ca0380c0c07400c1a4800750400c45034042441d09000000348180c0c40f41e42100e145202689503910b494032100e0158203500541868107800841074807094440c1d03034080025000c084209d500450340c50180f140010b0500c0c00d00c8102d1400341880e0b102801e4250b5001c588403230300b2a03080c40c002d44640d0b5030103412078a45407002da0061401c414820030220114000c40c1992103503000760020301c15612520180603400142407405081109041070410089109000070190400c000341042050300070482d40c014946020401d20019511034a0200300d01400744110601d0b10081d03d00380101c5103002d0310b1b0078456124001a4000700000307104402c10341da0340e000e00412400e4018048401c019198403034500300354000c4ea4070a0000ca02c144035001c00c03501c61003002c8001404007015200644 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 847562014 1250 847560764 847560767
    0x806090706140f07060e0c0307050d12050a021603050606090c120406110d0e0a03141206151213111507060c020f0a03050406081608040f08040503100b0307060509030a03 74
    0x803c07504503400841002c110110100c2e50702d000e40c0c5168074000303001e803c860403280101480e020303160307101c2405070021145e80c03c04141c4018018a401140d8148a41e90f4610364004130304120b40d28601440d01030714550f020051120014407a485800b080d107510285840d480b584030100c5c05070803c3d040d03150721480001740c000343c100d403c9140075606900060b42004134004c0c07040c05507190703480404c0f020b0b803100e4840002c1c50b0340190705000a1040300c20051034070980380c401c0d0148d0303100280600e004000c1a1420751101e2040d00846402c201c1c0c02c25460160b05101103000405021000165506807060b01100101d152440f01814000040125a8603000690340d0703038405082c003407040d0740a502840c8107400400e0740030300414902500c00e9850590b15428010003400c50900038290f0711655514101c0e0004890b004407a4580041d0003a050441c0c0f02818030340440c00788955009680c050041946520409005400410313014204400791030f0700340d8079503208560030b0207443d01c181e0f81684400c0040e00030a = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 847563264 1250 847562014 847562017
    0xb0c03150607080910052a01061706040f0807080a11010c0e030c01181e0618050a0e04022107050f04050c030408070c050d0308060907080705041a0c0105040507080609070614 76
    0xd80c40307806c1082c2800c009035080c400f48403240101810010119500c0703008480c083c80341202800381640c0d1810340d04d81c071107c9140c0d58600188020440c0001c02c076034806103d07070001581e00143d8004030065441d55038210041c404d403401d0307075001c10941c00d01000029190044c80e01c6204450003400a0140002c40401140d080c036815141a040280070040811080940080a0000e1816901c0c0300c1a081c0341610090207404038060300048032184840511040d901c84103600e0440703144001c40c800f142c4031800001c8030504008404945040451821100c1103000300b8030404446045940c00508400c3c03000380401c0c4c0b1022a5010201c0707600308001000511000701508005000b0034086190b80d40b203901117810450061000c0c2d01007140300f002c200b028a800d40045034062482d00e000e000c01d041c10000501980114050101e40b013085940c03200d40b80140d20290b804900e0034000070310142c102400d00d1500c469050046c0780b0343c0c0c00b5035400600b0016000134224110340603652440c40c2096030701c0c0c41051a = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 847564514 1250 847563264 847563289
    0x1151b080c010902151312031b0606080d02060114010f1803051b06070c03080d0b0d08030405012d020708040e150a0501090602030d090204090b0c031506070809 70
    0x5465000a800100350305802411800031414000268148140104800b003200700c071a00501600400510034842c01c03580c1a10229074111350302072031616041ca0140c502a03045c1c1c0324002c070121085a46414840250040011912031009a0f5007500080e0310490716414240500c15155503c0f0342201312951003101d01c09000300d568540f4180c0c0c5400d0100800042c0441c1d4030613a116800701c5c0769403000040c405c1c1000c5a51908607013a40c5071182956a18070408080e100103882c074200480d5001c00162030fa0843c45007694014043c0320030010b507240900b02a00706803415109507103040c084a0008038a4140e4069448a12031448101001c80000001a5020341c0d4201d075450820b0100203000c20030740100a02890005100310243c50000042c0314450501d40e200300d04000341c0c4841000b403070b0f03008000c80710800c088200c00328580040d400490042c01d54800700601c3c2810001c2008440100f41d00a58090301c04402e81c40300c09014002003007490702440f4005010038408010402c41850401581c204 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 847565764 1250 847564514 847564547
    0x91e091b09040302030408060103031701150c0303091506260c0a0e06031204170c0405013b0106051903052e1e05190b0708030c0f1801080702060115 65
    0x103007a48402107d414484d00b03902c00c03004640140401d0f40c20611122120780541245201e05c4d001c0c5c2e061a03801840800b2000b40a02815502c010410500184002519180c0040b80e400e00185551350300d2000044003003405025068000034101042c20f101103044c004001004100c2c140144c01c08000c580c42d0007002d07008a5051080660303041d04a968807003e000140541880c0b40340200c240200541049034400c0d000740b003103103004018884988418610400d4203451120001244545900c014440141910140803980e4103400054950351060007410b06620952a400c10307010a408254150b80c0c0a40d00410f00381102c402285041d0700c1c2c1150040d605034030030010220507544441c511a120018201201c0d20005c03050144290f0405200e45a40403491044012080d0319004120f069030103502c1c00148564000008501a01d002900356001603407032000c000d5841440701c112901c060701d2402640c1c0440c1040c13000031001e600200780b45040320041c0c4c220241d400610f01e000c85609208004420 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 847567014 1250 847565764 847565767
    0xc030f041e0c030b010611161502010e010f06170d0c0f081204121106060604170304090f020714031e09010c0c030c0801180f0b15091e091b0904030203 66
    0x140441e90340900b800003103006840000780d550400f40018420700702012825550742c050705000d10143e540e0105035044414842c018072221040346005c84c05400c894a010b0045d6007003c0700c404440b200b56101008403000060b0708402100c0b040c40300c80d01d40d02d602c805000420070300841c010210f011221354603e81031003010792501d46401200304103e840ca058070145d0710940e125032000e2105070001008580403113000010700c1d079441e180000900c244920700405c44d41d8012101d010050030000c0041d54041d1680c175038140051010804100003d412020f01500d20030900061242c000320048115070014040008001520300385c07084440302540208811410071030075900c504046898a032004000d54403800f0030f901d07030502c0c0c40c141909507206090a0074641c04401c07616000104480349255181d81c0c803a54800c4103503100b0034448410030300004955040b41c00d0208200324240320001c1c98000c2032040c60740e1500ca40301d01025541d52600c03102c01180e010084940316405190007500c09920503c2403040f00d = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 847568264 1250 847567014 847567073
    0x103110a090e070806070309020a260d0e18062d0a060305160e01021e01060f080a0615120f020a05040c050c07050907050a03020307032d050c030f04 65
    0x4800712100c040d403240003500000c3d42404000340c180182c0d80c009403c1e00e0240040c07411a00014030140841c4920031101040301c1e42102003601143c80640d100300c80700d0139170300c1d0001043c50150a821825401c2c030f00c1490102c064030760103040c2c2e05000d801a24050a094000901403070310010103a2a144485411035050184030201c1c6e80c5c4c840441c000d00500d5038007107164140a00c0403145422144408400e0048207010405181d0740050601c40d850f0b240c20088005048041d11030b40100107a80010381d5403201d070302c030224004c000018000865031196004019003841c926058024420358041c101c2e0300c8044e01e040e032001c1610b00400310780d850300041c5041e14665658002a00315100d01208401242d0045840c02d01398109001410043c6030582c0d40a80c603103003981004016100304135240051550100c00704909a202c7e42c020154a41035468040d26503a49440c0e0b1a0307203040803007440c0070b010b040000050b0466452002c1d680990318481c80b501e4036484075030301c010310301c914006041c00f03251901d82c40 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 847569514 1250 847568264 847568279
    0x5060a0e01150e06160219120f1b051c030201021c0b0a08030a080c0a0c0203120c0c1c0f0312050a02030a0b0f0d020114090a0e01091d060103110a 64
    0x400d000b028248201c084840d20020301401c0e4407001003015104050605c0500d001c2020444000300407541218001e84c03550f0120040b552084c92504026110039018000c203003080304900c01c0c41c82c014000d00702010840e000100100340c10300c081c02001c0d0031101c40d00d00c031a440307a900001d0090051080c0009400c01003842c8443d01d01640b1040c442d100592209429601810400041000b500d01d900c0610b1410120300000390100001a10343d9400843c00981445071500c1400740355801c95000f01030311504a40902585000d812a10710050349028175501c0b60f045280c1038040b00200c26180d914041415107640f1000e2619040c150140c090085070861503001003054031030a88204400c290051300d80c05c00c0c50031481105c2030401001d000e21050f00e0041026602d070485548010b509103071581c458203c469002d5103500440304450781014204402141c2241c1c0343c032100d4180d941c0020104101d00c105400c07884044400c01e48035034070f604200700500104442c4090404041000b0740001e00c01703640ca038103 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 847570764 1250 847569514 847569539
    0x1e032107090306021201060e06030106020a0803060a0e04050610090606020712061103090a030e04020a05030f0a020405060c1c090b0403030513180b09060f10050306040b0a030308070206070302070c0905060a 90
    0x69917620f0302c40600510056812030f1030a05440b205560103800c40d81032000c060350f9140704d0f280c09488500080002426552150407030009807240c510031041070b04091030203966520003514070100041c1e0003070002c600990207215000440f0b2865000306030061070704161928002c2006402d80d9016102c01c00441c8280c100e100540c011102000101103c00060900410340803201c845103108500402c50400640e030300c08140e0790803245483c810316141e140d01d20608000c0c82694403150b080000440c40e00091540455110390b0705101032024000d8420b082801c0b12846814000c0c00907440040c031042c00800d10400141c0044d02c56140c000003207680303030584404410b003500f2203212a2501c0f40b000322410304210741c42540040c010794030301281c1408040003030014003801c0240340401401100041242d6102c2e0844422064080e040803441ca449040003005000102c0e0308034058400c1c080400c800c0782c440c0c800c0b144010381201c5004545402d10004101804014140aa10403004072001c02c00d1050b240 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 847572014 1250 847570764 847570777
    0xc0d080901150e01080d050405060304110a260f070e07081f170129040b0d06020c0705100e0616151409010f1802040228021e03210709030602 62
    0x10900c3d961601c03205a01c0d25915003589030030003030b09110400c22a00c40307500750f036001075208160300781c25900c0e01c000c5020703a24154004028a202d100c03550300c1e07204504038140300f030003143d4080c3c0c0c400256130840541e07075506a12501104542580015500901c90088a40c001781031154000c0f9030ac1044802020013405500706504403456030000d140036000034031070b00d2802450f25000300a0340e0401682807007000c0c00b50460718021511880c2c2502c1d0303035580030201c0b0b240662221046441d0b0044100350399613805940240f90051342e803c41c0c904847c40c0241c6e0f40e1910190014012071800300d240600c001d89980742c460495807200244c0081c40a0a101d008a030004000c4000785d070502c0c5410100c55096450741c200c01036a192030600710203a4200c841c603031144100e8040d40d002d80d42c1c12103600d2103502e012540c0002c0503c01e04016500001035804105042c01d4030203030304004d02001030713100341035164800d0240305811800f4109804115050b440b81050b03101c1100d007021003149550352100000d980c4840d = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 847573264 1250 847572014 847572029
    0x210050f180f0a120306050d02030c040c020f03030a06060807020703080412080f0c06090601061b12020c03120901182103050d09030e0a120b01140d020406030f020f0301020c0d08090115 81
    0x5100b00c205e41c11300c140e07070040c142243e006102c0441c8ea00070907100d21091500c0b40c0540d403a00d20035200c49000300300c00d04480c450ba40840b5500c1c6841c14000e80109100e01450300013070a0750000ca13440c40d00c0011030714243c0ba00410141e1903c1d02d8030744217002c1c12031001011a0140c80c2409108812030381080504a0758920902802951401c00105404c00e0b10517000281400390088182c542d000e540c495400d0800d511a00301a070a1034404010b924100c9070007986c5074540f05052a03058544074a00c060040300b41c080e01d03a0180c0c040601c0c030900c00413210780500a03c1c40c50401d0b100c0250300c800b00c0c0300c0012a0080c1400d40c50507560030407050580d0406502580452030030700208450f400c04004000040c22003820510521025603110f51600c0780c18443c080c1d0300c44c0d010001e0000c61342c46d4000c1d0755001d0381c024801c101c1c031596413814004010000c04c05900c980210020052107040600880b441c2c0b02c00c110162089051084064850710f070080e000404030b640e100361160703918000c06650310242811 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 847574514 1250 847573264 847573283
    0x1050910150b161110050a05070516060909060b07031b0f02042f0702010801030f30030506030109050d1206080a050c15070b04020d031701090204060210050f180f0a 72
    0x15418400d4200d8413000883d80030b601c24108142d4029070110035141c1101041c80e01d10b5464149050051524a4030707615030743c00141000001903103a810600c41001c42300400c40600412365520001540c0340151000940420300705021b56442400c5400c1c40c001d100e00c1403080c0c1e200f0030032507004a003c03100c042c3c0364180c900d019003240e045084c1c0310307a0b44908c2a0020b01603c510313121156000a11403407061000810180801003110200594000304c04c0200c600540b11000344600001d0403002d45180441c24004249440d02240c001e0134180545010550040010b180d10700d000c0404070342c140d611b21070011010340c0d154004103502105010072420389020300300400da50800101082401c100307a0b8a080000b5401700320310000900181c03003442e80190112004030f110407140c101aa80030807001c68062249040000100303c001e0b844c0d01034425942994221049050440d42803c100c2c1c8007603650300c0003800e51400180f041010f80e0303000703903283c0c0050b82522048004108014600400c040b021100007c8 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 847575764 1250 847574514 847574557
    0x91501090c140f070f02031c0203072d2d080403030206060919050c120907030c230603180304060801230f090a0b1509040e01050910150b 60
    0x288480d090300e542c4a00400c0514002050450025034420444020070a01c05503e074101590b0701807003c01c00107020a1003401d5580030780b01c1e0003912035111103002c494151501480342c600b1141c5007400c03248981c03c0105003d1220300e584607032070034505070818803ea030140c0640c41000c03402c0140b48012044d00c034400107030b00d032810b600c0c4c00323418500c00401241c01044460f0070031200d10300485450281c01000a400078990300c402c40915014810480c407040300713804400034801944c1d40020200c0c1124000d0120b006440e4580e500c9100c3d01080a42410441c8070000700104d041c90241b00031070f04120070b000340f0040503c5c03614a9a003141c000750700000100340341c0d01c01084000442410200020151f5000f10a080403040000e08001040c041c440c1c042c0c880c510000b0080c5d0403e074028010200001c00c00c10068802504031001503002c400360074000e6003421035a900d58281405401d0148420b03d01910b0f200e030154092074010880c4604414510050ac030002034554140f90040c01c4000881d224182400c9 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 847577014 1250 847575764 847575767
    0x60207091d030f0a200d02010506030c03070e06030f1f0c03091e15020309071d070e0628080603011a0f220c030e0f06090a020603091501090c 62
    0x240c4101c140050600108003845038280c0c04030443c0d1180c0c140d1048a600c40204960894040e12189a40580c0b5410085000c04100b0002021500c00c25540d00900c42c070740c2c8070418140c88406001c0200d4140c3d0100c1c500f4000c05410031152540107034003034112004006003140342843e1210a8080341c110b244080d014000744542e600070100000300e2414207200c03134080c5a582c5115041640d015010403030045000c5d10400c411131020010443c00b8242c10343d100e003401345500c0e49800c01407103046c03250102559907003100075400d201c0510891035038803103100b201c2070701007449959401202244881c0b4001c410701c0840510001303960078244034598032244a480c02c2e6040c5821204400c0822003040100c001011550b611800340f88d4407208242e84150181d5800101c96a40f4042080590b054904050300d580582e80d1541c070449400d8a48002c80d07404e401040074840d150b41040d10a03901c26041780030b0310070142c200032004580203000102110300340021140533100242c000e8208040b0700d03407950072800c0c42d0b5 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 847578264 1250 847577014 847577021
    0xa03080709060f08240411031f050907050a0c0b040b0103020f04090b0c0a030905010501080102071106043012020f16060903110604150e032b03050a0b060406020709 72
    0x408203801c2070014043e550f00060295a00100715643c1e441d031aa00829801d44060742d4803601900140c401c0c000d6248241c00b01c0c0f4603403c1200c44844443d8078110100c040114149183d0440d00d0181c141c14058440b0741084030745a100c00c00b130030306015040407071800141000e00c1541c49640142c68003581541144100065120046a054030030340c205980e60020412030003010381c2204044040300c0e03980340d1002056004c0c02c420f00c0003038031341d502e04000000c0c00d00040d0014480c1d141720301319071079481401c0010007550307014602410449201200c0065076003501d0402c452582c5981800c0e040449103295204181021100c002c3c0700145c01c1940b804008800c20452201c2c0e2064100404d81c03c00c4c2888002010b44090b4880580703109242c00000c010342d00c4070700803500640a9000c009001c0300c554a00a0490400c4500c034038003901c1010f900707160800703000303940025800c100c0c44104a40103542008401800b4042c240c1142c650343c038114480b065480c40000c200810035a000341c01c04529005000048 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 847579514 1250 847578264 847578269
    0x30c0305010e1c080a051909380a020d11040b0c0637060f06080114010f08040602030612062d0606041203020c090a061712041401020f0a03080709 64
    0x150920042180b43d0b141d0060720040d072120688100040594452201410f81c00c011071505c40100e140c221404241b05071b00c01c8a900c90728030a0411041d0f0b448824040c0d051044400380e0b60f001401c00404500d14070701f19001400c4046054501081000c00c1080c018a29807087c0d00908030350400290108221109000045d13201c4504800002400346001c0d0307500520b11500300051850118020010000045a00240c003801c8880b03650321030643c031054064074001c0280101e4030341c110510007540d401d40c4078840c030011072a521354401440b0340b01da0ba2040d0103500701610071640000700e204401004201000001e2040c04014443ca100d009440142d101c20907488680e245003a03440c03401c2100c151284c0c0c0c01c4030220341b070300480200001d0b21424105d04044a4450a80e80704c00c4003002d2044000031500003105072444100c59078020b60f0f03007054155550000c514408003108042c04104901844451421004041070041e9504034140921041c104602c407407048011900550a00c071583d584014400302 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 847580764 1250 847579514 847579543
    0x5040b0a0b06040b0a020a080a020d1205161d130c03060512032a0106031b09020325051c0e0d0903110607030c0f0302072301090e090106030c0305010e 66
    0x403015900001c80c600f4800d40c0078003d10300d000041c0029a2070f1080081004954120320425200c14140c20001d4580c800f5215040c001804940403460807150391007040d0040041c400d00d108031071a404401c1d108000c0050800c503000c801140d0b05c00d880e45480043c041c05104803400011000070b540c4004d0222103003a00114001c0c40e4103c3c042043ca40f000045a440281c42d64112542010a511000212000400c0b0044650030300c04d0010400004d103881030a0820740403503091000f5113411200040b800221101d180a141d0308078410050014442002c420150074071742145420350013040c42020040c14401d08003070a070f50342c9051100380410301000c81e1150316442c1902c01d5500d035459440000440302e450620580001410310101070044440740e9000c2e601c550300001403115030902a4554a0b180b142c00c22810740c60b1003407031045450403048003070038005848802c001e0b802c0c0001082c0d403041c000c0004055650794800400030403000980040254801d10011035043d000f05501828018a07070003100 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 847582014 1250 847580764 847580771
    0x10c0c0b040206030a0b0d1101120c0806130e0d0507020a050f01141c050f0f01090501050102030f0f0d090c180203062101090b0c040303031413120207080d0305040b0a 73
    0x1000503500800c00303821903011210f9a4507515240c800800610440b81c04c00d0b03004460820700c4041112400701c0501c601c2d000d0f200d00c0c0c0380c0407044c000002940e85150403000001d4620001541c1c514141030030144114404200107113101409010524000c0480940701c00304401150000451504a8042015000558401c4da0100001002815141620301a40d000c0e4402290700d50a650f10068030740740d094444502441031341440100f01176200720941c1c1001d00014030800100c0c40c0e22260061604813135069000307500c0c2413000c04038821940c101c10ba5a03500c0707010800035032050310340341d008c0c2d0000301c0d02541822444034500700e104d65a03140d070f1340b0140500a00620402141d50346e14074410b407600a00c14005116001c0075400b250040c01c0c0c04000038410b4203160305020302c9003940341c040e02c1528440e4808000b002d0708071400b103100c001d04a5101038405041041c00d00014156407850001207070b103004031480c0075107600c0301c64105502c0d500c40400203542e510800c0280800846136139002404040100f = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 847583264 1250 847582014 847582037
    0x30309140708060c040e28021201061209050303010b070c030501140105010810080a030c1e110a0f051e12060103050a110904020f010e0f0901030605010302040c1103090904030c050d030608010c 84
    0x40d0b07940d00000c0440720360848040c2d2103080a00d00341f03110640400ca40c44215603883d024142511000700a02035a00041c10340154903049070707a01c0c070030710030350341c1c2c000c002581180e01c0e00c201c2030701950110104842049220800200162090140940001d5001c01caa0019810000010881d54000305003604012a12400f04004000800d410020b0340c1c05140070040c400050410000e009c01541148104402e1a42c8400501c041115512050740c01218200d82c019a5001840e9140003240103840d4000014803440e403031040000c1011260103400340525520b208034107101c60402c0340903402a1038640208074100d080080c3e10b4052403150404039a92070150426401240e000410400c2d114103001d02d00601348007965462110b0040180014240130351036840b403511740080c28082c0300c228001c504010485034500d00500c151312001054030011814504100104542c000707000e002941172040d140c082901298060000050303007041520007180a514210405007154000c000c1c4800700010803000 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 847584514 1250 847583264 847583279
    0xe060907060c02010c0309170607021002040b03060609030a0c0b07020a1a0d05090c0a03031d030111030a0b04092118080a03030b30070e100909030309140708060c04 72
    0x105080c00c0e02840e1400a4000306e180c2940c1e208415048608408a6001c1e42c400000d800501c061003a02c10750b00381c1e61000b0031044e03100c090340514042e09607250001d10020b111420300c3c070080d009400307006080701c0601c0c1c101e840d0711130024030075086003554050024035841542460903801008000e02c007600c0c584000d40e1196121680180b90000e40e5998950003c140f2241e410032815a200d613004044109a60707807451702801c807014040e01020010b02c601003640082c6810721034400c02e00114440c403403035583d0f4091501c006000d00440185c0c00b41d5180440740105a494540c20300c20103420881c000d090301a08805014240b0490300c2e80b5190a04c10000c1c0b1110102060b0319800c1541401c010480c51003040008420380317001c80100030705035030509000300c0d00003078008444c042001d034905035888543c8404810380c0d4400c040713800703511450201070100070a403d5980880247d901a180010703150903242d444550703441501480c0111580b0041051061110900810b038000100504042c9070614080c40c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 847585764 1250 847584514 847584527
    0x30108211e0901020f011d120f04151101050c1b07050f04200a1e02030708090d0f020405010f05132c030c1c08010603140109020f0903100e06090706 65
    0x300e9100001c01180d140c8259008106000146080c0402401041542c0d24020081005c0f07124a412a109240b00c1042c68040b0a0441e90501c2d85089024640ba051100c0042d07072904a1011000704494070454102d00c071820b21481e4080c003411451b103540e6641c000c9100e120b008c0c00c000020b00d90b8204d11010450f60355047e4040300c0c035150680b00810180602044c0640700545140420806100060140f200346d91040c01e0002c107240812030350b41c00c52003104007240d0300d02400400805821041000d1702640c81c01a21115049114203454840c0b0a842d50118090720821303404001c020494a03c1446103181210b4036265441079000108224075504140707005e54100000031440c2c500001c000130800e96401d02c2180c4400041c40201c42030380203550b8031078003060f0130484284009040c0c20008141d403480707402085203040f846501c8405c0759090840c814003d500491481004400800c034028190700c051081002c61128882c001410250020300c407420f082d00101002c070103802a40c0107202030b50308040c = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 847587014 1250 847585764 847585807
    0xd090302090c070c031b080607080a270f1e0308130c03050f070602060c0304050615030309040e060405060a02090904060b0112020301080c2d040b03030405040203010821 74
    0x7554180d068889000c1a4400c1c811080050041000d0070004000d02c186a110705603c84c02801042e403102e42d4801841d0f44460040c1d40304c800240c15840425610b00c82c9030401d8840941046030819200e0b00c2d880c040f21b600060107000c8900389aa01c2c407101c103003c40042504204e051a400d07402030b07182261b80040884100400c041d0034222102c03898402d02030174807080c4d009144e200c01101c2c0e0003101040700030343d82c00b11480303450014891980040c8489843c54140c0e400340d503014004203241c0d01c0e4070b14200c0105060301c40054140c8400e0000c99025901c502900d00841c03080005000340f400d0a040c400e00b00f2038000d1440410324010014001680c589402c000d40c03107a001071000803020300341001280d0300c002e04407101c1c0000740040700115151702c0104418035440310441c0d650301620728bc0a0408041d80f4000b54101c4403111541000780242460b030030801a4441c01410780e4a032584031400074049820a07089040603600c610702e071000b0130000c00e1080d4001c609201d00a03043c11140001c0103202d20914 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 847588264 1250 847587014 847587019
    0x201110913020904060608090607090b071e05030313060f02040807060f0c0b010312030e1501120c0503100617030c10020702040e011d25050d020105040f1202040e0d090302 75
    0x11400034464511582c1501c906000051013403100380c1c1d0f40d801c010704101d03083d2082001802000086448617019651380001c89148451060420b04140c403181030064010710b13a0b021201c16899250000b6505100039440791030508104861341955040080c11030300c0070488021079503c100004c2c0140c070000205201100d80d1b5160051455603c401d0486415814401c01881594500c0012040042140c0e0172110703804140e4040003c0c5010f0311312540d986021391340c1014100c90050040c0030703102d01c1020b120707800344c09030340c15000e425a603c01180c545055440803565440e9a14018030031030400c50060048001c0780001541001c250082094030b810550005120b5990b0000c0c080c0c045486a800c00d0000c042480000c02c031250f102e5505120480d0b080c0d00c080c1450040c403a18561026a412a039101c0311503144810a08501301028007003400e0708548180d05000f400e0100050142c420300c00326000c0c0070305802c116020790007841400b0558608540403900d981010740480060b0b54007035150012030341c04 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 847589514 1250 847588264 847588279
    0x2091c081c060f0302040e030d0c0509090604090f0b0a0204080a061401080706080f070e030d030b04060518040204020a1b03030b011404150305043e04060b070f0303140f061002011109 80
    0xb18039007c1d103144961304806400c1c80c10722030a11203481c0c0010150841020944449020340c1c0da0400300001c442803c0b00c01041d0284524481011802c214400b81d44480b103031800529007a2182c2c2c10a00d40301d00c4605c122502c40d143d082c07901540001600701801008054000c0c04070508090340a4904400104008000c03a0a9400100c10620854081d00c1d1800040d0648440601040000b030203854518011030080b4200440042c0c40c3c10901c813500c500c401c40307120350b41082d12650300b00000381d80084403560030130810881c0313519000420b03c1340301ca11510940700007130104a0907002404c04143d0615989400701c091200f0041443c1b1072180f00c0410200c2c0c40c00144954451500e04450010340b142d181503031710420009400d14401c1000c009001c0f004410541007542c048042000f5201d40c2d000d0a000b1100920640001580480583c10220b10a05010070803159189407095081d00440b020207421045009000c00303410710900602510305144000d0050030b10003c4000f01e280f00700c0211900404c074 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 847590764 1250 847589514 847589531
    0x4031a040c0e0f0403080114210c0a0e040501060e060604120201180902091f09031e0f030e101e1202041802033702091c081c060f030204 60
    0xc5541c06180500b50321003581d41c1c10709003c6541090840120340880204041400116420000034086d5031030900080c0741c0e0b2203c070045001084107035a10408550070b0b10030020045840d5031400421405041d104004411500d02402d10b10f00b075415962011203901411800e10080f51070710310803641a185100362261a6500c14801211807000500e01070b4055458500c0204284640360000c02548100300c3e01e81003e038207000086501210014208000b09550304070400008441c1e00e00e092002182180703c40e00c605007501c800131142c2110f0340031000207406444540c51b41c6041c040c0c1010240c400e00c1d02e5004d60040c00040c41100c00000c240c9418070a80704114181c0d001c0b0754048501511002c650729044607002150749019400644505002d04d49894003169075442080200c0d402410b162100302c8502e01200b1058029400111060381000403451108460341520340d069011074450900c190351103482c0c103c0c1e103000c0c1000f90518100702b4101403080000b05a100c0b040710689404603000544c80302e = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 847592014 1250 847590764 847590773
    0x1203230c06040b1b030906011e08010618061e06110a02030114060307050909100f0608030a0f08011409010e0718031101260406092a0f0b04031a04 64
    0x10105030001a2041d841004100200303201c00c940030b001058065406003c1c02c3e0b54403081c40c0001c5403108800d5101b100100007060320100e09480d200400d6a111050740d4407000c4003400d4501c10f030001084c0800f61801c040b00205144941402005006502d00c200c80b5a88030111408005200750420403442e642c852500320300078821541407660003002004200b6184a60041c5030a08a030814800d005004000506023445d0301141d100d2380101010f82100522030146200500310400c21103500d55a60f840031521081c2080201280c2c40c06854101606501e1700c4000c090704016003040ca0141e0800b640410b0030345503902600e040d03480d00484142d01d80d0ba0701380c0c100c91704407035980c0c12010804031000010501442100c042180102a84ca541c008a2101c0e18048080c4401e61401000a4900005008202cac554402e40d075040c81030045025a040c0e40342140f420100e80355922242411b490400c00286402c826140002c00f20140e120341414034586403103008181180225582019410020382000b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 847593264 1250 847592014 847592017
    0x2712050d020c040614040f110d0902130902010c0f1e030503190c0e1c020907050307030f0902100513081e1504031b0602041d0a0e12030115030e010203130b01120323 72
    0xb200030007823a84511901c0142c50181003800016401909540721941c80401a4000c119019406071030f900035010260b5030308082c0e81c0ca61902503a600740c2c6480300a00c46441142400901400780c0c0c0c1395a1031b410903541c80140541c5a20352072515510b05004491071941194804007090401c880500c40403001d081003102c0b895404200070344c0704c0c80309001c1120050300080030b1802400d040d581085800c0703031142000c085070b5205c000031358000521003410580da80310300000d000e005810041031038941e40d02c08040b851f0038525901d220ba003450f03140d50a41d0382c100400000c5101c0070b81d0f1022100506050300c6c00f807c80c0c1000b0700152000c0107681c800d00180f10b001d404881c010000c0ca40c11090012140444841d00e40055941c41c4a050619280311074400700000c550368900072040360149140d103040280010300814054440605480e141c1c44440b0b032000788080c0d4451080140c9805821045141521048005800005078503143c5560341001ca5445407200b20500c01030300d070701d0074241da071010401e809 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 847594514 1250 847593264 847593281
    0x5090105070f0b0f13050319031b0f0f021605150f040b0a030e010209010f0f090504090c05100f09050d11310605012712050d020c040614040f 62
    0x503004120002040212030a601ca01c41d51101881319410344071650101d800000851014221740e1052100520180100f41005403448040c2000544482e42c81d2003c0e030004001720090000c80e40454202c0d4505410500d4030004982c107101a11880c21800c0c3c20700d035400300038041c8130300450f9000f4124968218131822140c4890301c10740c80580b1981d0316400802290700c212911b400082c109136889040800c14001d40310185070503125a141e00100d00811501451078000c501c04024040a000a554585114440b0524010141e1000141c10704060010007402a0b48110802c00b40c3c64160f005940d1100013401611000c40c2e11030780c2c101c80350600ca56202c00d90b540d1268001095003001c40030200032590203411803905003651550300d0425940004850280c401c0f0341c003103605035500010720010070300c942c0c1c04140c1499550100319140e0350012400081070804075110740c000030944e03202e26010070a1240b41c8000f250284501400c0105058200141000f50380c000c0d6195540c2c41102e070602e4000d00745 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 847595764 1250 847594514 847594523
    0x2030313050c0a24110a021917010911010206060d080901200f0c04180303050604090501110c01060e0c09040203070306230a0902130e1003020603070c0605071e0509010507 75
    0x409503c03040b8034040398007802030312404c00c0000141d2034495401030030101c0c0004126005803660325003135028004910080440750500321700300c17000464144201c4480b03002840001c000000c410383e840c500501401d080008140c10365009904005042c2d48040100b1200365102c03444646404512b40140c1e10740c10f228000780d8600b00c1c9240181d048171000500280c0782001001160304010090040c40100c1c0d040100c1ca090400e44280c8940100340250801501302030041d1000a036107411380c40303088c01c4a0454843d025254000144a43e0142c0c0034000d10010740884a01403c441c14001c510b040584038907c0b18600030358004c0001001d141c00380d441000240030058440318400040700e0b5000c01810980481e522400600102140c41c481c107109440ca03c908040b20a2103503400c14085290910b4000c06041c3c0040700307130350040016110a0090b501502c0700c0e450308036070f0090600d8220305480004000c601000485104403140e00c2c0c0c1ea8682031003000c40b504049548844c1403004981c00c0c410300d1340140 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 847597014 1250 847595764 847595779
    0x2150f0430080a0302130e070323060906040504060e160906270b0d06090309091b02060c090103060506040e160f05090f04141602010c0f02030313050c 66
    0x100c080360582802800d154410410008030300341607400803160004480505802c80c00e10030095907a00039801030030b040c4005904204030640d07a0b60080c041280460b030000000703481c0e91050a171031200c80041c540c1c0c5480044480781520701100800d50029005090a20603a19600810180040c03580541b0021000e40152044840d000d6042d015141180c40384404080c40c1480000e0071085203c42c2543c1d07031205562004400c2101503120000d0b1048000c80c03540100340309207080001d840d134882d40e0040c80c400e44685003d54a04480390f01213030b24040b06000c294400f020b0407402103038046075043e4028809001952284204801200240960f810a40d0031183c001000b1402051030759002d1320485242c0403141c25651260070866000e600c01d01d0b85400b1403418041d45401c4e04e02020315400f4080c0103440080d04054030ba212034809102510800300c0040002c0070507510f5642030088814105007400c04580300401170b4402943c070711000744520121690303850144100601442880c0d0316060040a56 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 847598264 1250 847597014 847597019
    0x61401300606120501090308150109030206030402060c030a0e1f05070f2607111f0807021005040f05011401060507060207080d0908040815071205060f0312181c02150f04 74
    0x44d80203180b6900305078003050a2400088082d00f07440d1040744080e0040c1e560710303601752a581c2403008a400160040740d00c02d100b03203c00080701d8010005015a0001940d8011031005100f0501c210741d450f485210b03c5c9500032417890b4407000c1d000310441e0030082d030008825800400c141401c0301d045210141c1441c803e941404540c01078409880a084040d0080d9901c5202c40045020424841801004000c030841030003c03884540780582001e0758031461a006560203540021404000c440701201d0448102d40c3c141004070902809100e81d8a50000000b410021035060640140c4503003d11040103016507000100001000445415200a0b848414080c032400c0c0aa1500c41c1468016000c3c54160b84105101c02c034081241b80302c030f24040e0720a80c8032418450641c80200b805000c1c001c011315048840034001780da164604201c850510202d00c036201c0c0e1180046950810b0700c00c403800c8a20303c500c200c11600c0441080d20001c01c0302c5250b04440e14a508504181101094001e0746443c01050303e010400 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 847599514 1250 847598264 847598273
    0x3010f0b160b09010614041b0f0309060c0f1d1f090f121202010501050105090f012616020a0203071e03061104050f030a150b1c06140130060612 63
    0x400146c9036820b0100c0c0b4050704000078402102c5540f000e2001c952440121901c0d8030b4000c1400b01d00c4000c1c01d19000c588850641c4414081c0c6440401080000380035020498000e130740021885141c502c40400c501000140d800015102c150b00b00100365003500b00c82207030282a0041400100030100981407441041d6102708089a0b206130780b4050342c0035005400300e004100d106108150684070141c690b542800c4090382440340049032084900c2c184080d002d6000420b44e400b41000750a0701c00000d0400b030614183c03122410005642c884002598000701c110350050b60049080f1058900c5e0110501c80c083c0a17500c0401440d00039440940842e150640c40c40d00d04820b07500600641e036041c0d44001d0009443d134103041e40c501c4484e034081d19450080e801000e960045410040351102c00600c810180000c09541011207108403c040f40c3c81e82c0e131410640c5801c02e00380c03000c900400047c54ac4145040e800400c0440300d00d180040d08507255502180d0404000142d03010b88054005100d0849501e8841e181 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 847600764 1250 847599514 847599521
    0x402132c01090b0316080303190603060e06041514041202120304050106061e0507021e180603010507320d09030e033c1216030e030303010f0b160b0901 66
    0x161035004e80281c802001c0d01620300800c0a040300c01d10f80096186507140c0c0c92060340d4880c1015005181901e03034200002041c3c0f1406948030390b8a290025291904280c076058001c07050303080c03411031150b0500c0f8800003c205c0140c07481d40d00c1900164180b40031180c6000803801d01c00402140400d295020050105200055200c041650b1480e140c2d803541a0b0701020018204411686135000528104041c10040c02c058a00010310300c3c00c0d9198032040c80c4502d0004100303804c0c204942201050540411002c0e00d02405116000780c0395003454148800d5040d0718401200d09035040d0f081200c0503c1d12800d0f6502200210342e1054801c5004004c112180d2030024200c4103040c031072920134490107407040d014500180c070030086004040c0419200000303501406078000c43d05074540744140500d02038120603e8115005040312142c8038414015010310385030140144a804441c24020b034003d00061103126410042c200030b41e01c51183c115210611004140c010125508000700200f500d6014083d50600540 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 847602014 1250 847600764 847600781
    0x301150e090309060307030914030301090e190302030a050a09030b042f1c0c05060f040819022d10090918020634030c020f0402132c0109 60
    0x249803055110074103100c0c0c0d2405041c83c2c899020400308045a8004d0190303001200750382c03181c401d142181c48000b0a240c2150030036030150a5031515181c80c1500c0050a1200d44500d0344d070500020100c00d11618002d64030b004001905085c400b0000e4050341d0140200e00f0b0100640d0f10800a00d1545068a4401b1094502e000030507240c055105407003140030000d846100d41041c0103058000b4400d000305182041034022070f000c0d00c484c490000e0104140e142c1a00420143c0d4291341c0c40350769a4030341540d02c2d2a20380450f0000445094490b140c1c00141d81e10314101da03941c600c3c0700c0c03002c0348201c0c94540306131417001801026900031523940c500c45920b9007140143d030480d6015001000043c43c2140c5405000703103414002035024804212840340d00035900130010680f940820b00800d079410284002800d5140114143c0102d40d505e0084002c5103014404114464016902581800345640102c181c5048502071000c000d0240d40600d107a00e400984035001c12182ea800d111a5940c0d54420070b030043c003403003 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 847603264 1250 847602014 847602029
    0x20304080703121812031103180d020703030e220c1101110c1005070201020405030a0b060406090e060a0b030f0304290a020304180b10030506040518030f0d0b030115 72
    0x1405080d0f8407268480c0c40e0107486030548000103410f89035162450140c200801d003091569401c00000400d1806000e140b00d40c0301001c1c2d200c03100c0d081c40b180d00c2c0703031040124079182150b1101e0020700029a00031101e040c880016298a60020710f1803071061101220060080c840034649488103450561001c038a036000d110705030003000f1003841e28800f40b03920b10840112421030350001604258049090380600c3d84030b000c2e8070005007040d413140002400e2000a041c244e410420103c01c0c04000d103058403484004146503c030400c03400c0205034440351101c07001003001d034401d640c44042c02d1140e00d09214001d802c00c1c0325010350b50b4807a10f450011541100c41542c2d40d0541c2c44582da0625451010344c2140c103100c07d01d800030741c1050b01d0141c43c0604410007029080c40740c2c4d1036800c139628076215180704280701d0200b5280802c0c1c0e450950184000c690b00100700021a14166090f9111400c01004407480c9102004101c2e0703031005448a540090b1050141c1c0541540c40c180c882c142c00381c030b01041d2005440c00d1 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 847604514 1250 847603264 847603277
    0x270609060f03180129030a020a08070e0c04030f030c0c030b100806011a04030b07020322080c0307051f050403050601060503041a07170601171515030f070e0a09020304080703 76
    0x2004001c0d00f00e03174240c0b03050342d400f210a180850207800300d810001c49011004080b40c3d99004181d0210740040d030f0306d504c01380180c0c1c042101841605500c104260780300441c10790f80750030207103580c40303110020f03000c03400107000c3c00a02460b090a112442c0240805150071904569140c02c0c02c070078842107900280705040f0107014800022a800300c0503d4031402d011602d81540d41801e04640300d094039114050700c01010b5100820850314860081c5030051081810802d00c44044e40c80c1c42042c40c2017122040c400343c485c0c0c205040c1400385079a5a500007104030f02d00d41c420b00c44442100c8098a070b503c00c40d000507040c2d00ca000000038589900100440c445c2c2d206100062000a001e100340008079429201e000200c0e003206a50b04c0d0403812040f00590025051411982407290090750241d082000e407115822130202c054800020f080c10b2071850b0780300c2c010174005451071501300811030750b00d18050a5807007000300d0489203450660720315451801400e40c0000845d03523802d0071303d800c58a903030150381e044020601 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 847605764 1250 847604514 847604551
    0x605090f06180d0504140609060d0513060b010f080c0c0c0a030605070f050f0913090605150a060216090e010b0a06120b100e0909011512021203270609060f03 69
    0x708006172170848010009034560036800108201c12600803114480e04803d040c03100c0c0c900c04959008071030248003c06404c64a0082500b801402e42d06858100741c144441c100e0410080c0b54040355003a03110601c1c2e04480d44441c0c090460394140140a082c095100010a0003c41800113543c4594021401611600081c081404e8281c030140505c50b660002d481c000d00c88031800e400c00e40005480c3c0b002041c1c0014560081d80da030601140c100740c1d401d0044815021640c2641c2c01c1c86168400904410700007800400d903921101c00c0003c9540c0030b501c1c3d655403500c88441c60040e09400096820348010709030a680c41d260380c070090040c00700c200001e509030b05008a80c051400c0916505150303210581d102d5803421414401d0002911019111004c00d643c1c402d85114a21000545000503213000b40110703030000001d0040050ba162411901e8084d030b0000c00084203000aa140c50400e5412100a0103980041039400180c90f8050000602d4019100244000d09035038820000c5210f4818003031544610348 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 847607014 1250 847605764 847605767
    0x20f0a081c150b0901030f14100512210405100f0f09051807090807260d08060d15020f0307030f0b09060607021203040e10090506010c0605090f06180d 66
    0x10062a070701d6440d030b8840c140c2402001ca021005028580d010304010900c5444200c200341142c0c5980c9010062a10120620092402034030800d00140021107c410071003503040221921040c000300d40302c41e884044100c0c0c00340320794000e05840082c00000e1401030500340da00005081d0404032203044002410034012000c216002d0000350702601c00140c81a1080701050f080c200032044040d08007010322419603000070f000401080b5140c05840e850396a918001c00b40d044040c00b0281c000300442050304078500458942e6404a04142e00600c00c96103d07019480c20705200100f507004014498005000141d00e441e0003c505c002140070b40500d503010801c442811010004440b0510805a480803268011030300a00d842e40c007030181140020640300b03814101804051459100e03502c030300c1c0340074289010070180c2e43d1100d101c60000c215004003031042c0e2510400013042c6110b001d41c001c04a039590000309800d4101008000d03919503560081b02e0860900303010014603613542512075505032081c00074110405 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 847608264 1250 847607014 847607021
    0x40b040903020105060a08060f070f02010e010e0c0f010503130305031e01270507200106090504060906052a0a030905060906012603040b1e030c0405031005010302030c0d0201020f0a081c 81
    0x140149d0544640c0c9485040b01182c1c00003240f0f071460110740d00d606110404400038813071078403003039550801824580c400341c0501003c42542485107050020a004100c5600300d40c520410280c1e6052501d150380f680c80c9c8000c114030044401404904c4614000086502d0019101583c45150110304400b0b24028003521003007503031302c00c483c09400a621000f111642d085008402c060009041c4004245151940008400c54604039010344000f82c03114201e5041c041d0a1103210b41090070400c5000d445142c110280304620a0080c0b40c0707621a000046850400b0b101c0e07848408656803241c01d44600342007400499030345031400c2c0900303002840c15052a0030f0311a5074654591b46040c049000c0d5003841d28040c1000501e801005072810042d05007031410301d91100c1d0200851045900b0f000b40c0742c445042805051a00e814000e6a43c03940b80b03044014805a6000951111f120808640808400559100403810301d10200100703125441040102810031500901a2282c0301d640d6a0180d46d01c200e195480c8181d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 847609514 1250 847608264 847608271
    0x130213150f081f05130215040803181228320105090706021b150c0d0906080606030112050a05030f0d0b0a050d0b0a060506030a020909090a0312020702040b040903020105060a0806 78
    0x1c5c0880c0752008014107044075040e14002109401d0707400c20369034801043c1598407201c1040800f40907800e170940320b45403800da0403125a5103207005008102a1540e0304030358608603412a200c20b46110030810400c0340d81d00148030502d41ca50401290ba17800400c01c00d400c10b44803d0488d01d903500b00400103602480014018088070490b60040445446000842c0120a0003d03002c6402c050a03941c40b0b030340d02281d4401001c060000c0d000402d0400b0503480000c111105c0c540040c000c000d048000d206640e941d11060340e05560012000340c584100314035080346080100840207160f804041421103568007490060b06161500e8403090099504180c03c02000030300c3d500403aa40704c2c1c0080f0840000c0fa62006410ba80480040310000305540c0314030004005420894000201b50780000c0e140d14182070641e245608540800001c0016200581c1c02070920840c40d040c800358640c2c01f045c40b00c20b42d640d0381c020200751400500f08000e00b02540c10001c0c040c0608580160040c0136219000900708400120a4407 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 847610764 1250 847609514 847609531
    0x310051e10030b0a05010e030a0507030c080d02010e2e060605030a0b06120406090218010f06030c050a02060a0c090b0f0c06012108090a051c0b130213150f081f05 71
    0x413014103140041d180002c403c1d0317a031900751280c1080c84002440403c000703009980601c0481c0155458918103502c0d00035011152070459040800510f10140002800311904003200c40c1e05171080342c03a0a4420007800c0e07601200402030704011002800540002c0218000c1070404018004001c2c00300c1840114450b03007141b48558015000000c02041c8540e03c45040288000d0901710000210145c1c0c1c040700100382c129480b0350b6450802081032681501c62640e034000703a804c15a0031b100740003001035220038004100110458641d0001050a44a0030f0404058400f210b012510340d64401000c00b03803608040c19280d980e124550000c9044c595280b00e06802c0404d40324041210812030f501c81c46560000943c20380c01405c8050041f4180d691441506600c2d56012208441903100c3d0070701111324070300502845031811b2400e14076000b42e1509000c50754000c1e078007a00400c0002068550040c1f80440e43d10031906a110403030003089108010425105101015480c0040769010401c00c4085403000da68480 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 847612014 1250 847610764 847610779
    0x9030901140a1b060c0e0423060111030f0304060c090e04060b03030403120c02011e1202070c12050d120c090315141303110f060c0310051e10030b 64
    0xc50306200035009004040c1c540c03030300b00d6040d20001d02904041e103a01e1801c840403a01e507030502a60310746c000354115030080c0444040c00703c424040103c00a080040e0a441e40c592114000294a03034050a5100316143c068400c030380d03803510400120319641e0425241251490f0403d002c040982d0b114007031002c15a040c01207010440d849a41c0c65800400201d0a929010f000902c00040460130058100d141c09900d81c850207000341e068030004184080311042c044201c2345070780140c8101580410806a899802080181c1d0f61010342444600c0e40003d601190101501d419000d00300580804e80c2c0140c2c1801d6103551404a10b096107130350690302c8000006000880030401000829a14086a22102c2c15054001070302045650656100501101c48900111440502d03100b05580144100c1040c0703503180c060324200d80d610070180d032a03140181000b040300d400407001c501d124000c0c902e100d0081070000c0c500e4a011601d020601120403036121b8542c4149008042440c03258060700070600c031000c0003010741 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 847613264 1250 847612014 847612037
    0x903120712112b050f0a0b03010f0905160b0f0a0f031503240509060403030510080708070e01060e010c03031109060d0b0319030f08180a0b0f09030901 66
    0x111040d100340140c001d401034441100307125006164004040070403040582c8200120f003110554010300ca402c0d81c0c0c2e024286044200010900100c08141d0031000c3c1d14400705100010500090140003050740c40780c5100c4c5052010000c110001807961f4800b11000e42d0b107a4411782e41d021484990042079501d4142c85403c00906e0b481c0b510032070000d031541004c5d080c001101c1c298080d120b1444000b5030412a01504052a6120860383c0b00400d180c1c1420b800c9024051441d140d46455150a00a8401400d0685820202e022403920202001c060f0144508480b5182d543e81511a51080d483c0304d1170402c0d074401c800120700c0502c44d1541c2341000c54180c4980b0241d64050354205e005000c140405d01500805101a888903543c0034014500b49207501e00202d440c1300d0203020503042512501440395404400029000080d41106c003410070b815050030286000d5440520489911044148012150081d1042c100801613002a110701a51004404000c0ba50318030012550300e100d48006580482d601a150 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 847614514 1250 847613264 847613267
    0x60a0608040b0c0f13180c120905031b011e0b06090d1103011d070b030601080406050a090f060e0d020708030409150f06020303070305100e0c07061401091409031207 72
    0x10b0582094030109094030b4040c042c1c52200d003581082c09130f03030120407054504001103241100c1c1c0c00107902c00444100240d2010030409099181805a248000b64450000e907052060900a6640941c103807040c44c060b03808101040c2c0d00030060710354241030880014011540c50130840c4030342035070190302a1602d86072403c54010030180b90b40f002c000701c408800602c84030400342c500b0301a00c502000c00c80c9010000c40308907190142010701d15000b14400348014000c00545a074041e0429810680050000902c3e8407000d00710b001805410784040e102c1d51084e5841400c001c0d81360700550300320058034151000c0f5518080c00302e0329407010744a481d8169109010512408000341d0241c405140503ca5040403159920701d0f09003251825404640560004810080c410b0b406002d020340c8000c03c580c0f8820560b0900480c9849100050104052490045008030812507140d000d42d0920307403e50030096240da505c002c2000502594045074000c040c2d441e01140d01508000145c448070b4800c03694126041c0e460b801d0 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 847615764 1250 847614514 847614533
    0x1b080703030b032b0915020a030c050a06020a080411150a051305190e161707021005180c04020309060609060d0c180c050915221d060a060804 62
    0xd00e0b0358140521108804600705040b00a803103101c809a02e560030b07440c525800740003540103602c00c80d86101061001d11000c1d501040440c192903241c24040a20038407418658503044601c0d00045c1814400101c4020321034111500c54411445007040411240d1600c0a004010240c071400d9081c03950180440c140a60060028207030000c886c52142c043c0c9965103000070302d4000c50388244441092070306400c1c40501d19410543d039221501d20b800d116034019807a0020000c15068881c407001030281c1c400308015910a01c440440005424000d1005091007402e1103060341b026a0700034018440c46080491606060003628450b603d80c1003c0c00a5a07514014080e20900c02090f50394440e0145c0c4030800017030340c440c03405406403048003a000c14503403c01c03980d07104841d00c54844606201090003000c215503510313640e01550801c03903020b00d600d070b2542d50350700c0450b6001d11903002a15040c028003c5010b00300a10140b9613007802c5500740d1411f8540e07100f0307c030089150340154800a401d510028000ca00040c0 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 847617014 1250 847615764 847615781
    0x20c010305090307060207110109060c0b0c0d1409010f050105041104030f020d021009030308010f030f1506090608030903060105040e061302031e01090b0702030a210b031c1b08070303 80
    0x20540e854482541d172204100c0c0d009101c21166003007105000e0826581c81003900d0064006400c0050401215454501e4000782c003e11501c0e15000008545500b100e850708003022221400d99002200d003010303850a4081d00c1303640c041c00300c0180740c074000043d245854010305600c14603130b021003407900782140c41d00d64010801c58401e0b600000e0314150540140c9510400300c502c55143d64850305020300b14039004010503c183d1100607500d003c02024408105041000d13060254050342d1081c8120440100f4805025964440000c40703240c07800004080002000920040408506440490ba02c072800c1100b01d0b054400a01000e60100f070000e4141d8001000200403240010221039400c281c0140085035039801724400e4000365101c6a40d841007015100c000c40d04a16240095070400700120b900900b03240e5504403480500f03e41d0b80e07100705518204d600c980111f03600074080ea071140320808100b80030841e40c441110b0019101c00030707030011030b1082e04410341c9032544104964a0a01c1d0394404601421a64 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 847618264 1250 847617014 847617031
    0x324090712030f14040f2c1f060819090c081015230d050304180b040f11090d030e10030c11010207080708070201120f051e040209070c140d020309041b020c010305 71
    0x100c0c0c07141411014504100c8c803502034099001200010786800d103100d80d01a82c403001c14040400b081c040307210b0f01e4504403582c0301c045010001d080011418450b050745480c0e844034180703000302510540c2d02942e1340c00c44031801030031441f00740d01c165844019841900300090a12900d200e0001c1103001d5103820340034850128000c0d421281010344502810404851000d8108142a6141c101c24140c1c1020b004011541c0d01c0c1040401610200d00381345841e512889150510070810b200c030040415004090760f1090250142ca4030003074484504c0c0240007000282040340100e9440d10a43c040004140201c6500590280400d0700b45121543c4201c12030b004000101c1c140200609070002c0001c0900c225415006600004a05800d00c0903003401c10301c800c003a401003094101410000541c039130711080b9810001710320307140c4186a4030f824411400f40c8100300241450281d00c2103d00c03159030000141200c1102242c082100600900201500c441050207680150b0044031004141d503000b980000d9111080 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 847619514 1250 847618264 847618319
    0x10e0711060a1a010e0a0e07031d1015060909181a01140f0a050904020103021306020f0601060306080613030905030a0807110324090712030f14040f 65
    0x304014035082480480780d1444455490003189074800b680082120012020309184004454401c041502d100c401c3c020390020305d010740041440d1600c6035005d000b44190204040e100040c034000000d072100d890418841d00a400c1c40b00030411550070240d039004680e030340d031170f040344d524034003c2860064200c0001110300d0f40c2d240c495010108004040d1502030316010060008035604002e0086c0d201c1c4c1420600601032400b5402c0c41311661207840c10030090303803004c0318800342a07505d902c0120301a00c039100c44220916440c20001034001c0e000201d6185101400c00ac6d00e0b03060380c0b180800c034101c03442803141c03541030740c031180c081441802042c00a4205038001c1c50007011040d01c070008a0305c0c2c1207840348111030782940003415a090040012903000040c80840c00b03800501e1501c03000421aa5403451964149008034022030702c990810483c401c01002c414a00103628141800c0140c5a0b0080070103880c00314143c911000c980b41110000c071015100d046212808140c1040e0409059200d40500700707981e100d1 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 847620764 1250 847619514 847619537
    0x1204150c050d0e07050d0b040302120315010311070c0b070b090a08071b0302060406050406081006050304021c0605040305041d01240302071e0210020f07090228030c17090303010e07 79
    0x3c84400380450640111454495408d0a21300245014011161110015070074801d102c0f04402000d0344c0098075000b460089a0301525840c1d4010510404e00000d005440c225000030b00e00821002070004107026042250301a5a079039002034403185800c90003054281e0400200001500c2010401200080c0c0d14001c0c1409803654046038241d0700c541c118201103640481c08014a0b80c1c00008a5030041c0c04082c803c20051400001400302d0002910080c8513260042500c0c00b114540460840483d41080b4140158100350401615580c0305000c0d10601d001d24108456240052990031070485100410841d00c8101c95001204120043c802020426400300900340c003040128541c84e2140807a105400c2420322140704200d4800300c14404c3c03806540000e4600441e034030740441c00c0400c07a4001034015035a88446001c05000349130035800310880813525820303103080592645c0021182c1d111520fa900301c204c4080742c100107600342201c04080c2c951080006100e030386040701400e81c0210090070b000c481c900 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 847622014 1250 847620764 847620769
    0x1b070204020313061e060f03080f0c121602100c12080c090901091401060f08070e0105090d0c06080108010207020901030f02030f0a050a12090b0720061204150c050d0e0705 75
    0x513100070020400705c1051001d8801040340e0710500d00240090140640c465245944400d200d002d140100d1402071004654140e0300082442100e0030400b000c101140e84103000c03c09821024905502039024451192501c40403074001d000d40c0c0b51898111010900c4402c400d0300445440c400203010035441030003070254071170a45601c0c15070307806000c2851011501d0a012240624240016807144040008030080b094240790070200d001c1c1c02042c01d141c1502c442c00c0000c01643c9501c00c080a003a0003d030030004c95414060a0850070044c0c5526554544582c1d1383c44170000c4c01e0340600344029610600050042000840000010030b10900c0501039410301e00c442c0c08200d040410320403050b1055004864200c1c00c101c02412404042c480394100018082d0610702e09104a006070840200707505050032400c10b801d17140c20004034200f01c004010f10341e24404483c514401c10307401d6800b1a1a640080303c0c18802c400940101061808a56950390601c030300b480d524409049540411800341c00ad4010110360b54 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 847623264 1250 847622014 847622021
    0x9050102100b03120c1b010e0604060e030a0c0e0f06040209031f0b0a03080c190f021002010e030d2301030f031d042306090c0a030905070f06030905061b07020402031306 74
    0x2460350006d000404103501c511040403c501185c6410800c94000d80ba4459a90405036010340d00a45440c02c2011915000701e450500407a40152110308240d03000a0490710714801203220300446030202086440d84e200b8032041e4000c07285c4080e80342d000b8001c00300c00303088915045c00070350100301d10114240342c514000c076445044039001551b444038001500c11550004103d091a4200308a03981c40d808609612190300840720072400903c1848044a007c401c64802d42015030307030303c1000302500d0795030300d807290030b00700408400d54080c1148500c0003615070400640101d00b4100c80e003100405511b0151940c1c00c440b000e5171003241740f5102911301014411512148138416206180c65030b0459001e030707084103010351103074000c01032072142c0f111004001421000c00250f03550420380b030a01240451441c43c0850402040c0e42100541540c0e0b0600011030f80e40c190001c908071805242502c0700e9444410485001d130f0038161011450000801407100141001e500850348003110120410f8805103669910301903 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 847624514 1250 847623264 847623277
    0x610140a0510030522051908090405010e1603060b1b160f03060506090403090b0a031d0604030f0504061d060c0a0b0a1a36010f030501060609050102100b0312 69
    0x2d980380208541c1c000641700518050070f01440c400c9401c1065078070720765200c005100b40342e5101c603d41900e02c100f082ca40d050f1085144010301c140304c50740e116000fa0b285c0c01800c4420b44100380304203206107543c5010f846800150740d0312032030711440e0010410100c50542c000c0f10f0404202d00c40d80c0c1d800c0842410f00d0582d800945540051750404510718100300040d1440a0300041c0b1500c1c080b8240300001c0d40126084080b02e54640741a41c4940511000790020052244200300b014060920810880300100c2e5240c8528480d0710b0b0300a190f1005401200c81e4041c5024030004031302e190300d1090b00c01d4264104103d1444004200d5464100c03444a00350808500e80c82c2100c56500c0c5c90103000c2c42524a000d001ea1200e000b458026100080d000058502200f1741c0c260b4240c006820720702e4090b490a8107546d08030004c900041841565550743d03800c50080c152000b5182540307005004a445445038907100c040310016401000e94010080581004181525020b0361602c520301041c0c540c1402c2c400174268 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 847625764 1250 847624514 847624517
    0x8060108010b0301111207030b040213061101050703090b1b0712050a0f031104050f03010f0207030c05010605010801030308010510021606020d11060f16142701020610140a0510 77
    0x20158810b41c285403d40d0000519a40300710700030f000c0c3c20400080e00055990004a919002c510380d02c110003c80c0081c4210824140c42680400010030800c2c0c11005c01205600d904008010559039010110308443c0910b00c001e0403400c000d408030b40c6c034502c0c1d00042800305a22242d140e1415030255954400760907000319031000710b1380125130b4207001da41018180082181505081c4500c94182a402001d40300d140141413044803490040002a1000d500c070701010300300c0c036404644d118601d0130080c1c00103030f2030f04044400390b0030000040340b654410324800341203a134591a28020359003000704101e0b180304000342a00c214450481c07082090401c0c610740e50003c1c9a15005040720100c060300051002081d401840e1259000000784103803000010300c0c081d4000b8501c018001d143c52404022641490030600e0349019840105484043d0621944c4042480482c59807040b8010302c110016070b1610000c40c0c50315170101513003030108400176400101c90001103004100c001c02e10385400000d00c6d8103015680710790 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 847627014 1250 847625764 847625771
    0x11011503020f0103110d0c030b062a16030204090204020706050c1b0102040803160302100606090e01080c09151c0f050f0a0f1203091a0702071707090908040806010801 73
    0x106508042c04035000c6460700b03103428000c05807844c68070f43c2e6902c540c0d4890b041c019560400101038a01c2940404119100142015503e0384142045110104071f80460070302d4a11500f0841e90b00b8a00040c062124009d181c8071100080c507540800000b010103100590b00107401304410000611944102c51203041000300c2c0c203072200643c81c51294034031101c800b211820781c8108014000b003040002911019550b500e1013400b084481d14040f07003042e291011070000e1a0a01e603000c107045800c81a810152480d101440010ba030780c03401c5055480385400c2400750401980c2c4041400f01030600740c500502140a02544140405000e0b4110000400c000075100032074038515903401c001007030201b20442004a00203101402c415251196407001c0c900c0014003019030200c022030400d00a0700540040b41e0404681e01c20f000c1c548041da0f030243d0086540f840140116500070542004840e0380c0700220a05100600215040400440c004c02c0b01032006d40c1c48100500001031449410031102c0c1c003800d084400031 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 847628264 1250 847627014 847627019
    0x3070c0210030e010b03010c020604080904201e0f0912070b1b010b0901030812190203040f0b010506130909111f090b04120b10050415080601140d02010807110115 71
    0x41d00b1217510f600d40381d109034140b582403040164000b030980d80040d08100301c1c560315a0310200050080084a01c001c03040d2440151000001807076401411b0381c40414a222240f01c1c0034401b6260a5125494a00320400c02c04d110001c024100383c8500c00c8003400c00f40881c0d8070603840300748404982c0c210007121b1030201c0b4138000b0300c022850280240d04a88100b944d4612043d411650703141d003d07001d03059041086d80c1103100026000300008803074803103440b18181c08555904050034171942600680009540d03210600000082c1c0d81813440490700401c111001c41c44416003400319640241414070000c0c2d841c00411500e0310001c0c3e0ba440d0030503004505541d2100c0303e42d02c500001a141801c00d034002000444248020410b85c0340e44880702c1c01e419803081e85280e1130b584d90040280c28041a40140d038010340381c081003817101907586401d64240c9040104031007080c3c0e41c601040208014004269800070225010b220065004010117074000c8520b051a04500c6d000c8441c1c5821034540d41d9050504500e1407404 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 847629514 1250 847628264 847628291
    0x1110a18180c1112030c0304050a0b070c0201081b04140a150c0b0a0e0606132421020303090111032104060c360504020f03270d0503070c021003 63
    0x81c00804a2048003078807203d0390500c4e00c210140402010710240d0a0700000140810009008408065a01c0641c038030542c140907400404034112850224081076071100400c80030381740d5503254050100d03500d11803450302d4140526102c06190351a51190410f40c0d50360f0125240317452428501e1f00c4001503031504085c0f030543c1003941c080c10010f445080598582460220b01035404600c990780008155040c540d542840316035500182001081c1c8466050345a05074038540c00e504c500101100c1c070a4845001c0c01d89040800440c10300803c10003549540100174900b101d5000305140c881155000e01031f02d08280302041f100581d1405400c1c244003100120082008000c001d1151103003000a030715000d0715440201c1041c4006031300b02030410326501c40b0f44414075441d1400c0d8601c91301903c0007900070354031000d00001d007004d2500142e4640e44400b00445105880d01040a842002c1c04181e80042074060700780c42003960b255102602200801c4004842c08026840304400080c4102e44c3da45e00180d0341995004 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 847630764 1250 847629514 847629527
    0x1e1003061d0718030c0603051009050717060a050303070b04110307060909140c03130510020d06050909061308090a12080309120c0a0602030a0b030a0f1401110a18180c 73
    0x102521a0742c41100034404102035111205c191849414000b4442d101e0403008100507000d68440a10309040600308001c55600840c0140c810852010a050f907488150800080480c240202c0b82c050380309024500100d031500e550b0f10380250088126140c2040c0181c08a4203112003030f0490070204181c96410000c00c00030f031084008240c80481651010300300760125040c203101c060000326610341c00c0c03140f88060050a020b00c2d141c002d4420b80c21540c4101d66002d1001501c55486681c6c840e00038800000c0503036201080f514072a48001e03410040010a90342d4800b000e03045a04010741003003e84001052100b100742d01d01146c6402100e0b03054913450450300a0f441d01d071601400d81404a401e018102d40c40c1c0002820300030a607030188000d616036841c450540000e008200b245a498482e0b5000781d010b014508070090610740c0905c141402405940d54401e00342c449210303011a20150070801500b2840c89800c002000403200041c400000342e4562034090782030b17090805121042d81d20754004040581000c07 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 847632014 1250 847630764 847630787
    0x5070e09070807150518031f0e0102040e192c0f2d032101150201020306030c040504050c0d0c0620060601050f0712050301060e1e1003061d07 62
    0xa004008050514803076520700f00d130800700503041c0940418111803a02101440922001d805021501802120700c3c4429429013051030605076030f80380c81403000c003402040c001c45050310582240f0040f00c4c6ca40c000203810f00c0340d401201c00c0113140d0328045032500d612441d48000c4145001c1d101548806405003606003400c10500301e0400d03550000500c0080000c1c101451049526404403081036203450745034480c00c41c03054240b60b440f41c50396080300c84920904021982e058540002c943d18800300201410703802c038801590175580c5540046140f00f6546071582009134020b00c02c2042c8c96000340c04034040b0391400000ba000300c40e1728004600502103240e010441c05081c10804080b444041706404140c1e49414025146034100310f00022a011700c051220308585103103034491250f03510500c0c3c448c0000d0450308203006117800030360084255085450080e00340804481c1d0349590720264060641000103604900346900d042c1900c4010000b4403200741000070034a0315082c81c0000e03041c80c4c81c6000508207200c04 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 847633264 1250 847632014 847632029
    0x803071205060904080d02040801090f0606050904110904140a030807081f030b0c071a0609060d15051801060f1721030720010b0a0515180d05070e0907 66
    0x10081140b9660781c1c1c0b8071650840c1d0001c03080c5581e100b0146290001e0b1040b038010303007039039800e00c60b411b0204000000145100e60003240d00f042180c0d103d00c20807815190603600070307000c40900d0906240a181586410b40c0003071103071201c0100d00c24013135071076410700c0342210090b001308030110201701180d504050305c40c0d8032021900b940407280400401100d0010654000503080022410000b0944200c0c1000c403848241c12030b4042031040070314150100c00240c1191000e020360050000310f220307401d0400710030b075840e580100b2103280503080499000c0213010041c4800150030521281c400f100d4420301c182e401400c20030b00d1081e1803138141812030940c80c500c04010340b40c81d0301105800441c003c04040804240c661600c4c101ea030f03512a0001120b074050381c82c6102c0740c0c0c90180444c03100a488154410801c0f200b068a40c5078260303645400304600008280004076041c2c01c20844e040c6410b0400c40c0700488840300803e500580d43c0291142ca20f04200e5403c00542040302030107000f049407003002164010a03d4 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 847634514 1250 847633264 847633271
    0x120601030b03030d20030c0d290103020903120f0403141216170a0e130908090415030501091a090c010e090a140a150f0312050f0f030408030712 63
    0x901c0c02096607403042940000545603240e941c0c8000c0811800e420051400f0194402e80f0303810203034400c0030260b0040e254070011619105100740c0b40c02444190f0070706038030700f100103a080c50175080054010398040b40c01c00750300d8001c0c0241070718a85207203401340040c420200c4100d912141140780810092265450016a5074070400034002c0000ca882c08075041c4078458159217246810620348420201901e0350035200140c400700d243c1314100c1d80101c086c108203a0449030407442e080100300d000111010700f80e004e0410101041011320506003a00b015213405400d103a24100590303030f03880b02030071540e1040381101e44544141040081c40608401d95401c41c4103040034120520480e00040c2c002400344100e5801000c5213800111103000c190310080440d20001d80180c1c81d89400c1500c1401004880b40d03925102045100102d03501210460440640303620980c030031410f0008907804e13a0944c01074849480340d04010000c42c000c0101d9203010314050b03031282e803003e0784a04040c00c01401c1207103114004c8060f1440c = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 847635764 1250 847634514 847634531
    0x40c0518010311100c060f020d230103260c01020a0905090919060f15150903260408030a0504090501050d020306130302033708100b0a0e1512060103 65
    0xa8140214040303c2c111001c0401010120060304c004c88000c1010748070310310700358520440000c180c0050910154410003000000c40170000711108006071042e0610882c001001440000c7d000652600742c10703555100e01121001d6030095a10a90140c1686005a50003040d041d820a0700f002401010701402c640e01d040c18500450310075a40d000a140101400d254902a01c040c00301c29806540f1100a084042c0b010200800444e104071015201318048180300021a604003407181c0d4038441500d500000611050000d0039081e0640010340070a176490707550070000054510820802044440d1003515100d40b51882c040b003980c11250160701c082c0c000c4528100f02001681c010408941c060400d4490b462071410b1030804078a18015412050b1515021407060f4a601c020b400040700f44003101e59821508130340f182002c0300e022205907910843c008030540c05002981e1841c01030300103006c80e40b0f807852803403a1110001c1d030001c6c103144c155414041c002071507814404a500c001740d4080c5080c24103220391072 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 847637014 1250 847635764 847635773
    0x5190306140115080406020702040203042f1804110d1a090a1a100302030d050c1903020a02060c0a0615091d03041419030b09250b0f0909040c05180103 66
    0xb0b031007a182c041041004c0000904114055043d650b4140c1c000d401103441c2c0c40e0a1602c0204681901c10b902440b100180040001049007045800c54001c040c10320f00d00140c40300c1440703c035040c1c00380080340c0d80c2c090440a0a03942d215121842d0807076024454a11038580b0120003050809009040c22841da000824810041280800a0f16100b0461425001c0035502d000005c03111000e00e80000b50725011710740041000c9907010014109075080c520644105a18280389685603035032103000103000d600003680b680d01528091000d4201c4802d400140e030308980c400c0c0e959800321a00b04842d4010303480c120380b0a01c194100c51090011104613a15010301c2000b040c40056a280650310030741c00704240407003101d6025240c4525400c08020ba03a0340310a0130b19281e1030300784442c0b01c040b116554284540c6002821200309400140a03540e450024001c4481c14100360105507401040341a2400100f0483d01c0e840b51208002503104038025103681078a40d00b800301f000b0302140c0044011001408810042c00440c = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 847638264 1250 847637014 847637039
    0x1080705060426070906060e010c022b051606081305071a04030819030e031905070c26010f2702011103030f09060601031a010e0a051903061401 63
    0x1d40c0b11810500c5250f40403100c12400000e000344202c0503000f908400150000b2a8102405484035500d0b260f0010710602c0045a9041d6400c801135800384031244c1a094101c2c10280743c01c030705003402ea400c1d0340508264039201d107080703071b841c220340d1103201c11020030001d2030350104c2942d0300145003207085404101c40c3c1c0c84a59650f4000e000c1c00da254000707003a1604c51084101d04a0340156801500907803070368520034185401c08040034082001c00d0421584925800010088402d07540d41c071028200c101801c82801c41c0c464201400480301c58400c0c103400f1400001e0b81e82600c107103280110741e8990408044003010709407181080150752090034013015408d46420180081c00103100e0380c10041c0c000c8003074001290711a0b2a08500b03045804004107204528084a50711441007040b04129100303501c80340011003c648003084228200908041d8210940d80301345a50990607100030709940300980c48400140110031694103100000c66600402c004020310ba010303c0c582c02888000c00c040c6d940c906100007441 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 847639514 1250 847638264 847638269
    0x3060213031713170604170d09051006091b080a0b130c030c030203060f091b0a0807030606021f050a060504020c1b09010303020d05070c080303010b0a02160303120225080a08010807050604 82
    0x1800581c028507a01f940003404d8401241903450284a920080d060036900d5501c00820300c0c0805081004c00b15145d02c081c0501500d075000d80009403040c0c0000901203d8044c0c0240280c454140c854840d0250b50b5524100155140279032038000540b406007003009030480e0f001c0800c0c042898014820001d10b0382e12241003d903e00c00517200c03c54183c0d5006082014500c079003e4241800780c01260048000f41d00c034000030b1181c1510b4608100c01a101c1e042681d54942045140c100c0c1d01c1e11f417034400181d00082e08001e4203d11181400720340652188005402d0780c000e018202001e6100484190b82c02100e0916060712030b41c1aa840d034001d505545000791074420640c415400c0c8040010141c0401407400b84280c014821101601d40ba03585031840e143c5a036011074035443c010b01c42c0081112060b4000352890045030381c0f58803040f000003100c100c000302a400100c100e0050030403c0407541440e044560528002c9c1e881030f01c0d9a582c5414040c03000e015001c040e0041640d0764001070b01031081d0745800080720b05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 847640764 1250 847639514 847639523
    0x2030c030d0606080a0e0c060a0219031106070c1e081306080718180b0613080307060c2f0c0a09020301090c0903110108060d080d050106230403060213031713170604 72
    0xb80e5409c800016485c22540540c050400102015007205140d0321102501608a6500989189840d008400c40b80c04c0a680000380080d8030f010400340741071300c1d0a891031180620036000103050001244550000042580c484004104e0080030071040c59807140c000d03410b140611030f840044604200d000803502c1744a0b2030391810590380d09580703c09581e0341410b8a0214180241e800344850b02c1d02d21080d02e07038008803003c0b03e04a06107440d4120040c001d0045c0e40d0000c0104100341c52201c0416000085000d03018042c20150251114070025074480083d0400500740a00d40940c0e070b940f5001d0f400f001c0720040c0b0300703450800603100782c140b0024844a030450040c80091030070343c0c401c0d02d40e540017070ba030070034010001042070600081010040e401904050f040312415114445018000d1280c0d0090031745248101c000914104030a000041103680540041120300e4800c0005549a50319054030350903074541001a120003282d0030702c0c00c2c0301d94842c2002820b081d01041c107501514481441e59401c020340001c0 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 847642014 1250 847640764 847640767
    0x40e1203130602160f15050105030c010e24070c06020d0504170c10030c030606030516050d020c030c0a050f0c0603010909050a120c03031b0f0f02030c030d0606080a0e0c06 75
    0x70034440a501aa081012105010000e8036281d01e0504208198500200e03141902c0c0c1800b4101a842e511544e812604081d015002c2410950011554000000360642e0721450360303443c000b041c030480d402c1644501c11051070107a0304c2c001c6040400100c031059101c80304542c005403100e1815503100302580e0803140750f19030001560095030046400d2140107100b42d07400502e0441640402503054029002224807074800b004256201c140480c1511000c0702c4140540200e1058064191b224800400c10a580d0a030014100a4642e10040c10750740001e0301440142c2c4641d200c0001c0c80410b0240903d400f00350401030118034500408640140014031400c2002641c8010f12014800d060240d1146141cbc007a05900502d4400ea5024043c11800e00068000030715180c13041c13054080303d0700540182c04050301ca5910480d02920304480c50040e0300711600441c0400e1004141c103041c10009861711078040d071070224040f42481802170402100528529142c1e04081b4510454600419008002e150a171101c9 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 847643264 1250 847642014 847642051
    0x31d0102130b1c090605190b03030415030906060308130e0105010c060209040209040f020c0714030c0d0302070308030c07031205060a2d030b0105031c0e210d0e040e1203 74
    0x20883d4920898210034002c3c10302c0c1c54407040060381e50000d8490600c21444d03098012806140f001201d0840c00559056481000306000000b00c0324643c0e070640b0410320700420f041c81c1640d030f070750155100355100320b8503008045038a080d04403010841401419160020f0005989888002001002c0b6900064080c650004100d081921036030100c0d60034003000b80017401524282d8100304020340c040078801c013081c06003840c041070348084007044159040d8001d004100707000d054402c21081c141030361003c801350711a4100000020746188007852040007840926910b030813081c140a040896041262a07078a4580380400807140d603014945002d69020507020042d44d41c0789031f00700c1c1c40e0f140d80700c060300400300b08031400200300041410010305840c820340c103030741c0400c0e444c0d030001101c102c24138070640125004003600b28160070104008841e00f034844210980615103100003500306880a0440c00014184240050341418240102c40c58040200b0041c005000c810b004040030f0b000140041c4009010046030 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 847644514 1250 847643264 847643287
    0x408070816030f140d2a0e101b230f010204030611030705180105040b0714010506011b060513120903030e0603060a06050c100507031d0102130b 63
    0xa54150a500031501640e8100104040810610320350080b4000b4500c0c600501c426840744400f440c100c00d0100300c00d0b05140014401d1009001e03600c8034410140c02e0756017111000c610540a1015141d03450300c0b654a251510700500c400c100e2035000c568184003483c000311341e4001c1c4100b03411940c0d80e001005e030b80c08040100f604009200c07101c082070340a03216070030f0003120640d01940240120b81c8a2002004140620000407849010440300007006c0b036070500502c41548580100e800460340140750007403400345c61301c04032052070300000000d650b5201841c111182d000004d2142030b40001c400d007031292051079510541c05501520707420091030b26456034042441c80322705280c0ba120342c0394404d0036020350b201d52180050800384988002d80004061061251460400c8030403030f406064003424000040d0300300300e0281d440b50300c05088101d5500c6050000c000101043c07040038060320881d54081550310800c24000e020480c0010400340b00d9104105411b40050074034600002c640102c107069850f0000c1041307 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 847645764 1250 847644514 847644517
    0x110d0303090203010e0706020f012703030b1e09060114030a0905010b060409050f0c0304030f03051515090111030313030e060f04091b050a020a06150503070e0108151605030408 77
    0x700030b4040d03090581240b6100c2002c1040070aa40d403550803101c0c10f009850b011421307900c601b200c0c1c0b00d000488001710000c0c00009101910020700031b040c0401d00ca1414800b26001c3c00d00321111011109004e110810304d49003030218590405401d1a004c00c0c40c14200c0c00d02e00b01c920010380380c1c1080c150344421f40303410040c01703420480010800038401611156251000e102810301102ca107402002894000381401c43c1d2103090303074003883c1c00d40da0302e200740c403030790030b001e80060101030000070074095010660862580e58000e4000c20260640f2079a460304600c1002500b84441e4040240581e041801003200a50741c021204501c00e425141507840140360001260480c46168a1055080c500160104500c22250001c000c06c4810030781c00d491104050f0001c4500f40204500c000c01a0490440c05021030702d680c1008444211592042e4202c981e00e2000a282c03089591200a401c8a504010481c1100c1072000da000205003071060040341c60440c00190010f031b140303404502440300120104050000500 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 847647014 1250 847645764 847645781
    0x20309060a3903181a0714070c050a06230a030b2d0109030503030a0c180f0f0b07080318120409090b010531090501020703210603110d0303 61
    0x100b10402c0c11510a1800e807002c200c03a0301c0e400110b800e251401c004120030010402e1040e410608040b006003200c10070001c0303c40c01500c440300300526071541d0b90207002040020403e80e03101e4118505402d141500b80600c405c504d41c440c0c000e01007c40c44880015064190409008805404103540c4400d4510309400800400c0d5a0381d4001c400506080300001c1d102c000200c4030709682510030701c04a8540011a815502400010903030340061011a081c0c64003600940341d081c0c02804c0625164080988400d81070b9090352001202d000b500030b040120784072000e604000303400d40d00d480d14a400d0aa03183d5072450303c0042d00c0c01e041d81c0700d696103a4014074000c0c0b200c401021480103e55640383c0ea2030865401500322240e06a901c001d00000001e0315290404004c031042440c4010a80443d801850341c01c1690091401c02041070381b1941c00900044080c07000b000494802e8031914106c001e030040d02914001c260305180c1900b441c12006002051620054400010302101e0071103411042e482c003140684041c0 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 847648264 1250 847647014 847647071
    0x6070c080c120a080103052a01080a0b090a1e021812070e0a05010302040b0d0b010611190303022502010504050f0d020a031113150608090f100203150103020309060a 72
    0x303d00010031543c807004084c100d81c002c8045407000700e2a91809115048601801081c90459041802040d40540000d41c1e021001440002d0030380c1515001c14413400c0c080b02c1f04012180da810881c10383c40c5202800003a19032a59204504041420301900200c44510a08505c11405000a00304444007004010040d00b039003195021542010f246038800fa080a0104078400c44c01e11996032028100740d0384910b940c6400c4414115180d00e40002610001d0184002c1c2ca11805090f524060703e20031801000c102e40c0c0700c4d6070b0040e07440c40b050b00071681c0e10303c11080100f480c201003141e05000d83c1e031240642e03080c2d0300304075294581018a200000c10030a02940d00075001841444000300b40040100c030030103001e1003543c4001c4c1192522100d20200c9000f18035000010780303404014044103104095642c2d000c1018411a035142910858036480e1060368454174000c139800101b0007080003080b54581c501980d0a00f029401d504040100c41e40b074890080009042d9a9030310701514411445074243c1174000c0a0 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 847649514 1250 847648264 847648267
    0x1005280905060604151203021c080402150f090d0b010f0602070b120c09190905060609060d0c020a020603010e160c0302030d09060b060a0c020405090c0307090c050909190c0206070c080c12 82
    0x5a11f0040d48400c036468171024061100c00404107080e00031100e5901c40e6900403c00e0250762110000d80c10316400000c001e1154a0040c00020f2454465a12410f000e0740199429100d40d89404084c030325440482d000002150086001007002c8903451040d07a03c111200300000e030907a81c1c6c0c040f0070085801010302d04e99201010001c074400300c42c1c20414510944604017410301c1140d84030024055a441403075a82c94000c8010045440000301c10340c410303204d200d01c0d0310503158210700c25000102e4a40007138001c8070701404d4000500c42c0e0299064a008400d04140c18210740c005c1a83c1c401070740764050740c200400c07490349a8410f0b404211846c1c1c802048110f0041400e600e0344007440004100c000365110882c0140d2400c0086056581d0014502074454030060041007078a0a0054010152040c1021441401070034000c45640d90748080b00644611760351082c1d40030040c0086100c0055a00462091082d900305800340700c103003684a00c1100c811604841d50719030710424600d04520704084040c40f0301c0f40110 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 847650764 1250 847649514 847649549
    0x201110f070516090c020f0609100504021c150608120a030b01090e07030c020c030109080403020d06060f061d0f011e14030a02030618010e060d05100528090506060415 73
    0x4140e48010500a865800c0700c8001c0000d0210550708c03a030070b880032441c80e0300000615005e22200c3d000b180e48148090840d2113510f045846443e40c00040c144200c43c0c0c440b1220b0700000c120b00920446006008102c0186140903489500118520648402d40201134459036092166402501c4010041209003a152041e20b001980100107281030380c0000014010300c40d4098031450b050094016586c0c10820684c030b42407440c0d080040202c030921049400340d072180400541c4583c1108200001c01e5651220b1044200e42d11416209a01d40c0341042d208074881412100c13666072141d841c65161810100031030500803220800e83c2c103003085400c05150190b000003000310300595034000c4c50198078241e60b1000c0460100d1040c0309144001d001e25400c40812000080007840c0c4104030b8100e5031b0044054a5440140710485400e452044480c41243c0a4034800711915020000084a20030b804542c104014420b503078809480d02c9024140c117105030f0705d8001880d00001c118258500034000458003e00410 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 847652014 1250 847650764 847650779
    0x2030a03030614031617160905060423010b03071701090903091710020d0b04290612042d03020c0a0b1804110c0304030f0506070201110f070516 63
    0x10303016003000403d410007240800c3c240004c854000300d50000e2a40c00b201d0500c0c1003561420403007070013516544109503a4504140041103280040c103051140400c881c540203080c881990294104103100f0840b85101030b04400303000a41e10b041d81e000301002541c0c0d88030070000b1188403102c59400598900c030200009020b15169000c120801c0c804c0e260004403d80da140c4141e0707141c0c0141d5001d410780d0090008020a801d182d03000b40302c0c40ca0041c070002808417812001c81d085800000e89030302e0703842d080d6440c1000d0090901d0110f80f4100115913903450161003030305400c042400544018818914091045c0e00f0044014407001e50844105541c8803414050038001e584101d4550018001c0c40e4900300458402045000c490041c487c9000c003095541206003408001c4c241c0c440c0300c10302004140103d031109601440140000c41c01071824549803003035420414103008018040100f50380c5000150000d5900030340640c1c5c2515440c00d174007038030381c40c85081050825800540780c440303130028840003103a101d = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 847653264 1250 847652014 847652021
    0x4231914120313090b150711010e0609010906260403020d030c0903031b030c050f01091b0f050112020f0a0c0302010b0405040203060a1e020d0204061814120a02030a0303 74
    0x402114544008070201030301c2a1244142c2c024101011408542449414000c0e00b000c182080c018218401001c2c901100b0421500803070800c42e20300e1800c6010030b07029a030100d400308021404440151904410340e002038911102031081d4424019103210201c0c0a01e110814021010305c14001c0b01c0d824507052a0080d1030320061550300010a203000c604002c100c2c0308030352030301c2942c0e80f40d2501c100c100084d081c1c10745040c06514044040110703480c3e0340c0c0c000560601070103801100b080008241c4d210145082800318008880001d0303070b104d0140c4108480015604048204d5100782880b146070813504401c440039104240b0000d40300d81c00003c111030000d501c00c07080f100040c0654001c00c04035541104202c243d56058070040d6266002c40041194030b803060b0300400c2d0b80204550f149919650b4242904c041e40c0010300600701480d400b0508011907500940606421000c90401050071400d0024850500e01c41d0003405019000442c401c07110303288100100800c03641c00500301c0706003541916004024 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 847654514 1250 847653264 847653299
    0xb0307030f1209060c0b04081c0912110f0d03090219080a0213020702010c020910080a0b010e090f101d161a0406120207020f090906070f05042319 64
    0x19050103000484a100d408011350142c2c0c01b5201c0411500c82c0d8450b81d4598201e6554030000130030f15030701014034090a01c91034001a1203050b5032010031a42e010f01512800340045200d90313940004120b244040e10101c0c4802c0d80640d2070500207000f0000e400450320307000b0060301562940c0b100c2c140100e500d40c0d0010f01008070620864000078248040c0c00e80030309130302414000034003003000040c018006140042c0c0a980c0b0608460480c0c070100d60301c1c01c1b10340c94106144816502e04440200510002812801c0d240d400320381c42000b0304102043c1c075011a603910b0000602c0254540d103049c2c1c1120b00090348686003c1301c4d00340080f140a41c000607020b8006030114401c010b06242e400c0184412540000b00303403405c948554070b503400c1041c000da00d10703006035008040c1241d002c8403070001c1c07074281c0d03076924120341c050243d0100800303652400d07e801500602000760b0300014000184010003040a07171440c100c8102d9600310100b96a819540c3c04030f450516a00c000c1126442110404101000e1500c201c409 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 847655764 1250 847654514 847654517
    0x31c0e0d0c150905030d0804110406062708070e040204061d070207090b0609010804050106091d0607030612020613081b0312090a030803090309040906020a11150a0b0307030f12 77
    0x508800c1e602611903e9a500c955a019004403203c4034000c0c1c01000d11a51240c0124942d00c00403c051000a00300c0da855003000c80420006107101e0580703144441c012081408110800b42150704005403290b0300c201b544154501c06241e0f100090441d16641c2011000f00014241040400c0c3c840c0320406a09800305d0f400401403165020000c1c414900e4010000941c80c003810640c50076417018011034030102c0080c42550950340382ca000141c02074580c8900103060901c040c00003020310300501ca09042a001030802c000705402d115080c8a1b61a5907014607040320381c100c41032030f0750b43c081d14516010203c0070761000c18240110445408880500d1510407505a0120f06850f0045031116825803503001d10000ca035040302101c00c1c10f00c0000c0a60005540100381c1c602200d0405031158002000c2c0c4040b0038003241d0702074012558140f100d401880074100c5050a80103080b551180711030100e0348210051045856644400020240361001c2c0301d80d9000d0f640107000a06500000d0030a68200c403441e0329503a0 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 847657014 1250 847655764 847655789
    0x40308181011190b16140307030902090c0a213b01050f0a0c020304030c121a0402090705131706010609080604050d0e21060a0b0f031c0e0d0c 62
    0x30900220f80f441e800402d070311201031149602c0710850761448a4a425510301440340c0b00c450701c02c80c0368100028522511032a83c0115941203540306001c02c8240140064400050900402a0042e0002c20021800040d50500b03c100381d0540000d00c0540308056848590050309041c03550a040010350404041da0401926003841501c1c20041e03007214000c481104d520b80c619404160480d200790080c012b285103d01c100d070706168a130385900d034820b04030b5072002c45903246c0c09240d07100b040162800006180b0004008011b185090f0700841d0700d2100080c180742c01c10800140c10200304043d60035640182c0000000c0c1a288903076071b08150b959070028054a80883e81041c000a201b0100003035031441698017401a03d80781c008604141c8075100c9864003154800006501040040741c1c80c1700500c0c00b001c40c50001c00a030301744425510202c404074444140140701082803610b80b5180015415829103641c0c035420200380710f2240445a0600e03600115502c40800a852810b1005000d2190261601c000745207 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 847658264 1250 847657014 847657033
    0x204050a05180a0c051003060f120c0902031614250231110f0c160f060e090a021905030f090c090103030e0a0b160c0e010308040308181011 61
    0x443d0b9640b1403040041000407044800e10050415009481c4444524100410b080e62a4004602c2e02e003070b144c002e11440d0101002c84801d00c1b0125002e0001494100c201314554144040e44035584074030082150140603030514500c0003075082c0b800329155011543c009007030b0700c60342600c440200152101d0592240a802001c0c26503515021000007a802e0340d802c004104c0c00c040e100e214013904a0840188544209010032207084009800420480b51004040e054011940701c195114038002e03000050444c4048070140704154010702c1443c2c50550494080d0a203030b98600019010384a000501545440344440c503880407a0040c01840c01b80d03100c108880c8565903850903441da00d04182c0ca030264403549107801040400d000d1303070300340c142c644001d420f510035140c40d0b400c0b62103164000c8018403071501421584100b4041c80e261a540600020341c51700c400d9500d1521100118010303808040c002c1000041c20f4124240708003030407500e10202520518a0b0202d01c20080c02009c90980c084005010f0701c0b041 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 847659514 1250 847658264 847658311
    0x120c0a06060e0601080609070507120c05100b090c1b0109060b0a06080603060c032e0602070504150b03130c0b04060e2e120501091a0d0f030305130204050a05 69
    0x1103d01c40d180684d502103d5654140030012480f4000e4482e5080c80020001034011600c0d07002c900c041080b40341c542030300c1800540341c00703854908401901c0700a039142202c480a20ba4410b030909801c210103051007030315218111010700030140f40750322100443d0320780f01841d42080b5081e0004132004108071000b410b66903440000b910b1100c1d003214201d174107410420003d141429500080c0d500484800042c4d03205403940003c0040075a040d48103007003040c040220800105504001e01e00c0902401e8034140816416003041182c0480035020309000e403c0301200180b9480300e403d4001180c1a0016034200f1782c0b40c2d4680307410b2015403050242400140c061043c4503042e003005860b1130401b10521000d01c180912030300300b04852060f81c1d100c03d8100032034100e0004c020303641070042e903020f014601000949038000c0c090703025491350030442a40c058905024007601250565000400d03058050501180c150754060f0500000c40a200340254000d00d0041171024241d82e0754469803080f201d084460740e040c50785001 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 847660764 1250 847659514 847659539
    0xe010f0b1207060804110d031e030b06030105060a140d0905010501090b01083106021b16060f05070c06020606040b0a050607030e040225030e060f1803120c0a0606 71
    0x4108030782d10107001001054425840346a10901a1052821080b000700024404982d0503c003a0002114480204c441c1c85c8503134024007a0038240d04080109035040300201790180014403031244604c0d400f142004d01d241c0140131380d002d608c00081d840f990310200c07e54080c00070182884107841941c030b02800070404548070710818080f0381c0c058484154541d01c01341d04500700c0003c120f1907131045480e000000e03481c82d5000c00221855115100141e102d001c141041310960780703030203402019903100e01000781d01c00f901c1c4d0302c06100340c403a1450160090840400199602c0c429000000d0000c0351601d000241554041065070103041d04850034000651200108024010b1a000d0140c0c807441c10807484001a0003082d54a80300c1101420143c10700d80d038803016100104492501d243d402001c042003408142e8000418007245030102c13003c078100800c0034202201800b40501610300c650f0000001c4405503420000798a0490f0700c3e111039035035904450131b404e0f1288040482100c0a504005006c18103421414 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 847661870 1106 847660764 847660789
    0x40b2206051c0f0b0907030c090f0f060b0a050c0703060f020c06090102030c07020405091c0e0109081507051c050a02121305060103020906060c010e010f0b 68
    0x140070080308030900320310809803003555050001d200f6400802409070041d4409805a450844080c0752682582001e003080c00d0901c0002800b210541003048203000e51901409041c00e04031180003030b9034144c01480520300003030001000651203100944900d400a008803006a642c1b80c403454100c800480303854120640001d07040003080c0e0200a01c5810511510085145240450b58001c0740d01620718020721441d155400324114043c03c2113411a0030b0600c100d81030350244140c1000c0d090603000f00800d400b05582c070800190020002c107100c0031040e500d080b4207800c0d82d11003404562981c0010240155011203040d040c000c540b1501c1030b04c4c882c2e00c10000050341d03a20041c0d01500076030001810311640000d001003d5001070300c003141041c1125819240a03105803640b0000804601a03401184450f44c40c100404840380c0e01508030704005424282e0030010081810709000700d103100b10 = true := by decide +kernel

theorem cover : BRFrame.Cov 847482014 847661870 := by
  have h0 := BRFrame.cov_init 847482014
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 847482014 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 847482014 ≤ n) (h2 : n < 847661870) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
