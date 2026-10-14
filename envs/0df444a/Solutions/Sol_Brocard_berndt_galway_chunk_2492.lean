-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2492
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T06:52:38.319156+00:00
-- url     : https://prove2.me/submissions/37618d0b-e739-45ae-b5d3-0a8e0694e624

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 448021582 ≤ n < 448201438 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 448022832 1250 448021582 448021591
    0x9050322030b070305010e010504020c0f0d111b031c020a050a060c200c2701090603020108070507021c14010606020f07050d052116060f0516090512030d060e 69
    0x12a40710b00040d800394030911449041c0c990308144644c9503403d150a010003900f080c034440f0f169100d204101d0500c85810401d103000c42c0700550710032030180040c00c0d80d281401c2d010031003140341e0000c0c000036005503540890240300282d0007281c0390742d00c4044144100d2070000b100d203018005005003c46001407261301c0d0055540c1380b910b520344181e007132120400c607551a4040c04000743c09410024074041030303140043e007004203449144c600768251440c0300211841d0b800c080c4c3c080c2c1401e59032060200110350700580c843c2d03884540d07410310a06050781c64000c1508041c1032809040c50400c100440e0003041150300c07c400e02c82907500300070000541c84d40d001a40d542016603000300c8510035406d00003040c6c0380494082d040250702401415400c41c511003030071884080780c08a004a54018807490848050b002400c0004038091040480c60018001c00d038030445a018214100c2c01c11107542400040fa04101128210790081e1003192080590302101c40c194040c1c0b400b002600350a011000621204c070b020f005006 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 448024082 1250 448022832 448022843
    0xf0f080415181202010207030b090705030f010b01020f2e0e030d0b0f0d0302031c060b0f04150309020d02130e03180a0504060e1302030115080604110a0f03060905032203 74
    0xc0d00c58401c9040010f101c031000340180d10101050000a1003942d03941c0d00318004904645086807a080007d0802594003120650ba82d521070f0894125a07040240048108158001c0c018040b5403060078030302d204201007590000d584401c8660f8000d200e99106080400703002c0c0c10b072625940c1d40054040a00703801321034148502c003004c030040b040c0d2802c107d01c3d1181c01d0b4035800131850081d0035045e44100d0001d006c803d00c4010344c2d07824002040d4120070000d040c40c134081700c0d1495445050840c1000084030084c1d03000d04142c41c098040700184c0301c0340c002c01000c40d01290304820b0031002000090240c806080300d840307031b4040850800014090421000c000000071640c0c140e61540312002c0c07104440e40c1e07100d925015240c0d80301107603844201c42c1e40000282d0001e000840c41e07980a04aa42122119034080303500c9900210030070007880140e100465002c0d104580c45034410345410251886100c0301e00020301159501e0200100b00402041181c2940000c1c0b1000a40d0500c0c488c5d62802030802071209803403 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 448025332 1250 448024082 448024127
    0x7112e0614040b2704060e0a080d050c0a050a0c0203160801020c0c090c070b090a06090c0e0612120912121b0606150a0309050709020c16030f0f080415 66
    0x8140c03400941035010707035000d000c10684004c0c0030b10765481c8840000d401503400a6945c56004001402400703420b418038042d00c607032a0f441251041e8801125802000201194028800f5a141c03a074004100da40801c200d02e02500f6440e210300029041c00c0e8075005440c0c8081d000c0d40b00041d44501034001d8a500c2e001c65066401e40b001c000709110f6540c104541840010720200302d0715000441075000c0507002001e00c0101c2d407941c003441c2e48810465000210075a40328250340d00c01c020140402c2003c6a211009032181c00140c40b076801040d65400750156a540c05a001003181a80b80d140d110540d60b210310424204d480b02d04020003603606640c8200110040440e056480e000a140d001880d24020b1802a041d8000c5c1071124503000c1d4960000d00403681007688a0042c100810740811515010b400c2c07034400140c0c0c412251500e01e1419010900f103503241f4080000400214071021541f010f803a804c1403202521500d549418400b91141d0f8008030708030001c40e00c221f02102d510644490266038851042c80 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 448026582 1250 448025332 448025351
    0x11030912100c02060402061902030c0307050303150f0321070c03110306280504080f0d140106030e030f0703020705100503010609052e0306050315060907112e061404 72
    0xd86031340707007220083d40112042040f01041c00701c02840c0181810144103507818040640c4050382160300c2882c05891650010003070104003035201000328000b03101240d038030100d1400c810200f916012104484030342c0e14030000c09040041000005c44113216441580301d07045d00e480740790801c400102c1862141c01381c8198000504100c2c010344007105148501020692042e0301c0c001003070003a001c01801281c0f0700b0000d200341ca0303041018030050a2a84404140860000710300d034084102908142e01200030181026801c1480b03c40201c11201c1411004640d50b40e40c16003424107914210035079205039007028815641001d07040e8841c000c0c5050700c01e1640d80490096503030017080388400b000382c18808580307840d1070000c0e00510380b01259480e629090a002c10030a9944002905180d0030071014640d01030318008120703851404000c059131164840c104945603101c5203150b0750b515440820f100c0c2c003002041501d014030321151001c03041c8540e18040203203e043d844118095528039a00c2c505c038040da08184061 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 448027832 1250 448026582 448026587
    0x3011410050f0c01021e090102010f15050f0a030206030c0a12020a0e06070c080f101803021203040501390305010e0a11070b040b0f09010c050301030311030912100c 72
    0x603080100d65655040c20a01d03864940507090703002003915a0199820010f00e801004c44240050885104400c41074540705054000f9007500c040d00f40403c030a03403401c4854084200d4010301181501c42c1592035106402000c80420045915600080e41c840004000c00200f126070000a00e00b680c115540c55441107a1440340c9010707030240d07030000004289540d000c004182011006001a1405002d000703508a03504c4407281c0c00e0900c134148114454220041007460010030b4090400c010b040818041ca80e039403075407802911112102040d0600010000204091000075005041c03c6a03216a0389a100700482c80c01d000909286103881c0714242d42c01070010013050082c480c0a040301c050660014007581c0702c07042c900c002c0080340505d1155420911250f00400c420f00d400c00d00c51441600401400c0c18144401c00842500a14010090707040c910068100340d1301000741c0c1d0449501d81001520030604021160a60040b84003554101079580c0c42e40800c80c0c00002d580c051901d0b0400c04010b00b10644408 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 448029082 1250 448027832 448027849
    0x60f090a17030a020d1e120216050706020106051f08090a05031305130221061206040c090b060f0403021c21030524150c1603112b0314040308030114 65
    0x65a45904000015000c40c0c0550907002041f82d20140040c50014441c00c0c85611894102050360b159004800503c8413070303024800c1c3c0c03016200c00c80740e035500e42c68101c6071f0650141c07480541e074041240e900c020540c076032010443d07940c940350300209903a03e0710a60160341948000500c81e00d8820030003219690300384129442120a0362510010a1080e006071692031054840d01070009900320702010520304c0408400c5c42018055031051541c40c4021f45050301d1081501d40124510344140820080a054440c1322012182240e9040d501400011400352640344000b07160700c03005c0c0c400b03490f0103d814207a410401264000c040d081e1410061900c40507469424441a034880511042001214035494500070040000c07030b0624054081c80c2c041d480c042e071428200c00404400110850103030510400081070842c62190ba02034644415403d20000d1403040c0c0000f414001d00c40384030042d10b01090605c5021034044020741c44112a03544c1e9a01e00d848a00c9074400d00c6210003598a1140c100c08030f1804410 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 448030332 1250 448029082 448029107
    0x1080609070c0609030e0a0603020d050106020f1c2c130e1e01091b17030313151b1106151011070f060906020f010b060f090a17030a020d 60
    0x1182d4001c0501980c03940000c144400703040d010b004084a2010140c0e07a00c00c1044060a410780c4d0143c2c44452412940090f00c0d01a0418015508130352000781100c00c0003c5c0c06540c503d00841d060240300500241500c4032580c04000304051420f04204601c2e00d900620b0001540c1c000380d1b0828440101007050008881a0b440781401580006c0380d442488191001e0402e0b004d8041320000801c60140e07640c0d030f40020400105911503001c001c80070010b60f03120344d5008400411703901c0550300d10f181800f108100e1050b800001031039186c120380422141d484031f5100c0c9140003002d01f00c030501c2c01c0c00248040c1c20140001420122442514001841d2400100000300040710241c0740006010081d0f2065642101203000751805105844001448610144000004000a81350450706c01c1c14043c0c0281410315985800c0308a0703041403840d0405407030355000c0318600c1c190311000315121b40004000030300001c1940e1010702c00756070b08074240b103030040c0100003000d00d4000c0307408990044400b10710030b0340c9031401440c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 448031582 1250 448030332 448030337
    0x304030b241c02011101020c060405061311040203181204050a0801141314010516140a0e13020d020d0b1801210f1209060e0a0302130b0d17090108060907 67
    0x40102c000c4414184101428814109807a00c80c034022842400ca030891305101000394440f40c1400f042c8182404450340020b660b201070308500d031168030b480c0e00003d10004024003465000000503290508101d407440882d03619400d8a0100350f01607000d441a8220b40a510f1013401c85903c002920b580c14032803503581e10480003041030107a843e22108407000310001d4050703039240184115a03001100c03c0c030505201e030f01a00c00d074031044110040700070a400c0c2042025001e001042218081e413540044070b0082c800c2c001c81d250b01070108054080d10290003605204001c960011030f08204041403500411b003a52004d564800f40301060483c81070612034280305450b49080310b900503c514020780103c40860900403040c525225540d42c0e207205c07048541403103010008000540c01e0100b103501c2044084507100407900340352100c1c20350300000e21880c0042c034059403056945848a43ca600c6500c0d0141500f5001056400115201c2214504540c01001c100780002c949a00203441403504606482c000d031603a6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 448032832 1250 448031582 448031599
    0x9021b0106061d06180303030405010905150108060f070216060503040515060d0f4707090902180405100602010c02061306020306030c09070e030c100225080304030b24 73
    0x11010f00880350f1007000417039518960076440c10301580701000114001ca114400000340901756060160808100100e14460ba5910000400144000140c10ba8005408242540d501d4403030030010307440c0c10050000103403900e02c0d007040011526004005144500c0c015820344441110172040328044038021210940c3c0000b9041541c40498400320703003034100e030b84140d1000d4081883c1d030413001c80503560803040701459540d904d4070320701804141b44200310204104001c1745c0315060440b07000d0001541d07401070303100c1641e001c50030380c4000c0d040010150080101500030801401c02400c0581101100d000d1507000d50308020450428620001c0e486215941068001d120b91010741d590700041d500c00b40809032f1601c2542d6054156903902150310b80181e40548801842c1920744043c10308090400e41d14a20405860400d2141541c01090303a104c402403519001d00103c0ca14402040a04040e03041410107102c049004400c00810409440c0215031411200a000c040090103440700c0c0304c0402015040083d0 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 448034082 1250 448032832 448032887
    0x1b011803080f0c011e050619050102030a0c02040906140f01080f0601060e030319050903010b150d020a0903050d0c0308060405070f261003060c170f070909021b010606 73
    0x502d4080c040c40c010503000172801c55034038101804081d1045002c0b03c0c0c120b950f03105008452405c0d000c2d10070480780c3c04284d0751a0300e07e0040040c1d22409024140000d0100300d4a00104560b100e074044d0a90b03641c051405c02010080100ca07900d0098115109640c104400c13001140c8250000b0340040c1c10f070341c000001d11841e800c06100b01e485401031215150141f2062044406c031851111000921078495541e41c0c2d2100310040c209400d6442402165000c2c8001c00c410402038030914049881d610015a00940d440e480510708542440c400d0b0b1020f007113400788540305c06115922807041264207000365540380c05502c84c64100000c407070090302c00c500811111188820514080c0412401020402d11021108002c2c2c420b0340000c0340c0d085a4255043c1500d41d010f004001c154070a4040820301403901c0f1041212850241c440b00d54050300715507241159070300040c040b52094280c1030141c041c10001390b4444001d03200c00f000c00030700034140809075400c0c0000842c2c00d84c450700d19442c0090040000040a001 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 448035332 1250 448034082 448034107
    0x90f0a1101140c06100603091502071e060b040606030b0906010c1401020d0b1003020304080f1c0e1c050c071a0904020a050d0c0915030e0f1b01180308 66
    0x8049000c0c9051140c5550795848a805500140c400d00d54500050b11030f5140c4950801c600040d41d030052400c1c103151400c0c01e07000c1014081400d09014000380010303541d04150034a0703003200b080c210814501600c0118040108003103038202d0321403400f090360306022280e16601c00754103850002c1c41c407540100c2d81100041c0c040d882607509a1490f0b0041c0043c000c8412104909800d903440708489220680d29681040c03002c1c2800c2220b1031101c80c003494110b0940c01d2607070740c40442e0700c2050403d000b40d032004500c00a15106c1032140d09000f00c1d03030220070090340c1d401140d03140d00c0d6420702e11444084000d00c4071401c82e09004908541d1003109000c060010a810510041e0b512082c2101d20007032944240440130041d03e8910080216100c50707251141c0324801216600241c510041c540e00410142030310030084400606407042105c04113040200700c10580e8080b807840c18003042d240d004a8070036000c1c03551082c01610002501c00c0d6085c3c4e1025860018040507411142c40b62100610f02d41c0704100c0c54200c003a = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 448036582 1250 448035332 448035353
    0x60306010509010921020a1502070308071707150b010903030816020c0d061e06030c030b04031b26070c140613060806040f0905070306020f0f070503030a05090f0a 71
    0xc050500001c0c203134695201500c0791407000741958950017000741d0710b400e40c50a580c04070000c1940c0184620160400403009407240310300d200c01440b484000c00c140d02006108010a1190565059010b454503c0340c2083c528411440301c90b00701c614038001c00d0030030a500c40c0e0446803d50740c25440e20314180d100e00d4003003103603101007103d403c0440c0108400040b807aa1181da5100d030440c0a0b110104460480342d042c43c87d1003010510107042503103801020400640303041440c40c12643c00c00340326440307940c80d42003d80c0c00103000144400ca401e240c41c40340d000c0041d001400c042031030fa509000d10000008001d5200d076031140403800f0b41203143d074002c1080081100f0908040da22000f0706000d09041001410f900090056042040402c1005040052504103881140500441510103012045071b9888a54070f0b00c210f2700015003030b240c00052402250b003140c42219681594060251380d242154240303c0d4886c1c0003a6500020340b418500407415550000407100030031440000544500141c90741e0700035002 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 448037832 1250 448036582 448036597
    0xb010f020d110106051c0201081e0c030a0b0301150905070c020a14030708030d0f051003030c06050703200c210409050403020c0901081b01030203100e040f0f0f0b01050402090603060105 81
    0xb0340d04d9403408074450704d40c030310f1103d01204144181e0103805964800541234070001400311006000c13807003100c4048010b000400c1e0304914007840980d904d443c2c2900c5840501150070080390550b0070249090080c03041880d01c50100c0386038080400a50300c0d0207038101c0d1707072045142019500c01c45c055001c1c00440101d1803480a5840010304440c806039540c0c42e102c0c01c5070401480c980e200b50fa981c00c50300c100c45460080c99400201010600d82044c1103030740280c030018103400050b001b1030b625070020b0b000174000c0e4448512103144950210100b480a1052012a40681d50284a034050402082a40d032100e000700c62014103124203043c10281000040d400502008005a0451042d148600d5540c0c0758514064040e150306c50250075058031080300101300c040c444007503904152040040014590b46c202c00101901c1e00d001e1a680300e52101d041c010107026480801034031044804403070f0300422501050102001c0d04c514580070141c2c0e612070402c0201d001310340c0c80700c1d0892010400207410b58400e8008000c0d6 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 448039082 1250 448037832 448037867
    0x611100908070c09061203030f09081603020f06060d0201050c010212042d0309060e12060c0307110d053a0c02010f02090a140a1502030304060b010f020d 67
    0x4404808021426100809000d54884030300141c0d04041c0030b149012a03020b4103410703600f070040e5072030450700240740c1d1207400014003090b40e0741c0504260405581c021070340c01504191159241c90340d14403083d107207103503801003100940300d03a0940515800b4007244451040000800c1e60034142d03803175001500c09078840402c0c0d41e40d40d5401c1106404c200082e044141c0150302918800c000244040d07141c2003103506050300b03081185104113403140060b510a041c50141c0d003161404180000c1408080f810383c2c9860f002021180c01200108080c1090450103103104850640d55039041020105500340c031100350244180000e14200011420540d8844602e003005005403034a000700f0016810004c8210040500c48021340d032214401c942c0903609000d10740d0702410840e4110310300b80d07600380002c1100d5620f105915890b02641405a8143d60701c88016008142d9908910700501100078025181ea0003100e04403031052902c140d01c5029442940f01074002c2c1010b40080c4040031428005452280f00c00c480c00d0311 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 448040332 1250 448039082 448039093
    0x60a031202162303011404060b01090503060a15050105070312021b0102070302070303020601270902030321100e04030f0309080d06080610080613030305040c051c0203250611 76
    0x2e03059040c0300844020018801c035440b25406a02074111500c00700001c561080e0305240003070205509080550750090b61001000541c800070b1401a181039106621030399040c0100c80402021860540044128000035030302461000d84507001554140200c42015000880c0c004d9011401c00c0c07560300410002000c031542d06121281301d141c0c242603030300040044005800602c020000c041e0104a014050701c01c2800449d45140c4810781c0c0850000030f00b80a010360781d01c6403048003d6450600c100c1c1e4496047c02c0030212402160000122040c0d015658184641070366940000c018030001c0e0b9060169a0540d0303120740c007004983d4110040d0040100c15241d4040400015980b1203840c0b0818000f0141e050191250b454800d50048680080e94440440d80d0000380810a03040c0c4207244d070300800d59260038000b42907101d900f803c1c1601405604001e8000e00c8207036000c40c21828403600c00b00c00c20f20231011a10154409420721115004040840c404e000c0c1d00c030001d00c81140039100ba50401d403481d604590 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 448041582 1250 448040332 448040353
    0xa0f0303060b0409150504020c0d18050406120b0a09080901080603100608010c09050303090907050f0408030a0503090c0f0922061a0102100b060301030308092d15060a031202 76
    0x41060f4403070f60020107030a40c0c4000c9421507400306804140100b004071000c505001407a0802601e4802402850040101401c0c02061181e1416050700103000c001d0010016544c07103101c01d40740444448000e8030080744000008410854902071540c0c51035110b003149003003201d040015144500c0c00b8002c10b525000d42683c11000d00304030311802009004440000c41c80300c0e103504014007600e4568000340d0094104200c100481d440f2545056084103e620f0581e03500e450024442440d80155003000005010004c1c86018081d4400b02550046075514207945103041e00c0f804211100120ad00b000d07070417283c2140002c2e004100014842071a0280b00c0c1c02c0015118a940c5040803101c4201c8030b0100004d042030382c480d071075904124109c403402410900708520f4102400160380d500051000801b0040b090300003495044e000d02c8044440b100e05448011100c0140274950300442c0c00c1a150881489230701048010401c001c10135030701450003c0e002d03121003410f42c1c81320700341400e40911202c154482d089410 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 448042832 1250 448041582 448041599
    0x403050729040605010515040b070318090903020d09122d0501060f140a0803040902160807050c1311030112050307051c12060e072703150b0306090a0f030306 69
    0x102e2280744640000202503041c50104290044c4030710f40d0101150b0705200503c0440c05050032101050303050308040c52040e00c1c04030441c4201e1015045148481d040c517041108140d00001da1004203e56034a034191010b4071107034940c00c0065400d40141c90318041110b264120307407482ca03d80015400c1c04040c00c0880c0840e860315800d542c1a0783c4000e0a548040750200601080101c0c0b582c41717884103e42e503400709840e08403031503502c0c0194040c24403041e0f80080c0d10300c1102e000c4c040c0080d40030303881494a511400e0509001d500d60900c1c2c2038050007614504003070004500320344500d00030940200042810f5074209090101c0101091004440602c0200809008144200b111801c1c0307110002c00c002d00420103034002025554020154400103090001c2031000c5200f414800740d20103041d1901c5501105881d000c0c480054102c03c980010f01d01c43c040100c14040300345d2080a100103041801e1281c002402d0600d65604012522006560046041040003400d003a584d008410f00074034001c6070307094550081 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 448044082 1250 448042832 448042913
    0xd03110f070c05100513091517100e0c0307032006070b0103031b021c0c0b03010b040f0806070e010518091905060a180c030f0f020c1504030507 63
    0x50b1030503103030008104030701c0c0b80c104591000d081c01442c01c075080549420780c03802c2d40030041c010103c03081d883c0d456400a40c0b90f2002c51000800203880941e40081010051613103030558525542a110300b41050540c0298002804500d0b03a440078008000c11459038903105000034440041440f8121020000c0900f0f075507500140c0b00d080e0081004000551445c0b0340a0003100104281141f800100c142d81c40140e40c8107108030100e02e80440380540ba00b5514903201c03541072815001060a198080000f14013410100013410546071850001c030a960345841070749646980840301240018000421114076511030300c0074201641040995200407041000080c0c0705c01022100703118100809102c804d407250f5a03004068002c1801d032980181d46080c4a1175031070303601088850150441e100c07160341544d28826400340c0d0002031120380030410901e4503592080a5404007881a18600c11041d041401c00200d4400f6400f4541c580c89a43c5401c1440c1e5032600c91410a4880140000b0121041030b06e581c001c400 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 448045332 1250 448044082 448044097
    0x703050d021015030f061b031b0203030103151d010e0a020a0509090d030b0d0501090b010f17070302150c011508070902070809091b0c030c011d0d03110f 67
    0x1a001503246910001c0c80d1500e030040c5180000e00740794500304800308000010050f80e4102d41c52200030001410544040c0c600328a42500100504051101907985907010030f081f0b001d442c007a17069500c030b01c8800300c2e62030100f0b00020b0803210529103d49d01e00c0d10541e04c2801807004004851800a60380a1128210b038250361400c04641c000e04240000c6107400614000600011250b8661904021f11842c5d6145511a011428141d9601c1d000301c640e42c4400308200001c0c1e0020080c04000743c1843d00100e480300031312580d03424042e40040456000d01590b44400a01d400c2002045014516000c000d0900003660f0031100882082103043e06d20602800b8503105000080d90b0180c0c000e2414070041d180c0a0194041c4601714814070109001440c0b50040b07440d224011120417000f900c91141d0054030b00031418081c0000348000826102ea060701001a1049413060030080001c490007001c11404220b001c1340a04e095005071b0100810140a90300c520700150a10195608060020401001942c0900d0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 448046582 1250 448045332 448045343
    0x40f080d0209030c150a08070e04090302031801020f0d05030a1d0105070e03030408031803070819030906090506031906090c020721080405150f070c05030f0604200109080703 76
    0x90610060904000f410713080001a0f9040c001d203812500103042c0780c0142d0549801300100400800d1303072a0702c10030301003246410042c02048610054500039580380e21104045075078610001c3c000620350300104e10306ca42c2c103c244002e001702c160f449a044405602c000e017007680e101e0740c61940070403194000041191741c09158000160078207007408003512690704280c10922a520030007003072000d07000c00300c1a5000c81020898070400103102c040004e040c1500c40e00a40c01a01c03400c5401801401e5a02d440c201cbd19010340c0340d041e107841d00c801e0100c2d4500e0260180326001042040804c807040304540710070f0030207002320b50002005526014490183c8611005400040e44051702c00d00c00320a010380200380190445d034071504952015070300c01d605409240720b110702c01c0c8400840c0f012008c4c0500211500f080220071465905e114a2900c06600c03026801000c0c0a40714a80744201114400a10f15014a03045a4030340c042c0080225214400544a000141005403226000814000c00c001a03800b82d44200c = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 448047832 1250 448046582 448046587
    0xf0605040309140405010f06050f0f0c0d2003120414150601090b120103080906070605042003010c1d030f071203030c050a090302090402012006070905030d1205040f080d02 75
    0x1102403da68004810940b1442c60080104000d00702d40000404840c12400d01d5520b136601d0070158021401381c5070303942e40204000260b84010300c4000c1810101082542c4580b512010368084c01c4881c1403214885200a174020466001002d403003030b0b042a030207445242040da03401210f412031070400000307150a003103000c242000d0007655070304000110050b102a0f040641400341c19480392074101010310001e048000000b60800750390f202c5004458125405c1441801309040c01e03e00b035110000380c462181c84180c0d10400000c001d190600800b00d0003866071307450f0704207005825051a078000b13580300c41a606101d2003c941e502540c00b880910020042c41050300c070201c0e020f00340a0191940100118201b04007006a45d990940103030001007900d07015900000a82d40703507c010384841c69030441e9408000e28030086201d0800c40041c00d10f200d16010340c1c40f8a5a0350381c3c1c90900d5550f480c02d070304820104d00b02400c0000d5410803540a81c3e4440d001e500145003417181629106690b6100381c00c40d18006400 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 448049082 1250 448047832 448047839
    0x1606090c0806220206071407080a031205060117221b050904020a09050a0f1d1b0112020c0703021504090b0102150a0b0415061d0f0d0b040f0605040309 66
    0x41c0401035103c801c1c1012012000d007920254500f0458101c4020310621001c154030051101111103015881e042d40201c9200540340d944960f9140c0c0340307200c02c4000401c000040200c041e414000c017030245c20103844540100000910b81480803800800601884030111800b8042c003610320707000e0350001c3c014007006040b6028005049059210354020a02a518a806001c0140c84452072501240c4400c080020309031520b42d15540a0710b4840c0e101c10b9003d00340202050920303a40d008941c40010981c084500c02c00d0703a45099a101c40c0c504580501203070b150380050610300d05980042502a1100707055640c0c0503180d1340040c081400c5201c80d980c007a0f0000c54140f20031011071103070000800d003d00003441e0b50000d50700d0352110001d00500407401c0d2a141c9401da0040c0e1600c1c2c02004540c0c58803405c411055460313041c010881d6400c2c10071044030b08001012107070305d814510082c1c044850050100212018252145001c005002d40112403ca1581041001080491103064000c40c460307a42d00c800c0c20314 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 448050332 1250 448049082 448049099
    0x90501020f0405040e0a020a030f06060510050405093909100306030b0a050103080f0705010b1201150b0708040501050313080408010902130515040506031e06010504050c0c070b1606090c 81
    0x249031085c0b0340d480b81d11581c000d07a54505044080f00d80c0900e00e03548911051420340054032243d0310142d04140042d1b954040ca640100141050320340c03c2d15811356a40d10b846500c1940c155010090041c968420a245105488403400750b241c0310711503000340d00e8000e411001c140710f51800941c0d0302c0000d0356207209008002d29240078075004003d0060502035541541c0750901ca921500c3d44000041d000019000c0800c6001c0d040f54883c0303000280b50400350340303210a00601900700c0b02c104c00c034900b07410702c808101030305400156001560424000c504103818071006407065800038000b45000d81081f010700c000584c150b00140041c05400c03002042d11100c920600a164414940884826040c1401c0168034030010340b1010f010a004c41d13000c42c0d1601c40c0000319013042414888881c00708101c1c50510f0745007800052890480c2c00540702003019035075042d0f001000340243c41032110b140d04105002c03c40405030001a0880b504a401da042d15402c6030303924401207494400b400ca814205a0404101c01c0c0c8 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 448051582 1250 448050332 448050341
    0x3120103030f08070806190504020703120f0e07030b0c09120f21030f07030e0d080f09030906030406021c18030905040e030921031b0c0a030b07030c03090501020f040504 74
    0x4010f4200061541030810b000b038a04a401041e0902072130a90500302c0c003103c2c2942144005110251045644c5c10302420010807801c0f5001120500600b0091800c0d260100780c45007078005528140a00115815580c1ea02d42404000e414080a0601030110b4404ca075100900110842c80306c0c80180500861050102c1c10b1a4514000c0c2281c184104459030b079aa40e6801200d0b80b18504104049031940c91071001d5004001900c0003011038862008440041034110301d9032070040d0b85901000c145a51082005076480c450098030b0760300500103102060015095070064100e00140c43c0c802d021150300302011100b100d0030304031601c1980016561040038075030040854005840f0a0320113209810540c41031541c0c0b031280418042c0611030400c2d0850000b514026802d00304484103081d6644d40c580b10701c01d1031802c0f84d8503640714201d015401c0d0b010b2103494500c80540403280c0c81103c503169962145000d070010703d90b444814003816124002e4a0024030b0a200800440b0f05212802c3d0302d0fa0300348014041100c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 448052832 1250 448051582 448051607
    0x60c200a050f1306172a0103020d0e01020f04081c020c0d03090b0a0f0e2407020103150305031309050621030712050315030a0506150a09020c3f0a110312010303 70
    0x40e01c05031180b80b03051148501c01c0108800b070230056540c40160812200400045002d41c4d069440401d58140c1600070b4002042104d4041084842446882c01c1e8411310141b02c2c1d0b81400503910801a02d141c0341800b00554000714020f050a07014582d5900790140c2c640d02141c4030400040e002a0000c141540000c581e1503580c0040d01d4900c40e5880e8a03c00d5602c2040c0c226143d1f01840700403d000045a00c00d81220790004150201301c840e2950764030b480c59890f000f511007000070704c14103031022981d04042c0c4241803041800034110901c03100c1d000c566081711050a0036a60403404100501404a800c4200030024428140c0d5043d90740d1034615644040144001002803090300400007030404100f002851940041000c000e120004c900c800000e01080c0043d40080b0348240013180240b181c10001c035082c960540d1810400306201d000c400601c086140540c1b500304004044071095912003080005480440308a0601e100e0704080b0183c105e00d15005445100d0710080000018010540d004038501940c = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 448054082 1250 448052832 448052863
    0x19031d06090706081918020f031b04110d09050705090108070305030301170703021005090f0d0807030311090616050f0a0b0721020301060c200a050f130617 68
    0x1600300100090380750800b0b8419102081060300102d049000d55204940030600c21090420000c1c102840103000d180380c070001640309040c2d1612089403814040341210741d00240481c150030140c016000c00c001840c0601a144e09810141b051818440c0305114200f1510300540003403030003502d060b040026080050b080683c1c0358020741030400009000009603419038000300f0405912005100c4510b160442552000e540138001824400c48103400c0002002c258500303880c001c0c150001c0d60103011817442449401000c88030100b00300d101281c4a0b6122444580c0f111200b585000081c07030024a15802103c071050401130604441301c1040000c0000100e4104410041d01208009803a400001c403001041c2d807042c4012222011040442203402051200b2040001c5489503110f40c4024002001c0340700844d0340c844021b40900803000110303809000024001c000780c810a04000c10700048200c060345c503580003220300354001c07640415030180002a003462260b102a01243d1100c0d00d1921007021104c905 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 448055332 1250 448054082 448054093
    0x1804170c0a150e0618060105010203040302060d0509010902040e010c11120306011d0307060906020c0a0e0c16020a15121401031e1505061002071503050c19031d 70
    0x60034402051019800340c0048074074001908401c036440c0a08001ca03949400c43c0203c03810071801e0a203255500c441201c80c001101c009a0304c44005907940c0c480d03800084d5020500340718508290341a80c025544c010310340e0300042a81201ca0f40842c00350f4030854914613032651181d0b41041c032560f00200741034904600070010300d540886156070010510000e81201e0410000328030001c4090445560b02c600414090200e850541e9078000c0140008a1802100014042e40550404528000c10345906a5403200c901d5641d40e1074001d60725000b5403001401c071014598205813003015a036020f41c500c2c020320340552a05202c0001d040014030a14409410b00c82c80d07840d04190000c1046184001415294005442901d4030300040a146a003081c4c0070340141215003029009410380c2007a00994051202a540c01040b43c02c10542640c44203558020858100101f04215041c0c070300c40e0300000e404c0200075100c5444d205074414101488481098140302103900c9542c1900040410440601c0c19401302000d0b01 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 448056582 1250 448055332 448055347
    0xe0a0e011118040b06030a090c0e040803010f0b0a021b012102040509071805010f0c1e03090801141515030c03100b030f1810090b01090c050a08070f03020702180417 72
    0x16002d004c05060191f1300365a0306180307410072580c0f009000280c2001d05180310036140601d0f2180d400da0003401195032042c01c4404c0010022040c000f541e2034520640c01604095010900c1e514150800c80820342c104047c41c0e0070b00b403001041c0c0700003000c03240960501607500c5040609004403100050852410003040c0c1e9900c00c0d103812000f244806540d403d190035164400c1000040365000c0603100d02034042e80c4010000c0d00c2107117107845a068040d100391101200d65644160044c2200c1c00810b815280030030b503000060f8001344258200040076070091802c04070710310003860035400e078004032540d00098100206100041001480030401001255503542c40c52501d412143d1b00c540700600b101900340d44440c02d1491407001888061110043c1840802001e05141448420044c0c00e02c142c0d1151807420858080b5144035604503000c042d42d649405066480c3d00c1d108440e000d04e151000c00806609011290040e5240060304500883c41e104d6590030741080d05004400492440f200d4241030300401a42 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 448057832 1250 448056582 448056589
    0x10e07050a03090206210f0610020a0311030f070b090c041802090a06080313090e010c091a07053307021e0304090c030207050d02070506040e0a0e011118040b 69
    0x407000114180340210b080f140c030303202054944c041c0c0b81800403840d14011070b0000c07140080c9811485140000001d0000343c85020038414902050281c450068000407445c802007401002d038010300d070780c44408482c034091b0001ca82c1d000a402140040362041e4040c010321810f00300401611103000e07400c035420042042840102c151200200d180240180342c2e100004010b1101944103000800d03103103040d01d0380c94035082c210a4400025010713090701c06160480e0050003400512901c0d4102000b600c4110106003045540c0c0c002141e01c01598dc0344038410480440011380a11403c416549410000c02c00d6105424140000340f803000203070380044007a00100031004c0d600017014940700307142428032400040c05a01c1213085200b5500009000c40c1805849520140c3c181d0003840081d006a098031841115154200e07120b80ea244a403e51160f0144000d00c440e60f603000300c0790b030000039504c0c00043c204511920b1a0946811000c818000500820070b480986403262840705640822074040010440b0f00000 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 448059082 1250 448057832 448057837
    0x15031b05011d041509050a060b040b0405010c050a14010501060e1f120605041109090f010b070b0a090209090705100e01090314010e2b030e0d0f031104120b010e0705 72
    0x103204001e140c65411001d20b03111a4080c800341d81014a041d1000d917200d8003580050242a9034010085191060005000a5440646058511858499203083e244c10011103a04a03001c0c41580d25000d40d000d0040004c04160680d8804120080082065803410b1006880d103040701d000c4e180103020000360700001d224013020750100c0a4072410300c1e00103201d881c0c0310007000306005d400c603541091401c600c81d0180219000541030f000030403100c00307906990b9a060000c94400038031940a40c05001d01c0341078000765a0403c80765100ca6501c20000e09078106800040d510716041d54008c005401002040c0000d007003003818002c10622070305201d908042c850303000030031100c010312010b80300441800804045260070b400010942c0140000c40e0f4075142c40c170f07a03c400a080f2841100c60681400c0a801102502a01031290724010040c045c0035801c2034a48261a9000420b031443c0404d45d03a034070160386521107070002e813001e000341c40c45144100b20340c3d1803c644d82000607000040c0400c045401c0124a641c02400c = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 448060332 1250 448059082 448059107
    0x212190c0c0312052e0e07020c0306040308060d020406060509130501120308041a0c040915050109060e030715050702030705420301060c0204150e0a0903020c0415031b0501 75
    0x100010b00c0c4d643c8601106586011840090140b4030540d11003000c84e500342101d4050382c0346d542030440581c80c0c044d010f90341e841030030300c1040d01a04003800140c0481d0043e03070401d9010304050000c6404a680e5800a400c43d807894100303030301180000c41c503c2c061b82800b04d0740c0d0491a01606042101d0350420303a0700c00507a03c0c031050040821612500013410030607180d201c1a44510b0504141034142098520305d41d041c0c019001b180b084a00d000d5010b00142c0810802000b1100d06846030078500d07040000c01c4451004240d81140c151007072480000d8076020b1031810081d9680306964441e290401c0344101800c01d50079912051103407009043c405124000302ca100100d00070300c0c140c7c008410300045551880b1000d64082c18080030404000020825080488003200c18802c0b102003000b940c0e100c4880071f1501c0c103401880500c80440000404145082c1d0190705464006e004aa000c10941000201620781615002d501001070070410010042a41510b2410341c50b4100001c1307040d0b09060000703000071a80c45 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 448061582 1250 448060332 448060367
    0x706050f2a0f070203070e040210020102041415090d030f0e0904051c020a0b0c030406050903160303020904060308040306060503010e120f07240c12060b0f0c010212190c0c03 76
    0x2c2c600031100c90403411900e070181e01906a41c81d007030b0b95080c0700caa650340c2114140c5c0078500c25801194132501c10b00c01c40b419a82c2c00e803041605040f10304244144500c1c40c50850340951010080d00145507207881001e003000b0b02c01d0fa40c107900740c41c404000030925003400c600c840c0a1520002800700207138021031421010390070103079a41c140c550449400c07490410188009400a4164005e200d9100c0d4072000543c81035000720402d01c580c0e16851911940c0744500440981082c42c800100307000284250000c140c0c0c020000c2c00400c2282c0c0342e84886125a106500846155645400030001420f003801140920303150705c006000060001c9a0b40940c0303100e0701310718014509000818a080013909403958040032980c504000c1c55400c203400e07541c01094001c04a201149c1070000b2500c940304140512815a0b911f0260a42804131001c0c1040040d000144400c425540030b1240380c078400d00c046203d603c182d1041d240c1c03000c000c1c0000d414504980d075014440e0f080106c120702180120f50131489601c00300c603150 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 448062832 1250 448061582 448061587
    0x1505130b040e01060635040507030b070e010f08060a0b04121505070c170f0f0304063617220504110f07050c13020403050f0c330706050f2a 61
    0x74a84006c40b0001c0d0702c801074071500303200c0c10300c01031040000f040300503a03102d9400355601d034880b40c4c0151400d04205402500160f582101c1e04d25680c85031201070b4000c00042d110f000c9080d240c0350385015682242d0001e003600c03c03602204030709000110303900b5181e14a801000701721038141150000e14240703070318501400301b03505800c41880c0d0f04185000c0340c200f18100c11480d500d540115002d410507071320580301650410b080c801d600c05900314080c10014802828421402527007184c100103038040032118001d44171444403681414040c07403100014245c0390452032100a025501d600301d9481034407203400c154052407500c0004007040c0380180880348541400f0030705a40b5014180781c020300d4201e10114150f08007032282c214a858401a0300940240d0380304101703450100100c1c032540c0760f480783c040c0780b404d5000d0500e41c11525032612600c603004107241004036030b2584201058084802c1d07401660100e403100ea0311800c000000380c02c40111508003c20400240540346520204444440c00510192151000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 448064082 1250 448062832 448062887
    0x3150103050c0915132f3702030901080a1b0e030f0d0806040c0806130b150c070f060f0c0b070c0b090a0203010507140d1505130b040e010606 62
    0x5213540b6071244200810300c2600c0b040d40c01c0000d02410403107513920030a42d582c080b08014130500e2144000030384001c0e0030302810004103945d214052500e000c8a01c25881c120007000b240c0c02800f0185203940b507180e4006655802c1505c00040c0700d424010100480c0a2900408801804650b010040f0958061901d000450704030400070b8100070342a146d40c81580300d00c00709200340e1a0410340f0144900c0c0c04032020003075043d540c001951a03030b00c221349996114418451581280000781e0156080e40700203019518149184810800240c2c010458034034598401c0e281001400580d4082402030046450101031103070b1101c0e00a8401965045e0041014008000003010f4911a0303002c0c0c84e1040c1c01040300441401c040350516120110104140e009500301000200085d01952000c045041d5540c0380c64078040c0d600c010039009100180d000509403800d10380010303d075900c40321400349020300b0b24000601020f41c1c10400c41150402600000c840e414261b080111a4208031421264160704c00482c8010a1 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 448065332 1250 448064082 448064101
    0x1801081506061c09020102010e01020f12040c0f1e0f050d120212070c030203010c050406090b0702010219050105090615130f020c240f0103110409020f041a03150103050c09 75
    0x81c2c500c0c0e1001183c0403040990034035080d030300810b1202e4000e800070843e442002403124280d120301e0b01800c4000004004800c20070725034070310035603000380100c503004907858840250010000381a8800b81c00010400540b85211042c841c800b002020350710441200c0c5031500011510036100488007a03c150520034040c1440b600a00411704492204075100c0d40ea03224501e00344580300001d0205a00941c0780c040419000d500500483e0b095603c20f03100c070035200f49018a5203155510400e0109d0450084e00c58160030b45615540c85030b4614496000482c0d075240c410009854500300030048008402c52016201858407098041003544041c14000f24021401b544a40c01074802e41e00c16041d14411500d0105074040d0b5807400b4144159003980402c82a01c0700070b07055070b501800b8000035001c001441e004034010702c0c0070340c841841d643c03010704000b08000c01c10002a04444810700a030b03903148034814003003546140034003030040c80c048503960131640c55041d6100e084ea20724080003124080c0c0c500c2c0d00810080700 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 448066582 1250 448065332 448065337
    0xc1615060e0705070c08060709050d080c060112110102010b01080705130b0705060103120306050f011b0209010b0307110118020405070c1202030a140c300c010605180108150606 77
    0x150301410700c482801c10100003021580544000e80da000c80340d6a002c550400c0201d08030340a00c090380e0f140300c0514244410406002c011890450380400200f0600041100901c01180281404000d904400899050003000c00130103a4126045900d40000300c182aa0850f103603641101051900d291510101e030090740b40500c007504000300003076001c2001010060000f0720349060701e100b80110320001c0d00ba07500a40c1a6260b41c080c4690002004021100c0c40d4421080d1150b0350581a00d0300c03550040f690040380e01c1040a80006803030001c00410400c1e01c3d074200e031220503a10106402000040c5641902d400340e2440e2500003441180c0f140b0124101501c10001140c016800c51b19404c856008644003a650346c0c49000004007203040d21910011601c0307a031007540d000d9041031002c0c24052200d160b4000c031001c10700804000300c1e50000c226142c00242e8002412600c0c2a50340005540da091004001c41021105050b01081ca02100140403241300030a00203420b40464035040c103280c41d0f501c009510f50 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 448067832 1250 448066582 448066589
    0x31107030203151f12020607080910021c051804110c0f2d21040f030606140a0815040809040903030b010809061018060e040b07080c161506 61
    0x5114070044a42d41c26401c90045001320b58150500700a000890042142c131000e51107161007480e90b07040c944015082a4000b44030b1544280d2071146006640c00c005490440406200c0e4010b82c04002c400c103000d2249400c0c1520820b5900b0b10a00b011640394868103049500c0c8820f03809a62114070380c1c0228040079061f1040c05540005880042e90080d920310ba0f5100ea0031f110503070b07000c865903484003240014405d00e0038001c81c58001d4108202c3d41c030a0300c0c1450000c000c2500d01c1000401000a42d20a20320548016503c00c00002c1160f5240810780740c900321010003100e101c1c800c4003108101c9e1204c0022011046540c52542e010180c1d1207041034503440c052a4401600f05061a03017050415030b165100d540f000500341c86110580c1ca84403200b50352004120340c0d10103c4850110240b2030710080d40104640c1004401010175030030b4440742b0150040c10191000c6680e5050401031245046d0095526544183c1c2c0b500601d042618041c00442350101500f805080c444401e43c1307210465000c0d41050015 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 448069082 1250 448067832 448067839
    0x8090616110102090a060c1a190504031403240405060607021002010605060d0e150c0d0905100219020f0a02011704020402130b040602010b0303031e090a05160306061d01030311070302 80
    0x45d2544d800010b0b00f07100e0f40c80401c4a8420307000c2c1241c21051009034116001c0d1100c41500c044508403ca181d800a100140080d0103125403a140102401c208500442c400c01c0a410041501241c1d00700c4a81d80401200c80c0c41c0c8128102010081161502425107a841ea0111094500e00211800c160700519942e08061f4120000268000114089810011801d400d1000b201d030300e103149075601c29081c501a50082d20000040000c541232101603002004c4860040301992209505010500126440500d40005910f0805026420550103000d6030520060b020b0142040b04030b20f60000b440d8190900c443c0b03034065011000702e001c2d500c40390306640300d00c000441418086519481504440e0304244503840056003004154000c0f428044190780c021020480c600307504001c9a620300b10b0442c0002d02c1125144502032180d004140100310160180200c42c0601c1c1100d425130400780e003a2031240d0170290020154815020703026502100e4103044a400d450410002c10b2112002403c1c00700355400a50f0 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 448070332 1250 448069082 448069099
    0x1513330e15270d120903140a030209030a0f05070501080405070b16141f0e1b1504031a0a020301030506070c020a0801060602100609063209090d0809061611010209 71
    0x84510b80024007080420b031035142c2d0032400b0f0140003008143c640c01c11004000841c0b4001d00c0c1189403890b0041c0213a220982009400c16286001007483e0007280c91060768007100902c030201c24060705009007006804280303040462880e02e82c840c01d27a40d0307241e80300301c160a00c1d000034121303405480845d009000660094a079036444103562001680c4400041c018500850364180b480c040042d684101403540c202e00c0c014020401d2990000c90720440e0030000240c200c104950040d01804c00500140040d44c42109011215506420f11040f4250003c0c04414014070420040c004250001107241d4090014500301d1102c40140c40442c0c214403080d070105402d5801d0400c04211190085140d003403088089004005041e41d90240717200780d40340f03849080300c003d0301c1c07000204882c24802d41045c0442001048441148180c20100c3c1046208558542040c0c00001d032101c0c0b01503001d0742450304442d1040085c145800c3c98600c0c2450f20010b000c0c00402d000b008901c0f81540c6c070080d015250420030040240d41c = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 448071582 1250 448070332 448070401
    0x131a0708091f02010203090606030d0f05130f180e0309010912151505150a05120711062419180e1501030203150103051513330e15 57
    0x4d02030340003622031010600611000490504001400411140080d0799080300055280000ea466038000100d0000014981e00c010441c0c0315501002c0c0c00070226403141e0f1300c10540d40305590301200d03080c171481c1da00c0e504104205019030707038006500fa06a132200c03101c0711040165444c202d0610403040c1015100c0c01d08100200c405569003800800854105840708a80d295032440010940c0c402c0c1c201c180702007002481140d80701c420340341090394850502c0c1046203a4191001186141c06000c5901c0450a2650404e8500039803010310403000343c01d002c0c0e0381c840c001d2081d818501d0b44004a40118901554140301160b40b089564010349101d6440d6400d89002c4d0100c40e007290101e03082400141c0c0a0311401081c00c010345c040d1440307941201e0f08080903204242c2003400c4981c0d00203000d00110000303e11010440c001c15443c11000700680b08d0001d0240003600c2c40810901964400044000458580350100c45252001714114041d0381e400030308501580d840102d010651119a501c4145082c1290203c0d03 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 448072832 1250 448071582 448071587
    0xc05060f010f050105040e01140a0306020706060906060e1e011407050f06071d0d030309150515040204031106070c08150105031204081c14070305131a0708091f 70
    0x40303042c0c80382000e10000782030711080191600d20640c400c0c410b1010b0200300400515407410b114001086000b842d50040c00d0b603e4841105a0b048444240c50803955128100640b506510901c4010a4541000d12107210008005881d42200ca8082d90107541c61803811100caa00c85e19210b140240951b001c0c036110011820000d82c0c0320a03494098213103114403404551507d0103414200c413924404114100c46900f440188405254050300490506464210b940c000070400004144081e5000d48001190710b402d9241644909020300c1c4680513500c1000280080740e650762001c6140802510328541d548511310b012030010180f58401e40150060b51031000300a840100d4a0b4122401201120303040606014001038a106031307c20286658030858031401c040c0380c00105004c418030207040c1240d4814201c17000b000c4941c02510f003103001030400580e01004103900300c07441300540b400c01c2c080034805a61740150412441000d0001d0001a0003280031801e40c3c5d40c0100c0160b203005840344010300d840742810003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 448074082 1250 448072832 448072861
    0xa061a0a141002030c06041e06020307120c0f0e06070c030c180b0102011b230315180403020c130603020d0b070815030c0409030e030d0f08010b0324010c0506 69
    0x11140715041011444140500c00810b4569003030317a040c0504003949a9540d4446228403003030a0314007180702c0e0f072031010104102c0d00c05940728410070389406608481a00c0b280088581c041e12080902000da6401c1508035404199000544030075105640d03180620f041c5200758811079400180040b11004000c500d280003071900302c442c085c460704e003880480d820400590030b1711411110311500619251036000040c0c440c81ea0b883d030001e00c1c10b110100d01a040005404103074401c45641c1c40214029a0a00c054144000d13200d02c3d081d024514401241055070b03000791104810960785100345440d5024960b001c416070702103402954001d040614040c040c0ca086c98600344101c40c0b640100e031707440d00002e020703141d16402c14444c1640100507042091000040000a0039801d00980c20005041c50002094800b040015480d590a44078110f124045a0004240010582019141c0e0074103106200440c90f1650103c1a032100741581c0700c1d030b4146c10000481d10802e040d080901548a10307814025101d000b0403d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 448075332 1250 448074082 448074119
    0x180b15070309120206180f041401140109080615060c01061d09030306010906030509031611120706020601181e15060c05030d0504060912020105010e0f01080a061a0a 72
    0x11411216903559041180801001ca070194129108001000c0c10304032803000014207040c001e0007c0209000300340820704840d068079085500703c4403200180148240f100f10031000c10801d2030008040c5081925094a40300080c14a95003130220000502c079551700c59040c2c5407900524402000784590714486803074052051011120010100320100f40a10404803c4a00c07904040c0c50f0401e100c1d140c1a0304500401c0020600241400140180c0038200500821002102d000b12050050784a084040281c00001060f0408607503101d440104004c540204a05046819608540c820101c2131607000d40a480e01c050850b0130094282403910090b2815840b447d0542c4003024441c0d0b031a1388510b400c2d10b071600e0340980034080703134014030402e00304c4983ca0b040709034003a100e001c0c00f0603265150b0b600c055400000c4003043c2c003d0b035141c00051042100140c41540e120044000349240382d4945101c0d0b030785a03102c80e20050030031512134001d50280b2243c441498042c2c0e01c060428818503958048082d446440d0a8 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 448076582 1250 448075332 448075337
    0x240106030b040207050c19120f020411030108060c03190c0f1101050907120809091e09011e1a0a0b120606070809060a02070801110a030c0c050601180b150703 69
    0x12081c86103814244240d40055a011005100048402c4200040c1040b8840d0007500425003000100d850f080c2400880300f0140f00300041e0307403101241c1c0304100c241c86649480c114a210244010400c200c0c00040094101411402c91941c0c0d0f1600c0d511141c1d00d04800b40410001400c00b54200e00d1140d0052802c04403581e66591141440420381e2ba1500760780741500d8a0b5529841407001740500341c3d6000c1250581c41c80b03505541e160580c0b100105018007000c84080d0042a0788802c0811800207041ca42c56220300c400d402089484c513907090580103505c3d003c003813050185d80c0381c82c1080c00d0441d80b400b00b094620000c01c002145e42d6201c540c81c83c0c40d400040036086660203c0041803003401c0c41025690280d50280d10103080203000814050241c00448843c802c610a1103070001d00e0352400e20400000350090b1840b10303900c0004440c06819200301d1b075075070020803d59140200214202140302819100c0035400402010044003e90016100c81c0103c40d6024190001d010080d124050080500340c2c80394 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 448077832 1250 448076582 448076591
    0x90a061811040e0607030b04230f0a0203010f06050c101d101a06091c11041a030d050c010902090c0318031c0f02041212030b030c06041724010603 64
    0x1009110944000003d50721a03640020003140c002da000ea002054160006400011014450582440c81c1401c100900010004c0101070161458030246540c4d1f1012400b1815483c6515101c2e003d1013482c0103216803410070a010078228080203050010030200030006000b40300311b1441c81c00310051803600074403031b90952181d42100c500500590290385007940383c299000800c00c0c0440d0601c807007a440001601d071700c0700b00d40c030904050100403e44812600e0164095651807200402884102d807040140454000010324207088036607000140d5401941d06440c0264441c110340000310f0241002d10700095201c1a9841000341030540c1402545c4944800004038407a0003050030380301d403280304144110021400c6500d40365200d45007908841c070090411180140303842e540e0b01000d06500f4a00b24101c40984607010b084100507890302507415229003c40141c400c14189400240c9a81b10710b12944001d5444640c100d4040f1806002c0c3c1c4045103030307160418020100c0c06031800c444440074026100030a240 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 448079082 1250 448077832 448077863
    0x1090b0d03080114010c1502030a060f030803070e1f0309150507020d08091006060c030e0a0609140d1406010608130206040303081026190812090a0618 66
    0x80840c4103440d400d034035012116402c0c5003a030b00201c14200050781c18004181e0b807810010f46031039100181d01d0381640d0016200c1c03c1946c40f010586041c0d60102c184610b5002c420300204a8140850390488501e0801c00c1c2d54001840c041903645501480005440c030020a0200c4084e4150300300c1164103100d203581c0e0209001d10361404045400944142006030300c003a070308807460f900412513590442c044208031780154003015507083c20390b5882d400c034900140c0d407102036404254000c7c00c00c01c449202110300000d95810200010401c00c6a4400e0b02200c410380703600740780d4540319030b00300e0059582c02401c0108200405801d45658000078400d000000d003130f840c00189066480340c810071000d60f00070062840e1519549003182c0c40d6002910120f01c03400d190030300241c03c03e8251a8010b00e40c90710404811581c00b0403045500300754000c5921f0316140a161030034000948050200c2d11800c0b401c8140012a407901e4840c80e1410000000003000c640c503201c1c45128000c4120140601da82c400c66610304c10600 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 448080332 1250 448079082 448079089
    0x42705010f180605031e162306040902120103120804050307141606020106090608010608030f0a051303050c09070201020c0c0f060c01060b0a020f0a03090b1b03030f01090b 75
    0x1001d100c0d948007455424000d00c4100040003100d41c421186031404940c0c80d85490010b41009240148040c2800726881095443d01d42400b03030384604614007000c800d46a00c0c0c071b180c80c0c0038840e41813464100c050084211442940d11001900d001d002ca19100310748411415000c040040403e00040d1081c001d000e2114150700d1240e07102d14070807644039000c1c506010702c83d82d840703480c0c2c20310039011100b6020780c003a820140406000d105005020903400451020710305010101103913800e4118050690601b401171103400c0e4004100c8900f071a511101c5691100a018121414052280341050010f41440000140140000c0e101c640d05800c885151981d00c07042c03001d80c202d02c103040c0445025000500f0400e51843d1441c0c3d101038503800649014a400d09126940d400c4600d9508201e22006c80402d81e5044994100591165004480010080f10641d5100039012070510b1007400340c1c9080000f02403542d410b4005103920300103400c034201c0c0d48a0a0102c58024080400d0107801c00a51428103803070441d24 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 448081582 1250 448080332 448080341
    0x121111303030219080901080a09020301090510050a0b01050702090a0605060c070501080703050403081305070506160b0601020309130506010c020a12051002040510120b090403020615040c050d02030403090305030427 94
    0xc0e031120f075940c0b86c00400740c0195050280200740b14a0159909030035009a10207011f500d9034a88150040c2040038410350f1520112800075217a4405140362400d1610642d03003040c21980059011500100075503500600000545261f0b04103070f41102c40400c03c503401800014284c0142c60b000d0700e4030035240d44e07120001c408484040780c01500248024005c01c0e0485008118081002e000b82c0c2600c0f0015115004120583e011384442e25032010410002d0b01407040100800b500440240b000e54030f0f003e5501c0001d44404010050214200c2d174a1002c214580e002c2d4000c0f01c010b03607001c0c19128440369110803d070b061950820003607409016518070034840030410700c00c0714240d41005103000301250841034101c0781350661303001d18181d15585803c01001075407051006885240300341e009100c545440c800c1d130684080004a058091810b203042c003c0c03525006030076500d008000003001030303e941c0c0e1820200c5455010f90f0020348a400700040204640c024101105807141d443d51030030000607580f104500460307 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 448082832 1250 448081582 448081633
    0x501120e07170f06070518011103041d0c030702062e0603090302100603020112111303050d0f11070515070f080d0e0a05190c031a0406051501211113030302 68
    0x7a004001c025103480d40d207c1c0c92061000d040c58441003804c02140b22910310340c00390708241101c89141c003c00c0c201030702b0006010303804010200d2080c11414512006035441d0400b4110040194881c0c3d080380a00c010308560000c1007130406080b8684994521024000b03010001e01580107000d510301840e01c000c02406890103c3e5410f07544e065041c84019135203001000c2c600c204003460380c4100103000d01c2c0000540401c0185000c5c002038080a04001c001074041c100240101c07052050503c0802c080b010003041070400c84a0030768411464542c600d8200c0d0340c038402c10900501086103000390200740b101000103090f0484020004108103035400e40c20f5a6900c0076100018019442079034008109115071095031880c0307106410640380d050b100c0d1380c3c115842981d0b1100f101c1d80e01400003000300f8000b050080640060521704038a491002c0c40000030420b2004091203c10401582c054088098003a80411811304c0c002000c40c0c2c40e44e182d046185850b40d400d102c203900512401e801c000600003645c40e4100c03031 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 448084082 1250 448082832 448082837
    0x906080609060402030907050306010308130602210708091008010303031107020a151e08070206010506030c2a01020d09050735070b07060507140a090501120e07170f0607 74
    0x341e50342d0007000b029510041130720200b80a022000213a9031401c00080740614403c940b901d845580c0041401d452040a500c03500c11544074294810106208403404a48004402d20660b9101014144a230704c9110741c0741d0281d04a05041c0c282c941043d0705c0000703141601e200f981c0500c18040b81c2d4001c807100e03000310b1001a50180c00040100495088000c5096401655081c00081710302502e0f008181a0b2000c1d420102042c0042c1c00c0080b403035814400c0b60b01404089548900310304021000040900580b016034011110f40840c154507003035898000d000c40c112400003599103c2c0e0080701d00001d48900a01190244500c800200d0701510b5100c1d032614411a2400a00084070b11849590782030041c9102400c45005000d4041a00d41a240040800a016480105150818080090a0681150f040041c00e4401d002a5103400d41c0b105661080344c50910700400340278201040003005095401c4141f555102e84000065035801100c2c25100c100301290a81d1a03818002d80000d07160a8211500c800 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 448085332 1250 448084082 448084099
    0x3021215180618040309170a080d090f0c0b04080705090903030403080415050f060111070501050f0702150d0506090c0a171e18010e010b06090d210f09060806 69
    0x1840782040790441e52248004002c100a00e06260240f0700741002501c4c250009400b900003030000602c1c105500c1d02428840d401024010a10740302d045c113901944941040d40c68940b035042c004d10409034030082c400d942000c4005056070343c0c3e61603241154003610031020107000d0f4410001d030501d006080c46103d4151440035628640d0340799012900fa04001b0021a0403041410500c0592a17940c810305100c2e40f8480c02e0b000c49818003000140c15020b01c10070100c0a03a10110f02480b907640e01c9030594840f01c4500d100c1980310101440042e09200251034040c119400120300805110881d802c070a0082c0410347c2c6081076515a103007200b8440c40f40941c40030108030350b20281d0602040c288009079206da1707584030b520385005020307100b0410440c0580701c03984c4248900381029980708081c481c2e4140071140000800c0352103044030110f02c242c00380305807007885069000c0009050064407104080042540d900003081a070803c00f01410501c2207468600005065010104c0d8103030240c00203c0c001d9600510004 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 448086582 1250 448085332 448085359
    0x614010810050609120a06090204110a120b01020f0a060203010603050601110604030f03020c0f010b090a1a1203040b04090203010603181a191a04110f1608070f0303021215 75
    0x310590240400680119080785c140707041d1039003401a141c0007441a0000710344100a4010041a00d100740d500300b01e001e00801884000d140c01480344081c4610702940484d0003550b600050f03080901d0018184843c2c020528400c003041425802141030310b1240d182001030b5124003004449100c00d81611200540c052800710340440e01034112011901da80745405407520360400300e40d90928040c2e1141c4000c0ba919103413014a280b034110081948050101c50400ca1124550b08d00c039004446850114003c001c0361080c40802d1000344100c0f009007031001036031982d484d6903208400080d802440391800003807500c9485142424118070b4200c8840d0040030510f8024245203000c030300c0c07078005080410140b10306444810400d6090181b0f45400116a10807009464445d00788401d540d1002c0d42800c81c103170104030034824416003c05403140c04110701100d240f403080364541601284034605001d0203040b8440142810142c0c560000c240941800c5566040f41d1256002c0704502e0503171342c40b4258020001d41900703 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 448087832 1250 448086582 448086589
    0x31b09100c0c03020402041d06060a0f1805040627090f06020a1106010b070302011109092703030c070201110a08030703020d290307080705060423030d03061401081005 73
    0x25100c070b402445101d04680e0351358005022640568415802c031401800032840e468030290440782d2040d03064894a207841540d8000419042c00c426841b030602100c0440e180350091008491005000701900c10004913407100d8251103480721207601c4180e0b15200d011828004015030184041c1c580d0310001030008241d09903100d1f00a9003041020500300105605230202c100d0003008030500078005840e150303950303400301d0400a007994181045154018020068030700c254070b8840d401307648004801903040040c00c48c0f110701c44000c102860080103521020050000100300d6000070602a8400d0f00d80d101c0d40b04030303025115100c0701c8042000c0e1800788180001003446010382c00a10000c1d00740080080e90301c609400c500a035000b48031440035070f8401c0b0182d40009080410542001d800c14000034444c5510b443c001845c50721407070151249411051102d21034070005000d5032107510348010103440614001800003030007404507228111b030600e0b00b0f18242005500800c4014040c2c8100d00f000c0209900b0b06052 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 448089082 1250 448087832 448087847
    0x806070f0c0b09032107230706020a14030403020601050f1008010b03090c030a080702180c0d0906021204120906031404020d1704170d05040612051f030305031b0910 72
    0x40300e0000b000042020125009000751040100d8001e4005007041c810017094621002c0f040c08514804068020071003d040c7d007501c510350341c040c0b80965156529542101c071240000c819001e01000841440101034010a003107060703803800d49000c408030804604201c01102000400c02c0421107040051058001c60750017513a010009a00b00d642840c003d60100b40ba140c14420203135581759002c2484011490031074100f042501e810185210b031418000b03070550341442600181e004190b030710742d1f2070b004208164040d20704102041451601510382030401880761601800c0e070400080b0106008944075009110302d07207680d0700f110005001f55465900784906040407900654a50b2211000404001214002480600a1480380c80a55940c1276200c81ca010311420303141080c0300040c40107115059020070000c2440c0000c4001081c2a11030481c0044246c00440300d000a4100220020043c1a0824011805034404600b0380385031010426088049024030006035074130494101079403102d035110f07245 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 448090332 1250 448089082 448089091
    0xf0f04051c090e0601030912181805040203250605090a150203040906060804110402160602030a410406020412031e031a1c020405100806070f0c0b 64
    0x4841c414680c44001c00d030300090440c545030004040000500110210341c11003a000102820207021800b80c84d542d00440040c2c83c0380742c004000b07060711b14806640000c0a503400504239486100c480c07000c04445000031703010861302039001c0e00c1000d45054010052107591003c900c0b40c0c60701038401c98204641100c0544c400d104482d03001300e41d140089801501210b11020300001c80d002982d8a500c3c00c0c40700c80940703d4590041051080c40010080840e001c03c52805050b20105c41c0180d45860441d0740e4050300403c404041c01079031010040180181456000701402c49000500030f42c030500c80300001b698002c91340d04500c40b014216281810045803c1036490300584600313005414142c80e90650248011035000c02e07400244207800080d080010700400c80302c40d080502d02401040b154511078162f01021041850088102030a140781204403407852080542d8000d10901c02800c01c642c03081c00070b08060180850500419011502d0a4022101906131030500d440305900d0f9001501c0e0610b03008070080 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 448091582 1250 448090332 448090343
    0x20a1709030904091103100903121401091806050106050a032a080c040e040b160518060a0306050411070507061b1e0506090d08010501090f030b09010605061602040b090f0f04 76
    0x220480c1707580c091080001c40c91140304005401055401c0c002c000e10074060345403ca20345003101303e034900186a0001415201c00b0103000c07403010b860904c080166803240310003401c203500e40400410304585c8400100b0713003d4041d40c0d062000108440091070f109081c8904c0c81c0c81d04081c58011240e060095441d641d00841e800421800c01e580c607601d6450074a0101e074200c0c5c000b19131004000000f0182e104446c3d06030680e240040c2402d4500b04290010301c03000000f54840d410210780280020700c250041070207400098400c0c024500844403258598001d40c41c211210300440e1808540c151182013414034524010040200d46078a90f22815501080c51681100c403001d60f50101001c00d03810486180546441c60040080030420440103100200c10380105040180341c0e64200140b07240d1180c488182c80d00142c041c005611152007050041045030300c001e40018003c6000000c4c0094141000d052070300a07182407021601510402041800840e504050303005d00901181e00207842c0c01c41030380c1c0b052241 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 448092832 1250 448091582 448091603
    0xc0405061f030c140a1b150c110c01030b060304030810030b010e09060f19050910091b0e07080126100204080f16060807020a0c09020a170903090409 65
    0x303201c0c000350191081d81100842d894a080350040790b80182c1e80e030844002c00d00350904114a0010080c0184118140410b03d021418000710a2020000c50f05035070041507170041102400c0500058800005542d4500450060962096655000b4041c106044100070211303031543e036403030303409a0b101000a0511320706000c48180220020320510000c078040c094440401d012882c01c070704054039280c001002e620301d01e84100103000c8050311f41c02d041d90241d0b80e0901c000c103240c1d41b0a00c80e145040b942c05140445541801046000d0100038045141c0c200d030b4002c0038410403503c1d0210400301c6501074541d20000344440300104400e80c2d14444103030020400d0040e0010f0004007040842c6001c4060380c0004c0e1455002404001d403600403c440c80303504138400082c5c05051400e40684020411610882060048030070015032079074400e020380320f42c0540c01840206400d4894034078000070341110b20b0303403004941c401051200714000d001b1034501ca503051800a5160a0780c0c002804064040c0c043d08542007201d0 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 448094082 1250 448092832 448092859
    0x30403020a020d0c0905060f061803010219090e070f080411130f06080106050301180206030402011107181d07060e010e061b2503020103090f0510060e070207080c040506 74
    0x4030340c3d148440d54003807148a10080e0500701808201d51000e408035201703103052280b2407410b441d500140d03912903031251031100c65500c00101103406407040d8000344207032500320154900c800f6080700c105000d036030044201031f48613990000b09652540400301d50708081515123000400240d46031601d00891407000c1c00000f00d02c09543d01903002e1314880030f1602404c0d40c43d400c0c140625042480354100a1104900a0200c041c0000c03031000751960b0b954002e03000b900000300017825a4080c040c96071040c5e800d02c0440e200c043e51001d846040066035440510710a040c120b0750b80340d8589010140040f5001e113000303040740e80e1400d80c0689845405400850504c4405d11400000c1e80e9204c001c0c0100703c0052000e144520345c44071402d03060145a4400c101201e54203c26900103a01504400007501e0b4282000030b200081420242d200b00170f0444020300f54400c00c032501c3d10210a51304284104d9001c448001001d0700c5003107090780c0b241114064058035030b0001c1c02c1c401841c507082d01700a801500280007510400380 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 448095332 1250 448094082 448094089
    0x1d0708091c030e0d030504060e0106030c0509060406030b011502010c030e190507080f0313210605090106030f121107062c040221070e0a0302040b0127050a05040e12030403020a02 78
    0x25004e90312000c02d036036108100501589004800fa8291214001c00c030711421540c0d150f5682c0e41da80680c0c0d018411400020340d081d06e8903481403010f103401409081c1c0969588240825848040c1d200d40019400c0850300d060150103405542030300342d542405483c0301d05002080c502307540038150042d10700c0e110303410300050640c00601200200794001c1000e10340e180c0300c0c001ca50387c0c0061154041110508154000390303640c03003480351070081c41d9802107000c11540c80e2150554050322031500013411444040000200300054005602c9001e590340e1241810207202c401a0754941c801440b410001c64017035a040c809540000e038644484407851969440314102c0b4902240813a001a100a060500c81c543d0b00c041c0001e16204140d4412030520b00340354004908004203003020410303c03000740116114003c0114680c01b40c152288804802c100000c801c0007011601c00c03045860784a0540078001c204000f00c2c150030170b030050410741c2c003500d0300510151f041d150030740c120703a80b0003001601140540b13111728005a8 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 448096582 1250 448095332 448095343
    0xb09010c020607061d03070303051e13030504030501180618030230040603020307140c0705010e010c060f05060f03010e060f07050c0a0c051c02030615191d0708091c030e 74
    0x101704000558a6504c1d52901504a420103480c86d00b522240d610300ca0200600d16440c10f0780300e07800781900c411100c04c41c94141c40d980140c3d00003e2595082c0b806d80305101211074a1000803a0240d1000c2c05640c0031104500b40c14100104064016005160034000303450f1407407168821400c04400e0380000050346000200d094203c3c0d00b0440010750004144018203501800d0a5a030b91b000046035840c1685400302c03940e840c0d030340c0d2103514144400400ba440403a8040c51a00c0140c0e40c224400b070045400d800b503240b005200031207245e40f00703012a402c40740240c101442071003000c902c0c0000411140c0c4078500410603141008000310f040150801650200340d005100785400c5030b200301d03056804e1605240030410b0001c01c021101c540c00040016003000f582d00012015000034401000703809600c0e4150104446000c05408045146c03510b29002a03004511800e0500112004995a019484011080303c1c900c0083e55030309403590010389030340303036104800b0401c1c07920f13254505000030700e034018006103030510 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 448097832 1250 448096582 448096631
    0x3131e0203252c0408090d0606050907090f03110a05030307050a0501050105090403050703030c02030409020a0801050f09010f090f1d0d020c0907090e041a040b100b09010c02060706 79
    0x10280d00400c0c0200c10240c1e01400c01034402c80300000e12a03501c0c0500440001c0c120b1800f90200343c001d20120303062140c0e0b42c00301e5200c10382c061f00c1d1948099240c1084000740806106407401750703c00c00e0019501c14429961841600c0c114880c504a6600e152580700950001180d01a848191143c0006481d98200001c00c9414414000b519101020742021030031164140e110901421315501040f001030780c0042240c403281d40c9810b00041400554104901d1400349400c102140c80c030018501d03042d241c01402c1507048034070445440c43c400030020184148101c00b0b20885a4501c5c00341020300000c2c44030f4005c503a8400e5031807000100366000034090149641c00300e21106054010060213980c05605006a10002d5016103c0100034202400c0007880b07075140340b00700404100254040b500308900d240d02009040100840300181b03003842d0408132114001a50b13440d212242100000034180c91400699012500585600307034003000b04d4003801800d81c040c6c907045903c242e40b184000c0400d5805071012410 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 448099082 1250 448097832 448097863
    0x18030303041a010902070305030c030403020f0f030d05010b0f040b1e04030803062e0309051507020c0108070c0f0f02180406061a070b06010c0c0803040806150603131e0203 75
    0x3094000769951900106804c202082801040f498001c42e8120307048035008014041c20745ea0341c1e6542d06007241032002010ba0103400380901084200607030030001c058400101000001c10030b5076610700c2c001e0700741d20071725030013020140c401d01c01004142d8a80d405400044140d1061501c116180b0100820562151b0401c562001000c000d11855003094201e10030650507031001c4040400890420207154541c0f07403000000c042d2550100b10810106000d81e0700328204152000c00c85080091010b902c030701041c11300500107600301000540083c4998100b02e81c4a4022110103c03107610b07620f43d100b40001d105c4050b60000944441d04201207000100240710b24010600011050704110301c2d90080e48600070035400e410428014003010a9064544031342100b02400c04003903203130182c44d0050030606241e0082d0758901000c1030004044401043d40c602c030311100c03602c41c00c103489100104119400107071030410300c8142c110781030400106101d641360084030601081e01422030450380002d15210104254482 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 448100332 1250 448099082 448099103
    0x906150f0901120539030a02010903060216060207050708250b0f1909080615090c1e16030905041a1210090606030c050306040203060a0506040b0a080f1c0f03021803030304 75
    0x40c1145c402d09000400c1400b24040c10b09131645070002400180540400b504440d40003071007201070621b10161b4207205500490a41d00c2d1840d1303061060302c51040c0c1c0b0404140740074003841e0404048c006a218005001a821005412414404403e001e60402484c00d4220641000740300083c40c2c50001c1101ca203565580c61a02c914140300c085400c00344050034108081140c43d1285806640b192580759100307003518807a0340c0f241d500d03000a00341100341543c0554118000074500c1d00c1075416a10070b01026003c0d8441410503541c580501c0103d0304121035451202c40100c1008140380303001210183e0f0201c4041c00c680e880340103848000d04803044010110344456655100700108410320007114003c000481c040c064510b840d4010946031355000f4011600350365980002203055403568860342d1301d02e2026245180c01910307a600d160362614008000765003441082c489403080901100481d8913400710350358080441c000d40006901a405c0f11414800d071444808600b0f80945041000c1e40c400c500a014222 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 448101582 1250 448100332 448100413
    0x3090b0a02130e010602030711060417060a1410090c020f011a131b0c060912080403081614070f060c030b1002010b0307050120060906150f09011205 65
    0x2480c82140d8810f501e1010b519004210194010040d20078040c1c00841c61251150380c0c0b00004d1031131003560030030318602c01d10080c0d2806c8030790b0005686128030154001040541c5109001c481c02c04004c56004401d0305020205005905285e000030f1071000c0f141c0103c4042c9107406107194250f03122202c40c9994005540c0b588003044c90541e02c80d8951035203000d003c103c81c0b4511200f0444445894007070703800b4040907011101c1004415404030300d084d504010003c0032000c074440000c06450054406500040e03c8ad8045150001e4501060b85030540c0b80e10340ca5050742800000e182c23650826402980c4100140b0781c5c5402040e0980030300040406207650000f25505418100a080300b01c110f02901160f141810601603034400003810006e032442420044485041e02c40311810302c40d40c00c2e51441d40c9002c1c1030309011458000146c190b008141039040500d850048600b0b04c43d2587c03504006580c40842d10004102d00607801448400040c040c1d404d071800e110000f030303205805441a2100c2d9200300060305111 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 448102832 1250 448101582 448101607
    0x20c09040326040804030b070c0c14180603060601081f080a0507081b041e1b030f091e05011803020705041103060d020f01022a0901080708060a0c03090b0a02 69
    0x90040b5002c100b00c1c0c4076581000d0b00d85042d076014500008100110410100707034440c0c01080b168071000d03848004c0f49801c81d101c107400d124108032a58a24054070507184d41440f522000e03070b08a48649405001042e00d42d503010011688820098500c42480c03180031000e00c00c450f0a4108040a02440c0d0010001e624182c41c14910304200f90348408201d405c01c1090700810401d40c1c2084545400403500851142903100d000f14001003515a01e51243e03140410645c01c0c811380010890b007241c40754808004400b461104003064400c08000186103000c8400d0101503440c03443d000304981c6003d200009a1010414025401110710304400ea026a00410007003100b440c00b40a44c40c030108030f00d40700c00e045042c4100441c244e5103400380c000b4441d00c2c40c0419011a64400c21a00c58120703c00050030320108014070340119510440400b00303006a0802002099180001480b14220748603030340240901d80c0d401c403a0070000d0000744000c104050b01c603040003010036101c501e02c3c3d000c1c92a2100041c5d0fa5492032444 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 448104082 1250 448102832 448102877
    0x62d090321140c090907110c04020406030b030609010612030c0c09090302070305010e01060f0303050a11061302013f060312030b130603020102030306100201141512161203020c090403 80
    0x40c811020030411030100c41da261201740341c2e08280e2504001448551480a103424044080c0100c0d400501c0414005a1940c2c19080b803450060b080e000d40d030180d200ea03100079098910500030612080c002c03c50881c0000e1041005100a60013031121b09001a141c010050994141c110150b0040c1d005401c14014004203100d1080d004a0072002005040c0c03a280002e004402140b02c040c1c02e1150210b65440c01c07074020305011f98400f5103d019101c01345440d13503002c0403644007564264005451a0100703446a04c01c0802600c244e1502011040c603001c407951220600c80042d4072441629481e80000000103464400b1268401384c0341d00c01203690844c0905200e41090780d2113400b44a68103185040002d40d8010040f04e13080003094410200002260405170b0250200322600c2001c030041ea42048000c0402640880501c1000c668200042c0c13105200265500e03207024100c0c000240c01e22003005000340e50b011012055202e07005507251044c41100049080030203c505030042a410581c045035046803402 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 448105332 1250 448104082 448104091
    0xd050f01061809020904091407060215010b0d1e05090102030f060d02090103022107150f080903190306050d03110c012a0302070b031003062d09032114 66
    0x401c0e5180624800702e400c044020b82c81502511640041d220900d03490755001310203502c4c0c01c0969002c4002c41403001594801d250704c6a4801409001c0c04941707441104820030741215000124142840b04852503007004180c0004001001c0340c5900740c0c00030411031401040e105032208400140c03245846400b6a41418009105900c200300307032a0030000503503551081c0d0f81034079010744034115003111003800f4007200c0080c05011103a500c0342c12000202e59024040b404050111075862540a1a0910302940c00b418103035098040e541051080140945140280703a1720501c035480c000c2032003607890000c980310740c0e03038000150300084001c201300035015000c02400700100700038179021040c0383e040280341941d03110908020202c0d010242030310050600c200120000740c080f103a4240c0d81c83c2041130091910b188107210032a802c3c0d0a00f050103a26968a03d00d50741c0075402004410718200e00d10700c080d401030010344011018040e0031400044404c2900f0b00c400f524010b031080004039a142c03400c028811400040 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 448106582 1250 448105332 448105337
    0x7060302090a15050307031e090c090b04480203031b040f1e051f030b09010f0b1b070b1c0501061e0c02060a0807081b0a1b0203030d050f0106 62
    0x3c0141602c01e501004072035000c1d0301458001201800e070f14404900401100f00786140a04105100301401a03c0c940c910440e42048420030000a0150501065840e02e01d0502d0401c4e0414500c1e0a80c41c09400c52200150590000000040500e050000581100910310b0006a101004100080f2200542e0384145000600c4403410036191030f20740c800d0405140220324890030034040c54240001c00701c00c00005030000901c009280c8030f032843c0158128070041e52020000317081030041402400d0903200d00307041c1c0300107004007406030341003800b11945980800c07001841c0c50b44081607007002c44800d0140001501e0580c00c4507503a0104840008135070403030815105c1b4034516060042141e0f941110fa82c1c04154144000c107082030407098011745075040105170281d04143c0006000002541c4030704510b103d011252181c090680751070240300c5039840d642c1180d40e1040010400c803840c55024000144541d007a0480d041b0300d00c41c003907002c070341960440407a854840f6111020301c903a40c210907e0030780c054030062 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 448107832 1250 448106582 448106609
    0x60e070804080417030c03040e060108160905010c020f0a030302030a11030f091504080703030504170105040f0201031a0d0b1503030705100504020a1d04020f0d0c0515040807060302090a 81
    0xe8640095502ca01d101e0850312804680540101103402c0c810741b4081c0c544441642d03140d503990f400c00c52601c00f003111404d000448010000740769039440d0090504c204656611a0050390800006413004020074206a90000780c05880c45c0465039114414400386220383d02071601e4401c4d8a80187c200d001307003410b8a02c1c80d0018801751075812245800e0343c4041e002154200c0c10040300048200744ca1080e45c0010180380a46000032003410340003402402169103000f140e802c0441c0c01000c5030700300c9000340e50080000c0d40911441001d58402e4020701c4a5486200c1003000d120030100005942e028000c1d0100c800f0405c0304108070014441007131241c0d50840c160b000d9454010070b40d880d030307031140341e0329882c1e50703440380d0b600302180035500d5218000010b807441d80c0307405003400304514103102c0301e10080f00c04900c03c03282003251000c0f6003031401703410715025800303458500680c0c01c00081151b500070800b24440f4080045c080020105010001c0c1c0e0020006501d00580d250700020911000026503004905440c0b2035 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 448109082 1250 448107832 448107841
    0xc062a040501020c0603040303060f080a120507020d02010e300d031401030303050405010f020f070204060f052b06050c070b06030316080c0f100c02061302090f150d06060e0708 77
    0x204d05940b03d06412540950b5a51b80e5180642c010302807030301704100b0301201080c0403610000000d9001c000c50f00030003030180d104042490840b00791003500c20082d044840c3e200c0000c01540625000d408010b8010040f54034041a068841c10003034400c02003005000d0100d10784032250342d09010040c800c140c07034130b410312140000303003c84c000d10001840002d00f010b0355000054107018080d8006c02c0c0e066258a030035951030704800ca110790190081c54040e07100390320700240010640034405104044540142c0707080c0ca18095840d2001c01d40c1c1c14108425200e484d1081010300252491068621030380c42c15059603102c800c9810001210350004144030b0190340108644291080318020340075000c1c1e03000c400e0729901c4034903825941c01e142104424600d07030710680045900c51040354000c048200da03541e080780c601e5030b990710b48003036200400782010b904011030b0004a0312404141c015194007401400704070940200d881e0200c0c140d10003141d419901240c0d64641401110900d511554004681c1c0c504241c03103042 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 448110332 1250 448109082 448109087
    0x170d05090d0c0e090a1511190c1e1a060a051014040306060e010605030c09060d0b090109060603140c073305100503030307020601140a05130e0712080913020c062a040501 74
    0x8d41d0a240c05011013000700c1080c440c4039040c08050301d03a000e90200301603200740d0144403195400050440d1041a40c002000c03000355581c06c0c807845400000d01421200d1b19180070b202c90504445241c0e410000102c080c4c08600790380d031005100452068000007640c0e485c1c40303504806003034183c0083c0c04014040040c001c10301d202c0c0c41a6100400c007100e0007075403105001c40030030040550500090b00541c10800004124100d90302c804201c079401e44050140c02d0b00c0807e04095044116a643d01d41e030300500c603460115490581080c0306641c4404c0a941418a030310203007d44a40c803100c00c121840d04c840401c070f142070f03601e100e4900501d4207078000e42c154200907034040e456900502500c04413400700040000d4070b64540402800608014003080007507404002c840c406401e0340303054110709105400c0f000842d101403a10480e0704507009108181098a14000c10904003200c105400840d80c00340000e2021450a1050500602c2201901030100441182501044906004810303144209000410560341c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 448111582 1250 448110332 448110337
    0x6030c030d050a1412042319060c090b03040f020102010c09030201080402040b0301020d11030a0e3913020c0c04051e0405100510170d05090d0c0e090a1511 68
    0x80038207280c0c00700c44000c9004034a5001c0c04800f066028510b10a00052240c80b8400c07c41420515004164444003040141e0b51480400c52450309044401092008100741d944091303507c1c0164a010107a80d0b5480160011981083d14107840826442100d0800c644c2c0901c541014400c2034148030440d0391647e000030744004001400a40510340ba950807c500d80e8003981191101c0440c1030080007a184030480070035054004580c003004c403d25184076184190030000d0400c0c8820307400d20345004050b4500c0010004030280041d00b0403c03a0120150003100e83ea0b011f20415902071605006813110340c040700c11807400c285074020740d00070761404042c0500d00422840e4610084203040c0c1e070b403003561110728125240a60120b00512481e1410b01480a00025080500d080740d00c0702044443ca084502e441980300c0861050803404520100a68400c50521004004007c0c0c05140410813550392030580760790703c6400310795400e8640c00c807a29800c00c00c2a6100e030a2142c40340c80c402003003441480c400c02801031 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 448112832 1250 448111582 448111597
    0x3230106030e0703020a12050c180402120a08071a0709061d0d0611040f14060301050d030219050102030703230402150d020a120509010b091b0c060f06030c030d05 71
    0x540b82d601c6100e808004105100007141d002d00b130a0050b1b03580300072140b1081a043c40c01c4440340106550381c819860700e442d4011030000241c1e900b01e41c9849640c20008a500d04102282850140341c0b20000810481c2018001c51406036191030080254040d005005101c001d04d03001c14854021428424190b000c1143e81403c1d014070102c2000701c22000000c3c038203620100f0014042400c00d4080071080d9620701c050022504c901c1840024940c8402180910007580070310160044001c1c001007207a40703004d40358400707a98000d006641741d4510359100101035004421080c6d801d60340010503c040640d01d07103d20582c804501c40c214114400c000c0f0070014032400900040d00c0303504100f41c03000e451454002224003000c0a1801159900c00304080a041c543c09408028140c600d0b040018a1541060280e1203524078010705250460b81c0d403a003625001d034a40b0041ea246400c041c8031103089080d041046034080c0046801400440c50200101880c1040b01042d09000c0c0c0c02c0026503440c0b41e41c21100341d5541 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 448114082 1250 448112832 448112837
    0x1203111c030e160902040e060303070b0406020a03020c060718140d12050412061b031802091b040815070306080d0809240f0a1a061c05010b0a03230106 66
    0x642c1084110540b624030360b1031060400300d4864000003818562a401401203d8044252860796540c0f01c04241d05c0303000340038001d46031130800c100240028003958000c001e0302c40c02d41001410141501841c519041045401e0b4010541242544000142d10144d01c4000c02180004003000e84010f40455400c2034150360040090650600007400d1500840c01d4402800314070100300141529401c0c60702c0500b91000c0c46012070707811301b1a800d00162290240f0241c050f88007210a642c2d81c015820301203440c1000b0501d02c4031282030030540100d401d00200400003403407400018150080203000188245d14094441024140741803000c0013498404a0140690140c41c02d108007142e46115101d403c14050b03002c5e071440131008214900d02d5005000595014240354070f401c00c036599410305404111003401c10308a001114488211119140c002c1c01800d00e030401014184102495007124000d4900a802507284111f003c1a0a111180d01d48245080701c4854941c5440c800001d190305010460180500d504 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 448115332 1250 448114082 448114091
    0x6020909060603160e1507050a14060c09010e0409150603031d03070608070e1011190b06060d1103010602010501171501410120030301090b0d0b011203111c03 69
    0x1261b925452049014515204006e41e11099440d08030b0b101c050008040340d0a9500500e0000c09280014025203d5010f02c2188e47c9081d50010055402d00303542410315600544680342c00c07000920300d40c07094031800900280898160300b5403a02514101140a0102074a0741c480c0e0404e040e50b400280320401c40300b0500740000981c8404800302c61190342e01302071603040680750791602d0010741c0c004a030790340f004221001d0760101003588805284540c00000007070401200d100100c0c420b45000b100804000c1908071000802903c0000782c4115600264860005070355600010040d05420304410505480004040e02c40501100f5800f5514041801a480000b4a68516038203000d4405054030304102c152050f007510303a56404500c2c910708000c0041c1e0f400620040d148813444c00d18460700c00342c41c403200320255003561300b455100f40051002003404c1e54000500303804280030403264520742d8080c1201602c1e1540c49c030b04900b40500b51420302c0314900840d600a010003448114000204900035041f440d0104 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 448116582 1250 448115332 448115357
    0xd0809040e03090f06280e100f140d021e0403020405100308030f04020d05032208030a020c0d050102120718050f030d0c0212010c090f1a04120c0e01030602090906060316 74
    0x440052681280e100f101c84601c24045051f4111784602c50012003100c04d0301ea00c00c84800112000c5500d18030540104070701500344664a14410042c055a40e80301d0001807c0c0804500e20b41c000b00840c0403082e5001c01e0000b414425800c05001d0641e0008800c550941e043d031865075aa98075100040150400c1c81d148030200d0708654031a50310251494219040340d4035407080b220740b202a1000f8003a98150070100c2d10300010391040101c02d4954501c240d4010b03140800000d42400085424151308540d5550700700450601480403005082c09a49a40d8506010185c5074004a210032501d400143c4a84032001c0c41c0000f0369000a0f52211012203450821715a0408d403011854020001c0d515040755400d1421543c001688803035950100c0f0b5030100d54807442940d400d4410104c9001d00c0510f03803007613020001440b000040f407894402c154400c00440c0e0200d80da40808507503403c0c00384c2088400c1c940000c0c118845191003c152600702c4d1088500f1403442c20802a1210300c4035850403c4414000704101a4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 448117832 1250 448116582 448116607
    0x120605040302030d0609020d1a01050a030e030d06080f060601090b070327080102120a0912081e0f16080f010513060503030f0316110d120b0d0809040e03090f06 70
    0x2130340c244040103020f104083d00e4915010281d01b104040410407880c0c083c003100705500701150f03a2140901a15010720b0a400204110081e20740e20701804071600c07040108140244840c030466005017441c0c0c024060321341c11111000e0501001400d214100900400b05001d9810804101c6080c9907050602e00c201c03104202074070560410810030600c4bc00d0110400103403586041d00144000c01c3c0348904542c095032107800c010100c880143c0003812030701c8038404079031250b0300440950784c02200381c554454051190803030f1000b03c96821600308882d200d40806102c0003502280060f200344d521410714025074980b0980d1b80c1d001c071300d0520440c0c1c0b04444003800c04d81140d10303035400b50028210282c10743c2e6585001b05040f020a038001d85848030140d440742c0307070640d51512440449001175840350240540e0101d4480c121a10085221b484107619540c0c0310564030f90ba144051007090900c140c410589800141c1c04201c00c840491101d00c89540080000441960b40c04948000b1154121180c2d52504141da205 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 448119082 1250 448117832 448117837
    0x60617150a0b0d05120c07050a350607030911030307150c050409020f0a1404060c020d151a011d011b0f080d06030c0f03080316020c0d2a12060504030203 67
    0x40c28500410340e0307070601e17140b960004054042c030090403a8280c6554030103001802085100e4051030341c04180d10341c003000c105002e0700001a200841400030052000110a040c60303816034220001c6641c54202d10100103880314284d04c900d00440c0070b141021346544420740d51442001660b0b020340e036a0b00d05e80c14030714003600585015081c48441103444100800140c1035940c84038443d5070110f0300304820080003070380a000f02d80507500703e696040113511440c2e092002c91403a41c5022600c3c6481d6100001035400c403803160181d13181060803d0111103180d40005084114080e0b400e00f0900ba4075440b010059801900941100c29000220390741c0607001d0a0001e00c07901103101c02055814005501e803401d008a07040103095030700494210f210141d5910852800707100c0352000811800b000c0c0001005a121031032030030a40300c510300503070b08065980800505000280341040b10940041d40078142003800e0300700500d51030500b20000090803070820300c450788032031406140100301c030f0b85900001d400c0504c207106 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 448120332 1250 448119082 448119109
    0x708040215040803030906060d020105040306050c09060711010e040209010228080a0801060e06030f0c16060204080a0b18070b13081204030b09010506012309060304060617150a0b 78
    0x400755101d50710b8807032154881c2d1042d610f490f810300ca2000404c2c400d10f00940e054040d603031b050f103a00703243c02d24654441e805860018040c0d05250003d101c0080f09440b00001040700c5441030740e00e03182c6c0045220002d13120003c0c5814140c000c074410700c200c1c1400d0f41c0001e042c410414192403500c41c101140c48001c43c0e003410a8100030108000441c88084843d0030a100f02d0580d5442d46910a84209010602c00300340021100c40c0400804e5001188882e80b054006004000c9640920107604183c0d0312808103a0f03110b94803000c0f4036840b83d04084180029103009540185206030418131203101e0380305540e80e803c4203010707030490001c00182700c1d0020740c540f0340c10400400c000744c10b440c40303403014580303c040326081440107071850042e47c1c0000c4e20941301803080900c03c4805031510020051078901c06003050110920b120252041041050305036640d9101444c0b00361b10401c8040344050809030b542800ca58034000302d030070551150340c280c000200d82c44481640842c0984c0002042d5000c40001941400c8212 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 448121582 1250 448120332 448120369
    0xa02010f2702030a08070c060f02060403140f16031d0f0a0b0c190308010302100e09041b3f05030a03150b07061505010e031c020a150c031803050307080402 68
    0x8054007041825488078080708c1464485008909071481c090381c4410302118001c0000b052001c184980041c848060062802c000860a06000c1c219840c40c41c10741c445c0703c0a40200f20780a0012004d48091941c51860b0001a5804001046c404001c103c06021130301a18003104000726003c03902c0b0608000c40001d45904001042400d0801e0902a08904080c04144c1c0680498950200c48038018008082c1e50b100160142241d507542d40ca0f010350b5010040c4030b0f003031002c02e019000200c0f00c640c204105032305143d19003209201e00c85000403a00320152120100a407041807821100898070100c20341d90181094200864105541500003403074484c2500106200c0c10041000011b00c00c1e59400300003003514929207600c1558031207006440518010325200c0c0d055003c028a01e1800401e20700700c000400041c0100d9010f902c9554400c0c00c08649484844029982c41102d40b218660500030040c128250031041d003070900e22928010607601c00240114107002d07405d00481c08546a001c8101000d071880d6 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 448122832 1250 448121582 448121587
    0x8030f180a08071703010509070c02030f0706030222180b030705060a0f0206010602010b1c1a1e07030221040c1e0519050901180902040606050a02010f2702030a08 71
    0x10714042e0540c1d000180291204000500e1442e140c14900c0c0480c3e05840006202940540c0c4403a4122a550001d40b0220380501541035070b558413080402146014000949009d0785030745100c80b98040031b141d0444031800035510402d00b0020f01d085403000194800107150042003c000100100c2d24000d83d50307100e039400c282c0005650120304da11400095001005500351187c0d643c0e284022401e136101710b84241c0d48034051085c0a035890010780c030a6480d81d4440d0340342c01c55503840f1508900c181001201c0652016080001d5111042c3e140180c843d8400790a0804504007440c10000b891b104540e420001c0391150204081424000d9800740351004005d5402c1e0340700310741e009408050f104040c074807800c0c0c0a400c0b00503c0c850620811140c100a0ba4409001c0c41001c2c0c1c0782840b484c010078009100c120210b951100c6900158981d40030720000b51a540e2543d5a842d103418200900f11551103003005030030391034200c0003800c004200200300b400c02441d00040c2003080ea80c3c0006402c18075400402003446a00 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 448124082 1250 448122832 448122853
    0x11206292107091203080118050601021c020f010c050304030206100803030417120403180f050f010f1404030b100608070c1b0e13060c05030c0403031d03032a01060308030f18 76
    0x22a40d124103850750323410803440c11003006601b142558810780c2c045016800c402606030070305c032203041c035004034500900c12602d402c0300303051086007100c0c241400240094030003c208014980c041081c560095061455216064601103003071740c903400701500c01003511031503141010400d1060f40c1611180e4000304680348240c05c00d440c02405101507010310203405050301c0342c0040e03203140202e101011200054080840410803000440d011510080150107000711030250703860041d550303406040550b04c034511503035847c201150241400000c032f501100030231501c84d04118219602003440b040d4241c0c41a03812501d694407e02603905004503401030003170601a0790400c011044558640c082c5540510000c1142d10311301d103000c41c1d10f071004552008070404200030800009102d004596014200000d011401c44c141d500041d0540d8000c612121100c0c2c9140d24240300e0b1200e844000d024031100c1002045424519911045c3c0350000a001c255540700910000b80d403507032049081900c00d00b1000c240c4408400c2d = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 448125332 1250 448124082 448124087
    0x6030612060a0510080c13052205010903030b040903021911040f0912020303060a1a040b0c0a02101e0302090312070803010f060306030b010302060702011206292107091203 75
    0x8100c401340c04583c1100c1d07000610003070203d00070030f0010340500040403441e9202000000350070302a0140c0c100032100c1405000c20541d4a101c188034911840020440e10101c1c10000e09890040c2100b07881145006411800070790005000f012f03024450921442ea11494104100070207041810550002e00340030000c55160482d03400301440ca4803403003c07501c007110030320000c80e52400701300c42c0c0a401440d05001809071030764280084180030294100310380b0741a21a030055407103070044040070405600080c80700c001c6103071001043d5803034200c43c80d11150340e0360700d07034841a05011104185014540e0000b080b044644050000b6813218403288070710381d5602040d281204030f0354424850f001c00c9592041e00452554440c0c003404c1c040303980000d0114260390a50302004199402030b5000c0b410311100d00c01c214440004e90003850000c00c01000160654031003080151401001070313008145908080000040b0700c100034422940f40d103030000a165007542c80c00429120000b294108a15503003020128400300340c0d = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 448126582 1250 448125332 448125341
    0x6110a0228080c0d0f11030a030c052a04181e0c06110703121b05061006020606060a14070501050a29030c010e060418050105090708011406030612060a 66
    0x14405510210040c2c0d504800c0d030b21a00c80405055000203640307620f00201e000043d01c040c1441c06000da0010b60502e180029290600b8030314202c0106018910400a2240600004500c4804091621500d0390401415584c1030340750611688125034031104400300f8a400039071408203070340c800103800031024507280e0100c540d005520102c4401d010000007080403485a44250341c6048008018031030720781503565403c4100304c4216004104840806050342002c01000d40c03103c2c83e4065000342c891400d10340d41c00e85503486e2540240040d9804a0b007400f80a444140445503040400d15085010310202d0302c002100f840b5079403010b0000e41c00c00052220041d126401024200364416450784520600500c0c0043c64070000138155150300601c03100c41d100c0d40104c1d80b0451810004002d50301d0145c6841d1428020012811350320000342d0b03684018401d0b17041c2866001d41041e1035040c02e5145601d80741070101105464120a03000745408400305881c2d440c0d504001180482c040203544107031510107175800080 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 448127832 1250 448126582 448126639
    0x2030a02030f1f061d061c0f0c0e06070309170105060f0f01051207031d07030c0e06090c0a0507080403050604030807031a0d05030702040e1b09060a06110a02 69
    0x95209800304124401005109128203210380d103a00f1030034500003003030310b07a9488003042130340c01c0d400c40d00030344196a1080018400d13503100000021100115101e0003040300c4100d02c9980d241c51030180d54109058125203104071041c82200c001d951642d4a14048402c4c15640c1c1c811250b817984101c1c85540c1e4030040d08a203210b40015a5400c0f8048903038400c04c04640f20144125010600070422848418080010740d03600c40c400b4200455070111000981d04142c910180d41c02c4240c110032014000c005c444140c903c010b0440020304803050030100005040030a018281e00700d0507200007000300c01603000f0f1007078500d1940c000e01c00a4440d65a41006605c840040710100c2c001504040000c0700c1902034072844515041000303a1122100c05030062021030042400c0c01d4500d48800d024010050f83c40c0d0280e4484c500544015080c10b10340d07140215204151810001e1003601080100000d0b521003250140c205c810a00c4c03d254074204420409090500c2840042c0d045042940244000c4982c8100312054 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 448129082 1250 448127832 448127851
    0x41509031109150108070c05030a090801050606130506070606050d0c170f030315030f0609070e0c0a1407230708120405031b2206050a05010c020a061b050102030a0203 73
    0x41e0900c420480065000c403169561414040a44585548141a003d5012840d4200001040c41d1520742030b285810008001d00040c881c02d100384807545007030240c240c0005040e102607080030014040c400c181c11007400ba260150a01050300c1c014417449820060040a0262090241c042281440d0481e0701840c0134030318906c445004081c5858000107034842b01307041c0e91b402540c219103c0c1c1c0c00c01e84d10001c8241d244d541c10300ca410b0780081008820300159008180c3d9400603c003040c6001071800100100a01d5102c860740d0034040484c84640048001610b50389030024190b903082e00f842c2c856a104010f69031050b08080c200400403106000154141c02c0d03401d04000c64111801712078141010b48518026290150032520b000c8000c2804250810f00385100201104102c541c85d41070f06c12020500c0b60f41041e038075140e60b010450307403c0c03004141c00602000c1c41c000d42c035402d254002c0390000d0024850313002000014040c4441340034203110031484455000c6c0c000c0d9500c2c205000748070701a4100741c0c0c40800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 448130332 1250 448129082 448129103
    0x1812060222090f180c090b06070204110304030e0d05030304152703021b0a05040e0a15090308010603060b16020402090a0f050405010803030f0c09040b04112a0c12010204150903 77
    0x1c030303002000c0e002ca42e07170341c001c98031034031a81010385080240812068254000c082446400c0059070340e4010501000c0d15140c4240c1c80f807070036080003071110303840c413824034015080c000200001c1007002c401ca0354000e401404c043c600b03906c084080402080003490302c290b05000b0802594240d8682011100c00034000d600701c03003400c400005900411701507142c3e80ca5010004460401803410143c02c96017080080d241a111a800c0da526458030b8070000d9402d208000343e4802c10081099081441540900b200d845c0412005003404102401c0d840b88482d81450b01c518103400c0e108554940d0111072000c0405400d20785029a1040300c403000901c0e50084520550900001040003000002600e2040e01080003064280d282c480030302426074028000b890b0403917100c03981e020644c1c80f01d008114480030340891481da070703a00c1e07a0b409400502d80911603041d07a6400482e11010398074000f61a85540c8030854410721081c0c840c00c03030180203114552264000d00000510413403003a402510b020304480c0541c84010 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 448131582 1250 448130332 448130351
    0x3050601091a12090f07030f1b0e100e22020d020a0b09091308040b0304030c0b150102060604090512160507060f0f0206190509030c0a050d1812060222090f 68
    0xb5240c005e03440d4440e140c0c0c1d100103030403c08229036000c280c00c040e010f458900301c400011204503005c961503800040d8130b0402481405804070345804160003c0c041180c80f610503003040700070703162610444400c0008101140c2052000d550320002d6440050781c0c000e216518940c1c1d944442e500030b4000001e2103125443c450001039000d44a0300148034641d9100b52201c1c03805040095007841074001034001c0d400c004001f945200028103481070300e80148000b42c0706111010400000a140603c02019280100c0c10080c444000a00c00a4140070310040b1358582500c401361600250740ca0950483e000d4134074401c0360000070341250005589030071030304142e03280d00d084c1c0602032050381e42e000d00f600c80c803070504000d1724412050103103030340b040740c0168881050300d1600c00b46500941c504014003030290f80ca03400010b070710741059402c000170145140503228000ca0113071414090207805114518041d14044d00064200341743c214055004806803c1511032180300c9823a00703003401c010800e108180401300c0ca0300f14040d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 448132832 1250 448131582 448131601
    0x25120e0603060310020318030a02010b040c0e090105011d180105150310090b0d06140a061d0c030c0c07060f0f0908061816031113020403021003050601091a12 69
    0x240d2040402500400c0540071004c0050001d50008000b6428460b82c0421030200220a10081000481540c004600c0807c040d00700011924030036500c00911002c4843e4240c1a100d281d031990442e4400d082048943c00a1001564640d175404070301544000f012955030240c0302e000c690306059810645501d440e05110350400b1140d440305484c21034442000d01c50030881a501904030a2503800c0c0600040140040c9907203a200b95404500403a40704503200003045080e11407803160000400310701000180039407081d03140d030100d00000340c004c610181d00013000520602641c02103070511414501200c2840d690f030700004040c529020100c01c0081c1d114101d40711940d10a1055100380c0d04590050912501c5e100103c510031400440e00c03030303a18016842800194a90890000d000f036020b02101511030f1038070400c00600e0401d9841c4003035054814001031001d40c80315010f2510345802401d00181035110b20b001640c0b03509a940c0102c41c8c0d0394903000c40d80500b0001c0380c09010384070100e2550560588035050203 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 448134082 1250 448132832 448132837
    0xe030307020312071704050309122a040222060305070c231c050715021206010c0812010311030c0a062c090a06060206130f020625120e06 60
    0x1400607481840341004042c0b180e00020340085050922654858170003070188083c080444e8180d81c2d0741c001041c05140d41c00d000303c00c0c07a060341400d000362a405000c0001d500500c4200069110140f100003941e1810ba15241d04030303449108000040444030301040b4580200f40c0b068015031001030f0038400401c602070702408000c035045900202d14054182d5860b1201804000c2e842c0c8085a40726040a00141c105024502004100f4547d00c09a942d00142011918040c010800c88405441042142c004001c400d6005800490901c0c1030050002c050921503040d0092483d49403855011500000400c0104219554103540a4050329041170004040020644841c032585000c075002038821710b1700750a0221100029650680c244c03400d0baa4001c045225100115001c2e0002c1f84d07107081c1400400d404102c22035201054245560b0114010f945105d240310007080000e014240205000500c80311107603291100b000101d078040b1058185081c98000520400c2100300410042e050f49845400e25104 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 448135332 1250 448134082 448134091
    0xf0d020426151f03030201050702190503030a09020102151302040612020109090c0c06050f0f09060c070f0609021003050f09010b030a080d0905030a1805090108211605100e0303 77
    0xd42400404402d00600100c0000c00d480040044084410300d05410221580f0240d400b81e400000ca0b890010b001034a0031a40d443c0c0c00746090040441d2800283c0000100c9a2041010101066031940d5200503481d01660140d802400d000482c00c11400c00e68442d41c00c1c00c0180215030900c242603071008440c1103c101c1003406400210800001d001c82c201d160031418988513540b07444099031440707480308030465000340e522845c024250340c10310402500d007000c0c15801890b401c024005030b00f011403130200c983c45210f000810b402c0e0418020024031610380d000b50141600a04101a50359070410020300400c030449020f0040e590307842c00314010303110522450511440150050401090507150001a50000b0040c01c08244e168010728001803024805012511034940b40c0c190040117038000c001d14000c254101c5406600c000004021031100040ca54007a80500002c1102030505004e10354501d10540501c0c60703030740d82c1c0d40c12101e040190008110441092184040102d600400283c50b00c0344000e44c0e = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 448136582 1250 448135332 448135409
    0xf031107050402120609060f040f02031b131502010f020c030a111b0405090c040c210c0903230106150806060a050f03070905030a0f03080f09060c0c030f0d0204 70
    0x84c0042d8013400e0035042c99410100051841030b030b0440d000001007da0341c141c800c4182c0300780c020007440000808162005003801d06015118203001c0f400700a88142c524034841ca600c8a02d80c0d88090000c54000c0d808010312400c00c92040d50344d1008100c0c0d09541c1d901c6401404001020b8100d1001c0b10800803442d00c1c1d030414a139a800f09620600020080540300190400e8141d01600101c969640d03181c1c0720b041c03500ca18540f203038030140007401e0390a440801e4420000e81514105002a101c003580103034140c054a5100c82d00710030f59005540021440a2010344020040d0300e008400700398a41180001c0c4030b011216500e41c1d050743e450105020860066660080101e0003d000b85e00c18500000c002d1540300c9181e2030050482903503400043e180820b0701e042611000c41c4901e200090581c850801907010907101001c0e889400d040010b60b5840000805074103010501240d00c0008084c00d20454820117014281242c030f510b4141003d000130340c0315100b110041844d4805a4104860801c50342c43c5403d440b4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 448137832 1250 448136582 448136617
    0xf04110a1808030c3706090f0b012d14061e04091512050d030507020f06041415150103020901090b070507030302060c13090b06070f031107050402 64
    0x81030a541c10700c01c000d800700d81c003507803010045400d001c01c101070550305000380024150410b20411103d50081400007038119072211460915000d480c0d070601c1c00b051607011100050080c90b03414801441070307846900912034044d4100025039000c00001144145034140004100950303407070203402c11001244904801c00100318440000c40c80c100b00a00001261a100c900542d6000044420315074041d411005420303668400359840ca40012503e60050112a01e41e00c0c0045e40e15102c195844040e00c001004050712440000c00c01c6109100c01c03104009802c00710741090405161220005080c1d0b00c2141c40c030b100b403138801542010fa10507500d00444214508000f0541c04100440c041d42c8098006411b00044000020718a0002c0c40108609400b4401a00030603096140c02403d045004d0708030301c1c025809100340604c4003e80c000c0d44048461024001408203002000319580c1c0c0a1104040e00c120007a82040d420f158000500c02e21081f00c06c0c05403240e584c1c641e0100001c9004900c060b6100607442d = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 448139082 1250 448137832 448137847
    0xc0315030b0405011409030307020c0607021e04021306031a040b150a030209061b060114151305090718060801030b2215090303061a0f0d0e0d0903020f0411 68
    0x240641e5034000380500004103c0c00e1407100703d0000404c0580d040c00701540000200000309905100012604504070b4099107024800e40000382a080100c200340c4201c855950f03d2a060341d550f504840140305c00881c5600f0301555000c0180050540410801303210301e50404008003890984a050b05d0744900420304015214550714987e0b117908407411500506600300441c104655230308024011001c180c0d50600e2084083c03001250400300c041e4031001400c00d5405c0c02d41e030345580e0501c0600403242004a40c03504c496160260810100b111350280d6013000c2c003007062040f13243e400031440c403502d81c2568004403295580c01040310050024130000e0044000b40002c10303c0030f94803030103000d885120307841071031409600c40d100c2075a0b004070f0611820801e07aa80e08039400300f6401d070280400404188050140c0612044090341462140035408071507414001038940000c1d00b00d51000103140444012240e40e40b40e6503a000d0090072580c00207912a189441e1500301515050154880c5515810621801c0800 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 448140332 1250 448139082 448139093
    0x50706140f01170307210f030c09050d03030902060f04080f0d0c0602031f0e0a0b010503010f03141015170307030c11012105010e060105070b04171c05040302010c031503 74
    0x540f00920a071070008101c0b42c00810343c2003035420400a5003101c0b801140400e00304c05004c012003030106c0300515080a02d0807010030340217000d241c22940309682c0351045002a242c2100184004540294001004903c2840e0f0880c500301400c00c1e18100022034200701d0724107031050343da1048609940000356403951340800041c12900a581c219020700c82c2c036103113060814410b441000751504004a00000c100030800762100e45c0c014115084028240305240d5410001180c0d03400c401c1c1e0001401d409000c100d2041c40544c1009001e8001828020420080c1c0b20f0b10a8800311260314402d50b4085030055110081503280401210314441d0301d070700c03030010003180c80d50744800c01094030076040d040c810701411000122903840d04482e4500e643c40070004040d030400c059140069000b40100307041007418010394000444889140f80c20540100f85413070b0050810b100055107201c0c3c0104017a40c0601d410182c0f00d9502c070b5820090142d0302c40d4001f0f10520559580c00c500b200c03040c05002c0018504400c040001c203d = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 448141582 1250 448140332 448140359
    0x507120510150905040501051501030c08010b1b0d020715030b0609040507110f060a0509030307050f1e0a03050f061509040b03010e030a0807111f0c030b0907050706140f01 75
    0x42140202d9003146603280354500440360202d605451694403a002c10010315025204000740000900301003250000303000e8000c142050500650020340000035420420211902c820107101d98038008445544000400007034039500c0d1449203081103e51b000c04440501d000303002c2e1403590360700581454101007021040002402d00a401401407092011848070003071003d110000c04800f034500107081c24244101041d084a03001030520311213030400e0003030041b0b956014080301d810b01c000c0c803119510fa100750b07c64600c050301084010743c002403000074020b0b002038064020a11030580c030443d040c460359031141070010840344290b05988400e03007080a40603614182c2e01100324444c02a0002550340f0304404010300c1d40c0d02c50380e0064042610101002125a40941a0083d0700110301c040e05424030142444010a20641d103122211130711a60702001e894860750010420782e90013030a10005050140000d009603100c52801e9070b18904000511b603140c150706403402e000740c00c00030060403541c7c6032400354507900 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 448142832 1250 448141582 448141601
    0x11040f08010c0f39210503060108091603060903110706050409020c0106090501030c0e1e2206050c04050f040204050303030a050408070f0c0617280e0105090105040507120510 76
    0x42c000c0c0c002c03908001e0718a02c041c08400030300484c0c10038a514542450a68048014181010024496500c00107035502005507a001142802e040001c2c0d25541c0419051949003184c80d0001c800c40e56000080c4040c4d03070420035120b8000d8894400d050100901c5586541e400e00a006c04200100000c11402c0d0f842c1e401006a10040c500004800c6e03110711084d005d0312030a03071040c2d44890741c40e58288502c1098140d0305820102007103020070300c205018000c03010280b00808600c8100e4441d40301e00c1030940b40c0c0340300350360656008004000c07030b1401038000384041d0000e000e558003030410b0b1340220320f90707090520880301501d0000f001541160ba85804c21000f402000f04200c13049601440315100007440410708010703a0f40318011415041c2d0800c0c84c010988a4140501e6405010300720038001d40480445029007500121104035076908003426041c000340c41c16000d00c2c9030f258a00810080001c0040d442a4001c600c50000d665950b995007190400d9001c401030051310940154a2004404440b640f110404 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 448144082 1250 448142832 448142867
    0x60e0d240905030405040e06011805100e070804110d05030d05060a1a03011406190c0809030703060e120a020d0c020409020d05031e0316050903010902030111040f08010c0f 75
    0x100ea4121451010740d070003a8000c803038036840030038103005a24280c041c00e00024401c0300105101c1d03150944085a000f014400d18540c44e90301c00124910380684682c4030050051380e04c02032079a0070321140042101030300300c1d07043d5000402c2118814076440d140c003e81c14240d030400001d42c1441481c040403c01031101030001540207482000014040700c601c00c8052070361000303800194803503242c0b807909602d80c030981e64118802c9804000141140442161240316528a450041050300c4c151030400315a04c20700000ca40c1c58400d14034004100007840d0481c403000c070707404c030705459103258084034014060189035444400768100440303008420344503020803181c10340020804122150f494010170184504100203860b00d400c00200040f100150341401200041c1c540c40c0c007451407810f00b1001c0c441c0300166112038100031001071811250b9909400198145030018000c000703140700c9001d5420390364007a20403da811a03203442e0000743e2102c180700383ea8002002c0d440f49c0350350780059801115042039480c200003d = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 448145332 1250 448144082 448144133
    0x10e0406030b01120b01050102031e340201020f0a1a0c040306050705121302090a110c011416020f0d050703020a1205040602011d070e04080d020c06040c060e0d 70
    0x4030b014549000d00a00080e07800a90400c25030402080c440030580080d0305651003004100c0e032000b1088171880c007a07581e58942c00c0d1203011356082d242d280e59030510040b0000e00207000c1003035400d400440388070002d8401d03000c5a01458108400c00d89031014404003420401201e0401480240c1581d1155070040032203068600e0242c482d0340300d508031035081e10307240005400411386a5181c5080302440e9004400c2c0809084400c01543c002034482000500310300341551500ca0386c044280c8134034280d0f9404030140c8002e11903500540203280180c0f5003140d89850049902401a0480d4004a103141281030341d04003814030400e80e4082500c490740800411030441c400c41204c040850a000000d8100b21490340e50305569618004c0c00900792490801103003003002003a0706228078403030f00043c0b14045858500007035800b540c0d20b0800c0c002c1c0e401a0141070b424540005807104e03003941d02080c014440c91182001c81245030b2980400c4580c844540c0601d5004840000c1c00f602051440f41b00f0196003004504008 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 448146582 1250 448145332 448145339
    0xe160b03060f0d0f230619021c09111c05150c1606060f0503011112090f060f100e010e150301020c1b1f020a0f030201020d0501061101050106050a0e010e0406 69
    0x454204130b420095a48200c0381404240d10484c0c0030310038071010344010092405081c0301c42e440107000e4048101c0e0119a44c0003c0031504020414600559900003100c2042a1641070401c4581e143c8408400c5100300403942d05502c40c1300310704034800c44158010004160703450b407581401030300020143c0900e102041c1402000d40e0041d0380f00990800034440c007004a1154a0050304807629043d41e00080c0c403a90421000e080c03c000c00e8030940d0300600c803120001080340c642e504543d0030304040c110310044a000781c404020144809a603840e0044025002c4450004d0b950100410341110a01680601402a0f00443c1d0031240d58000d141280d5001800149442c02ca00320092410100c0701d45504d0409070742e841c00710240b40500c143c4100313510440403240d003884d80c804001e40f03844404400600c070f040c40203480000e05100f54141d655581d1044000c00455071101809060002c070350401e24155820700c5c0c00400c109101301c0c1070321100155a00d44a20501c2401c2c015580c5c100c190040c80d0308960b4404000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 448147832 1250 448146582 448146593
    0x17060919050402041118030d030b181009050103030215090d120c0e060d0905120310031b09020a0c02030d0c05030f0d020d050421021606110f0706030e160b03060f0d 72
    0x1404410505210310b00481c9009040c5803c1c20305581908c82410714111594905031560000b4061a503d401f058450725030354910400220748158000760a0b252a000005c82003640000700442c0d500703000d41c40310505a42c1d140e03480d40d480246103072120001c0c80501c5000d10407195a0080440c02000e41800000b500307407a000320788103070070504c1091071075074846210354113101e4140b22040c0c006406032442403075403910700300c07000c2c0310203071440020030f0714021482100c6000002010030001d446005c5095642c0e0803011030003000030f4101c0c08107900c03c0c0640c804580c9a10300900d01030122a40c41805141082e035003190a040c01d030400340056030b0303c41c1c00700240121141c0f140f05040c45280305c2c4400703248110042409000b5540070708600d60a6522801d240380782c00124010000458080b46030920304566a10f010750300b013401c600728905151182c0719011422640640203810922101022240d524030b0b541c2404100304000d01c15043c8010f01000490383c2070601440450400740060800f504261075035491 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 448149082 1250 448147832 448147837
    0x71d0c0703030e0c040c0e040c030204030c050d0f050106031a1f052404090c090b0a050d0213050d0c03021f050f0a1103120402100c03020616020f030406170609190504020411 76
    0x1100001f51000c24104010718061080b0142c06426180450400d1704607a03410440e10491b014252007103110620700342c1000301228450081e40d03071002c000d2003050760764603101225001c401d40c070464140410001442a0038102509040030302c48150562009103000280b1000e0b00344a0b04201c0c4508429014220011600c4c0040c4000d0840791070010742c0f0303009280000c0c583c1070030b500903180307024040200310003696110007503902800900100503a22520243d05201c4405690310440e00078036080f44030014854000e2100c1d048900954031074083c0322503615070910078030002d0380842c0072540a020310303407035540e014024101c03482c1c681c100022040c414014071841c0d03030095800ca0305104064004c01c800c504100101c02d03000001d606042400d6186940c000c0e440304c0008102c100b1000400d404850418402c10010703000c0030606003565a01d0351100d20040c11000314a0031102d0144020001c100070381820703c0c2c21446003d03002810f01c1030480c29140c0714003611b4060001da80c07103502d5894001c10344412400 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 448150332 1250 448149082 448149101
    0x7082d09030c031b01060807120618120f17070906050c0a0b1303031505060313020f2d0a03050c06031b031005030f06010e06060702011103030405071d0c0703030e0c04 73
    0x144c4d4604e5003484009582512542e410056003500719940130020721204221510141e030340500c01180103a9011250049945016005429035008810b070403141c0f50000d095684c90702c040e686440300340090075002031500398192288000a58000000c00901d0f2103903000e070001100c070342c0030388004080b00d4a131442424070580b14125403c2100c80b040e003c141e00741c803c00c0c18072103d0580e04044540b0702030000e251408020300071210040744001e500c0456994451581007000004c01010350020083c036071340301581221004da904e0300b40000c1603a046141000341002129403000052551103081e500744047c80d0006803c22080d407464082e04441b09943d0f00c051072061160444a001c080d20300000c25203080201d05000358290407000051001c203922080d2903a1101007520050307500c042e6840100d07034040300003038864410700010003448100308000c15000121080400042c0e01e0103448000310040550503a6040400e101c100000d800286c0039400c466807550031281030b1a0420303154000b01d800c1e254201c0 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 448151582 1250 448150332 448150357
    0x409050d0c051617070e010e0105010e010e100f03060504090203030d09031803050d26150604030c12050c0105120a092108180d090506030402060f040b0307082d09030c03 74
    0x189841c4e90701020050440200341d4010819403c1d49003407450070120b0011f01030103041101d081e06448903179003c0c240b201000740c0d000c4d00e424002150318000500c00b1010021003000a030904100284501c2c0501490f501c882e00200910310b03003142c00e12300600400030800c0c12424829a10f4042020f102d98249290066000d040901300301d100500c0000e06031400d000329508442e03ca240310045914034540c2c5207510590040401c0500d102d140c001924a001c0c95000030003a00d140e050210340990999406a141c5204e45e007100c000d20740810042d0303114001c2503186500400c0702c1000130080d1006420075100d09003c2c041c03c80100601c1d066030030341c103461042c4030000300311550700340a4024011141100c9008002c00038100c00d03101c3c00002842d10030342c2c6c4100c82c426580880031a0555840d0320846445000c07000d1860307540c1d5034038405c00c1800d42080707038280c011a0020300010007072080c000844c00c84c14103001074050030340c035500e1200750740d50800f03002c5040d10311042c08050116034040005154040d00b85 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 448152832 1250 448151582 448151609
    0x920030901050a050601261b0c1606030506010f0810180e070e0112060207061107050a030e03030a09090507111605120726030d18110409050d0c0516 65
    0x103c0c0c0821395002400c00f60400c00c0c104020100118030314003251060002c280240c0140e140c010800e42554080c4460254000b030001c0c00c01c41300b05001698400540c03012000840030355450005800f250f5040712902c4c04104042140006070380318665007503100b24900110b0004c0c5840701940400682e0342800000d80315602c500024501c1c83c104080b00c010a03081e9104040b17581043e5080f55640d03a082001080c060b00441c0140c1000400d0300f2045a5040c47c2004c1034840c0e00604009981d0340b078603201540818004100d154050802102701c1c4e0000400342c440c0303440640350114180003800000d04450400518004590240c441440f8062420202c05050000e030307420142041591880f010b0070384220b0f03120910030422044a00355000c1e12600ca8007071070300c2a65040f8101d5046110740b0481e092860701d032210710480484444520a002c5000e24111042a08a9814042118544a07000e402ca900243d00f480300f0718403c030b0100b440c01c0c4c89881230b14801d0a004600d80b004a010790000036004016 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 448154082 1250 448152832 448152841
    0x15070306031b14010c0501091a010f08151b130e010519140925030606030c0302070c0b0904110304050a050c2e091206060806100807092003090105 64
    0x38014406100070030410b290301c01ea45014090341003c8200300002d8140094140c081050180a5000004a0f60081f12510b5410040102c03441c841c8801d00941d03400e4034000e031012411a0300006c0c50f40900050728142c802c01d442c1d510362034a032041e130b45410901d8144200034407000219000e0484d001032051106066155042104100d044495140d03c1d04452214a07000c000c003005010045009000c02d031104c200740d44880d888400441c2900201c03114100103089101c1d4920b505621000440d851940d0030010840e441c80102d040c2e210f10300b00600b0070f220201042c0700e28403490006000701d680050000816540210440455810480c1d0030382e22500901140300030b104080c4a074984c09042141e12004140c0d10303050541c900e841d850300044055903800303900000107002c1c4106401801c2d0701d03828551000c2c0700e80742000103450b490050407410b0041c44085642406d040d540c420582e06024050516641000c0144005010422080180c044072201d1401e0b4401010b000314041d407100d00001c1050b240 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 448155332 1250 448154082 448154093
    0x1050703060b0a021207080c0706180603060315110409090809130b090c0702130e0d020c0f0109090e160e04050c18040605040609081b070b0a090e07021507030603 71
    0x146601c1210403080070450500c0196020400707101783d50858500301e440e500c450074003480f070340101600103150f4130072a00040790036a045144078080c1006070940682c2d03161582e001f107003a604071340700c01481d1a64a94044e14032003101c4e006889107900000481c3e003416995905101a40c0c0001e40c00e40380500000386050046c203000110a4520302d00500c203108403090000490070300100142110501103020568008550320300b08030740704d08000400700b070055003170024525480d000a106020058892010302e03100d203041410340c40804400507140c60306014a0669540003400c1d460031030310342d240203401050b1500440303403080001030310041d0301601c80b5240a24026241101d0b40450a101c0c40c0340c500c8081741c4580c01380341142d01590000010071913131501d152074406415100d1005243d14000310706210000314420f404515082000c04855005940c1d400715101d511900d40d82200160a6900501891054400c0d99070402524811121400407040c000520242c090780c4050019881ea04104240f09 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 448156582 1250 448155332 448155341
    0x60d0c180611070e01050604030210020a0515010e1602120702031e0f060703020c1b040b040905030c15060d020415080d05041505120f19020c070503011104140d080c0f01050703 77
    0x444039071301e0000355060000040050003a4403009100f0f0340203c90003170a892080c0079402c0040d51000440d0b9800401e80c3c0b80280500003401449080c00c0b0721000141040e82c4041d41e501c1440064015003507240368000480c126030f00200040e40c01d40f041c42c9641d20011000c1c46184100c00b1080080c101001040c01d05500f040d101500d804201801400803e0345a400480ea9409401c41481c044003ca4000e0010801810074000050b502c646048010418000003100504ca030001c0c41d4161443d1040c20600c44000410658000e50000018200d2000504007a80300d00403e1703951861a0140654918a480ca002c51082c2e512001410119040224031000360b2505611001c44c01c0c0b81d41443c101c4008802030781c00003804000502903483c042000320382c0a86560801d031401d8207055650300301016401e40c2c2c0e0206882280d0080d031918880c01d101242503019030301641d22021001d00307001c41d0382c0c040014140718003000760b40407030003005440352100d8200f002c10008c50740140081120701d8450f40260032035 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 448157832 1250 448156582 448156589
    0x3110a0503090105030a0e0f0a02010912031e05070b151801031a0703020f0705010204080d0302040b0403060e150103121101150e0a0906060303050403110f060d0c18061107 75
    0x56004060a800084011040c0c070b01511082ca840343c2c81741e9a8003444005490403094154a80c090000368220301034020882c003400358001c0e00ca4002c03042d5244407c081c40801014050002404000b00e00300c030b4112441408241c400b646410707800c200b502d4482e0303445054241d0300040e07102c410341d69450712030a181800c001d0604400100d02c1c000d615540310b41c0c0200d03401f003016440c3c4102541c00281c100c0d0013036065607a1283c641a40c4e680313410403850080d000b540603000b01c072040d12810300038a8409109000305c6056440401210742042d00d1559110040c01c0580e070130031024055440444d00024004500c14021805101007420110420350007a05031300801c25000000e9040090f001580301c140c0e41a44121036100d0420511135403414003440081a1440d0014117941c20000d001040c168001c01500640f07004104225541d54081c04000102d40c00c1486503030051020722095040c80080c4d4042003500a260070b00c11842c41003100803085180c07698124201107010a4005100c01d00c0400640019 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 448159082 1250 448157832 448157867
    0xb19080f03072103060315090b1503071505091f03050901110a0c03122f18060d021e0a020c1207030b090f0d0807030e0d0c021c020d060903 61
    0x20080c031034580e08a084108015034100f907000c041c402c840079103c1d0303204070011a0440e00d594003007010b1903c420050710a000007511850b48610100b84802d844241c0e02c000010014009c140c0d81d450300c40300c04001d00d40038840c1c00a11805020021b65500e5041c0200740352000c000c2c002049102c203078805001c544001e82010866803500540c402c0400d000d100312455442c903421b0111651225150858400d04d03003210b030820943c00d03c0602c8010007416107003031144c401052010810071840e540301503194001e0f80c000003890452070020407110309003071008100c91303c2000009850f00e1850104450002280e00c440e400000d030004001ca10240d044c0420072841d0750880b8481c0f845080107080c0c43e0350345498000506400841c0c0c0c045030440c242000781c29490390f052010b840543c3c0c0c01c408098900360081350560046400c1280c2d0f0301207601e002c0741050000c040c1c0d450b0b03195694a84c5d000d20000480703c11055071010000e1540d034000d40c4d9a2485003c0ca24814076000c84e00258502e0001c0410070465840010b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 448160332 1250 448159082 448159087
    0x507030605150a080103170f0f04030212061e0604090f0b010905010f030213020a0201020c0a060c0f17151201110714030301030305030406020d0b04050106121103060609130b19080f03 80
    0x310f1591001415044a411140300e1015407500070490b03a4600c00c1e148211000d40300000d210340040b0303120015004890088420889008940d88070070707103030304003103d0048001440041a009201c01e900f00c464021030041c00014004805954100d00082e0114060ba443c040c4a001082588a103004403405809078185c4100d070a45141e01040c0310f2000c050710b00c001c0781d40100d6002041d0b8400d60649044076010340c00c45140c50683c0c2041d0f40182181251140018460200034180300d00400c545d04501c03840c4200010596108202c210140804005a59000c1c035004120701d0401024001d038800159600c0d21569101040d1030003903862901c031862000c40d40c1082c4010404a5000000e5a0340203401140250740c9110107082c40300180030101d0b540d80e1142c981000070400710361042d02e4038400c00d0001d00400422000f0f191227080e0f800111078140d8003940070031120b003c606140310705961486100e0400305000058038006182510003c055201804030082d0070804000b08019081d20b415810307010b50b2 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 448161582 1250 448160332 448160347
    0x50f0303090904060b0604170601050402070c12111e0906030c010915140313060b0f100e01030e030406050703200601090e0309030f01020a02150114041e050703060515 73
    0xd48078021003000c54441c1c51800c0000f410300c8000d4002d000310203801455103544035221000e08034418003d505514440c4140300002c2124146407085400d21030300203d40200032480c0a1805401108682084528800902c0e526a0944407003c0a680c08078240ca41c907241d40c1141c50034883c003084002c3c5500d03c2944a4804004666007124540050703600603001910175071500e48041da01883c00d0f100040e0303054070000403c0300540802c0c11840c4514801c0c5002d102a002c803e080082100b01c80082640c04069074408030056401402e4480441070181004605045002e103120b04580082c0d1000d80403410000b40c8404165009040420b4407111076a20500c2840309190f15a84610502440d469683c3d40c03180600150010829540c80000c01001c030342d00d00f0703681e400603400303074001800050262103189101c0c1c5a40d60344081c0389041c1c410350450300c14136103075800030040900745c800003108120040d64185504032074107009040c401c0f003180d00d02084080ca40010b1122010715840c000c01020000d12405 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 448162832 1250 448161582 448161589
    0x12030702090a15031709090a021810030e19030f05030108060109020f0f031611070605091005190c03200a060e0715030b09010504051308070f02090a090606050f 70
    0x1c6800a000d02030004203000c034007801441001481e04007401d440b180c003400d94101c001c204010f205050094030b0f1800c55031903840c84c62040c1d005200600c600c1e1166030002e000b46013031030210550f030302034246030102d0b10f441401840d509240152030060405016054907906240c0c0100a0000300a01840e040c1d182d0344c500b07404292140700601680103045d030001003142c2c0000300c032801d4030201e01105d120603941c1e0510000d004a1400e15022840c045140082c0d1202a40c6011424800320b82c50743c1c03565858101640100800e000000720040c3c20711000f44040100c085010010508a204e00d031182c0c01c0f903e65a0070058506643c9201c10343d80b8ac4011540689101c101144040149602400200701101e03100403050405030303541c0000d10200510403000c408168150060098580103440d01c03070351642c039072061105880b01242c6001c05d41c482200c55a0014401030018911180548a81052181e45500056804a0580703603110525100c0000006000d20b81c0301700001050119040d01c0850441c0002c07 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 448164082 1250 448162832 448162849
    0x270b09061302281502010222050315181c080a05061c020112050a02040906170316050115180e01092111010203090102070506010807060504090515030109080912030702 73
    0x4845404440011180c800007242c003420003030000350507001c0040204c6103009000390420900c11200720414130401010260f48070114058a0015019101e800100c0c0680c50405502800c4001100075103203048100e5101804405501040b80e0391680140403460070040030710401502400789240303041c05201490380c07101c1d0842c070280300003011924440860300042e180107510440400d41a42072604119191400e07a00400c190b034583c5804100075900d404030000c18920b00c003800031349a0700c200900c00200f040b0708102400588200c0002c54880c8811004884281441c2e0004441c40c1d0100c0035022101003901a200146401030020082c400c181e8881c2c2600e9220300a10480c0c6401216030341c0e1034280701d52419064580070200a55a90410700100c0c5d0007907112900a0b206405040004203280e0030101d225800c8605036a62303d070502d420440243c008100242040c200195480c16107c0c0d1a2800c1c051458401d014171034070b80d21401460140080c03002108041616030f00200082d200590340d1800 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 448165332 1250 448164082 448164109
    0x12010605041d091603051f0e0304050603130614010302011403070e1e09090a03111609020a110109150e03041a07022103030415060b070303270b09061302 67
    0x12451081d40f20700c1c440760704010b00c3e10101c4002500c03400d0040188080043e00c58100040c0c941d207034507000b5450040c03200b1180300d180484d00d641c1042004001c5407078100051754100d1010451064000160351b00c20302102c03400007104c2c000c8a03080c0010025580c1092048000502d081003003891860038003030080c280132202003450b11071001c210030f2541d82e0a001c0d034070b403107035000c0580f0540e490300b030503c2d0746076490503494000c4001030b40511406605401c0414044200316141c40707e50365850400e003e210107508241100c204000c0d08100340f0401503403d000d401e01c01c5004191034400d485160741c41c84155900241504e030313540e1042108200803a80c41020740380d4000e000c2d0001e81c65020078400102c8000040503610b002e4805c00c600100c0ca034801000550007544241c00d01501c039024040e115003030384c0141c0b1486889901c20311917040403901a8020311104605000c40040c046e410309041060048015010707101c1d01080030030840e6401042110030f8000e9003003c1088088540c0e540043c426905080 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 448166582 1250 448165332 448165379
    0x5010c0210030204050d050102071b271514011202190c060207020414220b070f09080601170609060c0912100216020405060a08120901021c051201060504 67
    0x600c1d048414071940c15280900001416010107481c242031a40c045e42001406079180040c900c1d210202c2c40382c1d070304004100c80d4001c01c403d03048105c451070b04003051482112515401e440d0610f50070000c48050020000c0c1803140215900b0521181c00103046010705046803a907144104034519214200c075a01c0c2003d00110b18110011a2035403628a01038051a24000e410174242a101c60383e040302c444044c0d2180c5c030070090b0414003001c0408607000e241c2e8513041c064050b08076000880d0149114214091544019003000181240d407556400c2c43d0030403d900511a9104007000160303450010b000c500c0c0c00040400c014080c03402c1094040f0024410030b5202031080182014034541d41009102c1c889010503250800c5444c1e441c0705600c00c0040c442210200c4c452031400c00010034900e403044079507041d940850010008075107218a1007845600c5103007900d0540c81003007406400d0600240d0040d00c02042035994644480b160aa0034400381010b820400a2050510003032055084160300903050b0400c06 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 448167832 1250 448166582 448166599
    0x213150f0e060301090b221a06011115220b10050a0b0c0d0315080a0f02090106080f0712090203030301240915030b0f061306021207030203120618091501060905010c02 73
    0x1a1308038003507800f804400a280d01101800080c443d18403164231807281c8400e0320380425000b9540040303601c079003042100341d02c5080940c0114180d40640800420b28840c514800100b840740340d10340ca040e03150122501d4480400c251418032203420408001c4000308503005699081003580c6281030784820020f100d070b0042594858411040310880800b8000910248080d120340c0312280c03c11580303007100707814103138060320007a000041c4141c410000644100c182c07840000490b100c200c0203c1d42c1d03603981080c00d40910b03100e4400c071025030b406100945c0200052007401e440002c4002113400b00c10350079902e000501c000c00100b08881e40d8010300215034011a442d00054030303580d00e00000e46a44405600035085413002c95513003c00e0103a480042d055424a40803650b560507840b00c101e50a100781c5100a0040e0000e01005180e1740d03080600070b410130300080021190f030041400b9200e0100e01101c40403e03682c801c0e00000c25107088603079064050142407420030304007401e00d0300180520f911702c6802800794181 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 448169082 1250 448167832 448167871
    0x4030c322a03011506030c1403010e041103280605070c02060f071505011701060906060507150b1009090b0d170307180f03030e04090f0213150f0e060301090b 69
    0x2980414130b0300c0b000c90b1110000796211000200108203841c480c4022614910003101080300781740603030f8101c606441500405640d41d07580c10740c1112403840465010712403040c2190300d0340c0215050310050546200c1810809403039060680c04d552000c2c20340414400c40c1000400583c5034142160a002024015607550b1845450070070720001c0e00c10750b4844020718102c0085004605418030000441050000307100d00c90b10b61401d44200c40350751040c01c0c04550104006000580c04031030f0243c1e6040514400252031200c40080340755a44900a442c0010301315010031701602d0007512503006107480c15240c11459241d540c0e1005044034241c5201e541c039120100c0000c040c07501c52040c0e0000d0300d981110042e0703c15070f29082c50351801d090340401c60200d114103d8a400c00d0070030b442038030706040d000028558240d00e1a020b00c0340c0460b0724100441040c0d2120b1842c508100340101c408000c004001309459a6407420408000001016003564400d904187d064004540c182d240aa000b03004660054500c080 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 448170332 1250 448169082 448169089
    0x112030c0c050915040509120313030c060906060302100801060203160f020a030b150616080309070b0301080d08010503010e06041209170d1e0504060804030c322a 71
    0x105588a25400101d0310304001004013001489002000b00355000c1c016900c42c011000d8813030344402c941712402d03076050001500e0038000d01c20308190140030b8100312061a889840d0340050768480300703041d1501502ea003420000c605040c9030203941060140b81125031541440341c002e440c0c0c800c00c6000511310303020318080b40c2804600030b080e0130040d90007000031000964a10380032a0107070040350b15107444110355109441908205044070007440c400303142000031103019540d006254001a040c0009031282c80d40100d030031000400150b0103400074200405011510840061001405070800350003641040042c810390f00d400035410390030603400041580800c0901504580d4a210307503211606410000400589103400850090039807065071740c40c00c52440c203400080000303000e0300c2c00180004500b00420404103100d9034a068010b48246040000d0050a031203004603a0b082d40c4151075040d0364807200306034468081e46841c0d8140171540107071522000350030824400c24025408040c5103408034410851654 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 448171582 1250 448170332 448170353
    0x150503060a05040c030b010206060a0315090507080f0a121407020409060f1404051b0a060509130912120e031b010209030d0c0c0603021905071b1d0f0112030c 69
    0x142040000c030300d1310701e0010064615125a240503020710400301d0883d042220701201a80e4020801040004541d07804000601100c1401e40e56405181b0000ca441d45060282000e21b206640c020300c01d60341c080c14451340381801d0320040410701c0a04030303009401d100b026064452039901281c0000d100c141e030341001005456840d0024050f41d191502d0b003021203040d601441e0140707001d01c2c100c50080091402244200510580860380061130160070456144560b000348078042d00030707117503401300d540340b8603c002a281d01504c00c9030003000342d64091a0321075012060b04484e00e190f21b428840204005030032510382c4030341e02910b0114110051055104a0250102d0f41c04034006000c0b1804580701c100c3c014041d0712021021070b210344031200009005071080c025200da1040b0506040502c0185420030360b00d81e449208100c03411881103120341c00c03020002d0101001006000710881b80078598810030406064018a0000c12204240c018807c41004440d441e40250380341c14041002101410510582c0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 448172832 1250 448171582 448171589
    0x16051c0c0c021012110405060f0703091503020403050c0108062b020d1b06030902060a0f260106020709062114030c0c011106060d0b0712060e100f150503060a 69
    0x5540040c0c1e2407007030b41e0004000200d40d4140d00100b2600d805d80c03c00c03c400384294406d540c0e124609024041c2003c820700e0051604910900b441c5051715510119105d006286561050100354041001c1051042c180310000b481c500900e8401214a000000105003802c0f1f0448040307114081081c4003800552032603070b00e01d8190000d010500c0c030b000381c4c6048041710140803201e149184504500040303e502a003d0200d0181e4010100c44c10320080c0302c070445006103000c80700b40070021070388001c0400a1032010003800985181c0e0f0302901d40e606144001c0d287c100d2a83c0f20100080c40d00d1001c1000f8049817015900d50389061140d01c0d04503d06050a02c16842c140c5442d0b44580800101217500c1000010348a045007000c0e02c440701520a00c1e04115100c00b011900150401040e6a07950005183d010302c0c598080d4032402c1c40c51a1242441b60300741119800c1d04041c019030340c42414002c0812400711b00030010b2401821000b00385003441b014070075140d0522100001d0000100102d030640e80c8041907100030303 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 448174082 1250 448172832 448172839
    0x70201020f0705010b0a080d05070209100e0f040507080a02090f06041e0515090c1b03190206061f02120906041d100f2304020702040c0816051c0c0c02 66
    0x1100b00c0b504149008042d41c000755442143c0640000903460f80c0890f805941c05401d46519040c031029400340110ba01c4000c0c00c40c0c071409600303107000c192109201406801040115000001880d080c60710034501070440d00040c0955001c500c8481c0144d0319010303201d41c00f16a40032507084030788400380800c0c013920307400cbca080500008800340250742c2041d07540b0040c8101485119070501043c13446c1801040e0700706813188a11000100490221600306c0040400804255402c5a00e0421945c0c0000b115044c02c500070300058100c4000c0c04158607055159141c00c95000790501d800b030a051a02a5440000c40c42e5400307155800708000281d50384d1141554024014080d011580340c051044900d130340942110b4042d000300f89444041390784241400c041050b41c1401085681150342c0c00980c080404500707440641c071613020040746c40103071502c1c06800c203c6000c6880342d01c0241461240380c0880d022851815040103403d00802002032044070051550812180d800240c0410324241140d03450883c80c0041d40 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 448175332 1250 448174082 448174087
    0x140403020303070201050c07020604050f0123040302030105090f1e070e0f061306050109140a0f0308190201020a0903020120120c1b0d0204020f1e0702090619030605070201020f 77
    0x149a0080300641c856070059000300400e9031000d5084416020307103000a5004002400309101d05c1c2007000a104040405040c00070300d000040c40090380440040b036503850046004581081142424010107411110310009040d0f1580580314907603840031b1041000c8513145848016400c290b40900440014100102504081d443c3c040380c447c4c2c40686c10380e00507000707a024070041190049140b00711000c0e22030503500c1e103084a1425001d0f50240d0154190130754040b55401002030100301d0041c1c44030085126184054441d414901c0e250811a481040402964010008001a0355000e0000c106403542428041c0c43d88000501c002c203201c1c111101c03091203205150801280303100d490003516222880e1012184031110045030b202d81e90454008458214115900301001440c061f00908214204020203a007000c540d240020001d008090f0041c4144200048070425400c000002a80c4a60240c406a0300340352250030102a407005448082c0400350f80b40b0216a486200390101c40300f0040131150143c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 448176582 1250 448175332 448175341
    0x4110d050f06071e020604060e010b030a0b01090b06070b0a021612020c030d0302120c0904020c0d030b0906090610080702010b040c05090a17030d02070516060302120c0c0a021314 78
    0x9603500302c01d49010340070070b01400c3d2246240e1001c0426103070b4115640c1c098001e1b9150703541e955014082c0c080741d42d1050754840703000400f151000c004203800c4601800c0000140d500d00700e88403085486441c2981c0c00340c80300b004420302040c505210342c1e800c105840d0005030f403825007101c0458002c607811801050203602d0741c0040e04869002070071070b44950040342640d0200d640c2c954107030201d10811007e000c00314554000180d44044a4010b40110100030300090714000311072240038100b0f114144c0307460100703079203507060045820884100c41d804202511180c026041007000140441800003103103007048030180028207400c0c400c0d08200b1200c8400b50050110300444000a42140c00200400d809023940030400074a100d1a180b041c0d49245810000d186054020b101d040040d5110202c240c03268800e030020b5007128203410749131400610b019600183c481c82605441d0800b410017a0002d289802c0a010b040341c0031201142c92403a06604a80003c4254056214200070b4410886d0340d411850f030080400 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 448177832 1250 448176582 448176613
    0xe0f072102060a08132f09090d110f01060b03010e091915090606180e0312010e07050c0601060507050c09040203030904180c2705010308030a020c0f060a0c030605010905060304110d05 80
    0x10b681a4a801b80f0280104200c02d20040c541c040310800d1003a440100c0a03000d90340034100c0401011a80c106403045016442111420343d141c0d607000080e004800801001103508628404d0b07081180d80c4080c11040d000c10260403a008051840641607441411402146071103d0307002d802699031101003402040c0c0d03280250302100f2400d03c1cac14070300c40b8106000582207100200c02c80f40314a40020034000703240d00b42004c0c444955801084181484002c110540e10038030304006880c0244115550683c1d07441c498940603040c5807100b040c182c0204440f03018000103079408401c0d80e0702d00405031000146184c04481700c01d8032400480e400f03000780c941c0100108542d501d9104110380015020099246515114664001c540d000d10010380701203424408107190382134a4000b015401c01e610115001c00c2500d074030640c2040b400b030f01c0140301d05544a24450500d071f01402b940c4000c1009003098440203240c0004212588002070005000c0c154064800f101c950b40d003005202d0540d081000c0303d0b011002746102 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 448179082 1250 448177832 448177883
    0x15020c0f010e011401050a03080a170f18030a080708070504090e0303040309120305030a0c05071b05090a15030620030406140c04060e01030f0e0f072102060a0813 71
    0xb80903a035400d0446541d025525012600d04031040070304040c81051440e02e50400c1508000f41c1442002070110b0341c0f4071711100b5040002d0182c3e01c0e0680380d007018102645000302d245203260b0070002a030001e20402041c90380140c0102c1d441a13050600400310390b07800030700f16414851030700303d6042c03949031100503000070f41d000000e148114030980794814500d0f20352003a247c02005150000b0001801080002c134804041c1c0c10202200b0300d103041007030038241c5581d1843c0151400e281d200034004450203007041186080e20304203400811110003000007041c80c0d401d84404800d5408042e15098450400da0a0103071030f6900480145000d4917440c1d16402e06181c03100c080c0452280d100d01141400000c1404000340300105c5046034880d8454a00f40c00e03c0d180150080c24016804c041c0041c0d50740716840c09600c00340981c101801c02080039149043c1048103842d03c503010015890140d42c800d0b0041c0005880ea0012a0640c040c10700300f0308440d0b980c112881061a03030081c8000e04d400910015400116840d054 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 448180332 1250 448179082 448179101
    0x20114180405060d02030a060f061505070b070503070c11030a06020c030a0207050a0f0e13170a03050f090a1709220e0c010915030e0118050607050703050715020c0f01 73
    0x702404140c40714401c01101a45a4001a605070030402600001170f02503030050042686c031186c0030071440e03600c1c0c1502c841d950021040a0100300d00140c09400c000700e860001e80c0c44610303810000d080d0300b03241e10018100700c004e000060400102182c0018165020440084050760100041d59555075800c103154980c1c000d50801009032040b080003003500d1501042000030b036165003e150210902e031203900200114050700c80600c840b0603003640c0000c9101e20030708d4034038501c10001a507514482402c004084900052091141c0c0c415641030240c03402c07000c102e01c10680d0308901d00e114809060b02c0031080034800e42401c140d0003403120b002c9c0d0100352030460010b450224200001c110440d8070305102070720f41135869a001d00207804d401060200c0030048007062003412052800140c2400109078040c03c4400d213145220003920785041260810104000c960b43c4118280340244c02c03c0280c5c0d602624500825000810b442d0003c0f010b0031a02103aa410380300c00084030f0342101c404250071020310740240011403 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 448181582 1250 448180332 448180339
    0xc01020607021209060904021603030519020f12040201180617180c01110a06020403060f1b0804060b1206040c0305010b01020f070b0a050f040311040c030b0d060902011418 75
    0x1000a012940045882008016200c4400b440c0200701310411a1a5000394021507109600781b119040342803c0042001c041031090300c0010f4542040741c0300103c8100c50300e882050590040090b00e4000c00e1700000d440758005249003041650310f9510050b0380c142c41078040c8000c292a04007001076010360290840d134210300480c58100da15142d00c4840000c5202c0318400030b01030380c0078800101d5031f548180102d10080f400c07541900c01030360312642d80342c085e07030320650081d00c5482d12244540f000010f24420611100c03100c28890402c04940d140160445c40010000342406548000041458940d180c3d55220480440242c60113441d103803403c116203407407901098a4561805103140c0c0c041d40001400f030b00c1807180100602015107030500c15815544203803014004c204051015010002c1c26401500c00365110b4403042000030a89030500007200d0741404101d0404d42001c01000e030b60380700c106907904415045032011510300e00a00050769143c10003010f5050090f000241c02030401640c40c2c01d040801c1084 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 448182832 1250 448181582 448181593
    0x3030f0d091505070e010c03021507120e0309030715090b07020d0605010816080c0105070f050724020d030203042121090611070b0c1612031a3001020c0706020c0102 72
    0x40c0046a42a10019000b40940d01c100da00088550302b401190b83e100b83c1c5450604114480c1d541250b0956510110b02c51441d44045118001e61400707100400150864106040b012098080c00404410302445043c0702c4490006501095441d84020701840c260030003028040f44d40c0d04d8100300e0f43c40040c1400319550394542c0d030001c10a900080780c248900a0140d6865081181e2503c0301144241c98007000c035801d1152610004801102c0f0884e401c42d11458105030103801e007108030183c2011b540000d41002c05104104102c000340368070400781c0c031580c2d41444081d0308007a0b046064480da40440b40c0c40415107100c6400342c1112440e0b41005941500c10b40040c4000454038060f10340c24001e00d81c00400305103510b4000340b40c42ca9120043c01c51507500800401068045803195100b1048030429400000e8aa144122143da0702181c5000c070760400307580a842c08040842800c0322005400900140340340403490250300303200309406444800443e8429034030740e590f0780d050180d5614030a2243c907001d401780 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 448184082 1250 448182832 448182857
    0x1e0307030b0a230301150308030601170f070f210213060203071e030917060a0b1f03020c0106050a120303110f070b0c1204110307090b03030f0d09150507 67
    0x1061000e81243c3d8284044040c2d100752a100e0074400e03941d900d4282d0190b6071800501c095070b00400d1500b0040d8046c0c0d0744c5d280d59040040005015007042000141401031000901c2042d01c906141c01d0380c040c140745041091403489120444411119645208451802c3c02d030360f140302650f5a0003025001107102c25088000d9403154103a0701c80c01140c80150000942a16400c0100c0f5215504203171907219150035075441c3e4648240c0301c0c81c496000709500e03043e0310040c10002c217000188500d410000c0d04468100010175451340c2c1b001c07904c6102280c7c0c4101900440c044814080940000002e880000c00405480d070f1541e01920b0000782d495000c1e0002810042c0c03e8100021040c1210181403443d10194640758141d04c540036000409002040548000c00c83c03003c459040c105018040c510031401d802c1d8004d5250101441c00c41550802c054207454803402200c0f507a070000c101e40a41010040d403c5c0c03150721400108004040c443c2c40039001c000c0184401c0d0f619000c2d507200b18844c0303c031a201e91803480039 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 448185332 1250 448184082 448184089
    0x71a37030c0f0818011103041a01060804080d0f06050a0303022b080a02070201090b030a0213140a1e05030a080a14210402040b040f0e10091a0405031e0307030b 70
    0xe80e0740742ca0000c07079680004100103001d542c414001441d810030000c00c10400041084409900884090751107101301107820800d0140401180e00401c400d140c03000c61810140c807601502d03c00c0d14003880001c0c0c0c0d01c5600c40c11002450700081c2c000c11005007540381d0540e0368140a0f4481d048460040301961044942800905849040c1d02030192103903100091b55071801c1413040203600160b0240e040c005490030001d21911103900071841508074038000b58840300000c040f001018981d8009841c280900c4400c000d0b035803200d1401e1001c07540182000702d100c3c1282007032207012444a810942e014010541d1100911a01900610314603469580d44491074030740182c1d00880e0f02400c4130b410340101c009071a407a1200100307040381c3c0d04a80001c00c001038000c5200c000030304030340d0030006024015407101c2c6420003c40c028040b0f601e4462007070f0b2003888114041d507030302062980c2d94817800c0700700445040450240602041600e68451b84407144401d043c2c111107559140340c000301c4040e80002d0034804108410300303 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 448186582 1250 448185332 448185347
    0x8010e041b0611101b1202130b1207020601141e0a0b070c080307020d0609150504152405011b140c0406050103021801030209191401080603071a37030c 66
    0x660118520340305d241c00c640101c0e540c1e00c0003850380e140c0580911800010800507c1301c4002010300c60100b96079014030500e50301521600411130310940d0030080040010007441855480c420404403a042d040c41500b1903c1d08074038802a040c5034206020101c08030f0000400401800c05900451440b111761340d981e2781075543c074419098000e4100580307008002c000381040d0080383d2200d105194200001d00c7d500302c604201c900840b8240c46160410501c042d440000703114400710440100e1000b41708407070340507884080c99200e124040c1040800c3d040003901c141c040801840f466800130809401d4605c10b0360f07561396032000702e0a1910984c982000010150300078400c46864030360804160050303991440056000390000107805402180801c00501c55156280f4200090100d4041c144043c2c05c003140010102800140703894020350040901703000301c00d40b02040c0e841e00c3c240c0018080e40e40440d4401900740000c1d00c181100b241c00c000c80088041e001102502440c002181d60401c1740324600c05048170200f = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 448187832 1250 448186582 448186601
    0x21b0c19050904080f280201062103020a080706020703030b31060b120108010609090c090513060f0518010623060c03040f090e010b0108010e041b061110 67
    0x404045404200740e04046000ca540302d401406014203101981040d142c0b654080d0381d496980805035000280109840011450000c0440c0f0003041f40c20b04000e0300100c1800d040000f1104503401c0d501c1202018400c105c0c000b8030b103030f10540e20340c1c0b580003510344240607400c03070b44080300486d0400b03002010500701041c000b56040b8030400c2c11814150400441d40758801c0303400c210b00149840d440089400c03043c00b401000d1410350011480b40303540c50300780c0f00350031a1200d07044110502d040c03d2051b0013042440e070ba03280c02e9071550540000e0740c0d251140320307149420800e10000e10180c1045000b92010010b0341c031103032084c103000780551020301c2040c120508031000c50082c904d0124000a28101a05c3c0c440b9500c500c02c1e00c0030740880c0c541050204500c0c915003259000c0c01d00244500002c0c00700403114051003a54020300700007444100203140029003001014000c482e04d5034401da001506001c0b20251070492500400d500c148900c4c1c84800060058284480c3e0b280c5a10071000c0c05d18404080340b04c0c540c042c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 448189082 1250 448187832 448187869
    0x1214070e06030a090210020f0606040b0109150306030c26060712150e04050102030610030b0603130609120f020118120c15051504060510022806021b0c 66
    0x480d03520400c001c901c1c0c201070440c0115960341c0b5010310050311464100340c5a6500c1d90003c14030306289148171854242d0040005018600b007000311810b990300030402c541038a9401c14000c00044030010114001c1503d80c1c0041c200c0440341800142d110641301c100070f00c82d02c070180180b039003041d075082c0c9590301c0c1000d64005000604118a60818010f8bc0d4014400300c4040300307045821980d20081c0a82982003928140c070b059500000b0b2080514000030910706032401401c050100c65040c070001071071800001c01d600446222240c0ba202001003d5000e21400703035100c0c50320305401351401c0005243c0b016a05101c0051b6190100750540920305d041c03001c44031030f844a000e403400c90520000710364800104004440c041c1c2c0c05011031a04034031500690384070b8205a40c2584081c6580410007080c0c5056a000d42d0003801090440c40480743d0219401e03d205500002c403120010016569401464040201074110b510210f0345000e0710300a0500741626400742c004841490480c0000c00007a081c446080340d60 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 448190332 1250 448189082 448189097
    0x100f141f09021b0307140f1f0b06090315060906040b0303071203110408060717011d060102030c070f0e0a06060f080702030d0c020d110d1d030f010c121407 68
    0x1a508035002804184648200383ca50700800152040c556009401c040345d100c039102c003a02c55000020040b100007007030840000c0c0030104440400c01541c042e4050303174101a0362500418841500d40000f120303510780e8050300b15681d0a503410b0750000d2913203003526020f1090502c07c01040340341c542809070719070103d001030241d440d001c255651441c04002d03001a200500d501c0d24024a803401501014000030122080601407034030303115100614160700c480c03500c0000781200c00180458080c89447c010320701c107809000300f8a5250600181e107036004a03039404615119071040030640e00a582d081c00100c4481d180428840c3d04e444000741c6c1501d0003406070a000880355108100301c5440b40490a41298843c0162071600520188080580d070100094402586c08081c12180351b0741d02080441d2440288006448003500f509401000072410b10003c650751098403884011a94042c0101e142c03240e5420000c0180703900194000e000c004c40111120082842c002801700c1c01c403034001d00c1c94030510207a030300c103034 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 448191582 1250 448190332 448190339
    0x90608091504020a03020d0803071209110d110603010f06030605031b0108130b04060204031b03020306060f03100e01151211040905010b030a140c030a0c05060c100f141f 74
    0x81c400d48000304240e82c800f1380240c00001586602e03031070108580c043d010456403032400310f0000c0c003000311a482800b10301d440c1540e880046046400080f40c15202268044490300c8181040400000c0712040e0750307030080002000144880c840310740d400c00c0b1401030b201401034591700c0c4100364030b4007000c43e4070210788130412041740c103591b2164540310741c030040705828440c00110503190340c02c001c1811030b01110704680c009418000d120300054010000f030249450040700e5411980032072384680e0041e101d1405908170082810351907600340702030700d15134805001c00c0080c6255a070304e00b8083d0640e10740c074201c0d10071f280002084030706101d4180550f00d074000f551032401e600e80c0c04c03e000007420f200c1c005031165544d42500751100d6400340008844940100113400c000c2072613603c2241850080d40040f44642d01c0102c0100000d540d90f034103071045410440300c01d40c403018000000390a1a03030088001070b8661a0200e00110030400e0340c080740074605880d076180056503c1d0b5440c2c2c0c450000f0005080c800d001d40c21000c1 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 448192832 1250 448191582 448191613
    0x2d0601081b0d060c09091805070e061503040506010f051008010b160b040308220c0b0903010216050609010c0503010b0d091401090b06030f0309370b0a09060809 70
    0xa5070401a0103a680809140c4401040301c5a8001c4031000070308014082121000f540103103907940c03c0101e020401c181c038503516640d99441c1c2d8418843c01d04e120780c0c00104203690314981450060100944c13940d481c81c1501c3c1c455141c10f424000e03d002109890b038045910306040204070806c28180c1c42d6115681d017848400c0c000e40d0880e2a40792520708920326000001035120b28940e003d540700c0d0315400c0721408c1020360026512104540789a082400c02d804001003404034014100b03c52171120360f40e695403981c1002c03e01920a8441c10840b42c45140141c41c104030000034028406c101d2a0003c00100c07401c1c2c00d00700d90510080c419400001400c0c4864034078586140d000d003000300d100d00450b540c40b09007000c003d400d42d6410602681c451003040204405e43c14180510380c4007821540255251500190006224522101558285001c90b04a00d8806044030501c51880b1a6130400c0d0003130690703640540f101035403040625400080b11031000107017181c05210407900071441d84c00500b10b02080c0c504c42 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 448194082 1250 448192832 448192873
    0x706080408040311150c030d0c02010b031906020403140a17030f0103300c050c0d0f0b04080d05010e090d080108071512020708040e0c07020619112d060108 68
    0x1450b0b00c8032200b003170203801a442c00000c18041d48141e000d517072902c41c480001001c607001d14959100356410300800304d5059401140590b60050541da40085c280204e080c4400240202e0304001c6c0b4105030490300344906500058414000c5115681090500500314070080d134500040c3c84602402020200600004609080c9211440106190310403102003945060020103403000620010510700100c20007130220070b00110100007400c1d5515480342c0c5041e51a034040918030200501510460b101003801c0240400c2118481d1060304424002541c442c0d0041d1400c4a040d0b40d80381451080031034054005000c1d540481c1210003000180c00110720b044900402c4a14a000341d0003004040e8040308100c2c442840580b2034207000f842c0c4103441d141002d41800b82a48003400e01034005002340a44001030b680d40c03080320150408050b503807003080034016081d545000310000a805e1401139445510103100440041c900210b0320710610007181c66090b445a88409080c022040c0c1504151080072424094401 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 448195332 1250 448194082 448194113
    0x60a1523041a0a050603100522141009050402031f0b0d0b0711070b030a0b0103020c061e0109091502130305030a050301062c01080408090d110307060804080403 70
    0x6440303080490210005080b510b80ca5800d5505116420212010f42400c0300c0903000351900f80c450a1441c00e10989003408aa464843c580c072807521120100d8040050302517401c80100b55020038400781c000c00040700c0742c1d6441155007c00400c1003d000065000282c01074901403070b00078015040401c410000e035504418400a1440c086403074540409541c4c86284403080f80303a0144950007440d04100100429843d0030921100641d801044140801d5200c00101e076080180707504005240c03d20200141d01034010a00e103003e8034043c038010448594a4070204050355200c120014000c0e07a241e41c1d0010846840440c05002c44012003000e8001c10215401402403030180c60b800d91180391760f590350b40e156922660b0b0480009002100410640b1341002c10500510140c0c0024120f0348007160130404481d5001c18a5030402003100c02140500601c0d10898140d23000c0074010703c40c50740b51230901c0f00050042c0c0d000315010b403190800c00100c00307202da0302160003a68050001447d00c1c0c9503850f030020600c2c181c003 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 448196582 1250 448195332 448195379
    0x204020408030f0301260d050310171b0418020418061b08070c0201050306240c07061701061e0215040c0306050f0c030109020f0408010609060503060a15 67
    0x200106620704100301a0424000c10100c807940c0b981440d4510303020000290800c243e0307100ea1900c148804d100401d10586035405441c2490f26907503550902d460114140e0f11503040d04100209038140f0300008104401c1c0d00c003801c0c1009000c44968000d0100f11451a00880c10001821b0948001483c141e00709802c640400003c1d004282c06a8503070000302c400c070001d10313222100d83c000c0454016400800183d4803240a040485a1800580000e0f2452000501c1d042c071a135001c0c05c413906003005004103043c402d4552902161a5008201c9460303603035140340545c0c00030411400498100c070398406aa1410b80c3e610340c1d19000c5904003206082c114401920410301507000e01d90005218003103050b4070303910680c01103000160312803440c1484021510042d1064207071b01c1d0048104850a24404110703811600c01c4240141d855820703141411140c021500071500c15400c00f08001850310a54101c030302603507012002d882d46a15907402d20011500d0304011070302c01e440650b50400c015650400c2485020b20030b40c = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 448197832 1250 448196582 448196587
    0x1150206091f0e0f03040509010b0702030c1c0b09300d180f0b0a06050607050a02060c010e1609140103030c02010f032703080606120a0903050f0d2403030c020409020402 74
    0x1040a0b00708400c4d0580c200041d030010030100041c3ca881418180104070328852546007001c03980100351200304000c8603030300a0092041380350000f940c02800c2c41c101500140c0d0b000356410f0501c030160315943d0b8150641511054240401c0002c88a4440c01d40104200d000a61070b080503210038101a000030318107507049101c016045000b048602e03010000e4140320b000c0d812040d1a0180020301141d2079034000c24060781083c480c020000b540083c03481d0b1080d0b011101700b600c50112210850250080041c0c9100900032003d0342042110602905001d503090640c09100c0782d10546a20700c12034a0920020300006d0740c100d1600050f50103a0b000480c080d116150200300028031103000b0040360001c800400451a180c0319010a042c1d015482a0f0032600454500c4d01e0110300b04c0d03a0310007460707015000c5000300750b0b64000b41c1c0804d8050700c12a15401d00d040810f0740c941840420100042c00d84500002200702d140d1880041080e007540c0308010f40368940c440030715561031a02440028080d110040f6005070b400c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 448199082 1250 448197832 448197851
    0x2130e04020a270c030e0607121d0a020306070c0503040b370201150501144012150e0a0503040b09041401081c031b0801150206091f 58
    0xc40c0c1c042c4028200b4a0108000310601140355002c55040c4e2800d10101440d080300300140380f20105100f6041005882e040f148041740d142008024984d03003401551711400d8240c4101c0c0303040041146802c0c14002c805648803076481903825203030100e00318802007050300204800c0c821240140d024100ea18001400c1180c40e065003005201250700b1118500054031080c0c038200a5160f09014440d5003800031200300442510301800602060181d84085510804c0070805160303945459118100080710500209a8a100003020700602414441041050303804200c02042802212903030910071640003010182c4001c2441c50b040c010079660004a62501030840844042082000034001501500344816a41c000c00030820040f04d0000840c0c0391302c494564010440b6950118000c0801400c0704a44c880140c0f4840c030484c01070407080500314516400c02d102c241c1595100d43d206040c1c5078088139030107212100c1c1809982c1c4003800c4030079043e50b51262261101d5040c1c0070302c40075513003040d000300810382c03920 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 448200332 1250 448199082 448199099
    0xf0d1d03030310231e03010f0b090601050d090f030908060106030504080f03040f020a150f090503101104030f060207060e031c0e1204032d0309090c09050303030f0f070302130e04020a 80
    0x81c950840000100341d007217002d03ca8a820310550a200420b2207041080d444100c011070900d400c011301840c1449004100c048a20340541c215004042c0d00c0010b000011007146000b51007070200e40181c4541784920000421400e00900c14a1300681d007024035103041000d104440c250503440140100c868910307010080c40144c807041c1c03241e009015000c1490f501c040307100368002d2103083c1c05000d4408104007910304010a490100304030013040100c0e640410305800302d11201d00a482180e03c0107002c0b403101864001403150a84c050031450348100d409002d214030b10300d0100d50320700800120301010782c2d262840e101651500d600c83c400301310f1004242c882d01a01c4500c400c00980080c0d10039900014603250714019489881604041c2c501040c0028102420076140101007440c1c0740603d0b000c055540440c6000315000380c014100800004044a40d2031909009900300b00300103440300800800003030007040107a4060700030346145160007052417001900d00702c0003c070000d002420a0f40c0080400102250f1a01c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 448201438 1106 448200332 448200349
    0x20d030605090a090816080408060f0f1302040605030a0302030d06060f0c110d020d060c1202030603030708090d0605010f140102160b07050f0d1d0303031023 69
    0x2d005d02e041022440768060281c020b056a100c050304000205000b08203445000043c0c0d2516160240300051001e01a18000e082401450000720404013280f0b00503a82800240b000c105d2954406c0070909090751a8015801a000095903c5030034070070703010b00e100500d600d207041825078000d410001c002507442c5400410f8158104c02d0490540c6e182400384000e140c00900302d0441e841103107000310080602d0440400461170010f0650b00581c1644240c9100d540041d0140d40341940c6a5a0710085a1150611640c460b4842400300080b03412032081e180078002c125182c039800d904000c24545100c07444174260b81190300c2595560703001c1d140d1085e400c040714100c00005450b800c04d0f19110b42002e0942c80c0482817485011045000c03074ac1d1081c0d60f8840302007242c031031001d042802401d150b00d07448210b51030030b4400460300c0208200102e03008240c0842c4104500301c150220f05200145168 = true := by decide +kernel

theorem cover : BRFrame.Cov 448021582 448201438 := by
  have h0 := BRFrame.cov_init 448021582
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 448021582 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 448021582 ≤ n) (h2 : n < 448201438) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
