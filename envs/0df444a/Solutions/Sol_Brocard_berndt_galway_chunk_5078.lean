-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5078
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:40:22.06742+00:00
-- url     : https://prove2.me/submissions/d1608071-b8d0-4321-8379-85902c1f9ee2

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 913129496 ≤ n < 913309352 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 913130746 1250 913129496 913129543
    0x1e0f0b09190b040308071104021206030f21130b0301060c0201091403061303180305100e01060803160516090902090114010c0f06060f0b04061215030b040606090e070f08 74
    0x2c1c85d100e40d000460643c0d04009500070030086844600c01840e00390f019150030340d10b43c00c1140030141000005140368a0540c407904240b046d41c40340000382d00d00c00c0b0b41141c20f25511040e40b502d40c400c41d41c1c41d900c600c03400d42d008000040c0c500c2e007000e40d580c1d0080c400d1307036601d0050703481d007040090070001c8003040c9816520450000703462004103a480312005009080c84000b0ba855038040f05101c0c01541c100b2500c2c2d420210300e45800c40d03042c4c0259402e001c0d1440087c82998145288503503203008a070a040c00108e01d5041480030f010013031020300e20000c5001c0f1000c20480d114140b040180c2001d071800c038040c00c02c0c0702c000034458144529140300310354141c0d83d10b4400d403820740b038a13100e40c0c820b070606403040341d5100400150024601c0026000381a9030700402d03103943c9005005401c402c11850300b01780d410700b4814a0244501200c1104041c0d13a8415031102040e151410084000c001c2d90700030000191400113a208241e100040400c00c4901032003100c00416165101d1a489030648a042030261030071158 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 913131996 1250 913130746 913130753
    0x50c16020d020f0301060906180903021c110d0c0203100b0f040902040f0203250207030b040b07020102120103061e1802040506150708030f06010f0206011e0f0b09190b0403 75
    0x100c110340140003c261440c0a0303010b200090071101943d100c51451591110100008821081110740121000c00100a901100e0324013a4032519070f070009540c5202c00941c02558680250250440c04c0c03d628101c540e409040710b1702400c500201002a0f10030705c0364000d0b0b0918041d05001d80303401c03441e000d090b0200101c140014400030300f024110881e405600c030a10500820f1061019611032196464820203c0c0c00b0f6070003281301c11001074007020840d00f0220060001c82c90580c9160307005648062307010815560000300300d00a000b07074900e03503600c3c100b114000001d00c251a0840000700100c101841c3d600f0010b4500e400c100c41101441c100d5440c10a05030001515080d8000c0d0340c0908050030b8801301c1e010b0081000f110f03a0140100b2500c1940c00f1041c0282c203110b030b51500e030b0300540030308104102d108042800395403100305120351011104010190280500c24100309001007080f1111a8031280d100c00c10300d64250880c0b00310720b00030800342d192900c0c0400301d03554840c1181e01d0980707154642811030301d = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 913133246 1250 913131996 913132009
    0xd0c17180111030412050303150d0c0b2110080f16260a06091106030925080a0c1e03020607080a02071802070606060f0f0323070206010801050c1602 65
    0x4480b074098007040c030000900140c481690039841d4400c030040d560300d141013024041ca03501319405680c000c0b9031110311200010002440c0780c00b52074004001c0ca0f03ca0070845880f40c801001c09150183c07203081d4200384409218415006000c0c1ca940106558a0100c4a01056aa40b521803520800e91804410401155048418036031445204d1100000c101c44c2c9480e00c5850031910500032100c0e10b0380d681c82e40d001d0152900040d02e0501d000c50f2040d186040058515950ba85200301817403280c0e100440c0381c4900642180c102c0024400c40090700d58405c1e2a041c605449080c5200d02d9210051441d813601200c181e00b803100b400c1d030b07034010001c03824100682c5035003400e07030041c8000800303500c255980805c1180b089816003040104c6508003598801c1c00c1e00d0070105a4a4550119081c044036503c0c012031682c10132041b2074800c00500d00000c112003080c0018a404500f0740c1d0394000c0c25940c0d0180001c8980c085207950580320080000c0c080c0b5155a06000014071601401c03104030096512181d0041c078040 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 913134496 1250 913133246 913133267
    0x3021507050a0c1124030a06080102091503190606030b0a0801060506040b0a050c1e01200409020f0403120804120804081e0919050a051f0f020f0d0c171801 68
    0x40c04081045c038401c5010079050b040c11107440d854040102c01c00c04030340b4681c00303180d01620b003110003582010b8810011540071401c00d90302c10705042c03010000400d00781141c581c0c0c0203001000c51007440050350f61040a001001c3c442c040e81c0c001c19140c000403850341014058842141c20250080307140515081c02a5615007002001404000c0d0401c40d103014803104110200f030f8005ca50120010703a4174400c0c1c01c60701712482d61000602660014042d020b07203503000ca0070350b0b0840b04071410150791646050b04884141c4a20f40000f8140c03c8482400071900d030303011041a204a02c14188510307805917074081038a109a00301c0d802414102c041060600170311043d9000304007443c1ca00f108601b0300d40300500007214103444400d801c0c3c0e0f0b103418000030411850215103240043c002640c400c0180d80513482d038096900740d1880a1014407400003050074016200b0440711440d6040c030b0003540d0720031000044c020200e44401c1c40c1610b0350b8000c403a17000041a50001200c80908a51400c0803034510060015a6844800c = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 913135746 1250 913134496 913134499
    0x20011a0a080a021e0d0c0e07031a01080403030f0e0a210504030b135309060309070308070b070815030c0108091614030d0e09190f0903021507050a0c11 66
    0xb0b001152000a0806003906c0241c040701205d000280fa02c5030000b4211003103088505441d141048000303642da40c000100344d40203038041c0b5003c581d00c00c00112800180282d0006c200142c401d0345038000c1482a60311700c01c03000c404015418030a218000108403102d00507400061b0004d18801c0c08030b10300078882d898103500341e0711825081c0d403c1030130103160101409400d20960f541c0203c02100c4c040221400d04200101c01441d810b10390380301100d0b202e503520380c011140d401740200320000100c0c0d1714500800c102c42c02180e1020f6120765800b96840c01254540003901c2e00b002060088010030342e04011100090301c04d100190081c41d442e40440300440d601c00010701904282c2c00707044801c0340140b0500c08410040d200145001c110f40d8007120601d40b8003003485031a4010442074509100c42da41e0749010b03154001100030788111010710a0007ca000400050030a100038900d8004242e080540109100000c23405203860b80582d03940310401a516882113032110302c0000d03004551000003400c0302c2440c1030121360 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 913136996 1250 913135746 913135759
    0xc090603020a18090b071e082710020304050a140105010e0a0f1b031a0312070b090309190503012307050a03090c03060e0d0c0305090120011a0a080a021e 67
    0xd84030170140040544603040021080101e906681401e5003065a02c01024944207801d0324029050440320070303507541c40d80d0007500010300d41c3d046070404201800d251449100308560340e080c2894495070b1001021741c100e0b03007503042d000c0862208206120703445c121464500e0b84111540c0f11800900280b90a5842200050780c0b81541da104030035881c3c0307103c8070007095180010a03004a0304506240d400e9400340314403c1c0e0160901112075080302c415103c505601900b441c14540f05e032400caa05500800d4100d5810054452081c103a00410903218401c48000340c00800c043e001a0441c0d0403031224820044094000304408140c41500ca60001d052492540c80d00180c001d04582d1115400505139205840c8652a005040320000b0240315511602c0e2036410071604d8440b007650060810702880e90240e041c0a0303004001080c0e0143c002c0c11518811001c0001c1100c100300c00d25007400c04942c144898050b00881d4408203002038006105900b00b03800078209000301c0c0e40c0a21026000184016403600040c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 913138246 1250 913136996 913137011
    0xf09110d0c0e2d0409020a0b0309060708011401020c0f010309060f050f0906190504030c050303040b090f010207031b03030b0306070e090a02090f01230d0203040c090603020a18 77
    0x194911440c020a81141d94a10614880c4000c10008540c40b443ca58001005480340541d4503a55480e010003440741070342d000c22144024000034080b0016075101012990002003040b151580100702c040c440d00c44d0ba240e641c441d03600c400318102e078803820340030990159000f290401441d01c0c115403d0646424149408508924107076142c00a07600004407113600c2d00e840d0800d00520400c1c0024007907010413604000c10842c0b07803501d030a4100304a08100380316410764039408101850b03c507115242c80d042d00300003265a20b0a02d41b410640390f05049485204500490710440d080d41c0c0306000720f13140e03560140da40c420300054aa5003001c604406d540210f041c9591104201c000d61018003100b032140410b511032030a81e415401c203000c00342c1c900501b1800c846104110303030380c150740e103405030741075090400c1ca41394445002c080b141040d0340711b02c034100c48107020020460b198030f8005a00114491440303500b0b13201c002c90380c884403c0203a841c58040258030804030f02090241e6000743c0c0c01100c289400150104561 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 913139496 1250 913138246 913138267
    0x108031b01240f0617010306090611030408030601030b0604050a09181208040c0603110403241a0111060f0f040606030623060f01021b0604090501060c0b0f010f0911 72
    0x140d820b44010559004102000c010300e80b03120b40610020205400c00720000850b9001c1c0001c0d2400500006060654910407001442913a0f80618210780e0302c08407141d600d0a007414651081d41003190b2690000303042c004a21503909103202650300329034000d843c2d0305010b81040c0040c005010f01d1400380740116402403110b404184411807044142c0d04589615100d400d103030800080c0f94542c1d4011600745800c041c80755803046888022a812641c209003140d414107001c0400580012100705c1e500c407010b040500c98034048d440c00403148030405090b2291103210341e42803c4161541c01c22901803105210103000603071016000b50303103240d00a101e21000150366847e80e8070041115005503854501d4203070145140804922310103000e8100408a032040003401d5180300003544d034440001d005c4200c10041400c841c5a80b0361030103603801382c6800d0341c083c07240d503171034010092980c51084001d485855400000c07800c079a80e0b041016068070300714078140c0700740c906040000c4060302c42080356500c0ca0104000c29040d6 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 913140746 1250 913139496 913139531
    0x101e0e151314011b0c05031e0406031406090103020f0109090f1e18020f0105270102011508060f04080712110c061606180515040302010f050108031b01 66
    0x5807800d00c400030000c1c1d0075040c200301c03100050400b058560300d044481e000c01059107208148084041c980680b1000d101d1606506501640d10070405800707071708601d504826070300c4000c0c2043d0b4005680c02c2104002d0401c90400000042e03440d41c0c0c0054609005201600340314417804020740c1c060400c0c0039500d030f071180480d04032103242d403a1003619507880101c00900500c503800001d840100d480240540b40114070141601e0350107801c0284521946002d4282d0769005005817580c4080500c260071107103140b0a56a1282500808864010b510702041203803129007100020f0180c03010003004203d9a914207170719400d040342c05003080c3c82100d0140300300c0300010140340302c120486509a83c0d40c20521071070f00c04585005826068107203d000c0a1120880394980c40e103240c00310580003440856864401c600351240107000f8240034111740220020200a22140343c1101d00991007039000b0403107040c69607c2c0e101140c9081c012950640c01c108680d0500040c1d80107541c0789039040c0e000016000506a800000 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 913141996 1250 913140746 913140751
    0x1031107050705010905120615040b0d0501050108070e090318030a02130c35040219060f080f0705030c072f03070b0c0c06130f060e03101e0e15 63
    0x21940d001000038480f5580c00b010f45001040161408403400c0080c0744180e03101d000c01803281c030f0603008000c0400d03840c3e515078000742043c0d20050154007800d05182011381c00b070300007401906c0091013002000603210050144003485174404001450a040c500480711140140b118600c0b40d05201e0101c0060241c0e0b03508500a10140070a50009401c680b0070030003810310032401c40d12042d518420b0025448031141d80a240b01c40c0501d450502415584900c0003d4030185030a890300002c410511000c50750715005071a1401c038002c02d0b180c48026549024411400d41c104840900010303406201040b400d403401c4020f058642d1080d003008542d0348103108500203650502d1040303e904050b11100000608061204101900406040300e26002c0c450303d4041c0d4694150240c203028201c0041e4008c0d15000c1f03800c0580141402451070030742e9541d2044014510100006054440e000b40c0141818905551107031099020b02c3c1c00f81e01c80c01078110350072880141840b959844240c0210344102202074600c0030340c1ca1 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 913143246 1250 913141996 913142003
    0x4020d02030414010509030a0f090e18061315020a0507050114060f0319020907020708070902091003090b0109020f0d061d0f0405061b0405090403121b0903060b01031107 74
    0x580742e01e020f007810010407001611102080c0d00d000240a194030002c000c41d2440099800c100014060b4840308417a250015449035404151050900142c1403440800030310203081c05049414549540c035006010441d0800d0052a820790500d10317410390b0046801501e007888280c00d1290600001c0e484180c00e40301300c031154460100904040001c0c0d880c0c003206031081a001070b03005001c052403041c02d490800e400e01101072300c02c1c0c0b500d00009030b880b07208011000240010710160b6000302c1d07072015011301075041f4161140c8603031100c03221410360b107100703214100030650400380380b9078103920308141d020003580421060300c00080c007080454540302450090324000d18000241054200010b00b42c030044c6d034400341080020301442014400403038400640c280d042602c0c0105e42401c0812b0307020118040c8074562001c0e07008482802000306168012079024041140501d05226100200e002c0d01c0c1c00000c40e00850010510140003440417034090307440385480302d0040c1030005858003441c07207490740d40c2c10045086 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 913144496 1250 913143246 913143251
    0x507090506160302070f030209040b280501140409050d0e0411120a050a020301060c11210a02030f0313090b0d0b0112050d020106230f0603090f1c02121804020d 70
    0x100b08050b41085402c004000360082684035a086500161000002410140138000b007040813414020004104550348642a450a08040083d1a824000e0b00c0244202940340800011100d050300f40360240340d00c6c0c0b9a11802a04628401200540c0c2884098402036001541c03a8410109610654010724100c07408002203003032803504444003810340c0c600409606400f03005100420081d600040c000c82641d42c00650351104e480002c003c51442100d02228194201d50b5440300901040d001c0744c2280200d00079425240102c04811000d0350f40d00c07c1942111042e5032030803040040311815444400703212402000b01e92414000e07110110049001e0b040b001c1d400405411034020840100080210760000f80000c3c44050300c1c0c42a5010281405070904c2c82645894110f203050b5a03480058050303071180140f80c5522803c01c0004590b60380b12106d107100304c034411911990489003171030324090904080340c0d00504000000c0d44001265400c09900c200c0d40e5003990304413141e103a03100d0002c0d081215049000 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 913145746 1250 913144496 913144537
    0xc09020307200f06010317070b0c18010c0b191407030b1c0c05040506040b040c02030a0f1701270c030209130902010c110d080c1c210507090506 63
    0x2003210307a80c0b04000702c20140e0320801c007002001c1d01c08150075044a4001d80070420407169801c0303c21103031060f4030009100c10a09403c00c1000208680035214550004880200d40300001d001501c15200c2c5100290240b540d520000c0e920088082680b40c480c0618000800c070b042504904002444c5d00b0f55200022035200c01e56050036081008405064140c40d103051000e0800300c0e01c52402d1014940992402262628006602c5841760b0f00500102c1c00003410401088061810080d120b8124044203400110700044807000f0620845041e054440c00b01902c205d540d181c00542c8503804103a4041d400710310600b082840c1e00c2c802d00d08c0f4400103400c05842c05070390341400008100f4050b0003003010300001d0340340100c8100541d07404181c502c5c0c0030b503201d15600300c3e550307031800010b048080d5404010801c0e0800541d01c0343c0c110380850442c01d030015500c0b2180e0b02c1c0c56100c80c1501c00a054803020094088401c41d0182c1e8000184c0200d074000b041d905100f40c0d1140c94602248155120103080c01e4290811980d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 913146996 1250 913145746 913145777
    0x20303031005010f050f030c03072c011107140d0302010615020303070f0908100b030c0d0c0504141b090d080403080304030e090108030a140d050103050f0f010b13090c09020307 77
    0x1025a04c40c49629110307140059070020184030f4000503040210054000c80042c084501440703840c19070b680c4641020001441c5103038018024106500210700040c10306400700d115010000e40d81c01034490a50300d08019440e030a040c004c00c2d04401509408564940340c00081d1010100c0642d03d4142c0e540d0301641e03a0b498292030160040c90100c8041d0200400c048080040c0724010811441c0d800000c400402c4814200c4000303490070b60071101d10780d4400501e1911804100c10f0344451000c407a82620b0910040c03400040c44514140c04030307040105c80b00c504c484051203e42000c014510400001c0030300726880c010351151881e903041074100b1149101c000042c401850f03004134100300020320071100d00c200f546c18629550380702d00601d2050014000b15088500400700070000ba40d682c240c05910410856079241052503880c00e28280c0c40f011402002c100c561042d83c18003034041c203040080c01400080c49510088402080c0f01c2078259100c000c5001e0105045046000039405100c10780e0310392188281c14403 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 913148246 1250 913146996 913147007
    0x1203040f0210120b010e0906010f14190201060e040807031101021e09180403021c03020c010c020a031202090a031401092a0e01030f14031c1b0503280902030303100501 73
    0x703105410b06c0380c54001940707981d580c8852158040c40030b00e07103110182c5204000746c41c0020380c54602c04085401091501c1c4820503641c050208840b01c0e4024881643e440c140c0814401d410b85016000c42c904110b4071011030f0040d62035041d03030400c100005280280c240380c0f401040606820a24002400085203c00b61400082e044212040100e01007035034102581d0281d51500c10340c450000e01d94000010201040c004d0341510440451500240580240c4190003034407500c10040440110f40c0c140241c41c55a1414401d548010101801c14040700b81940c994020740d600190303d159096407580d09840c00a034088d649028003030700101400c0e8100c520a00078203444d00468001d24840c07514507004102003500e581403a00c00ca42c2182d5907a6241c086414482e04611031102d141228007035200420b005100740d075008201201a48080c02d4191054500071601c0748025248034a0405143c180001034044070860740341415549000010f84a60355070100342541c00072114030300c980700300c060200070958000 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 913149496 1250 913148246 913148261
    0x10504081f0e0c01021b03010b0406080c100f0f123209120702190807030c08060f0106051c23060405150319051911040c02010e1203040f021012 63
    0x800a00103c1030b6001c0001e5aa941d800c19404410801492481c0992002c0d40121480e80b40a001031080b103031502c050642e20342000f540035000b241003c05066030700b8810300c17980e20400c5040e95486100c0c0070b82e00c012117160500d841644c40161f40c0d8549c409484c1d43c840c20180d000365602c0880c0c0d070311031000e031542050050000c1107400175800403441c0e1840f03298080e0071219415811205003400150004601c80c0440346900405a18402c1000100521404080e15000c48035400c0450300555a04a44291203040a2103043c001c0b0341d050000b404801d40c042c0442000070905d4200203103040d611007020f911020640383c61240d22000400f0320810382010700581d54001203c122611004000502080c2d40c1d000c07d2140562501d04003981a0801c42c0074858916a0402a590785468030a10305041da95040241c140d280b0072481c00c41108103150042c021403888000990181c01e0b2020f0845032291641d200a00440391403001680a4006079605a0341e4403080c10140e960070101e0f00001041c2c422120071 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 913150746 1250 913149496 913149521
    0xd0513060b01090b0d05040f140f060924070e0306100e01050f150703020c0603070e1c030801090e01020903120c1b090103080f0d2a05210402010504081f 67
    0x40401344001c69100d0100c800c0880b20131800641540d4a00300b80b5008981400010000c0114194250b4507940c002280c5100c22460002d4518a03100c82d03090544d0b504a040c00991465040240010224020761165500070060304040b5814030384100002c8c00c10204440180c5995008501480039a0698080c0d07409414103598070030f490a484000604490b802c00110480c0500004c3c41000f014401d115008001002030041a10b904201d00041c04440b9400700706401030b0111680c0522000710128152582ca4041e16065816401c140341d910140c0484145001199000c0100f00241e440c02c10184a0120300d40c0f0741da94581c003281c00501e041070b620414003032058021940e01030f04ca945120745e0701d0440798404041907aa19170317445000300b1030240c02103c0c7c40103031401d840b0440c550400504040000102d1300c0304914061200740a5603e80a080151218141c0100032065081c4203011466003140c01414558202640c03007550518018a180c05580d88201c00500c03d0b01d510041e02a03c1f100454 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 913151996 1250 913150746 913150757
    0x9060c052d30040308010302040b0d1205030a09050f0d030c080c2704051e06031204090b0a050910060f0509010807210e010e060c04120b0403050d0513060b01 69
    0x3201e001d036069002d62006900c652000c1c000054803059801c0c90340491820a24802078540b03880d0a02410a40017444141c1c040e03400c20840302002c0c90076000c84080c090f4044070b4801d03c506d090208551540006110409880da034120301c802280c0c1c104080c407808482d01d0700802c000041c0301310040980f26000c840c88140100041030201a4082d0401e40e00c0c0d140e8001c02180c0041201a01c020400b0410b134041508903141106100d140145c03200e6032111442d40c1100890281c44600034143d0324000c21080404495041c40140203a050701d40080840c2d01c0001c00250355280c0b1080041d1040704261412000081c03401410030201d81c010594201400c16401c1035800c0800d201c002906051004224408100821010403880c41c887c0c003001450b01e26140c0100082e01c00c10b2481402080c000350420600d104e040d0016903850054000c0350181d540168040640040541e180030880801401c12400d0000034401415244ea180c0700780e0b8450805041052045029030030301600312000030010700e04015 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 913153246 1250 913151996 913152067
    0x504110a030b130302070e09010b1e01050d0b031018060c260a0f0e0a1b0b040302010f1407031d011d0d0f1a0117010b010e011209060c05 60
    0x282d45403011548451407000a071001e45240c80c0890038003403a6008041c0707080b030400602125602c15441560340020540740544543c0c110b104111031503051080050001f0000c00007030305441d00e0f03900450401e10000c1e0443c1d600010500141c0b042c2d41c410043c000ac21103804131607005020081c0a42405000181401003060300200070031480d59202045042110091a02050600c206a0302c078280d004064002085400e40d4844050380320024140151000700100c020b01c200c05829030300140403140d455642c2c0303140603d154019a0384187c0002c944041c07140080c511020b2040010040c09410311a070340343e0701409110104c81c600200401072031810012181108a40541001100c0221180c100c604804185507480c04990701c4503209401080060030f402001090380b201050103040e2400c5600c00c91030171481101d601c0c200d8030f0002000c5e000030208400d03c3c4113035000b0604c821011003049000f0419203525100c04082e41e1903098002c00003100002c9007170700500500e880b01d81c00702400340c101d1245c5 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 913154496 1250 913153246 913153253
    0x1323070903020d02010302032e090c0503010807030b06010c15060f080105090607031a06122a04050402090f10111b03060c0f07051501030501181218050a03060504110a03 74
    0x10840e0f020300a06055002000c0b60074010b14292580c01003036030b0000400c0d07405e04c54000d074100e121144a540516400c09004820032800342060328180c0340c14400811071300c0d1a54807408500703c40a40400d0500c010600c41002083c10301e082240040104000030884034034280001852040d44c1d0f004050380c4e407405052240e84107010482c1038100300c451601085076861480003000c454449a40194444400500c3e03d0024916481d4284280500340f0100c8014611440f824002100c070745929290b20001c100a1025161a902910300880c0182c85100c1242000d0089001c1c007121502410204226990100d5080d0301001250b4440c600d100b80c0700d080c031503c10007082da140000f424100c1084e8020894a00411594059030107540d0088122240c440384880c04403054802804156103c0d401d109807500e5020002c542241c600ba07120382008080380d402c0f05d00b11220030900249062107070701900b002030203665003000c5a000c0c600940300021503040501d0664003000d82c42c0141800b1b0b405201042020 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 913155746 1250 913154496 913154509
    0x613120c0e2d090106080a061b09030f0602030a0b130911150d021602030313030311070e07080a09082b060f05012706050406180503060114132307090302 67
    0xe9a980398482c9881d0b440300366426014045503001407146200e0b80041106001c0700e84c00440c800070100d0030a440d80c5c02c440030119a44201400060035132440300a001c40050701c00c0d0300a5a101401900001f00c2c04000800101d69900408c10700c80701a481d0b180800601450161000851074211a0060713005980c06143d6110b003d0000501c2d03a007980030601d0300c8205110141c0c07080c40c07940241580d6803011401c210a6004030540000e400041c8000d00c1da00301007000045410684251003000655540d5008040302c02c0900280341a03000342d1201180b10014031010041d08107001e20903512480010747c00100018081c0718204240c08905046042000f4002440d00300180c4000703180000e500321034104881d09d0a00454860b8200e0f0802e50000104d4580c8200030700b0664080d40d0728100508441525491058100d002d10760741604464010028078101039520b0807006801350005892901c0008020215080441100000040013034861034a40b6400041079000d41c0031304140c3d03812030030350700071454 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 913156996 1250 913155746 913155811
    0x402100c020303070f0c08100504030e12150426071101052820150c1303060e0a030e010f02030306040b040908030406090b0109090b04020613120c0e 65
    0x1032000404920095450610403150401e4000742c1c0e000640d6041d241400303444102e4030030030b0420f000354110095641034900980340580e40541d01c00803044000400c10401c2d55555408451a00c29522001c07020007000c080584120301440507411450000e00e044451201d503031480010081c4208601c01c0002e500d03078401203281c0c0081c81d01a80300c8000341480041c0d8000d42902050f885209501c04100650140c2049070a414901d804081120301c50031403a03803040702010801c40801d4078030004500c1ca8418018140105d81070b0f20312850b80d82e03291070b07032012201c01c0c20f04040741e50012229003040c0f5400c01030550a024081c030b00103425409842c0c00035100c4c0000f0b800e1a100d240c40e03042c1c1101c1643c3c2c5400070550107400010080d0f6a0415103012802070204000c101c80c04000140001504079042c8508e07101c0940080c2200c0c115900c0b5800c2104591128180204900c02c000f004200b00720000307103002d0054400d40c0c2c000100c5040c1a070000f0740c030500401c1c2c074420004e5036040d11381000c0038081110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 913158246 1250 913156996 913157029
    0x2c0f100b13090b06091302071a01051011010f0603200102160915240809010209030d03050a020d1104030330090201121e05011202360423060402 63
    0x3105003c2200040851191000503944640180c000748032407400750f40204860b078421824050031740008021018104424403400f81c0c407014241c800ca80240c083c0c1c0c07406c0e03100038131f410001400c4980311090f0400c07141d55800030f441860b45074a958052091112940b00c0301242400140021540d08010310100b45040c010400c0307a5494101c0b2000d40b03010310000300080c15200048201c404511051554803507003a9055500181051011a44100e0107200300d594288000c0d01401814100e11406e5002c2c00d000f8044200c00c5500300401907100700c0520402d10345420202c08181d0300ca1541c20028000500030704c0c6d800050340250141d2244075120060501c0d0403110321130101d074410a600050390b0024400820140560408600d41255182d2002c2c20310010200b41042000ba600c40d81502840c40038114001c0d081803140019480040d500aa10710044030107400401c660626902c10243e121419581207800d00c5090b85540c611002d04148202903c050070010403140c074090300000d040203002100394 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 913159496 1250 913158246 913158251
    0x70819051c0909090b161e0c1401050f19180f020d14030901020d0c0b070c15140f0703050405060c0f1e090907182c0f100b1309 56
    0x350189070140d90510010989594208600c04c2182001e003507254003110340b49410440c400c1203140c0a4022103018285030600c0c207500c3d44004032138070265050811f40c101520402c002c5605407101c00800d0141a116540c6420095080c0c14406071040001840888101c060b6080440c90940c0450105450508030b410840070680051503002281200d100840083d2402610500004800b0400402032140310300aa00301d948040e054041291980820072005206408500104000d0b51041501d10701050142c40800e0803400da807203000089072076040c014030106842d00e041020852000d011180e2040c06402c0038866031410741c1d00c1d81d03103605000300f41c0d10300d01402040d032a12101c120400d450003104a001210840d40f0340e918901c3c042c0d085000824820709061002443ca0741c41f43e00c482d01d6203514113103001c4050b418642100e541c01c011601c810300c408030062101c0c010042041c2c013680155107042034501c0d00d040c0580c4010340b1100c29048094070310410003502c101640d0490759441202e0808500 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 913160746 1250 913159496 913159543
    0x31024020d093b070201060302190b0f0703022a040f052a0c12030124050a0c150603080d06210b090f03032721030603070e0907081905 59
    0x703410b510742480d035150070400e012201300900b840c2c0550105080d00e0084840141216440e140c0722080d03032042c040c5607010f5038144a110725020a000250529610a00569503070345485001900f0400d0140c03250060840d640100401e90304040c85140c2560032030100a201c6841d0103103042e04102d4540801c00d80785007042c2c80c03050300b84403094140e403071003002101030303070711048040c003180000307400038001c000c817070929190300c0b914000b41d07a180f241c0e55491640344c05080080c0c4050556070341809080c1514503d942420203100e1320940d10402d80698401d0044036120010400f104081b101e894010081d50314000203010181ca01e40c42982145da640b00000c50f03140c0d918440c5440c00c10001c0c4030701480b648408014803050070340001005265164580c41c80d240c041e41d04071203d940f8071500c1e1104412141b002a40700c030303194500d0010b40c1e000001130700300c03007409684004040c031904c07046071641da064114140170b0101c414148032224604000d000003098450190702c8068a480c42c440c000b0304d4980e0600f81 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 913161996 1250 913160746 913160819
    0x13150e0a06030309150e060c0a03020105090f0c090c210103030f020109020a170a0807050f1b0603010e07170405010e19110f13020a0503041202031e031024020d09 71
    0x211981049006000d0a0308d0fa005a1040c507031301c00030000b00320055400c0c000003d699203000286500c192012400070250480107400340107400e9001f81585800d864104802c00c800c8040c260110034175280b0340c040b90031540c510b0034001c0580802c03400100469040800d0a80507a68490300394098a0000340c0400d003d986038405e482c64284003840c024a12032011414800344400030404504105910090311100300c80486014021403008960744c0d8041d90600040c42803d42030340c0c007030344d1250090a1410701c04d80c2c2941485005101103030101e910769141c012401d26181c4c1440005c44e07510306101d140704400c0d103d95665815844803a0b8550240680040c0c80c0f0b5a9660984a58007000503104d08560f41c00340c445000308142c0c002c0300d013075a51800080c05280904c3c40081100c42d44000806030500700c540910f001038803a400900603100c1c03811a0b0001143c4582c0403004103e5441e00305241e5240d80d00b40c0400030f420000042d60140c1031142980041016010700076540700845403170741240680820201c3d = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 913163246 1250 913161996 913162007
    0xf030a02040504050105010f05060a02060109022a0c0301061703040b0706060b0319061a071218230609010f110304091d0f01020901050d05040213150e0a0603030915 72
    0xa03500c1030902c0c0611092001c1035000b14141c4041c41417019100c1d03162000e20009108801d0450010703030001004004400242e400380130001507035905581d19401281c4c92018500c5100580381c608e42080c1c4c0c040e049031401b4420680200f011019070f125a0307a504001c2910303800345200310789200707000264840070007000754455405042e54041071520783c01c00d00c2c6504504094119004440b902d89040822094003000c8022070403200200d000d45889265651400008180307103a000030321070038500c1004030480901e140b001501002c00481da540d1502c100d0070a951412101d424040d040030050896240d07408017804145042a040c000405101d0005031451481140d02c01d0090320703e000440f410981d41ca210f442c40246d40c040c112000706080f07484060803446240c01040c0440c03000c1081d550b08a005410541d4482e0008200101ca007840c0e010350030075110304820290080040b064144080102c0740100ca8101c00341c80000c0040508564001d0500c440c47d000d981c5180c0700710030380c1016061082 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 913164496 1250 913163246 913163263
    0x14060d0e03030106020d0905010e090c18030618010b040b010e0105031504020414040b04060b04050d0201110a050703120806010207180f0e0d0f03020906041505070c060c0b090f0c0f03 80
    0xd0003101d03925039403420001d484241420302c050000d20100c0e800901c56105008003c001c0c0001000e52095488403400c064060380f065007100302501415081d28602e9a062111901c99040c0c0c458114a01c80340741200c03421501c022103c54400c929014141c500307a64403465080e1081e100303007400307540e94441da03610044802c17041d00d110344e00c1400064040340c004038001082a03291001d480a01c2a150310004210a40703449004501d8265410f0208101503e00014010b40c582d0040c100800d01000315202c00382800351004040e0368030303402180d080040020740c079100701044407285413680581c20240c00003904c824492040c482140e00101003c00d041e40760b9400041c0d0341c0724a510800042c8100002543c41d151808944400318911810032454580240203d804202008000e81d00c1e060078000404d50100a9483e05820000c05010000000704a82d0b212000f400603511602100e0005140c4040e09001c010b21152403500800b81130101d0300c40020312040c10180c100c500c000380c00031410100c0c1c83e16086 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 913165746 1250 913164496 913164521
    0x3060105070b010f1a09030d18051c0b241e0904060c0201060603060506161109090f0606060c06040605040512180a0801020a02030301061d040603120f03050114060d 72
    0x40400000c1c4600600e0720344400c4445e4030b0301600403003000074a00340103400b4080095400d500324011b00c1c80024402c0d820798980c180f144805020b0561035002064000c060030b52104d40c0075101c41c1c1c00c0340501c0034480100c0da01890810304201e02c100c6140426000c0401022514000c8907580002c0704200360004c40c011003160080c00b83d80b0180380c40d051646c007601d82200e0980140d440c004020883d244a4065541620005031042d8504041e01c01010030f0502d241000fa03030b000010442c0030003241c1c0d4030544180030322420002050078044141400d41080b00252100380705c0c502c20032035241030707a0001c070f443d6a04c580c006200242968035420594100f17140c00012120781c2c100000e4407200d610740303041c10a10414055400010490710303003040031f00b03c0c070030300c4241c03805a40280010841e41788207900d24000b1060300b0810850740900c890204042ea845a00704860380c07079014540d0510207034442c02c01d442c5544103240611041d4504a041e801c100f6100995a000e460000b81760b41c0780c615103411614000c0003 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 913166996 1250 913165746 913165763
    0xe0106351e0102030f0f010602030a050318030c070807060509090f06040f0f02130b072a0504060b0904230a09021504060918050f0601030c020c0d03020d091d04080306010507 76
    0x26100c080724000c2d481103c41c041408460302c0415649048403d04505955a0390011803800300f222205840c144c100428100000f52103107003164a401c01030002d01403103a05a002042245d003024015230920f910786d040034003000424019846542c1c0d481d45016000b50000c0e025050544440300400d01400740f0b840d41c15891806d06001054001c25035005000101502d00303200f46503601c0d00044040d901c00c0310800782808040a0b241141d81d201d4580b694800c1c0c81041c01010003079070740ea002c1000e449055000440c000800302c4c0f205050305060059a5000340c56a1000c05501c00d50781c0c445404501c0903190855060383c6800c8071085440d0030607105420413180c5030040d2901e503107000c01011842d45000b1001c10000c03008110380c10740041e004036070092442d0000481d407996240011002001c818100304c046114030046c14465031103603c1520380303550095024000c400d482c0c2401504808040c0d000c04034841c001c061007410108842881c98000740e1011550b42ea03900c030031004807424000c03114050814034 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 913168246 1250 913166996 913167043
    0x309030e0312090a1221200703120f0212180612060a0506031e1b0c0708060c07170304020109031205210105030615031608010e010635 59
    0x10300b4090803040d08111070704001c8985a100c9440b4441002e0300c01401a000c12040d40c40c00c0013a0003044071040864640f024418101c0300c481c409010700c800f60300c502c5402c0180300307006010000740d00d49541c98450034820308442001d80025640d03184054203003440180030a000740f805010b03152249483d60010301603074860070302c4000154885425074540344220700204c400281400c0840176684140303440000e0071456100c040b100e8406460051010448180058034005d80c03143c094042c04001580c179004040a50410391511702d445000f03040f26404400500464000941e0840140b80400c0b80452071600c0340c666200613241c0360525003000300301c02495041c041d03005500102401d9684000080e8414801c03518149140c9202c080c0111901504441c2c00209001241805091003d07005011941203045501c12807014449030f801c1140746075100c58000102001c00d004203c0603100400000398922000103c0f0b0285854008903030302c143c09007441c00c01c03081000b4404841444928410300c4c1c101c2 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 913169496 1250 913168246 913168273
    0xf0b0a081e010903140702010903062c06060d030e040b0406080f070504060b03070c021f0f080c180918011505130501050108240307120b070e09070309030e03 69
    0x192480d01c0c209603612030200445103079500500680d60035a4042c1c64490810741c5071440c0c040c180d841034a041e4103011044000100041491007900c6101e00d4071900c0c4609544003400182480040c040c8060f900c2e4496414000203a4400390b4001c1030960504115140400c2c02e404a80030b40a620386560740240340c032000040601001c50000702d1000c02c501910046a1528100320864203540038194101f6004d00010712410700a00c054103c0500080440d04410441c0414000d40e1012003031000004e140e115510b540c0070307007002d0895000009546514241280704264200c80440c420a2510643d02c140110380911824091b000040300600d00902c114003102542d6401c1100ca0310a090181245040d185500c030000d10451b030590300c05950744540e540780e003c550000204007030107003051009100021001950300300000c078002d00054140140c49452401c106429020080c0f401090040c051281880c5540761030304280d0101c11801d00062000303090404640703031400c04407a96050301c00d8003d84040c0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 913170746 1250 913169496 913169503
    0x32104030c08031c020309010f0603061b0206160f0903050303040b1b1306050a0909050103051e15041527020418020a0e22140106090e0d030f0b0a08 65
    0x35280101110351a60340d85140300d941e24400e662001c0c44021400d0f8481d03482242d60780003107800200e200008a46050346549250860b40907501c100c90b916940e40c0100381c0d18000e945c1303805203104140094002407030302c0403164620a66410700b540811180c40148890540101c04030f40c0030b03640040403a502d900d02854480d5182c1c42c29502c220010740c012024014952000f0112906400c00c012281303489480d091054a60742c02400401c0705001105c00c000c01c4600507441201d0003507000701d00806001584405103500356003000e141860b99003290b0421003000114810b45600164001e69001c06d8280204900001701121a2200500c400350300b03245202c13003c032004503180e40d27008450800c10b0340c00c920f203c841340e4401c0220080d0000e0740d40c03c1c10050201d598040e1640728107240c0c03d0b00011081c04444910003191000c0c111100082c03001c1056491409106171400f500007070328208080440c208255a0b90049545614101902c5e840e01405042c90740c1c2101400f4400940804c0f0903c0e01d0303003000c644 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 913171996 1250 913170746 913170749
    0x60f03040501270201140a0c031809020d0501150302040b0a0e0102101a0f011d130209150703031413020d021f270b0f1303020310060302100c0803060f032104 69
    0x10400d25a80307446d20341d035404681000155456000c1d03201056034090318910b50b0560301040304698800c0002e09921140000c041c0c20400da80000754660600c0c03000b110110855100808242c810700c401d00581009104850a000c4c06007400e0000004a01c0100d2410b602c00b03a4980c0d80e40d007010300e81038544000c102d801c50010000c07112000020303031510044958150120600e1181c264140e6003400509010100c10245030003440054540101c030303008180030204c40c0301103803608030b80011080281035140c4940f40601003002440c4407141802503954801103002a4061b01c2008502e4504045586420b156a003202e046541604410910a4041c100381d03810007186403d038000c07592150311050000254021754504e100d0007070a00c00203460400307450300405486500116810004000f5981c1003040c508a00703442c400120380b003429803043c4242c0c1e6804802c0c0000703001a0501c18000079901e08240c80e0f1100065030b1452600c5445030000e0714044540c4d80c80041211081d85017000141402c00900 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 913173246 1250 913171996 913171999
    0x4060b0304260d09030c02150406090f12021c050106091b02010504050d0f020f0f06041104020901080604050c04031e11031612080d0c1701090b060f030405012702 71
    0x241881034401100300c0c0c2e8001c50001c2d0900b20b0704001d55040343d07a442e40711301c03499806880c1c02d40d00d9141c503034082080b010498001500b030320004030b420407a840d800b0208130050145aa40345503040d01d01a0112410b0404a200911848003024501111038000055040c0b80350400001d210050755004a980100000441c0b098180c005008400d2464014000c1c6402254440010b003400c041c581c904542c05400580b41e0402c50184881100c0441010042e0307107444030419018040c0343c01c051034160201c80072951200d0181d40180f18048190b178001c11002d60160052301d0101d10b0f0317030390740405c8400c03845144c0009102d0790390b81c01340944c406208443c240ca118440c819404035040030b403040540d941000240700e40c82080310f020038007040800900c190015441458854103280c0e10101c4107041e00c00c801e52140004a0310741500c0484848030540078010030520000b04000e01d0350101140052040c1d003101409014004041001c000d0b00354880340070303040c5000780f0503d5400040c100428031595608181d = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 913174496 1250 913173246 913173263
    0xd09090b0402040e0417160b090d0c08180a09090803010f120203071401261e070c022e050c060106021504030e0a0305070914011406091e04060b0304 65
    0x1402142494403c0710156000804542040e50726556854500e40c60204007482820041c0160b80c00f489403510300382043c0c0c1c032440d41030740d141c80c050255920b40302c00e6a1040701005051059900490041c404458a00c80040300031080100b4420109070603000035072004d0401850316a0302c109001099020754145d40440d49661085035940c0307100511a01d240a029605800001e010000031043c018030040e1501c06041400c030342401e94034440803242c10020710444c00380c9442c0802c684c1c3c0d68009a10345080e05c0c499541042820040d00040101c01001c01c02400788065028196200d1120a40100d0424800c0300640038900b0042009289401c8100880040c0c2325680000c80c10f01d0020940c00a0a14407800181880d59075031001c9400d0342420440700c1c0c100241c40c10210216600340088000f40502d1200411850342c40e0008010000050740709001c11890006000b405a88107001c480e5100d008603115900740c002d40c1140e100e43c803198a89140d126150034000038441840e04051440782e070040b10f88 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 913175746 1250 913174496 913174511
    0x5040f050a0506042105030406090501030e210702120d1148030105010311010e010806130e0f030c0d0824041d0f06060306060303040e160509030d0909 66
    0x81c4280310516016042d8000070501043c86010340d1750002c2407800703005400013071180045480b50350130755019401c00300001300b92850074403040d40c2500072002d10080000003000c5482080061140b01d0309900202c42010200090b5070040d5510410f6400c11480700c4800d40f402000c81c003502078900c01c6d451454100c81c5c010030707404284000c02030f8407989030101c10403501841c0b0800e001090750310307070703680ea0481e8607030701c0e548944200c01d0300d0900c2803501840c80740c803542d07821125010014003000506d40d480d038104a0400200413030b030b444100155604a01c6110082001c0c2fa41941042c200308130b000038000310741300105400c0ca60903c0000e2100252070161a6004a916107200908825411344151100c84041c540d03c200c60341015445518800040d080304003a492aa062550810900b014208003641c0942d0520a1500d42448601e0b00700700120010f514243c940207040403002c20007842c0e20036811450350f803003e07030f14044c80441d90001802010354404040c0741c036014010700301038001e048466140948 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 913176996 1250 913175746 913175749
    0xa09061e0806031e011b0f050d09080409020a03060314030715090f0b07021005070f02031902070803070b0121020d0602070321050a06152001060506071208130b150d0c0605040f05 78
    0x80001e44401c00d40d482c54627048442013040040e248000088400d030404002c005040c40041c400f17854110160758001c15014614100b522016009001c0000707076030010488e0800143d46064201c601b603441110119060540307040480082010b15006088610300c40c080140e25070307000c640c0183c1165039280c03c00c4241c5072070f075007110003c10103890701c00940c0c030411500c2d0201c1e03101203440070540120300c11a0b000760307140c00c41a410745d008034008070307440040140103000741048006030b5402a01e264a000c03174001281d40014044540010300038083c5e55000a079107050610818501003401844152030103602014499034004110448088802a00d000c0c0e010a141810f000560300e9001ca40c1c0e2440e02180e01000031506815500c51504000e41d0f83c2d0000142da6201c40014111080c0600d001e03a40051402c603024101250090002c0d6000c0881003030a00003070104400940c221101c1c80c2d404c0404007800000c2100d80204400141c00c0c80000e02c030000318a58001c00410070307109941030361401c0b19981d20 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 913178246 1250 913176996 913177007
    0x83c2b02031303030507020a180204090b060c030318030f04030f0b070c080f1c1107120305010302153006042019120c02030a09061e0806031e011b 64
    0x128001600b4190220810200307100780c02400c103103400200300e1482d42d9a5501c40840c0d4030f141413548030403140c002c03404104011062143c441c0f90b01085e24458038050b91110a80d8480c480141884002c1e2444a0309010108040096440c00c000844a0f25559038403408e003101c42d030960310000c407041c0e0801400195118821210f030510503600900c40c03410100400300342c100700e40182800345c078940c0d500d80101079440c40b640149600c01c0d02d5403401d00d030f40314640d0604458200c000c04c680d200303042c1014010401a1943e0220070b03240d815000a0b070b6241ca00c1e10380060b407138184840e030910006000d40400d40c02c44000951090250004840c20480f508a04c40d481201e6011140514040d4005204108944c182d01080f840e89a0312880d080c5100c1e48014107060865455900220042c0d2010449032105d54102c011080a0806070400b00080b41c0740040766018440b007203000000300050b1501107801c0751002c02180d4141804411503014244030301400c20f000340354020994140c1c030901c0f01d80403525401803 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 913179496 1250 913178246 913178257
    0x5130c030602090d06062d06020703120e06030a0e0c0f030a1202010b06030403090e0105060c0d0e030304260c060a02070911160b10083c2b0203 63
    0x1621150a903440c41c0c4907030000b50040e00b201074010f10300f5081c8900007809131051310003400700f600d92100d00c90340b202003c80d400003815071186900c03d0041814480303590005080d404581e40480711501581d048081120b400000c040c06039003004000c070601ca818001030300503a4041d000c107403c442218540008100f40751101c6d80010ba01034000750f40120100e11b1000c0a4000401745000100d009901d420200742e00d51302c02c54007500014100c1e0814401e13041c44001c068010001100c90904000b904407a46807261031205149082c0249448180010344040c802c2c1c800801840e510001a003110141c1c156003042001c90b0b070701c0d00d07000793701301c013109407404400f03848403500d0795402050301e01e051803269402400901c461000d115418060308100a03a0700c0c00d00081d00d4440c00c8095500c0c1410741076022504816008800780e500002c8400203c0e842c400c17190411041e04000d40584011181d0900701c4a0391104010350f00c0380194028003865604000c045400000407900c0d000342004441000c9841e030094 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 913180746 1250 913179496 913179503
    0xf190f0905100e0f0306010803070311160513060f06050903150f0c030405010222051c0305182403100e0103110f01050c0708010e07060c0c06031d0d120513 68
    0x240780b01000341c0300d1084000c002c2e00141c03000390100700c0000064544042640841203d5200042210405910003001c090154800c4010221032800c15038100b54148a070007440e0080ca200b00c08001102c41a810903001009004a0074019645540000308550b00140f20b190280c070441c1460256100c48500d81d1744101002d110051894440342910309041d400984103544964003401030010b00c6048001e0014070840450f501c0340c1003883c01d400d101c40903155010184401001c000d0b9038020903002400c03202d144540e42c81d103184030301900707000130040c2c2d4812000c844160f402c4403d60500c0b1103054005e40c080c0e944289604076669403541130041e00300d002d00000307000c10800d88a40400b41020b030041802c114050502c0d50a0001e46440240742107103a41c0142c06580d12121803040d03501c414007580c40a00081c0c07400c003040000c0f0b615060b505141c944a10801c00d03946040015031110614201a81c15010b00243c0341100000e000003003a8084050050071384e103140c440400c1a007034402d1071040c030300f81d0f0 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 913181996 1250 913180746 913180759
    0x30402010309050304080d09031103010e100513050a0b2703160c170c01030b030d080f06060c060702060f15090a050703110703030207150b01230f190f0905 68
    0x111540110041c1010240031500d9100501000c500c8060034848078010100300c0c1d640e00c650f1441c60400a40e0520721540d0759021364500103c282c0d40c0c24011034146560380c6a00c0001c00c1c10381f10711a0380c3c101c0e00107040d0060124010445070078100304d0806407150080c541c1c01000380045209042c145c464403040c0910520f581e104001d4440078404030f00c0760142081c0100340690034139542c2e034490010900b55560343c05458100b03007100a080c1d0f8052180c24a4400c0a400400002c60302c000c01620b030860280c01e01030150f0388000028507640d65002141d0451140005807856410301c2400a50b5074281030351180d915820a42c0011040803a40c12100042e041c02001003400e52a00701010004001c05400c000400d5210705110b00e240881030010240c081c840d03a00140e444259040c0841e8030000c10582031840c0c1d003802a690b4141ea44038203d5001200402348150540340000039130b070321500c22040c44141004010a918406100c00741c140b41c3c9070b40c250f864100d40f40242c0b2404a81245050080f2070344000d = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 913183246 1250 913181996 913182001
    0x609030303092621010f090504050a060222290306010c080c16090209031e03090a090624120c0201020c01020f0304020118030314030408070b0412180b03 67
    0x244260482d42107070b8020b0000f200310240b11008600000d408856691150f507000490181485000000408000c40c036540e2220550404d059900001c400380320362160583c660000c00c0c10b001007806041c110307a510000c11559862950b0aa1209560341c1c441c04400c41c0300b010b07000542c54001450304001c104c1850046804615203190f80d5816007024209504000450301070500180146000b0000765481d40300500780c800050b000c02c68100c4c240c2d000314080038018401c001c600d4600140c1c6041001d581000303c90300301200040785280d07000b42011154046804100003c20f1136031030740407805031040303d00f2442c8050503180202c0a0602021801c10020780702105080b546d80b20b56101e014000c100c1e02c0050724000c803020b00142682c206400c8400000400014013045680020b0a00c003100341c4507400420140c81d40e2005080c914803511044920100000060100000340c012180c01c682d00c0844000c0c00c0c00c00d41420003080103a030403d0004150a40c0740c140902c940350000b2012501840308051859 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 913184496 1250 913183246 913183253
    0xf01030e010c09051c022d0d0302030301090608030f160f1e0c05040515150405120609070f0605031914520309080d200702010806010c0c08030406110105060109060903 73
    0x80a10104c03411100302451f0118083d03035101450044024040d600441d04e95040c1102e0100321121a8424401980108110300f00c4425010944950b80b040341c410301c40740c01050802c440700d01e14000c0020040310742071103070844160a4480d176200f00c2c0d00400158410540310001d02c021580151107261800b02e041c24100340d503103058126070512442c00c0e003d81d42403c0d075440211320381d41c8440304030301d01d0b58101e58100f05862608002c828001c1c100f411a100c2000e10b880d801811511000d00000170308400e200c00607240b0061078001401950f0000079110103850569160300d4031140c42c000a40c41d412800745240840000720b0000d1000030f910000c0e00501a40c11200104070701c85510051040c5a25070b0354860114050034090101102240b13004504d00c082484d010700d18106084c1042c1c8904010f00503400586d030310603080341c1d02c80c0c42800c1c1048400343c07608004080024651000780e00344000940454401d5000c040e08030352520000007030040380c49000040d140b0074805d0203070b0000a40130540c2003011 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 913185746 1250 913184496 913184539
    0xc08070c0f020f01030e0318030f0a030804030e010306032f01180504240e0403120c05091e10030213080703170313050d0905030f0f07050f01030e010c09051c02 70
    0x9a43c14100040e40c2c6401e800e0040c210740052180910b19010f01c460081103040600c48001c0d56110701010300b20441d210f690151041ea40a000a42040b20500d8450a564020740c000c2001e19040402016030301d00c80384103000c42c1d10000013019007000303481072101c24a50040103c6800440e45440c601c0045040c90103000081c02e40e0320301d43c071892416200c2134141188007550a009404810030050795481c00b1f0601a010300d082d03250081c4818a040400b500e0076500006980007408120395840c01501c03050782400c541c90b05118510390103185c2150007000144c141d0300034a0404032076010b140045036549006520f0344401d12000c0c00b0f84010040490035100e10070000c41d03201070400c003131a28202160b00c1d0540f40a450704d555038040b44d41d01e44140003503c1c04005070b4261052440003410b002d514045481e8458085105940c0200e0384107402c080268001c2d048109205030f00f800070016901102d000510700b18a81c42141c0c00307070703102c0c030001c025001d5a02841c035030310340c0c025282202c0303040c03083d0a101c0c4 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 913186996 1250 913185746 913185769
    0x601050307270f061a0307020c011103070b0c09010306050324040f080c0c1813140f03030f060a080a032f03030403030b030115140d1407090c08070c0f02 67
    0x4440c0c56200444082c000d41e071160216802c8407800c0000c4450402002e5032641409441e40c90031014140104228144c0c00920294800c00a10306422090181e0717103030510310301039208001d0007403100004000f00c03088014040c6c07070a824242d07400d0103495650f009150301d90341c5c004060301c03e990038408668110401850100c0d0800c1c4500300481c89129161911125600252403414a5400c000c8034090301e0b2406006620300d024a0341210410b07801c00b0f08404165800c50f51009055605d6107201840c00d0780c0520900c002c0380d02c5807090783e03964501032410340344003441110704a100d5110107a0204480310002640b5134880d41c15101c42021440140c05400035112038801c40405041c42045640241c000f13001440c01244662004111003884008042c03c1d160354520707a880300074030200c08200802e0403143d442190030040e81d200f2019000743c200000101541209a40c1c14031a0240001c2c2959295110507100041590b4544698840d2681103400c5012144041c00358503d6008002c0580340c041c10034103 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 913188246 1250 913186996 913187039
    0x3190c0804080102040e060103230a020f0d0b03100603050d050304110a030b0402040506060310051306050d030804031805220b0405010f0305150403051903090c0f170601050307 77
    0x6085004a56410585501a070000a240d07500400d003003158a1012402e10b40001090070107214846030f0f241011f0b000c0c921002c406030100102c1011801c4e00d200340d8111982800d511902954034030a05907000058083d07140024080e10070b24000c620f01e000680703d601c00f543e5004010f0200040b43c020100c44641000d0000d9400c400a0400a601a44e40c0030b110710085218018810603842d1034010001200e80003020540602020420450ae00c0c440c00c20310400e0b51000c50350740840071040c00c495001090250000d54200451b00300364001d01d60003a10302441240300766583c540001c42a58129a007060510505800020b059503207140ea011070102c3c4c01d40d980c8510800101007903014009401c4e60420707809048040341014007881840f9040c8031311011a1080f10a94940d421300384d800816601c40c80c0300c4015045020344041105605c6034200c00c0c0b030540c100850604503910ba200c0b448c0c0c60f031410f03c100c034884000030400440300440421128100c4100501400d021403034521103020010714201e50f03a = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 913189496 1250 913188246 913188257
    0x10c0b07120614010e010e150a0e04140402030609070e0105091810020301080f2d070807062c030a0605150402070c17120405100c150504050c0a05030319 67
    0x1000d003502e00c181c000030801500c1c4039000900b81c000140000c80100b0f0070504204401c1402c1c80c076a2a0b100e000c5116000f100d040503600c06444a0031101c0403170304108198001d040c20a10107400061440003401280201c0603980c035626040f805541e82c031050b21512070a140c0e841c00401240ca00700d41e4030b0ba80f00102d10300034444a292040b490f410b1100040010496960100040c054043d0800c510307101c0c5101c4c00000c141981d4580c98544012100004500c140034401d440565141414007005009041100c102d502281d12a0340182c13142c1c10b04620b5403620b08204d10f0b10701c008601d0450390f0b4121035010b006801d1196a58a0754006060000c110301611400d8903060b1009403250320091010b503004c1d0380c0c40c603009410140102140c0044c00d41c102c01d554030400040314802002e40481c4e0441e141214011920340c050003050318a200011409018440042c4407074003480317143d4204604c614850801d03641040d104d8810040c1540584c060150140c0c0280400159140c003003003504102c01150400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 913190746 1250 913189496 913189517
    0x1230913020c06150a03051c02070317030a050c09100c03020c150c0706570c0906061b1704120b06031b090a0f023006010c0b07 56
    0x100000d0364402803807142964000c80c02c02c0f91000711140d13007088020040300d91418062441e2600740ea54500000300201e80745032440c80c045070600810a00004581c880c81c104c0741e588695440c05101e800c1142c6601c0340c681000005100140602d003141c8200200620301c150510307180b01e044500d140b003a0811803d61084440a0a01340c1c1d4420b410b0103590304c14034030140e5441e020300c155402d00f04d10b50f0100e003e01000541301c51f040c0c40301542140341c1c42c85102c0c008000f0b0f18820307150203c00313030360800b03405101003295481d0302c85114614981501c04d005030124003510380d440b5001003c48036584540400101e0134040c011281c0002090390105078000c1c0800c01c00d0b003c0005000d141c6034883d40c040d8042c180d249800300100f112602c5900e522040490150051903101100f421141d0250203c8500c41d0425000141446016500484000c10100c00854030384104000d0456650003440407d40d0040400440101b128804040c182c4203000c1a07540300300d1074071669652042040090011004c1c400301419 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 913191996 1250 913190746 913190779
    0xd1205060d2102150f011517010902071a0402060904021e0408011e1503121707020f011104050a090b061606020406030b100831150506012309 62
    0x10284140185078a84003101c603850b0300b02a14107285202c14107066040e5804028005d40300051050450340450000c10504001c0b00048492200031401e008103030381d83c2000070070301a6095000e080c02078418640358101d0009420041c44141d0101c40c025440300007000007104604041d00908100070f840301e055081090251210034080c0c02c00e81241009039907aa800040019030442108440007421604101011045042c4071500f082c0d400302404510b00034541500c4148194140410300000c100b414080303040190f0002c2d1110134070944215991300300711980d4401c03080201100e0844100405030b540c2c0902d05016040509188500c2c3c550145040c44480000d80c21042154405480782d00c0050360782d1708028001d02100c41414441c0d020b00c01f201070030314610b07802c500030b40d421154a420f07405020100e0120440c010904180390a4030010304040c84081001503011040c00280003c0f05104a41d21640111020304542001d1a2043e12050351059074211040c000c01c0d0100000d80414003074078103201d = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 913193246 1250 913191996 913192013
    0x12110c1201090f060207030806061914210402120f100b0303070b0109091a010501120504060b060d060f0605030c04061107050d11010f0e060703081f080706030e0d1205060d 75
    0x4d0710300c0ea40000b0024105540441c0c50356101004960482c2055441c900f2107035207014030f913110341c2071240a140356540d5608440c140d5006c0402025004101400103480344000c030000d0740c0484c042d09003e0981a880c00010403001c0500360041d006111423940503a2a0b009400401c413040d070140004c00090020901c4d02c00b03494007800b11424085500000d0f0314001001115020000d146c542c00d80005008580c0d10820004016220410102d943d450700d0400800a0040c030022942c4500000340c42910081c882d0860030442da8100c0400c072015580301010384051200301c81c3c88404190802c0140704440c00344d58250724542d00202180c0c1402d4441700400d410703c4110f07405440701009081c4031240340da8000b00d2400000454640702541a0291001c22450b003c0d00c03400070207006144001882669280e4080000034882003100502c03e81d9071040d0940725001030003000002803c240099a05410024000c034114900d5038030031003d4518034010400038080034101903485080030a50002280d42a03 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 913194496 1250 913193246 913193273
    0xc050901171003230d0207060f110f100f0b09010501200c130f0e0a23010f0207030509010908160b1b0a05031c0501050a090209060f030f0412110c120109 67
    0x129018809040782944e2070345422000a14a021980300d000e007400960340c8404500b0000c541418403c00d010184860302d41017980c00781e5202c1241c45500441ea20512498104441c07802160004000011510040c0921601c0c00d009460100310241c0d40403504405010741144228000d8042c0e4001d01a050000342e0313108603490144c52210344446100e000c0e840b20f40f03e41f210701d5586800514001501355281030703607000d8840c401c200c044802d84401c55403203c04c2d000390948004544c011941c4000625024000f5000b9441190000796402d00100b00c10000184180f181071014900110b240c0c41e1030781c0b405040d03010014100e12a00410b0001ea1410310400c0b051920511410140d0307190700300c80640c054440e160407103100c1028141001040b0b592145112a829641c83d4080035903141d21a1010448034801c2c603c80c07102c40c5170f0000c20459511498081c80d405184503030000402082c003110211a5214401c41440c0e00750090200858a450000b807041d6002030304400100d003006603500c4442054910 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 913195746 1250 913194496 913194533
    0x30901110a0c0609090509010b100f0516062403050604060207060e15010e070c0c09110f220617130c0b0a082d0c03060103060b030411040c050901171003 67
    0xf13605090220940600401c0e41c4454903400800c6103000c10000035100c101c5092484d03050116111031081c0d070381d1040d821109403403550b4a031a42000020720b0484000e006041d0060703204c9401001c80310f00e410810014100b1650020300402e43d649841c1c4526009510104044454594031503030001864020300c12016100300c1d2074070181d62985024104920501c0082030784007000000c0e10020001001485c0c40d005490b101d81c3c000860300c0d000702101042c0c0c403844500302d01264000c940b40444c007040c441c60a103940300c0d41c0d039074502c40b03641c1d2042502c0503421081042c41040401d00003031040c0301d1181c04910400d010360740e10382c40e031540ca103c2500581e00241c10000080c070f00c0020455846020041c00698880bc40401c182c50111030340e00219001d0041d00d04d441196000001c107825a209802000103481e00244080d52404c091804e20000302c0b494005601450500c2854500075004900b5280c007110706864540b10364111820031040e8100042402016114510300030011612030144520038045 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 913196996 1250 913195746 913195757
    0x10e040c0e0903070b0a020c0102030c0409060b0a0512190c03021810020618030f0a050403021815012f061906060509010e01020c130b01030e0f030901110a0c06 70
    0x1060304000040344015004038082400c150140b01002c01c0c00800c449010390030030907424150300e036036040f00e010740710303044510070036600100038806182000c500500446030403c800f08050382d0390703c01641c80d601401c455100440c07001c1c054900d2a1072184601684480320b450041e0740400d880b1141c00c1241c54415402e40040d0f40411610a5440301000c10310341a2000c03100071103550b2881800035603c40c0000c14955480c2201140340d811143c0c01c10548440446843c0c403651605800b1000401070341080c40164424508044d100b0301105506040c2e6004803400c2030100d01461180d401134501420f40340032210003584015014101c0a107403001840240b0b1120301400c0103052800c0c4050ba28503100209040041c54610204501078005080b120510001e0a101d010380e20003600617410400800245c9070801852640b0326080d82182d0301100c02d0308400d0300e081203084035001d07109a4a1800244584003a0b00800240c081507010b0182e41c02d24458441c200c481c0b07499030f40d0701c6051040b0b103503004402268 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 913198246 1250 913196996 913197001
    0x507090f090e0303130521120a09032c0405010e0103020406080d0c03030b011e030f1508030d0b0420030406050601031407080405030c1b0a090c08070e0402070b010e 72
    0x14441a10060000c008140004050040c0701074807880702030000000009212503c05c00c004082c0203680c41d2008006c5c007a400c02d01c419070740d80200da108403c40340311a90600000f40440d41280300d91060fa6070540d0310110400c0b02c14880f14620311078805d802042c036802c03941d619040d54660207920302a0050103514500d40d45144144410b840250f00004451f0b003103025985074066102600c201c1e495010f02c2c000c101000410300594001d21540602d000e2640044030541c0c0c000e4144d00035480500c2a1042009510034240d003844281c0c0407030181140340d80040144081d105c080750000114488028800142c0c00118103180e80d03c1821891402c50170325000c410802401034510031240d100800f0f080c00e01480d42c001c0c420241c0c0ca10020180c0c0240008680454140702d01042958545241202140c80d803c0a0134070810030142c0c101d01040c42141d2a06000c18040c00e107010381d0b1750340c0019484042c0161103400003070346e078034400781c44050304542c0c2442504082101d040f80640241a01d880540450 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 913199496 1250 913198246 913198259
    0x9050a1404051e04060506060912010e300904020d0207120e0a051f0c060e0714180609090f07030803222001030641011209021201050709 60
    0x45200078000e950081c0b00000122049000c003070703050713440f690100c000170f038581d9440c0009181e40030300c000301c0390804400762452400c46015401030103101c503844200e901d2a82021146030583c0941c82c480260082d0501100c0d80d120400400f6004a2500810150410703d01311043d40807030300442400d4507500f11f64140c440b0786503007100721100f003020251102c2e0b08550815000c5250b55440003004c2400b016003000e0403040d140710b88400c1a106602403002c0c8a03081e1440f0701103640701d0190081c080540c0007940003d0103072030242c2094020f0f0314241071140f02642d4000400c002c402005020320301c5801800c46030041e60b038040c48084051841900055180d0400e01c3c20101a00d6400380480004407210007444c006c030f9803507900500010b50b102c0c18403960800c5180101d01504d2039034420540074010000c6020191a003066688243c4a05501c10610601c540e0000e4000c1d04000e00d0540850b00c8407202c10346036680d0784c12013044c0a00240c0b410140d00d0b140d00030182101c03400c55040c1c00103044400c0c1030041c1c = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 913200746 1250 913199496 913199501
    0x30a0609150605031b040b0a0e06010908010e190302030c0d03050a0b04151814010b1b15070c02062811030f0f07020f03070608090c010c0510050709050a1404 69
    0x7011190104001800c0101080d80d802c4036409200003540d5004101e8031a030f5654002c003003a200054040c00e10301d951519058200c03079040d5501070210746040d2001c03403270040521a220a444040004202c5410030007810084c441c01014241d0860104028080700540c00f0090001900810f940010f441d01d80609c1a804032070039112954130030341c182080c210600300c804441c04c05030b070030301c2500b0300340c145800415078000c05803560b00301d04030038400000240c42442c1002138100d040c842055080e68105402c11161a2440c80048050416600003c140344500c11450000721500c0075000300e180030600d40341c150314090f4071000c080385164112041d11095600030605d0043e0b400c50b400071428680500c200c00510f0181019580c1a058040341318015544c4101041040c02c0001d026103041984805d0002c1c4496812035000c122485200c1c038142c401e5100710020b20003140c012000c1d040100d0211314210180001030089010003407801800308041e40c0b4500043d0042c51079800c0d0040c85104082408103 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 913201996 1250 913200746 913200773
    0x1101021e0f01110306090a1508161a12071202090604083d0b0d14030a081003030f030e071a13090203011415071b05031b060a03020c0c030a0609 63
    0x440c2d10900c2480f010761144451150403400825002c2410050101000401d4501e41e104214511070041983e04c41100cac881c90744241c3d144175080102c2d155025800c01d09030b01c24081c40041e103480150025020038031485490756902c0c2c18900241c680414100041d01d180c10030f810a40554000d08088000d0741451003c100101090340b8004c8000818104006010780c82c281c0004e41036515a449481183d484042403410250f0094003003100d0720003840c0c0d23195a0b400a0302c080d0003091000012a550101c5c4a16010440e80c0c987d48a8160b40040c0301d0850103460540c0190030540300d50840800e00c46000c0480102e02100c48012645802c0841183d24881405a02130b901c0148108014803080d85145108150524180c6420011421180f40854580b00da000090305d02c1c0121100400280e101e0211141221821003c6070310154030700382114800c07164034446036030000040010082d054000c0d00504201c000d080c0c01c3c2c0701d0007400e1030f0200e424541a007400301c03400c6559003100e20030020b210702541e1 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 913203246 1250 913201996 913202021
    0x15020a030b181b0c1b011202180609040915020c010b0604030c060e010908060106020303070f0e09060918010e061e01060c0b250e04050109020f071101021e0f01 70
    0x75030300541100070080000050001c40c001850110040710707100383c4804076001d12428038121a545040c1039000303c1380c10721902c5100e0010305211182c1201854034000d4070031400400c05101c4032031110701d00300f250551107406c0c080c0d0410b0311109400d011078012500c0c171503154040f25001d0b946241071b00354a0f0031a810502c0701445a00309200034004913034003011207019210b05040c2214819030240042e6011111a40009080c0c4594000400c480f54007101031401242c144c0c1303941903080032030704040d59400148018650806050720010b452881c0806441d82c003c1d1112021110891402d030000d801d464411148602079800203062060440c8884c240c804503110f14203a41c5155410604001c15038001e07420b01030280300f515804501c0d9001c00350210121810f408882d01c102e2a99400042e041d0b02c20901c0c5184200d02d080000a149151402180c101040500d009803400040ea512800000c201b4070fa06811480f80242030240d16074940c000c0a41c107007220005001c0807804c40c110ba800d5903040312080c03 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 913204496 1250 913203246 913203259
    0x501031b0803192c090711030a0c03050f220e041722032a0b0406050d061e0305060c21090c0a5d15020a030b 48
    0x4211121010080d201544008440d992161031200800c60381c0003d40c44072005410300d4001c0901d15031008034010380c0924005d0b62601c03501e988000040d0340b05400d0712080444d9400410502e9601c0c0e1081482c4501c0c184a82080b5090031417654500b4619000346045106446404444803000c02c1d9003c403800c000d1400400344409442d01d0b03602d544000300c904043ea0407050307002c1070061000d010b88404031454803284046100300d0307035a4280801504e00d04410020000213062882403118007501c109019038000707140c660301e0540f07000c1c1c0840d040d038445030b0852920399840001080040051650306941c42c8140c00040c0c4044c1503007005810a5405880015038400c100104a1207441941c03a040281561220a07842581d585808034140343c88001905e621980c058030111309007040080c4030041c25a004140301e03022404d4103014950120400700d14030b5241c120084003a168800460034101114090840b1203031801d071f45d4446141781807009503034600ca034002c00c900031501d91501c5032051107042220075 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 913205746 1250 913204496 913204499
    0x30409020c01180317152713031b0804030503030a050702070f0f050105030901140415141b030408120c071a060120070503061f08061608060f0d060501031b 68
    0x1e071902ca001500c00c5e4001e890302d0006000d10452014810820b000941b40c040d1102c000c0c4801d4a0b4102d0382c0c041854030041600105611201c4a119515036039032644800508802080403449084020310003100c16150800022002800500155020390914600460b96080c1401c1c0a410240d1940250711507032145282003115800b0400000c0c1121000e080103a43c0b621451b20403405040f4001000d455400f120701400200400300300041e0070030014003c01c1000701c2640e4000c01d400c800030381da000d55551901841c1640452003200a503002071040305c21a20300054003074407a0b800103085030b45030140c0101151000510244030421001d0700416449030089141c0400041c1003110b07203c07402c043d81c0c1c0c904503034100c18050400440010b00401422204186810b1064034004005584003926038150f540c8000b425650020301d81d17014014000003044004607030101241d808100a19490307100550110340411303911140d90368400540a40d82c0404d05d58107504012414060590100c139114a19000 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 913206996 1250 913205746 913205753
    0x190906320105010509010306080115030b060a06120b03030408061006022107110f150d0b060403020d2d030807080711030412050312180105060d030f0c14030409020c0118 74
    0x1500e5055030401d00703140c0e403241620360040707000b4441031300060131940c0380809039a40c6001c0651182e08032803050700445000e40e500010702800780094400e0380041940f02c200303221040890f400c8100c2d002c030050200d030300300b941e070b040103a1038590155070300c000898509034148421a0b06000c213504084980050b24603407014a0f0300c400d02d0b8403c400e80178102003903850014245079610034640801e568000e041c40d40540500b01e40030341c035600800c0c80c08440d03403030058030b0f840506110050b01c085a07001450710309240380035162190181c4000050380d06c00303100840010340032121070f6a01d0001c580640c1d64200646400c1d1009032000502510720001d011040b80c040c1100540041114282c44642c0c2100703000d070400d480c04501e10302a020134480400c084000304a10a6040b8144288070410403000344580c2c0c0381c10084c0a400209d43c903015002880180070105002d020300b0030905450f20a4800c0114024010b40c140c0c116000b542000380303919000030705100790340030034000c11000302c89510884100180560703 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 913208246 1250 913206996 913207091
    0x31603080708160806030109060e010c020c180c0c0313090b03010c11030301060c0303060b030411100c021828050108120408251d040309170a0209190906 67
    0xf420300c0c200402d00380000c109840030741111b02c80591014061281c06020741c110390281c803000c1c0a1a00520170603446180034070746144440035044d0800411550764079034410405155203d04800d404600c4100030660050b00020311100081109420006001d0560b00070542562200401c00c01001410004024001d43c08801c40741143e1607070901040e100e0b07451a05902800807980f1121034920080200010b010354004118130107501155000f00d1198148010360340d00c0c6038410080d401c4210000c8195249001c40111b5400c4622080e840c0d1944540e010b01081241210038031a0030191201c00402104004000c100d6104181700451400d06080412181d40d5401c0501c400f81078202e23000b04003900303004ca038101e4000340c0411100444414008007100070074a4007a0703000c5002800c20800000c0580a030104501381080c144082c080d085819001c2100340240036002c56080382903900388900a480b40e1099000c528070505001c9849506028990320300c0d0303265810017502207048280201a080d250 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 913209496 1250 913208246 913208281
    0xa020909061201182109151b0b07110d03020906092404090903142a010f0614100203030f04061a0d0501150807082d031603080708 57
    0x640c1c1c90555030261425041c00b4040342200312291486922612050080b1702103002c50784000f450111440b00404801282d002ca03e5108008418003010421926144110152620241c400440902c0701d801a290a0b2440c001514240003080503802130013a8494140001410080f00b41800c40c248038000e00425050f104980c00c583c400d000062131901c1003801041100b1000c003259002c01c0e111525400c000c00188039414050b404117401c8100359800c1ea08400032102005445450766415240c1100100c001c6000c802e49140213540754040520042c00e139200300b00007805100d020049241522041c40504084505084110f41042080100c0c02020103101e50700242d02480000300f0201340c1e060002c0a600c0140b2580d44034040b65030100074130005401844103241c00d41c44500005980b00c07030345940ca09e140e101d44039030b68119807580c541c07880140c01485080c0010042d8951401d42010410b410b5900011800344031600d003c07041c00a060f44103151072341c883c105041c0000c0b1409c100c152501c088000 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 913210746 1250 913209496 913209499
    0x30e01050a090911121810090804090905100c050a1704111203090312071a010515181201090507170304141f031b080f01050d0c03081309050a02090906 66
    0x7035050351407a01305807404460f001d405441e40c0340f00b94104884c18624144428040c014588100105c50320616014412500c249a01001140c030b8146000310a2016103e494402e4035580507080b07080c2d025203220302445084465030307510700e99149288800941321a40f1059005851040c034010040068410100142203003400c68964035111b04041c0e000c0e1451041076005a00760040d480160702c82c614040240400710300c04c4072000c0c3c0e04a012020b0042000c7c0c244a0642d0002030b90050003140c0c003c0e0b000070300e240d08c0c0f52400269106144008a080c0c00c80b91107603000c8981d5202039800038804180500400307030802c0e01d01d4044900071111101d40d05d0040307028134011a14a05130700034050390f032405180c84800d6484030074889661980740190041c41c041020a07500c01e0204900a842071040b4601031281c220707110103180c00c1e4288424001000141e201c101c0341c00b0307568140803021548900c0501440c05100e07604c0341103503090000481c00e90310080c10b00300e440b50040c030610701c4a40d2a1303d0002e074030010 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 913211996 1250 913210746 913210751
    0x306010c0f08040b070c060309120e01021e030d18050a0b06040618062615070507080c0721080a14091503041a100e1e0f04030e01050a0909 61
    0x103a041904048014500003000b200d00003030005644642a006031000c50700401850402c20756621055003a02d100d210018619110039498001c105d02400b5802c045403810320448808aa082c4042d46084110f008603040c0396101054980c81c0000501891203c030620356a82c2e040705083c0d41d941942c8918001c0d0081100c40f103038002130381c5131311141d00020041c41d400c038a0b68484000011200300400c7d9901418880390f580c070303040031142c020b0841042000507500c0000c214040083d1005804000c0c060080b90412800b0881070022501c943c028000c00034030308000e070914901d0140030303100011141b01c6191030381002c2d10f40b50000c16103181c01e0703810007052400e060103c40301d40000a4264400c48100700ea200001190035405443d045014501c2544a00f100e02ca001d82203a018490500c005ca6200d44078080e8503109000c910b106d03402940c2c1108001288282e0407640141d2200e0512040310410700c58540c440411003816070241c40031103c0c020a0030500d2511030b841000900c411840d000d0f042c642c68 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 913213246 1250 913211996 913212017
    0xf03021804210513050405010b120a0204091515082701060f0b0c07050405010b03040f141b010f080702060606070c0b03011409090c06160302030c071511060606030601 73
    0x55a48600c410141c1c1d9480309150b05400410040c0107604400800340f00510f6681e0081010300740307441464180c40c1c001903100c0c20015200c62601c401303040104036009181d000d0000042d0f6040a00812a110b60220680c203402c074100500305140484200400080002e00b100344498000354520315602458400100c44010302d21840d101c1c0500150392024840f04041c0710009103503d1040c014008041c0ca0405407840c99a07030f00c0811007941d6003801343d007030485010008240050740346581c00820602c14032200070103c040b50341e400d051003407504c2c0605c800051403001c40c0c170940c1d12403170705070003c0400e041802c1d4505181100a40d01d030f2005101c64020a40061140c050090035041c180c000c0041c1c8191550b03030360715441d03d04a4049110000c90141140c400801c03080070022840418041c0043c050340c0c2803020b03501d41c0525010b2944010f80660004025440c2c040909000307401c0548614030a6003000410707004010a260700c80010391325644c0100060181c41d070b585404a0b81c0200c42407074090050b6 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 913214496 1250 913213246 913213253
    0x200a0923060f0711030d091509030c050d15060b090f090412110718020c120703082d1e090c0108010326030a050103060c0504060807140c070e060a0f03021804 69
    0xc904041136203501d41b0510f110a21103d61084007101600c40000811001050001054902e003006000083c42860616424025070a10b01070400b16103001d014540c40c0c0b03520070500f00048400c150418801c110340040c4004145c20811540d80d0a8001070b100c0c003c076482c064450248017244402e40e501080003031190003460030401c010102c090060310b81d214a01c40e40f1216030000030f6002a03441c1a46000e09104107510700544001c1d59031403078068544524179a910b141c0e01510803100080e01201d4034205000c0714554008851082c400c01115041c0c3e1000404079001e540c001ca00100180c02540c844440c40f4196613205100300e0460780d000c1c1c02180c85010901402c4c40020528640400d41d0030080204024041d00da00114100c1e40140380c00c02000303403100702c200c685100d1400b90101003042403010503040c0b40721349c030300c42e000090381c1078150b04180c03010f20390703500705001d652010101c40400740070f12045142075648040280b0b60306c40300107609440c642c00725040c242d00000c2000841c1038040040c003403 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 913215746 1250 913214496 913214513
    0xf05090f0112020f031005010807050a030c0c080a030f050609090c040b03030c0f0d170c090f0a0806010602100e06010815100806071e0f0e04200a0923060f07 69
    0x4111600000d6443d007810380c84113040b90308101c40d0400400303c8004002040e50003010101e00076551552180e1800306058019805412604000d03001c10941d000380e14086420300d4050420303025a940e000c501a001149040192403010300050311400e0110b082c04560180080c45506ca00c105643c003080c91030118002900b1744c041d000f1415034030301032405445440100032492514a00062b12135001c2099441c040000080c3c04076004050613804000c004102e103003050440025113402444640901c0d01c529806062070000c0e40801c016a1100403c202003400a0099008409002c0014003040d031502c44007550714041e01402c1843c0191034000709a90f40b00700604000600000d00861302d19081c650700007845c1503400402080c2400002e070310301000e240b0a0035440c4842055231b580d00d8030a5605003c002c018210509018160303000c0580349034690303541c8030140078004150b498200c169441e01075a0b5841010101c46e43c580004281c1407a4165078404040d02d03041c0c2003126042e44c8441a62428200 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 913216996 1250 913215746 913215767
    0xa06030b01030f02070602030708070f0f0309050a0f0809030712050d0f050d1406040509030306010c12200c0102070e040503070b04063315020618030f03091005070f05090f01 76
    0x1500f900000302c0e401442010b40065003c1c3c0480d9540491a58030a04200e03005010152102d00244c451081140c205120b60811403103103001d4000c4c0e544c41003c9690b8404100400f550840342e2840c04100101c0c41e14044c404040100303403414102540034030036a0307042e40320040b01c1070301380a00c040c0b10242620a8401c0c0140c034a5144060070410907050180483c580c0403900300d80e210f01c074506080c00144030f082d001c07081e41c0c02808113845912615025940e00300041a40c80c180c48100090045294000322001e1a0018080811406403100b031030034400082c100000c54100c40300c04d100003800d20002585c00022200c00c6a04000310050689031441d00c4400340c800b41105515038403c00c5584004210b07411500e00003c035880b40600e0849513110f4050109500e180140800b6030004000110240d2010300720156007480c00d01900e00d403060600c84410a034105031000e8410394403412041721402494840c954000c0f0380c81c200074403103000c9007500800340c0c8103040e1001e02070803120110000030713405030071801d2 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 913218246 1250 913216996 913217021
    0x9050709031b051e24250516060818160b030708160905090a06030f140609120702040b010c06290a1a1602100807080a0b0a06030b0103 59
    0x1407905a0744461641c603500180038140c0b0648443d9405032180401810100500c01c0151404048020000004181c002c181002c0207002000300030394110746c0355035100c0c40010340d040304e0744c0d038030b4240e40d07060003880c014034884400039400d004d403820b04c4496044032107150b20160351180086940003040c1154241030f110040c0040a4801c9407000c9030191414020703512a41d455030701c9030030301da40360700e2164544403003182030350080340c0301c0d0340c0a00980c2003c1e14143c0e4001022980408c18590302d039140c2d0030f1101480000d81e020702c40314100b80d030a20410b009058204002c0d01c014000c9100e1941d800c0308a20940320000c4c4110b6442c04062400c0e40603d60030040300350000c800700405052a60042180d05900b284545d15441e404001c00c2203207040c11a9005503032100c0d8545840c2001d6151900165202d0114154010040a4513100507548c04100100d5100c060341e5604032428840c3c0c01034440386000c0e1480b20501d007008000841c40e01d03890820b600302d900034074001c11442e0700e01006034020158048401c = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 913219496 1250 913218246 913218263
    0x50303040609060e0a031e0212070902031e07140a11010c03020c010b01020f0c0913150b0907110d03050a270212030a050708090a050d1b060f090905070903 68
    0x41d02070308004034408841444d00d614454891113000c1084100031804010040700c07801c1c0c20000c05d0501003c00f50a04c61001d007403030001440d4140b82c240783c046154050700c4403a4001042002070701078441c03070040401750741c002c2d00c005003440c80c0042d200904028040c8040c540c0070516041040c0f080b204104007801c82c00082000180e01d450050183d4010f9200c030250b0b60a044114095510019611a01c004084068045214410200300103040c0181c00000c40f40d04412484000c610903c205c00e06c44001180c00203007140084062081c2070000402d440d0901559180c2e45103140b134085066803074040302d840c000a43d9602c51704c001c0010007488464952031644400c03140101d81503c0004410716000700c81280b0642c4c2001001682c82c407c1c0741745100010301c24080d03680000c1d01034000e00955200101070165182d1101d0101d00602114034096a000740e15540442c0509c40080c00c2c54050030403854200020030041202800031081c620801008699550002d8075480c41503030703080042c51780010301 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 913220746 1250 913219496 913219499
    0x11206110d02030a270305030a0513051b010e1e0127030305120117070317040329090c03030a05030619030b0a050a0c091e09110c0106050306090705100905030304 71
    0x20000a18a0b49aa410041c0101000000c1ca04091710b0035041c039641a80c0751031071552800200c1000d414007078032115003600d001c4d1041001800c14001425180a9038007990b09500038000010040301406004a00405c1074100800c1c0c18034182500c007141100038240b500c001c0090b40c901c104d2120519152104044510f00701004250b44400103041d031b00c441c101c2e015180d90701c1e1950380c2034110400b10312040ea5482810b0410000341800385803030204801c940641c0c00c055aa49070000c0800c40f0004400c02450000c0003410070300c010000030317900400b80f1704c001c0c51030b06c0c801c5001c04d81d64842c100c0b0306024060048002a102d0b80c540340c503180790180b1424980c00040c3e42c6d241c02480c0c460f054440c0d100e401e00f40030008010030300501c90f119154495940d081c84292400390b5000840d6890103000510704610300340800c1c039098a01680b560000680ca00d2580e81001c000300608403401e54002c00e1180d0418130621035003010025030303001642c0d0210f0b0741c14551115604240d035046601e601c09901030201140 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 913221996 1250 913220746 913220761
    0x6090e070c171605060a051513140c071406060a1a0d061401110a02180403020f250506040509060402130801091a06100c030807090302031b030d08011206110d0203 71
    0x54507104038401c03000c40d071103629a041b8040549504456006a4003905082800b451034a00c00650705102c0398180007a1150404c90780706915002106d60251701d00c0001440c20810941c68040c0030f4000600e00038140c0c1d407c02c580000e60313890341c5100b00c1c1c1c413103d00b03520b1500c0000c101e801225403006000e0000c0003da03030354000101d172460b01c2c84805408242180000008503401141a002c2a940101000d003c240e0040703020150000290081d4214821701c4841072401400b003020f01d510390b4034001184000b280c54203002c0290a003a41115000310381c01c1c04104069200c04180942001e41180d000d03895510141300d16900030001e502209140d820b11004100b4803964814008510207000a90b00003651003a080c171004988441103280060745828603140440d126503541c03500803209152022840b5503d400003841c0c099007444102c911902184210071600e02005111411601400d05007919854400e401190395604100540010f45481e8051155144841214101c0404a00854481c2032050 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 913223246 1250 913221996 913222027
    0x6210a06170601060e060f1c0204090513050d0201060e15010c0213060e01150203090136080f0a080d1503150e010e06130201031a0d03050c0706090e070c17 68
    0x444c00020a0000301030181c10f04006040381c02516119500c1c3e80340c0341c1d51500102c00c0c176810040c040c466690070f00010034001c40500442e40106440002e000c58000c2c0c41c1406030410005108140c103680c5021800c210311119103880a0340488050300500200506d040144d56a001c010310003540a0440108030380360104076440401540c590808020050780c803881080321403030744d0002e1000541d0081c050004150b00c11012944841038112000043c2c4002d801445240884108880c10880808409004c640002c001d91031142c100ca50041404014944982400303200e001180f003845074035441e03e1411542c41507a9003000b540e010031881c50888008002000a05050302c04d21400c0d424021003180304400041c1d02c5020342d40e240e52700060301c0c0702a40190000c003110701c0b519a44080d104849040b641d0313000c04444160307000c0e1703c2784c0d0b42d034107051504c0505140030b54202d802070052459041c029041c0704180d030f0b070b440a4039041400a01f183c41c00d19030b51400034180040b50612000070381520860100 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 913224496 1250 913223246 913223249
    0x1050f01150e0a050d1a0901020a0e031203013606080c0405010e160c0206070803011e06020a141c02010f0617030a0e130504030305060f06210a06170601 67
    0x703542000441c1801101120304060728202e07154000c00c0a2010f00c01da2410032451400144204c00c0c3e032103030552480c219074050700b04a468500036540440d100740e8042d0480c02000201d41c1c210003800307400c0743c0300000440314001030140d40240c0c00084c2005c504200c0b540000d40040b1448481c1140000e10502c1c454040d0606000380b00b180c0c081d51302e0013a101e01301401054140c800c3d40100c10406d541d0780402e5480c031810030080d401003180f481402d0340503032104001006058060001079030f8a44c140f07031041c0d28582e805441a1144030f030b0814104101a40480c1541c407183c0e000c2c02943e20144a01002494452045c107540c0104900628014010380c0551080740307440c400710818000760341c1c0c880000d22410801d680d43d4080d50401c2101d40300c80c40c810032180d129100c0050040b182200b8000d000b108650b070446003213020a944030240080361400d260641112401121903928001907a0500b008681d5101e600846007010140450b0111a094000c803010f0700c411801c900e10130010224080e541c4c14213 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 913225746 1250 913224496 913224509
    0x905100c02010516050a17011409070f08060609010314180c030102130b07061503080a031b0c02040c020c0d0309181b18031709010314090a020d021201050f01 69
    0x4090040030141d0043c000c2070720420001d4001d042450352071009540c81d5001c002e40b101000b171040090708105151900c424081d10011805c40500c1c018a010f00001d02c00150055060020500d543c0003820f0b40103441a501ca1001d9820381d4840242e040181c014100c1e8034085144031244408201102e03a252014442001040d811510020303260001c2c54202d00c2452019140746020050500240d0b0082c80117000d5144512000507040a15001c801d41c0440c07180c01c1120000340004034069030582c1070003080c80b921200c01c00c1d0041001e04500181500c4101c210082c051910b420f040c0391164000c0c0015a9141e80140c21240820018500207284804a0103203c08111560780050b0300c46e1020320400c01090200900640c0900d4405001d4416404030f03160b5410340b003003007480400082c2c0880050340b070054610645035119404800094165510040c8070051200044204104800005011140e00381c0660380840c80c047c407400403071403030244040500903039800c1400b405078080742400014101d551 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 913226996 1250 913225746 913225751
    0x6030213051e0606042303030307020307293d081207050618070b04270b09071101020f0a11060a1e0507020a02031f061d010303051c090510 61
    0x282c480c49842c0120381900c4843d00282c1c180018400c5001da20300d19840b100b46502e02c0c103056010a40000c2c40d50b4402c40d12200140c1011903083c0c108541c00c020880d01d002c0c1c500080740300c1c42121046030741c104070061401c4007440c148060144000c01d2600385c8217201c10294082c41301005102c01c5105144007a12034400b55100e1010207540c0010901c00b07468001740c2c000083c01c0c0540f6411038040440890040c03100d02c070f014842e0001004100817004000500d80788614505404041e44240748000701d6909905130a810a86075580950390100500c0d8442240c2c2070441150485101c1c060080c01201024003420900140d5680c9450b003002c4505d0307800200c2c008881207580c4481304002a5040201046514100c48240c0501c11100341c110603802141c9104552401c030280c1c0000b45000680c2c5000750b61071a02c0301e08040003114501420014190102c1c3c05408030858620390390800300d0500c0042d04014002c5260307035600c550007042104103215494244100071040c100940c5450080e2440c201252 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 913228246 1250 913226996 913227031
    0x6420501020307230708060a09060e0a0f02041509060e060f10080105220213050a050f010909050709050a172a0d170a050d061d040f060603021305 64
    0x18800022151415402050400900c4d640c2443c4226040c11000320001406400404580480101711643c407514010201145006c440d0070002d00b21b4045803e902c400c0d070061090b0901143c0480d04140c907013541910001046031280302c1451414040c0d03003014129500b4504005015101200341c0b6000358030031108880948503200411881000e0762050201040c40200100320034508040c26401b140646886100701c10040b000c0e400c02c9078420f02c031640c0d10102c1c6140900c030b10f0401d5007842001d004162803043e00075940b040040d08601d007911074203e07507544580c00104204d200360b552030020705c00034102c1e2010b241c503002420042d6407400c0c0d4440f064480c8009076442280d21558230020700380c50000105080504009000350520400c01c140c4140c07081d03450741120b8060240041c0b0415480e0354905840d400100507507030950340c4c02e600c13030803140200c007403509003500109030415003096110910364160805c928018000d40712580c4043c1d8094183d40802c50f8602c101d401080c422800d228a150404 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 913229496 1250 913228246 913228249
    0x51603020a0b0112020d08070f0b1303030b3115060804030f050711040209040944040605030a0f05010b12091609090203010e010603050a0c0f060507064205 68
    0x83d22000070280d406104030381180081f40140d0020b04840b801900311540d20006502e0303840c05802c064a0000310f15001c20107900606500d841209103581003190303042d80c620f00560003802c0c942c24a000c1014041960010b1001802c1c03143d016140c0004010f580891150f6030340750182076410704560075404500021115070380d45108000b01d581041c1d100c5440c458640365102440000c0d0003200510360007a0343c4503151400301d61a580e91200d00304c10141100c00142c541103140e245011000780c0d290040d0880c038031104000040c01700392402d91719189402c0361281d50b041d02e403401810341c3c0e07420900c070700b46000c001003103e50b205c0e8010014910700e00c0c80b0f00b206489401d440ca50703480c08003807c49600d642c1c1032001d02004595412070f940c030700d000030300100e020240010302c070707084600c2ea0380f085a0356804019940100b0074840c22500c0180b4141c002d0761f198601c1d10310040d280303105480c001010140e80c2d03003080d1401200f40a409000d219503031580c03201e070b01c1000b41c0f03003540306900210318014403825800041c99 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 913230746 1250 913229496 913229519
    0xe03060f1f0f030f05190803160201020c0c0f0d08070302070609080a03020705060f0c06270d02060c07080d0213050f1504290c10051b070210051603020a0b01 69
    0x44a480040c042c101600d1070310b80503c02d132400c400c11155401112070060051500f0920703582402d0054991650364200703078005e2030201c03e20004a03415a4018010441d02140100f418032001c541074550408400a00c0002001c821080e0030041000b68040b071000241a40014030500f0f41d039441d02c1d4604c1140d2141d01407540c030707010001c0080c0107038040c420520140c207059010b00140109200b0890810210040d5a41010f500b1203800c034840c01e0594814080415980c002c12078032000001411180840c103400a49442c03004000e05840d41002440904011800342100c1c202301d41840d0031500c5010042c07115407800300512500d41f00b55070440b4880614038210011002b088600c064413444c03e132602c0b6038051007649108004512042107039112001c0c80500c030080c150844000040c4c0075501030f42e80d50000322400907102201143c810100c6c0308110482404807411b194044900103070301c5407280000c90b0940b18844c2c4611841072144005004c0540000f004048607100c0c1441407210387e00c0d8441d2080 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 913231996 1250 913230746 913230749
    0x40303140a0c08130f24020408031c11040b0903030d091109060a06051206031510032108010302060d1d0d230726040303050403062a0509010e03060f1f 66
    0x8440c517118800340062500c4030742c00107010020f00e2103501100303079400781012a0051307802003207582c10000d0800502140451104050110020200034012a042c48610389001d180034107001000002004c480380d80d420010f880d11218044804d00400d800703490000400000400d040e401160100040741881c90440c0500007a5491aa60582060700007050000d940d031010f0b02da650103001c1d40440d41c079401d031410078282c880c03420328501082d450b2445c505901031848810b060101d010861100110042c3c0c060f21543c112a011601241c403440099003010040000c203a040368116034a000c154010302300440c001c401d000480d2641403d00c84912100510140300d484200141402004444002088000d41940c1a6220107148400c014681803200c007682c0680c1094020440202c1c082081040c42d000390051001c0481148094001c0340c404084030a0440c1d1611088c000041080641a4462804241032100084c216002402d1031080d5001c20001070b102400c0d070700040c1282941d0103844203014130 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 913233246 1250 913231996 913232003
    0xd0c3f02030d0e06041205010c020f01090c030201052104051b03071a030903040b030709090f150302010e03011e050f1b0702010503070306180b19050d0b040303140a0c0813 75
    0x1100d1a00410840b542c15540d9452540200700380b01c003040031003c0c2282d11640c43c2c861f0000282251120201a2401031000300c0318030a0380c184150400021410040d00301201d50a003000d44e201e4100c010820b200000e000d0340b501180c8030642c2080f0038010001030004003040fa134410b5034090010305003455200c0a29019070007003010314000070755800d6001c400655204100c1d9080c0ca007043e89900d40c43c0d440307901c00e4031090006042014180711013541f070321032000204903d6408200c000c40161030b041c13001d0a5403002905000848200107403a032002e400400042c6070104003940c0b00b98000d40604002c4c44255034104185407118006040c4031511702180450314590b9030854188411503004642590008040204040e110000000d000075058178108044002c500301292880c00101406034115801111140c000d00c00c01c400c0056854161341c20449913000301c0b54914070b03907450030705038090081d40034020301c40c048100401c0794130f021a5101200000b015a1820f515880d000e0300550303180022003025 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 913234496 1250 913233246 913233253
    0x3020c0303060f0d0f0c0e010b271306090f0612050303150a1706060316060e0120030406120b060a08071805120a060e16050d0c3f0203 59
    0x2030b4140f034050103902034440d0040c4504075501c00c9541d181c906007450b000898918100d01402d009644451055501406418000d9818020001544400440c0344020f0200395650340140324a07070303100e0b00c40710205640380c0c3c1e4050021969030034000300200145080103003401d180c10008640803908030103440406821500943c00c68440341e08000e1981d0940e280503a100e04007140014403410000800b105016035600038050900d040c1d400d25041501c1c403114140d002c29040703400e0003900d805c9030303034082980c07000e10b01240341041000c03040c10381c0c0456070804216440017080005145034000042002c44034030703070010f004004019040c040b10b07003e00e90395080072400003000a60f203e80b180161241c0007c110b007190325019a1140030440600d03040c00c620096810160460302440042d0041c2c6801c408600d008010480360034018001e030f00094000c41c3d204031205c69460341030010711036048002d0a80700d100d0f024010700d003580c040380303a151900c1110404800401000298041ea0340300c404200d4029010317 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 913235746 1250 913234496 913234501
    0x60c12010e07050c060703022205011d0a1d01181e1e050c0c0c030c0a031b0f09090c14010909020a1704110f090c040902090d0f2103020c0303 62
    0x1c910300108002d00300b0040110911941c541c1410400107240103d4441d24010f9550401d0105140c11141407807996001640c0404200860b0344d0048100e02c0c901c0e440c5408a2008988800244100f61980d1050402181c490404245125260f003042c1c12540d07000710f054101c075150729088090b20078903c804078442078a0540039403c0f078426008080e92884d040d070030f041401300308089081129025102005408400719188180d074600300040070701003000314000d100c140c507081c0011318218510302005000442004d18464095518407488000d0440c1c51205801151191031080003080800e1050751500c10945000403200d0740c40c29134540d1100181e6480a129080410b4034003e0b5010710b565008000c81c400840060300e0341540b07200d0042d0701c10044a580c0200c100d00700107620611495003032003003040200f407107803694891080360110b0703007604005078a400011000441d040b40c40e44d07000d01034103244054141007003c025407520042c8580c0ca120020314201d40c0d022000c902480c10488060341c030802c003 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 913236996 1250 913235746 913235759
    0xd05010c0f021623060c0601170304030f1b150203072915011803060b10020105190e0705120f0633030307060623010e0f010c05070e1602060c1201 64
    0x6803542c9041c005010445425082c00410110390006c0c8107a811900040f006202504148103400300c0c2907801d100860510742140c6842c031401390003c400904418241840d42c1c501c219000d01c2030300070202004c10b40c9000840e2036001e074480e48490b00844601c401c2c1c000980712603c0e0315108011080c44c070310003050310f9642c042c040342014048030f4075503050007205000350941e40304100304c40e000b851140d030f0085503044001d4140062130340001c90400959061104102d60b280d40307000c621010850205002c150a10030319401e50900302c07950005604000c1c981d4020a090b0400501c00e544c8080041c00c84441e03550703000c481e00b084d822b961420585068802800c0310038131104403440b403100c10014180c1e454607200f513407030104440f44d40c0e0000460000c0380151190311100318814010341e15003070030000c01c500c1e2090005000c000d42020702506100b03114400030b040c040300b00903910240c80c001d00c0366135003070030100c24034a141502e400d00b101c014401d0000141032000c004054074200320324041c0303047c00c0b81d09200 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 913238246 1250 913236996 913237019
    0xc060c03020a0c17161203051b0a140f0601140118080714011202090f040c030212040302061006053a110904052805090109020d05010c0f0216 62
    0x140540462266001c404041440283c00500074150300101c0e280050114118505014501017901c1e200e61451100300800140b5489440e20705506203480782c0e072242c00c4a4101c100790305a40810b0a94490a0164010800005208020b82481c0f00445444c4221401c0b0640d880009014007010b500d56400f410510b54015400080d140300d1034160f131204141c8912106191810542c0110409070308031195501c20350b080b00002c0d135041c02c42c01c0c0551410b11054003083c012000b00710344a01a998401c42d684a99100368145d950609120200d0851402c0a0400a581d824180c0b640c5168074641d11001030241d005000f2604034502001e0385420b01c00d030036208a0244440b0310700907031070b041c80c5031a50008201d851084281080901040a072599000c00602003100c03c020904160340c2d002445044140d0310705140300c0d13182c3c0001140401c00350b9a02c1145809400098002034001c03903c84113100c1001010340100e2114013840c0d071030010120000034100d075a400703100040d0307011407081242840210381c8036 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 913239496 1250 913238246 913238267
    0x1002150604020c060405073305070f02060304060501080105013017190215090307020d15180b0c07020d0b04081e0c010605040b180a110f030106020f0105040c06 70
    0x41005041143c46000702d070900c0e80440f0125030b15002201e06100d0700002e8081c3c102d403030300300860303150034089003004060450344604e40b08800d0101c0800e014040000500c40341800075409480651030742402d1410001500e4203004e004038550030803001041e0f0f00380b048101d4090456845c080e45880b80c02410492000c401402c0550b0840345450780581781341031110040100000340e0b1580c07100b8401040000303041951440348141e00305428014413400740800826180580d40481c0d904825507203900d40910070340070040c4c030101c44c00c0c00c1c2801c00c0013170011004181034031405507d80300ca142d50340520700a00c1744101e0200035804840450600702081d41c001c0c0c526031080c81102e040703140c80651980f4081c03150380c6102610034a800058140c8400e0070030700440c001000b0558050204070840070005082c82c1c2c4100c10001140320b004c00040841d085030300581d0900b8440104070b035442d9500c401049080c1d00c00d00910015215003c422200c840c414030030325100700d42000b0b002c5001801d081c0111100891b2 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 913240746 1250 913239496 913239499
    0x11030f0309011d0a12030e04140a0e010f0e0a2901030f062c0f060103081e070204020d020723100507021f1a0d120503090304080a03090f0510021506 65
    0x41881403a5403521540743d40039100303400e036520110380f451800030480c0103105000b0340a230b410005400f80d5050b00304c12503a040300b0700240114012440070340083c010520820201c85141c100588040620004104604030b68021001c0c981c040040407100c20000c0e411824075111802c240004001041d40030215032a00ca2254002041e40a0101580000d0520452924107004040c4480d8516401c0811110b5560349454014000035851621507800314090a5442c1c404801d281900c0000c01e810b034000c0390700541d4014000c545940a183c5514001e40007400210703842041400c0103031005051412001c0755160b20001042e090103480401400760030041c00c0e8000b5031080c00364425860349140c104c100e429800110010700c2a114682d92142c500d155881e0034058143d80b8020340c0841d6081c00e03003074000703140c505020384e480d1640c1780c42c64a5407140d54440c004d0f40c06010141c10800d0b5008241c0011200042c40003009140c4070410089541c004040380000340e4030400c00c1c2490b00d1508110560b21500 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 913241996 1250 913240746 913240787
    0xa0b0c0307080a02070b13212406080304080604050d050f0901030f021204060506090705090a151b08030709050406051807050c0a050606100e150f2511030f030901 71
    0x10346044c1c810b01900318040040c21f03240070700002c0c480d41c4000820140340e074030001d9100924484544a0304444400420803000040300e060010000240703940142c070041030f80c1811a5030304d83d640c020707481c1c03030b00000e65044456016014403401c1c128468019145600341e2200c55618200e510801540100700000c80c1510700c0f038090104d603d40d2000f07070000302d11442c003640c008a0344c3d10f09036041100e1080000e0619090080c1801154401e45400c01200181c500c000d034428a4449004829142c20160b00c04458040361980d243c141080555000307907004010310303140c40c05820303207802c1048140da10500605405c411440c024401340d100e4200b5450b00000c880c00c0032031600019450013820144011010399a9500c039000707102c0c0b1414032080012100c11645080941c2103402000200c15040400308001d032010080340307004017540b4110442d84d03250b480d40458449040304108842c00724009a0b0103841d0207030000e800a159040214070b18001e03a000001440c43d00034604019903ca01201a03a881c4816 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 913243246 1250 913241996 913241999
    0x201140d18061d1b060c032206030b0901270e01020a02071409040206040501141603260709050415080714120d020a0f0809100e0a0b0c0307080a0207 65
    0x30103070540d00d9124010b9501280204121010540c210701c0c1c0f4102143c60390021010040c50a10960341441100e41210303299629103410007124030390b0050440201c8809094525030700004540014072003114038545052080d002820200000140244100104051000c1101c0d59402c00034913070410003200308000144102841030803d00f240c000018040c0964424441441103560720b20503c00741c280210381c192181e2400342c0c00705915020314032407a0b051001d500c0d41070f100c14110f801621b65804203000182034004981c1401000ca1005501e0000510400103540f034042d800c0b01403041c46017403c2d848040c500392030081440000c2015601660030b41780400c80c00b1a0800c800d01401c401810300b183c1c80c01c2c03146a400c081006018806001d0304599002e646105000c0c0c0d0041040c1e12400c1d0040d07000c0d120250079090a2401c1d00c81c03100d02070303030010038800041e4603e0f4214400e01c8200c3c00c142d40c3e84500039182d9060403014400c0c0c2c0e40e8690258070900c2504000b0351000006c085840d410300c1950300d400d = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 913244496 1250 913243246 913243271
    0x405040f1403040603060807080312070912060912021506010e060f030c0c061014040c05070b1918050606090a06180603110103050123041b0c060b010c0201140d 70
    0x118000310a40c4502d810000741084026458040c1c40c0283c410704c40035260003840c1000c1107030782c2c0c414401500584a08a40007401050141104000404040140e0380c0e201e201484c3c000c00400c405c0c24101c4002401300107446455200040c41c08a88400150300d94443d03c07880011b45040728028042035010360708011f00c15903c8013a0016601403841d5103101358448043e500018106000188404c007043d54201003004154260310b100d0928410560380040d040088440441e01403041304c00140c95032002ca014429000700c44644180300044154080210030004209035113990354941020f00b07264050f0740170440514103221030541042c04008006443d550380d203000c880144c070102d00043d84998400703081062001c0d031000070300d034403509190400c000d41c1007000780050a00b815810001414000d584d40c0b540d6101d603800b0054000c4403e4040f00300e842400402020880b40b0741c000c030750940c241004c901d560f501880182e442103a0507100e000e40040038180408407508041107000380c00341c580c1038041c100d = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 913245746 1250 913244496 913244513
    0x1051b030417010207170f0d0c1e0f18151101090b0f090c0d080a03020a030e0f010c110307030504030b0901150e070206090d08011806050a061e0e09060405040f 70
    0x1c800b900c1002680310061030810b9020600716648040304070300c081041140d1400142e04a910248400c107001038083e08a5404540b040e0520094196550845101c44910740e0003240c09130300f05480d643c070040284134411004510300032600c12070360b0011000b00070007415030151002d40c000000c0500001100d04d802d80f52180c2e41201a9900700ba092044c50503c421000b007817003801e2031000284e551444914950340d0302c100a1040c5000c1d103003003550110f025030940d8401d82014170741501c0765003201e80c90011307003010034024070001c010103002c26504208003038200f03004420b940c0300076013644506060901c3c54403003200d900c200030141401c0e55071300d801e18403010017070491400281c000341600c10910b1514100180c81c01c4000340c0380f81c0e031540c0228458201e040d40704141d24103541c1d203040141660490b00305844082d103055000079510100855000c140d49034410203000f40f51441d44038440f03407d030040100340c80d028445002150404030074000a8803d00b0b25800c00742d00300380324010420405906032110900c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 913246996 1250 913245746 913245779
    0xe061b1f060312020d0503040b04030c06090c140d0804060f110703050304031a130809060c070b031e04030c0b060604150e0406062f160305010b01021501030201051b0304 74
    0x540360341e41c000a00901c032440c0680707a800d4400b80010110a040c14202400ea8003000300700506010507000001c01701482030010015890340450280085640340c0703001c0c01012024000c00d080100b150030001068900302c8241c071322064215582c2480d03e07041c0030007142e2005e9004002c01c20b10980203201011440108040340080d8095005551120704600e000c80060700414140e840c80c40718030060042280c3e00400d010b9100b507010803d56a12136842020480303e02503c0e215035418014250700040c4100c210b00150b1088404031980413060442c0000360040c02c101750f41c0500000e05c00c000400018404810309600143e00500d0141410355070350f040c01212402052804c00070318448008009402d181c05000064440d0341000c001c00c20b4426022519007581c2035503c00c509203a4040c4901907001807004010380b050040000351460388a06200b03019115071000f0314010302c500e800f0401442c07483c40c40076050702d505948451424030050b920382c0c42110700b090404e031540820400000c0301441d00c2c203102c9 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 913248246 1250 913246996 913247053
    0x902030a1113080c0405041a0a1104060215010e09031209030702090a15080f0c0f0a050901080a150501060c110f131e2a02010b030703210e061b 63
    0x81010f081903071203803c184200d041c05000b00d00742420302000603d020304110f00506907900703012103592030501d002c010f8415460140c841c0364001902149065000c03c031142041b0504049441d9039036280408001c01104985012081d00203120b0160811400030b100c0707401c003e43c2c80441741040e100350000ba07801d00382660480c008594810703c0c44201b031080080200285408805020840034526100340c55000c400042c0f0b10400383c0000322026540c03070043c16000b90074094120500d941c0c50703008071a6281ca1180040d6004107140c40e803030181d02120f01505050f108680c0d9280610042c940d6540e48a43c14041180d41c400010030010b0300989410076000c2c1d08486032000810707080c0c01400680140308003221006070303150508621041c1103529840d000043c0000c5401c040d40001d144030220700502520000d15810f005401c0008107003c0070003403505000428031040c132803e035068107054880305c1844083e00c2d0896000e00150f174100c011190a000040d118105541208098180140c4e00000351038090 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 913249496 1250 913248246 913248277
    0x30105091216140607030b012007140a090603050303091b030d0e2d01090603110a0804050a05060103030314060906090c0d0209060705030c060c03040c05131e050406050601090501090902030a11 84
    0x840d96a000d60040703003954402c0120203a20a1038034800b43c84ac030441c01425200600e503120803140780c951000f05401045c000e04200900740c1c5034a0400d861358020340d00b606c20b42c40f4840c4120600c030f403c40002c02035807134000d008208880e6590426221051090720139644162250010000e043c0c184505500e0800d00c0c4074036070480d200020002d070880b28160050000c16292100b500d072682c0030042201c0e0548984c0c00e02c242c49565502d8003514003208081c005209003d0300000200b050f41603004901c56042e8030003c403481d5541c42050042404049409035031005d481008185200c0d07291008201e08d81c0d000b4005440c19a9020121f140e17940a2403040b43c06510001e541c002000e000e00c026030304000e20292480c51401d05450704c81d000141409170500c202c0303d0a07800006a499640b03c1d00c0b200c2100c0c10b198426400110418004000c1120180c501508110000314158481c005030000d9917816100c60007424200202440250401001e9840719139a0300d2810b15000500405003210380881e040a = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 913250746 1250 913249496 913249511
    0x3120b060c010c090b0c031c02070f050604031409010c0b0403022406210706030c030605040906090b160f0503090c18013f0309090e0c03010509121614060703 69
    0x2000c3c1011507000a09407401071102204c04c803400300c2100c4004d0090301a03a00d2010500d076a050081c455010010000c414088a090800cd000320b0410322540c000d48a00500913907440b13170b903481032282034030b10760020303002042907000039211482c10340d0401e001c0c0c41265407041c0400c4941c40344000a51b6848030444c3c9010800100d803501c0380860503c02440c1e0b0940d000c448035954400c3c1d4a0720980101401e01da180e40701c5401c0c04c2e100703602c5031006000c002d1040c0800c0242d41002c10080040380301c16900d100b80300c4009041403000c0c0c000c00401e600903580d0f80d88098182c0d042203580e07420141c001c40c4503000d020415a210f94800b409048441c001c00d8120850b54902a070f5200c985aa44140381103507040341549015070b0340f08a51040403040711108507c0c62096501e4110b45466590708007101840c9000d800764508400004e5801d40c01a06500810013511068503d542e40d41040c07005a0001c20104806000d540d0200c14090b003880c815804800b103072010a0722a0f080c507008803071302800255038420 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 913251996 1250 913250746 913250771
    0x10218010503070e0a0b2511090406140c07060b01110c1908030304140609010e100c02010b03010501090b0420070609050a0b0906100605030403090311060d150303020d1403010303120b060c01 83
    0x447c1d540d02903001c002010052441c1da40ca031500c000610703100d202c1c042080020f018020580c11000d4483c4501c0c0f90403000b0704c0c0003100e1803c0f80d0030001060312814a00a8900c201c1c0d405040064440c1103078000420003041d0318420059182d00c03000f2500142200007000040c41d400c100051402180f1910350752599940c05a0030038a8148010400080baa0402c1500f000d080b4000c03031800750500ea0b5110204e0691001e04060303014000041e5070719055072130f0000006824401e40d11000d13165400f01c40510203540c0359004044d050146201000d03035004104010344c0024180c0c0e200d03002091082d000c0d1030003003800d5100e500d84010101d41c907a1054000704204400071400f2142c0d02c000c0c01031401c0c82411400c00f80c40060449195000040000c2c003812a941d03100d80d540d1060314883d000305001440540044080c1021149483c482100036215144012240502807030119a02c46042e500c0581103a1860b00c0481e032030000d456026142c140e071000203140544420b8020580404c0c4d6a0012429108200 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 913253246 1250 913251996 913252027
    0x13090507031b05121815060405150f040213050a030803270d0e1c030c1101210504060b0603280c050a03051b0a0206090708010218010503070e0a0b 64
    0x2400300150010b0381407070725103003500a002c0e2200c00c403500b415545076a40f0640c40b1621507003034201d03410a03485115001d2540d041410020344c800c00080da410712039074490441d203030352030107403003035000d07401009282411254203040d07018041140508a003040c41c0380d540c034003081180303909400580d04510008100b28080d01d543e4003092034003421081c0602180020f140c1151100516804041049041425409295514202c0314008074402c60840241d519624020346440c24050f0704940105d2000c00c00c1846602801c0d0460f69410000c01038801c80044100071001450001e00403503c05039200c02c0040113071a080d001d5031041009502454420700c0483c1d0000103011803071504281710f401d01c1c40d8043e03202d42c0f041c2513441000355410003240649884d121145a80401620360b001343c40d011500740000c40d800940b245c01006904c041d1036509441d0030130107081c0d02c00c080112031003000d400d41c1d105942d42b04400a5a004400786001c00a007041440040c0450440c1d0f808101e0032b0201044040701a030584 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 913254496 1250 913253246 913253261
    0x1816030c08010f03020f15040602101401060c1b0e161209080f09010512070503040c1203020d0e03030d06060e0a0e04050c1011030c010c1403040b1501051309050703 72
    0x80c1801c41c203030b615140d601504103542c0d0200a008410314010340d6050344070303000501000c0380c20a8900381c4039526180001d59465111111010890411710b000119034102c0c580c460688920f030b907810030784002c191203000d08409200760030270710001d0354580080c00280c1e400c412030148200300b84811490032100c1000b040e21103904100954180782034410300010b0301c8401140c074031401c205c40d595161000400103031141c0c010510400c00c0d1100c2d0174108006075900c10300440c400c80c4210744230007010381c84041000240c0c03011038000f8056485120048042d6006841901240300c00070122807400c107003400c00806440c0740360310a0000c01c8220401c1d50151a1072074044002d804442c110140340e2030203458490f03448000c2c608040c020041c140342800301a1164102080c110105421a0740d0f03400c0b0500d8460003021407042d114000345003521320f1328424100341c084030300994024814942e9610303140706520030f00e0016800329047c40b0782000490003c03070b00c581c18400140f12401001030140741c0f0303110240541d00079 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 913255746 1250 913254496 913254521
    0x6060906030f0c0f1803020918120304030518040b060703111b01050d0207060207081204031d030312100807030b1503030c03031906031406190c0c11181603 68
    0x34643c0d00b000c040d60007818903008011a00d07201a50304c2e040102d09402c044650400313508003d0400420281c0e81c0c0c0f080d582e0606030070500403920301d101c0d10162140140400c0d82c0c003c0005008100e540d59602c81106098a44c44000f440007440c2c1c901d0500254160b80030950440124280c081c610500880622080c440c1b10b04020b004000c04801da40003c0061007038802000b01184c0c04214042408443c0d81503820003948040314a9440e2102d6460340191042100c084002640f01140c2c0080003211614031102c8810203401076082c00807491604030169001000f003100065092030010b10b410b410050000114041e00d00c4000c14100095800d600112021400b4003aa004200185549000200322603010180514030300030800b0100214019003215071015018600300034000d000c0702d4010a000e4010340e8000c154202c00741054030785a09172020114007001041c8043c0c0b020300840c0301c01c5600503000d440108024480e40d1144094886040e050750300a50400890303170b00202960b094410100d09140 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 913256996 1250 913255746 913255751
    0x101106090d0c0305030903090a06091802040e0402330703021203070c14100f0b041802060306120102070f0507052107060c05031207080a060e0c03040b1906060906030f 73
    0x16480d40150601002c00401010004d00100103a00d130107042c4162040140000d182c60012070f9942d030028003402e610301803d03004100e010f01014175000d05108880495003490360350030035030365141c080260201101e5018203085460655545d01100790900e40d640f0407050a038807546a00032420700a01d00aa0503503880004081001403007492900081b1001c0301c241d0007941c4030740c034000c0300b01c07014203044690a104240908003603112194484a8001301101c2400303a03010003800b071840d840080403c5010f10065044901040030a03801e0904104201414006900140c40c10040e640c0328a462074540000399416044408284582e281c0030f0030b00b0524182023102da4101c40303500b0445c540c4489061040d01300b8480901d41800400c0f1050054030703440d0000006410240c94000c00140401d42c1c11150001d42038601080440ca912880c034a442c0150300d0f003c1642e046a603680d5984081d0700c0e0141c41001b91106034068003034902f0407800b038100a405e050303a40c078490030b25041300942982ca000640c00501070 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 913258246 1250 913256996 913257013
    0xb030106080a020f0111030d1d012f13080d0e0907091e24030f1e0507211b110c09041401021201050a06020a171810110609 54
    0x100240202c201a0103d44c80070748a02c01e60016100c070300300001030407041e01010921b001c0103060340c0d00105803084c13144442d0380700f42c803107080c03043c2220380300201c80391300e602e20701a10700d01d03071000c0840038402e0300075034070024904003031901442001002075101c00816030201c2c511894183d13104240200c0d02105403072010b424148070034040c00c8504030b030296000404c0b0552080140c000d8102c0007200500d00d5100d030b4500b480c401c1b20590901e105410b0803c1c04607040c440d0310042411b641c840d2038130b480b032140201051a58030402a001800f00580078008000105111041d030720a101107a801c041c3c0b22140000d10100d80300da81d9004055080780500c20700030500500c0c005000045240802c5540445000384141d81e079103000b0311001001100d20616610208001801c52202c042480c141d0b50100c1c3c409001c959903600499031000c90060003051403240469401c50342444501425428156401c0350044102c601e01103001d10407600900c00001d0340c2c00d46000c100c4c0c034082c800c031038200d41d0103000b83c00d000 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 913259496 1250 913258246 913258259
    0x70818010305011a0d0212040b09060c04050a0b0306130c080702010507170f060d06150314061b03190207030f17220201020109290906190f0213060306090b030106 71
    0x50381c0904c0c2452070800000b1000c049402650490701650810307100f1540714182802d112003040340440d2009030301d00c01d400201e4854880e40c016034084440007412040500d00b016004540360708050329298111030010f100180300035190103039001c036505503a50101d2502d0942170007400d484010b40820180039940103151004601c00e0083d90f400541c402c640c007000d0312043c0204500d00604600507058528140356411864103000c10001182e025108000404000e411056201c0c502581e415240058500c0b60004c0103080c0409598050050b40d01c0c0b00c0c0c22401c40f100c407003c0c0e070b11524081740010b5035000381210035604614101c0c0070001e40400303002145000709480e0b04484d10342c0700382c5404803038001c00e41d821680300b50081c00880c4e50220100d009524506924a091541140f68014080a0000060f503180700086d4641c810340100d60108002442e450f0700c1001007060609021104d41c0030865065002000d020f444d005102e2036500107405480c0c102c180f803c413150308034a0740c480e904101c01009034 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 913260746 1250 913259496 913259519
    0x50a08010611070303032304080408100209090f0603120708030105010f180317220305060c0c0a151b0806031006031502030a14040503030601090501090608070c030306080307081801030501 82
    0x81c0d83d890b0078002016800441c0e00201f40082d13030302103036001000800b08008c0041c14401b410840e4034a208585c146900401404164080e454045070001300080c00160b0003c2c1c03100030145c00240180640340302030311001600b104c95100b0318003a182a100080100400d5a0040714020701103843e140c0f003c0e80e121080001031403000c02c0d00c0043c02940d07141c15001c07903076807804d070032607006082c1c135a100c90352904402d01c4481c081145106c00d6425004050010307109249020072294984000d03030180c00703a14141e0b0b98207014407451221442c070381540c4407209040c0128900b0841098520350716100c04901d0300c40308052030000300590724500541094030810010b0320342401654203200341c002c090388950b1741d103040c9001800ea5185c0703451f1401a0805110034890007000450249800707a907108030458440b00151113402d0f0a2158000248100c0009201e01c0d1084402c600460f101e8603021400c581e41d84482d51541e08208002e6031205c0340041d080e10015035181b98003807996000c2c202408030b03615000c1c04048 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 913261996 1250 913260746 913260749
    0xb0a0f03051b060417210c030304141f0519021c0b060c39150a0309020a080c0109081605120304030c0e1609051c050c090403050a0801061107 62
    0x5030b440c0401c001e800c0da0340d5000140d82c007034511004004500e8014224090742d450300c03200f809401009851040100c4414802101c0c407000441c0000c5145032030703590b01c0100b80d4070350129500302c0f4090b862039840a03002c220380310360300702c0f01800c0c0124042c10f08613040c00d81c4501c86505108458070412440c006400e18181c10060305002010004d801c030a4040400c03024840c8442400c00c0f406840926110f441c0d0340250f4a030400d00c00d9414040483c51110340010070203510100d640e001d1041440801502c400100801c0c03002d4092601003124003842e404508202460f4000c5a003d4010b90b5101c82e0303c3d6032240010b0000c001440081c80106800f000103a284030450244a0245140952a0400e801c00b00121801198454080e42d2541d0356220512608441540e0b2900d81c1d12038444030501c907900c5800900c0039200002c25658490b400c14410f25021003031407000f2034250144000039451943c0e040c4150b4070440c061b8a0342036079503103403000003010140160040340500c000e1341c0d046400c4c0b032000503d100 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 913263246 1250 913261996 913262023
    0x1020c1f0e010c08030103140d05040605030610031b08063a050a051b010905060c1209041508060403030c02070602070504050c09030313050405071d0d020a05090a0b0a0f0305 76
    0x80d4020710340c1c80100c50500b007900c0302400312000000000704118094020f0748240600d201518000f000303804044a40388564803070035000036024400b08056180043d80d265110f107182c1000508610032012071542106c070410400040b0361039600700204c1e420b00303880024840031a00a1002c6500078102d261102a400740d02d0301d80d0200348170040e0020080100310580c001500801141d81d0b04829501d00c1c3c04481c40c92104900180c2c001800017450b080101c2503a001b203040c500544000031b0020304640c240e4001040c1c65a100d0740320019060300c00c41284a407009840c0740000b40c2194079041c200a4140c40002000004542c001d820800507940c0c0451040d0030f403902264049015155035407103000500806003260f0b4103000c00110914400d03a0050940c00710395098030140b00640e02c2060030303100000d61b44c0d11510442d041c10360111981ca00702071255030340d6200901502d045605c2e04003085003a103003216008044c603507448036541c540c54076039800d50040400351043c6652030b0555a8554450b2003020007071 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 913264496 1250 913263246 913263257
    0x50106090b1227240412030c0e1309061a090c07050a020a17100501080a030309080d111b030a0c0308060f060c010f060504021614010216060b01020c1f 66
    0x10340c0441d0381c036450400f0122031910244611202407059511500048149000c291002e400d0301c1080da065071a052041c0c2c0c1049105a0781c490b07104080e4080d107d0080702c00100145c5000784809035540b40075500051002c0c01001445c1d641d185451340454112184464110302e80c2100803c0c16a1a68240350340880007060007521a82c0c02c0c41c08078504000c20310f00a50101b0340d804045419542c00c103142d00c1d0311b030b107020441c0c0b80c0c080c1d5a44018100c90003030280144981240c60403a011031300981022510901c00d5112616019943d100e4904684000c0c2603d0182100000c0b000824400300041080c0c0e2590320740a945000701c0702178090110440c101c1c3c010f040c04001c0700055541c2e550107200e5140c004000d08029030760002803100d41e00034080c04002c2404d1600d80705001c90030f401e0910076030b08040c804140801c104070b0161540380c0c21490b60040440079640800c900d06854520901b1100d2051040a000c5204400352002a0800035070380352550290101740901200c034a00300326112504c54a03820403 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 913265746 1250 913264496 913264501
    0x307080c09060d2a0803040909120e010e0f0d06020c160b0a05030106080405100e0f07080c0901051527121501090b04090b1006020706081e060a12060f050106090b12 72
    0x510802501a0300003402c038000440c001a4006041e000440d492b0300c60f100d0000100c0310300100b41d810016080445001a240c2021054141880301d902c0d00010340003001c055940b000356950030140d80c007280154907141c100c021003520102e40c544401025081c0302610504110072010002c00e80d000c140b0411007006071120110713051000c20b00c400d00020340b0380170040c440ba10304101c0c490760b50300626403400c9161041d0000043c40000100e9500d0308028010034608040c3d20b07203401c110040032940c00c0c002402004004c4031401502501c512180d6132200c0355440d24607070711007041081240c0021840d800d2500074248001b540b5441e002e6040c150780c90300800288a1460101080081c1404c3c1030080248410806005403101da50007842d00301c5400340e084800060b1986000c9400500030703039410780210740c880011209403409001c820780c07004001c0c0c03940d090075584a00020711146440020380740716513580041c6405013014052a800f40141e81010082c0310700e0305840025510800c1d40740c100c00d0403002c02 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 913266996 1250 913265746 913265813
    0xc031b08100c090305010905161502070302040e0c1e1e0f010311040b07080306040c030c02151b1b07060206060307050418170a0906030b13090f020307080c09060d 71
    0x120079004d960890020040d042051411999501c604c02454503d001b1600c8002a445010300320f5070b0914035542d0181140501d55800c0c0030140c880c420000d8240d00174008501c1d06912000c001e82c0684c0c8100b80301d13100d176210f0241800a6203200c5500c0540403443d500c00890562684101c2d40034200080c6000190103807101901040d5000365040a101d02c0800141101070245c800c1c00f6500481049400b00460001041c0c19411250084182c0025800c59003100c51540902c0c040b069001c0960040440001414a00c040d0a0780c88100c4002403004408001e0195400401c0380d10083d2026000801c024203004001035940c80082c400d483c840c0e52104500c02c400e42d20b21070b0048071103602c8032445c9001d44030042c8a40c501e8002d400c80c840016000c40b400100680701e4050174940c03420140281e0220901600e08002a000061042d079069841100c1c031801600c01300b2021005100c440d020b0413582013810f04100e03050501900c0b803440391a402000d0b10110700f415804060b0100200c0001195005400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 913268246 1250 913266996 913267007
    0x7050717030709030312180f0512040603020315030c090604021c0903051e03072109050f0f0717030a03020a0c050a0c1a070b01060305060d0b040c031b08100c 69
    0x200002104403001c000d0008540d00603000f0300c203491190304d5140800c100110280f0841d1380c6d084080030f600404500c410081101001d0845a0300d0168040d15541d4403031041c03c11003680300340e02000000f580002003180740b80b114034903051045022005040d140c5903000c001303013041c580904902d12899000074203141c680244080186206603d15040c0aa0a29420040c149400500005110882000c00101404e1109040742d10032101d030b8641c101b1009001802020524403d880c0540c59503859000074085081084440611100c0303000400b02048805000341c00d0800b0f642c440b0242c04001c0c1c0f1891000702010090710100101460016150360007000210b40c3ca142d451400b50680c020240802c05102c81d088100095804904000300c0e10380940f800c14506101d0000050711082c030034001880f9407031103504a00d8104000802c40d0000740300c55220070b0302c4894280c9040310218200c0a0800404c20304a03212000411859107100c0041d140c0390200791030742c0d40c1040d0072403466035840100e40000d029a = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 913269496 1250 913268246 913268273
    0x90e070905150403020a06050a0203160c0305060f061002010606211e020309070b0304080a300e0714060313050a060606030c0e122833090b070507 64
    0x400710040c0381020b03180102150b1080c0016030058403a030740042442800307041120745000b02d82e80150b15107114010f00100010500404492910600c20008003003a0100101030003660045181030403810503104000c840122042200c041d0b90610300c040104581190300d80c045508418400c4901c1c0038400503050013072a4084c0f4900f074a01c07154028240b4100141e014601c51000007003240ca04136101c4940542e070780001c036802442070ba4104244030595120b012445070b089030003407010301e4440100b903d07803214520521071a201940c0d1090a041250713810071501d401001c03051580c4100c25030b410081840ca2200a00c1c140d0090b001c0e5001e80f08111080041c2400182c01003006c00c085030302d9001c0200a4401010210001801d4042402c11803500408160301400414020f204280c0740c56103060100d04910038600391100c1440d080e6000c2100c4442101111a1252000490006201140d20b0700c1c170414151500e034a2601014400140002840355000555410119100c115a181010400010 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 913270746 1250 913269496 913269499
    0x601051605100207050312130803010504021b0129040c0e060f0910092301020d110129010206181203041407080c0a091e090c09050420060901090e070905 67
    0xc08000f484070100c0031f0102002504000641500c500409000d100305151014101200c00c100412180c40c0a50003012268902c004003000c40c0190350801b0f0858580010305000700c110382c0400030f101d00121418180f0004c04607810072140382d400100600411720442d8407400360b200069410b4080c2a13841c1943c0b091070005100311003c10f20054003c009600c0d40c0b24500c0c00490450038580d03400e01c082040716405406034020440441440d00c203c510118051081426541e076111035440c5500c0c2100845a0600e407200c8100710b0002c00000a10741a0001c0440380c0700603094900240c0107601154004a10200980541e03d0380c80354144001020301030505c0c2d0900e0310030b0010005864001181e0100102412107800c0d85035030340d42d2140001d80708219224140340b4094000c0e80b04000007540103140d014051a490514580c0b6105034100300c440540c0d051700c0842080071024000305a4460010b0610381c11780e403045c01c0c2030500e40083c008510902404000b080d8007030004200f64419601e61000700740 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 913271996 1250 913270746 913270751
    0x906090f1214030c0613020f121f140a0204031208130803040327090c0203090f10020c0909250308030601080606090a030b09150112080702030a06060b1b06060105160510 74
    0x800900c0c4c40080501c0c071108a0240c004c800c90040c003071804051415406441072702410420190030602c411403100078400d00c00c0b441da64003140000b011407511181c42101040c600503980c500b182800618078100801407010080c0500070800460300521103503050952100c00300b038036911186400e88010100031054880407010510490301d820450b2400ca00f10380000c04108011101400100c0e200d108440d0403a4001081c00c9030143d46081c000ca0041080b07099205480d81250b04200148502c00261000700d050303440440b002c600c0e50080c2c881078000e80341c50510704425603e0340d690200d29000060020f030501c59030304001641074460500322520480018500341426440c5c0c60302c0b07206450140d6410040d803050b0440311189442a554040c1661441d908003005030005680d101c0d041d074007252049805002e00c20b503440c002103060280d900981441450181c542e0b81b51440036010300800482240030703a018030203010050340c00c40c0840d201c0041c1c080c90b110072151a07042642c80e014004035000101131 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 913273246 1250 913271996 913272001
    0x412060f0231050616050c031e1b10440c122205010204172515051b03041d06090a0507030b0a060906090f1214030c06 52
    0x1c0c00801011a24140e50301c96250340b00d41200182410003280c020f080d0015410060328849070541a181440c151080c012200d892081201090402100c101064080500055440c201f207400307000c2885000805041007401c12a0380340040d4800c001d640c84401070021100c200d0b11292905e040c400ba9110380c40221880525424036085840101070071141d03a41d90100c0041808a009102240c00c00607000004505684070f201c04640e120505041189600c0b00e1881010000f4100b03001500003040459009940403001404003420203400b50201d004000c0c0d010b00300380007805c8a034103503007d9070b0700780e52140d000c9075510405030303603900c41c407601421040040c140600041900000810994401103004440841d18885c1c24000003015681160700901440000b40000d034035a000c01e500c041c81d071901240d1042c0d0325011403064002504440001813207000e00340b02d034a8010701c0c00c10061620070805510f951070b115103220006540c1c0340042009013100307680140c0030300802c10780d403503842d5030000d448030750 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 913274496 1250 913273246 913273267
    0x12020306032d0c030f0c0f0a2c07020102211008030d0b19120602070305070206160516050d140f0f010213090b01211e050604060905010b0412060f02 65
    0x84a00c0844802d520407200910054100807884224000710a0000c041419450040020280283e0040341d0070401030580054002150012100072841c042c00b14000340184075900001154001c0006065a00401c4501c20188000e031080d140b031480f00d8840c040c161501004149605095801040f5501c804100300780310f00713200d0f40b044010b03006c11120690040035090400140f80128031842c0003d03522026042c02242158005201c5d45100b07103000343c07814400e03500040c1240c11040c407000d080d290040310007042107820040782681c0140340c00907040e500e02c0d05001482c0a01884401007840d00c6c0b440c507800b8021410451040c6060044040c2d4680403810b0814038002e4002c610490548106124000b40b550020311801400303140694a590801112044130700c0710036000e6901607170003030b540c6400c00341e2190300d04040f102c4401118004107050a016041105884540e001840c20510b0071004000500324107040307800303c450a81010600c074072170b0f00300f044c020006490b013907090f20300020b00103a60 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 913275746 1250 913274496 913274563
    0x1c0303021909080f0d021203060301020910020610090203100b0d020f041d0f0403090605030709051009030c0806060f0d0305070606030c0302040e060712090501061a0c07090c1202030603 81
    0xa8030400d400301d0fa0303030804441c4d481c1d643d000d901e11a500582c0107802d1003015444c4800056a1003000540054170700002d1101141c10200d41640700300040c0c02090070300403034080700e400d808020526403e0a5041d03080c214503603051880c152282101607680040c90141c103c04a070190341e8560f4040303418580b210f03600c4107004102c8000b50802d004c2c02d600340001881da0720b042402d040c00781760960703901307109103040000c103030303190b91010717161006000020381c0c0095165a02ca0f21000a03d413207545008611b031440c50301c48403a03019600000301a0300a50100801c580700c1c200200c44c1207004450410340011281030541c1d9600c600100503002504111020040c4900d4481d42d1003168401e076010003403006821080e6844100580756080017540080340d02c5041d08840e004200154028400024402d0343c40300a0f1000c1c030000c0d101c90941480104091070300d500240403000051000020610881c1d65410009200d00c16203035020303845950100100c0e140e43c508010503801c40f1001d01c50200c1d00c44610070034000 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 913276996 1250 913275746 913275749
    0x17010801090b0f040308040204050601180303050c0c040912140c0f03070b070201021614010e010204080a0309050909070b07241b0e032d03030705090a050901051c0303021909 76
    0x25100c0008001c50508a42500184e12841e0140d4580314541c40c0d65080201900340a892507042001034208492050318400b0741e00c2c003c500c40e850b03017a03403180c1030501c090505107480511782c8150318010749c0a011880182c48103c0c024120314001642569400e643e4480c0d0061261840c0c5520404000e1212124000b008043c6103008450400c05681e071b955080f0300303034809c5401003070750044510410700c009482c1441000016020000119140110440c0381e402ca13003250b84010603a51082c0b1303410050580040e2007201030320041e10102d07440c0c54401c0d0480d50301c6855104c1c610344a1000500c040074040090095805d506000003400d02c0c0c0701d4012100310182c82003000302c00882c035032460803140c500d0003400d4511002d40064064240c3c80d511fa500c1d2220f4904082e6a0302c107640e15001d4080f4400c0090004503c9002c0a4441c1c03501d4080c1041400b04114098000c3d9008602400052050f40d6a0701d91210625030041d40000381b0504a25084000e1301030510500446000030300d4000c444d40d0445a00300 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 913278246 1250 913276996 913277003
    0x313090b01090b130608180a0f031209061b0809070611030d0507020309011d0a090b030102041a0a12050601141813061805060d121b08030916060f0e011701080109 71
    0x506d9522002595103442903102c101c003506900c50000640000c0058905000c11030107030503e0081c2802c0301700c0030002d444107501c04441c031503502c1485003070035440410702c040c640c00a441c007805d091404128040e980c2c90980103190502440c4190408900820011184c0c10b20f8a80ca090000d41810003000c1e55a4200c20300e840d011442c18002200511450010f2801c00700000300100c0703040d131403d240800200000e842851b0195001c1102140340050b0003035607041d0f5160f0b41642560f0790405000142203046d542d5000410703500300000d01c2160f0b0b0380007921403e0240c0b58604942e440070600d07800006c8522030512541c009081c1c11080828075415400b803411104080b03004055280d80d094000c2c11288200d424552050407094500080f070411403000380a03000300d050070107081241d88448059038612402c11501b80d48000100580700c1e006000b010a041d60030a101e2a1240c00e01c240605081d04a10b0f50300200081d201003580e85a01ca0340400c10000155009020340b07507100c48046010300400706098 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 913279496 1250 913278246 913278257
    0x260a0b0a0b010e0a050105180409050c18070906080a090c180b0909030d0b03031e030610080601020a0b1005060304080d0c05070f020f150a021506030313090b01090b1306 74
    0x1c03001c0d402001607100020005103415030843c10b0038019200342e0810090040c2403849203c5812a40d102c41c030441d032116006034000c040a40590040110180410040320070007100700b028401c95070340014011b400c0c1c41035810900c1135680c6803803100c001402107400c040c10321401400300144012151920b010001c004800502c04007902c1c50078440810b00994900145500402484611502d6540310744820b850090540746042c0b07d0051454030300344001c10440600c0c42c00401d00055103448080319070003511904044845150440010f5211034841e20050200c51490000440410a0801400180800800083d00e81c100750070310082580284180e0354803180b9161640c0f8000d40242c06030354086601121034002100d01e90309001c1200010b81640c0d0f0407084076020340c3d441c4000400a00003102503a4010030140504501d00b45a030a805402c281c000c4e04200120900442440300c2c039000d86039540b401055800e41c00b40100c0b40b502c8258002ca040c1d06000c1580b07907101010200c00c60494585070b588 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 913280746 1250 913279496 913279511
    0x70906050403030e090907030c03060c0315140f060c07030f140c13020a090b03041407060302090d02040e2107210e010c030201060b0c010c030f050c0301260a0b0a 71
    0x391018071a40c000940880c055051000c0c40e07203070174256036600000545c187c0328800d69075524400307846580d0708110740c015201d9840c007108982c588502e41031114640c4001c201c662404005c03511210920b001d09004451501e01104a07440394001c40303040b030002c0320490340e19035070b2400c00c5038500c82c004e88100c0b088151001a0403400c13000194000c00c5050080081c0340904c40b1212140c004d500c0480400b05001c1405030019a03070810341c002d0741c0324501580303110b10456510300f181400c048036500704509041c81403042c0c0c100ea440320740c441e40b4036641c140c400041070000181070900c0c0203007840001581a5032240e809480501c04405004180d1280141c10403560110500d1092802074864020008806448000f415840340501c1c00f6028024000000d210740c944450710010340c04500c2c0301c12103079103809204000f20b915119000b41d110301c020302040356042082c1c0444841c80103200301c018180f09400348081818070340c1c1c288403580303030350034100c54014135146085201f0000480d40125414500120f = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 913281996 1250 913280746 913280759
    0x90106110f0114010b03040c0810061d102705160f0f0509010525060606090b12010e0915091c02210a02031c0e01050c042403020c01090b0709 62
    0x1440f611002d020340d10704140c0e00f09030003080075810080041e5034907404101c001074500e109205140740000c182c403012480b46d0070148035002d940461407190504901040412010300c401c00e640d4429a0500c0d80702d07104800e001a81c0316040d464000c80e4040491400b010300000d00060700c0e0244c0c4450554032505400482c0700000c2d24820080348150010a90030022000698400d02c01444c031800c1c803484c84181c5505000103036145609941045807065910a4184200c540003c4108000c00242003c42d280c000401d201ca8031004040c0b245e0000050450040303101000300b403040d0080c14048100c021014505070b00340b40d68540114421899416400e900c110300507101051400078030103001d40c0708034542117000030a11030740e02440f0140e00b140024000d044404a00030007400c44041c4401d03001c01c0745083c011207176003103d801415035030801c40d0030030080182038501d48241c402068a0808142081040b4200342d000e0f20030102600019440c1031410310400c1090310f41c1e10b0082d14640e4135000503548542 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 913283246 1250 913281996 913282001
    0x40b0303120717010e07122c010e0c0f13020702030318040605040c1b02280305060a020306030a0809040f06030f05071a0d1505031c0806060403030c030f030b090106110f01 75
    0xa064010b805c1d0380c000b4010f107020712500c40c1c102e0220000016803000d07100b41c02e1480b800c0b916408003008110364640c004c002c003d0107000d0081410f03001030002014803e00090188a00744500c40c00b0b8500140f081317850340700c035605417441580c001e42a40d0740d444800304800c0d00600189107040c81545000c40c04612070409201e150340552850300ca80035000c00c4071821101140300840d00701d90083d07401c0300180000442510a66164a00d050b041c4601410341c9001401c10301d0007406c441d809403050080100320366002501410050b0409082a91850008003180141c0505040c1049981c1001c0c3c00104005c1340710340409406029034151804552a82d12081c90040000c5035161100000d1003071481c55641584040460500e08106200d42c968850100e07042080c11240f207010080300e8030150320f0345a00001c0300c3e079004c1000c980751031a0504581c0c000c0c21131102e0460140c20041030940700d404071030182c2d101c00d03060319008001805940c0c1d1985d00800103c41c0c1100031020b80200034174510f50341c2050 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 913284496 1250 913283246 913283249
    0x503040b06010305180f16121a072c01020f010911130603020306090c0a14010503240d0b100e010b300a1401080f100b040b030312071701 60
    0x40d4a00c41641c46260044000d0400034040800110350180d032040c0b4100c00300101c0c000c403003440d0040c0200b00c00c1d00d900f42404400320341c041d849405c2042c1c1010002141c240511000d802890700041c0640c5541c00202e844240000380c48565110f80c482c1008030440300300d070410b03000b00243d00f140c030a60b0450700401e09072004501e0040c2130540c4040c170543c0a10b8250503903040740c5001d0000083d0b2a50303030b40000b40384c54420b8840680300c1e0000a4250201d0602480703d40203000c40154640080503071000003070007071100074829182070594070300c05100150000e02660100c0001450750005091034281150900c1c0c040d80c1d00090000c3c0404006590700d00c03000018103e414150409051503003001444801d00c16100f031000841e00c9a0108001c3e4894145489019501d00c0705d000816400080b505901048180c024412550005c04400c0801600107807a0840301c000c14004590fa0381001c0114015250b039921aa515000215000c40c0b001040a0468031170300d065610501c00d80c0448041c5080d5800a = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 913285746 1250 913284496 913284503
    0x7090207031e08062e2741060706061503051f080c040b03150a0501150c050c0d02030c0406060201020306090a02040510050f0d050f07020607080108070509090715051306050304 77
    0xc0ba5180c107245c0d005911400034007000c0b80641c1280c220010b070300107880050750002c1500111441c008907050310020301281c160140700900f1411540700250b0541c0e0405092401c500c60b54001520004008031a007058004045000001c3d5844d282c41e0f01c090054034044038104d82c4090840d4035680c0c0d0301c8641030008201d80b1001e0181100700f14035401c4c4405002626101030f05440352201c0701041702940d188092080c442c0050010b140e506003142100408080e850a404112820510720302060703020848500c41d1104480c844050a901e10210342080398609121341e0180c50302c00300064040c1c064008510500046642c100ca41d80c901d04ca60003240540d000325a00001c2040e80b02182c103010310010300e40f807040101114101a840ba030080240c3d4402c0b00d1055201c01c0342009d00c06000c4c3c04011198000c0d19500b4140c405606004404e43d9404140c0700d41c1d8451242c075404210100300a11548018203031003080c184000100141c09441c503848402c09451036a666900002c01034400d600340c0b400b44c3c0e803 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 913286996 1250 913285746 913285819
    0x112030f0810090207140d021b03151f1e05090c0c12030c0d020f040e100b030a0902060c0a060b010215190902010513030b0718030507090207031e0806 66
    0x4110b540c3e8001d4110140449000d0884030446040090030801031510400d03650041510004100d107100300125140c0d191400b035400024584e820305980c000d16a801135002505200207001641d00b00d0501109038054655040390064065250300d1141c0c88074269182541e541c0350945131201013980d140302d2b4104288054109041c850850244903005507003140201d01140d0a20b0740030b00b0080b04980c441c20040c0c103a040c00203020403440c01c002c070100d40e01ca00119181c1c1e2503e440d0100c0c48040703100017081002c0255985041004564550b419201c240d4203031130132100c500d0402c6c9042001041d000d0076550152042980000c06070f4000c0d0140c6104254141c500c0c542c4490300e8440384041d1503122400c030705102c0b0038403941c29800c800340410390045014010458050034034180141c6008610280702403001404401400443c20004140040311805000140c3d10f04050800300c61400c1d10354484a820402074440010041c0c0c482c0c021405254100c90b02d01044d0314913503040002d000c0c40e40b042c4907501d1 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 913288246 1250 913286996 913286999
    0x3032304080703050a110f031c0902030a060b1302040807061716082706061207060206060f041d21090343080f0a02030a150b090112030f0810 62
    0x901c213401500c4503180500304540f800080c0309170541801c510074041c14050b0303c00303c1d07500c21160206220a0100c0c0e06800100000d081d80d03000300741c031600e0080000d0a02c9841d40b848065640303542450a032204101c2d40c0440d151f503110104152601032034451200040e0032000721080c030450b44000d180c06420075480b00c804604c08c0701c00c2903035000c0b001011450364800203d19000c08252200142c4607400c210303005030030949850020810740045004003040c0039440418140f024540005ea02504201d04643d1030101c1c0c40000c0000d07016120307004103200000b0f101c400901d100b0710000381049040300c51030749040a4000004004403d40a0140085e6050f8400b9404141c050008011090050803005180a540a141c0711000700413100a08441100301048810464608148a0612090b035800c0180c0400c440e1500003c2d6070701003082016040d044130407000500c800c510b0703010140a80018288115075030791000c000d1104140d80d541500442d0400d00b00280c0d0700e02c9504440d02c14152041c1409906 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 913289496 1250 913288246 913288253
    0x3010221040204180602120c04120303050916030c0311060f1209010e19050f070e22060c0509090a06060203041215090c080706090b1e070c03030323040807 68
    0x3040c0203001039030003e560750903200c20088004440f1680c13600a280250380c500c0300100170024100d0040521008140621091029000e65450910800c0d0140781c042850780b070f01484c26080c0b078550801e0800504482e140001080110f01954046900480c80b4401d4039101e801844800d00c5400001d80640c40704110310f0800c2e4400c4041c540c0c21000c017400015144043c00c0256180c5030603665203e0426030b41848120401800304403900c850440700c8094001c1e1407030010302c084103010113408503203204103d169426610741a0090a14940d4100710140a103088070f03840074200d5803006c820580603240300c03000681c80e55010b002d004101d03180c51780254641448c180c00040c00d01d01502c030484082d0901840f00c041c40b4040e004800205016040b910015440c0144140c0350115641c0560148045028100b00e000799180982c0e03140340640f0680116800c01c02c03170400d19486401c40040492407024008420b15030300d5440220800707070012400c210f070300b0140000c5048d07003402c80700241064020404803002 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 913290746 1250 913289496 913289557
    0xf1605030c0d0507030b09040501021e0702060403261201060905061c0c090504110d0e070e13032a0227150604180b0102070e070503040303150b071a06030102 69
    0x205440c0e280001d042d080e4980007840d241c4003a10b00761014be401003080c911203100703602109504600e050700a07207403203025404500180100d22000c0c1c0842c10804008501c0d444400c1400301510503040c4142d0f50f0310341d003201c0c110b9104080c007802d0700041f142c10700851541894021107003c69000b06044000d444420040d40c09480710042560030401a4031000400e902c50b801890054410f0035505900c504ca070300c20b12404c0301c0118070034000b240d00c005410007140000c4840c460b003100100c1500740811031141421364090309121035a2003c1490705000c5400c51310000902f01c01c1a1017100d4001108052682c401a0586628040c520452062001c5000c1344525a10551850409021203040650b00d4010f08075601c50010312408040d00e82ca10808250b0381445004042c01c03020400d0070b01c034108240010814003000700700070b0038541d4400681710244032502440004141d041c122aa60b01e0302c42c5044040c1030030901e160a500300140000c00d4a51030103000f66840c8000300404440140100d81c44041c4 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 913291996 1250 913290746 913290751
    0xc0c0812180d0302091e0d06050703020f03090a02090136150602030301090509030a17060f2106090309030c100c0506070504080d0c0b1303030605090f1605030c0d05 72
    0xa86410540c4518001c0d01404070894015040d00c0058440003080305002c40c14010b03010401c00d00c1d00355009402e00d036940ca1441d04686030440c000040685c1d030420107500a1007502d071048080d2402004100f441c01c03000421103c0c0f503100303844c4460b403139a0783c6030b0303600140844200300c402000c504584681521414120544540286580030880c0d106c0e800303403103161602542203000141c000200500010711640195500100705d00021480c0c034a10403402045180c03819080061211007101240c0203580ba4003d00000307000c0100032078440c0b540340e45180c01890f001d440c000740350b0051000041c80070501100384c58850340f000c2c01902c206182c0303004000690140312543c4051011140000021880400200d40700c3c03285501e0781640c0d01d05100880f440e1040d460714a40c10011001031090005a0740c90503079402c10000c40104c2103030700d0507246c2580903003281e420a0382c22500c008100034201021001d480c0c050003a03c1e40001900b041c40307400302ea0703a01c012a4180001c070420810071041d64030580c003055 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 913293246 1250 913291996 913292011
    0x260f07050114090406031a07050715050403031e05180a0b0c09031f060f3203030c1c180b0301270c0909050603030a1b1a1006030c0c0812 60
    0x510f010f00080028080b0781650300261540140f1544822000b101201219048400780c01c240d424000c10303a03a17101e86080c00c07003584c001651f00c48011500305402500f020340c80020f0501c0c0c1a01401a1021010081001b158411040d014022854400703100200703280074803d4008081030019500d1034000d40350355000030242500f5108039005504d00d00350481007085207110003030020030030f6890320451142820707082c1c000c40440c16000e0000d240141001515003076044c00441d901c0002c07003504c0000b0341103003c2c00000798400c1c090f15046004140c0301d548848007600c0d50f078503420041c0343d02c1c0c41046281d4030076008012501e1401c00040c49041c80655003251114285a01c501c1c240004c1c0e0300e03200a031400050101d0226600f21003e1141003035a0180300d0384203800354000c5083c12200c10008283c4451540d030300c81186c0e82030480c00c0900c070140540400e0850f10603240c00442c1008209502d80c00030b50701c030358400a03140200d02c0003194460346080da4582e41100c5181d0804982143c5400014400741000 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 913294496 1250 913293246 913293287
    0x7020f0918070f030201020d0f0806040b0402090a27090519050a0c0b0c10021918050d0c0807090603020d020f040e1f0608010b10120b0604260f070501 66
    0x941e51080200800009060107015040c0200d00d148006413600848041003024009a00300c100005035200d00300b560b12171000c41d0046040401e440201d0000d1103044542c60700720300c52000102c1c803235019461810001d21040184035040c6030000c25201243c0c12b1030f000400982290429468500c20015a240c02038012030a03540242d00c0c0b960340e9102508039500ca541c800c4c0020451081100c1d09000301c03c41303072231614015480c2c08004442c0340c1d030400c0ca42e101101407110410304240010480c80000d800303040007800c0c4440b0001c0c0c904000344401801d2154000c83d20601e140410480d0741340c040c0c0401c40380e001c0c2044448040d10350030841c0c1c1c50b2080ca0a207402c1559001540d140000070003011144440e000380c104401d642400300402502c1682d00542c1c0c0684c1082d83d0f8009a0711142500d40710200c0c44c0c6400d0205401d1844010003512069612540c001e10119010030f40f09400003904181d101c498200102c7c0d900a43c018a442e658010b00340f10760b5401114081102e540a203581182640d14a0080e = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 913295746 1250 913294496 913294531
    0xf0114040f060f15050108060307151b170306120a080703030b030c0d150b2209031b05100c080403091e170f010b1921060e0d0207050607020f09 63
    0x20203040b200300c0c621500c0e130400014002c100558202c2d09941d0450025009000c1d040c1c1072040084081c0110b440e00b00130040281c12100010030346580034020668000c080d00d4202c00e0590020700c05802c15151a44030f2445030040003440340000903520703640d0b90300800c610709160f4a514150001c01e90440d5068060047e0160f000b0995039240c8652130044c49100c4040da103248030081c010865440b841c40c240109403500203a02c00b00b0102442d06000541900041500702e6a4941103400104241e203554010390032084010070840e0225802c01f4890620004002003015078908448951060700c002c0c001c42c0d8015020320407030002c918140e00e10134040548030011a46e6007414010114016402909900030600c250240d0740280108101d40e0300c1124a4081148031003001620045d0318843d00f0303400445000b007903401e999200003d40901e600324008000c909100b91810b5103400c0720390002c00c01030140c4400403525141210a50b0107858019154550701c12212041c0b2160000140c0090001b2038100d10 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 913296996 1250 913295746 913295771
    0x40204020702091321050d18050d051c05060607110a050d03050408010501140306070809010b1c0309080106120f06090f0c080c010311070b1513020406020f0114040f06 73
    0x51150042c0c804135829501035455041040640034100d2601c602050000e80750300c0f45a601206070b0348200d15141c0005480500280311018840e01d1031002052400303000c512000c1c1c40e802c40b02070a107529130440c04603035070304404940300122a0704980199001c1818400c240201d80d08800101c1c0d038070b1015000e0000b07135480d5400500c00c0103d0742d1040b00001c90005080c0011102030145074018803540d889000b00c81804000203840d000010054000c000e140e034005040c0c1c07602500f001c1e00d080000303081d0103d84441941030059115190340280e002c60784034940002d500340c0511500741107540e29415840310110594681107001207107070050311215107666041d80429005161490018071801c0340500092411400c00d06008501c2041030600d840e015428080c15006411580c12940c03016220410b5a0f444000b031a00203115041584c11201d00c126421070400141e00400c1520059001ca4580c1040100d05600341c1e804840044200d81c05200840c00003140c400303600d070000b03100d01c8010591519034031707 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 913298246 1250 913296996 913297009
    0x12041a0304032f1006050f0d06061a0a030b0a0503120a0512100618030b06040b061909060e030a021003050c041502010c0807050309060106140c0304120b18070905040204020702 77
    0x5111080012111054205001e801c02c640701860310303060401e11060385483c002407c40a40106054010500f10032044d00b0040f096202001419405812030350308038147e4a81521900101500b00100c0c0c901903550307429280084060003240d070010003c0014001801411205070001d01803102800b00034080c1403248c150300d031307043d9200e00d035944201c03085640360500040c98022403806289510418040902c04240c0d80c02c812907214000350381c04a11403400d000030482c2841071745075100c04042d0144403594110761021440041394229034070300030301c43c01000405894001450000b50b10691007500a04218025084540c0c401d14040d9080e00b099600c5c855100e014038032540006c0180d54071075980b101d40da008030380306070001038038904541185000054960b45400c10302902c814803800b40480105000a07070103d42c003405132141500d446990f10b40c07240a1903c1025000c40742040303c0c07000030700b50382a03030410a01c0b0803801c00011b00c0524940541d08006020180090360403640030001000503840301c0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 913299496 1250 913298246 913298297
    0x3120210060e04060c050f0403260a03051501020d0e090619090c0f0c0807020f03010b0a0e0108010c080c030a05100b0f121602032a0f0a0512041a030403 67
    0x12020b84014900b52a0140440e81720088480c1400f20174040415800c00d91030503101600d41c0b200a2002003241440006200f001c0c03404948224100010100da4466040c2c001c9409a1601da042403d42e8241000598403110301440041c0006c01488083c0018502641d0513500840050105000e6402c144d1a0b5900c042c0181c210030b079526255803d4901140e8008096400d46c0160b00e090490b85a56039220001403050f098081d2203154514402081560294802c0e000140c00410b4403858a44d11404179070420402d1003460465440c21f010080b910b8092940305101d000701210092565555a0509000b04405408a0542d030700360000400e42d07060600052486940e90380b200d0392a0000c1ca680085060320041c4200950914091543e440700d4002042d1024201c422003001c1510746003107034a440a010b0004032112a10589626a03041800400e00440c200d0207042525a1a02525603400d80c40c8503a20072a03c2100d60721446414120101c0043c1d81c0080c8245441e02e9645141001619480c005 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 913300746 1250 913299496 913299509
    0x81506031e040f030f23071b060c050f0a0309031502090301090b041e08043309060207060e0307090207050f01141503060f1b0d0608072105070312021006 67
    0x103510070300705141c5c01c9004110707491424605001c100a41d6601c82e0b5150121821400655401181290400007401228034680e400340954480300ba5440300002d02d26603d020043d03945003d10410020511008510185c0e101d8154032580320f0603203184c0c0c41c00f83d16445805140401076082c04803540b260781c280101010a4010100d110f02818942851a6845a08410000038202d07854200c000902039070146e40c2122901400080400e0240e0000803919207002040c00000209449690b1520f0308681e140b01520610f6086400c41c43c0c55850540b0600072241c44164903038800ea500b08080301e256001071401c0c500c15001e44104600826280d403c4d680b40544031080000d41c00b00308140c00c00c00945c3c2007607410044008241600300840010051100030b44109a041c07464408488034000e00c60403070f156181000f0041198594420f09075840351a0390169180002040350001404200c0050b688005500170014181e03543c9140d5484141e070b58800c10110550080208015402800c0c1c030694004184 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 913301996 1250 913300746 913300763
    0x121020706050c03091c2703060b030304140d150213090f090b041b050303040e062e0e130608011e0204031e030c061a010f081506031e04 60
    0x3480c5800400c0d68002040d14607048001e00811840d101d00081d800e81c51034000d000303485101c0040208a43c1c0001400200c603850308040340d403e0812554101ca44100c9005240401c054210f010400d6120f22491061043e40d80b500103000d1000d01c0e181260440561150f105d220004100100120a80c1c10410240340440c1588904010341111801145103105050500700f11081842e503c0b402c07840c40287c00588612800d42000c80d502160301c107000c02070080207049036103c664503446000b2030001100d80c54040e02d603411600e0745000a40703010388015400d0b69000624008081003c0390b5507812001526400840395108800f010070300c1c0b041c0360107048040c3c00801c1000d95010402850450004400c1000d4410041000461440340c07650000301620890340352a5501d508040f42c406100c16005402d691400c800000078503501b02c04405007000c01e0326002c801c4154060240d8518800712a5480d25081031550000145044001180d02404540010311400d0941c41070103014031080390216107812 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 913303246 1250 913301996 913302007
    0x1719030c030c0527030a06110d0b090105090406020c0115080a050c0f18070c150603030807030c3903170c07020f12030d0905160b16030c02012102 64
    0x164107002d0a1100950740c18030381d02c2c200403c140304580652a240c0010110712458681050f581c0138000c2c0000d264100209010b40c1a181c1c428240359440f00700c61021143c0340c01c130300b5507007804c000095604031074005204e1b01483da03840e00e84601940c003001d40e00103555a00c00d800d0f01150211000c10001c2d003040001001d030401580340017490301800d50740c400d100c1c00c002c24010605654031032a44181c00040da201503c80d40320520240d52986001c58010245d52040c1e40d10501400e60f0341c803010441703001e65a4484c5039114a0016411550000002e03c00540b4074101ea04101d080315440f80400e00300500602c44114440461003510344500c04120002050b094581400301141d80b4625041160040c150749880341d1580001c2c2041c0c182e44807140602c85111000030500c0050059404426901505115070310f96031800c69158101056600305c40d01ca40c00d000b060b40e20303154041c1d81414820031406188200181ca00344c0321001c551200320b04000c1610308a80380608092011325401440710005070310340c07 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 913304496 1250 913303246 913303271
    0xb0a0e010608010e1b06071e03080f06130c0203163e010305060f100c020108090106120b0c0f0c0609070608240f1809010501050913171903 61
    0x480c1d581e0b20408403681001044550b10310301080e150441e800806103a440e01a0000210b0514000c4000c060101152840003404840803000682c01c031501ca0740d994039503956086204602050117071003e41e002110160040c0300000c00c0c1d4440000c91040e801200c1c180800071401805243c2c651800300e40d84828042246940484100d100a240181c103030b151750034200d001c1c00581d000411a0020b8100342d00c1d00b0118000791140e45001610441c050b0000305080300d94038001e0110f44082030304a0015180c0c6c000103d400b007061140d882502d86410340c2d4041a489a1201c0714004005072151000240400c00ca091031101c040051441f407048201034926490001c014905114a0b980b0002c14458a2800c0003118412076040307925522000c00510640400302000c51102e0a48005c004c1c0c0000c0030b01e0300c041090341c094082603c20007111000b40700070307a02c840520400c64810350302c1080301d10745d90f0030050002e0b54020884110301e00e0084641d0525a4281d54482c01c048404400c80210703540d280346581e007 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 913305746 1250 913304496 913304501
    0x11030601080303010e0c0a1202040605030610080603070302240a080711010203040825050303270703080f030a15121a0712020903070305030a030e0d020a020609120a0b0a0e01 76
    0x10080301c00070b50304541c5040005a8210b0005004841c0c00e1300006003aa0020301900495044a00c03040085480301c0e100d400160040e0700c29161184950302c44403a211469200d884060310800000d00540f403400d10b907034280000b052111f40c06201038986501100311603100c09000e8401a101550342c01d445041401d005032140900e07801d01c40c0d03164010403c00010849210072284002940345c8500445200382a03410612001140d000340303280400008c0c4075094181d15000003001b0000c0c01c040150781c81c090005651040e4503c4000d100042c00d100070304400c0e003001c000e141d04c50300344c0c0301c0810113070310074401c070a80740815821007a10800c94007002424020784070146058100d0000741d4860740d04104002510300400e8452003e60260002103010080c0c40502218006580c02001c80380c9450190b20003174003506201c1c40f8011988550300480036264400a1205280e039000751100d031030480008180300c0c160b09991040e0750a4031a40004c0e1001500c0c54203214450b400003940041d4411704520310a09 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 913306996 1250 913305746 913305749
    0x4060e0f16060509060d0f020417030f0a0806010509100f0e0301021801030b0d060c0801030614092127030111040b041a0f1b06090c1c030201110a1d100c060504021c11030601 76
    0x4070781d4424405005041d0cc4d15044807035605007030070411660b50b2114012240d512680028940089200303901500b480d40110701511010710503200c2040c1d4880c0401450300301d00501907a800741d00441043c08806500940c03024450100c041c5c0002d240d01e500f0303122401940e18285550340000c0a14004000348651841501c00c060078024140d040c0b414802e40c03440d6224408000c0d000c90114210200c1d4a600560301282e0105060085250303101c40507101d5284d4540541e40c80600079420508880180d6030750500b260142c4000140e01030403c0c1c1804000701a280f11040c0412600c0c0c02003183c85500c807202405410170481884d90741d0300700901c0756001d909003000904550349a5100c0c442c0340503542d440d903c00c1d040001845840c00c101c0403030350801700e0261118030898204494001100c5c10480e90081404080e1049030142c3d005500141060203900b09007241c8180c0002d046080b4080020015001203802900040c41d40c143c2400280340c0f015021030081040350010040c0301c081d06c0781c0c18140a41c50 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 913308246 1250 913306996 913307039
    0x30114060f0a05130e06060a030e010b0d0f02190b0d02030a06050a08300f03090a0c03030f03060b030708160311031f080a050a02090703110304060e0f16060509060d0f0204 75
    0x103146e0500b040416001d00501550300c0c2419241c05100c0041c0009502540080d14010046006c49049003080c021180118400360b0007400d401d4503a14800640c800d40404407800e481c1043e02d00894621b030240250006040d202c091034948000149030b560303111013040501940800b80500c03402684011f0050846c04e0860301d40070107284900b10303010f000201503400071948901d150ba541c2e6038800030302d803c1c10340c8105d0003440359003248408401c0c10b0340020210b825800644003000802c0c6c541201807035a0008407680e40c00203118200080c4517804c072001c400c159030343e903041c089406004e14500c025a40c100b101c610001000c40b04c0c181c1d0000b1203845515004ac40c0010142c0404041610351903103d906080c030180c050720310310010070b200c00c0c0b196200c140c031a01000342c203a40364100361a050000d000d0b1426039884511403444800780d010300c0410b48940c07460411152018070b40c90b19038156440e400403400d440e0700100a020100c0821032500400200044422005903103900f4082100322020120042d10b = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 913309352 1106 913308246 913308269
    0xe060f03060621031b160e04240525050c061315090303020d060e060a0e071403010b1b3c030706060f0501050906030114060f0a0513 58
    0x1000d020301120151a07003901c080c81502c40706d04250080050001c3c8003400700300000c03401d9000c011104001281186076501580f41c400494204451070641e040c0c95507066400c81100680081203000f050034a03e0038500001c020507560840102105000501362041000344840304400c405220b80c0114144840b10f424640200a50042c84005000744d081c03001c04184841c0103881c4501c0b0314005041482001e15004c0748080d0500050044400e100d1001058101050381c00015400b030b0168403042982e800f1050003114401c004004000300a80000c00090300081d503003680c0710340940300a441c250810103044d09005203440054503922040c07000090710400c101a907007046044513181c0420b07200050ba103400555591040c4112a948000200014080054007481e0350079841d001138030050416140076200346041c2d00540d0200081280410b25a912280725141400a4624400078 = true := by decide +kernel

theorem cover : BRFrame.Cov 913129496 913309352 := by
  have h0 := BRFrame.cov_init 913129496
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 913129496 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 913129496 ≤ n) (h2 : n < 913309352) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
