-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0533
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T20:18:01.292719+00:00
-- url     : https://prove2.me/submissions/6c1894b3-df44-406d-b26b-a07a8698368d

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 95683453 ≤ n < 95863309 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 95684703 1250 95683453 95683501
    0x8030405010209030d0306170102040f0e0c0c06040b2706070f0309050106030803070e09190507030905032701050a0905060304030905030a030c150903080601181509030b010803040806 80
    0x110011400e0740b130900c601c88040301c155400162107410b000b401140440a080412203683c81804103000e038401514090055400700f0352407015955504014070060320a80c100d1215900941082c003040103c1240c1c80b6000b4842c602041c0d56001c048040031020031205442c0314142d921440215540601030628102100c00914010941c13880648640782500e209500c11108032000000308149681d202c0d240081c510800c0b104d20005d401c2c9603031480391500c420202c07030a4503035407100460b5400d4000d41c1703d0044558018162034862025400241d000302050b0302170600d0310800100400d507503202d07200b100c0c050311058039003102441c200000c2c4449500000c000320240b100320b0b100415181e50822107000790903c29a100510700450b450314030b0650421100030580c103420b0803444400241c021000c62b500c520203103401d01c0018008554811785a1482c0e1041c2d694a40c0782c103101101c15482070320842583c2c01740c0401e61450f6661082d15980e4070481c49403d05075080310380419004001c0384c0509050103400 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 95685953 1250 95684703 95684707
    0xe010b030f030c1038040609020d0b010206060a031e05030f041e050604051e060a0306030b09030304020d02060703020a0602181305011a090402040e04030201051801050c07080304050102 81
    0x440424904030485407600c800d039101141010071854200480040c0101075a0140304112043e201070450108818091348000201d9041c002800101000244e002c00c00801c2840388582e1601400001d511846145403410b00304803101c1ca0075400018158010340010382510101891621441c100d50b058850b040c05100b0140048400704a0070009031409000d440b01460740e0783d10302220f026600c3c22026143c0e404143c54101000240d48000583d0210761058443c00190344100300c003821004507188403103030b0010300800c1026186500d40e01c048280c0e4441c0300000c100362039405c0300a50301d00003103074002d62105d4004109001402c08c803018000f5144240111584080f41d559004113a03000b00701c07001070f4002161684902031034410207007204040c405408000b99414110300600403c0e1015180c3c410490001d010595070301c442e41120001d00c0481c0128410781842d10380240038102c01d84078501e20040d0070b480c1c0249880b040c0303c0c03580a600143c0c0c40c04c0c40c22400e5594101141c0000b00265102e56003 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 95687203 1250 95685953 95685971
    0x1e0503040302090703020306011e050703080606070501110405010e0409020a03060905030d09061401060507050705011404030b010b03011707080a0b07030905011b0f020111030c090f0a0e04060b0d030f030e01 90
    0x3d81e5a458022050f40e10050303180e141c420001041c60280100fa01c0410309009000d20032207402204480040c0e405103800203069694002045151154100c0180190300e8240c500c283c080d580e001400a4500076a1003081ca025000104401d998050340042e620041d0b2741e01c100000340840c3e0100782203520490a42c0e0510264001c1402141c1074441c1c00d8400c952107048070343ea04640c0d645c000e40940f005003001402c0c4140303600d815541380041d0041c5070511418004501c040c481c4041590000d66100700389460940c0c666a00c20074941007841200500307000814482c3e00c42002203465415210a00010b040102c22600c1d1030b60440405000801850394a5a058010510a0142080010f0001c00010b0b8408150324010030012460380e11808691501710b030112190b030b0750310840740c029078100c5246440c0c1401e513000070300c0d50410305001d41d0320914440d400199854800403032807185026000400c004400c1c00c0078801e01501c1c150008002842000003031305014069400f0700b1101150f5000001c86450b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 95688453 1250 95687203 95687209
    0x15090b030c090f0105030c01050304030e041e062d1802031b0c01050915090a020609040f05131b0605030103020405090a1e021207060503060d080c01090c1409041e0503040302 76
    0x1054603d08201800040144014203081124811484081c80c0c524558502a00c0c01401c3d10007032003c0c0e80c440e03a100c83c900d840e030014008801614000d07400e020855555101010110100d06034040d00714001d0481d8440d145407499400c1004071a030304c070b000d44240d68030010751034000d52000b1311403403003071458101500c485141355003c1e00c8400b200a0001900e8140111128079100d80d0035002030002c0200d04c100410390301d020032460a46a0b05550541d142d041070000600980601410114044d1401c0c0400403800c900c1e00c40c05030303842d005650107413102d42e20480c00d0390803c04038080c00c0302040b0108010801824203601059203c1507040644010b8016541c0d000d4564028010400040300740c000306505500c3c01400070f503120801d000003000000d240c40c86c080c1c00f03070100510302441600800d0850041c80504022511025510302c000c0280c0324603842e020000c54103e0042c0c0306403034569440c00d41281881c9080c2c6008a4011550416080004a0f05104114441012a8940030900001006071 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 95689703 1250 95688453 95688469
    0x117100b0403060606032d0e0f1903170103053d0204051804212006010f0801050f04060c050d02070b04050c0603011d100312030f0507020115090b030c 66
    0x1d031240c0c00c04030b15285040402010340d040c2d02c3c400e6401c0201d244030301035500c1d1f06035580769580c1c0b003000c0081107000c0c0319581a41080c001240440307950281c0506028040114902e4064251090b1585001d4120700c4c000c2d0300c0115005d000040a81d88803444c005604841c26001a0004c044442c645060310410f0004e0074015002d200c031480c0268002ca014405858290b80b15a0050609241c140b91454141c07654100f0710001d180d4101e105d4404121010507522440c40d48482e29481428030311500c1100e4100c9a403000309100b055400e60300c4031000f0501400602070796001d181c022000d0000741e2120f45848000740405604d0109000342004a0a441b00b02e9001030721409000e004442d906151a003070450510000d0604184914401c1006000c50700d54031000d980000982494291503a85000c41e03940c080203282c0014294207040405106000d506070410303001d60510711803d0000780ca490780282c1c280ca2144d001012248655141440440010361046440000c01000c03280c1d000000408074441c6 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 95690953 1250 95689703 95689709
    0x71e050a03090603050a09020303030606130519060201110928210203070e040c0603020c0102070b0c190f02151009090302030c010c170f040609140307050c030307020117100b04 77
    0x820030050301048841e4051082c3c5031b01c4050720900344a454140e9000940700d200003882c491081c80045030002c0d401c40307000d0381d080180c040a00700f902e1020360390000c454001441e201d00d50040d030070303e00d900c43c1b05074918040d201640c002034500b0404501000843c5006440d00b03845aaa07201c01490010b000d4a196407100b40000240f20486000f940c01e005040c10aa52a04100801040c031420b20000445040e01402211028900180c0790107514144502902c20b064010f030030001d00308180040c00d600741008002d41c440803846180040c000c0c0c0c0c0161003a0154111160168200507074440c0c4240c3c0e01e21026600c000320b440003040c11070b1505030100032078000881c25001030b0300129402030844024420001c1e65102030400094400300311065440f42d5030010714401c110406000031404000503500442d10040e44849040003003001580860341d41d03086804242c03820320030143c0454441c1400f20854032102d8041c0e42e006003541c0c0b83e135110910004094038901d20309031401000102e10524201900107 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 95692203 1250 95690953 95690957
    0x3020306041b03240f060f1107140f03060c091017040305070b0f01080c0d020117070e040b061606090311030a17060f0f01030b060f0f0304050105090a0305071e050a03 73
    0x10003002007440e6900805480040b840000400c400d05c110001c250080703003125140d250602c014244400103c170003125802c020260792040420204003000ca010241800c0d007001c0d9012020418400c0c1019900e01040e40c074200e4030041004040e005042a001c2d15451121604064070034181084000902d40c1c2e04981c00c0c0d0000f0004261403040240300009150808414142d1012550400130300c81d84030b8540d40344d035500c6034452a002c42d00716401001140103813405881d09034064517001d1400b502401c02000020b201d14034150342400d2030714007902520a51841c120031888410180c3d520f950040800f40300170360a110700b18035540b00002c4c041004103103803081c0307130b0381c8a803072030f0641144410076900035000501c65072440010000a8552a8224600200901c1d0208110001c000420300c83c0c400d882ca404041c040002e4103500d24480e080046009520602c000c00560395040000381c5c5401e5081c13030040010b541004108041400c02030b04404035002156076000d844025606ca40c50040000e0003100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 95693453 1250 95692203 95692211
    0xc07020d110414190506030607090b130806090c03250509040c051e010912021f0513080a02090603070605030411060f0a020f070f080709200a0c05010c0e06030703020306041b03 77
    0xc00c00d140071705500130b001039005000509084a0140601d80c1030f000700381000401041710141c4404500100000f04512002e40f0f42e1400c10321b4040d5218014208803500a03c1761440704007904442480718180c103504001c15407215400e02c01080325407580600141c82d1452107000102e450742c0c41103800c002c0c03c1450b03941c41030032492400c00074102075096440081c60787c05006444016031960421000c0d49441c142e2a4140d11452090603105801583e04000300e00c00031040200d00c4040000304180064003c8484030481c6da5108205940c0c0c0040303000322800500240045000929110181c141d04000200101c0c1044000c0325007000726007142500200591284003046031f6044188a07420190001204142000741014061561944244603882000c2d50313420540d4906003500e4103104c42a0041007126a5825800c04010050801d00c41d00b5240c0e54030300410210043c0c01961141100600a1312a074159a28110300381c00940000b007421343c02c20384440e20001071020440b00001c240d111610002 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 95694703 1250 95693453 95693491
    0x181d010216170a0804080a11061006020f030c070302010c080f0d0506040b0102010c02030f0d091a0405060f01050f01050c030d050a0204081009020a0311030307120909050c07020d110414 81
    0x801042070b40101030704400010410400c400c1d900c109016400b6411058060b603034180c1310f4080303414000144030080907008000a00030702c18400c258035010ac0c2c2c0f2030f46c215051261803814003030701d1384208061001964051001080154003036843c01c104640207a00003401e01982c2c551001441c0e101e200a0a10980d4900400c6000d01d82072051800c018001e100800207811420006903492041c208016502070011503400b00d40c8429821040b083c0350300207103181e044084581c210942c0c40060f00c040380c190013410002103040b4070892089049950007410391456a18902c019510755110390055542804200f00c1c4210109850290780d020b4121844e0050f0741d00d103000f81b054101407c4214181140342030681120141e501c050122064980099a0340420810304000910314071540400400441e082144620101c0d0000c0d40c1c40c0031680b404005119942d20f00000e064039200c1e03403c0003980511444c000802190160800301c0340c0c000003400002c1c84080800600e0400d040c2111f5034109140111059 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 95695953 1250 95694703 95694713
    0x6181b1303120206090a020108060409170903011413060522030f09080d0512090102070f1416180b010207080a06021905070c0b03090c0406060e19181d010216 69
    0x7015107403610103403213241011020a6211080309101030b0401c4000e0340422400d039216400044c0c0e146d441215803c0c500c400075984c0b44160003004071030340300303510b4041d00302a00c080541d0094030403c5940031483c403420b0295514401040b0183c24007080300d80396a4852048002d44440003e0b40d402a262810300000c3c0160003800811190803001c40c03038021141c0398600c9030308907056400d11a440301d01c421240c2d0310134580714028011003201034050644c03080c1d02810303c0f4100302807504044603041520b0403c0071254000651001d248208815003503404a0598000225030001e000c03080c0510503241103943c1c80707958a1800b40c00000999409900190441c3c01c420060898001c01441d4140b490510755940c5400740000c03c140b06980c03801d80c00200158034071900380030719080e0040040c03003040000e071182d0b00141b031a50f000c02454010034810640c804400c0c41190b0303640440c0da2680c4008102030f8088035030f401800d9403000041b40300c6103903e6802e004400a00262004182c10800e155000f400d40c281 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 95697203 1250 95695953 95695973
    0xb041a1807050f0d05030f0d0b010c0305090f0f06030901020a020709200a02030d02070c030210021b0f01090e2a040608010303030b010c06050702060115050306181b1303 74
    0x48442102240103481404901401140c40c01c5450b0340e4241d98240215140000080c0020020701001504014030407161018005c04003c0e100100b045000200055a41c1a080d8801401080c028000b4500505d40742e00308810020018005804c01d030501d40c0843c0c00c0ea00305031072402c01ca0750045041c405031681040705600800541c5824048039082e40c0f440281000307401ca13070200350203000410315920b500030011140f50400e40001155140c00504001c40d12031906d0100300d00c9481c9a0780f005103a80d100082103051100081c0d42c81c0045107a60003000f0302051816200c0e41400008140014828004d1841c980710300302c050130310600c80410080ca420440204001e6081912061000740401070b0300068880c103481d454200098800d6a400c01079510310896280104550f05050402240940c0030620038101c40c0011041c6081c940c0c403020a07149400111125078214a4400c1481c41c6030208903206c0da00b020001404c14250081d07118000b0560303200d40f000d0b812003d01c460041080000d00b04e1 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 95698453 1250 95697203 95697211
    0x20d0911030123070804051207060c080717150d0b04051b06070b041e08070c03020102060105010311070204021b0601120308010512060f04060f0204030303050402040b0a0b040308070f0b041a 83
    0x52110750442c019628903c94040260080e000c0020220010302005010840721092016006400d611500c01d0319020000e400740d14528400100c4110101e01c1c0c20740143d02c92010954205e4105209075605100007000c11000d224071070380039201c20091310201d4003444507580a64001c0c030280102028109051400c030308900b07c180c0c0180c00410005001c640320515040e0002d6101c5c2200c41d50005e61907001044450708000a8002400020340700c2c200b0090782d510740c003200d2003a02910400d80e078810043d0121644541c50746980b200c100b00c1f6a0051030a07900800f840c11401001410307140c03080048915001d000d0308032805e0000c10507500c805041e040708500c0e0061a04580c8060a824142d10490326000b0185c01c034240c400011010408100c02c5403c5401c0310380051130215161540c0c0c0c107005024003801c2e00e045c0c1c000d03485d103c4401518240101550250f4584070320061034545555200080d652240c44c05a402c0c0c1c0c62103030783d180042c00662200780079030701500c0c142c810310700030304080284510050 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 95699703 1250 95698453 95698481
    0xc13020706060e061c030c170703030b06090a0911040f031407081c030e120307030614040b030d080c04050d2904110607020105120108060103120815060d020d09110301 73
    0x2001c0101079655942c031410142070103154021041014034080ea90424030080081031840380800d608238050500d00540400f5001e9901400311402410511106214403104103030415020101842040000c0c0c01c100e080d000b94401c024a403544c0c13000900d405920b10f40044880014040e4024070415080120304050501d50025050700f2070380f4500d2211501090440702c051680310b1034100136203802400306031114135a075111150340f894464001002400c1034018168a03a205424400c0d00741030921481d6414100540203024040c003254043c1c86400000305000300300001007101142c1921941071840820748281440d00a04910810325500110040740003820503880200700008107900101010010406680455803000c0714001221544219440c07255100018000001c000f0340004810b81200d0290783c028128105d1040100d40640e4281c0c2d030803c0394003546a00081c240740c52310040580d07111105005107040c401052580c11740d02c1c130300400c0d2180100c045680c14641020f0246010180002c = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 95700953 1250 95699703 95699729
    0x51b1803060a231509040f060e03030601020106060908301c06060503060a0b030703090206031314070b1903090203010c0801030b01080a0305030c09040e07030f02010909020c030703110c1302070606 86
    0x80c22102c400800c582d0305c1849113801080501030010038014815410002c10b100c481030000c8220758a03442512090700640c600000002c0c4030388101003410543d0003000c040e040c02d40c883c40c01e0b80c83c1c02032810380c14007140800e001840400f03900c1e400141001e281d1006980404042114180c00700c0e1280c1d4000300a2100410410107540c0c0e8861616050b03d1411500503165100d0000880007041d188100a402c0b40000040c13001c00a503841d035110800b48903080f500702880408219030380707803529842003601c002820700400140142010301c800c2e101420b80390001d2041c4240e00040c0c29201c101000c5400700b401e01c8010300900001210007800342940d5001000710242c1580e0040c0a0300c8010040c41c0e40641c0441d0380011603459411400416a01c0000c40d4603040e140c0c200807403d108c00c01000c074003069100d6000240a00d20b4001d450115920001440c1040c10b1b5440c1503170310048101400e4028022100c003092255169072610b9440c1c20b444100680341d40440c9400c0d0129074550300081409112 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 95702203 1250 95700953 95700961
    0x801050c090f0907020c040608150105030a020a030b060310020403061509020408030a0315090e071403010501032004090b0916050a0b07080c280213051b1803060a23 72
    0x15150b4405001c00c4280c94800300d079a10024200d051220748454160b002c4c0c10304000081c00c1400041c0100540b034000c041550b540d984404255461142e0980203411640c0c40b9803c00215101125090f404403000d01568200700c1401000001c0b07901a030070840c4e034160365009110040d241c4408400203003211300000c501d03007401d01084696a00600c00c0c41801c0545a45038506400f10b5540071100074403450500f030000d0750500d518151109101d0241808050303e00200781910f14050041c03e0489411082c0c1c00d803c030034103004642c0c070600305201e1135800c0717511003c080d0000380d80c2046041c440c1090b00c0c00390401a1006000103881040d55004a209c1c5034250700610448803158201c40c9a43d5020240315a40c29150413244d08140e41401c580d4001ca47e03517010140080900d416500c1c4d41442102e03c00390a8051304240e00842e5001c2d0303249d60f01060640000a0a12403010042151106125400030401c0c56480007910f0f0540860340301d64010346481002101d1188170b024040004000f08124540e460 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 95703453 1250 95702203 95702209
    0x80711030a0305190c0804080f0d081006080705070506250314070e0a0f030503090f031f0e01021303050a2d0303020d021204031e09051f090509100801050c09 69
    0x280f0301078a89490441d84044c10803402811681d980962001d042d5444030b40c0c4000c1c0d03a880340030201256050307015800b03094001c54401c45540b031281091a07103007030b48541008401c0342d0001c0020704480034000c08010540c0410001c202c05880b44c0450388074403215100b2170030140c0c280e141c040c070001c0c02d150070038006004004038041a9544003ca0781703000703187c465000c0001600c01c10347c0d0380142440828076401000340708000c801000031032030680d804c5001c07005046c145503803030a448211460681c281001820092950340011980e110044000341c208110202e0600385008a58801c803203641c8450f14000411802c1404080d088150a801d94941841e81210700c64440c4501c0b4000d0170507038001407801c4e21390000e030305450014a040c001240c880c0380c0b0b450080e00c00f1003288107201180040c0100d55240a01c2980007000780d8802414038020394108460307a003501c000302c805030014010b1881012132292200b070806441402002e03207100d412031900c8046801c403680039248003418036081285100d291 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 95704703 1250 95703453 95703457
    0x816260306190e09030c0115080a02040f0605040c0816050a300c0206070207080d0e0d020a080607180f0b030c070c090203090309011421040302100207080711030a0305 73
    0x10300305590304a0140c1e0040d10304a0740c482c5a0b00000040000d580901a0000000010300082207101000708800c110300000d12001c4189845856815400200c4010050410b41c10040d0501e100d42d6010600742d840310000b0b0140d0303602e0401d60340020348410800c80070b025000388000314804241407041c600461140020301e4020b4140b4804d01c1c600740300080d01109000c1001da01d42a031880c0c3d0381080f88443d10302009403942030560301f00b4014031907042c000c108480042120300d4501ca990300e5180b038038944842402000a0310120590b480b02c00d0079000a8040800e10a1500c110600da82c0c000e1540c0c2e01d0f05440764074200e1500191410002c0100074002c045030301046035044202c000101d44c560b001441c0c03441411071f141d00034081c40f40c004414800d2017800007014004514090320780a02c80c0e075000d110038a480c06070f04000c2c3c1c0c0002c61948000c40034002d46001d650494000c0c07065400800b2494821001c0c1c2e40161422180041c0c009001800d20400207810344800008031302804502e0340e40d8800911714 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 95705953 1250 95704703 95704711
    0x50f06060a0f12060306090209071701051c050f0c0a0806070804031407061b12020c0d05071a0f0411030c090402060d151203030b1f050f0708162603 65
    0x1001c040002c0081007030003802c024030b1104490f1000d0094503142d19020010f460b42c1a0128000c0640c103011818680c02005003044105040306d060b02c0c0c40c0c1c03a2004100070a40180201001152860004808030303505111000d10034202000912448000b507042c00540c490544c00510f0540080b002d10602c03036407146040340c020343c05107002c0244c211907034140d4903680304040e0014100740c80c044225000c0140d82d01282000340c801d03190380800d4241d007221a01603105464004025412840d80e0a480901410207401124095054021038041050300e024480c00700750388110b20210344004000801a904c0d00250508106601404c0b2910413032000c24150180a84000d22600012850903a4907901e0307030084e690707802d100058419543c1da5407600c4481c4010564150f002030b08151585041c1d09100c014120f102480302c1e000e44000711120022216900024401821203004011600c00b240554014042c081905203451910b12003c0c035101d1140000c64011030101d480c64001c079814107075060141c80d40 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 95707203 1250 95705953 95705957
    0x61605161704080303041101030c02010b0109150207030c09020c1608060402010e03120703050d0b150301090510050409030210061a043b0412020a170d09170d050f06060a 74
    0x8000281501032280d80640d0f04911a1444040b0410080c0030041526403501402070720101322403280100d01300d09030342003640c21a0220b2076030340b010016410f91213140000b0a0482c81641d803540d44981d240128a032a5511003200503401294141c0f11140600c11000301c0910b054144810300d107000c50581e1503900041000c0d06110050380701e400d41d600c047c031920300040000d07d5016607400252030301504a4110b401c3c001017052810b40d000d00c00d41001c0c00c69440340300b8078424250035a031078421504081e02008001040d1020000300c0083c040d212401203100d0a03100e60042c04030360700141c2c3c03a042116200d90003841c5c06000d40c00c08000e03030102501298213490f000404403441c040c0d0315444c03050419002c1c01f01001c00f100c2d002c4125211116602c024001d510071420140c00c010582c404a13500c5145030780140c10008509540e5980c40c0310500285190b8a4118011030350740c0003515946002103072105002610a00052826884d404038030816501c070550689061181c1031400200e441e038042d042800d82 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 95708453 1250 95707203 95707223
    0x718050601031b02070620060103020d0309080d0809010507080709090b0303040f0306021909050906010507050109050f0102030a06050603010f03110a03140703031d01080f0705070f0506160516 84
    0xd6440780d001540c1009628605103070b10000c03844004c0d5240201d129250014000302c20350b1585850f2903400c5208840003070018101350342143c08010301e000c05e0304001c80500c4850030002418038005d00c6030045102e42c0762640c40c41c80c5440480c0c10f0075518000e12681c00c2048505c104115140c000011100f50340c40307801d0000d0321a024801180c610f10403030f044551070b00c1e50740070000208051030700249100600c0d0040c42003050104031041d56140901c0c00385542c0007201a001550310b520071009020500c2c00740700082151009a00c1e070781c1c02c11a0541045003140d4000040210190f25402100010302c2d050741d2580c9158502520310410140314040200005107151006900d60394200e00b200c05550002103906030310b0845003a172951744041d84400c802045480d50010700d03060f1819400c9a48000c1a111441c44c2d40c0c5800108205540c02400082401014460744012824041000e4580751040c2c009040e203050001800642d0301c0550300c44420007000300480240c03d030342400300c0c441c9240e0180b6210 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 95709703 1250 95708453 95708461
    0x8040210030b0a03230303010b0405040b0102070b070f080d180201030506030a030e04050703020f0a12050123090a021908060a05030a080f0f1612030c0318110303130e0f0108071805 79
    0xa502c0305c8180b15034107024480030001140c041e0318100144101c5008440c01c20010302c100300166160455403089002c41401840b004e80070034010f2803068019803090050382d00d81040d400c2c12804807482d0200c1c02d00320107110001d490455825100c0c594201900720024049200c140d60300414409501c101280078980b50004200003174003940503100702405244003984c541380c4040e4010300810100b804410000d00b028000500340700d182c41b03511550a400c6091040c07652010007030002411000d041c01b01c040380d0070061240303450714000d100811f9109555910f9010b043c40303c1002800b10540d041079120342c200d0b0b50b0300400242204103e810b0440c2c4842c107281c5075908990284960300500388103445440407802e4200c2001004403068040c80140d460400c41c0070f8559500b10b00b00c5907804400507400c60b844601c400403802c0c0800010040d60004c08880c9031140d00d0400705c10f640300540c860a0142c1c1410103110781403c103d260b05025104500051500d2440d0581c0c12500400243d100c4a40c40c0d40c9001203 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 95710953 1250 95709703 95709743
    0x1c0e040c031e0e030412050c1210050f0f071d030102040f05090a05070804030c2103090615060f0e0a03060e01020301030510090c090b01020309030109030513210602090a031208040210030b0a03 84
    0x22440c1c08c1d400405100c050640c801020380c070380550740d8440c81c840c0d280c240040d4035a15800f282170f00a8814110540e030070b941e0705005490000c01e031580d00100f0a078003140d09185541c00d0000344058042c507040c41e4010391600382808005400a406040c8480c1000704200d119075103e991076038041e4061a0440400140b03080209820200e249040c08400c03218003a40302650b00360f0000d0355080c1c40785c0020401c4403414665030003094440d015120000c0e440f050300008240c400c1e109180070b107200910320907100380d480d5a10030031111407070344681503a5008001081403240903c0b0210010b0302c6407400340040d646603542c5200e501c01c1e07406180c2555030307a060000400d903c00c0050f201c2949003c0d00030000301040c0c1c1809032003500040040c4200708d80041010507010045c40c01c103500140c417000440300c102480e99130340003c0e4005981d5a500440c0340c08000000c204200c0000b14044000c4d15182080e080c11b005204440c0802000c14084c1401e03c052040c280d10342d02c04881c1280d400c40c00705800e00d10008030b8 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 95712203 1250 95710953 95710963
    0x607060519050a0212071d060c150a0605030f071202040207060b0316030215040f0e1308070b1902030103110f01031803020606120a051c0e040c031e0e03041205 70
    0x1484a80500d0b000030410301c9102c40e4020052070700b490361034241c940c6c0d48150446024801c01e842a214501d8516050312900300b10b0081c10a13601c807034059900740b030301020540503480d008640c0c1051083c0c5400341044981403d200f046c07903038000c11010703110180c1000929200344401c10742c002c0c0504d5000030544107100302a40300c0040d6090040c140c6030606164880003040d140f150000740c1c0308045400b030304a919060030048808603220760524654444c40e00002c04c1c01c4060007000460a440c40440d000001002200201201d900c030b01c2a1440a0030101013000d6140308039502c83d070010348100018000300d0103000182d00c10b02c10444143c28002c0182e07004801030110b868041d071400c1d45918500040640115100348541d9056401c1410704c0f20726001c003941e400300982e0261254200651084000100071040100437401742041e18a415190003ca005c035003946a600b400070baa50401d000240080d0450b64820700c4451106105076120704903040e4803841180324a040004e05002450100b04003401 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 95713453 1250 95712203 95712241
    0x10b12011205011e05040b0106020f1e010608060708160c1a040312291c0308070c0206030c0a020c0a06090b070c03171b010501081221190b040204030206070605 70
    0x10482d8140e04031301e07841001030003050381c0c200c85c8035981600100c0c2042c4000340380b6001d1780102e8000c0c07001c400d1080500d00c40b01040036549850b07541ba01c82c042355903a0704000a0303000c3c0195907910019494149000504500514907080c00c00124403940d0b03011038160701c0c454034040740c44040d0400c140c503280740580c0c8203208011000421030070720701e604000300c020300440d0300ca08801c8140c1c81c01e800f810320200034a03245a44100116207071120340c0e40700424450384038180d0108a03404c11854420264000904d90b4000701c074031f000108000a6452003103641800f480243d1542551403a0303c3d80e090401c0030305881c15138059803071040c0c0042100414031000719009001190440d0081c1c602110886c0344400b6907006d952b044040028034800461a5101403003404c0c12119010f01819141c3c0c800fa12801565204c90302e2076200d401b803d0031080d0888401c3c10100d00070941c9042c0140c0c40c1e01200302c3c400a9441308000144038038414882000541c03a04412100a190300800000d015034440c1c9a44a0782e0007911 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 95714703 1250 95713453 95713481
    0x20f01110423041506030b040506090a020730030c08070804030807030605060c060f06061207030c1e0c0b0702010204031e0602040b0d05040b010b04120b0402060927010b1201120501 79
    0x25915002d0000138011001d4565942e82400203a140c1818442650360039641640c000030480b000030080e880540c05002e000d03100308009a00300f80041803c0c0d118440d50344c17180c160039490060390545140c144c401d020841c0c0e4681000011072170103a10140241030020406824458040001040c40e031096004401a08000f0207444d160b11540021941d12170741125011200f001d01000b10302e071403610500b9505a40c24070b188101d250703035a0803011405000c8007010401400791600360850820017200c02a80840e0b050b50f100004004581440f1030b140401401c3e071015a40304000610118004042500c56070440e0409244c85c0a26850080000d1003203610507180b12002181e6a07920111035007005020f107000e48400c0b4000d989404607107200784910f00c036402c00b030020710546800045690060940c4180014209410401d035000490000c640482403805400f041141c0e801c0080070120030f082c05403544085c3d490801c4260380b100484c0c60010301030034104e0101c0c070030100100700c802d4001000c1c0300104 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 95715953 1250 95714703 95714711
    0x160c0f030305180a0f0909060603060207200103020c0c15070605041202071d01140409170405090a090201020604020d05070306020a0905040e0f060720010501060f020f0111042304 78
    0x900740200280c0201c0c090a4000b00c003041c611620385440d104400070b0b954003004800c60107262001050081c030040e141103640980b00e190000c0424824400f40040d1401902c46440075040c0c02455903031b284464071203074141407040c0503810f0880300028490014450903100c1250166441052a41324002c002e001401507043c0380c1003108001d0b41c1940e1803d1440d003502110745464850700c500c00e250b0f0340b11140803940319100004100101854814581d12200540f00080140c1c8a0711f0b0f81035000c03807002001d441c83c81d000600300018209541e1003a813187c46000c0070030505100c1d0780001d40301c82016102900c140c001203155000c0c00018043c0d0702c011640814115903c20b007a05003e0b10a071820b204139442035152000010380c40700046600c5a400c01e02d000600b0343d5a80e001019100710b03034010701c9074aa0062411301408220000d11540c0e0280c0340301e440e44c116104020030002c0c6071020b880f000c03007140d03410500e9461222100c80103039000e03103d00b510081c021648618522622100311252103a0003400c0c = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 95717203 1250 95715953 95715959
    0x1f1b0c1d1b0c150406060e07080c03071d101809090807020108091911010f050c1f020405060705010212130c05011202190804060f060608060d020a080d1101061208160c0f 74
    0x2a944600c041f2144999106e210382d84082c01a140e510044806100320343c01003001a1980d8401d1080030007a10042261103120120000800d500c040c00300e5144000c201c9000305c0344015010302c28000c005110300e40c2c043c0440510381e941c3c1a10b41c0030303001c00281400001070109805180501480c019692194021500d4404078200090341000d880c804a0210f01e0710502503880c54803c2d8200c0703140680400081c1441d8410080f41e03800c02d440d589010a0310381d8203010201d0660303903503c01092014058000941c6500c10442d80130055030001d02062004c1c9044400d2000144049804c982201c0b02401d01c540c081c00d0251034000a403040d004072084039800d906072800010342046105004030b014480800100d0740c5006084100d81c0f0a00812020941c180009500351605080e06e0501e5403000d0100350815613a81d102505d031060088142000c107003820341c003040082092041074028414600422070310082070304e40e070303c180c0704040240240c0c603100c00c064000c0c044103d480c030004050481c00b05c4c03510b5036 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 95718453 1250 95717203 95717213
    0x601090b0309061009050402010206040209040305090d05030405100302090907030f2a0e030303130206090a0b043008160f0b1e060405061f1b0c1d1b0c1504 68
    0x842e1300c8135482d036800c1008a0503109074410b103031060754180c008007010345a82e000c02c16010300c000c008908000e0100041180c5032101a00071000c140b09070b0003503894509017800c0000c6194620500300c109441400751820981d14201358a8210109007000501e280c029040c41001e80605004d1f0070320f507000d207801c0d002c00c21201c6041f01c41c03840190b43d135285402d5141040541ba44800d840409008030340705400d0300545000b000400000c64003c01c0c3e40202036031707941c2003541c0d034000d5070002b450f4600d100c0200350030a032500c0940c00c4081030960710284031002c0760707a06152400341022052000200301102c07400c1100d80d00056076030301c1d001202ca00c075528020482008ac2c01c0c3d070286000f07100341800d000c240b01e0308003409240d0040030000c10202403a00c139020380b01100c0101040300800c01c10705100359506080340011031340f141c0d80507181170071200e41800480d8103103144903a9003120301f4501350100649000c18051503030701103442c48101d980e50400156921303e01446442e0207203681e0741d40002d0204002c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 95719703 1250 95718453 95718463
    0xe0702010b0d0308151509010e01051204050703030f0309030212090402090a08010c030e03120c030601180f05011d13021602030318030106050a03080307030b0a120c0e010915030b0601090b0309 84
    0xf541d010381003034411714003900707120301080340c050b101310b940038107020307c4044d51300031900c1d0304a020061620506141580e10040942d0350107880c1540d098000b00400e20a040c1d01c01c00c0c1c107080512500b800e101341c603603a80d00255a00d400d903c0a04900d40b010800200c150b442d601101c4070640001e003100e000586030191940200240c90803d000b091500003415103016021042c0d4600c2c4074210540401544c0d0785807440c0c040d03030000340303150304004018115120072054009031070302070694590a81c1c03d00341810001760101d840b10110704110049024138040c540c0e6803460300310340307155003180240c2c03100c84a0403020589030103100001e600d8000401c40d81c4a039000900b41401000080b0024440340c0e90301c00a00127401e985000c094102842000080d40b4240650403c440000d0007034028500259100382482410381d003140105e0b0608503203042080305d50304611138030b409041608400c000300380a5a680d4400c00f540340c03100600b400e0301140022200c1e8040d015420007410346005940da61316000070415213907 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 95720953 1250 95719703 95719711
    0xd050906090706021b0d0c180b01030506060421290907060c0c090b0a0506030a0c020105090d0509150405040509100e1b06030405010b10020109110315010e0702010b0d0308 75
    0x50711036210b0019040c2d10005d050f03050603a0305108896000260018000514003044050f605600404400540343c071030700e0b00151542c0c4007680c0010321040c40d40001425100041c24040c42440b045c0810311000c51100c0c20340b5400402c05410030b1080503c0e1418443d1490a00040c6c2c0c0408240d6010303182001041c6c0f030b503610401188080e1041280c40784030030b6403640301c862405884540511403c3c04500c032241c0c000900a90010480c0800507510710004055600c00c4503801551604c8400c840c24082d0240195078015880c00082d0801d040d200b2401001401084000f40c82080b980c2c030009048041d0000702c0e0b01400c00504140540e02e0200d103800d640c1c0c0000041c11304000d18100d10b1041d01d030408602507200c0681c4040f200798198181b0f080110681018000b070350295602c032504400e95403080e00011448801760004240c078441420030340d9502400058080c006d40000040f01d518100741200321741591030880507552281c42d030070ba08030b00502860460b560042c0c20910b81d034003032540081c425445 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 95722203 1250 95720953 95720971
    0x130203030d0c11010608030f1b011b030b0a05060d0c0c02030a0b01051e0a0b1c0606090915030503090420030a061a09010e0112150e0106170c0406140d050906 69
    0x505000c0f001a500301d0f0b55903c42c0f501c0d5078005003d6450130282103002001d074581417440c0000c0d00c840361074055084800c40c240e042e0390403d21f0780c200c8840d15014083d42140040454401e01d00e03c2ca0b0601044180c4101c1450a11440d80c0780300c07000b10035009080c013006664019040700c1d01e009440c40d10341e0703440d04203000d02172054001d0003084030820039000f003a890025001e440700012919040c0c1c0b490240c3c100e1015078440d0464040d0101c040707078070b51151000420141c1c2d240132205150071489002c551140344420160340c440d140c240086400042150745000042e2070000710340740f982200c030418081c45483c40320082c02c00028862040c4094001c1c80550b06038010381d96a040d00002c04006a204912265010075040d103160345140d8040c8800304080070780400082038045180802c10400401504800043c1616038014403041e544504c196000021080800e500350a1216001440e4001e034402c120400c40c40c1210a01956660400c0c2c501d281d15000e000c2c001030506544040e22450308481c6045 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 95723453 1250 95722203 95722217
    0xe0f1215011a0a09051003060312030507031104060c1407050d0303020702040c0e03100504051e01020d05011512020903070e070314150a0b030604090c0f080111030c030708130203030d0c 81
    0x640c0302460040302c83c081c5481c0c40c1d5185151901d418008001c118101110900d1f980300300020224500007045000a500350f6800102c528040d2006803c80d40c1c1c20003000b601050502c024001d080c0c110701e070013405940141c0300610f0740450160480c60820f06800083d040001c0d140500c04254068001c3c08059100f210280b0102c2100481164800d40300c00590358181c0c00098250240c3c20320394403442c1c0050043d0140c1e00c0001ca4490000a075000d18145107007241e60014003a07500000e00c1c45414090902d811040010b00d6190344020300001074000c401c000c590b8000362500c21583c0401c1b0501c01009208c49008040c6070282c009070040070344803c83c02000503100002825100e0480407441c4a110040c42d082516081014143c41034100030b051070741103565441100041141803415400a00349922456015400c042c00c0d00d082d1001440401491002801403140c0e00da11501a40d83c0130b481d070700e45807505a50b6194402181e00300500040c0d0503010005800f4010020303034100580400241e202e00e0 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 95724703 1250 95723453 95723489
    0x151d090102031003020f03010b030d020c0a0f0f0303050c1005010603090209070206090d0e0a080609010e0d0e0112090303091703090f1207110a0e090c150a0e0f121501 73
    0x600741d00c42294140c82081051000f031005241440740c01c00a03040180000034a0b03020000424907086440704914050703408103010440c01d1500010b42400b601d2411009110304e0315000083d10041542e01009060040100c3c02840800c030400c0f420104c41d8800c102032004e96900d138000380041410100a0740550f002c0c0c00091460341c000240a4000e90886001384100c003a0240d045802c940c0805035140c6c40144100005840c1c1020801680605190400040c1500311208240d20b00301c0c8281c04081401400061518180e8001520800c140d07041000450200060f107400c400401c2d02000060082d91003107640b00d4190140d02c0a540b05540c2201210039800a0701c1135207503aa800d0180ba0f01d01c1030030030400c28002450a01821030100d00181094850039111603240e0343c801c03000c6a880c1190b6000e10b03420300b00751038800030501c03800c1e213100c10f42c520300f108690000303082200502c505801418501a80c101c0f40d00c55a0003031078012882c5003500e1403030592802d04120603d003841941501d20a0700204 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 95725953 1250 95724703 95724721
    0x6051309090b06150403060204030501020a1107030309260105090a05071a0712110d0e0a060807080a0c23070506010f05060a030b1306090902101d040906151d 69
    0xa510078035005a100b2000e942d41d00204800c00b24070304070500700750505201c000300040d041c6c000b81026601c6140050307200c3d0070a40e00108408010113070804154010b1800b000840d030404081010399100c0d40e804102131903100201c09815221400b24511913182608214800c00080b0b480318105200c0d070305444e80c1558550038109034034250680b03c000c5e8207081044400142e401341c0f40c030042590394100345504100c0c1940c4581000c00281103000030945500c9020154a407100e1684041e101509200180b400c0062004141e000d000700070030401d5965802501c0451f004900081c0e11000c008001d03140f400f243c4c0c50096880d00b141200b1540f41c403900c00040b031028940c080000070398401030403990406003400340407809402c2003140aa084403000843c4001c80e0320740d01824001d0681c1c1140030034208074605c18024104981c0e80c1610405c00b14205840c0d0100c071540c84004030b61012103011824001d10708100f80103040d00c8413000d00d8001204e41c0051401e081e032030321800d50000d11241c0c85196071030f42c0c45 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 95727203 1250 95725953 95725961
    0x60102120306010f030917031008010506030a0f11010e10020d080c0c0a030c0c0e011502061302010206070e0a0b030106020106060206012102090718170c0d110616050706051309 77
    0x24480c0801c004408900c0118441c6e40042a49401540d4100000d40c3d0f0f9a004481c9038010f0320f00908c0f4602511050140c52424060f4036000314042c3c0040074220603a44070b0007402000040020051800c100150200da84107124540406200622004940c4070314000a541c4030303800d03c603140101c4d54000c00107442140030400d594590300c0c0c00010f4980050141d40460701707840ca604007280d070b07070300c8940012800b0405404a140a40710607540034519690005000e03203401c0d001041d4844110240001c0f000503640070030543e800c80e24904110b0121300b03d000004202481d00d0700081c8810101100000d4000c0e81500210211909902a20302c00d90302c4503102c500a034400300c9200d00d00a48606000d005080c01e44103e03610510760314061016036540141030440a085601c0000c4504028000e00b850840502c0300314082e030310440703011009100c0f5684120800c02508000d138460503001c0748804030804d19000380e518265108040d9907004e0b0304d030103001e0045e4000d854004150b010700300303021484c0105441 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 95728453 1250 95727203 95727211
    0x102031008070308040b0c030f190305090105061806060d15090b0105120c1608361c11030d09031a041a0a151d0a0902011202070c1205060601021203 65
    0x84e889282038202114041d180c1d1121800d50141e100030400b5412101c620317805081c019030500d008104920030407500806480018114134141d03454102400b03010340e1507171002030b004c0b00c01901c10324181e5030300303400035a482c0180317181c10807403d04101c00e600c403044401082a00352401d0410030030514a4400044850f8000d402040c5800883e1402188100048001905141341c02c84075500c0d0f40c841035601d17254642c00503400340013800c0d83c1405112100601291120651320a0905841141003d00026034170400d54155400c2c1c0080500408080c05980b486107070040b1000313803c585007002042c000030001c01140c44203231030481403140d1030301d00601e2401d80e09020b5a0014903088842082004031484e0359005002c0ea088982c1c1c0748040d00b18070b01300306840401000c003100510301c00c00e02c100661610300b80060842802c2840c03d202040140c4c3c0018585503000740c9800010b0b12892586020b83c0c3d04010b64010740d05501d92076806000b04980000d4682c031880d0280c3c280c4036140c4410035401c0f132034003040d2 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 95729703 1250 95728453 95728463
    0x803070c15090b0a08060a120f05070905060105040311030102070807120906080408030103020108090a141f0b090f180303130302010e0106080606010f020102040b0a021e0a122001060801020310080703 87
    0x400313540b03518402c031034254000f035004042c03003541a87c465941c110418580803c03188a41d200c000030003445010f1081d80000d1002420501480c038109000815501c500c1c0401060340c0c6141c0380c0c10116890950641b17000551182465541d13007586d041411920b4507240c80c003000100650360204040348114201409103500210190541e42180d005503503e5078010310440803442080344400100d10107156081d020710409001c2c0040d0880904841101200030004014180c100030490550381c40f102c0030180d01c00140c0401c8421500d5a00c0348011040d0b410120001030721010043c008090310440e09800114030a030004c1208140401d00d140c266111882403421981148001468039409a0082002813071144001480c3c651241210105a080b544510005034014040c170303004425800e01d00c40101a144005000810076503445c14807101c292040801080345800000103800184240e40518a40c000020b000450711581920b000390412900111820128040000c0403907000c41e0341e5003a642c102c = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 95730953 1250 95729703 95729707
    0x303090c12021f1205101703030906010b09190801050105010314060a0b090f03010f0903020f06040b060103110903060a0b0103050a06081b0a030c12030801240e0105040803070c15090b 80
    0x400c2d4907106208040c81c3c4140310100407079070b03140d00c1d00d0701c1038a00c50682e583c0111011410b24901505e04030401480003040d41c000c00610000190024019044400700e00e906650b0760100c1002c100701d0850304410304600c841b2064049030580c4103400c924182c2d5400e98040150b0742c1c41032004020f124041e04d0341d44d08013142d10030034000000c0070030007016001d20191590226a900502103403c444011041c0802c003503a0f10124410154117220100c586045500145120f0810351a010316156021302428103041e030392102c810401c0e002c0d0090383c001c0400182070323a52900d00401c2d544050500c5070b20650001c0c2c60a40050382e9070300f1600c200740036a030f055001800d460043c000400c5c40c3c11048940d280c0d10082244000000030041c000140c0500196040d120300400c8a280c06040c518040c0c0001c501e02498070b60107113051081121b0009040040c0c0340009941340c01e00010780d100c0c800c0d0342084000707000000c0c1840910070741c076061004440e043d81c3c03000044c124900c000c465131113540c0a92030081c001 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 95732203 1250 95730953 95730979
    0x1080613050603070b040b030a05060121090309090c0503070909020a0c0209221518021f0306080102041e05030606091308041511010e15160207120303090c1202 70
    0xa5101c1c0340d0007480035080350750041d11070002c2400b6800582c448000100000200a44221280034858201e4800e080008154940131310b1745258440c2c64071001d10040c0d40d4504401450301c10007000d001081003030000c0104941c86400240725500855107180814100e000008440c0307000c3c030890301000019510240f4407070540c0d080201054001d491b8140142c0b460710180c1c0044041e950b415005485507807010320b000100d45485003581d9027685001f028202005200000d81c9070f9600c03100307895000202103003030640d002500390006c040e80d4201851035807000c50301080d10000c0c03041c14a5501c54010300c0081060f03590f810581c0d0343c0d0003100c0c690b8003e8070300780c04a40044009180350382840d100b05411818152202d180e0508544041507600001d5140468001c00030390a1041c030052113060405031880c1485020700014050001c2d11901482d25045d0714504018424800c800c040d040001d88800520b0740c600b030040c040c1c101c0300020350311044c42d42c40020785050340c1c00d1210b012507400703009401b030005 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 95733453 1250 95732203 95732239
    0x30201091403010912020a02131a0d0f050604060e0705090c0f09030a05060f0717150907020a0c140a06050406091a0903061003050705042003070207050907020d020c010806 75
    0x50500d6150b034040d925102c08100042041e000e241c08041e441c1c0c018245030150b801000441c0d94010f024480503403805a6051812560381d03020300c071485098803140c00d0002c0c5807030442c912104c1d00401400c0d6006120901c01000340e036403c5002005002c3d0102d0314203d483d081081089541503460f100348003c10401030703209101860103841240323001001e40344041c07250380b1007605000e030454080c082c0f00384000401c4020f42c0c100740040c012200240d46500c0394501130170501503480d5643c95140c45102e0041c00980f003a4400c00212a04980c030034440b001c11035640c00340704d0001c41015081d43c03080041c03400c007080c00c40c8148182e4044803015550000c44ae840d200040e4810609800c034107405180400c9405a00d840400685004190701c003c0c01c0b07245495418440d044c514203800c228850342c244100380842604954401f02114810680e07d0307aa5240e02e00140c0ca004050303800690850020743c20425115004240d5041291064003680d0701c190840e001161031103001c4030140c4e8841249180f4000f051 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 95734703 1250 95733453 95733479
    0xe01110910050f070b190e0a06050606090402040603050603060f0f011202060f0408060601030e0309010e0f030a0f210906050d0c09080708010204050f0f0616060207081303061503020109 81
    0x1218604140f80307080c0e8002e20120050b400440181d607013603038150903c0071a49010801058400030b07018204007126500207401e417034040e02c0318007a01d038580382e80102c1d000e503446808036060180c006104541d141d503910409409800100c50309440780c061040050f0482841c403a40034860003c02d8103400e1741741e091446c0080b2000c6002c106076000003040c002d042501e000b00b002803011b0319492000f8400740c640400018156111035078403860581051080c01c00c1ca90f000f59190704181760494500f5044091003010a10f0301000f280042e1010f05210420020b2128200c100c101c10b004a804860b052106610180d900c0e00c0140310300340005e001000640c901d101258008440600075103804550150780b0102180f500c091504040c000c0d035030000e420045440c00c070a0303c443d2904d040d9004410b1500d01c0d0001071990140c055080000c01e800c12800007005101d23412200841c0d4440b200380c0c0c9400e03a5080c0149034000c0e81c0003c070f540600d4442c021060308a41c8a00800f200e505940d60f05406080c076806006070 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 95735953 1250 95734703 95734729
    0x60303041703070209070e030c0114030c070204090501021305130b03060c0a031d0706020d09050603040f0507180204050a090203041718030321010e0c0403030516020904060504060e011109 82
    0x150006120303c0c80141c0c1e03001e1401d03014864941c1c0d290503200d1000100b5040c201d2256401e8140b00c0140150700308000342d501907a6001400d444065214060740c004070b8040c1180480c02000e80d440002d920303d400480701d120500781e8100303403000c20301e41041d19204000c07a0358031181e869050740040005501e00708070034001c0c144040d01d4a03010035510300034400002070b01801c90076800d041e003003c4000e005482c0e0400298000703489524040c9a9079203000081a100e100c06000038160288a05903002131000800c2004000c150044641814000c480d84440081d081030041d5131041900074400550841e29000350385c003032030700b0a5039508014156952071039280d1040e05040e04c0a100601c3c0386040b940c050001e040d501d150910a2603150008186035008131030141c00881d0340703001140074088040c40c42d509441c00d480c3c0c541016a40c4641440d1441c070214201c06000b580007080d03004020400010f5005203008074400c29041c402c1070f410420702409e81e610034122200c00d0b0001c3c010b0412074601150342c0403403 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 95737203 1250 95735953 95735999
    0x30424021515120105010503060c0405091801110309010207120c080a081009020d0906060e010f0303120f02030a0f050c090d110a080a030818070f03060c03111306140306030304 77
    0x101041408643c003400b54440081003139640702d004100c1e5003130a00c1002d42c0803040100700361a1504041c00546981c0e0054043c0160b03c0901603604c400c42c0007540403074280e1082e503c0803901c0b4036202c17032018044c1d840540c0440740351924042d00d907401c5008442c501d03440c0d0350003007080f070810148a008850620006285105d110101e86000510420510082c01c2c10022450b01054141d201d0601c0010365403123512034811200c4032401085272002c3c440d51070081e00c0e81468052444000070b038000001d0322180e099180b0003031001041c8003100d413480d404a81078100c0c2e020b00340140d646100203c5264021407243c1500192200c030400002a0042150140090000c080c406665180c1284914200c40010301314042004c0741c0c28401c011054000c501e0078ad241c41d500500155003800610101190b2502c030080c5400c0d210481002440d009801c02e034030541800c9942c940f5100d0301d00f046040041107110340c2d400b2412400840440403018801c883c403602018004600d0146801d4031180c0d08142007c0981c1 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 95738453 1250 95737203 95737231
    0x90f1c092310020a0308090a03140a021513050d0e2412010611070e040f02010e010e0d08030718050a05010509030304091e0b041a0913020a03050304240215 68
    0x76955681225500403405a005112a41d0189809040707890086d00e000080e0b40140005800a03501059500c181c0029002d01500d45921843c240c1ca00030440038941480740114040107840050501031411590144007220104503100009450784854408003581120301b02c003102a624109251207080074024079200c0e40b51000c0b0300c000b1000c100e004e82200001658402070b42000100030080403020302000300144240c0d0900703035161407515400640090602200c406060000da02516598045c030b500601002880340d450316200c44141d204031180b402042404803e404180712240c07513003055440141c41556200d04010064550713030002c00005901d441300f003001140b2402c4900880ba2044469200840c094110950003820b40f0f0310303180024010b5140490b40c05104224104510303801c4810707150f03000282c03a000003e0aa061b601d5030040d40120b1030000000800100000030401c88800103c03402c4420710708540e4402c40a000004100143d1094000040c05c51181e0721454004000e525040c03 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 95739703 1250 95738453 95738519
    0x150111060114150d0911150909040c080114190902030309150f0f122202040c020c1507050d090302010903030315170303070201050f0105060412021206090f1c09 70
    0x8016610080c2040c0c0300c130b911150000308025422090300c1008500f1200c450a074214603c042c5024000c070070142e03100c1e4402d0408507042c400c1030f030680000340003204028031800044e08481030250a06a0f182c0303c180000c5c6074100404a400d100340d1411a0380107014501c0d14080808120824980e5401da103c145000c003c805a01c00c0302c00002c04034010300441e00b603241c2e01040807901c2408401440f0300421400b0388400340380400d007000910344103941240d00080c28600410220f280602205800350098452408070030440c0c15000900440b034860000c07910350704015141200c5189041c400280419812103003880000d0194001441c010740e0031703522106041d920b40003440310880300c2a80348090342002084c044c0141c2c1c28000e90750310141064804000d0351511000c20518465841810000300c84071030f03950115913410726001c1c00c65503110300701ca60600344030184135101c03490701201900d58810483c15440b000016081c0c00280c1d85940c1340e0883c40c51812110800a054130f0030800a0240841612 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 95740953 1250 95739703 95739739
    0xb0c0c0d0c090c080712060e040219030213091e030c02010f0c05100608060604050105013501170d030b030c151909150203191b08040e150111060114 65
    0xc80203480060340c0d900c105041202e00076140700d180003040883d250030304502380001d0400096090300b240e41500da2031805500da030040e00d821080f9070402541700c5810365190355542d02070340102e00018010080c41c0064150000c0d00c0c000c110042d880100400ea03140022070166014103d102b41d12840d90910403207054099543c20304149902d1200481c0c03507036400061000c610b081144513800745040c4c400308240d5041c0000a00412506240702c800301c4490401148180c5c3c0345004c40a056050386a000030550b160382c1080110002c10b060140c1c2442102c040230041d512038000d105540c20f028000d0f1035080745240900900301281c0c208440d01c4074013004821005078440511074015205030b500c481c0918109a5045003011090080e40c0440d401032141040c0301c5080c5650b0050001c8906101c0401c00e01030001c07002810f040180036120b00804500000c400d406024035038458182002180e001461039001502c00c40c070381c45004610780d0711000062103800d942c0d00e000c5030194070041c440b1107141292014 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 95742203 1250 95740953 95740961
    0x60306060c0a150b0f0114030709050a080c030d171902040510081006020309060d050a0b061303060b0a1d07030f0204060e12071a0a03020708071a010b0c0c0d0c09 71
    0x4116402c40650f100c0c00b07100311061164560000045480031010001040000c2044132481840600850700101154429000e084103070024031021740340700040c1c1d0361040100d464020142880b07029011f00084e60843c01e1003206015296602441100110f8980007084480c00c1c404440d41c0d4042d036400c00c40825140e035000009851400c0d1956100e13032514041c11066004031072a070005041d94001d01201c0c2c0550b46200503503110244100c80003529070794910740d0b8000750025442041d080400026400c03602500440410305403400340e9024005468000107024050007140f00d1501c040040342d0144811441209116030032513124500400c800c01c600360500704a80c050ba03c20000700714106492101418904482c2c5a0b41c2600f030040d02000b880e10501c1d030a0300602d1400e0b0384040c40d0020304420708030301079030607a401d641d0032481c2c43c1d0305c1d02c2d02440e110110b900c005082d043c0d0003603244000540c06490508940ba146400d10241401010352000c2c80844183c01400325a40c42c4143c002003001c0c1450700c1 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 95743453 1250 95742203 95742223
    0x1a0a03180807060c0201110d050a060b0f04080c01050a090501030f110414090a180f05030705120414031f0209010e04230c03160e040207120906030e010501030c05060306060c 76
    0x994155142c03682d1a0400494a0500a08040da4144103800d4605801203040d03550403900b9110124050399991024401011140c020301c45041004c243d80c00b103d1140c0c1c029000362680c000c05c484c00f01142c1c400568050080013039200000c0c20394501840325520941100c2d508080d070301008115000f440c44529001d4020360803060a410740c2c0440b514551502d050b000360007070007100707041160382200301a4910135844034102820f43c0041da96588204801041214070141c1c2103810b07039550080d13200040350301c5c1d80140710300a01c441c0d22040803140c40c075002c0703480e8410781da02441800041e942c0580340d8020350806403c081c1030011480c04030350252654001c002c8003402c40901c5074034021000aa81d810648083c0100007116018420130070141e04101d14080d038000c0301e00b060001c03890301000040c041d1148000c0103114003000340c8200602070b04070a031700090b20850b443c140880b45180b4040d80c201c079001d200c06800d51303408400c00c0105061450055400c01c44c064416031804034550100703441c1c10034081c = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 95744703 1250 95743453 95743463
    0x40c140d080f1b011b09030b011e08060405010203060f030607021e010207020604030507060f110606090c0d0c0206040c1d060909070e0112020a0e0105010c020f040f09051014011a0a0318 81
    0x41501d65084002c1e1178014490300301e418200c009600703646810b004c0c0841400f480c000590501840045441b121021900070442041114a030346070a00c0d109010350026100c00340a0302c0c000b0301281541c0b0303000c140b0794818203032030740100454040c65004c901d0688600101c42d1903554204180005038440380d0042002e540154002c10354a0301c0c0c640d0050040349024402e904000b00b05112030010380d0301240f99504004126540c0b1031584405924820b144602d1020716951441c00c015040001c3c1c000c036080b80310390f0140c0c00081125a40f507240444000b0010000d01e403440380e00000518510384000c00030340100c140400c8070501e0362100d40d40e0852000c20b820400c9170512801c0c1000c214074200c04d0320700c05481c0740800520254034090000c0c1c4030f0041c5200003403090940315610501031b01c0310b520484480f02003d00911410740e543c100941c9818199441d440d041d802c0c01e942c017500c0c1010180443c1255070004031150790a820380c0904c0f5070740d00030030001020107890303403010001e0351641c851208030a4016 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 95745953 1250 95744703 95744711
    0x60b0d0605042a1202010e090411120c0d031b050706021005010602120a03051308040902090405060d050c19081b0102010b180106120e010c0206040c140d080f1b01 71
    0x16082c01140c14121628210184003e0040d0322030780c42101d240c0b03004903005411203010000d010310050741c410b0300300c89505410941d504e08000502c203006000801090003500c00010041d58a28100d40701c1020b03000654201e10070408810000b8840c00d80c008070701140421a490343c242700c0c1d545508220842e4440c1006900601074000084504d00c0f40c2401004140000c080c0c03d460303010104114020444064281039803100010300e05507221144950b01c9074016100d030356503078456802130000d411000005005519250004a45081c40241245d2407a00030700144010a01d542c1000000b1440341159400181d807003400042c503c0d0100180c1c1f0300748040030b00300e48540f41070000080c01c54009481c0144200310700e1000300403150f4030803002419594180350801c0312104103101007016140030f8105100c01d610301515040b140b030b802710312180642d1050b000c0014440e999032603404560588210f150340150551005800550b100c1c0c02003080180c56050350b41010b541c900840c100843c0c00300035580b83d94407 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 95747203 1250 95745953 95745961
    0x405060a031d03120f100e060d0c09240b0f07080d060806180303040c2c01030803070305131a1306090b0a05010b040602030306060705010204030503030a0204030501051803090904060b0d0605 83
    0x1004e9001c0c0d00500011505010340b805081d02180c151080c4900090300203804040354058a401815011181d0013030a9205420f40d260442d0004194400e00718040170101d072100003810103405140b01c11110401081414654600c2d41e80d410b81d4000e4800f10360135001000751505180342401013000400e8030f4409402149402600d00552060000141c5990b804c10010040000c2d41c055401d020344006008011422200780c5e030001841c0000040b0b1503148a02c3c00002080140d0b241c01148035281503075041c00395440301c10344464a5009100024420714001012840240d01d98103882d80c05000601e010345141442e840d040d04840b0103580940d410076081301040744084640c041c5c0e43c010845070301c00a02c0c240c80c0ca100207490f40005880688680000103812050040940641d00070b1a003000c103483e42c90505886980003948244003c03117040d401d100014136042c00c400840c141480582010b5458141c80310204a000c20b00200201c0b07409645e1030180c4640d85441c01100b0303403903110700800101c07824 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 95748453 1250 95747203 95747227
    0x140a020301060509041505071103040e01091b0c030f1803120e030304050a03020f030715080106090b0f030103110a0305010e01140f0705160845060405060a031d03 71
    0x1e001e400184c00b81014609000003c4c1d045c0c3d4a20b01c089000c0d86001038143c440b00821601e0380140666200248004174000c00c2c6060f1401083d41200c03044c400802c014070b440e03c2c1c041d6201150880a0000c00e540c0809040803038003502d01020a0002840e0070142e400485400340c1030403d41e83c0040c0c58400d04103010a07111500101d51a249800440082d41002d280c400000c42c2c16015010003401502d400082c602640c5003001100098a010307007201102c08400c1100505051091045c2d01c0004c0440c100000e40da0700e00001c4400710412600a5451607085850351080443c291210070f40002c100a4004042a402e01c2410f0003d03c4442c00400c3c90328501101210705c01016000e100c488645105025038550040d080b100c1900f00c5148050300e4240c1c03130510343c400703002d00884541c001c819110f1580f400b0386120000b02500c1e42c0344402030541c4005504ca0f034000700c0605d03d45030700b20360304100c00c0c4100c1c40c0c9417000d00bc5c102551301d0086101181c0795041c15a80c04100102c60060340041518402d00b0303 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 95749703 1250 95748453 95748461
    0xc03040807060306260309040b0d0206161a010305060f13020a0801021b03041d0403021501030302100f05090601050402160501020409090b0919060902011709072402070311010c140a020301 82
    0x100d030448080111744114031602c1c0c0c41c0c0c41400b2a8601c5103540703001c40202a103a624404002c582c00500316070300c4890f03410721103011200d511000c50741c013401030f00c8258040e0b103025100d40c1601e8000006040503950804030580d9048041c2885291050000701c001c0103030303101030440307028002c8000050b071103092614500d0407400302ea0030f4460f603a130800d1000b404505000b55a1034040c104240c071200c0691103a0506070b050054080348000065560350021040c1900001c0302007824071800020000e001c1c11454020031224192088d80345900800010841c500d8143c014041d104100c01e114020303030340281d5500307089a100d070f440400314907100c4042c0000e02625100d07450307000d1003400182c54100c800401001075072340d010700010445540c41101909691144241c51040c1510b10800c90060901024641c0d5605152003155242083c0b0403210b400030350303841e200c402810219001800618150356510907980060f03142c1d46d04100382440d00d20045006c02c1d41c100c40400c03400000d45882000d80c01818252 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 95750953 1250 95749703 95749739
    0x90f050105070b0f060d0b0f0106120507200708100905150402090c030a0603080403060504020310150e18010221060301020403020108060d02040603141509060106090b0c03040807060306 81
    0xc000c00744000e82c085801c88000310b9000d040c0400c18001e5544080004500000b072500c00340c00e180380c000800040790046031109042e5242615a10181c101c0032070300c1c105882044814a000848050483d060100f00d15001111500d694040e40c460981f6400e10518090030b5100341c8403400c2c0c845054a01b400800c0c082250400b103020301d44603041c0341a4001c911091000ba104481c805400400a11001c2440d40101c1c095580901e00d1982c031a600c0c105007016103800d440907440303030207005003620b170b8a4128450070301091000c0f20b02e014020f183c80821484000d008140d94520468a01241c4441700b0a1008018021801155950b464404000b11400001c0208054048d030f01c100411300151f81c001071105e50082c1c04913510301904030603101190246c00298402400014024016a003002e40440d031440070700c544d04080c18460740c501e001c85581c1e420a200b0b8034046034000c4800e1212038a00b800a05048030f00d4411249807559840a50345000215400f44e00042c0d5103003000c2c890041c150132181301c0 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 95752203 1250 95750953 95750957
    0x30509120a4d150a0207110306070909090201020316030203070312060602060408090d050619110301031a0405120c1b040c120209030a0f0b01080f0f070e070c05030703090f0501 77
    0x30440e11140b480081450078100080c03034603031605851a82581000a21a0750030720624440560400086003806500b100c60101c0710701c031107401c0100a500740024a584141020358604200a1501d20b0040040c102d2140690460001b0404070300e002d40d6403030032400c8840c800e50043d0794030816070500411100d000d11010b507400e07042c16020080264002200780e0055004914140d03124012000100c800080050040c1503002c1d0008202030005080f40d00b402150aa0340d0034020b2081d02d611400c02e512090100030922001580014a45500c07080040c1d0300a120340205d59034180c1180c004900390300030044801d500c0e440b600c049402045102d2025a8000c001d503070521010004882c00b4111110b41c80b03124101d00e84c0401e149500780d80800412202a400000c00c0b0845242410080750446007409840000d02c124080d1007000600028001100c0d15000301400b2000c0c100003005c01d403054040d20800420102b4598840454000d100910000c2c0c404d8a50301c40c0c0341e240442403c00340b00f5960003e41 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 95753453 1250 95752203 95752277
    0x50d12030e06010e04021302120f0114010201020903190501020403050f010b010f03140711010b04060906051212160f021e0306070503070203181f111b060a030509120a 73
    0x282200713007000c4c6070840c0d4102c1d040c0202000d03041c80140240a550726010029480c64103000d056414112054169810003a0710343c141e00c910401a4240d02c242c45600e41c140e0310a4460365171000c01000c01d00c0c801403045001618003940c9480e0b86d840c00d20f03038400d00e01499541d00300d90404d9603000417410542582074102030280c035526291a0400d800010080d606100c0c074010403900c0081c003035000c036024000c010b0081200c3d54030f03081044000c240701d0103040d0080c0b600d4100034a16040000e4609040184410103a2814855000c00b00340025175140480b460403000140000503500c2d00c00c1122202c0030303860940c1c03010703d10008040c60a20f02900031010b008081052168555000c02114103c030091480d040c80c040c0104046070701c20303100103034000320b0142c2c081071a01041c1d40154040c440b80024000ca80150307091005a80b1245007400c0c25941c040d07010803152140501940105a0065001c425149421800003034400310390b000c00481e1002465081d1211404500300040034041da041501c030700 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 95754703 1250 95753453 95753459
    0xa141e12130201050f0702040b03070803040302030709050609010302010f0309060c03020904050f070203030c071b0b03070f050408100504021309050d091a03070c050a0501090b060108060301090f02010810050d12030e0601 96
    0x40c2c04e500c107258007142c415100058070015511a500b01003c2403602a04480d10130744d403129000e4681e042400120700c00c0c010040d00140940c0680101070003540000c1595101d41d18660064030f0081045d4000802c0c10f07100c0c01c07008042100ba2042640c0b001894a02507641d0101d402000300301d4078014015494280280203002007180c5c00425241d0100c208844644d84a216040c22200c0d80b031240380f0321641c0d149030080403804101c0c1c3c20285025843c41d840d90b0f04804140d201c140c60034051402065420b0380840c0781c10b10003c000e070700640c0d0800d00151820a01141088004080d952000410f40702c9910008443c0d4240361300500d8040100400741248030454002d01c40c0d4027441c840a4001000c0008804104003488403e109000206030b000c00200030101d00c51820580140084840e180454a03203030004034541418059001c00e00d900000261107050300ba401540d00640240c00c02c000401c000c940422030307498844d44d10280034020241c1c8a03540700c10190080039912101062142600614010 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 95755953 1250 95754703 95754707
    0x902031024050309031e070204060e0106020a020607170d061a1c020304060615020d0305060a03320d03021801050412110402071a0403090501020708030a141e12130201 73
    0x50700d00c500600c2c20039960313220888464034500404101005030007000044078026441035006151541c42070700c0900c151907441e107205005000074400c0202580043c1507a00051910000070a032261107070708011a000030041c20b0700c80c02e402566614000c1507580109000d0034064690090503104007440c0585410402054405503040701201001c4503130300440030030200b102c19040324000d0480e0202c56900c0791000c0d5402503992104621410209160001007841800c100050500f0fa81e04400c00b4a103002224000005030906031042c0c003c603003040c1995124245013441005c0380c80c0e949640c050389942490010400302c8260b1030049050107000c000810603400401103104105803c4581c44092a4508000c94064402d01c5001401c0e40350308019400c108080395010b9005501075650f141050703407202c0040e40d40b1a0f480c090410207600600030358180720701c6482d4100300d000e00200708504004082d40700e140c0c4081f001d540c2d0781d00c4080100389010140d40c034002035070380000b800010303110720040da03000 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 95757203 1250 95755953 95756009
    0xe060102120d0204120c230d03050703020111040801060602150105010e270a0516031a21010203090114090c0604060e0609090405010506010f031406010c0c08030409020310 75
    0x1d680381c01980880c40b4080095550f040e01c00034510401a543c12482c140340c44071080a00f40100340440071011011050014508940700c0c02450241c48031103520140e03101aa540d4124a8040b4110b41d200e080e5a480301100e400548014000400040342240c20303c20060b0a10450300a10b040707215089004110740d0380e02940c0ba00d040700d01030791480c50140c0721f82595141028050100403552104c50103110446a00d0b40c402d5102c2c081803100c3c000c010301400003c03010f8034080c0900c406c000f114101c000d005881d000d680d144405280d04180e04078008114205400c0ea041140c0700304069640c0e1641100d40541640507a9129508601a0110002c40c03c0007c5590051740910001c00c0000040304159844410850703c1c680401031601c000e03454071303142c6103000c0c1c00202d07080c9001410840540001601901840a81c90980d201805055460b0401120603000d0b20500340e0310781100c0c2d600047c1d07106042c030060000d02020400541e4a20300650002b026100545c040300070205804d40000e40c00b460843c07 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 95758453 1250 95757203 95757223
    0xc020f3007060e03070b1c090515070e0d060b040902040509010501030b1803030a02401211060c15040302010b0913080d0b040e03180406050402090102210d0501030f020103060e060102 80
    0x1840d11920a00c0c42c000d0300c44040840201745a188c41045030501500054807082980c3d4126801d2031031b03440d07038411151050b0455280f0342048a05075090005003680c0c025a04135080078200240c00301a50700041c0541d5025030311110142d54460041c01841128500d442e40444480011040075000180090762440300502000441d503011681da034015400c003001a404688960300e2a0500e9204c2d0706801d05400010086188002000340024107a40d030545c42250b202c2d0814044025090424140061540040d031203440d140039003c1c240100001151545001d00d020ba800020981d030018180030b403450010b881c80041c00001e41a203000115103c0c12110012a99980811501403071030100d405080c010340304810b940400b0550390403140039503151020042c41220148803199079032043c0802c921862103484c1c0142c0200c030f20059a40c0001e000f40c2058941c0b6101300f86000000383e480411142d0a80044910f45030001c0414259270b0302d4000c14002d0300803010b051170079081810000c1d542d60700b011 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 95759703 1250 95758453 95758469
    0x90b01080615030a060510030509010c0819090512030c03010608060102151611030a11070906050108071b020409080706050601020601152001050c03250c020f3007060e0307 75
    0x80003440d0307002217030003c0700107240107008a08003054012000d4050f200444544030907601c0c0000c030009141c4101c1e030311400340c0500724480f19000301d85140000070304074140c01681d45104402c01c1110091505000b544203c40a0010707030303240c2d4100400249101c4000d000c0a04540c80008440e9041c220304078410780200090700c80103d2104054815106400640c050000e240800315a1080303c0ea04440d5030030750b440c00d510940300500d454074410302c11200c82d802a140000c1c221000209940c1c021b403030442d01a000e04400144101c51030340040d05566410a08451a0038041440820481c0e14090903170042400d001900041d814030b1201c400700e100c03c10003001005011084808103a142c1d034178401200e0400740090240c3d290031a5801050f07401580c0030010300101a680340c086002100c1d1080062100c1c0d51031700081000c41e000c02503c00b00000e07003035a019440341e00e004140c07003910015007800800c2c0c012440f0340206401c19141070020715070041c0e003803000c101c0c1103042680d03001c64088142c40110b = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 95760953 1250 95759703 95759707
    0x11090603070c021f11070317250507050117040506040305181908160303170601050c011b080604020c030403020904060b0d030519050a0206180c06070606090b01080615 73
    0x141101e102d000303010003a40003403000b0403c45913003040300403044c158001074943c0f014012044100d10303034a20b4144400b030040c40c00c1031004112100070200611105054043d44000c0d8850415582c0c07880a1018040b955648804400c1086580200d180440000704980800040c9407941300c440e200d200050005042200006102505a00c1c4c807411804140014003110b1b11140c45040c203100041c580d020314140e13031003203005000c000705c6c4403420802540c1d41540c070b454a0310081c1540c58001203000d88401d0600105024040511109108020100401d600c0c1c000207440042c4000c0c1222030302801d500e001d02e00401a41117411800421a01120b6041d143c4000660303c0703041100041601242595001503901000c0c0c00380740c0d2140103480202e290b0085c1824a004401081d2200d105562142000d030f042503000030508081c440c04003600e02600000d40c2c1a119003200041c0503075014860072500c041e41c4440600c000541803044105415081c02c119085d403d00340f002518050441003021344810700 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 95762203 1250 95760953 95760961
    0x50405011d04110708090307090e0d0e0612040501020a0e01090f050d0204020403050706080f0609072a241103090307150b2d01090b0f1b1006061211090603 68
    0x1d02d0f44180d40c500c211100c000e803161107510302000a0341c400c1c03441038428032919401041c6030005108181400400100130440122880d0003502c4148050761b055a003c0c0c8107001c0080300c00d52040d162441684500001a600c041580000d88890840203401b0b0401c05003540900122007640c061800340c500c100c070900500c0380d981c80050f029105036000281180145480080c5003900301c0c08a6000d12295110150342e03070385240c2403202101f01280c0c54000500c2d0b1000c01c80b2100e01511004103449040b00313480304610b54503110307190061001c640403020030b2010b4042814400b201c1c4a556064007221005d2451410811082d0366240a03001c1c2c0a00808030105800c0704108542c0c1c4586280340004e00054071042c2c443d40d1780004050075003031102d510400450413003015807040c01120141c482481500f8240180e9050420360341e000411842649511505009001c150820422564058100d400f03d055400c0c08801403541d103400685424bc1070921819200d40d4442106484124000780c030400e0312035035 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 95763453 1250 95762203 95762209
    0x1e07060e0d0804080a020306010902210403120903110c060301180c020708011404030e0d030206040623040b0618071d151204061805060f07090305060906090607050405011d 75
    0x682800814410b4002000680300034080f40740300c0da55000b02c0507215503a9881c08518181c8c491404558074580c1b8030034043d0040d8003829072107504513000c0e2400e804601d4a0071007110407106103550940c0441e04c00e5500c02d4900da420084401e08140649289042d545403485000790b45a180750301c00c2c05640c1310501e00008601c2000071100820421009010301441d10382459000f4000351019400580203c075a010f0710700b00441500e00c0581d00d68003c104680d16520762100801c00355400903280b030568035404070701350759601031280502c0c01184107810900b003560170803c2c04642c04a0540c1084001e00412002e25041050055101c001c8491f407149400310000141d06c10b00319019800305482c01144200281030320241c086d00c280c0c801c00007003000c2c0b03081c81c0060342c40c075803150300c01807941d8400d00014040c5100c09a600e900620b440c00c00110627a200d50380c203410b20754116942107050380550201701650104200003908244e541c10280d18150406000820124503500d04d03000c44203107603003040c02d0380d2 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 95764703 1250 95763453 95763469
    0x1180f030c080a050414060f1207091a0405031513030e0604091406010f02010b0f0103020c0703051c1d090f1504050a0b010201150b0412050a0203030d0e1e07060e 71
    0x140c2d10003201c2d551084991009451904180503051846412140007a150306001c030455000050300c01e142d03400c000000e4026840b40d030005009000f0403000840010381705181c8100825031440c05e66400b62614148020301d85040c01002e91613448003140810f2050541c000103e00725602c0d0585044502c80000402040c403601c919405400d82502c1d0500a41034814908515400345509980e01c1504082c04401207080c2c450700c61940390301100c103403a81001076000ea4000c00c004c040b9002a56007559994503614240b000c43c0c0c00e040302400c00e00b1801e5800e107502c00310281c0910302e101141c007102d03a0000c0c086003071003200800c0302d40607050a0000c2044000010700000c0b204c400100300740410306e0141c40600c05441c02140b120b015608154044090f1034240d003003803007034030300764401c060500d1702e8200045070603a4019000d441d280140c180700c50140c1c50034002000019841f44010610300d95114540b0b140403120003200d4002c440c01c4440b0020740c0c0c0f01084050031592180760054880380d042002031542 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 95765953 1250 95764703 95764727
    0x140d030e0901090c0f090b0301050105090a09060905041506080606060f070c0b04180506030a02010c020d3e0102060f0711070e07030501060c05030a05071a0f06100201180f03 76
    0xc0c1d100700001415881a4000005019043d6201c070320350341c80e41c6415505c0c0d44540c010325044d00c3d824801030240c1c1d4854405042c00c44001080030084c0782e9664000c2040b00c42541094005a07107800030801840b4030a100b10747c0c00a100ca20070480d1901e0302e400607845032805844540b24440000340c200d44007500c41e0036036408940041000c6802a5640719200e0a0f80c81449108002000007100c2d04c043c10700d81c42074600c0350b54058050f200712180c5600440e030507840c000080380d014a2201110011412010702405080a9500c400110501c0c8201e000c1d040f105d100c403092031041d00c230107248007181d9022501d5601b0001035080c0525a8030b44d100c080c0c0708031a460010142c1071040400000d840c0c200c498009002e508151010001c0e6600d074001121080784070384c0041c015a0080240c01c0350b0343c0c4202c0050401c00d004010003a103007182d04c03540e0405144151a0150b00000c44c0050101509c2d044085200680303890000300403800030032014600e608013440000c0c4c590341d50000030909243c000c3d01d0820075 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 95767203 1250 95765953 95765959
    0x72a02040b03160e060406050102070b0a0c0b1807090e1009021c15050a060b041208040e0405011d031309021b03030415060b040e0f060301060315020a0216140d030e 72
    0x100103c2d90b40d6001e0101c12a02c100c5000301c0951010803050309140c030507041030f100c041e40076103a83e60a08000036a549d100e10491800c01c282060307207401140b01c02c10858058516803000f00185500c51080314907110460300f00440080c54550008e10070300c000640c40351000190f10303000c58070280a0002441c404235072a030030f03103520100c8120901085040c850804032992044000c0000d9120360140b841120068003a50000c0241040148500a80040d400c140d062203100403915243d2200403950a500713040c3d6007210280c2d105c00119001c081c1c40203254020032440b60086091415038071030140048220f10070340504a900040b1f4a40d44500c500203480c0e107030040e404907603a0307003041d01d0042c142d4180e15900d034480902c6e05c400464607501c0c07081154100c640d610b01070b003d02c0c0c40b000c801c20010280906080ea066603650b100000090100f4850311903240c0c0c010005031503c030250006418800750440c840d5a5030340010f01444038140f41241624014010745a40c00766031070314a0103841d0304468402c550340c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 95768453 1250 95767203 95767213
    0x6030c06020a0c0e01060e091906030b010518060108061e0301061706070203040602060a0f0b1807030c091a0a12020c01020a1e120c021207050601050405072a02040b03 73
    0x311103400080c00c1d039506201e9144050031555070700600640b014207000701c0c40000c1c0c04183e40c8102e403500c400c1c09a00300c900035408040381580241c0c802d0444099610444a0b1000794004026600e010300c0c5140c070801045005440c1d51801f10300007042c40200500740c0344100018100d80c4030121942160401e20b1101800802c100b40e02ea50814440709400c00703550903a84507103000100001d1021090303030101e855580042600303840f940b13140300281c404015200456035440e074005120b503440c040041d402d084440141d030810f05203003a0007020b41d580401420709103c000b1800304511031003045000c1030700c090f4414103920390800132002c460f0030000c0c1e41c000709101c0c000301e030241101e070040d40200300388031407030b2100841110b0403c20f014000502503001c802080c0c1401004002c001542c02800c0008aa0710503181d0002100f540c0700055003143f14140c580f58480310050025003014480c1c150070000d9801e081480518003440c0071078982c908089481102030451010045480305d42040c0011403008050725 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 95769703 1250 95768453 95768459
    0x191101090c0b0903071203021b13052502070303080105120c10090509012304051812071a01030b0c0a0507080a0201090606050406260a02040501030507170105100e070306030c 76
    0x410315080b00702654401d001748100003074400c0c40b96103006c84550b0315401034509100502c50307034030400204503407290f00300c000c241000501e00c01910509104a005c3d0388400c180312000000848903400407c05213065603c099401c0c03000c80d03082040a81140e40491b46a80c01116401c8102e0a010309640d8954001b1085290100046c0d000161142902c0096034a54100d0303980b4801d8040b04691144403480300840b900a00f0094245074220540c4000c45010082c55444034210f410b14002c03200501d948c03988000f090304008c1180210788031400c69070305804a541e550564031902078412019001d840000c0000820300078450042043d1000320382c01c1035420b07840d0150a200a0f01030a101c1c8401c5500b540381c400086038038a440d1090b6001d4441c441c800a03103240c5c43d060f83d0401c80b0240b0164115910400203c000169140d000b101e0195200d600a04151440e2500044103508500346082903039041c01c0401900c1c90080020908a40b04c0d03038103880268850b8941503009048a410241400b04850004 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 95770953 1250 95769703 95769719
    0x4050904030f080f013506070e030705090106020d0507062301060e03010e030d1a09150307090c0f03050402120a1b05030304030b010b090612040f1502191101090c 71
    0x54840380c21a80300c848a0355075024000c988074100b4001c10f2980d00c1c076140b150b6180d510b03180385141d4908402030171604061508448520b401c4042354450001040840d00c030602c2d0500b803101c1d000400c01504c2180455040c0350001e9114485030042804101c4045610001c0c0314880c2c11040c5a16580000d16003c4484400140001182400741c5000f241c0c043c0301419490405100d04648415100051402e001c24038a061024008024114a58810310714030641c0b5580c0d225580760080304c07008203540003e1000818141440c00b254801c00c4907619100c0d41c1e41046802c0000c20032220242d10780011566900d04c005542d403400040445c2c16807090904400c2009018415446030018a00d03119007480c0d90350080654070b220b940001807600b28400010480030310030380c026061660000700180c0c02c1c1080e00362240ca404000b02e074140e40d0300a040d03038440140034034501c41104081c0401c0c015413030550103104401d00a001c0b121140c04001600400710210303c000c0d8020005903500580c98440d5a55808007 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 95772203 1250 95770953 95770967
    0x31b030f220b180c03190c120812070302160c08010b0a0f0b0a0c12020705010801060806090609040501290a05030a200303070606060201140a1509050c0405090403 71
    0xc04000d24030305212810000695001c582526031154080c0c42d039a4400110b80210355a41e07400c06441d00c1440c41c81c0346070745d8007070004540688001c46100310f81403080c1845100741c1050ba108201003d00d80502c0000710704039204550030300e01c1c408440005620b41000c02c0f4000d10400f403284440c00c2082d584031007000402c1810b071045501c20f00003070085038400380401004404500c907a600e080c4d40b800c0100550400c5202506c2c010025050110344006203841d41c4d082685501c1482005030001c807010300a5603003240026015104614040b0903e203030501c0424905030700079003010311600c600b200080800000350044030f03903400200c2e9220b202e620301000c58035204031003107010b600c60b5282100201c0d4505000888505940c0c011501304412200301e0322840030700b50400c2d44076816000800c140008102c00c2d010700c0000b420254000500b6189000341c2030b428907405040040154100401000021b85208801003505d00140c000529610b828400380000d00c00c95100a801c075038020104014581c101131 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 95773453 1250 95772203 95772211
    0x7030c0209060a18180203070605030f0c04060c030503130c0914090c240d1401090f0903020607030f140c03060913120c02011101060b03010503010c11030d02031b030f 73
    0x6101c041d6516568100722244001c1e01800000511300104070b00d5849a85c0c000300840004030711802e608044030340109080006507003181002c1480081400400464100703e168040140c08459003801d0400200420b0040c1c18800603040250100100f4911000c00603031440d0039900003007104402c0d51b142d101300094207145c40807200358a13140c00041d45c540320101740305000040c02400f4070800c4440d400009440a036503004c89091600a0000c5000000c40d0300c43e0a0420b4111220313200c136503150800f54810355101c1d02c0407240c118280122407000940010fa03a07904000c1904000c5521400748054100400d10500f07180c940c07404803070a01000c0c440850095029660580c1c61441655895a0310400c0c4013600000a28410000d038a0102243c071138100c02110f2441450843e1080000d445c034242926519007000d1076041c0c0001c010044c0e4030f000d100d0103c1161150900210203460048140d4990260310159610150000006400c002c02030006056442c9607003495a1681403c00c054001510116 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 95774703 1250 95773453 95773459
    0x90f01060801020304020a03020d03050d0e2a090a0c0c020618030120041202120303180f0a051e0c0d080319020f071101030605120a021e030a200607030c02 68
    0x94404507840d0018000c5074840c54002d40942d480c03911710b1b070034407900301e8000c1c1c000d50800c034040c4444402080700303000c0c2c45000b071140801400100c020704c12103082541207000712a002c120303012883c0d07203d80380c7c800316507402042018001035921441406803580031403004001d45c41701c000203003003031400030000c068980c14100340d0081280c1100780e00020300500c5400324081c40340d141408100122500c0c1c1c06c92141081c0302900c4441c00402e1050742c00d14580003074400700040c5401903203500c08000100a0403120300d036690010034400401c0e0300d0307403600c484115000ca0111121480141480c01080005d03241903030000e082c140d01540d460034540300d0381e0400d07070340e0418003903038060004c2a6480c41d0080d510300798020a101460100c0541d00d100555201010450505449010005440e40c0303594600e03c81c0c4a000c000f9101d201103510400120b009280540080c881c41d41c26503000d1901d002402d90029036025000d5400d4008182d0f03105507480b100840154006400140f180415034042c1a0202c4d080c429 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 95775953 1250 95774703 95774711
    0xd02030a0b0603091009060204050915010324060e0f2d0a0303090b0307030e010501080a0615080705150409110d0c020606010f05130302030303040f0b0709030510020a050d05090f01 79
    0x201c041003958801500d040403070b5804a54000c59031421503211624540c031400005140c41d5844c4081000b0250440760911741c48403a440c0303c2110758140c0140e03604031300c18400c01609a1000f011318400030060780100010400542051402c0d03484e54940310040d4000141110102850102d406206000b611f002c2c005401010103049100d0500c030b0081c80981384e154540e81451030600c0710400c42c94000030700c0041015101e0302c000c02d03200801e00c1003d018042c09005000300c00014140a010343e484c0030003000740d00b02c80d48401c0114050224080c819504111190000850440010255802507400008455282c00401202501c026000703110180c0d52103014070088613400d10a0740ca0b010100c030781c035021962401c0000825880381c0001c0060307042d544e180f101603036220f80200f8035503081100c044417202103c84040043c4158400c03655480b5034070303250440d001405c555030107442c1d100141403c4180c540120300005624040c00660307460f8880c12004110b00d15141940555480040d070440803d5480c1c = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 95777203 1250 95775953 95775971
    0x301020f04030c060206040f0b130f03050306010e090c030a050403020f0106080109020907021f15030b0901020706050906090d0806040204170a0c0807050307050f0a12030e09060a12020f040608030d02030a 89
    0x444c00921a90704a07801c62100e200340d1719000040080246240040c820402cac003080010b00842404850354001d40e81c56272240382c41c0700050441a081040300c0c0c0304051560401500080c03c0742202d41c4000359001c081200d446510b0242d250200100340101c15500b42100032612440c154800031b2103d002310f4000d0b13141d45802c002030741c407100c042111400300d0030112115400203900c6d0308004a80b129420000c40e00c5556512055144001541c104026075000500b0350b050203068044c4980020b10003024041a00b4260b500a41d07d400001750b440c24070400500190040e0f440f42c0c150307401011803418076028101c604403e9a203540c0000001c86500d0204440030615000c00101c3c0010307114041c000302880740c102400c0110002c0c407a84620b6100044100c00328050580d6480141581e1107512219945428030003006400d5500030030f80ca00406040e082044400c6004c800c000d4101c1d0169440380a16921402190140585810004461000060390360241801c2d60040d44500314012042100c504 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 95778453 1250 95777203 95777207
    0x1e0516050306060a0c020f10050c070b0903060106180302040518060c0405221d0307050f0c06040e0a0608030301081b03011803081f060e010e15041505090301020f04030c06 75
    0x800e031082c0303411900c1480040c1c820707801a080000140d000800600c00c1c29413000005080302e0003561424000345001c507850105144c00c02c03210300a40f409202c00341c14409002c0c0400c0d0303100414130a0380c08200740a00e10904075040315800a0207107402410911413490845401c0d0464004115113050500c260000229008642c40075501507540040030703540e40d11503201c161600e0313881150100603002c0c2c0d5042214801054121038a80700c022144c0031316100c00f1a400d01e64144060045250030540041026141c6540c0b42000c0300c0603501c00500c20006602d03001001d40040500740c0154119101c00000424ac0707940001c0c070b502030b48140c071081c081440390700d50130b060983d103801d80ca50940f00c040c66184000280541d40c000c1c1d01a0103050b503d240c44851070310003083c4064907800200070a01501c032a02d51564012180c580005082e2603003417005402d410858070a1150707210700b205070645810300c3e0001902c40c000b1944003501c010020b5483d01c0d07240500d40300c0d82c0d120b480b04840b040b01c584000036902d4 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 95779703 1250 95778453 95778457
    0x503011e0b0307030c020c2809020a020309011103130b040f090908070807031b110108070203030601090306020d090b010306020910020d020607030c0e060a080103030207090b031f1e051605 82
    0x150038445102e082d51545182038020b0014070b8a42402d5014592441ca0030307865600c2c0382900100c20f9441015045401401e0034001c4c0d102e40c0010f2406401002103010058000080310403441003840c100c02d000420303685407070440c02909481090810a10800904030301402c01030001c0e81d03004000044095511200002280c014a00080031103c040c03250801203072404002e07061581c060705100b0f60210b0803190314090b45801c0c010803659109031840c8442507513031103462150301c0305071400210b02c0d40c00c1c5180003800c024214400107143e60303000240c0f4404003460703402582d0fa0b5a80300307081514a507100d00c3c100b8082c0d08180000c6008045001c184030320144005100000d440b00340e0090026a226408201e015007204030003e81884115004524241c644400410008840c0c3e51104250f5046103002400c20cd2298000c0d038950341010b212082a94001c501e802a00910201c541501c000a410f40805011045030b03111040e0300f00c410038090300ba0590800d5204005e00d07580c0e1074a01c00d017640103445034 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 95780953 1250 95779703 95779709
    0x309090e0703020d021513060309050610120b04080f0d0501031103030703080408130506121e0c0d15080a0c03060b06030f010b03101502010603060608030705030715060909030503011e 80
    0x4200c50941310140c00e008100c0c1c1000f141c00c0107228540144005006001042ca510500001c0e0f661545c00c4103005007400101e8102d00b1b211303450281e00d40782c14880c00384040b000030040d010100050101e010080c01c00c1c100c1d905410310410b400d49811001014030000c11091006480030003268a00a40038a40881280e0a003170f4103407280c070031360749440d114140d02c0e401018064482181a0201040720b5991001170404000011456542c03490901c034050003210304002c0400101c202e81080c01003e151440c160349008024000000b013084180340c41484442c15580100900c2c00340c40b030800f092040b020070010076a409400240010b400f80d80902c8600e11045821950340015203006100040d60800103580190304800000326168944c0c205020b0210903200550160307566800410400c013403402080c0040c04d080b8081d50a060f51600e40342c2d00c034454030b44003e00760141030301110360131000c80e8440b60180c0740d040c004200f20f207e20302e40038000303510a00a03132140d030244e2254000f40c081041c400c0350507 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 95782203 1250 95780953 95780959
    0x1202150307081909020411030103110406060906050903070e010602030a081b041401030b10030b0f0301020316081b040602070e0c0c071505071b0f050303160308070504030f0309090e070302 82
    0x30307650714400d000c06080f2902c681801c0361912042080c015903240c0c000c42001c181d1180c680741d5207503d54038100c20b058088101483c002d40c14490f04000f41a0800b510320102c4401782042c2d6651100240064100f143c0d41d000f0610b09100240040b4100798008003074540721140c1d40340c0c001c940d1603091544014958070741c102600ca40040100f840b81e850b8040c0800712104042c10302140c0300803800c0002c1c2d2076669400050700040d0703945484111510703019143d022b2406055000f14610300f4104182030190706010400d42c188041c640201c0c180101440000c080b45410705180750712180c40303003c000d48645881c80b402c0b03150214000444e000490030b070212015401c0100080003401c0c41d0403140c0c0300707500c6100030f00000d01506100c600302041c3c0c19146880100e0b81d008649091a042000105204065812480c020340c41407003080d4070b0000600c4001c95107a0903080c80c0c841e81e070310101c0440c0d65103d04c0d00014050040c1c06403032010141c11000e4802076a03403242041c00506c02d86000740340e96050912010754 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 95783453 1250 95782203 95782217
    0x903030a180f0320011407020c0a08210f0a08061801060c0213060906060302040e0903030609040f1e03080403030b060306030a150f0e070303090911040b0a17011202150307 75
    0x40060300543c013041c0c85258a0b9031031800d0310003ca942d682124030b440340008803030384404100458154180b1800345280400c6800b050342a04010565664949840d0190201011003d006104180100c16124060028000030f40c0e54810031800a011080c1910f0b07603802080e07456540c0d1115164400524140c42041d07035108403661242c1c08101c140c40300203900000440c1d51384404100d14140c2d0007040e0103000035403009603440e03140c104260641e201c0200702101941003070090100c00d54800b42c0003a00306402a0320002c240c003ca0030501c0c102c50f580c2440324a544501d1100c84100f640110b5001d03c920700039182081200d41940502807644400c50b400b41d4541c00c1582e00c0da00003011002e003100b029020020001d1481c240420810845480c101d16042590000d0002c004040e03101c044038010b0013069a0900403e50a0114496180140e002e800c40d8240040b81e20f5403010312a20710000c0058280c2240282540d40b07060f01c07150b400d0038803002d0340905006911030010f66145401c803401904103950f101 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 95784703 1250 95783453 95783483
    0x11030a12050304030903020405070e031006151d0306040609050f060910020c0a02090109090b0c0702150702010203070611030a0b0607080304020d031b080301180b03060703230903030a18 81
    0x100c0582c0000e0040342409005880071000d43c88921500703102e41d005446103512420850105464104500c254010890810303000f0301544955110042078241142001800036a012071803800040c44845010b0701480350000b00014481c03140c00046c8000e0084054408400c141400140c2f1810100d503a0451a44440303211034241003568010041e0304001070036520450015800211401401c0c0e001c00c0d01291a51504002e01c200340c01c1c0c02d5003100007039901d02d203000c0c415804500c540800c40b107841090707034012850405590081c0200c42c00c580c0d10030402c01c1b605841c046050a01e1304240c0d210841e0038906540c1c1071076810319400b07c8500c4c5801400303c60079552141d08020045000410480030030004164480c240000c1c400e84600d05442416090340307a40c14500215454072040090150060601c40706000a03180428029002142d5140228901c03403569114006c00085a24038140c048a64013007018003036012000e54050300d000d001c10f100c9085603603501d20150b018540c000d08029038a0317140c030b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 95785953 1250 95784703 95784707
    0x3020d050313020d0b040b07081603050a1d01061a0720061902010e0d140304031101021603020c041d0d032705010c090e010807060e0609061611030a12 66
    0x40c5500807264001c48180168035400301e040130420302c8040b100b0340ba1500510080204c05071521740d0000061821140358501100710400b80340d46034108005050f50b450115a00d028a81c200b40d241242003c00441d040c443c03100520300030f00442c07042071101c0e40a40c044000d114481c0e400c40c2c100301d8100080c159210701c695451036110740c11404e91a0b00403000c0000f210f26246c600060343d151000c0b50000a0303031000d41c0340d00c1030a290f4401c013101c04001c43c0c4d030b40310040d00344d1110540340c00c180c15190103a001111400c0060081c81548151012032240343e00d01030800d64009030655840006480c1800780318000018501318007405020089203412000c08401098460380c0041c508a4200010b0405041d806c1501c403100c0c0500c00c0b0607145651502c2d038038580c0c160810603400040001c008011519072410101d50f49440305800b4600812002e82240c4945a0b46c0e50161074200200508c043d0362201000862021505807880c1119014002d0415035441c1c900840d40c8042d10707401078021040d01f2070384030301 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 95787203 1250 95785953 95785957
    0x903091302090d06090b010806060409031202211017010501050303041509030804030623190c09051801060906020d050702010c022706041401080a02060f0d021c110703020d05 76
    0x1581c001c9404460f60000c1407140c0030b00f01c0903501a8001409075410103441e030781015030040220380218200802040001c2d0b000c3d04007441240048401a25144021812448142541c000200308100101442010055240311104413501030890b1110040e0444805080e0307082407007260b80c0360f0414481046506000302d04d0030b04d5480249420809203880c3c1d500d84165030030542040da00c081da280c0c0c0820303100781ea415030031031010084592100d052030095040c0303101c110000c0844480c90b4a0310310784013410780914200c001520000b00340b01010400c0c0d04604410704400d11400000030440c002c0015441c3c00800c401502008994996180402c0c81d001942c04071100e0000304c0e08031030b010000c00c85800c0410704d80710900c2040f10520001d420310000b007105581300305208001034103a00713004001e02a0001002c02c00c0315810b4a00da46c4072a1016070707401c100c1c007030408442c01882c000a43c00743c458504510f410949054244204000105224002d142d03005081005006d64407541642e422f01d402140 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 95788453 1250 95787203 95787217
    0x1090803040e1e041a06030615040f0603050a0f060b150d02030601110307030906021b0d15021c091502030708060409060e0a030504030b0112030804031b0b04050f01050903091302 78
    0x20341e814158407a400403d5003a01243c1c1a200403c680302100c030042c01802c595900440c048008200b40d040449909903038414400d00d035480345542d14001c420142c016007003c0021500f1500750365818000d4200600c192448040881d03069250514010700303407170984100e01c1102e41c80c030449410302486100b02c00017940058569414001011129242c5000070401810b80d5403182c2e48000c0860314140c03000c0e203090342d02c10029101c100c2c81c408095540c1c0320070403907242c065081194900034041c0d00d81d05100038411032040c06a1180c810041030101122078000000321446a4040004908926030f244201c2c0000c0e01d0545c0061580e10100e212840e1580000c000140240c0000405c0010005090703e004204001140803034404601081804012003c0c0780c0100072070404004800025607000f445451f0060008090101d204881850201c07072000d9100c016502008030400f50170700e03003000c030340c2d07140b0f88004101c0d65070034030f00011b001c01c0001c0196820458082d0421103518118a0703540040d401c401 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 95789703 1250 95788453 95788471
    0x6080d120f15031b08010e0c09130204021b060105060313030309051204090c12110405100309052a0307051c170a0905010f0206041203020c03120411010e01090803040e 73
    0x1012100c5114241e0282c0002584555000c8400d4040030007082c100680d03ea001ca4400e034035003003400d0030703001001c104c2c242d0406040b101122503582e40e03150349101d010880c0c00a9007091010403006239040701c40f01505c0502c11544100d54540e81d0301c0301000344500c0304403a00300500c00d14000010000b402908051950303441001910b451070040380e0881c0290b0010b502a08102d91136003103100301c45800c0480641c0382d1039290014230a034203d40e450322005104a124041c0034011950841c16980d201c1d9015440c080c0e481410b0b41c20346030300781004d400c000e14000d40c02c202d580d000c24211261480c00007548802c940c0040e0443c0403a0303c03002484c5990b004102e4090352070001d00003410010008103001080c0c0300b90552201d0300c021303003000c0c0014a410303610385c507000940d80108284004980d4160301075a801109150141e0380c0c080b00c215090440c06000f4110100c592484148800c121080d204404c51030001c1e81c4401c0126140c0004640c12032030303445500c03507940042100740a180361800709503a0003c400 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 95790953 1250 95789703 95789711
    0x91b061605010507030203060f030f070303210c020303070305130b0711031b010c3203040201090902030a05010504050a09020604030f022809110408031605070f0909020406080d120f 79
    0x81e44030682552412a800d5001984c0001000120302c2c1c0780003c0003003440190010081480010101aa6000a0f02010341840006580350002c50315242c41071480c4c895140040c003040c40200d101035503a40043d81d200d80030a007840d001a2503290083c03554803080d81c02001c0100305485164040d40d9429461418006a020420004050743c00b06100c00042e8408000009040b440303c850042081d140c10b001141703030f10000341030311a00882104d11108400d07101e440702c41c2d40351a03500c0142c40d40c00456104080c400d00100801280a0140d4003050498205a81c1440b203960717107046803801ca48803110003d6104100740000c0c004580e000b40c1700071440340b0190402900300030700c00c8a480460410318510402d07404102c824052189a0f010348040c00c20506041d0303003040c0c1402880c42c4c6901581e486c0c0d070f1905549072400317418030104000d80d90091000b0002040050f465600c40b501a0803031a105074081c034180400010b40da40000385144c90591950b84000d49284119a404050007920644d0070000d912 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 95792203 1250 95790953 95790997
    0x3180301060f080703060b19090c1701030302010c020615031b040207020307030b0a0b0102010c0f0e010207090c020d021504050d050d1517010e0706140d020c0115060206091b06 77
    0x74080000007070001e403002044014031317610b0b004055400080340f1a00800d98402800c1c036001007200d00c44c0640d42100c001064400e8551811145450010a490100c0f104040004180354042d0b10818901d030490382503525565905501000e500f0070440400e81590100c0580c540004c0c50010340e42180310010409454801e40c0d400084c0382002982040e44d402c01c010041c032407c4c210a00c40d0000420007030009004e1074401e5040503250305400c040e01c6040c4140788103d01261ba1080c0480c070042c100e4003204100c103155030341c4000d58a231003490710350000d4401c074200e0b05420070318507441c02d21403030303210300100000c3c14070240880b0b06400c4805000401034541290940b0f0754010f5403220040c0449100c40c6d2501c685140340542510501e0b441ca80207078100304424411075a20a8000030300840b500040e0f60b440a0150340e0100a1040541040c00e6500c0e01800036001c0200070340f004229002d0360708940554030b480d200c0b6502c41002c01c50341e6103e400039440807085410104050101c52201c0084240c00c109 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 95793453 1250 95792203 95792219
    0xe01020601060e12030409140f01032012100501061101061518030b07020604020a0b03091b0d06061418130204480f0203070b040c0b0c0307120503090318030106 70
    0x21a03041407c030a92a104042da8042d0348140c00c650040c00b40c2c117105259451034641200d05000908084102402640c01d44200c1e19440510b0401c984031900b191098942030842c2001040203001e0600000d00c1e400d080408603405028000940d100c60364048007003680800700390f51200080f4009002c040d2400700020101d800f80c0b4905202c2c01c013076000303000a0715203841004a9501c154000200000c2c1c284140109143d000450300004000c1044100e90911402c00141c884011031500901701402c01c580460a94020402c0b001c240b041a6052501d0107031141001c81e01001c1110004801000d110785070003d440c00760410081102d50640900c45080c103002c44003040909800d1407206100d4009030724100c0b0104044480304030807a40703000c900c495950040203407280b26603080a0f051800d040c0110b000d0200300d803020301c02411040b11450f03a500000340500d450750012001a18120001a1000850344c0900c0c00c4a2281a10700091481c103076a9144951202090102c1c41760199a125808510701e4 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 95794703 1250 95793453 95793457
    0x1609150e0a060203040810110d15050d0602070605090c03060c03130c080105041709010909051009020c0604050705040902010503270d111002090a23030307030f0206070e01020601060e1203 82
    0x8020b0758061a17070f480c1030526043c40c1441c05a030b04460140780602d40c6242901c00001d803513441112680c003148800215001001e0703c001508050307846604074035100100409907000380036182c41030001303020960303507480c81680700c4010a0340d494142d0014000070314182d5190000310780c0400a4039122841c032500d916080810140b942026045a541e0010300c410700c070b002c0c0120705103005032001c0f00d8a000c08540000b80100d03142c0c03250440003511035012900144212035000040c00099100315180c2420310821640c0b901d081e2415181c60040c1c00c4042140c0c20180100390710250182c440c41e1454031000440064840350004603030358862220103800c2207020030711052500104d80d41c1c40e940315031006030b15a4288a12242d122440318810002140c80f506c90860780c000704c4041859543c03450603d84000c043c004d05030401c203503050100281d07540400d50032441e12581183c1c0c560817602c1e943d60f004001e80c0d16183d80040d49025034001401000035510400c4110040c07030000d415102140d050303140300c510755 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 95795953 1250 95794703 95794709
    0xc030b0c0706051e091b13060504020a0c030908030a05070809011e02060901061409060f1302030408040f06030c020a110a0b0409020c0d09060c030804030e18010503061609150e0a 78
    0x113090400e5080408000045030760070442607000f5080901003440e4a80c44030450115450258040c1c000141c480005540700d000245000361065584c0c0507007220013030a41d204403104030045800e660300801c0c0e100001040d6401ca0b1020344482e480d14041d919100703016080417120390304004940700789800039150035001840d60011600180001e0410410f55820748429812458a000341d2150541075995002030003a004403050b911100c1d011101d80c0401d0340b1620b107000040e1042c0c000000d00080180020003402190701186002d0030a07a15100114160341020440034010381c8502c10b0705020034601c4c554040e10650003080c40709480e0741d4003159162500107070300485c00198040707030409003401d05004da40021541c0745824041c032420884041e00d610507200d400b40810030000c00180c200b6000301c2913008070395002044076000340c25007400402c9031802405910b02a000c0d00c0040340d58481e07070300b005840311203690b100c01801c6800d240d1411410130a101d500401c00c2503a01502181e074403444aa6005 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 95797203 1250 95795953 95795971
    0x32d14011409010207031b0309170a0302010b040203040812060f181005040905100f0f020c0c0411041202060715050405060f01080c060a0513030804060201060e060d0c030b0c070605 79
    0x403015890503101040c018071080c00c2d079004002481c000b95100c4200c010a4100a00039000980c8600b021100c00d50700390041c049010b02040c00c484030000004810050a10a500900c010b00092040c08160300013941c00030490302040c09510100da10f0002c403650300020240280045030042e10010302281010035440030003d001c8000e0010308004014903101600062343c0611017440d09548041e520101c503446004082d5a4030512840f51085820035a007903811310710309540f61a00044041e1300c0e65005120144654a060100513401351800700350307002c85001c0002403d11020720780a112655111807000c0f1940340c0c10313068841c103010581c4200c501681c0504003c5c035051401d84111048450107800c0b01c81c5a40c005c2c50001307000d13581c2c02c01303c07904030680d80391268842030848440c00f8a40c0315074100801c03216001c60081541541544010103c030450300e895031258584409104940c4002940030782607802c150020302c0840e40e02c105503604540721155641c641039061b21400101c1d601902e0303000c1 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 95798453 1250 95797203 95797211
    0x10204090204091109010801030308040305040503070f080609010c0905010f0210050f010e07230c1f0203160c0807031116090203011d0907030b1302090405030c0610032d1401 76
    0x1140f00302520603078480e00e41014600e4a0510510b00180440505100080c1007055610009007018402ca0549000340303030140442d03400a031074400c040b050900034022003045100781703800104a20030500a01a40400c0c640350060090300f00b000440c0c1d25464000100251300c40d0822041848500741700d00c07403051141c02104c02e03655050208007413031100060708810410800c5c1c40104159490000032400e18810540603a940b0168215a00d0609401383d540410611300402c06003004801c6400440c070552001c480448070030040c0d042913400d42c0d40c00c0005480a5810b00402001a020f100300441c2c1c8851b100c02c450752200782c2e058199104203140c0000788040d802100400460803c024a44104265254071320410701e00315400959858844c4406403a00000c1e50229841824080081aa00d03802401c1c19156180604186039680d016a540784514845e0b2030024201085025026003500d038020b402c0c156207070710048030911920402c0d0788039030801000244200091490041c4480006002d0004a = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 95799703 1250 95798453 95798459
    0x30e030f1e040602031204020a050301050403020a110d080f0f0c120702040b01030b0915151b06070c030903061a0a090e06060603010f030308041b29120106120e010204090204 76
    0xc4000e60890750140080410700c000c1c03000d16000303c1981c640c43d9951500e04032950320741c00007810b01c820f140c0c48280c242d4039007818841450b030302040a90840b030255194000200c5458140200c0e066400c0002e06040d40910043e80c02030943c10061800c258900782c05814070701c000310441d0420241c8826080c409000040c07103000c5083c07900414001c54002d080030030001085402007102603030010064900191403020400c100c1d61480c2d66a4280c10084410325201c400c0c1c038590140581001c40402c0861040400003000503214805100d042540340d9079842a80c1c0ca907a50304805071020011487c21035841c00a03401e055101c80d020140105601c2c540802d5002d0480c41d11400c102c0042c14a41c050101000140089a0b1000e10750048913414544400c0c81e070f489081980250700333651000f00c140f1034241c2000401c19084156161001c0700750b0382c2c1da000c40c02e1641074204a4490405c4824000e0f940d01c004022143c0128207136180c60b01c2d841c00225800c1090703680700d42280c0c000c0e0807100d801d0340d01080c00c1c = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 95800953 1250 95799703 95799727
    0x408210f0f010f030813090c0504050307090603030c08031003080f2101031e060605090114030708030a020c120a021908010b1509040b0d05030d02041a07020108010312030e030f 77
    0x465002a2141a0481d01c0d50401150f041c03d62050301000d07101d20b800140d081203480a4603100d000401d0415000c04c401d603180c15004080b03601130300c641442032250b90004078500420388201c90849505403201104a121640e07000d003582c000400b0079080000508002000c140094014075003540032107086940d641504451400031030030305807030042142c456401031000038681d8420301180004000304185030741c59458101d000e0241500301c01e07009125940002451031024045a100d008120140c5440c1d9032140c642c1681d0f401100300c00b5006034800c0b10a606581001105e03142000300303150a841a41c4020713004194003102e102c4404c8a090183c100c108040b031000c6c4038006a5010807034000200c00c41da903d010000c1e0162147c00c0c1d11032030760f80591005660f04c2841c06d04001e94040c0030780762102d11134507003c8000d400030f104038404901c8007820b0300c401c81c1c0c040c0b0486440c0d0307a0507160502180d0071a02c617480407400c10400300701490760b42d0500e0006100e08102520f80300030460802c03966600c0080721 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 95802203 1250 95800953 95800981
    0x310b030c0304032a060e101a03070506070b1603020903150412050a0804062a09140132160f02030c030a0503031b0d05010b120105030d0504030803040821 67
    0xc0030304d166139400d03941d880902c00509950200c42e001000842c06406904d44c4a0404001e5842d840c21640381030301ca0360105076600c0c07071b5502d0303103d003201510f003010769507c20300003503204034400209000c20240018000d02d840c0e0500101c0b00c001440c005003080c075040701091400c03840060108a814034041080100044401000442d0007645062800e000080d00d01904810000e0001460552030704a55000c072203c481d0510140300308a2034404844601c0c043c050440c0703156000798215090050a205840d500500c10f01500c1d2245002d603107521901040400f12641e034011802801420130000d01891101003981020003070300440000d071200801d40304140c601100d61081900a4200309000404a030000c400c3ea5441090380c50002092a48500d100780c5074424084641c40141ca42400482c080400d14083c2c03000c242d001c6800c0d00c20b640c9510801d983c0c0d0317254014003400030700100414800504650040c4d60450b214404d07050a0070340000c0c1002c0200c3c6d0043d4030041c210301010411440102d0750b45 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 95803453 1250 95802203 95802227
    0x60a420504020412020f280f080a0807020f0103060302130c0e0d020306270601060302120601020106050303160f020d0302010b011205070e060903030d050a1b05310b030c030403 77
    0x3074114605442e20b0002004402d080d0006031007200c1d000d050b1107280e02d8084503424004050b00c65240d8864140d0f0490312004000c3c02207803003442440c500400c01c0d0b40001000710380c0c00c0d00000d920742400d40c0f0313a080042000510b402c040c1010b03241e2100100503100d9591a07003070404803800c04910718484c0c0200602d20300e080f0b0740480c0b21b0007080c5004805624080b4450360010648410400001820078242035030720031584140e0f2051285800010310250300d80d001e0410680001815001600c0ea6001203098030094043c00d80d041d0810031041403110032051360315418a10613030000480c0358498001500210720107109401503515401118071960b444080f21003003112900e07040049081140c0014003001c00205024064800042d64038810342d4104180c80040802480c240310501d0b040b450040907040205600003511101c120009865000710155a010a000008004d245400a8940344a008108000314180e801c903940407070039000314402107106025481c0056070724109407a0041101c00128 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 95804703 1250 95803453 95803459
    0x209011101090b0a02030402012001050a050c031e06010e04090b0603161a090d050a03020a1103030f0f0d14010b131d0a11091903061a03060a4205 64
    0x4802d140004120a51a40c0c019200e06801601d82d9079900c0107846001c4d8600810354500078118855200c0a01500050711a00821800f88003c1c2c49284006129001c00d0310a40203418691000081c8003800e115030b181d20540500d00710050a400202203000c1b40c0042000f0703904400d42c1000c00507282410006a40a64280031820504528285651203004001c00401c0a640e100080d035040710794640c080118010741000a81d40d6584040c90007a43e1030341c00003401c6852400440c2440c10518011064440780b060b50000d00b40b414426004100182c0d11840b2040043d650b1240004440904104030320b001c0d12041d20401c0c3e85060948045001c40300d15441070f69108561031141c007600d142c0c0c44100e50041440003003c0b40c074040c9240b10003040d00a81079150f4020001030441d228500d82d9541c40c00459020b40790401c842850180340300703000707000003940d290141d01c0040030a4400c0240e501240c01088450f002c104945000c6011411103601300c040c403610340111340003181d032940c041d84044004110031 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 95805953 1250 95804703 95804711
    0x11220602031908040507051c020f09060a050f060f0403051501090204050a09020d111602120601120201081e01090501050f03010606020613060b0a030807030f09050a05040c02031201090209011101 85
    0x1603003440c000c0d004902c072410800200d200414100003040060001804c40101800c40b000c91202e5152411442a0303002d80c454902c4c190002114107046400601880c0b018107000403a506050034880d08210898595401440c1004541522044013014102a521031406800a8840803241d41c46011040e041308001900c1004200469940d0a06144c1124560200903858441c0d03100d0f920010302c3c61904002c202140001c00c251813202c58140c044109208540c008030180c8841076580d036500e401d0050340c0003003400b0307608a805503005052095020070307200c8006114012100e440f04500c1800c0c0d0098114a80394030046c00355150140c03103802c03151001d80007040500d10f0404000c1d520200600400310b8000684881c10501c10301390071009680c40054140c88140350380b444c09181a501960701507000a03400420540c5251181c008081105d10007422038074ac1506044c1004010400c8078060029440108900e20302100550b04040c003e1411540060325152094000b4090740f010075079000550b450 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 95807203 1250 95805953 95805967
    0x4150804020307060207080a0b07030f06080601061710050d080f040e040b01120c060e0f030f0a0201080f010e190f051008100b0102120906042d060e10030905011122060203 75
    0x24030010041c2e0070035284a040d45078290302f5402820712803054032155040a4011507030708000a030081c103c48096588100403039008100c1d250628060b01c1d2001000d041c2401003040f40f0300001c40c461445e000744031082c07614040c25003e40360365000303030300101c2c01692400c00c11042c0459400b05230300400e48400c0c4502c00030899640d405461080b40110414044000030340e0304240c03244009503c4082c0c028044071000403694450030380d107202564040340045c0e0104000b07107241382c0314800702d4102d45030445a0700d0180c45422040204403a000750046040d540c541040c00d0142e00c9002d502d01403101201481c00301e50a0030461810700c0c0081c00c1070320019082440307801403a60300280d82c080e0300740c0d40900207490382c020000013116071117654046810007528868800b1040c0920280440c005180c6001404031991054203541c90f50001d0141580460b000c609260114040c3c1c108183d5180710741c1c00004c161190703a44020746500081880109440c804c4400e6442c20803140c006000b80441d40029401c20704 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 95808453 1250 95807203 95807219
    0x10501150e0909030d0908040807050a031203020313080d0f050f060d020906030109240c1706090a09050616110613080a0905030a140c04050105091b04150804020307060207 75
    0x12010100d024114002c001000204203000343c80d1800000314007802132501c10306049034660014020400c090040000c001801d140400c80b610403030303520503107240021020782002c0c0c1c000d4000500d00210a50341002580010344420010b0141941c52600000d080840b80350850840ba802041c1d040360845690910401d039591311030b030b400d48640c1144d078204140e490001117409071841701401041e80301040034402c0b0210440c695449000c0341c08070100091001a42c080300c40e04581c1d41803c003c002000007041090410044072a444075002c0c9010480400c82d507034851926034201c1c4c4a42001c01c00318070394152194040c441d4020350100360000e004c00d04007103010410060440c0d8008280b00c0c0009410300e2454043c2c04140e000781401000e850209181d4244807058450414601307102c0d00440c1006045403409104850503240b02a041e0360980d81e034021420b40b04001b00329600d9076200240070010301c2400d00f0303603013520b0740a2607600c50031141811b01c1070500d040742a8103d801590412001444844 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 95809703 1250 95808453 95808467
    0x309030210051014010c08191421040812010f052d101206030f0201030f050f010308130506041d060a0b03130f05060a0c020d021b0f220b0301050115 65
    0x5441044054904c59021340141c50082e6000002010b400c07000c500000f20001c10444030318204d0050300d40c2c0c045220f04c00c001c18100d104a10100c10081840303070b00a2120302424141c50b130f20602c14640d003491b1440f4024288210f01003640504008161282d0600490415810900404101e40c1c085042d8480e881c03400703070324505200c0c616401200981d80c0e0014962007032098149400048030104002511380c1031605506050a2080e80401d080600c0f41054003402e00c6680d100d5000030000004690030345c5c4d2401e00030f40c00543c1b040001c004010010569039102001000105201d4032280064032850781e0182c190b81008001d2442242030741c1d01003000d95554801c903030748003a424102074290a0113160400c03802d4038611003e007851088008000c0002c1d6140d104d0660288180c085948840910008981c3e65040d1081800410440c0a00e20640e042c030b070454242071280103210b41000300726100b4884c041195200d600d1903158842e1241003450400703100e902d015200c50b002044210450a401034452 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 95810953 1250 95809703 95809709
    0x2070c09050403030b06070803010302030d080405060f0601120f050103020f0d03080103060e1002040603020705060a1104051e0603090304030c0608130f0203100e0106030b0606040609150203041503090302100510 92
    0x180e495070006010144260b20420341d03081c0c0201006c0d11100c075030520800c1b0350000d020403030191003580d4440f185a4001d05e015449158000000c00241d598881080f1001c1c1026050350305001841d914440c0a885c030b07000d0210703516042c0500280940c034500400070400c001680d03a034081e1508000c2c0c60046640b0500f901d05480e0040d1000c201144c1303103a1010324101e901c1c1c034603825180c4049400315441d41e0580041c01401d0299080f90540c3d180d00c0030300c40c1180e52a1903040ea170303a00f0820041020b41040700400030b510840c240c83d08200a0300c5408540d240e801110b694603a07802c001070501c100100220440c0c0500481d1514883c140307400030402c4149450b00c40013400c07074403140903410110f513020401c40310a07001046d0107200b803403105000240a0000c50000b1500502d020000030346a007440003d0300c0481e14a551810300040c5082e5904241403034400c15401180030420000c50250b40c040011140d00410303540004010000c1e0400904017008600a4056281013206000c1e40000c04180d02c029 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 95812203 1250 95810953 95810969
    0x7020c011d06040e010501080901060609050114070615060f0f020c0607110d061a01051905030601020a080703080a050a0e12090a1a0307140c03040e04080d021306090902070c 76
    0x40105480361078841c40c540c85000d01e6114100182c045030b490101080d16040340c0c402c0e282c079403064507581c1429082c3c034220700500c0c00140b00005d0801056218048503221074481c00710b07203880c00e4129180c150684031000c005010701c102c00082000400ea10828425400803545029141d0070383c7c8910094541580d112701d00d01c218800300c0d811040c4a40d042c507140403140001c11004041510345400300103401290a084130031540815100b405502450032190040c3c0c00320980704580000000580b00c4c0d03003000e0241411031046800e044005020305008244880c0251204502490102c00e0802540c8000b401e440c100d41c100f5803404a0940005421550041701c5014a52166050004100d43c0c055039030229032400350781d03d04001c110000038010350103610720703070b65610759241c0480a4600c103201d00021005168030400081050011107200c0c0c80d0040c0c824a4210b180c6542441c0d84403d82c2c2284889244c44007424070204a82508210507000800d0004404c2d4207040c2d680c0c4822301202020700c60700038 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 95813453 1250 95812203 95812217
    0xc010206131704170a0201020f03090105070b04060b0303040605030a050a06030201020c091503070b090901060806180423160509010b0d050a0f02070f06050705070c150c0507080c030606040507020c01 87
    0x340c5101c10300646029121031031610301038002c3c0b13541a80d5030700e00d0841d007640076000c0e540e812048402c010048030011035060312f6191030419141d072079080d500001003060316166500c02001e44503640600040c0004c10007961000d40f00e0801d5210344040310030141c407000740389181050410041c1d80200e000000c01c00b0031510350100740e07111103610445800540c00d83da0726004105002c520400d1304c0001d0120032405481e1440640c0e282c5000790341003501a2500c81d80146203808400010729840c003000e038031904c601c10000500c451400d0354040c0360741d0000b1152041e04034614102280001042c540000c10302141c03c081c095141481c6600c00d441100d141c050400e0f180c0c0c000426844080e00141405212104119507030a518140407802c0e6241c01d03422600e482c01c007408100342502c02e0084d51a0b140d0000d070f6403100750307103455180b40e80420800003030700510180b50001404240144030038801403245401a00c000c07513080c02054103007200140024825403406081c050010742c00292b09490b0002820008 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 95814703 1250 95813453 95813483
    0x309030b060a0306050709081c02120706140408030105040c020a1509110d0804060f05030402010207050607060b04050108011a150301060804080c12131d040201081003060515030c01020613 82
    0x344240b64075410280c1180d04140502c81c001e46d0010815048030815420380700c42c4410000c0f038040001000700102e005a0120089030300b0701701454010850940f04010020f050ba10f00101040e4084d01143c0030b440e4041d020004100a040902810010001d94400b4204035249580c42c0f4056040c1041100122030740d50910300c04110712064000d800704070007440200040341d1803800d4440e5038050b00035500000c005c40c951101050152042d2801030354142c015040031400e1809114071504031507001d440440d1940205021030712107209290103010b039100085180640e0078032180c81c1c41c0d21003c030580903c40f000c2070340900c6040b441c20740781034401514202034180c0319410081c3c0d690103041182071603030140c08241d18101007a0001003002c4000b01383c60044041c0d035030060740d03054104403c0c0801c0c000103038400603005620070755806034050180d0304004403294890300c918081307600440300b1041c084414a000c401da0301e810045900d80110034801007116250015082c14107580b40400101000140c00070780d = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 95815953 1250 95814703 95814709
    0x160303050f0d14011a1617040315090614100303050715020c0d110c06030402040b030a1205070c0f030209161101020f0306040f020403080d0b03100c0e01090807061d1206191401030309030b06 83
    0x140c008503044a00c164000d40c40b200ad1000402d0003c008403034907451700c000d648200a8a8140903c01d42c000900640010715648054402e5441402c0032222130303a0081c00802d50350b10f03900c00f070000c00030b440e0003c103aa075104d00b401604803809079200e010b4680c03001601042030303a100350031664802d81c16038000c6007168902d404280340048a4500501d944408075042c015943d001e0060300200d4000c2014080041d034130320100200c541180400f0313400280d000f0010f0300000c0d07110400d040482c000c0c500b01c0240320b0f10401040c01ca0f0420007036015a00383c0001400014a4180111000440e0004d42185414074550384c1c04414403c1e0400725504a40f03030540442141c0d0144041c0e070882c01030610901000401c0e44004000008086100303020540405020840103000114081a00c003592a11a020701140110814642070148050b42c0840c4100d855500031209200b5540600882c01042c0e0000c480c045c492020f68203000d10b540364036040f000040021170740c03103074040003160703042000d03004540c5a81d804 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 95817203 1250 95815953 95815957
    0x140d060e01050408070c0e071407030e060301120605091c080408040e190c0806060a030905100e0606102a020d0203070602100e160303050f0d14011a1617 67
    0x348106075442c0a04000902c655000140f0f60244108105c3c02200e80b90400315083c50002da840400041c0c0c0590f01102205030756006092207402418004107805088000a9503944260060b608103030304011403004001060103a41e0304403900c280030b855440c00311500c10080c944585c0da100100003072100441c0070310510400301c03000f4202c488140c0482e4079103410240703e0904500f840034001450301c0d00d0790491900c034060340d41c0901c20080030103140804100c002c80141000a0082e82c15000702002440009903e01c2740c0011500c6c0749000d8800c501d041010890399011149103035084c404007810b03070302940c003203030703500300b401981c0c5141740101980c0b980082080c0c010a080300035094401c0140100320f003500051600c0d000d92030031310f09200c4401c9050310303543c680710502440e1024503901402400020b0080d0003810080354030b4255a4203180c804040e40058940c01e405030b43d0407490850040c02961030a880200c0a010306941e01890030640d4030b00150502d0a80c1000780c10381c0340200c80444050010b00c1 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 95818453 1250 95817203 95817221
    0xc060a110102072102010209090606090109170a030f0206010f061b02030a0506040c050a0b1204050102070506010e07090b0403151d010e0102040e010503070506180607020411070b01060801140d06 85
    0x2c41d01c030040752a0403040740d00e668400002e26024a0a84100b1500c14001c4071800e50016040d56104e44581e014000c8a0f08280f503070074144016032002044000001030b401e1007070440700c801044094024180903111840e1580c0c00c50854000d000140001282c0344810b6013101e00c540b400302000501601401052101e079000258140110030700305040c400300140f120b0144d03000c0e40c03a8841803a40e0340d0030081c214001b4403e034109880144007008603801210b8009501500810000d85071080e150f48882c18058241c200c00e59501c1311303406005010b03500c41d0604001d44040317080076180c1415904d40c0b074541016903854a40668540d010142003000704841c1400f003000c07180091010075080308004d80070350020f000b85514803000800005551400044032003c03140042c1c5200d00d0580500c50701ca0344c2508040360150401020001900180c0300c500c900902d100340c0c0310403942c80f80c2d0185170040800324180d02060402000070014800901d00c3e50702420250400c032038410b65181c0d245031000c0a032626074 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 95819703 1250 95818453 95818487
    0xe06030607050a0e0d0f0605072a0219030b0906040501140c03011215050108100b030703080f0a030608030d0b12060105010206160306150302040312031127040501090b0406080604050c060a 82
    0x10b0006c0400495400c03a9024a5007500d80081400c5070000c501d6485030007602608614000c00c1070701c4094140805901400000c1040d0041d520741c890704c46074480d120503260034582d0350029081105008080c4230301d250b80c0e01c24140403100c5060183d401c4940e804180100d510004002448608000c441c0d0039141403560f60740801c1c4903943c0d56200d4107850b01000402d951880e805c1c00a0045a031a01082c8002981d501c695500d00700007910350003582c50741005a8500606a6444010030400d504001818500c010000302081e50f103a035002f480840b0b1400180403095901000060000d0780e004100d450b40810703848844244014624401c5011b000541e01940c0a010380000018440e0781c12780080083c0c0780144c1c000d04280d07d001f1004c40481343d03410700c22085070a040c000c40628500c41e0b410950700d503a00c40d08001e42c60180a0010b411242c01b0713401281c0960340c8000c12070341d9080038011000104413001c05440c8518107078541985400c405003c05101d00c070b0028a000c40c00c2d00419026851002c54 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 95820953 1250 95819703 95819723
    0x402091909050a03030203090d0207080304140d051b0f1f050a0c080d060503060106020f0304060f0302041e0302040b0303090f0402031012030e0102120a0e10050c0114010e06030607050a0e0d 83
    0xd4207005d002507006845290b15030194000020b18140005901c0003118a804010b51400d45000100001031660700c007034a600c6601042200c0200b030040140383d44001d28071001041019080007088403229044e08a00e001c3d18810003032412505038003040300c10350340b050308003107035681e0032410700b11000030351010003c05000c800b040d440032051541d4040c00c160340c000c0d0704030707642640c030b501003030703035941c4254020f84000ea108100602256104800d8418100c2a0b410003600342a181c1201201c414000b448004407034200100800c15840c241c0100c111001045d0003442c544484a00810a045269403605004640000100e041e24a0f04842500141444100413101520303e10303000340049031b5a1400c600601c620707501408105481801c030341900346180c8520051304c001d0410f001c00001401072040a1007000d00407007107405400e00440700e50400d04c0315041600e604082001d0b40c0c140c0081d1665000b075108004000c0082c0d0013408440e01e1440c40d0904010301c905044c0010a84038168070002c0c014000d07 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 95822203 1250 95820953 95820973
    0x70f02061303060212010e040c150e1509030d05090a0b21090a050c010801060813060912051b01090b06090a020418020a0e030a05060712020c01020c1c08040209190905 73
    0x60f42c3d014010341d81500d86107162070b9a85a0342c50382d00034000d039805401030a020354100211084d008400c01081c2841c2003007160380341c64a0001d0500e240c0c80d50a052401c0b80014040c44503d82030000c0603810380b06090190a024041004c0340c0c80c2c80f8940540c881d92200040c1201420503400101204a6080130f5242e8542c90800c15079600d40f07a441303104a03a1031240000e01030980d8001d20106050700c00c15038510516540310040084244090070301903c885e40d0311a051004548070442d041c100f041c6544603140d940d0641c1c2211061007000502e0b100f1517902d072000302070004601c400f1030b6170030040440d814001038980c51410402486a80e2111140c1402d809090030305c684146c000c1c14450506490b1040c4008842081c1611266100e40041140d041200000c25003406100b400920f044103990050420b0a00d040c81800c9922003248601d16510001401c500c0300e030751000666511003527203040d064508107035020403403080018103480c2e0210107000c0c2080d981071140d4820601c69400004898a0b002 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 95823453 1250 95822203 95822213
    0xc0c4f0f09021c020a14060702040b2e110604080f03040507080109060b01031109010807110712080306030706020d050307141603080103211d01230310051005070f02061303 75
    0x2240c00f40882c040d2044410019944103444565005400040c0c8510b15190b45982003200a02d0554040c1c1d81c06848602e143c00c901448625402c05558140d044848d074010134140074281c0f20041e0008802a40804d003013100003085034043c4e64403e203810314041c0d1240c80301d2504c9402e06440d0b81100c40d40c1e40c0781c105000144040c0b0b42003540d8046003a00e0400100c241e1344031409251103401e0b00303540410300304804030302460300c03d290454812000d90151007003240c45601c642c0c40310f040320780c0a0320290030200c2441102e10341400705200030002c80c001801c2c1c00f24402c1c8060041c0c00001c260b18240101c8101a5081782002000c0340c2405030840340580c003680c018a00540142e0082c00191b40707803041c2c10b180d8040700c4c81c001059103000125442d0366110b10000d070303001c01c0c2c003581e0403c4050400c0400c50f46580115030131306d58540211008110b4603145d241603980702d826020070394400c912982c209100d0221054002c0300321240550440d514180001e80c500126410740301d101c8240c40d00c9045a140001404 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 95824703 1250 95823453 95823499
    0x60b12030309161205060f0703020409020708030603060c0c06160909020c030714010e25030b01181404020901030f06110409020a090b030106090b0c0c4f0f0902 70
    0x283c0507403109941600c603032505040b011100001031140d07001d5804107080c0110083c01d0781e40a882d0b40f03070152a15031035901090903a009420200e400b80740120a010b40b40c5020701010703601a40c3d001c00c481c103201001649541d00e40010f0144000f040174071b4030b8110142d115084490241c100e07038005543e6180404c601c0da6490b441034400790340c59000b01411805e4a241801410091541d01d002809450741c910130b254458000b03031001c5190980e28100010003c1d0074554014024201480030009490012000405440c0c2d01c202241810416004110050f69504601d03410743c0c1d0882c071100217540462070250000c080404460703040c503c0114001503c100550010101103845642e10b0048a03564120a1490f02086c058440407518400040c17002400010142c94a000c04108503a1200b4404003c5206404410445000c07200c24440360414501200e4400023140800358020866200c100140d1b00c503455086175810034a515441e0541595800d6003080515940040c00c5c084a06400d1400382184 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 95825953 1250 95824703 95824723
    0x9040c03050d0914060c03071a07090f05011704050a050109110a090b090112080403320303070e01030c020f06240114160303020708070b01060e041503060b12030309 72
    0x9120310b00340c4160051040c0002c00880c1c0c2c41c001c4807025882000c00b000304075000101440c50318401801104046018410001013030030040303109440f0381c00d021034020000c014580251941450750306082041d0b981c40741440b40b541400042d0740f0416101e52070a907040290039040606035600f0801308070207200700c2d2a6100101141190003c4181d6030311503400c81500c1209515544c0036420b00010018061001c100c2c0700001c0c81024100d24140c2ca070303074824900288501c007031401d400d415a40c5180a503488032603444041c004c00015415890408002007a0800920403181016224040c00c1001402000700c280c040d60950306464040c40c0a1001d100341c080364000c2c079040c8070b1280024014a5024011243c0e20318081c0548514110000c0c0f41d01140440c8032008404140c2e00b0000000800d015001030103803c0d00c1079102101552520100502503203400c1c241c18880d501c1d141c0c0d440500101e0301c001e0403c907948102c0214140b100c09002400080143c03108a20070300000041040100001c1001100 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 95827203 1250 95825953 95825963
    0x80a1112060907060f180302060702030307054207030b120304061d010c05060c030c130602030705010f062108120717090a0f0b061f02030901092112020a0209040c03 72
    0x1c01a00000200c0c3e184011244110f000c1043d42021f00240c10142c1c0140001400602120b240031400c0d0f80342450302044403c00a08840d0300a0a58030a0340d400c40781c81c0240d1240340b1100c1241c481c8149080c000040501900241503848070b0000c15074540440c0002414205000c0d81d80f220b03a1102c0140c0803d22004c64101018860380c0c0b000d04c558040d50340224120381000c01400559584141d040c07847d480a07080c41da981c030040c880000c5580321a0000300c00380103e0b07405103440e0509454034600b07540d05403000f01c1030399043c07050911828040340141c040e84030f05901c080005ca00e40381005110382c403d03c0c0e050001709243c1c2e010000e000b90803c0c07000c074412490140103425580c50480e056181c10f020345000b8144031b400b201d4100410024888150064802045a2208101014181d10301880c4400d0500583c0011810441c9982c02c000080c00030038500020741c8404034103280782ca140505040d401040c078280125600004c1d8402c008544280741e0240c601d090310300309410019004441383c403084032 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 95828453 1250 95827203 95827217
    0x110604080705090903040608060d050708011805150c0901030c051911060a0902090403030b011b140111040f09180b04060603020411130e070e1305060306010f080a111206090706 77
    0x841300c00000100c030112402a95581c030281c94600c100800084a1481602c0ea4881e1800102d0313201000e01c030304618064400840660b04c94a40b810500b804150041d801020a4501c01c20031002c922001304c0b450120b003460000340000d04d800d0150380310f000e0004c100d0343c40705001424203041ca4120484080030700308081200d0b560707520000c8070016982d41c2c50f80250880004000304000030b0180c0c01c2031100e01014100101c0c922181075418100140c1d918081c1c403120818200b0528020007032240500c2141c010305103a150906221825240c114a48903d0317031120350714000c0c0e0b00c5038211869045072240d408102c940d2a03040c070381024809400c450100740c2c0710300e280407400c03548440c00c0e00c21a55070310a985180406030307240c6619440b000f24014101d409110f141025904542d4611445d00c2001c0c00b1064000f40f6410910245858808140c020b00c401100c0f000082c030040c0400552802c00540c1320107808c032841c01e1080450382e4548aa0841c01c07061080105105114101240d028142c03070a0341d913200 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 95829703 1250 95828453 95828461
    0x8010501140315040f03050d06050402070303091b0302090612030903070605041e060c11040b03011e0c02030702030604080f041205030903010b0402090f0603090a02180709080105070e01030911060408070509 90
    0x103810f20703826200100720401c841d62070303000a80100302600d039245d8100c0c00085d00d2662500400e080e41d1100000f00c000968541e008401c20450f242c07294180c1d42ca007187d2003002030640e80420704046000d04a42d01c1564894000b43e4400c1c410030403034003036210250070348850b1540c0f0a00500b03550041c1c00b600300c101006006015103810303041c0340e01007100c001d81d81c0c0c0d50740c0c41c072239464103a00818000d409a80003902c1e6000980507071424051120342c0d90400042c4001120042c1010040f500f01089500840d0030130400c1da40540d82c0041c925030400d1700940004e50f200f40580400790284601ea0142420300401e50b082014040301001a2000300e50075402441081034040030401284034111300241d04c00d0072420100618281080a5a80300008034200c4440003410340000f40315000390011080400c2c1c0c0c41003004006540700e1940c40041030070a00074051403e00f1500501500000310040303040541d584c21074018000880d201030101e003c0640141d6071a52580c40c0c5076203810b400c1c0601c0707024441d044041 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 95830953 1250 95829703 95829733
    0x6080106030e0d0903030c050c090c040305070e01030512031807150e030a1e0309050409060204030203070b070b0103110112061712070f24050a0212070c03091401020106080105011403 80
    0x480920442c544d981010f44d415954180c070100ca0326001962180b00e1030150034541c1e1546401d4500030300c4030350011a102c0303213507240c02490002e050300543c0039007030984010070009a0005034040b110003415002902ea40d1054105204849410103507601d038801e0000025810b1980f0920309120b040d141d07244c0344100107850500d0b940750200c50000f04500c00703045105c0c01450250100400319482440e061003659078410008040d203094800a07240d1641c001401c20840c41c041103014001c00400d801c00741090603035114000140c00c140f00c080e0242034480c002c0300c02c42c1e2140104202d07402c14498100a455103c0c05240021848007006043c94858000701441c01c010f008203a894440e404040000748648554920300e4031140404001c1e1040411944c42c140083c07a03000c2d00713211308002c00f001a02c1d5400a010a001c480f0058010003e2011440d0080082603012850409a6600200000400b021180100d00500f441d80c0005d1b895441d200010807005082c0214140b46041201150700c14600d018030 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 95832203 1250 95830953 95830963
    0xa080f0603190201050318030304060614090f0a020f07050d0903030315030b190207050a0303020d0c0503060f04091502130806060603092808041401030608060603100e01021306080106030e 82
    0x901c003854141c8801d0b00640c4502c00455010800155965100810701013461864000b660200c2d48180c8518081c01a0620295140c1360403d0440381e281140c1000400c00140f40d6000e01004840c2d90006a503103d030341051822103400b00e81c0031080311498040382e01c0c0101000600c4c00704400103401c0c01d602003990100c0d082c005090720b402c0074803d400d42d1175004030f11302044081d1414125490f0240640300202d4010701103c6a0f550090b00c0150f0364014440b140350403180003548000c2405010f00c18040c19494628504c041108140c40001d01d0700628205602c9040880c10032001c40307400003e0462243c0c009400c0ca50488440d01300b00c451503102c1800f0000e40b8001122088440d030710012005000c6d48154003a010308180390546540b035603400c0e0310340c40425402a0011900c030702c51810050b1495a0501ca0540108166070103017102d0700302400066294030440c030442030b20503120000030154403420b5040b05c03002030344040c40d21003003079807440041c1440000b40f04103000b00386018500d001c0c044001c60 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 95833453 1250 95832203 95832223
    0x6030c03010e030d23010605040e060a03030c031b060e0703021c031707050f03010e07081317071b060c0b0f131203140a0b1002011103061c05030a080f0603 68
    0x4061800c0080050040004113175000082c0c12207040c2811841441c80c00d810094081c1240c1d0340d03030950721070414022003d45100980418094040c01000700040f903403008010308040c1d81480c1250400c81c040058030f04e05060391502a0a071407800319446164900080c05004880c401e49505208460703518007502003001e0000003801040200c3c06407902426403094040d44000a401c0203030a10380d44110700900c4e40c02c00d82000009484000600454981016a01c0d030300c005804420713092260203568124205508656000d41030401085640c01c00c42030a040100520b800c502081541d0756422000f0416120401d069907a42c019001144214030040f809a1185030309007072101507006180d4420401d12040c40c02d6404050756001e00740e65031f64007074044038000d40c1c5103400420b0005021003040440c44003802c1c1c1e0b1040d68580105c990030340702c016003500c1e80304004482e2448164044864a2440001542c0040007404000b9002c92581e811030000d9001c0c400641c18050b003030341d42100381991016040 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 95834703 1250 95833453 95833481
    0x303060d081c020304030e210a110609060d050f0c031b1c0e01050609011203090b0c01090c0906030303050c1c1109210609010c0c030c06111206030c0301 67
    0xe40022800200040151a588001c00c000c2d08070407078203210403070b0400d80d011400220003200254642c030b010071000b408036010000c2041280d0f12850015901d001c40f840080c0301c040c804e886444242e5461040d038800110140c131250380c9034092400b07400107000c1243d200c585800680003003080c0940260030340b40b00d901010301d400c18440743e214481549070005e0794000d0005609000d440e40b00710150040300241c01241c00080380700d003013100401a040d003050f004240c2c055030010000780400da00c020014100c410b005411303652680303450603050141c081d101c0043d1215170400000035008040358003110460380aa0350802081c0c84007111403195100d0300407032803c0100030400480c0f50800c070360b100242240190ba40d1515141802003c00d5400980801c03848001e500201c2c440ba80500c24480d250f4400d14040003000400450800900b1400011001034104001134004400b004280d900c5801070308441c0b207010f5203500c562407092000e038000700c1e00d1a00900600e5803010b4981014050b18403461450 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 95835953 1250 95834703 95834719
    0x1031403090105040618050604080604060b01020f1005090703050102040806150f0d110a090f020a0e0402130e09010f02120703150503070504020705030d1113140307030b04030329010e03030306 84
    0xc198101e4030302c50001b1441840780078018000907a41e03a0034004100411040024003c03920303181c1040790858110203641070564024000259211401203100c00403034001e85000138054179950360b11460001650001085903100080106100c080025010710a035202501c07102c030301d224207040c082101e854016441e001406c0e0700800b000a000c403448900d610340040c018040056a580e103d0303094032040c0c2c211103843c90b4002071f0b41301c44a6000d810303141100c4058500707501c1d014440207601880c203140d209071200082400f000c2540c5408c2904540141c50703440030259222000041d282d41d0004090301d03001c01080c6000101d1030300c40b43c024200000c8075001000b50402c00d2034601400040c3d445190700712a940400c0048941c44a414451201e84440440304142c68890041d008005a502d54001031001c0340a507103003081950700010b500041d40d030310019401550b141d0345410b40140c24000500c0c030000e0344c0e0b0740c81041181c2c246e0300c7d929441036017680c1c1d40c040c03040e415050540f240b200341e6805801c0629 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 95837203 1250 95835953 95835959
    0x302030a030b0301150312030b0111070302061e07031e0c050601050103020c011d0102130e0910090602070210020c0405070504120f05070305120306040506010e010512060a1d0103140309010504 84
    0x399101501c1c1d0b0740040d00110303465103024160100d4420942003250f4940d10710908100c0b0590520642601c2c450038240300e005c0040000103641d6800381880b0092245c00006030394a0710001119a10b403c8034480022144c841046242c06840904080c3c081420303500004e08e00d8200758807414641a580c0d80007009410241d01307102c01107020354007034040d08210359200c0d404c513100702d84030002c0c0c00f11100841d000181c0301c03804444091540c82e015841480c800100f4024840044000300e070343c1501c05800d02c40003803e03c1781850000c02a000e1044042c0d07024140340b503d00e44881d00400c481200820490b0708000300d40c0c403907000f0f40f0303580039501604610303a8010507000b00043c003400045000074002c1d011140310594a540346807074110324119009207000d01005100742818680030b0560040000d007445540400710324002007082c09903490394a69410f01c1303c085542d5445100074040a00340341e034400007448801c000d0344100c0c100c0a100840700a210b40005c07800080c07010040c2d51006034160b640e6454145 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 95838453 1250 95837203 95837207
    0x2031c08070f140c0c030607020d21060b0a03020c060c040609030201080414060c0d11071106070212060a090203060109140103080307020c0406170606010201200c070512010e0610030302030a 83
    0x4030803203100500c030a105210034100d0361007002e4131100c0019030041c11403210031410306091200142490080d5070040300d080c4031185d084200074101c440661001002c180346820100c01602082d0702012800c5000a4985411507151300105801d08801c0110780050310f8030311505045100d0346c0728107400034440d04018001907200740902074005009940c006141030500082c5801c0020035602680310540000c4c0092a00c400e60003500700c075501d60540c81c0e08003d0f00b40c4036154014140303803440d071103120009462811941c4040c00c00340302c5003800003103980711328208007150000e08800d901070b07109101d4940001144201809000b1569410900c000c00e01c1c3d1a41d5200000c1e504040d04180941c06007905000c00c90f02ca0b40b10b900c000705892101b41ca42900000e01e16030a20801400c2c00741164103180c1c060450700c2d51028008110f503010324000b5038881656403283e00b488800c0d000103034005041100039603041c60541100302800004020b6510a4a80a0510443e14200c2c4001030158100307120f10000c40f4 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 95839703 1250 95838453 95838467
    0x50f012301051213020310140f07020f0105040803010501030b09011206020708071b050a1d0126160e1e060d110910030308011a12040c170a02031c0807 66
    0xd0410304002d820070490311050044054200c80003030802c01e00000a00943c0740c104048070022254a800b0462540700b02200303002054018000140d21071150b0200700c10301e10800c6441c1c1c10308d000400800c842e0a0a2502c084294000c3c803c4500103420702c102500c40e450049180307030407900404440120ba9003e0b60300d803800383d0041d00f0241c8542105104003c041880858400d640c0d07000c10034400680f44c00d040422040e09420703045250806031902040c45144010001c19055482d40c130f41c01541030210303111403010581c0c80b14810308640605d0a140f0b0300c034070717149085009844001c0606400b82e82c07014918142d450303040d600036400400410115503581000e4100c10302ea64001c1660351035100003013001c07441302c0303006a400c805c40c1c0348540420420f02d42d02915030341c09440c03103d000460091026a510901e401140d40311050f00307402d400030130300b040154401c1d4002400b900d0002442c40102c000000c0c0c4483c0c50600c02e03030190003507500030b6a541c04c0c0403280c0c1c0543e1055403100d00468071002021900e40c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 95840953 1250 95839703 95839769
    0xc070e060a0b04030605040c080708010906271103012306040c0f05030f0901090605011409010503060709030308150901060203070501060603021c0e150a060503120301030b0c0a020106031505040501050f01 89
    0x8c0c0701c20640440c41c400c0c00d0284001070300c581000400da0702c2d590b1600604440107020303030618601c1c81c40c4844000310240c00340d4584260704410f00014079900f0f180080e00401070400038070a40c80da42103040c100030500303d59491049504403810080e042003c0c0c415900040c07401c0751720000801c1000011030482410030380036005428540005600102c1c1c1d40e07800100c50080c1c000c1071914883e868010401d140c40074041b80940710a501914050500d241c02818003011400003c0034800d6002c009600f0440d02e51504604000080c1b206400b541e444102a48941c00b051058415500f4810003246007402402101d805103203d2014400d54501c1d640a400240700e100c1c165081c80c000e0031464050010340c0701d2014040c01102c0f0b80000c2481c85e140405107010400e1340c14a00e054414401000814124452981d21080c1288215955490200201c1c01010715800c02810300f20424a00c0102e40c032603500581c030843c07040e0001c20003916140d4990721008024440d408202d1030201992071241703250714ac40511 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 95842203 1250 95840953 95840963
    0x42007030905030313091515050a02010b09040c232119060b041404080702010c03090e0709030c241101090206040b0a02060c0304080405010c030509060c070e060a0b0403060504 77
    0x541c0d440d10006411a8000050094040941c0b0018402e0081074031440b03c5036800c11500301d265601e01560082d07483d62040d100000e00401050700303034016000b034101002003031005090340da807490140750903c034602240c01008030180c0340c0b13200c000000c00d00d00d82e1103014000092880c0018160341015000740b9503068402119030040304400c0003405c07102008003400c030707200c2c11000c039205107608248812141c04100d58022040101c0500020440810844000c20b4080ca49010085001d08003681d04804a5001c1e90350901800104030085500030741003403d4034407400300c060138960b446a04000c1081c51410500c4220b40001c01d240c1c0e1030b80640304178030511030018004950344029800140f1103801650042109050018482807100e80c103101e4913501004a00070a421400c15498040d40c0740598056a4184000340348600306060144050b0341c00687c2c010003007607440085441d5240c5440951143e045900d8003040840c540d4541300644c0c0007513480c0e030760350746040c0703495621120003400740900141e038 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 95843453 1250 95842203 95842217
    0x90c0910030602120a0b18010902220e04020a050108040209060909010f06060215010b0a1403060f040203150103140601122c07060813020f012303070c020f04200703 72
    0x40c140d03002410303100581000c031440c24174001d1050300540d00041e83d090702c40d0224160516041e21040e20749419500035200c01030720b46550088500f030411158103031030311860f07580d4000605078a244244ea03200394400d6a030814115907641c01550100000d50b03009503c1f028080000c1c0d424282120b00c82e0384800c00c2c00020410b00c50f1920f8036012616150402c00068001d0913420001c148038101e000d00605002c0c6c107040c640f0b029448010020f0303800c12040c5202d04030010105909554101c009582e54100600c1155a41010b009030b49104000d8128240460f06200b01076681108510a242c454130043c0c60340d5561165003441c04004210404001c5810422500440c0040380d003000007203440401800101901070416501500d5a03400070703e0112801858411400141c0720760525000e080344c02c0c2440c0303000400c07903064510414005078810001410100c00c2103c81a4001c445404207402076039207101003141c80090100356803104262003800c180203a198890442040d004090082c0a841c00130 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 95844703 1250 95843453 95843459
    0x3060108071211040501030e07060203030402150403060f05091911120109080307030e070b04050a090203190504060c0f0e030c090601051c05011a0a020606010311130806090f06090c0910 81
    0x1040f10201d043d4460b84441c003207014041d0396014403c40c404c90400c0c0300181009881c01400950301d1200400003406a4041e200c00b8010190000584000d1580100e080c40003448906285005101c22070b07800c8014402c03400c645244000b034081200015030404a01509403005000344110000712200c900815969151136002085104001d0b501440250b50f0109050708201100c1d80340400b2034000d5004c1c03000410041102e960340c40a00b03011250b50210140e140d0b80e9035200701c034103508112002000c06041030100f01c10003a090380300c0304548a40380ca07001c110405c00b400440f0042d804103407882e0180c2c405074100b001c030b2410b00d0045902c00b1051608074542104422941c107100791010000c602581c0b2040140000e649509c0290312801d40c0c00100c03030902d104050007d644d40e03800f4100d41e050641e51a102140c801d4400d0032900e04404d810194007500c4c6d660035007299106821106500320f40111811782e0103213400880c140d40035066000091179080d0759402007010108020b00071b000d8030031000d4000 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 95845953 1250 95844703 95844737
    0x30c02012006041121070e0c09130b010201050c041a0c0316110319030c11120307030507020406060e0a0603051906060806010801050102030a091211120325080306010807 74
    0xc0e100318461002644140c0c4284140302105c0e03c0042807480c0c0324104100780d80c8101c00024404c0455090000075400c54650a07070240d1648a1000c00c82d400054896a405103c80190440313803040d5402e038020400e99030b813524010407c2c01103000348a003001e255149003443c100f561018008203c5a00260780c03802c1101c0f248010004c00c4c00c0c0080365242c00000302104546000d00000d041c10104030b80100b01c091031071703400420f415403190005103e180c40e101c034852103440d01e03c103194030800e404007166902e245509000d80150843c10040344200e062540c0454110700c0381920b161070300405001c0250441c2440b000b0f4016180041c0751064850b80c90404c030a180c030260040f800142000c0d12015014281080014010881600f210707055520801036488855444201c0381d084803010000f0f0350f801c40c00381c0b420b2994840001811680100b035400142c0c08228084010038070703842e8003a44c80b860300c209101c04450841880c240034182650600015044d54025518194000fa040c582040b8402041c140c0e = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 95847203 1250 95845953 95845963
    0x8130f03030908060705040501080f1305070b0d0506030a0f020907030f051006020c010804150e030702030d052a06270f070510020115050f13020f0d1107030c020120 72
    0x4107500041d064501041000410720503590000e41c02c0c0307480c5292a081800107072808502500100412046c9000208401a41b41850038065071200030354031001d030743d42e01221240d085a101c8801c4c2510f88408650a4503000610340059a03001c40f54003441c0e0400e07000c0210041e0014500b40526441d401d001c480388449200c0d00784149002c400c03408406040040083c40d00025509031410f000540040c800031420084401d0b00c019145500803405103400b10100b4110b0103080f80003500340c8111003035110880c0d0003102034524004203403101000500c114501d05000d50040c0e00d003660507088a804502400d01c600f56081c8400b599001e4050070b2000e03041600c2c50501940540e042d20780180f6000c1c031440c80c15003159070b8070516910081c4412071103034104405001702c51142900c50b1044011049070341d2074541071001810071254046403100d05031000e400c169030001c0ba6003501c03070307240401c0c031000c2141000c107440c003103131301641c580810300000e03070040d0b038564050036a2810003009115013451000302004 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 95848453 1250 95847203 95847209
    0x314030106020d2c0f0301110c03030114060a0c03030203060120010504110a18050a09020604060201060e01061e030b060d020f040f08060705030406151208130902030c0708130f 77
    0x1c0108006030402c03d004010448100c0203070303e10a80310800300042030300d82595051000040340c0728500c1c01850000030317004141d11045494407110104080302c2d41c0c0d8010014504035051071081c0c12280b00101d080012a1040230500e10115500c0b036010000f00740f0179805164051810304014440b00c4400307100d00501c0c201d4468589880e91258200f000b000a80c048900032075034107581070100c1c28100301000c0c1006554680e0048050fa549001900d0803000e0b420034032415030003414540d81c8585030700340240a00428024001c502c0400300001610074419044038010034210000a403081843e20000c4014060706030b0500d521140500c8060314601c034030f00c01401c1044140818641d214a080322104022940354803848075a08124200034031550044201ea074032030340c411130000d10302000c0d0007050081803064115480d00a5082203500c00c00c050b08006111083c5008842c06035607070340d001030105920080302d442c203ea42c0e0520a100c0004c03101f5004d0099090ba10600b082c000782c48140100098040c1e40c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 95849703 1250 95848453 95848457
    0xc0c0c090e15010518060607081b06150a03020d140d030b040609021312060207050d1d0d11010f090305030a0503010303091707060c020609090106030e0f0c09040308040314030106 78
    0xa014801c40c15401c2080c241042401c01002c00342c0d40c509400124070821007040442d0190412000803a29910402240d1100d50321400300c82c4c4940142041008410031110b4002662041c0320218001a08181002003022001005003000b2401e44d03090011384c0d0103d00c0c1c2242c0e60104d100f07101074030600030b00521020052070740c0c0009143c0b00030000c01c82a540d65a100402807841040351069040d041d01c10748003590107a0105d100c5a1009160040003403007022005000e034080c9803100c400c3d10350700040c0d0341c001c000c80703107090410103040200704101a09081d000400540d8240112842075025030030040b03000380c66062104025035a522524107591044d8241c2002a00c004014410142c01003110390140c0b1911403840429004004025a5009540031344424003003104140411555104216003501c2c0300686916050359403441c018008d40411210407505009448000c9600e65001820710708013600141031080d1512940c509441540000d4000e404000940441c000e4031001c1200441c004c16550b = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 95850953 1250 95849703 95849711
    0x6091703090d080105030d03021e0712080a0e1c0e0619091d13020a0503010207030e010e03010c05090402161a1006050414130e010f050402100e130c0c0c09 68
    0x100d0515401d200240b0704901c148108140140426103001407200c6655000d800c00507518041003181050880070036490388980c0380001080c0082008281100404007619100c01e0b44036151840840c1c1919452405917150f40c0c080e4031f024072030388000644541140030a040028030030f0078602c007013042603220141c107841c103240200a00d00015446a000c0c002022900308400d541d1600000c450641c241c003070070616005444c0f0060009640c0c80900050081c64000c00855491b80e182c9805401711480c08801c0d80800c404040c0507800741018003400502c181d040e9100743c80c000707010381080020b401ca07000d400d5242c00001410700c001070802005181940103444100c00ca0b03c1c0019200d140c0c85d00540080c410000140300c20050001c6c24010348002d110b04070b4220445505126000c40240840344100d12190308101c0c000c0503800942d403040b0b00071380c000d4403603071030030311000b4000d941002c2d9403c1c00c560000b141c6c81040b210744284da03101002d51050391a220021000035181d4102d104840d400c8048400d5032 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 95852203 1250 95850953 95850961
    0xb060706021306080421170702060f0a1e1e060b040e0c040f12050a0b010f080c0a050a0302060c120706020903010c0306080303010603020a03020c010903020d110604170706091703 78
    0x303070a112800030002890058654038150340d541e8281b0040326241c0580d40b400d541e184500c05d014181401480a5465916101c0d14040b50001d603211002c0d6902e00c48000241f01142ca600030707a010700c0c01c0403402082185000c600c0304140d00300074041081103e03402907022070317034090054180c010400145912245142c8032400d14201c1020494041c04800303800d40100810041030303440b4071a0608441c07139880307000d50120080c01c1c07040c100707044868002d14115190002180b8000b05100010940d030815003118041350b40041800003802d154010a0750207840c008082006141500c0102060f0188001342c40000740300c000d1030744140d00b00341c10441d0b005802180488150409204811001c00d40e450103000345885e0108140d120722060040e50b00701900000c0100485009404951ba02616000204240001806d0080d2100620345001000038503c000d00314484200140982c003035500001114417510074000481800c1d80035000443c0e00c15100c1c20306c00c01107981c602041d2a4001c3c101d0b6030b241e0f01e1170 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 95853453 1250 95852203 95852227
    0x3120a080a06030b0103150b040507030e0d0206090616051e0a080906060d0212011d0a020a0b03010b030a150b031e01170307020d0321020705060105040501060509010c060b06070602 79
    0x300400d07000d4a2860700d002000490041880641101c0c2c1100f20603500200002800740074003410a484c5070498144028821314641c5030f03202840408207803055512071100820201c1e00d032241030b0382c10100c2e68003440c080f03402d01162525085042000d414114944480790580040c105003a110302e04460380c010800340903482d04003081d5588240440060301640ca003480000b83c008000142c042d014840b085049504600c003544400500003810481d080f03040900410740e030782c840d0a010104d02407a03520034005800c82621013500d05803446409803034150340c0c03244082c500070a124050400e001c20b800360300003206494500210300070f030600358046c503113100403441c010041c3e001a0300c81c1d034200c030b6120b68540204001005070b032005581143c1a100d0341045081c00c032420120700c03010040d00d100e8140303081d1098041c0e5000b058158819815101240c0e82c2c1c108010460781c0910030280030480030407801d0910b41c482c46400791885d00c541c1000402c0190180407a4040e000508115115070340051004036140c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 95854703 1250 95853453 95853467
    0xa020307021e06040303150b070c1406030108060c0d0f020406050a0306140a052412180a0b161701140102010f090804120606090507080402091b0a0e0d0203120a 70
    0xb15988000c00340c0355010840c11992000c0081014003015500c100140b0054214002500102902c4034855151180d5060106041c8132034865040b00c0070041c140a10315040a10903241220400006001c11ba500c0c00101d80c52644610a040f0100e9074840b0042e81d00d480600c0680007038a202c2c1d0380c040e1109610340e0054100c0703100e85c00404c0a4110411501103940e0740c40d610100355803080d11103c1070045040500500316586aa038080000808070b00303600700502e465104c1c0d124a40b0444071001d50030030864250f880c0c1203024000f81c000a566000110711100700322240754480a54942500019651040b00341c0c0c15070b0a8110048454488006120710740c0d090080c007140da03582010130000c012050f45c500b040d038402c038031601c1074481c1161045414001640c0c000d00042089400c18809854100002410303000300300c030101d00c6060300b180030403a55502d2502e00c9804882404800c9d1500792011420b4400e080005195680480300c171103040c0050f02c060218070f000c10900d0140586502d20000090242c17 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 95855953 1250 95854703 95854723
    0x241406100305091b040605090c03071403060117090319020304050a080c0f0d022202030f071e030b03210403030e0303070302030d0f0204031410060503030901020a1403120a02030702 79
    0x5003000180480c1d06008030324400701d1180c5000401038850040003240c0900780302d42c0185d920a12208c00c0011816450004610800c25546c45600c2d0496880020400b0301007603510310300040c10010803040f80a602c45000381c006465038105e034181481034140071030341c2d00c1d20004080180c01c080740400c8281070030540d14010b0031425001e00040c0c1d00302d00120307013044251100503219260320b08188066443d03511070091005c200300e40741c40300100a0800500a580180c40003010007085c1d60025503003030303c111480d26160118650400d28042140c800b00c010303051981c131840d0716000f00b00c034031034040d44e0308101c2c814800b41e072881a94a13203145041c09400c6001046506009803c20051303100040d5000c41240c5500d1141075000a10b410781140d20300080c080d07500014504103801400c19655100042c141908200b007000900030b650325501410380301c2c00703070503241ca015a01c01039403c000a00c5102c103c014003080c0c10b00300c0382002441a0002d09a400c01c0d20306c0c0c45201e41c0003085c00341d40c0740d06000031300078 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 95857203 1250 95855953 95855957
    0xa030f0302041d0402150301120215041203270816050301051006080423030c0105010602010618020d02070f08040e070f050a0e030f07140f1c24140610 66
    0x1041d1503c880d128041012204000090500600250842d6510000454050101e01a0f2034036980c58000722580d18203600302c00e920030401c0e069114010006402141c0a0700c0f4070000394601c1c441c0540d001c1d6860700052600d08410f04000868211000c140ba240c00700411051005041040c084000c200c14858207401c401c3c040c0e4145001c20100307007880c0001808403800c41ca4105020780d55820b001916a1030200c036151480311000c0c0d41c03110400000054000840901d0003002140d80e5400d0a0303080310610701c0b41c03802c101d41070a101401d024040d40078150381a90b800340945816569503c0d1526020504800c131807590010409010001c01c4120aa50145ea81c1c102070308038445900c8060001e000d04c40f4220b0401501450801c1240c03020b00800886200f0802183c03801915603010515100c03011485074050000d0040c1c115070751400702042d220326003584000b10440d40d0a5103405250280c244d00014840140221030b0340300d00b0481c0300b4502d05854910790781300b560801008029519031081d0260007 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 95858453 1250 95857203 95857207
    0x2090a020406051b010e060106051209010c0f030902010306050a063207020907030b0a08030309010f0209150a020a1401050a050903090108220206070506010632030a020f07050a030f0302 81
    0x400b1541240850b003800c5100c00c0742d484040c05481940c0d01422035500210b0081c002d00d4000158185c006d00a0010300343c2c5107a4180d040e0341d40072041ca088902089401001404200f14014114002d07408203c1083c011724001c1880c1c0e40310b00114182c1551640410000341880d000708840c091954089441d5940011900f000640082c10141c0d06000d40c01000c3d1082c407482d808505501c1c0a0780c4040c12076a000b40200c1d5525a40f41742c16510303500100c0d840852942012a1041c03201e44510840c0c0c1002c0e401001c040c250b4003a500c00081640002141009620890100c000400c8800c1e80da00c0d440001d03d40049083d10306480c40380140d0300301a242c40030030362041c07110440c00ea8000c040c03198030070b6a840c09004054003503d681c07130bc01508000047c0d04000c0020f08102030181c080740d194140d515a03100c0812036001004007442d01030100c09040003000d039644032185010f240c07c000715007000c180c88000d0b040603002003c03180c0c20350000600315904d40c4010a100d0030980c01c03000d00f006040031410118 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 95859703 1250 95858453 95858459
    0x30813030c05010c0807060f09050109060b01020706030605030718060e100503070b180d06020d020a02101505010801090509160902090301110418021c05071d0301020304080d05060a030605100302090a0204 89
    0x40c5c618040c18100414081d1191040060100301c0e0303010582e1315401900a0102450360300b130150040041c488a240140076541c0e001c20064041d004000071150040c3c01000600e203052983d58240707840c4818095540d482d080c000901d404e0510110780529080d01d40810300390718190400d85013811031f40c002c00b082d00040c841444003004451000518410669211078061400d1070721400921504c01840d440d2440401e00300d815580c0028040c801d0008400100202c00490035136840c1c1c0c80d414403c00e8006054030303006010140740e54008c0c1e03804c9400c2c0c40882c1d540d640f0858101c800d00307446402c840b07042903003c20024038030300e424042c2050103000400740610309801c00e030f00c40454540032000441410380000d14051a024444c44c850b440106007030080101e401c0c005002002d19002c1074100c1c80d0021541003601d5146018400ca0b8003071944202341c60b1070000d210b9003a0b8043d040003082241e00800c0800000040385050050307912032400450f20203829421807040244005002d44599101c910620040c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 95860953 1250 95859703 95859713
    0x609040615091e0513110301060e1c0210180e13120806010e06070305040b0301080f0607020105130b061311091306051e150403060b0f01110607120204030813030c05010c 74
    0x100e400e036001958101005010104000098202c08000032501c800004c00007400c80cad4080c10b0301407002e80844000300d6a4064260b0700c91440640c0c140079500450350403070111110f0150703007155042c012035480003c0403a510b00c2c4c0c41c058400c0441e508504c2034070108100d410404424100203100341181804003031410300d80002000d5100500c0110301802000880200307240c00b40082c0c80040101e03500aa40d6981c6914803a5210160f08020380103038400c080c0030600d56070040c084c00707103d5285040c1240446020ba15446040c4601600003a00940e1034005003990700b8a50041142c440180386a041d03490503407005004030044004044540245000002c1c0081d540301c0c0c002d9800d43c80c250310605c101548500005c0c814003505820441c0c17201000a00000b04035a40c0c110544180040351072004003c03245005480c41030b1034407200038040d00140c0c0003402c1c4038050501c69281c00c0354070360018203041d01d0b96241c80e89070340190000e4070000d01350300381003041104560104025210030301e05140207091590341e07 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 95862203 1250 95860953 95861009
    0x9060103090b010e0c0409020d020403030201050702030a0c17071a01050108070906021c030b0307061206120206090904030e12070f090c02120702030c0402030403030906060b04180506060904061509 86
    0xd503203101d414801c08211801c0c400c5c0180d0340030389440d040c115551b11203101c210009502c580300440140d400d00000503825030003c0182c901858950302d03000e00c0d061682d0380d07800400da5103540100c1c1140060041c503021844200703006c05030701c0154140300d076a541454005401321800070040780400002084c2480660360100344030700005210840c0032041804140150007030040d01c0c56498041c071628500044603a0310140407000b00b01047e1b01000700c59101c1003c0c2c0c04400700e8020183d0840f104000c02c84282c00d101006641c40b0380079240c0310800c03660a034001140b00304880021186a84170f010240680007124038581c00030b100c01d11b800c04c40000e2041010351034881a50000c44082d0000c80c542d410b40d101403045901d0314000810840d928506441d0180c028010300790241c607102d00d4100003245161078582110f05540144800d900302609102c072000180070300601c40c980181052001e40e04984079409400b020b09500c1c50481c40d0101c007010010501259a4400419481c019044c00c0c5200c0034210 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 95863309 1106 95862203 95862209
    0x207030c0e0c0a080603070e130b010506031e0711070e070e01020d080105060d0902030d0c0314070b04080c0f0706080601110a12030b1f030b09060103090b01 69
    0x45a004840070480c2d40301d28041c8104a41c041d440e0107800c00d2548800c005085070105038840c140003034400d0050312552070b4807a42c0c94100d010030401d52249405881300766010f81c11490f1603000382c0020b0700c0e800b00d50a0300300e400101283e56188a031003610000700d103100c11560242e5581480d820541011901c144c00510a038100b07070f00c00e43c408252920f1050072543c540c803641c2d0802c010045a40d01c010302d000b07030041d82c03101c081d00180c40501c0403104251550b1140200034010f402c000e018000d5513044140d20000030132050000543c0020950307002900a06030b2501c03401c528200b01d24001441c01c000c5080c5c4a00040058403a0340072800c64807445003aa0ac1d140c0403100d4030985aa605000d48000b00a01c1a075884050201d1117940300c2409214014080ca001882c104901002642c0c1440002e00180c1c581d0a0103946080018059070850400c2c0f07010031808101d911060310004040c0 = true := by decide +kernel

theorem cover : BRFrame.Cov 95683453 95863309 := by
  have h0 := BRFrame.cov_init 95683453
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 95683453 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 95683453 ≤ n) (h2 : n < 95863309) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
