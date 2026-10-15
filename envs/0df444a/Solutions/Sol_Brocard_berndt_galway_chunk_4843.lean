-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_4843
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T13:55:06.306356+00:00
-- url     : https://prove2.me/submissions/0ad01f6d-e481-492c-8c10-7622f54b419a

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 870863309 ≤ n < 871043165 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 870864559 1250 870863309 870863327
    0x12090b16020d061b080114090f0601051213020907090e070c0512040909140105130f11060c1005010501031a0f042a03050a02071e0302070b040b12060d031407140a03 72
    0x3005c00d010381c000182000c8140c007190290726010300481007680d942c0c00c243c100410000c01050511a09020100614400e51002407059180603c100d00d4a0420f0041240c0740702c00403d0350040087e400000d1121740c51b00c4660766002001c1c0d00b024000a0010310705581040c40c034180050305160081000a51080150032000006007c0c480070705c4526944c12605007a01c070202c44103001c07169809030b804001048006500c0c0d03c00e00484141c0d0b2850703840400224141c4c000c455055883d8070486169002c1c0b5010b12980740180000d0030108520300101000b54410111000410321034180001010301c81c0d19507420840c070f0003d000103407603503142c80e04c8018440804035840070f100103403400c2d0010f0184511071003241c9144c0d4105841030307490703420910000c001606401c400c07400c50082000001d480512a0060f0001d00400310145403151701e101c1503000c008070010500303881070068000d2100420741043c00418207505070019155558858240b04002620001c2c6070221446440c00000a140d440322040c = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 870865809 1250 870864559 870864611
    0xf0b04141b180103082506050103210e0f060c070801060b0c1203040804090515090a06060311040b0d15150203090406050d0b0f180f070312090b16020d06 67
    0x40003001c080091103002c40d0341c00d000c014144c06003048064030951402c04c100300d01d030000d18201c2920b1080d641e00c10046e28420782c012030702c1c410700c10801c11080c40004c10380b80505030039280901c1e6142d54500090030207000e00308200e00409002130070000900c0140000b1001e001068004c1c080d503640c0302c00f0111180e00c02071901009004041c2c92000c1041c084041300e0103981c1001200303041070304190516000301400380c09458100c01c82c42c0400c0c000c1e00e07400282c1d88214010400090000c0ca46240a01a1900c0c0445250703500d008100c14004107035030000396090244542030000e001c80074002d001304804480e411003801e480444641003c02c0c0d9000009000c068020789040c481c0980cbd401c28016000050ac00080500c060100002c950039241040d01707500450820204501d89104100f560401041390406101c1d50001d48040c401d1003044481a542c0c01000d10b00078440514201d140d2421b4054170482030561a503981a500543da2440300400c103568010f03c08108030b15100300004d80c5681d1038106 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 870867059 1250 870865809 870865819
    0x80a02090c03070905060f0c1f05090c091302010315031b0504232802040305010c02030903060a0e0a0c09050601020105070207060c0314040306050103050a050c04090f0b04141b 77
    0x103019800040142c9010b0189074a030b800e64a424881001071a4121440300b03041d8080621401c0340101040201d00c01c1e090184801e1101110100d13100410355900814641403903000e02801c0300c1a494008900d5403008804440d40354090701ea00c0102c01074041e000f0802d242c80714a500110901807240145078086e004c2260a250250b594403d10045d0390441ea1071100d5503495440305070803034160840c050760002200000a005085070310800851001900440080c11790115062041007801d10403c942d440b1107000540c1010b00d02c20000303945900050448902c1030b11101001505002003006080c2c45500c110015641d68980c59800001c050441c0ca46d4010b60811010035025030000c42c51005592079680c48076180101610296a03000d4010302444c0059030400001010540742c0c864180a10b2181018004c148194240f40d03103800b00b5489014812850491201c001603e29244040c0303840e030289505480395103d0501c02c5e0352030000c03806803006010782c0c03410381c0c640f02c7c0400d9041202801190 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 870868309 1250 870867059 870867061
    0x110a020c060310033305040213021c02130e06180103170408030a0c0501050f1614070f0501090c0b0c031b031606060501020706020111030a020f040812030703060b030402010f03050601030e010501080a0209 89
    0x61417100762001070724080c0d003145030210005890780f4150010104028284010f0000c180e80c8890340e01240d22458640c410b9050320801402400d500c020307099040381e801c0b265007079811046403002c4103640c4103210051040d14044542565101c400054600a10201040e00d4484007003180103813a2081610040b6401e5103003c00154800300900c2e581406424011104240120901000c0d15003803401c02c01240c046009000c110000362003840600c080e140f007800086050714a81c54403020700f4a8503000340c00980404d00040548103400001d0310070302d10a80a18021120040c0951070940c401c2c0e403211151aa8038030018020300c111600172008803035003a03080356445035640d0300407401c90341124031030341d41c0b9402000850440803258010b000200320301103885280c070707658040c1c46207810403104c0340003120000402048981c541602c00d483c01001c030080103070714626042e40000c00e0300c14500007070818075a982c400b00e44a44d02c240e11014074180040000c100550f15140c200c2d681d07100d000d80072841400c03204 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 870869559 1250 870868309 870868403
    0x2d15081b360601170a150b03091c090b070602030402060f03090d0f030216020f031e0d03060603060308220b0a0905040c0302070b0c03041502041404110a020c06031003 73
    0x9520044c000101c034459030030340d1141a000301c0500700903405802c8416602e003000c1040142c0c20000c60141104d14000c2c40d4000400d5401d01790088107480c41c40600140700410007440340c1e074104544105901c002e00594070b40d26840040d845001c0c0181350020311300e0200c2000044140054996408130380741d10341c07480308060310408606901c6043c4012480c111442c0f6008018108290315805951004083d10614803804e6000344980240d00c60241c41e683c04207414031112a014072412001d0302840c0790912420b41036403103031443d0380700381e0386000182c0c0d0741c0c05205040e002080c022907016000c2070f10255a0740880c144028542007070b5000d400c2c89a80340c42c03018240580288224bc10b4198003e03480c2e40c10f955010844003080e000103000740c0c0c112006400a480c0c94869200610103005115000325050803270743e062004950020300d8410303c4030001c0180c0724406400080d0801e11030400c40b41c00390380c1d68403200000c0d03951142c0d0340014481d555916503011f24881507464074808084001915510400071 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 870870809 1250 870869559 870869567
    0x409050a1d07062019030c1a161d060a090515030f0c0315041b020f0708030315180a0915090c050607062d15081b360601 53
    0x2d4401c2c900494038010011540c400101c0c0d031420000101000d0f5494244107000e941c60002c030800c421400034585050882c00c10028110001c84400c618010b0107051411540d501c60350a510240c1a0901120f0580403a40c0a040300243c0468480070b0800c030b44610304000c0180c55110a4010188542e1952039a40344001d2540700781c1c1d03c5004c1d0703031244540c0e9403a4070b2050501507001502040c3d0b1224400092591512580070340d6034200a8442000c2c006000210000d0500795600d94a0406800104041180f600c001059942010840000c04d00d010f0b002c42c00240001c500d070004040780c0003220b0030442107105950094120380d000d551406000d8035a203407140d0840758010401040c00c550b0080a200c14145600074001642c031922000610b450300d0141c030103a26000e5009050341e09a0417200350581042406046805402074070034001d00d50420a10b1a25115012100311491040c50b0010039550748002c448010b01203140010011703455052012000900c810051f90104000007011560552017 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 870872059 1250 870870809 870870823
    0x30b150301110702010507260310050907020607030c11070f09050709030507031101031d0d0f0e091302010c170d27140c101d030109020603010303140409050a1d 70
    0x14201d03c3c03814840f0350064400da04420405d8030780101c0410000641c403109060f1040f003500400385540c907490f1200c88104201c4041d00060b018210310018403800316000160700740c11080c28100030444d11104d8008507281c0400e83c04a803554800d40300300042c07899041d415038081c2c500c1c00100b8450b0355561601030b180710000384402410395110103410000320b5800d43c540710f4158014900491600d60640021030f110b04040b0711503155400c0385207070720b191580110080a00258506101c4a500c07003000006286160050100d038030071014076424002c40e84501c07500c01d0300725800385601035180154a0740e0312558000300f001e902c0722850a04d01c007040b0341c4d4000000f00308a0751468020070041c0a81c0e201c84000e404403103c1061131082c01410020f80d5680000c440c03005a40d650b03401001600c0d010300c06105107204100a000c0d074074210350f030000f68030f862084078156505414280c092160509184c00288200d03808030354010f1900051040d04c1c0d0b603540100031201e0707400124801204000c2292038980c0781c = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 870873309 1250 870872059 870872081
    0x103050c060f19201b04060b0901030207050c030f0a0b0f041101050703090f06020d080a0203070e061c141906060e1e04090606052431030b150301 64
    0x1206104001c040c401200780f10703000100b0380c0740082450501c00180200740703060069909594000c0102d8642141c100040121401005c0b9010310150b450002c008034540314580b000344c101070300003400505000c020070011000007405000c0f2800000381a180301d888681c0c800c82203a60034180d40c0481d10702407000031514090380d000310700b100302c61542c40015151030740b104404a00f80402807000242032860484160018282e07030700500303184080054001c284910013041110164414010b100311a94001400c00200c00255120369540c00c0203030071500c0c4100b400405035011410010300c802c05c81d1800c00c3c0c0e0340c0141d400003110380c500d40012071180c042e40c105004002c00900d1101c405212480d01c500807040c9070000e03035030b0344920403003a101040c26580c03e020280e0303103292609010005030030b00c201d65003400030751480154001d0303410b19110b03c40c038172400e001080c001503d1484150766001c80302034148a2070001c02c881c0724055992074940c54048084030f40c0401d50000d8040016141010301405000e10 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 870874559 1250 870873309 870873337
    0x516080111250b07180b0c071401051b0a020f01022a04020d0204080d142514010f1505010f020705040507020712050c0f010507030e0d060b060a05030103050c06 70
    0x3003142c00121200101d80560700311400d0402e082c02d0040f4401081d0580989aa903841442c2c000900c400d0b8885c090007a84410b6242104000d030821081e00410000c0035106009002400640c2d1a001210f00d4020f28418910540e03011082d48030040001850000e098400e6400703114901c0703424016600c88607100e0030610090005000c441d1228911500e148cc0c1400c0204010304206084c0300d150100d80081e0049400b07540081c0d80720a059070008a40402010300c03000291420400200301d09403001154940758a03480c212100004001c0c012503203000c2d40300d502c2c0c000c012411510561001803e514410f0038041c5405d5080400c0c254844e0404458018543d002403403840d01c1c0c4818400282802081c282c2140508400030441042d5440d400c2821802800100441c0d45680200600c4981150106050000401040d070019802490b03540d9006022114000d201e901030230400302501080301040d900400000f80d445100d5004030186069901440c00c0b05c0708140060180604d510a08500002030 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 870875809 1250 870874559 870874567
    0x91e03010c14090409140a030c0b010906230105120c0d1a01090b0705030c07060c051b0d030c020406031b08070807052b050d210501051e19030516080111 67
    0x509042e005814174610485107040d8200350f085645080801c1d4000450002d0480c440090134000380d949481c2c00742c140400c00300421803030700c0c0d405030301200020366162070114131002048050380180191614600e01c08041001447c0c5682e02d0303a9980d200d4600c00c04020302d0020740114810251507000100300068644011090800604140d80d40000b01b085845101c10062042d0114003881094000c2180b621103002c0744c2903903c0d00b0ba061800140081211442c542503040c413035550804148aa980c040c00d00f40300044450003c900580f60030341014141010250391100032202440c8000c0840300c0c0d000c1980d42c4152940401e40e165040b0f8822540e2108808440054290113400b107103c0c15111200007032400c190781d17a05e10717040444100c6110702003810414141e015151180e5501861450f41c4070801266042c031000403c201c000d842020400809000c3d810041d484200c85250f01440e500f0400c400e140c1d403442e1455a6402004492407081c0032400001100c2d5014020b403d8030f05c01000c80c035070030 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 870877059 1250 870875809 870875827
    0x2030d0b150a030b100f0c03120e0105010806070e03010902031510090f0b0f0f13020a031404150c0507080403081602060712110d050d11091e03010c14 66
    0x18040050903140e00008916088040700701d50002402074012903200403d851640300200302c4801c44001140050240780741e00c0d45891944a0130580e1040d82c5400c0c01040d446410340c6140c01407c1289105206602e45000418882c90014401e442419160b0322221103504680c00e141c241c0da00307803100030b400d50b2000d22032941c000d400042255000098240f20000310350f0303c4140d44255441050410b40f001e5407150400c0e0384d414520701c0d42c005054207507002c1e2010171460380400c0516442c8500048144d0340401c428460520035000803140c2d01c0c0135030703038400541000e0500d240405524203001054500d07080c0e2040d8a02c2c02030301640d1415410014060400e072950f242c40200b1351044810050001e200280c1d0310060350b03018098001b103030091420803850403210b840500741c7c03400b05144541a40c0304900614819601004541e5111280e40000c00c001c00c025000340500e000341d80f10b40d0b038002c01d0748450b0f059403038440d03a0380074050a0480007801400403c5100755140700510b404411080303c10021918 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 870878309 1250 870877059 870877061
    0x50f030a020304050f06010e010f0e090d03110d11120106230a030b060f12071e1b0c1502011104050d0803370b12073b01180c02030d 58
    0x50f2150140382665440c40e001080c0d203003451000d8024040e000701c480010301c5110756011440c00039000d040c0d4103103158286941016a2401450408000c25854072001c13242851481c040c1c4650400c045410b104c2c4100f04140180980c00140140c46407403891030000030030f00d11038400c441501148222000d0703075080d602c10b46074461b07001450f03000070f05071181141c04042e22210014403107128107649007a2607900240701d4a1006402410310b00c208685d10000b8440032408103140c0606400c1070030011140400032421000d4042074041c081e04206440200040e82c1c014600c001c110300c801503000700000304402c02c409400c0e0140d80603541c2c01142a40c040400039140310001d5801001e00c403a51031804401c40352541d1000c0c0b020071001c140c5200d0030f880b0034200c0c600d0f0060780e00031081103c0c1d040e44444020000740c0c0e02c185601c110070a0100000f444a4502107000014502c020115030081c1c4401e000c0c0c01c0100f22440c280300d500d4072081888012034038825984189904021958003031454020b903004254 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 870879559 1250 870878309 870878311
    0x210106140a0507150501080c0103060e072a050f06070306140111010b0d11100518041e0c030c080105030a0201020d0e0f061204060c0507240b19050907050f030a0203 72
    0x140a01c0000c01c06400415440c0150380d01e0313000042400f14040d814a9111418403800c14180c50500d801c100c41400042002421345d40c0c4a00b0781e10f130004810400c200c0152021420449948030060048184400e001001c0cc0300004c02c00c40750226403040d120f002e0124201c5500e840340ca1211841c010203040c4940c4242140c1c510162600c002080305c1403001d0000303881003880c0c1d40844510303071100c18846803030030507400719088006241003080c02d006ca03901103000401e04481096110303a035030303552424440c0041d03042c003109281650410410b51105140280c02030030205c641d50b001c0b90207180002120b00c3d0008080c40c00c0c80d41a805400d0300b8402003c20780e0b24810040e001580031904210b20074254548101900500d25407a0b4804440d00349070400e642101c0e00f0311080e20421204105d4a40442d000c20030310030f40f820b0100325041000407502c40e940020450400079590027040d230380c18404142c220012101c1941ca080310031140c941c4801c1c5060b501481201260074a483c8284002200f0704a10303401742d = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 870880809 1250 870879559 870879577
    0x80609160c020d06050708090d020102090604050f03070f090209040f0207202404170a0c0e040809060c06100509070219052b0f0f090302061303020a090221010614 71
    0x5501c507001c1c25580d84c01074031303002ca40c00c0c40060700d40e000b000f185850800203402ca1036607134002103182c00042e00c00319820780f0450060a006801c18901e494550320104801c00041940c5c80341001d0303ca4840c01030030302950022110900c29420000844001400c80c0300b10388074a0350211241503110080540941032072140c0100310b5014070f05105c89000d203502c803201a00000c04142e43c1564171400d0140005002400c410101c2e89a80402c0d183c03000601c5c459854029030760190306500c3c05545501e402c1c1124443e181101e9001840859440041d010018000b4001c9540c3d000c0040312640f20f83c184000d00344112405c0780141e0190b1411440c5a040200b1503110601810a5038007982040c030140b04107c21154a403001240004640ea02c459403140246054916924103201c0c00c641c02c2034010040c072420b01001c1e03c50100050443d902140c828a810300440e0302406074100c882d50b800e00c3c00c0081d00410a0001d0700b05840d00c0032242003d21401707260682e039498071194040c040380402d170f00c050340049010f = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 870882059 1250 870880809 870880819
    0x3070e04061202092a07061b02061b0c0717010b090408041503061211031b010c0b060301020c0a052404170a1119151a040c02120c0d080609160c02 64
    0xf403618500208505d0f2802ca600c2c1074100399540d14518106080301d40c51560b200e00710702e0340f0b40c443e03868035030101c1c91a03005040b126110781c2c00704014507003003c6440b4100b138643c094418071400083d00c4a40c000b84000200d140307002000744040d1441481094442160300501d0400200300510985070819905091220b052500040041e25143c0c51080c8040800701a1800c0381d98210501451170708100765011042101104400f2b030b83c038040080d0043d41c0241d002445041004000b80079a20254151074011091604965000440e411306a8440444041070012f890740030b0340d103500d040c407503000b0580665402208900c1c10030600c1d10007000c0c0d800010318001003003000340b48440600c000b00300811485c44100c5c1c0458900c80382d490181d00c400c4201c0c99000301581001c070101030050b0f41c0c808041c0348042c10ba0b008113600d0301f003940403800d004007079a0744d601c0080c000c00c05c900004400034640f04043c2c560380701c4040c640c03030380704c10080e0912080b220150004005800016508d00c0b402e02d07650110b00c040c207 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 870883309 1250 870882059 870882091
    0x10120b040f050604060b18060304030e091003050d09030c1206060e01140307092a350603152a030106050712090f050f060c010203070503070e0406120209 67
    0x20016080d12180201000d4058071a000d110842ca05032146000800071104d0360341c075050000341411180101b141030180720f03960101c0014181402006200004640241001030301d2910000310f50540e2400d000565140c803c8480d100d4115003e400d060701520f400101c5090018076103215029000d5929500711111074584200003410300c0c9111905010b85121072800d9010070181c420305203060107990200c000b25081142c082c240940c2401010300021440c95480018a100b0205540100203441d140e4450310b4000c3c2e82d40d252074292000030403403030300c0050948860744484041654600c0d1151f41c2e0f40010720104041050b100000080451100490500464580c400b10929105800c01da0019001c13410029101e0108449400c401c640c903407a50403c43c0405003008607564060842d40511070042e04900328a0741039569400503582c00c0c0c00c02400a66807440e08601c010011341040c6c407100c0105806441c0c0500da4a40703402040c0503200c801044400d040e5141e02003010701c0c1400381011951a00b80c070 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 870884559 1250 870883309 870883331
    0xc06040e0a0b10020d1b030c0615051e120a0822051305040213092310020d0b010f03090506070813020a0608061e2413030c0905151012 59
    0x100c1c4240c071803d255005404118500031018040811b44c048030301d003400302000031900190700040365001d030a401403030016a0000a05a8021007050740d0070803940202c013043c0084501054202001302d021059500d1a21103d0030100581c0c1d0306e01c07100005080500501040e400c038070b122403040040001e0201400c0400380d80d440032402c1a806242120b0f00300f510380d4100710541c107009480035091150810100007031903c0c2c1c2c0b65107002c81f40d02c1840103000480c0d1441e00c00001e608024214800e0741208045503a181c2e80c0c9143c10080000200d810b01003422031070421402806445880390b4142c0040207002d10b03507903100f411642000010800002c44030503003d2580562946100e0501070540b94654105908002d4100140c49100000d88001240c1c8a0f40d00c1da07454498021031741015542003505020807580d000480c1c0315010701144407040b44c13510900001440b08000c010001c40f860b5560400039900d80240032000007044150858004080c158203440d564030401c44406005505000001c14103505 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 870885809 1250 870884559 870884569
    0x51303110a0f0501271211010902040501120311030f0a0806210f120906040909060e031204060c2a0c15030b04140601020a031b0c0605070b0105030c06040e0a0b 70
    0x44003c0d0b880c1c0c0c0d0340d0074013a1242c10510103501c1403900c02003401449203000d60f456400040300700d9540c104001c541220082d07280e400b5081380c00c100c0c0d8020010700c4150707116000514980c902c4903003500090030070407059401c03050100448882c010f42c280b13558684056000c065031215406060703903401c01c202c041c0522400580050440c0400c00040242c1205402101082d10700b05c0c0c1d40140d806c444001300103a452590312031088400700c5400480200300b8074880d04142c0f00802d85500c01c2c00c010701001401100064060581c10f01c40d52056508201205e0103050403100c0050300c41e81303071981201001c6000844c6908845824040d0303c0382541704800e5840e00c1d02c3c881042c0c01c400e0300101081d00c518024502c1e180030300400003826921a012010362400500003503540c3d52aa001405010380300d41d59100014001142110480d00818a41003c41d500d10000340558400c4106861565400001003014903000c1640100c200000b4846810304d81002c40160310360380040c088140c850341e2462001406c0d01c903 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 870887059 1250 870885809 870885833
    0x1d040c230412060212101d09120c15010b070206040509250309020f090906010b07111804020f030f2a03150718060f0f0e09010902031801051303110a 65
    0x400c0c0c03c00340c0c565500182011a05ca40038021901d100c4000c40144405080c44250341c8904141804040c116121000c441e81401c580036041c2c40c40031000942d05245070b03400540114501ca0f43c90040100340c1c1c1c1c0302515105405543e0f002540050f0400007045a840c06c1d0380740303503000551490700103032444051130240c1d454409081c0c13a1000c6500d5006140c194503280b4822924010140e440c20800d14100f05882e8071000d050080415403440458800d0034031441c02242030703207043d01400000c0308448130303800f18210050496003203100303000803950601c003402c0110f442c031410540b02c401032440fa80041d4031035541002540201c0401c980e2a100a521960304000418900221072300c01400d500b0040350003001d03007808240100d29025075620802c17100f80d10030700d500400805898a614400304030b00d0102c891004152403c0e42c40040c200000c01e1002d42a401903006410700602000364042600400382611130465450130100e00c5544c0e00c201190149500070300b0075141806503280c0038855520030300f40c004 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 870888309 1250 870887059 870887063
    0x70b0307030b0a0312020106092a1b030306141008390d050708070e0607021315060f0306060909050604090c0e041b150c03050d06061d040c230412 64
    0x14410050302c001346c1e0288a00406001c03044070520040b6008183d030340c2c41414030044400d00e8541c69680c2991244206450180c3d444240d15801d01c180450900401620369405100404a03854090411a00c0d008400704429640c45d00c0c0d0a04a607107011081b40c0000c48120750505a8210840c20f54403148560903000041418811803512003411181020460708010308803000e00040005004201f600481103404a0700100d9406907542e40910220304155147c00702c1c000c0140c181002d80040e18a50040601074650a665044500160034001c43c240d0710f842c81040c0c003150344c0020034403020b901508070540c071001c00b81001c928440c1590350712019440170f91100034190155824407041003413020945200580005190304e10310b003004c0d401202124640c1a483c2408500c49042d01014060310645040650100042045540c0c03410301801131140c554a1901e02d16400c026110145020301c00d006190381d0701e9035803c101d60054000d2485a4610780c540071000c1205100c002500501440000c265034 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 870889559 1250 870888309 870888323
    0x15030c180609300609050a0b0f0906070822020a030206160c05060306011209140d17010b0a09050613030b070504090f050105061614031207110a0302070b0307030b0a03 73
    0x35103001074561208512480141d00c0e00000100d000340c891000c0c0c1010f840603000710700007a949030103140c014640840c0e03080081c0109014002c200301600c41c040907502c504140015200c0e15510490b0440f42000c04031886c004050a210800007640c603010748040c01a40b000c0c1c045000252a070700010303402d400000000b40c80000d42c50426082007070702980000208000d541c001c0c1103051550010b41001420784e600d610465466400301c042c007403031016014201d10300c4015600d8a140c007071401045451000c005204403d8194000150b0b0b02202c0115003d548095881080781c0f1b041c882004007aa00c0301011231101e2070f40f05000300201d50381c0c0842a00480c8503031500e80d540e51034101800280c8035030301070305001c03145004010446070320344130101c0d442440d1a404089100c1c16514100c4102000012007181601c000f04001c083c42c41d82480b040c1c0240d0180c2c5600c82a9400144440da0354000100c2c000e0050308450801c120506020300a1a0001d90609001c0f40302038a520200f83c00301a00da20a8a00f5 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 870890809 1250 870889559 870889577
    0xd090c170102090a090c050409090f02090703020409140f04020d140601060c060b0108190527030901020115080c101b03020d03270b04061409030d0b090115030c1806 72
    0x1030310b01362004c034004141485040c003000c080007801812074001e5110341800540c0750b02e030000811400d19140d80745140e0003400c440d02414003141c020003e4200e4014000c00c2490040c0981005540015644c425008003c90580980d503075420b00c000c103403c030141150800c030204401c00c40214203005950103880c580e0381e01c1c007000e103840c1480c100381c0b0007041103207060060b01000d011140300c00c20009560001c0340e42010a1f1515a02c204c2d00220080402a800c403045901110710364100200c010204c84400341c0c004c0c0441c03240c114114005080903c14055160f1162800e65581d00b03028402803000c0301c560402c5e2000b07580610403070307520041c0841c0440060f0800c214080b01c071030f054030400240c11a4141b0042400b44d94440300c40402242000140240e00b02100240030044250409118807071004403281107400d00c0305501da6241c1141e0700c10f1100740c1c1800112542814410079150403900d20032500e440c98a08107009030000d002e800c0a030b404004d07040381d4850f500c0202c0c00c210b60003840541d0301c5200d2 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 870892059 1250 870890809 870890827
    0x616060510050a03031d13021201031511030a1a152d041e03022d0f1e0307031410050a0908041a3006010305060102030d090c170102 58
    0xd07011040d0049407040000080502c08a51b00a4000c3c6044a091540d480707541d41035000500b0b8850040c0d025208140005483c64502d0180340300c2c00c1c1203030310888900e5a1040d00441503420758400040e1140d445d00c0c1800003070740e10b170901d0b0404070100c029800d26441e11028500490104007488a40740592900020b1030310702840ca260f085449000c0038412860307040000c00e9068200e107c0c2d40714040c40d001c0c0e5000751403081c6481200d10801140d000300084500110004c1e80c402c07100142c602c506011305c0040034400b450400550f01ea07040500100710a095046054005803500071201070f541e010b100b440e50200002d0301d84c0313200032405000500246890068100c860080d14002440d8500840c00d00c1c14110000d0950030985041d503280e0412610103d44950a9500c103001d00c100700716070000540c0601220500d0a20400c0c071401c800c80310f00c0503542e180001582594002d8580900580c402c1145015100b420351000c2c010f14801e000500c1d0665503041a071389030b04003019100e80207035030008031120703 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 870893309 1250 870892059 870892081
    0xa200604030c060806030d0914012106180c090608190c120f060b0405060a110633010c061d0f010b030f0a0308150411160606050a03021e06160605 64
    0x83d100c1006ca0050403805200400244419013500c074030b0510403901002000d03141c0c02941d40c0c500781440d500004d00040203e0640c10080c00a5124030310350740320600485000c00d0994000d020503844251a1041e41c00e00d0300500311079011004104c2c02142010b00661280c02c484d6000b45605003100350b448400d06490188000100c07615007810000760ba01d000c0c0c0c01c0090b900000240c4d8116842161425110761210009032905000d00f8414086c0b4081c00301005440c0e0101408a00703401070709000210b408995404000494021800313960100d08101401400981e140d017154820300c1ea501c101c0c0303411079019030340c00f8509200c0a080315116511042c104a040c24200a4000c82c13a03003510042a070161141ca02409150340035000c0e800000c0040d0007078202fa2615003200c01d94940d8500107954800c82c0748000e580c01011140d00b2102e01c1c0c240800000c60303103018800201601d80060800908019618490703444810182c00c4075041842031200c40409a0f031180c26514050080101080615010340010 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 870894559 1250 870893309 870893311
    0x1f2f0a031805010915031d030310061106060d0201092310080402010c0308090c0a060309030305060102030301061b0f0c170d03110a110a050d0e0910080a200604030c0608 74
    0xc1500401c080040205a030f02c400000308030f8200c0c82e903041001501c200200c0291001a010340c1c403158008174503100c00c1c0c80020041d8840c000c1a4038504c2c43c16129102200c45007a40103c0390855032200000c65240e1a03c00180101700d841410710204490b40d031804010000b80c5c12008080b1aa580c0318511841d04004018503191942c03440c0041c0c080c0390690003e8500c00320307034a0143c100180840000c41440c03003007040c1200801c00030901c4840c0c583d00c1400170040c07d103c20085000a04001c08240c1340d500001c1030b0707816505641c1b41e2800d8034100c0d000840385000214015505401100c500c1c0340418541c00c5180082c1c00179100314101c514103055603503e010030400b51841018642034805040e4140781081e2115440e6074903211404c40b0008080d107140801070034014015000f503c01a0002d540c00120201440005654068156030340e01c1080e0032403409481895001d400c000d6584000407410714050001c0b400742c0010903260b003081004035100d80c00c6908101c507504807081c001d11440360841402 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 870895809 1250 870894559 870894587
    0xa090501111606050a091403120708090d0b0619050a170c0d0c05150708030a092102030c070f1208030720060118051b180405041209051f2f0a03 63
    0x44110f4401c1f81010030f6940d4881c035007001141b40040f400c182000307000700488401031002441c0390103103074290410310741020042d6207052007490409240036840c0700c83d0305102d0417280010300e00f44003140f03001007a10346c02d0b4150f00300f02c0d080c1c0901d02c081c406980d110b005140d0080d010301400c000507400e003010b101f0300356224841840004014440302c000074038900d0443e135001044050102e4103480b18035100d0341c1340d0a50440d110f40c2c1142c2c10312002455a000014041d0980104100c0c3d04c4103030b4680305008150402e0040070041d4040ba910403000c00d041000950300000755140c00611940e0006e2810b04a80842101c181940c000350010002218004010050000e60b104200301074102203561646d01a075994a0310705224000c82c00542c8960f00032811079a07010064410b101038645032814004907041c1d0000a0f0104103c2c4001044a017050304011005017a40c0c444066060080c0109480300c0c62800f5011410b643c5801c046080e1500100071001004c1203a00200a00980d030314002e0030226150301d617 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 870897059 1250 870895809 870895829
    0x80703080a090f0b160309120b0a0518060628060c030f0e01051905160507080106060215040f1704060f080a0e031e0f03070c03140a090501111606050a09 67
    0xc10702400c044c600845002020800e4401c40000c6a481c09840e0100151701c44c4c61680700b1000e8000900245d080d17941d100b404040410002556006004200003007080303407412499004400150541c10b0030f0426079030307103400d80c0d5006001c44001c2c02148600305843d0844030000f8031314003e22041581180b64a408904a402d01024540c00c9800082241c05441410395085ca40755610542842c0076404840c429044203500044506860400c00d41e1004244540c50341da62030800b0000d2180d1010070601c8a81e5900b404040b215140da840300d50300d83c44e40c0c0c4019180200403c1e80c0400b81501400200001c160030749582d510b20344621000703001c0c1a8004c00c5000518141031a18081080c040f080b140501c080042084400d030884400301440c0c00b81820305c0302c01001c004140414035801c130b01c80c0380c541842980c4050f180c040c011890740720b5005d02500d00340403800c03072003081c003a560150242040b119540f000300d460058118010070b0031006282d12000101c2c6001800f4600d25a0002849001d01400d1903 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 870898309 1250 870897059 870897089
    0xc0302100615030f1113030c050906150c1914160e22020a0b0306101115070e040f0b10020111090d02150d060906080c130e010204080703080a09 63
    0xc0c09003052030301c1100081019515040a0200541644005d100c000c0e003c68054031200492841102c204140c00b064401881017000010903260100c83e8600c25200074020487d03582c01005c5000540d0803003823001da054096070724078102c1e60302a40d002661071405071082401689102d404e1605251900d03c038810451032000c1c007030013411181d0840c160030450f650344014180c41006a40d003020b40030414025440021001c000501540180c05140112004c85145407a103413030070026268007980d0030b402a1580c0140c46040d04611a9521030380d03000c42541407005900b20200b0000d0304640c584410380003002e0340d400210f2000c0c142102103030740701c14190000700201d909015819019026180b2054401c1f855488031800b15160142007919540742c0055260700d8009004030880504140d005a1041e00e140030800241c1140c0081c084980160182910800b18100c0400e00e01901d050410b440300381d90200000240c6130340410080001303601548159444d000c40320300081c1144e606030302211140c0002c00c = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 870899559 1250 870898309 870898319
    0x5120105130201110a022e0c051f0605090415180b0109051803121506120a1a0a0803040302030d0305090d0e1306090504030f02030c210702060a0c03021006 68
    0x58600703005980c090800d804000d00c400c2c00b4610700b60300c8520094102d56024140119800409101281810001840150200c54040840703801c00090340c041d0040e031080b80301c10200320540307045007209200460080781180c3c68001242842c036050300c0c11a0b01128150a50b40c0500e558401c489450629102c038841c2d01803140c90b503032211101801880c90031981ca05c00305030000c0f21400b910002c1e0b0220400e507500c40032070606030444490222054018411440c032203440034900441164032602060364407035800d840e1901404010207040000c440307101d8604429007031654460324080b005105543c000e668883c00c6105050a00707869414000500d804d05041c000c0f0100081840c1c00f04000307510b01403289064140000340075191b05407100041c87d1600c0c401040c1c64069420051141d4040c1d2103016603d040040c00301c1e6207124004610850380c00a107004c680140142d400b1ba200d4048200025003401401d03000a500d80c2d0051602c01d010812040104041540502141c5088070b50981d040019034500 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 870900809 1250 870899559 870899581
    0x406181b09150519081e0c09240f031f060b1905070515161b0308070e030309040212010e0a021c0207050f01060f05150306030a060903090e1005120105 66
    0x36010f40780c40343d002c0c11000e050707500d840d600c08001001260200e460003a00a101d035100508400c440c154140076003d264485810000708160041a51180725210782002e1980060410310400e081e550201c0c0c1c442c00071a442c1d4040010940c460701a060843c030009110045400300c5245a11841211a0a01079207400c0c1001501e00107001009090031565040c480c9891400c00c0121341c0d26626000e0081c1c00e004080308191204000c1581ca62107803c0c086111354061030111031958030080c002160100050b06251040728161514040501140d090246000c00203081ea00084035450380800c560004115801d04d001c041d070740150640b4000c40c0fa004915a2502c02c1c9603000011200d0389030005280c1041042c1004a01b0044007500300800c0b0300c0d61a5608040d06100a00c1050301c50701c10716422040b1b1002c840c0852380105030080062224040030765410b00503103480d200176000c0c000c4510001901d140402207ea210380c511607007940303590f81004100400440500104000c507850001002421089 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 870902059 1250 870900809 870900851
    0x7082a040209180c0403030f050c0a02011812060b0a12050304290304050609010f060e061203070b0c040f060809030a0c02040f09060f0e010b15030406181b09 69
    0x80e1005a0b4992040002c2030b50690514280e242e4000518104500907001c48040c0c42030303034802c1e502d081005034510303002c440502581e09281344680004500310010360184010303031510000030640d030000c80d81c2c980040800380d00501c0161000e90b01c44039907200a103071002075513014200c03034058400f4a4840f912540e580303014a0181510b91540c0d4210050740c03d030718015804054100ba21020b54038641450803507120304081d01c0c802541e600703000160541c2281c0c0e0050900750b482030600c1c200603035030b00c208008481c400314021460350700013000a80003081c00070341c42074414070008280304d5555203810307041c40300c041e6190700403000c1080d41c0007840b4080401100b1074418541364905101600340c0740c000030340140b031501800c0c2205032038a1080f20070010180c224040c0e10049030420003000990402c0a401e0f00d12030b242c80356118650008039a070b403601d9540a10b0b0014050040051400640007064920b03080400c41511000d00c0d102c02d42080c0c840d03a28504000d0501c1c0c250903ca214080d89521824500c = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 870903309 1250 870902059 870902143
    0x40218031e030301090b01090f03050f01060b16060234030e0a0f050105090301060e100f080304030203190618030801181b03090326090f0106080c010f0c02030f0708 72
    0x203103d000031b81140e8412042000a09940c48103016281da0780e1409a5658001280c0c800e025420030900050f004108000d0301e0b84010208140581c0c030956a803440f00950040c80d60400da900200910000090700b03012100c3c1d452014581c12500008d103050240c610340301403060602c100807014040c440fa042e0100701c801107800a0818075102c0e42c0c4239000074003502140d0094030240840b0010095a411280c0020046440c800d9000240a4403040b036142ca81c8180e000103134156020310f1000c3c1c0800c20320b54482c841e9038091000002d44181c10a04252050109001680010042c0340140410407000c40100110b040e00b8204020781c1c222003800c0007aa1580c11212401d25a4030340c40380f401d040c09480200c1401d020780d00c0c01406800201c500e04031030417003076070030031003d126802c0341d030b0a1010705209805c19603904400a0082e10300040c01101c02c01c9442c2414800c1040c02c41c0d0400c01620308029000b010360300c14000d002d03002d061001503072919000e4280c607603040740e0b42c15014142007049080900586 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 870904559 1250 870903309 870903311
    0x7020d060b060702150301050103061205120a170c0714010902090c1605010e030304170f0d200c060405190b1306180303060302090c090627040218031e03030109 70
    0x5107105002500c01c2c05807200107501314030400a90b10710088100f005605994003601e04120050b22a1000c5094040c41c02006005922005012003044c2404020b481511200c0c600340000c5514880d10001d080010f603582e008d1032201180e48010429448084000d00380418004c01000e038503500029180d45000c0c0c051004000000b510011500c450848800120f03000f1000f408002d0000080e207559500480c4d05480b03540c02941906041d030841c108490023043d0b1160b90a00b8083c4d040a404000c0404c2002900074103a14005c0000301c481080c017404c054206500034103990b10302820b00d02d0800313040030021000e5403c2003400000050160362155003100b6038005400071000c1501d00040104503180c903035850325100c0c510040070540d15400200c01c0e40c1c42626002a551120700c074040b001e009040078541d100405001c8410000401c090903504102e418200e580c0031402e09001c0f8040307030302c80640c1800c1c01d143d40d103820b080c5050420224001d51441e05500e0343c034918609126449003c1801041d02c61 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 870905809 1250 870904559 870904571
    0x9090d08070e03010c020c0f0907120510120b07180b0a05130e01031b140f12010908040b070606050609090601050307021c030e010c0c03020d05160803010e07090b07020d06 75
    0x109110340b901910884002d0b0080020103200100a5621004010b00780d20540d00396002e60810300b00b154146d0300032903494031600d20071028440440027030f0500420700b0143c0c01c4001c03000928800c0c810252205680510ba0120640c00d2400300105007440150014140c041e009004102c01c0101c001102c85925a900e0041e8603500440c480c400c00702d1403640034407001c8041e08008010300c0744410f02c419644a84042c0c100c0190ba54021007034641000c441200d5120080d02d82c50074203030819400c80810700b50b890f800052501d00942e1000d80b25003160308420690800810b0314420044070303104480c00b61104441c041c0c202041580099541080100100d041050100101d17010303a0080004d6800d807800072240f501c2c03400460000600605020341c02da1660360900c0403c01c03241d4040c800400400e90154080c04d40304201c0b84054680e41d001c00b2403000c400c00c0100048011071401c5020318003804001d00183c3c80c5051590b0010621903007600301600b881001c211100050341c921030b004401c20b03031084000c144 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 870907059 1250 870905809 870905821
    0x40c210b1e0a03080a050405030607091214150106020f0706030203040206040303201c08220206031512010204140a0f03060c0507120c1e02180603120c0d030b09090d08 73
    0x14020b096100408860000c510001e0b510b800001602c2628002c2d800c48200380d954a40840c0c8140381031044800741202102c501020800310f08202d100020185c08840590110307841d409603048090303209800581040e242d1a4001d1814000365006224901e000c0d4203500700703900001e4041c80303948001018030104d10070703420900031a414400720322441c0009982c4040c1c1c1c08880c181c80c2c00da00750345000001e150240040c030118a20341e030743d424a54054502012078030300e43e4280105580040e1256858030154410302000e03541d400c1d00c0c110904601000580c41d103103401e0107026200a0551b1603407286100e103c0500800c501000072004503604010b0200312550b02180076160f0307104419010b046004101035080c146a0004440741c2250300c41c0d18607459020300c1515502890a041000941c49540d0b216445241c1a5880d01190002d01c01000e4901001142012450652020741000d0082c1c0004001a40342c80d00f5206d001321402c020355a96101c1d2404e080417030b403521444610b40c0148081c1c80c0200b10 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 870908309 1250 870907059 870907069
    0x1506041404030f0e1827120705010e0c011e0909020a0c0c080d050a03020702120303011e060302090a03080c151008010f02280509040c210b1e 62
    0x40340315001034940344641414180280a00001a034000200f03080900c2842542010040010740101c0b03141c1000f410f4860655540e056a6180e00c3c1120305219030024008241c018043d1a0700d1000340003800d0341d10b02c040e1518030b0075a0900340c480040c0b50002d145100d400c0c0d8000444111160400c00c48544000604005031111010f0350000c810851002c00c0c0d25240d075801c03441c1a501640504542c4c5640342d95000003a550b00c41d010340c0e50780094020302640f16054007a401409407248000c0c8110490315003c2c02c01851508240c2c024001c00c91140c8807151100b9480c41943c001d410036250035031410301d03082c0c0403403000700c901d10004003040c00001e0b00d001c0400042c841002c0708070001c081d40300300341011284480f61b10340500420354036518014200d100b158442c4201e40a601040c1c103240349440468040c00180616201705205100d000c000c61207942d501ca205202c00751b9242e0300d0b07a600185841d803004c4a030900a0174019426841d0021340003056484040ca80303080140100f00521801014020071 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 870909559 1250 870908309 870908321
    0x31c1e0306091a19080d0e030f010c021509060709030f080d0905030901020c06041202190b0307020102070b1f1401050d0207050a02180408040e070e060a0201051f0305150604 76
    0x441d440c980040c62070b883d82c00001040e0207242c00c403051072000012003810024021148a592041d038480b100034080140596480c0300110f4006094500c01b50b8403960080c01e48080c1414a00142c1100310544281982040842d070010303802001131010b8500361001030082030030327400040e00c150a600d44d84003c211070340045602440054109001c050650303c2d0450f600c0e0405400785e0f0250041d808004810305140d4107450031603241110502d0a1001c540030311810b803410f03158030101e40c42208004034168100f00001c500035030007a400146d98400341d05103803140c2000039000680300803a611002c1c0f10001f03404072107010b48011400101280002070010780700b40c0f146043c08007201c0e0000c01c00c1c1d130503c18080740c1c0080346402a01c0000a40c0306242501105890448000301030b00c8050200780860903041c03802c180c0c402d02d030b42000c0d01c41c2e5207403c000030141d80000082074010f0391904e04100a0800f0103070801e55500ca03103000d9600c1c0c98110398bd050b0721250000e80350600440710b9030004609030b0752a0054 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 870910809 1250 870909559 870909569
    0x11030a0c030e06040519080106090e0705041109090c070627200315010801050603030c100b0303070b0c0a1106070e0d020a0509180105060a030b190f0e0a02031c1e0306 73
    0x10f600d06c5010024110800c4152065020325440e180b070010302d402560188c030700101041d801402d241400d10007004001c2140300b6250b040e11000340019401d03070303e032a003646024001002800303031101c0040c9400c0d415181c1c01c0142d8007556031100d0603003d40306590251191220f0303006020552036108071001e540749080c00f200b5140d262281b00346490707418881204440c140d40c0048024400d80e030358441850344d0b920030001500031030f90006441e07201c000110303440060841d4008091381d1400000c0d844149076030500f80c0d01d842010340d0001d405c010054100444c3c44001090030043d1100d480e0008024000140035410940030b09070200c01c501c11581c40140c1d540241400400c2019a414000f40c80342091241c00c030090055843c00011075070350701d810000d800403240d01501a502c039a940144054034528030000b50345100391038012003011164540900381089152000500c90141240105480c0140c1c0e06200c1c07800e020100803d0804550001c21782002000d020950b2512440320344003100102400e5003c = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 870912059 1250 870910809 870910819
    0x1505030a0f02070f1e150c1106060a0b0c0c090103030f030c0f0e061b010203090102041e03050d0f0323191b0c080d1b0801060302030f1501050c010203100611030a0c030e060405 77
    0x280540403155910400d100783c190f48d24a200708900c0822140d59400580d5940d03480811001e04011400e4004014641d50381c03100140c070344010318280442c107409801c0c1c20407001f02c2c80c00b801e2180300c194507105032541c41040d40740c141c9582400510181c42c0f422503801207406000300203280313501c811241004488806802e0000c664074508622100c0c003d4000b402540300c032240b841c6c040d001c5c10110b9504202034070b412001500c2c41600904065030b83c081d1082c0c0f1139041c5a100c02c107649031180302401004444951020040c0d40d4070740154030811000c04010420507152821169034922031400c2c030305010f030020074140314200d13096904140c00c15000d21740d000009036040040032400210143ca18401500a5841c0c3d48200e0340c8420041e41a4001150102e051400d00340018600380d924444c2c00c2a41d04060400da882e0081c1010204c1c01d90380110380c040c14800c0c801c83e0030071449500941c0755041c0c81c8114042c5042240c100802803050300c01103c05010800402c18510203580d0351801c0b10010040200 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 870913309 1250 870912059 870912083
    0x60d02040f141f0b040e160309140105090d18150c0b091f140a050c041205061506070804030b07140406030b09060f0307050909071505030a0f02070f1e 66
    0x21103c0c40d01442900700c0b981c20482d140010250140015a82a00e48440c125113a5542d81341702083c100352002419001c03d40c5444606000c0b0780c652141c084108681c40021580c0d10342140300a03d406020f8511004002001c81c1090b00c0c0310481c00400141d4640030003c6110715015001210000c03e0715102401d0f50701c81200b401604c1c01c001030f89802c0304e042401140c4440c0f018110310b10844400a00504c4000c0344c0c1c40000308042190f601040d404081e0880d1103051944aa04181c0502d01c601c004580c0d9502003028010b1410b03103000c155401c0c003405c6401a00e8100c0c43c0c1c0c0c07118000d00891000070002000303900899070aa02034488c441c422807441c800c09031034030341c2c8120080141207101c0000c2c0c004c2503204041840c40c284007034209285c3c00040d0051030001e10385014004200d0000700b000c4070b11b0041841c08254074946102110380780806685035178a904004030842c04482c0b01e0200c5d003034140d204025481c0001c02c1c0d4041e42c2c4500381c00080841c00d83d180c1095900e668249c04400503e240380c542 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 870914559 1250 870913309 870913321
    0x40507020304061205070903021201091205041a0f1e04091503201c0f0c090603020916170a0f061e05030a0228091416020303060d02040f14 61
    0x20140040341c40d00e64907051031482c40300016080b61740548181c4002a21300c602407000d810450382c02084541010000161010141c9941d0720701d5440900702030001c2c0c400a8100302505000388130115001e000039203d8a4605034440560386446040098058491080710b00c810301c1c22604280e4005244806050001c500d015801d40402003c5000c11500c1480d09148442c1441d44001c5030f001c50300010f0144004100c080400410650101008031811011480c211000540800c0490000c110400b00410040c0c114810001040f0005160360f441c41002501e42940c070794441c5100c4020000650480703000d807078400d44080680141090300c17100d14100140000c401141c1c5180241101808911644107078030381c002c1584070002000040c3d07001c0140c48010310700c01c20b000c904c0c0080307084441c8402d9180c0e0b51070741004d040c2c4602119405840a2280030070202141461034202a10060310185185251050005031145006a0040d0083d0360714445100b0020303040d402001c000e8403148802c1c4142ca414 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 870915809 1250 870914559 870914563
    0x6040503031e0403090614040b0409050709080f030313031103071214040807140607021c1505010321030f021303020a080604170306030109080408011401060912020d1104050702 77
    0x596540c1c60b07180d11051000b010301455090325000c0c41d80b60307458180c007a01d014000c55030b044204020241c10681000001382040b0011300502c01040001e07000301d02882c1c56440507013040c1482c0c2c40700d20550010810301c50b218902000b2691302c00540c1268005450f2242003c480c4d0619100006200d8400056228280024800c8040e4910021303134034480400151440740c54140521310502c0c0903940b20078000d00c030080300703100c1d010b4524a01030403030740c14407105d85c00061002c03011010101e0564640054401481010800007070344240c3c0c008240704e1f40d451f6030768414a8040c40c1a6420b101428442c1b00702d01075200c1c4d0000c1d081780c41d85110a5442d880c503441c0700903a1200c86c1c40224812001200d00085150340452070610580e00103020b07580c542092054481541d10040000c0d6245d50398913034640002d180300340504094030404000003012014914040c8030303920103800401c01d011021408000c86884c1801c0d4040544d41926124040c0704a860300c91121458030400e26441402c01003044011580 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 870917059 1250 870915809 870915811
    0x207170a0815060a090303120e01140702060f010513020306131a090f010605030126071805090105010e0109150510052703030a1b0f2906030a0f140604050303 69
    0x54811503146552402c0e040003440d100b03031102800414120a400c00c0820f004080310360ba00105a0800f040080f2004015400c45510844030b0040314506424070149035030400c0f1182d80a05009003c45482d41004001105600d50401d8400d120b600007000580d561101c1039104901c900141084c0f0089800b040c00c0340c103504007514554000c55100c0000b6410f10240c0c08641c0c102d940c1030310340600c0c46c5d0a1111603810074240a0301840030140502600900340020030a50000b4841f11407080a90a4507210b10025124050582422030707061100600c5140c603401d080380c0c11a80411400211121505141000c1e4420f0b5481141d01c00c0451508954460700300000b4020514800c5000595403a0b000002501c7c00f41d1200454065000f0302c030501209000700c821a00810b804008007000714920390300e081080784c1daa0703012141e0300000e0101110f0320500300d8101c2c1402c0603800c00c01c0d54a103040800f00e81c2e07450580c0c20240418401200d244207000e506600c5500031118a4143c40540c503190030160b5403640 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 870918309 1250 870917059 870917071
    0xf0a02063019051009243b070e010306120804081504111302040314070807090b03030d020904060503190209070809060703090602041509030606080d09090207170a08 72
    0xd100c0c00d0081c40000b451142c5481070140b06868503045003044003004c001c01c150001840b450644034803e4100062074010680100500c1c10402007080b01800c0c1c1030b2001030f0700070903e25890489498068001070035000d40d9030010061819801312410040104c01400c05517004100e0031001d000c0000c1440000401401510560004c0f520085000b480e00b05084004543c00380c1305031005240c01141d803400141d4090000150b410250520ba00c07a03c40e40741c00c03950041003e003d17501042d0100007a8005006600080400c03c0c4104034409869020070f4503071052080c9000c0c459800200022140e989a0015026000c05002c40d64a030001220030411554203d03000c0c1d1280210000041c00c082c42960403d00c1a00014041c0100e5107680c041503010341008601114145c0e02400007080c01449104200c03082c5c015503032106203117491402c006003100c08540010601d0b410036400c2090f070780d421031001c100b111006200107070b4500c681e007040500100010a10800008001546c466983e4400029802a0 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 870919559 1250 870918309 870918331
    0xc0c081815070516170303040b070c0212061501050408030901081009090302100e0703080405090406060305190b1501051606090204020f1902010c08060420040b030f07020f0a020630 79
    0x4d03480e0000010201e601c0c1702c0d00c0c0103540c010000240050209855150817510f14245806000c015a0014a140624102d010820381c4003c041004942d0342c0c0d44010606582030808a00d41414500c1c842d0312486207020b09414803c2420108084118003a003800050003a6076080024082c603140007511054010320350304a445c200042940c0420f004a008000c882c0c3c42a1414070f0540360406100c00c3c0500100b06440d40e80d51440000b000c11400d01040d200d0000c0301d46450003e10303080c6011440c40074003810404903013400d0106d45605036005401c8542e8030012103010384402d4081d00c0c204001d4130103140001d411030300115140c90b149204401501503000d20014884800004982c101d0072038011202c140001152034001ca46281801d80c441840c0b14000041c0c0940c000450720300c60007960103640500d0b480c2d0400020030280f800b2016040f50854450300c083e241507011000620380c0c0d8444190003a204020000300c8095180c0d01c201c0081c580402402c500c040c10079813000c480403007607049130120003e07 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 870920809 1250 870919559 870919603
    0x1b060c0915110705090c0c15010602010e16031103030c0f03040f050f090402060f0408011107020a0608010f03060c0e131a0402071707051f0e010c0c0818150705 70
    0x10b0b000300b82c84a0b0800401d4018248140b0706403c00c81c00780c8001d820104070020030890b00710301072800d006083c40c1ca410050034090f00c2d450108021300f11401c1c0310401550340c11401244980c00e01d4641080d045030b0300494040382c075420881c002030640c81140c03542d00c1a8410b82c40307070515282020001d481114a50074403c40219910303002e10044000c8449180d510200140008005282c0040030f0007401180385840c60626890b40c2004c0e0071201c8503045440721850103e8201c045103004a0b10901503e035070b181c40203003545407011954a2021500000700203d4413030000006540c840c0c484818070440080004d01388604880b4418010b1190740d6400858002131240b500142c18036000711081030f03a000c8001c000d2140c60400001040c0c11011045805000303d80c003d000c5906298402389032004103840000b05030012640c60f908482c0e030503005000340014030715078002181c0c4090941703101c0c0340381007148000c801e00d03640059036040d29407012480035400800d95400b13100c0002441010041d03040584d00305 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 870922059 1250 870920809 870920849
    0x60c011116030206280e010f090f1106041a0c0102071a04050106060302190e03150f150a1424040b070501140112080a030b0a0311100f0509011b060c09 66
    0x40b5500e803400c64170720030705d5182d890040c2c04603561164140c0d8a201e000021203040c10800981a90300d0700c901a1002c5034051041382c10722290310b00103042303608202c80040c40c203480c0284904800341c81d800803480d0b01a01003403c51101800b901100c3c00c10f580000340c40c6c200503550881307200f400c50589082d40ca0b03601e04038010541c24028800c42d0100030f41c0b5404030f220b05c00348038802c564040c040c8503c4d54050084104114224012081042c014109000112801c2c508404440000f14614054503c00d0f40d40744002c109600c42464020800c4109491002c2d50781c07103030100301e00340c0c040111100480040c0014005041d681e8003010f4034810b423040009100c4181c8402005500500038003440480c00c218040110025000380d00410740c1c2c001604002c2401d51000c0b002500740d81c0710b94015030303145461070000c601c5450214102071090955080120740365000080080071400703401101c40c1441550110019281c0c03007c02d4030400c2951281051060349041c14005040201c10320804202071820302c1d0b80701c2 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 870923309 1250 870922059 870922081
    0x90b0307050102061b04030b090f190803060409050c0d0516170709150e0408252001020f011e0c080106080a02032e08160e06060c011116030206 63
    0x3007114016401014682c031020100380e4566034408240c1c4181c101004000005044a5181072003036031281d014264440a00b05400d090000c000c880c65107589855031808005102c1e181940e420400542c3c0010f0000f942e8030301140f500c1d140b404081e070700c0020306940c4010840c002441840c6a6400c15001c20389640d60641400101548400c00c1c580c0d410100040c8104000b80c4d04c05174920a0030440a908240e480700c01d07504460007580c0c241c800c0310000480100d441282d400e40c031104507084030341d07002078001c40d103e0080e508101c5840c1c1402141e602d10f80c11aa83c400c00c400c482c0f8600c030f20020081560140c61408124030125030600d19541072540700c4180c240203a080358102c4081d900ca0400c1030390741c0480480254802005090501c1c00c0a014491032214020f4034450349440d04030b0105080e081c10209071408204000401c005000c20005010491502d1205604008241d51031502c81031421fa000b405019000c01130741ca81103002c038400c8030002020700c3d00108039010b5000d03601c0782c1d00e41c4200030f2 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 870924559 1250 870923309 870923323
    0x10030b0f010f120f0602130518070201050c0c2e1401140306220201021c0305040314090d020409080d0e06070e01031a19080706020c040513020d0b040602071b090b03 72
    0x42c00042418130030202207100c41e0002e008000a1001c00c51541e40c40b0800039004040c03240c2c00d800645021810020002c3e024031940382c20842d0301c4a44c0c0d041004c0d068515540d00b80d016000007088032089004100b0780d08a11109602d0081d01d0b81c1030007200001041000005024030034030080f44007015218640b41004030701075021b1184002c500085d075801c80501401084900030890451203510940e8100900b441008810000c040e500403d071810310f401c00918081444008602d1140c0821500d41ea654491078101400d035415200441c01e64040c1c2030080306400b80843e600e10319810300b03481e10b10035400441c00c01e100380e4030760300c42c501001c200c2c0c030044080b10711150f6215560061400d10010130b142c109103521000440244d02800580c48505440c00c1c07003030650119001d0383c01503694004614160040e00c1d400880d81540d401d0312100342d00010268030107140c020301780c80b02100c00305050080c40d8044900c110340264600c51540ca5129079034080800e03e101d02480d05191102c07045031032401281003 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 870925809 1250 870924559 870924563
    0x10b01140403171305061b0f0105010825050310060e070503010b03010b0d09151a010804020307030b090a0515040204110c0c0108090c1f020705010f08010e10030b0f010f12 75
    0x5110544680f10307072011a91000d010321640e2100c0550005031544d030540100300840f62075402d41000d064000000e894005065880145079041c40014000c0c8800001c0341c0586d01c0051840c0b030201060b034405131441b9401034020a4060203144803500c90422240c11120483d50260300c04022607482e00c030119024082801400e85c851002c0004120000c0d0110150150445c2228002400001a61020144e030841e441c0ea0040d1034964000081041032210041001c00b020302300030340c0754541540040c1d2142d81031300004140d080313001c001c56601901005200b1540d40d04c0b174220364000031418416040c00504840403807065040506004450740d04806503420488000000c142900450006450140000b81207005a02c82c10b000c81d549566241e8513403907102181c0c60302001c0b00403e800b009081a0683d0012810300c01c55080d8882d83c240c0c003001c107904689030480031300c1c59034070303040e50200c8528030f10340c80680000041c9060015042c0380c20f1242d41255015034aa41407950b03229810b0045903484000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 870927059 1250 870925809 870925823
    0x5041a100b1e04121b080312061c0b100806011202030c01080403021006090605100c030203120c13060806131107081806040803030f1302090c0d1b02010b01140403 71
    0x40b064031890102c0c103140c91200b000d15441d06090b00c4e01205140410407180c29210fa200240c8413480c1c42904800b00c8000c2d10b05040510702d40002d0a416500c2501d000c0d040e14050f03114803009818140c1c0d017561908103668010001c0e4002d080030070900e00d40c010b0500908505010b95000002c4801c0c001d100816034a034060080c000154580d8019074007081c0040081d0f041d03000301a11415117180d039106480c0544080711f0009401381c00c0c001030000380c2a0509044041c0000e00d081000401e40020903500100c140c421180880d40c0d0703d046507451809020902950344a0740346000c030310143c01c82d420a00c90070b01a9081c2441c01012180038003601c0c04841d8140408208001440105600340d00804400008003003201d1090ba05002040740c552160740040d103c2e41001c0207010500c0e428070021a0041c00c1116035280c2c0782e1941e000554101300142044080c0b01000480000385a041d4001d21003484100c2800c2c2807003d00d90001a02a02c03904001030b0000e0030100d075242280c9000b100f51000e89401940b = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 870928309 1250 870927059 870927067
    0x5030d0b0a05010c061a130e010b0f0603131a0c0405120d09260304030812150913210905030f0304031112030705030c0307150e0c010e0a0905041a100b 66
    0x100c0d00000d054107020040111446101b9202c0d54540040e14544480c8480c8000b0309801d5025200c0d0031607400464852052200c0c42440c44542e44074270a40b60048844419640d0502d110720345240d403aa51440d8032191894603108010160017140083e0046800540b0700d01140da848406964a4484a00e214000700d01c040c2014007031040706031000300d4420309000c045050320a500c940c10b45160029401150201c6c0c0024240c58201880c2c0300e2103401400d1404032181000300d0600040c0d81c400d000b408a400702c1c001110715030034409540b0101002e28800c80ca20000841d0440004105410710700400380284200491007925071800030498089942000c0380b080c9240401d004c01045c042d42c000101524401070262502103102440100030781341951005594565003032810242d40e620415045540e03500e018090300d42d40c0c00100314503070320301c20900e090307008142c1c403000144240c04260000c620481c5014204802c203c00702402c0b40802d2004040140c00c0c3ea1082c6031221285064041c031960344100f44 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 870929559 1250 870928309 870928313
    0x15090b071b06150512010603030e0d051c0c0218091b01050d09020f061c1505010e131d06041a160e030703060e0a120503130b0901150305030d0b0a05010c 67
    0x1034890303000701024590344240580d580e03000501007000c480040617075940d200400c20415802c50781008070700000352405490401c0503100c4940b1150040700e484403241c403003070001c1641031007070203150703845036000340390041d41c41e62803103131900021085480d40702d9072244000502a01007001140c10304480140e4440f8900180503d030704000c0c02441400326001640c11400003410344e90b20000d003004c2488542800e02e28100300c1300600c103070f03990070b00c2861502038802c000b0321031641d104201c6c3c002d88405503101a8400f100100040080102c01d0b0003c80b04210058044c14019011810138045c0340140000d50310952b5940c442140f4100954407905444402d8041c204070501030641c20000036401401e4bc1c0d2441c2c2d40340c4841c0c00765540314007004015000000c5060401c440300f90303900004d41e503d140c110300318504800e645041d01440d540180076500d1403000a003000000b50400000303280318010002032030340d0f2450f055542c0c0d002b004029800c54202441020a4184030090000310b5074160349681c2d00b10716907 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 870930809 1250 870929559 870929561
    0xa090b25050a0501090f03030c0e0901060e031c12051e01030b072a0228060e120f03070b15060a030203041a0c0c0f0f1c020a15090b071b06 61
    0x50101240c0c80c1c06a15a001c01003202880392501700e80c0200da802030603281502d002011a542c9050580034003c3c1911050b10b05d48481035420706603482801c0c041d99109580e400a450850030105c120b070311010760b02450070300c0c6500c100f0701c617442c4088410600554036035030321080c400881d1001c540e905900d07803001000071858140302d05802c1207160900f09502a0003246400104140c51200341444240341e0f191400c504202640780140b503e80300402c410b000f0300a1010000480d01c2c400e10303040024500070745003907540780b00078240c19155030170440351800d030020b040c1038503500041c03001d0f80d244220a00090088103000b80b40c141620001f842d180c50f045603074200303800a4001610980f20001c80c0d4041c1e441468030781036058003aa90740703010381341c84206ca1441c0600c0d220000301c0300711440d0080c032803004030540d001410007100f50301030070909803616854408a1500e414107c3c0500040200e230b90b412189203081d80401d90141c010208202c8565a80106076900d504c1c4180211a6400c01c546c0003000c83c0702 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 870932059 1250 870930809 870930877
    0x20702060d0603060606080a0203070807030e0c03150106030605030a030c0f0606080615030d0513030f0501110f09031b1012150905060909010b0d080304030915050a090b 74
    0x2004000608003040c94281208482c0310b070700103d8415540c0d10044c400c080e0024002507001035040e03400d40c5945070090f0001c200d40406000c0800349a11000d621048000506c098a2001f1014040300d8030190402040264401d0030b10591020900d0034201103164140070a580005980684070800040002e50f0742004440c207840c42503403403c2e03643c032010a80d0710042c412240103000e032072518420028140109401d01032105456014800e0811884001d0141040c0b1441283d800122030305043c600350626038094145a001c03107801e180c002403800e0601040d14090100008145c084640c181ca601040700011201d0101c1d056020140d510724440c5c0c5072044c00c40903030318807030300001040c14009800c0d44c0746104007030b800160700d2a4548007004030311301701904c2007a403141c420750082c032400301001c0202d02d10307001049003e02202000000141410f02401e5682c00400d65803010705400c1040e050010555080300301684001500b19000040e810f0b051415500d074610b090294440460003028944440d40d0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 870933309 1250 870932059 870932063
    0x70309061107030f110c0d0206090405010e04110907120c03110a0905040b0402030105060318011824110910180605031603020a020606010c020f100914040504080a030207 74
    0x2844580450028125024031072500940803580c0707440b00c01c2460094002001150008100103500c4144440c0c100000b444030300d120400d035414184240b1500200d2068030903442c140ba0802c0c1450000226030303100d64030451080b030044006454022519040101100082c1c420200007030a8541301c04185065a10844580580d400c00150b903842220750132007035401895110f404035407002404c0029007414042c082e8040780864003140f440d810100060498000a0800240d00c0030048080d41d21160075840314042c21180442d280e01c508a40c5041150911401030741000c10040360511040c003c80c41c02000c40b00303210040100e0134404071200f07026079246000340c00420044486000305c808480f9030300780c1c00600000d0341d43d50341ea4600181c1080320800901003600030548100303e0082d40a5001ca100d40e0404000d00c0c0c00c850080042c0006030007a50030f40c1301d0340c2d4400c030380c0c8401600203904001224211043c1c142c0c3caa603401180c00821044800880300071b0400c080c10840c01c00344620a03401080c420b4 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 870934559 1250 870933309 870933311
    0x30711030c0d05040513020f030a0207140a05010501180b100e150d0608070503150c0d140a09050708151314030a02010608100b011707110f1014010501020d080703 71
    0x1c54051101c0c03a110700d02600c0004034400090a00042c2041082880700d402c3d40c400640c94042043d0062059200082403134810541c003040300c0381000f080030380304442210f489003240c4006499041c018002c0138284528900d5060880d541c0c0300c200118016201e410400070b0000c81c0d10349412a0550b503542148440039130180042d001030b01da100c90360b400b800411305e099800141c040e00304803000e0702c1d00c111500304911a9200102e030f02c01100c1507005040c1d00c01c40300380d5441e0f00c81204a44440180c07900740e244104125511007048004d000c50790045040c1c0b4094800c40b40403035035502207076888840c5158060b400b40d52180000e5080c1c0545079900d440d0720300c500580c0303140000c00d0024a055403c070b02c0d55000180d441f00c03800c0007954000c06c0b09180c00303281c0c45000c0025034903910003c1d04512292060201124159000840c11402854000b004894030015a60303000c141c01c2141c0c1e2a0102e940d42d44100b103103040300f03050002245e02038150581d041a0020541004000e4044d00d0700c00c00100040101 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 870935809 1250 870934559 870934567
    0x806120c0f041d070515310308030411041b02120c0f1606031a100e13060605070b01080607170a270302250504020d180c06020601120803071103 63
    0x21104042c0c8503281c103a4403c2c09041100e04140400072480da40550f21614440107206410301d00c850008102c20350144d440001c401108265050b8101d141c2a5201a10b9070401000301300910503465071040030b00b007044a04201d00303644003103152520445200640c0040c0d01c4907501703c814603c43e90051004e018610201d03282e81410f401541c0c9407186103141e03000900d040740d03020040660580640e05e4800800170040c0300c491441d41c08144245000900f0a003048000204000c0a480d1020015210050003005001c605c0d20f401d0302400681c4140d07400c40342c514640e03000040d541c00220307681e4000e4206582e800390403100d1246e0f95144030009006070500030f40c4c4484940e123071030032a03c120701604440710020300c900180341006400e00c2e0f031841140c80883d001f818a1600b00c412081038405507402180d00507100c07980c0d00d05010017458081c20881c00c0140501051003401580d9130080100e6686a08841c526a2035405c407a00007841040700901d64441440801c1d40e86010314140071004030341004407424 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 870937059 1250 870935809 870935831
    0xb12130507120c09020d0209030d05040503150a0e12180117060607081216030b01170105280f080705100c0b07052803050907060c06020a0e1207060806120c0f04 70
    0x106da00c84155120303880d0780082d47c80942d003010304c5415024422420454101460200441d407034800c05082c010b0700070030204c0060b150006e43da02000300344440b0412030b080014040c4044180768001581e8072620b511800b151002d40d8070809008100b084402c03404150ba4541c0400c0c041c8541103610104c0f40d0f54402d001000d0000741080c001841182c401822400103090440060100d070040c200040c104020020000c09075549408500e046800030f840d0000d41d08080c884071200c0d451400c0c1e0413248548141c0002032903045200c0c100c8150313103210054908065403001003001d80340d29904620041401d001103000461010198158800240d051681c40c010034980303034203600e100d0041d00d40305450410b240310310b030640c0c103114440e809000a0300402c140c50425601a00d1201c107020010929600001c07049a4188600421b0340183c9000e844125220b25092169880c3c103018080e1071b0000f106030000a12b00d10742000500c03142c60706240940b034070030182001d00c0903034002604107507000f0b910f030618105 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 870938309 1250 870937059 870937061
    0x18190609020603040602130e0606070b1005150d05090f0a1106160f050c030105011a071a040320010b0a0312020a0803240d0c1205070b03010b12130507120c09 69
    0x4450f605c100070040e610300500600c0514030300240c0002080034000c0080000035251401114581c339041410140c903640c5095a0610f800e100790005500701c0204521980ca03402540d000c0c00700041c07800c00521040d600c3d01d441e0b40e510907010410300300940c003140c1600041101a0011025004094200ba14112086442e8031403681e166500321740041c060409001405018001d00b2100a0120001e004c15452300b0002c00f5190b00102401c00940d800146c80410000c00404154140c0203100f4a28024a401d040250032882005080450900d0044021513280c4d4184600c4203401001820201210b0651b02c4810920b01044007110540c03059041400c040341d001e0000e10b00c01c54548231307410781405103003c1040f40101c0a400c035902a4105a180c80c000610806598040d10010b510581c050440b07410100e14224540c0c2c4280310303a050000000c1000d00039840240688009474200c40c0d06521900001c8040412058003e4000c0d00b15800074003152001c1d04080804d02c0c041d0840106403603c036840300c0 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 870939559 1250 870938309 870938311
    0xf040504020d030f11010c05191826060a0504050d020705060a050c0f010911040e15040b0c041d010e06010215070305181006030501060b040f050f060c0a0605010302010818190609020603 81
    0x201d0800b00f41c51001d03609da641c0020002d840d5103400e628400318042d1007a2511601c0c01811002015046150180034803014107500c0e01100d130048030b84505141440c500180b400303980580d481c0c0501c000714a51280005207074000c9500c080e1220b454006890b0040340c550700007244040c46030050a08034244a00b0034040e1604d09170150008070882485541080211340203d0700c0e400c05500315110300c401074820388409039403007034100e0780c2d00c422555801e2030f5003214440e50b004004802030300d189102e19003030707480340c0f5a06962810f1a940029207a15005aa4a605510a20500004050000707801c82c1c425004203421140181c44500300d04548160507081c47d801103c08000035540b1042001405024080e16000300600b41209180070b06045981980c411180941e9010f034100141002a549607501103c00c030b1040706060350701c1c440b200c2c80d0000c0544400c1c4800e0380020300074804500c050809605030a402100403004024a8bc8100b03050780019054880070f58038659540210310268403240011 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 870940809 1250 870939559 870939581
    0xf01051f09210203011410060e030a1205040308220605040b091e060703020f06070f090312170a02030603101b031806090804170307080a030b040e0712020f040504020d030f1101 77
    0x100900d290242c1e85a0811041d0323030010f0b04120f00d1403203608458030301049039100281c10012868500d11040c60594142c841c6600081c4400c2000410908008807802400d14086501c141d91407003540d516000c0362640503500807104948000c11400004d880c08070501200c80100c2b02d1210041c90031100007450940010800380d0142c0c100c1c1c02d070041c50711010700000741e00c4011400d086c681d070120240f00410524160100902c0c9a082c0c514540308140540c0e01680202c1c100140544d141c074000c9003c8001e90020b843c3d8074020320411149541951007402003429950b41120120600c0d010003a00f100500300c4c1d07500b0401e2590924101001044444c01411901d0f03000300c20f0107640d1490118031f40b81d1040140400b42054105205c0500080c072090200c43d05000c407880c01044007007840300050010a1b8803a620702d290b00c07035500000f4400e000c80441d554039500841c3c00c2d00c444007088042c0002e40f00200d40096201d11202d4400c40003c1c054100340c0210078861904800340300c02c05e02000d0071a10f20f4445 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 870942059 1250 870940809 870940841
    0xb0a030207030201150806060d0614040303020403031704081606020403020d050328090e190c08070f21111606060311010c050601140103020c01050f01051f0921020301 73
    0x10701c140340c0c09000320481072040c090450109458424581e03207a08024080e1881041c02424090601040f60002180002109441c802904151501a0082d0b000b0710041b00421940b81c000b40c070102a0302d60b214801ca4200c20b8043c40c048142801e0907201f0115002252560b600740004400341c0c9640c2000300c0d943c2c0c41075004590b107401c2c610751400603a26402100c404000004002454141e0160b00002240c281c54600d294584400741108807a841070301e070001c0f9a83c80c200441c109558418242800386a4944400b10a801051011514154004c1541c80c1006040c0701060800d0340540c4041c0489039a108501e05007962442c0c854000040101e0980e921600c1d11005c2c801d02c440c0e4048a5040344090038035041d01c0304030f81e0794541c80c0d003030510412039440c0c20300706952181d9009404541c4078040f008020400d41c50020b0040600302c00c01c0c003599000b202521202c0c00780452508000c01c017041e0507181c3d42900d40c078001d0130801d2042c140e1440c0c045041ca04d418000103840c01d000c0e140000d0034181e4 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 870943309 1250 870942059 870942067
    0x160c15090b0108120906070204140a0903030e0102090a140307031406190e0d031e0f0f0501050303040f1203050f18120c0a0b0309070e0106051e0301031e0c0b0a0302 72
    0x2400007511006800000c0c06400c1007507030720707081090782c0d0031242210020380c1e44903101d441500001c6c005010001600f06404159000c00801410f02d6004031003492294400700400b14452488900302d0083c1200c10f0340003100301405104001c2003406445058070028101c03041c241c3ca0780c0c0e500092003c80c1c000c01400d90b12140911511041d5801410380302d10440c1130030030244406040b51036a90000001e038406040d0b850307061481891015040400b000c86420301801880c0c104503d400040c0409003640e07010500d0304001107040d207000f00440741103900300411190424200042c00d81e4816424404405100040028601014110001d08030401c910000d00080890b0301042c0230f011240b00040d001c058101c5520030080b681c1e007040072820790b24601801c5807030b0f50303880340c0c0245041b03208e070030154101c0625030000a26030b40c480000c02d031900c00c00c829135403c3d1041703507801a41744c0000c1c0401003190304845d480c420718041c0e10300040d0010340517a250000c00390b518a040740c40c03a4428590320000a070000303 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 870944559 1250 870943309 870943313
    0x200a050a03260a15051203090901150c0305030907030611030a1a100c03140d0b0a08010903020606151c06230a0b030c21070f05090306160c1509 63
    0x10300091009000078404503009519000b04000c40c0000400c01d1541980d503002000c1048101d14501c8080c0001a241040784040f0031001c965a0b0441c807001c0e07100d20809000420782010200c900f02400c01c1e141c17501040482d09540648980e0002400391160348100200007000c28101c0c010400c14181c4038501941c5e90034109441c04c103941ba01c00c000150302c90304c100300d11002d40300c003011243c02c80d0b0381c0d1501407084422458101c1e044c42c4501200f900206c00030600c96a04200da034400d0181d160110b4034100a540d0300d8002900340e6904001c0503000da00300074002055800d2a58075800c2030030b52190b85a2074105810340941c1c00043c0c07014090b41641d40c6d100c0034407502d0041c894041d40e80c0b44a07003121034600e005000007182c0c3e10350760080802c00741020007c50b40e030325190000e0302d203107000c1103000141c524840e6191200c041012241c520005d01c43d081c61321042405401120001c1070081c014080d16030325511994000c0003000030000801104603d1034012034601c0b07680d242801001c0a0100d005841c40c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 870945809 1250 870944559 870944567
    0x3080106080901050405070608100902040e0108010c0804031e120c0843030608070801050f0705121b0c0106180c0302040807121a09010c12060f030201200a050a03 71
    0x1050345001c3e84c508000e000105800040306400c0b1842031800f40341c80d41e115058080708585070b074000444e4034000b240c04200500c0c0c10703050710b05070345500c0004c01100c000c086045400d0002618040d01096205c40c0002074211002d12032809138034a07007840c3d40800f40038840b0100312442c24824a000030121005e003c014555202c0740201c082e07400c003c41000c40c0c1e41040c1c1903210f0603603036059046000d05040c0032803a940030b60051802441c44101b603030001a59000c1c1e04d400707484102c840c1501d0944036800104014020002d44404891803940c00c85143d54030841d2041400314100d68000b203400c2400b14400b42002406803401030000c8425026554076206554001d65900121803028180140801c3c000c02d000085c060041300c0c0381c464403140062840c24004a2070214a41076071042d6518000c20626110540007502d641c4880d81d10040540742e4006002e003100d00c0d45c02061701403948000c040015604c12000c03800d102403000c68400c220426500b01c13618006100404548030b07009238092600b49508 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 870947059 1250 870945809 870945811
    0xb0f0601230d0902040603051501270e120d150803040b1c020d0510260304121b1509060314040f0f02300f03090f01021204030308010608 60
    0x2800d00348440c1d010341003031404080400c00300100d004000304201000d200c4030f4002900e10b64000e4801c200041e02e908186460b0904440302d14105208180005100c3c04607a5254807092003400d03d0303004000c6400301000107008504d041c100d0701e110b4014103400f4114031800400798551503907000510301c0f03c2c81145c40c6540400740d00c600507540090000300b14030712144080b0703040c5600030400000324000b520200002400b030403d1551a1500d040b04009440e070b11003881009481460340c0400b0300c000d114948001d4100321928005403500700384401c1050540d2190582c505e64030a004454103024201c1c060f52603030700705074000c644a0044121412655411112a1000d80441d1800344414880114022030100b4090002002c80c694280400c05118486456481040e070003044079165034010140c0b604480c09a211450303d1070303442000c072041018009603044a080c040c1001e10b0500102000f000040e42007412218194010500d050b40c85460440040000d1031103030303e0342649035041890003000100 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 870948309 1250 870947059 870947071
    0x180a0917032e03121b0303050709080f0d0806010905090a1a12060106050915030711190c050609120f01020304030801120b060d140a05030c012f160f0b0f 67
    0xc00101440c0070b1001c101a80960b034101004405000d02c40f40c0031100c19011400120390303000b010911000301541604042e0050035036540da01d82194403022426220742129408030080e52081c00107802d580d001d0036038141e0224050400040a0795500041703030510780300702c8a40010580d01e80c11501066002e420003080c0d010f007600c0e91503035804003a903030300d81d80c803010b0040e03105101c804211424241d4401c502c1030440c0040300c1e403480d16410502c40c0a0320005203803140c846035006103000b2401d2080c24500440c0820f40000c500f50a2074608400c0c818140c0c0700c2d0160300d8011050550600d05214100681c041c3d4058241c001030362485c0a082c001d018140c1078100ca03030010042000100801c4990403c0c2c0e401c8982140c90286140d007034585030754101c1c2208001009402880d410005208003c4040d00c090b103204002030101d4807829645061800c1c0d8410103007442c2500c0103000c0d50303000715800034240c407031309004584101c1103154580c501d000c0ca0a0008032010550300c2c0c104200c90821010b0300360854 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 870949559 1250 870948309 870948361
    0x11120a02010b04140c0f0d09020627120d030e030903030c3f0306031c020a02040e0606010503040818041104050315040305091216151805180a091703 65
    0x400c4c88a900d524902c02d40c4c00c0c00341d03e60b5004c0347d5030305944050f80c0002d0106500a104d05e913100c1000c1d006070046a005010000400c6080004410508100744203440c0c0008c0100500743c511080030701900244449003565141d8881032001e1212034a0800080403225030510090808a215104404807007a543d040015107039030040c0000181520701030215000c51903101f01740d840740e8810001ca403400a103620840070041420619201c2180c0103d41075a20500070356040c40401d0201c810f266452205840c0c1e0741c001181007000038003184525008d0800d43c80d00400140c03405240c440018203850704420400c001490001d020806843c0030070800303103d0602c001c1d0040c41c1e40343c903860262560080d04442c50040c1d412841020b035400041c4081d00240c000d0880c820041c6496119001c0655016140400800d400c1540b5040d400007428619044a200401c0308003040b075503401d502e280d400044c1014640303d4132000f00c0d20000d9100c1160701c101100e410101d40c0c072468031004000c5101b11540c0c1e0001c2e60 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 870950809 1250 870949559 870949561
    0x18100201021c09080705070f1401090302091308070501050910060509042301020405090a0e0f0a0b011203050910030b010315030f081312050c03010b060f070311120a02010b0414 77
    0x41141d181044a070b48000201c0000c141c0c0e00d50421107124451a040100a03000c1d1a40102d46121102c00c030800348c034003003001c006a44c0700c520300640b0b4041281c0400795018020b180000c00052150088808a40c440d45c3c13042c0c280f24cc079039107041c25114250307031082503134105a0402d11500320900c0b810004101c21102c18015040945820b254150710a441c610183e078101a540701806094048400919018105080781e140c07041004004020040750743c0e4441c041d01526030b07000072001440c0c8140c07a40050031641c50303900e003200030041c85038002c4084080c0882444840c00c603030b5580c1c08030034145299803004180340810780001801c60303105540790840750120000074170108100d5041132641079440b200440d40e03054214200042186103034411060341044154078001c1000c00320b0615001c11082d00280f050403c1d0b04100321150007040c01802c444030b424000900070071f00c50300221000b001520182c60314000c00d42c002400030ba02c10581c00c0c001d40c0d164581d43c2814202449100900342028030b1111031 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 870952059 1250 870950809 870950827
    0x18060f211905071d1f0201020306040e0a03080a0e10141801051006120f1107052a040906060308040b13150e060a02070f0e0a0507020d050910050f1810020102 69
    0x10000c140d82e141280c1084c5400105080c3c2c89100750040d035807501a501e14540400f040009001c4d500440d0f82c40d015506003101110100300010303203100c030280d1580718100070f42d4400c088a0014000c00e1030b0300d81c3d2842070312100049068203104885d0002c01c0c1102c0b06149203802c4e8807281c00c01d0050b00022802e0303854803040140210000d0005000d0f58030525003081c3c903404a05a00018100c101140311f900c80c42c04011250180c86903008043c2035200e041a60031006803c100c01c1030581040022a0905030b4bd0781108200b46001c3d441402030a201d00e10014940740c40761204409604660401b0a40f1035001030549030340c1c2c2207155018000d09460a01d800c4042c4001c170014440018030722040c0c0503c01c04100c18007001d0090080034080c1c4401e0310003006584d034034001d40b4030302e01e0144c881400081c03038280030401d8103101080c5407200030355030344a8600e042030a80511185031490203605080250030f21840d010310b9280070080991040611031501c4140d005002c010716000c3c0700113224103581c410401248 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 870953309 1250 870952059 870952067
    0x219030b0403030c1d011d010c0c0608011505031b07260c07090b0604091d0a0302100b0108060d0b06010c0602180a1e18020705032d18060f21190507 65
    0x74403200100301f008507101c035038005a0311b1544400d4020048807103000301141d4690300205407812580042c04544c01c07020120810303a501c0c0302c2a2800d65140b006964407000105034000200f2605105041c0f44088011844d10300c04c039010804200028500d0008994a02c80d60412101c2c015280c43c500400c4020601400500144110702c54602d0646d11402c0b03521007802c004c5001503040c0240400d8603203c0d180d61400035154403151005001071403800460004c2035105080c80d030700c620701c05400c03004120481c0c5c450030400b1200621150410a04a45a40000c0c81c2e50026201c00c060204103180c20324103030300030000305800ba50403105540000410a107480030601d90024101d40700300c906211800c1044514801034460494090114480001c040c0368074074000d80d00614429008100b00060210007100c10a9449005440b030014500e418010380b1901d031020090541c0084801304c20f16001c400b03074200e0040210842090a14152902006000c014154880d1a0311084900810062503d9580a4 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 870954559 1250 870953309 870953327
    0x3f020a1401051206010c02030a1101140a120f0605220b0919021e03010b07031101180813050406080601030303061505190e06221a070219030b0403030c1d01 68
    0x841c035650000d01148840c2d01031b5440c3c9407040d40107002d1340e11203a8141013150340840010080d60001c0e041c0030002d800d1015000c180d0f50a2805680c0c0e00d804044016850780c054810314a1200319655070341c80c00206603032a60100034468001c08005d0300c081198107496412565001001401280d4080c02c00c010101384505514150000000040e1100a810800d1301414000c3e2003004103003800000115212440c80003809149100755030b8059005a032982145c00da651128010030980e03190300d010f4000504d0440038140420b20340248108150765100000c0030395159910104003a00280010300c1455414000c51014080d5680c0c0b43c2c50064074828010401e01c10400729135180740442204105080c481e09043e51702d03000092a094541000c011240d500325070303400d0048120618900009101c001c2012448013402c20140d400d81018801d409100300440c20110404c0142c1e81d800c000310002e0444103409028a00030f90b00098102c8650784054110240c1c1ca0403200519054400409603a030301c5039111b = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 870955809 1250 870954559 870954577
    0xb060301030b1803090d061d0c2409040c0522030305040302040509011d0105092b0e060408010903020616050325050d050109050615030f013f020a140105 67
    0x41021a8014686415402174030070540e80310f40d40100b5441402125040503e0182803091040c2c04100d282c07a45a6443e441152442e42110100e10107a08140620040345030030510f805d02140b810841100180843d80304142e2000403440200e01c00b45202c10703000c0b581001030180075456011508588000e40580580d200092041d03450300002901050700b900121300c46c6450710300316400040d42541d054081d001c11a1101c02500c1808110081035844c1080074040722100f6400c4102c0021a04040366102c0440b00c071150000c8c0300300700004040f0800d2041455450081e406041c05041c0640c0105030441c0078a0141308200d4140140a0f40749110385c1e038a0742610303a105002240100007141551a0300400c030004081a1801e000000d50080c1e81d045644900c004581101061203201600c400901090750031006c0c010031000140614424018810061034a160380300c50440c003681c1800d004d00c030031846402c00d158441030700d040c110f041001d000d80280c10302c404401c00c0d048000b80000c007203010700519 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 870957059 1250 870955809 870955831
    0x11070e01051e0301020a030615050f0313031b030f0201050703020c0d081009091401050f10030f030219150b03030412080f091807110109030c08070507081f0b060301030b 74
    0x408204a409182c0160000303802034000e544410305144050f0003000c0c184a40c1c100791a00c08a0860f60030310901c221504043c601c1046400c648600c0411045641020703800c9040c0000342c041e1101c0c0303d01d0710210803140e034403991310715105403200c280080c250b84025040000380f41c0107000903a01e950000c14249204002840c0092041e581e810a40d42c00a641d6880040711030b180c0800541444003040300c000030700f4500c0d0000e001076190140200011241212106000c4103078420510000784c040c064118258040c0c030458840012030070044071103010b80c550450b045034294000c00c00d422100c3c001c05d000660120301845c1010700d04031802d02c907a00b01c0c8400428a5100190071500c5070ba001c0c042e02c0381c450000e0407074695400401884001e251064900303501041a045800318106414003130046081c2e815603800001c2c3c0c685a440b910250006c0c4801c8900307010f1030314081070a4000f0007010052403682c50788034181c2018250010300700c0301c42030555030103440104010b0020a143d00312561b004808498 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 870958309 1250 870957059 870957079
    0xf120204140408250f02010f1403090a030201050f060913060219030203010303020c010e09070f03020f070b010617010b07030503041a0916081b12030c060a1a04020a020c040f020c061611070e0105 85
    0x801100c400500f43c069000e609c0002c0203001d02003d00089000c5130034402e80080096480e40c94803c04102c004403901070744540d072800081d00418030711008111440c0b080c40c0c003500300301000031b02c1803403000145410f02c0000d60120040040c540d0400034086507420030300301043c00340309440200d065100005c0c08081031116000c0040041d911940c11114076400c80341045845544901d052500b0f88001e116400000d90314514505091440c0d041e1681212225440a8544034181d981690143c0000f44140c402c021010202c81115080d10b20040c4102202030240440a1500900101c84016074100321550b500007503442c07102c0d165809100170b40360710445500c2c5901003d01c0c035162451180c1312000715940141c0051140e855255001720b40c6021040100c980c03080c244c5400d05c012406021200c01c01a88050710542c80c50078076a00c021140c4a580718054503040d05030880a1a2100c16103100145085011643d049107510190100004400e0405003a46e203140110184400e0018002c0d5842140510 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 870959559 1250 870958309 870958337
    0x10504090b042d06020d0c021b010c0c091b0f03090b0f100f0e091b06070201080604150e09060901180809040603060507180902040f120204140408250f0201 68
    0x1a03101003c02400b41c00150841c0c0d0300c0e281c503001a420141401c030325a802c1800c2c00c6c0c6214000300f29140d550810107414004084a10011500a40030641c03e42c0d502c04a51400710700c910560082c00e00c82c01c01c401b288140c050000714000c007980203801580c5c08040c6420394080000701c0100510342c00c1445d004000d20251940d0101644500107a8010a000203c4100028200514824180c803c44216064400b95820f904021500d0642d102007030780d000d501000351790015030003010b17002c0e0841b0001d8000500c044030a42d480c0410030749500041e80f400c0031a801c0214403d0204145903022060300002d00c110104055005944030001070f00510303050020511004a40307440d40048019508a9401c2c070441c10101c03c01360207550b0910a800f00340c6051180420414030324000c80f0f00702c0c0c41d40300f00c003040c191910200f0f1841d4089100d08030703401612015050003030300740540e903a4005ca004140c01940c1e803103401a207900307400c0101d43c0165400d098843d1500458201171006004175020f09000900c141700c2 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 870960809 1250 870959559 870959603
    0xc14070e0f09070501050301050d03030c0207170a0203060c13120602070c06082d06061e18010809010507120b18010303020d1d090106030902060d051e010504090b04 72
    0x580005416110036020092510481d420103406003224605803506103442c0c8004446900c801d02a05400802031000680024400d501080c41180588160340780c040c0c49505104500c0b0244480781016802455400d0540c50203220071600280c001e14220b10308000044c2689118201e80308d08412105a502508240407407601141c80720303035200121001140d01c80318003500b80c800c29260040705192800c00084544120051000241c48801d10100315030354003c20400550302c05450180b840d038100c044258010155070140030850148006040c1081000b4001041480010034401103030381000180b00019407c0500503155039001040402c26071109004a2081c3c00c4c280020b00c101040000000141079003c121204070219564031500480e460030710b100e0600b2009403102c2c4c0d0040e00c100041022178000da003c2007505d03101400180c1440c402005600465101b241c02c3e003030b48449050040012803400d000203000d4a0304840401c180425a107400e003d000d00207000a141e045104021a22901e031 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 870962059 1250 870960809 870960823
    0x10510050c07180c030608010b0d140c0a18180b0c0d0209031006080c04060f170703080a020604030318050613110a0306090c050307031e031e0309150c0c14 68
    0x12441404508107016143c00e4018624000c900c2c0002e45010004103603020107018003542010014404102d0f000581c40c1c4020003541c0100120305441070407403070661500d800b01c03150020450700e041d60250a04110860055458020061002c1e000e80c5005078001150348410a8200e03407029403050701c03080d4040da041d00034420485110b81c10f22403070541c42907000140d048034040c0c400800940c2c0020144109110544045014240912880b00700a020505401c481d0043c8400e4003011242259902d48a00310f407940003400400050b000102003005061f01401940c100300c1601160104119564640030f441e98000762206d500070401d00f190303106100504001c4400514018442e00143e0f40d03c0c60100b0080c00d581c4170448020140c0140014a40740115040040301d030454507130b01401500c040c1c4c0c9640e00e40305142c00c070184400901c0305400c04d02c0e02e20f4010301c0c0625035140000c2404003814504586d00104c030042c038455013000540c61030607501038101203526038003100100c40c40c1104c4c1203d608081c5 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 870963309 1250 870962059 870962069
    0xd020d0f021c060506090f1f0c0b0906011a13051201020a08060a0e0f042f241801020102190314070201050103050a230f010f0b0603010510050c07 64
    0x420904420100000c039802401c00c5844101c0c59001c0d4078503004828140c64603407058030303404841400b41054605000a0055440200800d4180b009031950a0002c0385010262901e000442c0c580c0d07540104000c143d807542d000300449008106542c500580900030340c640c00c05003c0a0b540119a070303500451202c040300003410000380f4270481c450007841c41c01c3c003e40265010400040e01100440d601f400d008001c1c0054500300c0403ca200b030341d5440d00401c4003080240044422940d0b851409074501c14a500c0310720500d202c5c1c00c1406200108004208041804802401c2d011300790081e02c080241c50703030046414243d54504142484198100140d00a021b4071003401d00c0040441515840c035541640140620f0310114400d51003521104009c034200e07070b0240070040807580b110f07901001054409408620140300da080100441c02804c0c4240e0a1240c0034050040b543c5d1030317040d06401c045082c066000829010f44050341158503080c0095214001001c060090050005091310300107003d0080300046c1c4 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 870964559 1250 870963309 870963311
    0x307121107060503160302070206090d021c0503030106083d0906090605040e07060f050f0723010f1a0d0606080304030c060305071d0f06040914040c0e0108120d020d 72
    0x5942e01d40151603a441250a50005140407810240c6940648203451200350041c000e54109640401400008102e650090340d1100c0f030340c3c42c00c00c02000c04c2e00403c40b860b440307400a9034480d450454040c1c0f41d406e0182c15400175144001c2e0340031010005c4000c001041b48103911042100b640600407010840c00ca4110a001504003080800c05451980243c01182d10a88003000f9511003403554a40f110441e000310300c000799000c00c1c05803001d84a8005800c4c402620415103107400b03002d940b003070102072000c0e103414640c01e2449030100300d0f640700384181c900d4580156414051200c2c2c0c1103021040b443c2c100952841801c803c0b051100348103440d800a0003400c03440c003c907942c8989a081a045014480c490b0400090070140050b8007944910b11b0501c1c01e1204a4100c1c0c044005001041241c0d0752001031280c10a000b0f100001300440380c3e0007040218034040c0703807040300340c2000e0070180030548054104440b007000f01401003101c00e20010340303409144003802007991a1200c1c5034400c0c01034403406c007455a0309 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 870965809 1250 870964559 870964573
    0x1a0c09040204082b051b070b0a17101401110a0606080609100204060c022101052706010b1215060301030c090c03050106120209012016120503071211 65
    0x30000060301012a240c1040781076210205070710042e4501300843c00080028a00784410490410001c060003001c14002090340c08041e2111006141500900749a00c0010315000c960350248840320100d9400100f48018100e00900b040c1340480c5c1c540070385100c40d0400c5070b00c8114a068020600005540c00d40c040e1040c041d460b500c1903019a11001950002c10a00400b1080301d0b030141c440c070071035007110016122280760704000e4081040343d20244004c43c03d4101604140640c0000a1084910440d900004110f24280ea0810720317004265824000c80998007100041c081c1003650410703104009405141d03100b00d55180200203844808420005030000ca000c0004000c0080140101003a144e0091040100e00c411201c101d0030f4070000e108005c04a183d0781840718034500140c00400036000181400c0c1d0508056101c1c070001102e03601d10106541d045910a54100b007460303d0460010311200e44c1c6041c08103800d8891a483c5d2044d560b0081a0003080c034000340601b070150388030110341c980e00f909079161 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 870967059 1250 870965809 870965819
    0xa050a090c020f0304030b010b161203020307091a041707090204060509013011120c1809190207060617060103060b0a08060a0b280f060c1a0c09040204 66
    0x5000d8207401c02001d030080519005800b0400020f980031642c00c03040c903104591a00780d100419a00818004002d6401e00c1480004201c007846040c00b802400c1e1740041c1e0320310f081038000300250003d8002c410f0640c0050f0055407030b1410f0b00c0564007034401100e02192019801c40e05c031440c000c210383c0151680d500100780002e08542140181c41010021380350903042c20102c95042006400d604d007418134802c80d1760391444200321540d00408992421781001c82c41c001c0c0308001001d0312441200c10913415000082c2c00b1800011005c19070308900001d40f0400d106041c10400c4e441364986150241e9036859011030003406000c55a0040d8000380701034029201d040c0b06035850702c2d844c0c42003400f00741e03230060600c00b56040d81c1c2440c41100d81216001c5010300360035111408040d0251601488040c0c0c4030780c0e0410000340074030030f200d09003800035030454200c0481c43c644501c40400004540c002000d002080c4640c0000c14400e982e403078100d0114444a02e00d96032591180d480a000707222886401520202d00071403 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 870968309 1250 870967059 870967061
    0x30b0312090406090212180102220305011505061b0726010614060708131a0c10050705070b04020d082b0b2808010207060b010806030d0207050105090a050a09 69
    0x1581e080c0503a02404100e40341c03425001a44584180c04000c240030303500084e03d80031000034074071074210548005481c02e042284400181030141003601000042c1c0b00d02002000802d21841d0000803003900b84188251070b0600103501c5004a0a1500100203090307001e5207087c40c1405000050040200811b40036600341c1c2c80b0780c1450944014030b1a00350301e06400855100080000c0100201c00249005d00e45062a0748080245d0400c8148803080c0040c034002045442400c03210100060100813210b459442e2200084d1406412400642d01f0510b824288542140e2090885d080d00350090a8030000c0c0d111071012038200c04010701e014040c00408210300c140140e5065581d48035131102c80c100a410049611104100d070901c80d41941e100034103c3c1c195103080c060351340d41d0301041c0a000c00300e04140d5907420302070f0070b80c0c0c403142089411030358510b403180566800c20900c035003000d025002444001c8500744081d50341d0165000d504d060003800314168070b2030307079a040390200a05030207016100c1407555000014 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 870969559 1250 870968309 870968317
    0x27021905030916030503040605090a09060801140703090b06040c0203090a2603030f0f042102010525121802040e06011406130e04080c1509060106091802030601030b0312 74
    0x1405001c0d44142e031100103c04000344058a811601561070b1031315100382603960f64803203403005401c9090000c0003e03182d003981c801c62005205030340000c00c01003900e0918000c1603d00038881c800f41858455500b0100f00035206460384044d0070749001845004441041c2e295028903200c4981c0085814400f064400c05882c903e205543e928004103420800581d1450300ca02089861480301c0c502180010b0340d90210452042e0003601a070807040d26401c448140400c00c2e941c0300741d00740241c2e44542c20321100c800116040703584103c0074070104200c1d250700c1c1c4004144444803114120440c0e19071800850070304180c4000c0708202d40c0203100300300c5085006201070b00c8440903c1554a91401a0800d01a90500c5421100110455210425000e0400c0300790082c0801c040c0013620410b80900c2290003158041000f08000b107c4020f901c0590f2500481d00c2d450204140c000307000b0005004010491100c400d0005c3d0007136404514090385039650a03004900a02c00b40139081da26100e182c0142094440520043c = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 870970809 1250 870969559 870969571
    0x10309050d0e09421c0b130f0b0a180c0e010902160308040602130311030c1c060e0a020316090e0a02060306061e030a061403072702190503 61
    0x2045065413112580e11021005246110030f81e180303060403503030070a100421030401240600e0304840f8204264045813072040000242e0440d03201240002043c03203400a1141d5114882c0d000d43c0418250542e50030210300031900006040591100102d03001f040180c200300420f0340c040c5800510249203062210f1030b500b0501c0b9010300206810008100780801e4000c4603400c00400c0c82c01c0c8014116944e007141d20382d8000f001502d40036401c2c8030707050791410341142403030083d8040ca407002d40c0c4514040c2054149034601c0541c900c19007800e008540314400b584101041a03800000c0090920003d043d15803c01c010355000950500411200003030800580382c0f02d1342511044103081041c00d03a41d40440c2d6131600c0a40003e548501c0c1800020303020b2419400600340090b6080d400405000301c0007071000c541c0c00c1907510000c11501c0d4202030220024242c1e009003101070072002018203500c0c01982c1507010340450b82442041240142884089000d50125140407070318151f02e00c6941a00c100042c0030780c2080e142 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 870972059 1250 870970809 870970819
    0x6090c09060c05071a1c05010503030f1804060b0409230105060c0c0306100807060206070c060c0c12051903140c0a0c05070801090b090f060a020c0109023615010509010309050d0e 78
    0x6c1440080c018415036050302c2c00503008500d0440002c0034482c0c190818a03032100c2c4042100b060545980301c0340134038001000c800307510503203450800c01e007a816103d012180c620001111a01c0d500002c1042d4812811034400740d545a50340c10f080408070f82040090101e064141c807603101400ba500c5400246142254105819a0010780e107400d001c80c0c8505003030b0380fa003000a400b503c800c03005c0703401644054201d2600d4140a004115280e4272080309c8920f8020342ea01041021500582a0486001c0c1d509240310503d4104aa02141c00820407000ca01509001c0484404038014040c64020000c0c00c010541000485080d40c3e6a01031140c0a00070305c40b822180d941841020940c044000101c5c00700351044007020b0843c650725a40b084000350403281d034685040d900e8115020250b00c0d12190743c82c1c40c0b90003c1c0810101042ca10400341c80c0780141c504040f60b040010700b008030b04d20a00383c0c1b8031036001c82480e05c90ba554603842c00480c054550554054100d0240c0e81c030015001d90080720480c43d101007a20 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 870973309 1250 870972059 870972097
    0xb0c03042c0705070506060105090d1a16090b040e0405160807090b060a02030901082d011a0a1b0318060503040204051008070e100816060306090c09060c05071a 70
    0x2c0455042c040d51500801d558041e901081056000c0c00c0500307502000640349103858101902c86580168802003800840c00c208024086412020414003405403601d00301000038610b000c8114150348074900c1580008414840480e00b000300a21856500101240552040c980c43d50012500c0c1e00d154841d080e0b485241c4896200a800d00c0025101d400710035802540c106084040195443c40c0018643c81b540c001040b1195101c0074140c503290741458114840a01c40c7d130401c6550000c503225031440841c0e9000c00e001a004007031740190241000e0310804d0020684481603c0d040c0d640240c0014445440d04500101140f140d92000145100d240200d80c141300f25100c450081c6030b240003502030700303206402103c0305100d001040b0200c08d42050f10152000545965501054140342644400700c000b504400c80801080341d043c001c01001c0c200c8440100f000c406002005001030030b462041c5030501c80020307174030810b2100034801c800c02000030306800c00f049440c100c041d1006902540700440780b1a2501 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 870974559 1250 870973309 870973321
    0x30c10021f0b2d0f0a0311010e03060a02041a030c0a110c061602030c0d050714030a080309250e130602090d06020a1b1a0903130b091201020a02070b0c03042c 69
    0x16a01140500b001e401c9008031411038a03060301207c550041541400400304840c403450b00c0070004248107007884400140c42d0b9041c18030003010820710058041791450b06105100ca01421320702226503802080c02d1191000c2d014800d014204807807040060381c820b4010400e509800303180218556402d01c02c8007501c050400c0c0c0801c000e80307508650030151880e1300a0805008a1031012041049035800600f21003d0542641d10f001492344100c0c0c40702007607004041b51895081c405007040e01070f0420300c44032810f01030a20f0200f0021000050543c004031400303000380c00038000c05030304454a1100c040c05c00c2600c440b0342d051850113940100d0311280003030f04070f41021140300014180c4c1d00c8030907442440384241ca85c0c0700c00c0d1144190b00181110619002c1040005680e440490300b0400420200b10907680300c0b01034030204100030000d20052002a401040a50245a0b01140040503907000c1c40703a0035104c3d0365444d84c1c1c034514040c5c0c1e00040d41074010781d41503441d03801c0c1d51550140e90300c00c45502501903998103 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 870975809 1250 870974559 870974569
    0x38121015050d12050c0c0d0f051509030702010305070e031005070f02011104030f030e1908010b06120f2d1005010311040e0c0d05070509030c10021f0b2d 67
    0x1002d01522400c2c0308036140c40c5070f0744624010000c009440c0100d8054000d2180011000c0401c008100c0e543c4240d010701c541040130511002078241d149030b1201545c0d1130008612902c9208411000341055a24000103034524010100110f4200d8041c0c2107602e1402da022550f00201420742e012008518450480b144c1d05105008418011500d40c042c02e08080c41d5503191100d0012406e070071030910021078100b00c1c013074607809011012901080143c40c6400d140503205801c5401b190b88060095030100200d14021076034803200c603000401400c4202a543c0e40e42c071480c50018091a07420407500158104c0d201c1000c5e01c1c00307880c2c01809021250020255518010340c03c0700c0813401712540e02c1200f40400c1104038241c800c0d6070790055000803090f1a02070090440e00846030202c8041010030381c0401c0d69409400d017000905d80072442a00c0d28400c0040300100a5960602c0030140e01c0061980085c000440079540c105410024002c2c11020441c480c0c02405020046e00003800132884208505904041c070702 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 870977059 1250 870975809 870975829
    0xc49060519050f04230d081005061204060b06040e040b090a0b15010909150509071403011d16051602060d09050d14090a0b0a020109150e013812101505 66
    0x10000301852840c06e182610170ba40010522003044418100010350388c0c66030b02c01001c800c000614000c44525251030b021040350a460f01840c004c0f20b090006001d9954101d84203900a500124510420340d9103202c428076100f0120402410446a88180301c40d560a1003c4040105003d07240d40085079100c11007030080f00c7c8901c845070762503000418100581d04000d0002608200f4a1601d461190b0301d615070100d1561003a480315070b0b03022000134100d052140801901d40c0000052201010384040c00c0f60052450050765500b1907800700c0d41c43c0c40411560340c80200d034020681c02c60144080b103d1424000d0729520600b0150740441d01c0b41d0100b6005681800446040e0754000f0300c081d140c2400c00e4021030440d000a540c443c1590344c2e61140c040801c950300e80c400300d6036540c0603021500c3d00c0c50061940c2598102e83e8000e1183e0050004c3d445035581c810702000d40741f9078404469800d85000c0f400508054100f40558045010320620481d0203911500901c11a261a0084410442c1c0d1181445041c0c24 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 870978309 1250 870977059 870977123
    0x1510110139080c0d200415080702010b0a090506060702150315121c031409100e0703030e150708070b0a0b0d02130c020c49060519050f04 60
    0x41081300d140702e0701a40f043c00c50400c6480c620400036131001400915a000d60000c140c07500b2650104290558840c10362a80680c861009004045403480460000c01040c05200b14041d1036100242490301c400e000d030307002980c00412507092041030801c0720032698400e4981b0440d840e018424110141041045510640809001401a441c90009942e405a43c0200c88401c050300d4010310f00c0b0728210741d6084d5000303106a2000e00000d400608040742181d640000200305600040d07010004290172001d600c20008058a003000200c0c51a04030b840944500030f002854050045184800c0c440803903c0c00c0e208054100082200000d4042004400e4044000c003c2d44010303c810681c0955100d034004c16103214460044031f00800c4004c00080080e2002051404001c460580001443c50220f186440c00c050b50800e40704000c2c0f0260390144003070114000030b44003a80b0340001c00c00c60158500840000c56007000c0800c0241042d603c5d050041900750340c103441d45240042881c0c60f000740f803210961038107 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 870979559 1250 870978309 870978331
    0x5060607050303010306050a0b060a0e01020717030405040207050a06110a0815090c0702012a0b010b0f0405014a090c0d0e0705130204030b151011013908 67
    0x2c5c0ca0756403640041c01008040c3c0203107644403030340078156482d0b5001604d0041c1c0306407240007501038444002803030207031140d1004030750003100d03003540311404004000c031400d55074142d07005a5564814180b15180c0240c011000705400d1070a50b2070351400610304007030b24014210b0307614140c003a103404002d000340b45180460307140c0c86907960300030411080720305000b41450361060410400045801d442c0d54155800e420700c41d1014040c880054041000340c00d40c5601504004080b00d0400a503200715101900036401298144800c00201d64561000650b004109043d103076202c040400264400c01031303840e40f007155489071501200c0c0001040c6030080d0a94810b1800682c0d8504240703850100002410305420300e100140110f00000c07445440e003512a1912241e10000580c3e00c6255203420030fa00000103100942e048213096202186a8805096510880301c1c1c2c5031a11615140703034105401424a1994190807108021041d10742d1514080f00d00c032401d441d10441c4260345841c2400b80e58040c0d0071501c507560f007 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 870980809 1250 870979559 870979561
    0x1101020406050a081e07050301140604080c0d2604090b03010b011215120b09060f0f070513051e0a1d040615030807050304092703110f12070605060607050303 69
    0x12403148030305650019005145d05040c540c21002040708060580311a0b002500c0000144a04c2c0c0400300e402c240c56805885151801c0d00d0115039035161580f420545120300a005014030a01c4142200c5150131301c41c23645c4100c1841210034205802c2d0380a8030a405c00141400941100d92806101d041403412040c0c482444ac13101154190004000001c820815504124404074602540785083e018061103005079060700d08160446a1510500a100210900401c0d003005503108119508a0b0040500c4c10b04545070b0f440d401c5242ea41c041a80c01941e00440e007004a4121611202404441e9603015a080c030382e4940c65002c0c0b0b046410080c00b004400c1c0c0d000d82c0100e00051a25440840e91064103002ca91095899036aa90147d03480880c1c1030702c2560010030203010484051040601042000314003034144142c500210300180b80c80403010b01070020310340e42890301c43c3c0284266148030740340b2000d54041c0030f91200701022a4100e88020784005241c5400a0140d080000803101e8642e0000025821 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 870982059 1250 870980809 870980827
    0x1060309080a0f210b092a0a0203070b04030c0642050a0b04080607210203180706091e050d080c0c04050c0a020105150f0d03090f0e0601110102040605 66
    0x6104441e24460f04206007007442040011074051002c91802802e10b01140204024041002d00d0202502445088001012410010600c0380030641c1c58246050a070b40c03102c0e212001a82180030f0804094548020300702044105540019524505072140c00c3c10414203c846050310841c80070b0001d824031801d2250018038100d8840030482650140100d0140075168454001c2035242e03006600207041c401c00803c052006000c21701555030f0001c1e05250008402c8902e25065003030480f041385030f080c0d00f40c1c00008210b41036100c0c0e94045000d402013046032507081d81c4607001858115648035000c0200c210140d0700103106220b5035040101c41000b404041c2c00080d9440744c1c845940a41052412842983c0840078180c4a6010b51440340d018040901d44491a1950280c00e452004000f84c0c2c030507041c071040c032000e81d8690210012102040e40c5032080412985000c1c1c400c007015400c00114820000b0001800001d181402d0740320314020b0341d0b4a01000181d500301c0e03080c0d009600460b0085001031140d000c0c = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 870983309 1250 870982059 870982067
    0x50c240a0e1b0a0807080c120d021209040905010c0e1309121115010b12010e0f1f12080901180f09110d140a18020a050d06090218060901060309080a 65
    0x11441d500070420034605036501143c901d40517955100030042d03000390303250380220b15042c0c40c55a404081d100107001c00e05511f050003902c94000c2c18625901103008500301505443d540e010906c2180d03c20002c002854020002800803001914043d00c03c19141b29510540b80150040c101165840007504100c29a20001911400d0010101d0100c52051501c3d00f02c550143e840068020720712402d44641e03502194000c42e0b44004140c01c900c48003480300c8188211245456442d550281310122603020607108000800708402c4e50394022410480100c0105081c07110b502e00070080003409890703210390f045a1140306885910148034603a82040044404c00800486400c50141101c621700318038a488080302d409012100425070100f01d0403000010003100314144c0c420b2020400c00b1044154a699503a4002072508000b802040c0c01080b100c0b0546007082015040303c2c0c101a8010b02c4000b0b81c070b22003c502d0303000407000ca07112403160550343d00000e00f00f8028031032a130615400420f028a030a10b010020380e = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 870984559 1250 870983309 870983353
    0x613091a09280615060804020409080903010609060509100312110c1005070b07140417030d0204172814070b0310091d070510050c240a0e 60
    0x101242c05582c00e1400c0038000a0002d0300d44000c201000004002941094811645411880542c10030b80c41402d0010030303044a403581e80540d04440114000d59030b0300d40780055024001080b600f40d802c040c800310300c3d00306980003842600c0c0c050b0380008840d075441c0c11000c034078000d03840080c0002c030100306d40e480598400c03c0c0c01d40241c2d200c070741243c00c03650580c008a420342070340892080001c0d501003920400c11400c4482a60020b0540c58004403411000740b2200a40c840c40c46a030351011104c6000c091030000500a0701e60403202041d0441d2250f66420703402c80048402c487d01c0d00240241d9200202d20b0615214112002c1c107075805040c045009550351103a10300703148903038041c6407190400001d04a01c0b2003009500c00e04c8881c0790511801c0c6054810010340744000d40148a10501d10107203412440006100003ca8004480e4090350604402c0107440c1d03841030358034040043c050208100310102d9003010500310440c65440145460b0784a01d0b85404440c0083c402410a0304500d41e40a22617030a0840c035 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 870985809 1250 870984559 870984571
    0x319031b12050304050f120307200303091609022d090918010c02150a1515050304030f1d060906090a0f0302010e0108011508071101140613091a 63
    0x440000695212039100d031410640e207400241c800410081000401d01c030840b141e000c10001403020001102e03003803105000041030002004030520403030b00c00902c940c140158040c02c02056036502c6c246049055207a40d03009500c2c08440c01e800900040c0010188219806500d0141c00600810565014000c414160844164412009008a100556441d140c840c083d00028243c80700740e21040c0b07521401d44440401e03110554014240803c200711a1a80ba00d60114103014005000c14004889800e0782951b50001c28031441e81c04414003803250803130b001314010780c00398440e1030380b0b0032900c078080300d40199480c81c0401321100c619100c003440c10580082c0550010042c15036080c070603001c01085040d40c1705d500402000d1100c1c9400c006658008010380d603100402e1800500a6040c01200d030700c03910822495208010104000a01992150305904242c2c60550f000780030500344003058a0204105581c0217101f646000e844455500c400c0c81a14810380d8010181900c407042523001d04d00001d4010f000c = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 870987059 1250 870985809 870985847
    0x120c180f040b030105391801021231050117060402040b0705011b03090309170a0f120801170c090c040b040e1608060901180906060602010608010b031903 67
    0x44010aa90b0038003849205e103c00b4070812545200480080848410422402800501200e054140c03174010b10106e8428031151207c00283c4c07050b801c0100c0c07400e401c0b2030456541d00c3c1c012400700d84000052242c07259000d80807180801d070504c4410710b8491200180300d401e0104049942e6210303003c001115056010600030801401d20703545050408a55000460840721a55500c0c4495611b104001c6800c405c2c11052401704a42e0307000c1da0f40134100c2c15450046400b00940c10000f4041144100801d4102c0f503400000402e43e80494504501d0404070b8140300c1c8045880b2400224400c410342004102e8080c0c03500c000d10254000500340304203144060b1000c41e0f078510800c00490356004482c001c00c01490038445141440c50144050082180c03110000000c0103500814081030b40c1e60b4003200f90540305188214070502010701d800700014507a29030020013503424810005219034040d8010000c032001c403002409003d000008054407544844000c1c64074080c0920100013207445030703c1c402c0707490700000c103 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 870988309 1250 870987059 870987071
    0x206070c2415080105150906061b120711030607050307050f041203090810020c0318130c08060f010201112d04260f100507020703060908120c180f04 65
    0x40040d094a405100b28409040101c0c0c0411040310f003441050360003030b020310081c2c521001a0001510b10b0b030f4007a02503841400b000c039803a031010205004805a0f401c00f001101c80c8003a160240c04150f4104030000c0e1000c0601c0381e60100c2c035050101e1001e100d099950340fa1441c40c0d50752501910070340c00c908184125904c00b40800308038035034029900783c1d04a010f074031060110340c60240d02034600103046c2c4050349a103006028285c3c2107103000003900c13880507030444807280c1048540042680760582080803c901070814200d882416000030096006202c00c0d1510400700216100680c240c42c0790554031100b4240410082001540c0100c0c021110b003d80c180200c2c1d60031000a50600036007180d040080c00d64100c0d51080c0c510002900d200446030b0302c00014110380001c1e014020f8a03640020300390302c4800c0d01c603c0040c00380384c424801500a9544660700f088000614240449160030006440d80000d4181e00424035110210056903107140310444200ba11462803030900201d4400444030681003902c0d02 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 870989559 1250 870988309 870988373
    0x50a09080601080609060105031c03051e0f04030e061c0c0203040b030a1401050a05010503040318050a06022103131217130203070b04150320040602100c0206070c 71
    0x8001c06000f0181d10700103004900349018000c1c140b00040c1d004612a81c002440051007002c400300c14041c2411904000650741c4d194554807003461000b00b80b101d15140b8680810011103a41e5070000d004a00a56440d01034801c05800c1c4400f900c1100c2d68960040c4841a50703c3d01424250010020740203103105403401c05a845a8400c210381090b6100c201950b00c0307414852940b040842070f68018036040750314400e00e510f0403002a0903440050800340c01c01c660025506443c10903088814010900074061140031a60b0302c6000307407107000d000c80d0b40c600c40035421004940454030b00c0a07a40100400f0400050411040d65242c12400146441da018402c5c8400f0100020401c24107413032062409910600d440034007031042608100c1c094002101c89081400181b040214010f07140c004650207040014154070029480142101102081d61103400005404915568042440d4110004480b024803080c00d07902000e07170725000c086408400150b000e40c241c2020400c1c503445409400d0750070641e041014001 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 870990809 1250 870989559 870989563
    0x5040504020309010e0d1d0a03020d03200d0525110d050f070e0621030d0c090b04030c061103030c161a070f1713030509010909091104050c0705060601050a0908 70
    0x500408002c1401f0048074940b5802c024801c66010104882d1003260508603400541c038803040d184041d04004c5401e002401c01107504035118120b64001d01201c40085000b50010082e50014698241e819044440940d00302080c01044d8510382d44083c070b4401d9891801c080c050407881c1e10100f03450a120304103540940da441444040064440c100d005065440c1c400107002c14105020003184001c0305150070f0140201020094900c007011400c00400ea000040c00102c0e00b12040c1e03003109880c008005000000c00c800310f0907283c00c9849580f120400503603080c984c00d0f02c0380030072103217041580400c000c11001621480b11400340e544c80303840540021034021841d07041080b8211090000700300c00c4600c60344019041a80454a1510404da500c8145044034410704191801080141404000300740e05c485070303003d0400c480190103085000c010b07000082c101580100100b88002c0e000380c0c90310000c28040c2c441401150505900f000080100d500c43c180116807d520100d290803c010b0004008101c102c01 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 870992059 1250 870990809 870990823
    0x7030c0c11090717040b0402040507020c0d03210e0c030f070b0d0c030609020c0d030e0a030905090c071a04060f0501030503071b17030c0d02070f180f1107140d05040504020309010e 79
    0x21b007000d80c44502d0144103010071030f480602804190b510410146140c0d40c4c0341c001847c0301ca5810701e08a0440c00400648001010000b5a1103041d00c0c24241315800846000885900540b01102290605030248114a8a41010340118034004404100050f48041590080c07941f000091400042c000d9869007003504917001106444a0794200c0e04100c072040d41d25004111000c01d01c84041c2a461807641e60107003001000e440f40c54080c0c0710580014490121560a81d444181c0003406030310a062003c03100c0c410740310100d404980345460500c0a2140315103500c1114107a990240055241602503122022422244107820f40e14440204000c04e408020320312040860164034029600c034205280007504018070b00c4080411540811030400c1940d440111040c1190100820080b080012007101805060f20100c4032080c82e00b014201240703040d0b602c00401c40c00380690004e000d52451103a1642d00c400305000208000781c0300703100a204510301a401150408040e5000040c040c0150148508140c9 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 870993309 1250 870992059 870992063
    0x30703150504120815041d030a0207031a0f0112020f04020a030204060914030a0f030201140408070501140105030618010e06041406150d0807050a15020307030c0c1109071704 76
    0x340780c0c01480704000c11440c16948405240c204800d80b403500c01c3c1045184d40032601c82500c59612108258020a03040903000b00f5010b4080a8999a0042802c041d6940c0e901d0b00c41241c3d4500c00f0300b5420095000c401040e4002c0c0c1605c04850b95903440d158a1362003030410a98140d80c0400c003000d03d482d086e6901d00c010103600420342c50150703c40780b0380760001d841c09007035034000c0180b080f04107a0b646941d90007180304a5099401004156000721506081380144043e0750155803980c0508103100500c240a8050686988030b2002440503049280214a0f00c500c00c1c440e03550517504c24400710f032004441d800a03006503d0000300004207404034004031361070b0a000703540c2500c0305180115a0b510303c04081c0405580000c4000c41000c0f14011f044c04a8402c8000304805001c081c0040784000420005200e0031003000e8000280c3d00c1003907681500107000754801c0c0c1e81c460202c0c0c500341541d100607000d41c0b40b55806c1c94019640002c0360200303d09000043e00001e0440e02085018000d642c0410101c403c514010381c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 870994559 1250 870993309 870993311
    0x21020117190921180e071202040602030405100e030a140a170d0e03041211040e010c110c0a120215250510111605011b020307170705100b03070315 64
    0xd4500750791a0304914000e850b28200083c13144590100703811a01414220381c07801d848002e5617900c1810844083e024003046542040c00002e00290f0a036000000c6c1003644c0003244d0b5002a080c003240e065451420072a0b606406070004c028050108100c2d25001c44481e00a40a072500e001055603024000d85200d414003096003804280200340300290f100d0603480004400042d485e20703041c0020641840d07202140100302070409181034840d911240c1080804200c6000244185000c00704003401c0d65036401165059842064400c507130520304040d4110440c0c40e41d800e8254031852980030f00c10b4200d4078a80024503080c04101c20011034504031391500d40e48004400c4500e4200c030500d06107003081c940c500007070702150400070414a281506012544546c41b0074400c0081100340780307009800f518a185d568802540c3c3d0609100001e90084010560207126210340401d5081c0c98074141024012068060041d80c040c0a03060103000c03c4e0b50102e0221710004007198074496890340c5041980000e07409100c820307 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 870995809 1250 870994559 870994583
    0x1e060310230109052e0b04060503040b16140904021b0d0201140601080a0f0b0301061d011715040f0b010909120201050c0d02160206070c210201171909 66
    0xe40045a0000d000d455685000d0001d0700b002e02c82e025002805c44030681400c1884542c1a04a201c10505080240322500c0e60540f200c0e0703a02070103801600115025034864038a100020110800d420f160340c26140b554884101c4004410744000040c0c00c80c00c82150016801c21080c5c608814070b07050040e04860301e030018110a8040840203003512100700340c100380303074042e0f50500100e603800a42041d8001c252034070018002010581d91000f4142c40d8082a4140d483c1c1b60021a00343e11064508148a00b09180d912959982d0800c0c040307040280c0840c0c00d6540c01c0702c03007201c0c1c5001180d17a41c40c0c0c229002c1c40224190060030b84440c0490a800c3e8824900da07540c03200c03a20100f00f64071950808084403070000700001e14181000b0b80c031038420281480c9440f175000030b034014041c030f2001c51080320365000303400c8a454a0540c500390307001c1038045c051080c0383d90064003981c582a039500c0c404107405a0603582e1440048400b52400c0071000044c2036440c00311100844907460300001d10603c80458003502c401122 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 870997059 1250 870995809 870995861
    0x307030f05040503120a0c061113050102060c0304031b05030c01020d0b0405070e120106080307050312010b1c0b0f060a121b1409031204170709051e060310 68
    0x214815260310441070090521042001c2e50300841e0f1240c0c81da9101d90005d66491800c0c0c421100307000d2149005040e1450001400d40c40038628002c1c085510002c58204060780c3c42d54016a529001101e14407104041080080c0c0007a2146101a4018011208508100c080d581d221800e5421244a80712540e40c0405c1c400c0740c0606074000e0103407204003503a04200e1404d18040003040981d002c1c54240c01204001d20740312001c2c00940c0b000008054141c19030f83c80b98043d2818a44907402101c1201c00701200301d002242c1c012501003240d500750a00c0d2601c52091820001d010050011050345a921012021104109448210051070401110350fa0f0500610ba0f480080088415801300d02525460000d5454151500407211f071055911103d501030b21001e140000910340180c0b0160f50503041000301e00054114044403807900008040004d5844480d1241080300c01c65004031103011401c018ac0780010420700310403851540210014040c0c4054802c0c9401da21300b034034040c00c1c4083e00302d02811560b8030 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 870998309 1250 870997059 870997067
    0x35041409011202030a1202070f1d0f1303030e010f06090203090715050a080a09210f020303040c0b0901020a021c020a080c0303071212050a06090b01090e071202040f08030703 76
    0x4050400000c55403007020290b0042542d44074000f030010088585006c00641c40b40c001c02845005051103050381208507102c0300c1c3c14215410110318201c04000c2c6401181c0100e01078119148502160340400c0004122518124080e0100c10800c089030b560301c400c01d0b1040880ca02409000d811104405a924100711541a1400850390f0080001d1001da4aa40003000c5c1d00200702c0354441401d2401c040ca986541c20450003c246500b401031646c8e48030342081100200b2a0f8040809840944506034040c4500d030301130380c4900c0111401407501306480410f000c080d08142c042e003c188410b10403a81c2001255001c19203400480d051216203102002c2c0c420214038100540501501c4200c01604c401d2003030501007030b035a00034950010703e500c140150040c0c100c0e100d613940154401e4505030500242c1840c0c0011802008180141c1c0c070000c0c2418924005075006040ba07a08480f40d12840c00c54030360724607034101d80100150300c031246069002c201c00030340b074650a1701803806000c04402966488200b4034000d0 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 870999559 1250 870998309 870998311
    0x336030a030617010e120702040e011a01021905030901120212090309031204030b0f0903070b15120303070915111b0f0109030f022b0309030b06010c35041409 69
    0x190321380e0410b081d84140040206002d410101044085511030015200060103001e0b1403061050543c640500408208003000c5107103005071080c1c00342d444c00501181b801e15540c1d2615005071070740e8420003038034560794421804003e030408500401070078014068581005070340c0945211407580d01c00308a010746490f040c40856440c1d000c40c14014586840c543d501441e04900802d03885070030b0030050004031440001d00440f21465400705000c6154944042c101c020302000c40b403a00d02805021429081c400400401c0300d000e20b034036032100c810702490820b0215108120085031410004407084e42d40070702c9410064400300c0d00c2c0c1501d00c04a000720b24420f0100402040c44414100f003c80c1b1800c2021078140f65038108010780650740040c1042003545280068007118920b01c241c2c45d55801103405041d4404650003d032403089503412015204c50300112081c5600c9c5002410b44c40c101c1d400d440e1500607025294038403140c070200483c0206010421f1904540295100c000b201da1698103500640c5000c1b0001 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 871000809 1250 870999559 870999599
    0x30c030b010212130b071406010e07051812030c0303010e0604090f1119081608030309070608090a02090c0c0105071e1b051903080a020336030a0306 65
    0x810114284000003943e900304800c0d8003200c8030000400d013880c8600001e820380a0318005c0419a5103e80e14544007a00510f003403040e801d00d000e10743c0040b4030b218014034158052010360380c505042c00740c6451000c0480c2640280289c3c00081d210403507455550500c0540f00c40c103640300141d42c0b0b80d850080d003010f4206008004a1103a86040032510028001003040c84503260401840d0101d180c01101040300c02046040546210a60000006480000155064907a00c5181c4000c40319903403009055502d01080e543c601080d08155400d01c6441c0c403800006511290b550104c40170400940c0100303107511819507100c00300c0040000c00059180c001d01481713800409030314105800b9903507903203840030740c02012075404100002481580c402c00a440c054022540d00441510303101190050071240740c0b45400811004103210f0700003d150f00445201340ca224000c490012280c248100000d2007050460a0b02016810000360700c00d800d030b510401c00303804503940540340014064140385108680f81e2020000d = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 871002059 1250 871000809 871000811
    0xc031e12050a26070804052a03010b0406230102010204151707021c050901031509060518012603190807080f100e07110a1208061503060d0201030b04050f0403030c03 72
    0x1143ca00d804080340d6845072151401040d2912a403422505108a000500308806c00032003c000c1ca40d60225440410954103d000b080488460014032080e2455032103600c50107072800025a0400a203a00415602d8505200041ca0948c40b1030007411003610300da200e0000248800102c080c0354503804d07446a04407000d800100031092004688215011400d16040d003007240110300c2c0d0120ba40a500004001c200318085410000c1d11a0500d100520443c03044c81d1091583c160f910385507404d0740c00000d050350000c8407820420440b000d03010389600c01d081c00140139440b00708a040c904907103210990b010041d0503a9a0121401e08050041402c0c40117803000880078040d209006400003880030720000c440315900d0502450340c42c40d00940300c2c0080702c15061064041c4071405070400c502490303c5a0825070607207a210280d12001e050200d11581318503100801038040000c1406440c00520888c1c14a03c14540480c4000005001c00c0c01d8600546142c0740d4410074405100416404d8003580c800301d03000f850 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 871003309 1250 871002059 871002107
    0x80303160513080a0b090c0f010519171302131806050403050408030a08010509070f0801090b1c150f1a0906030f0f0601060e0d0c031e12050a 62
    0xc90840c40c16581400e4401d0000c0007545100c1400c0e0400719000411040040c1c1d12112098100603200700307001c8a04500c0c50103010181260b501e400c0c081da1b4845036041e5166818441d408003900b9441a0000b612418003020b0041c111042510f100c2d0030f489a00003c545120721a01841804214102030f1900b08205051482007040c00005403549076600d42c0012010a00d5140c6040035216441640c00c000080d000001e40c1480d025041002941207840a5402d06080d40c0c0301441110a0306902c5ca040c8001101034004101a208a42003154198001405000302d07190241c50400d084150f07203812070301c02c101e980d05442d140702d1a201e1001614520b28040c400d22412038100d003001d010102030584200280004103250b034404010003801c01070400111040031480808031952103c09203c0d081c001f039a921070100325410990031000b11035600c0708251001030709554131214115100c080151045501e15203000200303100070030400d00c1c209603448603070f9112040803004180d20309945400b42455500380c = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 871004559 1250 871003309 871003321
    0x11409100b06041a031e07051806030c03160e0303130503100b030606040906020904060e0f0106090317090303071a010f05060c071e120803010528090f1e060f080303 72
    0x40c4008100459502c40c00c1d5a0355a8211590f05d000b4007800010014581d6601f00854141c014009000c490b40b140d0303941a40101c03500030082c5510040311841c0c0450818004186c0410302a0403030300340094603040000c80f88980784042072642d0856031140600c40c0a0210410140c20148444000c06020480520941e401500403c0e0b440401620040c045c640d210825024030403594182d40144100034802c2c00001e9480c0c0c58113104020a42e40f281d00f460b007070000001c0080c094208001200e601644003c19494500540700312030f0000107105030580010000200020b801e090500300740c0c15034408442255041808000c1c3c0e8542980000c1e02031a010805020f14000020b294411142d248103042d4400a1407442c44841c200c03240c0c8900c0144003121140c004105105014505a9100342d40c91010707840d0031807a00030130f0986028158800c2440d00380a0010242ca900000355440d010a03001c40c1c958441c5428540300c0302c6081300032102d280e45180600c1140000030100c170040500c40c0003542503007440 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 871005809 1250 871004559 871004579
    0xd0c080915130f050d080f040b0615040905040c0905060102010b0d0605070302040b04121a0f15150c06010f120b0a0b0d0b04050c120d0e12011409100b0604 68
    0x809910340c084141000031104000701041d030102c2980700e020762600164903e440c66403040054001c8011516041c0040c3e5a403c0d24001c1b60710454020040c075039542c03548170511825400e0b00c6610490721108000109000d03082e409841d00a83c030602c098054103141c403810344d0844402038501811641000713103da04a81d5000c90b0095515040f0138005110f40b143c50054000703100d290701060000c040130400240b480401a07074500c0c0c190203022038104c240ca031440b6018801101f11080e12103c034103071002c0740c05244032003004c401d440c00103024170014078514000110150041c1c58040e9450303200000501c64084000e0200006060b0011580700c0c4226550702c922041100034524190a6031780c3d40e070f40586582e59040c1c0c0280c1500000c0c0f013201401c1c00d0030156140e503040c00f001030245101c0c846d610300d4054000348826000000e595003200904c00201007122b800d1403054221080e40d250034081405604140501d80101d914030001c01804030f602500000740d520840c3ca25105480c284420000d403244 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 871007059 1250 871005809 871005823
    0x111c0c02070e090f061531060b1201140a090e3405120304050607110604060525020616051015031202190201052101090b0307080304030837050d0c0809 66
    0x501080e0441f240382e8100c01d564010b0b40054920b581e908150002852660b12001403505003100c188800d0207030307200d8180c0140500c0810b14990808555881003042629aa10000740340b5940003c0e1070880092103d10b100000c48200035068841109503207105280c44030440308010401950400095020185403c1d103c4c007440c883c1030301030b03940014100c007004203c005060003050002d00540e16030703864040040c201c0c0c01a61800c2011540e071508050080060145500099070040846250542d014241300030350401040c22180f0b486842c1c8400040d0703d07640120150004050744e9141c42500e1800c0500d08000e454014900750740010703070303180d200d0341007032640b02044e90f028201700355a0081205025455640c0c03820000f144e18404001050040b0b81e5044a045844100c0c1182da2968580600e287c41e8842d81c4001414500100301030300c4441036510308114020a1039250300b1000b41460818480e0501c41c800340c000103000002c4c105400406c6101d00d0204001c64540040d40c1c0c90302014140d51208 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 871008309 1250 871007059 871007089
    0x40203030910020a060204030602090a0501030b03070506090103090c1502160812070c0b0c1f0b0d060b03030906032d0402062a1f111c0c02070e090f0615 67
    0x800b110b071401214000c0042c1c030720f10b0790300060856403107980741030102c021b4010144040c80740b810740300700088540c0710f4016000106801005008024900b00810a2543c409548141855115002c3c0340108584040a4008190362031b0040b11855812800034100800015803122402c0f402d01e090012000000b81a0081c11404560541c1c41042e41000500c640840e84070464201000540d108a104086001c12200d04400c0400401c040d400942506880d00b50800da50000c01c50314810b40403075503d42140007400300140035a03142500e801c000ca01158012106420030410006488076030404008103100b4903980d24500003aa400c0070f50014200384212140381c005040c140980c110045a14003d03030381e0316441901100c500003060a5a07009100100b41c481148038604200c002034008294100c0741c2503002c458038001c0b8018540700302002000300c10281800c601c00d48002180304234401242500440d020001001012030703510016180510042040c1c3c201c15940c99115480d8032074a5000744026 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 871009559 1250 871008309 871008319
    0x130308090319030201150e01060e0f0f09040302070e1f03020d060b101701080c0102121308030a03092009070c05010b060a05030108120c0c0409031808240402030309 72
    0x601458000380c07074400100108071102010b00d2071a81003680550140344c0a155403241c0c0c1015682da1001c81021032024480c00c0003250042c5149151032174440b24900d0050801850000201c081001281c0000000c8400b2005640036030810f1014894583c1019031100c1c014440824403036440a07004045078081c070000b4014000d180000003008003e41001c0018800030742403848501403d000289511300c6d0140340101c200808001056054000c40c560703104071385c1a0020442612285d140c0b4200d40c0c85601d65220790510308001140600d4244000c01c02051142d41c081240001ca040824008200901341e4841c5440701415a41640300c500105612000908028254845a00f01540504040c1c05e02c3c9070310080c0000d580340c401d83c2100c082d60613a07030103808640c01c0031000c0c4507100303a503c18040b0018107035101d0326480c1114030700780e0020a03c1502c2442d281310b04a43d4400081ca021800d43c000075480d801c244c01c0002d031189100d030714a1541e40f6520f0742d5070240c142600469204e2140c0e141d254060 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 871010809 1250 871009559 871009567
    0x90302010e040207050105040b01061b17070503251101020c030a1509240c020d050403080a0e0303180306060109050f060a091d07021e0616121806050a02130308 70
    0xa99650f8144d5124541041c02407180307141c03d250082c48010700b405041c012a040782a801a6410001302d0480102d902650500340840540302926281d080350b41c1c21181c9100410000c105040400c040aa0388018101001002c000a00e081050f11010040703050456114040183c161341e00044c2c1540225003102070551880131090281c400752001140c007400c0d0300c59050100c2c1c1d000d1440180841180c1c4030301c80c200003040740c1d90741c100c2c2c586403c9080440068028403081c070110b814103000b810000300c0ca080c1441086940304c0403d045404c0034034121400d070058042c1e038001c1c1c10b040c8146503020300c09180030300c813107414280011820340880d2401c0e4010322010a40000d030074020210b1070050a0200310140c8002c405422002081004070303141c00060007489800c00c03440d44400032040007000244041d0486990f162084070485400100d0f00c8204002d092480040e03e02501c103a241511a612120032080c40c036043c40c001340c8001500c0c8584d070900c100413442c031000d0102143c8060700c1e800342c030140e0b0b9 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 871012059 1250 871010809 871010837
    0x13020315040903180f09060b090627040608030901080a02250602040918110303030f060d060b1207030b0108060106020a140a020901091413031b0206070501380109030201 74
    0x601e07080d03484813a003c00224040800c000c04168060000c03030710a000144600780d02c03100f105481e4080d503c0d0441d0480c8061141c1c0c0e001e040140e00c0381080c0b481184800200400301400681541c03041da0042c000341c3c100040c0031885503800b540c0c2c55800203100d0401d51a110741000305030f0f000c1007405165640c0200c2503024100f0040c00d6012034000301880c260602000320310703010076241e2401261085860b51115003d14260382400310580c0d00c2560500c54440c070980d0340394144843c000c0d112000303c40d455a05c0f40009501e41c2c442207400c115100d0b41c00245030290443c40c11800c40d00c81a00886010342c0040010407001d580020062034540d80300103460004198280690b00c2d0100121009510003103003c004a00e1403042d03440320310001c00c0600740303003040e40f19803034500e0008419820160000c1d00c4040504070340d00b241c0740501d0b0440d101801d242c3c40d081541c0c8965003150f000c07240c104141c05141002203200704010420000c4200000910340000c03005400103013040b201844003d05000c0d280b800810 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 871013309 1250 871012059 871012067
    0x90a0c060e060f0301151205070504060e0d150f060e040b0403180e16260622020d020403290a0f09120206060109170316050a08070303060513020315040903 68
    0x1a0403485000c915281d503181c0001070071b40710213044544001048400139010b825014080e80c0d00542c0d842e12010315141c00e1982c00c650011044003420b030410707c50500300c400281074200e842e5140c002c44200013411800c419410741138980e154081c5017001c540c103041c0804101028201170b04140d26050000c0034810f03101c441840c8090384d90000165440041c2080f00700f0b19042000da441442950b603120500d9240c40da1404451745021070000a140c9500024969080c1140440000b09040359035030411000c42c2c3d138403000e0380e01c1b14064456041c0c0201e000c1080143c641b0030f00ca800345d0201d83c603116911200700c0c80c01120800400585400e0b444401c0b4148031030640e80700259141e0481c040c0e118809023024003a41e81e40c000e0f94100e001506400002944000d01d0310a07010021042028510301700c180f44141284071000141a1443d016000403040020000f50050010900c01d44010400610b0070081080f21480c01080000040c010810003104075651032895001400413100010b0854150404031 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 871014559 1250 871013309 871013317
    0x8130c0302100c030f110a06090212010207060b040605010305250c14030c060601091508060a0e160e01020a03050a030507120f0f05180a081806040f030b090a0c060e06 73
    0x29400c05801d81018903083d41c0400c40c0388600b402034540c43d0541c0b100c00d2044030000203060803400c0c19004801498000b41c40c07500034900f40d03400140200ba41c15034811125089a012020803103610b5a100d000f81e807141414001c0340300609013406c0422440ca041487c000302a1079102d18075214007100c0316288405030103052850882600025018490001000d045a072035000c0130003001141700b800300041866100c0d124076401e45500a01d107048201205d20251034000010303040303581c004c4400c0780208510884d1041a4031580760402244481d8104050240004000301001811500100c50120100303801900b10341c08240320389000101a42d52803000c82d0b015010b01258800e040c1444152007040c94030340c0141c40d0081052900b00500d480d511490708124080c2a140c09241d00700c0300b01e40d00442c103d80050014581c01c0140783c0c6600c5103000002c1c0c03269000d1f401911103040102c100740700740700f110345616901142c11401445501c115488010080105201e001c2c2040f00384003040130075440c3c01e4252 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 871015809 1250 871014559 871014563
    0xf031e02010f1b0605070c2a05190e040804150806090c09010e030607030e011d100209011404031b05010c05061902160b06101d010c0c05120105190b0108130c03 70
    0x5c000500780300d03000030000000085c0c151032080803110204e6000302d41e40300414501395003c6202c2425450301041c0300f40b58040d0905010fa5007141000010b000080321041071180b4403807400305640c0c5091844440f401c29006071243c0800c01660100a040c2d00d500d44511340081c000758805485050403001221100200700405406001d51828400e40c142c05400944180c2d41c020007d010550001c08030382025807960b0140c0c0c1450344681c03440c011b003d0032507004100c00305062400650011840f041505540d115600444e011820040843c400100808800b0040c220902e000c240c0300a9981300c1c95075800c0007034604c111004502c10340003003841d01a411142e0603c600e0a2104141c80e02d81052113610034219549400b49407500820898030b0300c5501e503030b5803041d00300c0030880e000402e21004507220440f08004403480f0600407404600c1e59140c504031344050683c9070020516203001c000c10303401c0d1000c00c0044840c503820034015880d107a13080340c2c0ea6607000d4141c00c01c0c10814006810480d544019076800 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 871017059 1250 871015809 871015811
    0xc0727020703122d020d150608091501060f2f030301050405250309030903060e0d020f030408100f09080c060f0c07020a03140708070f031e02010f1b06 66
    0x460810107402c030281c4449100f14050401220300c0d075003020b0303108120a9400260200740746503080001806940501200719510b54000344000c420021400f91407121f422210100741414100240b42800300014003c0b1411005007203002d5241490203803105081c0c4e86803070b084c84841d0810340c00d0000010029504419460300c0d105041c54010045600c0e60300038003416006904100008001c1201b2030851181111845000c01d07c0090f101412002400000011003c01503081000800726145001c0c680500c40440045c01c00c1c4c254808001e0f02e809080d0320040d40c3d0b60400d20003004481c2d0b000c81d41d035040c030106034130101d0545401c005240c024464440d00416500000c60710070050000024000c1c4500c0004201840e5910b64680c00341d030a00034914002d610000c1e50f4000d00c002210540030001c10010001121085600c4210003800e00c08103400100340041000000c0007486981e400070081d400d020080c440003410950002403000110907a03a0341405240c2e8000034048005a1821003002c1c1c10001c = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 871018309 1250 871017059 871017067
    0x120809091803040902210f0c30150306040819050f18010f080105060712050904050a0e154c0f051f0e0402070506010e07140c072702 58
    0x42030100035041b804100302030101d90803440395089400d020306c600885201c0c954582d943c3c0d440000c110342d0742c00958001e50601c200e00840c0089104a012a0101c00c1142040d4007a4580036084c0000744490002c030902c02e9101c94140004192a04121503901d1214101d91000070040c541c1942c0e00d1090080d01000907000049094a41600080c1d40d02c2d5a5802d80e202c2120245e200c00480344400c1c2801601d81c010703000c02c4024009aa1244480400301d030701c0c14a0381c2004108070000b400c03a10f0444040314640d46a03001d000d032100091195401a000580890400f03084c03240303a504000546c2001105940742c44549020707510090b00107442941d0826980d034400b000176094002030103406108000c103000e6403c801103414900382000d400c0c15480040d404141162208040b20b5860041d52050b4002d50300300550f4000c19004e004140c00b0301710030390710409142003845004080310b00250141407001014800340c802100c000c15400201c4000200305801500e40b41803011040103a042641d505502c001 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 871019559 1250 871018309 871018319
    0xe060c07180e0c01021605040903170f060306070c0b06040c0e0604031401050a0207050d200714190e04110103020d29060432062212080909180304 64
    0x14100a00d0000000266000c0d04482c3d0700680c0d440c00c1c2600013100c00e003c2e11005200c681425070004c0506070082c030341800198281c42c0e801380d007041d058a02d040c022407144104800750030104040d940100c42858840a102c90540b10030503c888007410305403055481d10103a55000b8422446030300703480402080160780390ba403072078803409049401954030810b5080600042140e2030610aa0701d115420070301a04144400f5130044a11000380d4004000800c4c07032240745907603140204010006401c08410040c0c03a07885803400c20584101c40138503410310b9030081c0c0041c8680708080603040e41160344402000c204203101d50059019010716100001319602d008000c0380c509c22102d11210741d00c000781148503902000042071001c3c40c4507900518486140e9402600f074400000e0103109500c2003140c0030f800020740c60b0f500180e00e80e40940310600000b03140e010072440e10130005108000404110301c28004c20215035480503500c0c0038014006215000f10720028240f0301d03130941c0c3d901d4400b04100c1620780d1a6210 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 871020809 1250 871019559 871019561
    0x50307120f030e031c0203270a06050f1b0a030f050709061e0e10020102070c0618290a022b02280813030b1003140c010e060c0718 57
    0x4010750200103070030021003600ca4034000c0201c1e01c0146804168030440341030000c07140c0c0a0741c001b4051f04030f400f0300c0b188400342c2c4041991383c0302d82c8990628064001212030303041c80c1c01500c40203000e060008411906214501c4050503645e940c80c9a46050651500008030b000d03401081c0e10840500140d0400d000c010400d584071082405a41d0192104555089a180d41f6006000289a01c4000c50680c00c40aa040d00d40300144203031400e61740c4009440c0440700d9883c2c81604526074048404034402d40d408042020701004620083e1401d001d10455160441080c00c400c20520714a4401c0510700003000007038980b080c4007001d5407411544c181c03d00072141001d03104180c1c0000c001c060044c06101c1c950031708814000b140c0b100740548000501240e0110b5103650240794003a0340c4c009889031040000000290320454101d1060301250750400d4030a02d1410143e01c06009101d44041e0b9400198a40b07075103030703001480c01d01c1820041c0e45a83d00d41c82c602d003031b6515103c0a5007000f0146246c84408400610807 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 871022059 1250 871020809 871020827
    0x302180d0c0e0103081209240603070914010e010611030304081c02130303080603160311040e060903040315020309032b0603140f060702060c03152e0e13050405030712 73
    0x40801c00300040d0703887e10041900c807620704541c00741607d0844000c00200c03031002e1a0a0f000107008050b10300c4107660390349000c1120074440d80c00d1b0010384ca000c01045810400c1d074506c2d00600c0c030350804400c5c4010070f40c40341c0d869100041008000240c08200e01d10603502c0d11250180c56049288119520206404109811a400c0c80103c00249030000020b003141004100d030b03100e1600000f220144941542d4800850840071614940c02941d1400710300c117007150400c001c0d030256103220040c2d50b03038509609188090556403845801c2d1603004009001c21a00000300311200b07803003810300e07003445541001a000c004400e000204d040d418102500031003441044a520508005910700302c0740c1d40c0554025103a25414102c518102503001760380003e02c14030082005503404440c007180e04000140180000b001b14441d008000400880c41c0d60403000c078612103c0c1a9a204030343e0400c202542c1003840050280c0c005012a5800039407070b440030500b000002c00a65010356409551070380c0c04485500300608030b03a5 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 871023309 1250 871022059 871022077
    0x17040b072411040e090102250311010c09090b13230105090c03181005010f0e1005030717120301060c12051611010c0507061d010302180d0c0e010308 65
    0x54400c036215184101440381d4110340a400d40c100782058901301000100000003040d24941d075400b0002c0185d200c07100c010918002d0003080081010441a00b07008040c02001c01e01e5051580c034000020524940001041003116240800455140340308008148203c0c0d451415406080c18103500b841000d21420071b4890780f145a251011032aaa81c008000101c60180c820507002001040410100420b200040b1902540b032401c8074060501c942e0404210b800980c03096200149242040c4100f075804070b4100d03001a007800400d5171042c100b0340003070380310740d43c61203030101c0b01b00c00020f0746502c01c0341400003081c0c8100b40403d080c0c49680d18240500301d10b26100003101c403003c1c45913640f000c1a0052040d2102095080400f24940f102a03a41422122001d0781c2c8a040c0105100c8880014000300f21020107007540ba903843c2c1002c408644103e021600f01c2c0111b9042c1401400b94001e00780a0003411462140d0031640c007540600341c4e061101c1d01400e6604901d40c2d1042400000c000d02c0b0344500100782140c = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 871024559 1250 871023309 871023353
    0x2205060a0b06130501031104120f14011a09100f091b0507030210020d02090603041112191205090307030303060503100915270506040b0f07090317040b07 67
    0x1100000c105030ba21580307440440060b01a01c0c01c0c001540310fa405200d1350181d1220b56441d1a403141c040b04407174290340c2c008582c1290806440000c0250a410407000c0081546c002d100e5020072044d980600c13a08622403c2c082c1d5450400a060b004030880110010101c15011810a68880c5050700140c98601081e24401580340000301c50503106108880c8160342642c05400c1c80d1150f10706010107540580c100f00781040e0244180111341d0b5421004601580c440c00c822060152031034144125402a040f21084a8204850354103200a07070191b650112907019000d86d1442ca6891003c1d030340741c00f0345030401d5014402c0410200804d07070154030250070764400b18119001c080d036124002c0c040e503c1411009014105503400c400a00c43c0f5a00494020341c5003c0101410450b8000c1e20030640440341d01c00d5035198014402d20052050340c04d4803a42110207603155074000d01e002c04000c1c0400d4090b1000034a100c103000c0402e1030807054007050b031700a441c1c800401039031000300b810000b41e0055858015081c80b = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 871025809 1250 871024559 871024571
    0x412030b040212100609060f05130e16090801060b1206181e100506041401020a05241005012106080d050a1d100f0201020f070c03050d05030c030f2205060a 68
    0x1724041c0090004032034841d641c042d452031004200702c0300c83c2c004100a24514044c0d40020039070020f01c00c0308038400e40c911540c0e151b40b4040180f004103899003591194169900d03010041c07007500600002c54004080344a0320f5140341c0c48a0001ca030403082000d0500078103900082c2030100000d174451800c01c0c8042a80b8201d149612035002d4030310300055502c511a885a800c000410041c07400000709401a8414010303103580f035a29440d550f0500e26180c4a41c04100d854200c0c43c10410ba000d1015900710074150780c082c1600d030409001a2101c10340c00d80022112060315418031261900e80c00140c080e01504064504047c0104400f03041a0031250942c0b0200d0442104608140308445c420508483c00804c4000c0360b0380144026102181142209401c55400300b003c82c01c000e0300781e001080143c0c80b42000c140d1044c558280242020b010818206c20003000700203202c0c01001c040260f030740001e070040342049552950400303507255000e184d014401c03006400245a0070b102c00440d19501c6240014014842d0b = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 871027059 1250 871025809 871025819
    0xb01030507051e030d0e130c0809100b0f0105133303140406020c010b09091b09040c270504051c09030503120a150e07090504020c03030412030b04021210 67
    0x800040d2043c00d601075200000c01a0070030312031000b08002441c00381030943c9502000040b0320035100350f100e00c0e00220b24041e061144007002004601c01d441e40060041040341100000940103014004000e41044070100e41880c40d4120030300c03540001c01108103101080084401030a4009540607010184400207503411203c003030003400b42c004051621070980f85980c3d900d40d00c0034002d4010740d089081c00e6681313000c070102d0b5440e84084103000380d00785002404d00010280301403e8041c00a0101401030f51414180000100c9030a134510640d81c0b015414103410107621101000c03002092a40007425003050140700074080c020400483c564102000043c200c1e01450081e07500f80303198840280305038410815024411b40066a00c0c6d0002c120160204113500d000400e44001000c5130880030704085240c040c040265001419036008000075a019410800d01e001070580705c0c0001800904609201d078807078100544a1b502c00d02803500004d00854032121000801040305600701c810b1001003c0d01e0b00c0100c3d03 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 871028309 1250 871027059 871027099
    0x30108100f060b160c0510080906091c030c0e0d0b04051605011403100e0106022406130b0f0a08010e0f0307080703181d0a05070315060e0a030b0103050705 68
    0xb00361180310400602d081050700300442214000c0b1015030741d141500340082140d988003402c4c02c4034200169a50042070810008590420001904000f01507000c03602c025802840d01d0745070400d401640c100003030008004082902e412154106895004803040c41070700c10800d00407945d070300480c02603003120009a000c20700a21090711074003501d4041030082c4108034041380c03a0401160704c92506034001c4000c035075980d6000401102a003006015800003031040ad2402500c10902505804019500c19103080100104665030b4160855251103902d0380c8403076185803201c0319000c043c4031010308150b403100c0d0b4605149000f4039041003010241e000d601000d600d1001700106a0f207195400680d140d140214a90341030320000701000056041c3c1c6900240000c1c024071b8000c14094072075210941a000c0e18001c0c01c0c400840704018414000e1528010401070142c07a042011025240a0b0601320040c107480000603503001400e900007040c2440381030001c4204140840c03184102d607420342d00c018a40b20032020203c = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 871029559 1250 871028309 871028321
    0xf060804142a120609061e07090e1e160f0203090609041503080712030e0d0c150b060d0204030c241b02060c010603030e060408190611030108100f 64
    0x1050001034518101111070545a410000800203004000b4180c900030300038200070044617000c42d02e800c950100182c401055245940c0d40700c4ca0400c140d07051600ea000503001c01403c1c0504898030b9403042c001801c110f1810700e4420200e2a000c3c03440046d1403c00d00d803000426944840c040001e01646500400d5400042540c201c0c02c0020703c16800c1810100501004002c036480c80b903040e52034071a000001c100b11b41e0080c40b400b03000301ca104014949100000d415a041d1030085e1031141c0c403e18005150381e41c041e007180034940e40000d94401100049640c000503003100000540e112000081201c0d51028550040048a00c0781240b076444956690100d083c3c00103540c2d85190500880c4056500a4498420154000d4007510b10104030b00d215004100d082c0c03c0202d0500c600d0f99500c00900502d500308207100c0200d00304a5041e4501070401400e103403141020302c114400d1100c0b003001081001044d03008034809164003041c264896949070b80080c1d56944520205401ca0f1502c441c8d0040170b54035001b00 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 871030809 1250 871029559 871029583
    0x60602010614190e0705190809031206240c0706090b071401020d02030a09032304050d051908040e0106030b090c0d0603020a17010e0703020306040305130f06080414 72
    0x100045140c21018022049503411411090b00c0d01c0c00c03c0481d14011240000d4013030740440c3d40d02503d0f40d124200a10200542d1907101d01070264010070088158000030490782580480b20f5183d41d43e403075250201e4500b10b0500d050b1050b030070f104038400a42c074040d48c0c01717048402002e80840305078603980ca4040e194000d0034091644541d008000d9140483e0800403058503002da95400107103030480740301d03074041280c100352400e50069484d03c200209155120304c1991000c091380c504500c81c0c900010304094140300e5481558003680c81c0901000600c4802d000c60703094403404090000c64a4107615009a15038820b000e259011503131013001107109071181c400c0f00380c1c44001810124481e110145000c10702e03000085076550240c0c80d0040800107803182140480207041c4202500000c0f0710140040c4d0a40e04a104410020352107030f0310400241e500014200c0c3c01c290181001ea90712000d41ca4082d1040560b504081d40da072207862000510703a540031214a2080e070254000b052010048034220380c46040c245c202c = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 871032059 1250 871030809 871030829
    0x1022209053303120403050d03050601081303020a120201050402090c070b0103230a0809010f030b100e01050c15041712070e060c1f11070c0b03130f11040606020106 72
    0x241075007400070301081002c09050560419400710b0200000d180500a91a0070300c049004071342001041002c02105089510791300707090100d850f01400007420040b000304681ca500916090aa0915000f80445411242c000002002d030014909019003e02800c0ea4200d02452240d00010880491902030b280101d0b804125141e00703929648410b5402040f250720755070701e8038084601400422041110b804064819134615464140c0c200000d0103207005102003070180350900c601c410042e503c0400c02410700c050f07410041a00780380707800100c4950180c00c005c0100d034802d001c0600600000c1d03443c240d01c6188500c0d0600c00e40341c0d402801003814000c442000f250101c1140100b0050390042c28280081100230749680e0403d2071694105143c40c0418240e02c4105003a4110f414441c6c0c0180150202e10821000252070100381d5174230781d1034561452003000354030400400803421728000596003461454020807400c1200a250800010980011302414030492038510000b4000b401030240b0320440b1401d400d = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 871033309 1250 871032059 871032091
    0x603010b040f23060d110d05040b07050405061608040f0314010b0d020108070c110607111e010807030209010e091e0f101a04090c110705040207020f0d060b030102220905 74
    0x8184403403078005007a42c500c91703a1103c4e88520001060000382c00d188401600103e1103003031030304000748005030180c165010400300300410b104984500044666121141d0614040e1103490b05190b60180129041428404c01d6440000306100c041c000010400e204280204500340016040005403d003400c4000c3c0800d2090b000583c03042c0c0181d0991100300d0003401c0480f66144c108001810b03662010400303d0781a00c404030780030102e0130581178a0709501400b8103108185400328001070614803006008ac4109500065100400e91046448581400000e80040141d00b0062590800c0510007004c1004910602e400150806900341d0464082c40011004440b180d00300040f2490074005404408800c2d03e0410000a80c1c1401d8402c84c0709003115541c8406c0040100c105450030309a007540300d24419401800020090b03520202481011581110443e07440005c610707000b005400414a41c503855440420500c401000c0f030040b0692088803000308052068441401a046540540b50320314004011b007 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 871034559 1250 871033309 871033379
    0x715170f0a0207020a031202010c030b0d08070b09030d0c03020304022404050105160b010e070f020a0503030109050a0e010507090512060f040b060307030b0106020715030e0a030e0409020603010b040f 87
    0x1070b0007484410b0000d40a60320407912503c400a58050003503e07540145e43d60201d4800380c5905100d1001680030865410000002584450626000740103001d03000740d00c00750205468200400444e0040180c0d00c01c14803003072410f0540a4000c1d081114141d001e00c1d040d01407000080c58429200014852070441581098103001c01100c10703401642c0d81045c140c0c408484000030403c1c92005500034403807490403655905c2c020310005c2c128042c00810009560007090a14009500401541d064074241100010a075035520340441c0a004a243e9440c0d01e54640018490301581c4202810b080c1c0d102690950902e1401c58409569103100310384159080c00400d0200d00000d0400d13544036013200009040713596454a0740c5072688500020f07402140527a004400c100040c0240c071500203000d4600741810011040304c0c51a060f280c008180c402000c012040416003419034956000ea42c5007900541120740f01d60310b5201c0f40180f54000d0240400c20390400301c0018151007000000000c84040340101c10441b00e500b = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 871035809 1250 871034559 871034561
    0x603061e0c040b07050109110603090d0e220b09011707091104030b0a090204181e0804090212040c0512150606210a0b01020616050f09030715170f0a 65
    0x2501c1c0c042081c40822001945554031405010700601503400028040c0c440c0c940200c2c110504601d10380100400c0c0f0400194240124104041d1030080c1000d8024807080700001d001c00c178440b01c4406554280303e100006206c80c42d80180101c06080c0d4068a407079894140943c03c2080d0707811076110680c00f040091100e400c45400a038044d0716912942400c01da204c1ea100605401c04869004696070785012160552415000340c05000d8440130001103252019201c0f000480003051795941c1c110003200b03204003040420800c4500821040f8400c43d2035803c0038448041d18002600c00b506d000080d403030040740e10b24003e03004c0c03542903c1c920010314103101c2200460400000090503035030b00101c10300c0130342038404170151018990700e40444890311a2600c1c0d8004000c8034401f021090456026404016219558840342c491007030703990400603244c0a000c9072054991040500454050090000010f00c200740221040900044d42e180c8014078260b0a035143d4401c0000c95410b03c40300e0040010400f0b501c0c03d = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 871037059 1250 871035809 871035811
    0x6051b07061d070303170708010b040620010c030e120309070509070c12092103020d140c07120c1d041707050a0c15020309090601050c250e0603061e 65
    0xb8035081e5414000444002400c00c0990352060300403440c00b403102039482c8410098950300680300d090840c959414080caa0111307010320f001d003900303000300d19000c040c9031090101d42c60003c10891000740203041d074160300103014201c2a5500502072148403110b140d5010280f05592007401000020184d1525003820040b00c050301070038002c01c0c80b18003058080030a44032021070303404055648032510986d2515068003034035400242200c00075119600420002a4040341808000c00549011840c101c1710305181d1103d849030031120401841058400140054440d1841400e54020706081d101a0b40e14090003601043c09012441412140800a40001c4254a5004030721082440003801d1114076901c40c0e14110000760306650954108900304105c2c03078040250090500c4502c00356040000b40c1011030402000a04070328144100420842c0300e0890812201c403603d00329080d01030354005002c2c502e41640400f0700400f882c5440800c0011154100082e20a0181502d4013802002c80e220503559010460 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 871038309 1250 871037059 871037081
    0x100c0b040b19020c0d0801081b100504080f1e0f060610270302030c0409030c0204090206120a020909060a03030c0209072319090b180114030403080406051b0706 70
    0x180082411031802d0301440903094100040c0001e01c03220f5400e14010300b55440583c04603869034010310743c03d402c800c40c0790406001e1346402e43c0c0600b080710a001040d22240229040b02d00d46104500307821841c2c1100045172000b050b030300c9040140d11885606d55035140c0000c200c411205034011004107456007042d813081c1148075036a10380400203a038003114410341705030a041d25101c0f00300e00640234025823509000a440c828000c8030104081074017658040c15000b0394101c00ba12a40c0e032102140159202d00c01190166403c14405000505e40889201c009400c411403081c0184032040004032141040380922055940684925000140c01d508008901c3c0c0000c003d2030030061062086020b4208031000d040c0c0030189440215240c4210074003076500c45102c40480400c10840c81010410707502e00c50122060300201e0070828070505001c82c010b95961612450265004070004100030a240c3d204454502661064005100360307100c154404c2442a0f0f0000d58100c0c52400304908800680a9841681080303 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 871039559 1250 871038309 871038331
    0xf0a0b04180b181905070e010810030812040318030b010b1605060c0a080c0924071a09060906040201051c1506050c0d0306060e04050a0b150405100c0b040b 68
    0xa20a0041411000421500f1480383c0881052000d034a080a000c428500780720f200c20402882e05200c01840008407661450500c07600c10003198142039603c00c42c001858004174516601d800328014101c202c00221800d0f00001e40c0611150803047c01d000340c4500f1a9004019184e241c0d00744282c40803140d000340c500091042021041400040e81404440c1c811100012800d131242c2075440041c06400e40100350806000f4208409400c56440e03c00c54403401c03482c014105011541e0700340a1109109e0904090611800444d054400566915009101c0d4480740c0c19a102c0b9122450b140341c1d9a401590020b0220300103020031a6080340e102c040c01c1d0740040b2110080384042210001c2d000c51012900041c4c001440001e9410380030b04200a0300f03400c1e10151800300082494144000c06030711100200d10300c129200d60200759030084540148400e1780005200c42c820282e1a444400554003a124050042c1d020303c1062a1050103001520681a04194003250350f69581d603985200c81801000340d2151 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 871040809 1250 871039559 871039571
    0xa020f070c030503210105030a08132301140a2a06021c050f0c040308030c0405190503010605030d1b140a030509150903030a032d02090f0a0b0418 64
    0x4204190341c0240114094400b5590310300d0308002002d03189507007905030741003c3d0115004000c55100042d40c5a0070540002d0390f10b8440080c4c0055001458155210005850700164200404520855000300d2032609032210701020014801ca40e915000e0401c0e000c001c14142034403520362100c900c1e01c0c0f00908661000d01c500c01c44055803550704980200000c40c110242188500c103640c880d6100c0d07207421000d0380320740300303203910781a40e10b4020b82c81903000080040c02c020022901006800c0c1c1518040c142c02032130300c0444074030048030b054111a248070340e80c070079801d0040c0081c3c42d040219101309064240e9880c401200449011881c0441c40445c0860311078000390010400d200c01401a0404584a559400d40e900c0303800381040020000909040f0003e02c0030050341642d60b070000b0403515600042d05002c60441485669855281c80b9441d10745018510030307801c4044604154002c024401c2c0889220026000c00360a00c1044001802030b1114100100810700c250003a664801e0316101440b40c0110350 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 871042059 1250 871040809 871040813
    0x80a020913060e01050901080d030207030c02120c03070f36090b0f01050402040605090f01020a0b0705040911030903041703090604030609140a0b01050f1908032a03030a020f07 77
    0x20408040e504000e02659100d0601a407500f16038000d00400089425890950400300c20700e48601c0000034580605500103100c00802d0f00440d0380300000c030b8004102c240828102d102468460240000d294460301030924040f440134000345510054910303468095982e0001c2034550380f02151038070300b241d01e44c1c0b0300c40e1590881201c281c0140c5080320320564614000c2e003013410649034400c2040c1c200511440c01400203001e00ca9004040d188140d80807200d192040312070000503800c21310f2481018115100000400c220141c02100a02c1181c10341c2ca010845503036510596855804103a40900c66038008000801600d200c425450900c5c1094070203491401081d100000c243d64003030742c81181c1c010303120411403092012056403405043c000d000030b41000303c1c03281e0b544030b070094050203000e2055519a0003c4030985411003a80d220b050300c1d182c003040c501d880300038003680c0780c0082074840c1c20301c55034142a6008019100c189000c040141c8011400d42d252050180043d405c03040c001c0d00c02d01c40c02c1c014800 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 871043165 1106 871042059 871042069
    0x120218040201120f0b041103150406080d110f1903030c1b0803090c06070809030609070806010b0d1e0c2705040911062106040608030a080a0209 63
    0xb1444c0c03c229035040240010085240c1103481d01001c2c0c070040e4000c4004600816500380c00a4602c00080c2c2040256803083c006d591a58011850354100d80d4040e401041031070401c0d400703407601c0d08001c100071031801ca68084140c0d03001042401c09418590103114185240c81985880f0701440c612140c14408811450002800ba02c4000005030f24203600b4403910f024080001c0400740e03141020b00340310525802c2800f0081c4a4041d50000c91007002d00010039900b12903603503024040503882c0010740140354010b48400b91519444d00f103290004c0c80c41c460040c00f1982ca4800c00106a8010b03d4010541e0f02c07400d8038514501e44a045a170841c0c0c500ca24440100d480c02c54020882c0c010500c1c10355070050245030020303000360b008a2100002c030584207010086d642c2d02c00c0c0b00300440c2e44200802040d15410302c14484150001c20400c0030052099103000d9000c80e49410141c42c140e507500c0421 = true := by decide +kernel

theorem cover : BRFrame.Cov 870863309 871043165 := by
  have h0 := BRFrame.cov_init 870863309
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 870863309 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 870863309 ≤ n) (h2 : n < 871043165) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
