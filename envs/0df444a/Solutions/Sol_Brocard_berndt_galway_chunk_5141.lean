-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_5141
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T14:53:15.579867+00:00
-- url     : https://prove2.me/submissions/63ff57d0-f495-4b4d-807b-08adbc3db016

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 924460431 ≤ n < 924640287 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 924461681 1250 924460431 924460477
    0x12090a1202120105070305070f0c05060c0f0403080c03030f0903160b041401020c0d11010c051b1c0503040510050c030619210c060513140d060908130b090105 69
    0x7502c0440710301c280c000020002440c001c440540a031004a64250002c2c0c0311303104030040280120080440960484005c011030b555500400b03445034800d59203013882071014400080020f40d600000d03c1e07810307010805580c81c1d0815200c10088490090031001c500d410074000100702900c2001981846600032415850340d85443c02d11a0b200f0b02c04030b05010311940000350790041400000b0b40c1850090459503001c41160005031803900302e402c15100c40d00003034070400501c2c504210880002100b0010036040d245010505400d20100d240002e590341e0110b14040104030a000e0140320030221032030380c10810301440c503060300c502d02d440c0320007400d8030b102e500321030b9a07220400983c60b5040003601006018455100c107111450301964a4181d0841e12038040620109515210341e096039606030481002008060501e02d184113008005542036401049210f00e001c08075a80d4015012000c0c007480300303141c1e54140c0c0c01540340303590703050340090401a2040210481d030382d07408400c5488643c0451601c2d1114082 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 924462931 1250 924461681 924461689
    0x80a050702040c0f0e010518010302030a0f0203090d080a0c050a08071e17011e121b06030203010e1006080606090f0307171006030206070f150e01020a0212090a1202 72
    0x1403150180d081490300045500741c50b0801101c1c48038881e1900d036103014074006401142c07207102c1c17a01150f4620340582a00b0001d94000c5d000b542d0011229000498143c119114074030403604126040c0d1580d501031000a1101504113403282e400403804607060101e4422141d0241c02c0f44120200d95003003091140c00515240e1003880c0340718400200349030400d0303450304025008043e14685e60510070201c0044c00001070060110f480105003500f4400282141850031624842d150400601902d180c0d2407031003001c05286000da0140040c00702520010703200d50411020808020300100b6208911000c0c220500490342c11800c8958464021500715a40304209400709070241400b01100e509481040004600c02d410309000b10320344071500c02110b150021801c102e10039600d0074403010750410010841400407482c2c19032192201401400d00202c5042d40900038030480f841c00b100e41609942c0814405125035051100003820000f840b9041d042400d494006441602203115040303440858003090401c54507 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 924464181 1250 924462931 924462937
    0x11090a0e0a05030d1d0601142107030606091a120a080409090209070207030305040e0c09030d0909061203092102061902060f011508061c0c0e07110a080a05 68
    0x21880107840031000240b0380550b50b6000741c048501c1c12410003104680a500465000d4501110f550007404d440c0d01c0c0c00014100b022081004035042007100c6203a900d0503491142c4101884060f40041403024a503081c694201c68258000e1240c450425041460b140c0b1044454440118111090700340f50b1000d90f149460300c02e00d00c0f0300038590800031074005080300301a4809013120740244d64840140d59642d00880c0c484000d80402008104244030600c08904400c103059407109034031072030514003044000024a0140c00d00d10f5400040c0548405101c90161030003802d00408060700000c102c01c0c49990042e10200c12070190005a0000e500d000d8600e008180e110084075801404250b914040c96901c00032110445007150050321680c80411a4640c40144107030407511b04028013500950010011078030084060010340d4001002c042500184401044400600d23101d048004400d901c0d00c0d42c41c210100005182e041807204a00c00c130005003274049541400540c1c030101d070319915510350780240c603140 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 924465431 1250 924464181 924464201
    0x705090c03042f0315100f031a072a051c12150e1905010b0405060a0806030106050913031704050a0312020d230a0504080a031802030102070804170a11090a 68
    0x80300e403801000c850100885000e016688006d1104100c0b80c8a82c81012401280c0c440182050080943d400e10450350b400941c5e0004940c0c50150540d07040d500c9000c20915000e0f001004c030800c0780030020700300b00b010030119048040741d07502d441400e050540c0c00b6108907014400f03480050340301d038101400301511185100c05003440c40305101c0c007070a29882035000b24840154103034582c3e19043c000300d5104140030503074048440041911f842c00300c10034000c842400303014054582542d01c03100c1c049034503a180c5451521070b40049003800d10a8040741002080191038484480046003003000380004204045000401d29405082c055500074004041e01d0003803103514040d80319507280c588140c04040203040c00c0e40c070380c002c0ca9210105544540b42410b0454000703842c0140007540c204149844a80290802c62516444c88040d0b4145046e94001c00d09a9000f44400c843c0341c01c0015080c0b28040c2040c481141c20001880109100344455450b02072604210701220710a03601c40d00007034503180e41c42d04440949 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 924466681 1250 924465431 924465433
    0x806130912020d091d01090b03101406011b1e0c0b180f010314062103070b01050a0e13170906071407120c051002031b0705090c03042f03 60
    0x2039110340c0003500c0f80d1841c0160300c009080c10a0001d903c180300d40888981540c1903114412991a00701000300030580d80c203603183c160045958155a650b002e1250043d07090440900303800d2850804001440341500d5203074000030812103107103500031400380e0200f1f8034805001c2c0324030150046d40f401c0c2980140700651080d009520b00045120159554202c1070001007000c1e00c442c0c0048600c0c00041d41903032400001c602c4100f1069000860901d8408640905d50f2000e5854500007011251643d055511101c4180e0703201410000420850070440c801c04010092030440c2d0641e0b040103114514130a600c0c40000e407880d407242c13240c001c020181c40c085648034540100420365031540e91500050312490b00c5290b60660080c61740000302160807114001a240e4480503c8000d5030070308040102c40104040a01d01314403050144048410b8611000f1b069401c030a40100315207440d01c01003145004c40107204080644052080c0b1000030b910f00e2a2009170002020740380f009550040b16032851840140c207450389 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 924467931 1250 924466681 924466703
    0x70b0601020106030b070e010f080c1815130521030f070501110c010f0f020c0c040e03130e190c0e0904050f03030106030614030706020712030c08041412070608061309 73
    0x14071504441e11080c0d403142030b25014864555103000341d559890440d5244401e490070002c406c00ccc07016a094000e04107900401c4a840c03800c4051090900e07400c071800b09424001003144c203015a2410b005a045002d00d0f15500c5007002c0221030905480703020780d80d00080500c80105441c01040307002e4012448103401c4045550f07c50102d1401140a483c200c0300c034901031490150f040110110500031209813a18440060030b5425441040c00000e1805e07281c140d5441c0818807114a00b80e4201568200920f964820f5441a0412101c80c4203190540c01c01d002d10b003882c00b04103640b825085204203000072411508100b081d0703200d091031360404400c0c0d1003c0e11907000001c004600c0c1c1d50158008002d90740303503035414142a28040c1c10f050341c54126004040160340060300400070b14802c400745e654035030310a1404005220503a82d85a40c00d42060b0403c4501040300d101c61410303403c001031040034009031003000b4000149041000b41071340310060801c0d80601c0c1055009011400b454200150341a402404005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 924469181 1250 924467931 924467941
    0x1110c0d0c1104050a0212070306060207050d03020106150201021902150103060902040b090a0507090f0503060f0c041502071a070f060e03070203030304050105060901080601081002072d0c08070308070b0601020106030b 95
    0x4000d43c0811040382208021f0008154401d100303114040548000d03800a2440034142410000e16011345801142190b403120000305580c5401144440c400400e82c001688400743c3c2440704d100e809640e1840c078219800000d2500c2d04e40703595078106d4112600040e00150354401400401c0145c082d0101030350300030320404280700d110405540002c1c4143c08540d00d10000985802024500c0391503440b8543d03066220601180d02c0ea480210f07103a03000252001c10fa4607141c4c0d507003c4c1160f503160390110800541c000c46010031014644a801d58403410002c02890302c0c0c02003698030b0300351036006044041c10b070990300d0300407545a03038040003101c80c51074008003266201e00e482d107880740c00307000d00b204c12a02800038000000380c00000040c125050302c9526005c2d0030700316094241c1c10020741100100741c030b6407140300d080214440f491100140000b01024800c2071201094240754a60360034030342c000c840320f501405040003c0780c420826115400c0d4400911811501c0d41c8004034003611150b00b0180c400702c24401440 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 924470431 1250 924469181 924469201
    0xd0b04140c0d02060702060a020106030213060e0a0507020d0806060d11091206161116080d020c06090604050f041d030c0c0102210d140106030e01110c0d0c110405 71
    0x1044410490100d48448440e90140300024514070b0b002034108406110f00001803030700d1006020020b9141c400013810b20b039250001242400508103104003a03684000c107000e001015017007903921629858060103d8140751400035668249000c000040028807804100700395034480171202032824200050102440082d4424050b40c04032074800e108056010500c02945800b080442c481c02140c10706d054400b003607000a40d8415a900b8981d02c060103142d80e0052510b07640f034869006800d609000302080b54500001910f800500380282d48680d105018100040e500c00b01260142c1d0019100309281c84001303404a03000d8081c2c0000307005012840952107602d550000050488488802e048400c2004a4401a612038181860003034590750103403005412240c03500010401a11106400600350034a2850740502d1002170b040500026100c0000180c5001c09000d0242d15801d4984070a103814000c1002d143e54080c18206c04007444206914103051102a500320000050b0140c024003041c078040c0000 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 924471681 1250 924470431 924470453
    0x3052101080304082107020907090b030c090f031f0b0a0807080a1a0606040e04020105070f26030903030612070b0403030e0103290603100909080706060e0f01030602090d0b04 76
    0x3013903840c400c000d0380800000012000004c00c3c1050381d550743c6008102d4080c0710201000804000c04c1c415030f09000035280c5100c2d03000394420700c054190a42c84d0f440140400a003a0b01200c0c14610903402113003442c1c2e844290a448141014200d01c00141c17440d0000c0114a07a03031602d07804200300c0d0040c80d800050482011406007107141c4284000c0c0b18144c5002ca030b46a02c207801b0750320a0f801100a100c20301108038001440307a0001d005040041c2000031954505600c007550500444da1500d943c4400e00403245007505080910310041c952608500c0e02c81012566804010700c2c01d03101c1c0044500f08008500103000560180c5040440203a6030303516400d011340080100b01d40a80003e180c2303120507034450501140d5006105400100f5840b400ccd0380e008119140e0030107447c03046030913514080010199454440c2019051050130071544a242908060b0308480f00c03980b09103488040d000c1006103860600713114506603079000c0c00060311800320308045120036081020080c1211610014002848861844 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 924472931 1250 924471681 924471689
    0x902090906040b070f0c17280f1115040f02030a0302010209010206070c0503090f19080105011d01050a0b030405120f090a230402030a0207020603011e050307060c03052101080304 78
    0x14a240c0c1392038100048070900f10f4000b2040004240340c400c100060841d8403000440c01000034114100142800d1101000c007040901d101008035804c41c0d080c01540082d180001942d2504000100340c42c3d103140c8503101c0c100c5205650181142030300003820850100003c0c00c2d4103070060112200c00c001c1d454007034002d5000646030b60140c4200400180994405c0704424090340c0d01401540c14500300f48180080e8001e25802c00c0e60110848140d0014950061080c0f0024145070001141701c3d40740c4400316004154401404180100c224010f100c00d85904105034201d03558404100e94a07503c60524608102c41744001882d40c2000094907521440d41c0c4000e4005c03820304540c00308034199140480300107012421514030800c82106400d040c11300d00769000c1c5030711844840e4054a031a40d01d0740081d8a0b03620903000700c440445c4002c072a407580c103641c050749000780c802a401030039541c0c1010406401c410391000020208413001491514003202180500b0015140044504155071a808802e881340c0207805 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 924474181 1250 924472931 924472943
    0xb1009111b07030201140a120f09020406091404081b03040906030b240f130e150a0507050d3810051303030f09080312010e16080703020c01090209090604 67
    0x50000099400301d02c0340b04076075058550444c100c09202c120000d5030011540e610900c42e071202c2400c0061241e000d9550300025048000175408454810030041725415002801840d180101d0403114100b2428802d40294100f40c001ea242d822180c3e41803c505c0000c22444041c0c007020a00040c0308030b080c2c000300f05903031283e14821816a0761480460700340c490000d0155807440241c8401240b41070000415041031409480c10b0b00070b042250f55481500c5c140070003020305900c50038149800c100121060341e003040382001e0074007103801c1c000c90082041c041e2190b441d05983c0c1d034018068003003414003140e51640c030030f41c5404070351240300240602803154047d0015000700161904010003a100350212020401c400401201c49400c1d514115940320840a00d00706020741c2580101d101c000c20400b40001e68102080081ca1350f0504c0d0042c00d480c180030b0090700d24480b0106041040740d0700000a81d030b10090fa0720300140c031748030142041405046a04ea0103908200c80703000b48400504041401071003540100703 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 924475431 1250 924474181 924474217
    0x3060a0f0801060e0f044e0206060105070809090705190804060b0a031e08040e09010b031209031b0a053c0a031203022a0d0207060c0b100911 62
    0x117240300e010034101c400031f04401e21503214000c481d542c0200c007104100100702030441801840b09103000d0f01c4010302a54000841c0d00c1e002d4180c0399040100c00c0e4000401e10b01141006466035aa00b0180a00a00d4510402c103010000d000e5500c50410f40b010000008001551a610900050308003030b4156401d8911906005d0f1150407814141c0946048a80c0501440807491007150320482c0408031001c11075040d42c00b0031000804c2c046000029005400700000003070f800000408140c9401c0008040b9120017500384902c0301a95000b04101001c1080b00c224090f6001882000403003940441d00281d52151250240341e00103503180700078a603c1c1c0c2400f480200140030a100f100004c91212041c550300410b03240e02440001e00020300100c8d040b40609000d800e000190000e440d0003100401d0180e2118245c0d1441c0d115040208641c054480381130000e80480c500700307035000305000803081d00604003c9034000400d800d400244170031002000000000c0201840d0366520a80950203c001402c00a0400d = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 924476681 1250 924475431 924475441
    0x2101110a0e09060a1511120403141507080f0a0e1605041d070320150304020405180c040903051c060320030309010c051606021c020303091203060a0f0801060e 69
    0x40600131040d90080c1180b030365001c0c3c0580007201c0c0401d1142040750140140751555211744c006a003d04003640c80340c0b840350010002d0780c00c840c2c501416200704001d00b422032824061182c0d04006010b800c04a55148005c0b0395580c15915005448000401c401e9880f69004c0e040d000c2c3d440304191015a42c00f2903081c40441d070321311848114414031042041607034000f40c1d010070000e030f00100b12001580007503c600714400a11800203840403040707a580c9650200000821045141a2140c0d540c4a109003018071440e160010b20541c0d609907140d010703030160307582e100f400e02454007445c282c9500010010000e8000b2105240032000707400342d440102e07404141c592044003503da120303075007001c405005401541000014401190244e28285056070540140d0380b0b0145c0d00c04003104084041c00c4507030000c103100c144130b84080c008031124416140441d003041c424420308460100703191610300a840c440c00e0b05c07070712564005008040d081c0c7c401840340184c0100050b601c141900003104850030f04002d003400d5911 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 924477931 1250 924476681 924476689
    0xc030c021801292a1f110711011101020c07080d030b060f07061806090605040b0703230c0405090405010c0f03060b0904050406180605060306152101110a0e0906 70
    0x18280a503d0041002c0c08506007a10483c42c3c80c0c0c3c440c1030aa880c895415080c0c660742424249884541c6000c080060072a01c0c0d0a42c4500548120403540c41000f072402c0420744a200b500c00244400381d0421200391a004a001400d40548040d40c0400382030780d00450766003400950352448081c1c2000441d0400c4204c07003084c81c00034142c48130118400f0301c544c90907020350750329402405c18142900c0d0804500c00d000020070700c98411034405a11410000400713003800d0901c0011181d00500d4402018146188010000c012402118a6400d601c40640c142c0d00e640306e904202d40207607000903400c030403401301300300c180407054101003170f041c1c45920788984d142d090031400c405580c070074000d422112800f0002c03501b440c10a81d000c140d101e405031100007080103903012003602c03403400c4140c02e0303e100f500c602c1404020301d8140311803074020701c028903000c2c0040020000b01310f50815107400d03230300a034600401c0f207800c0a50a40000e8500b1100381076456803030313100344e40280c104103d50a005000b1000745001418a0034 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 924479181 1250 924477931 924477989
    0x311040611061008190206040f090c030b0a0f060e03030702040e100614010818010609020a170c03060f01110106030c06111006180f06030807141002030402100c030c021801 75
    0x8004805131031310f200d042d17a9410b60007005c44c13812a00304800b0070000900c0d40c100c02720304004d4a40c1000200d8130740b00d0800020700390fa0800c02941d115004400d0100801c0c2c0844410100725402030801c4c07041111128002800c40c0a0030f90041e40240c01c1810b01504400d0214840c140c0c20300c10b6004101d034644609465001c080001d10003404210418085212459000c11a075000490a070000c50155107c0b8006c1381640c120040520214a540c001c0c0002910300680c8281d00c01342032880c0c3c80c1907240450004400f140e0b105009410300040f851410b00200080d0450009180c110425290a5582d120000e00704003d000501a03180144104141484240d01070003046901081030320000307000a280700c1005203100c440c80305146d582c0710400030016400001829200b40226118020703480110340803414032000040e003080c03c1d80b04008010059403698044071511071240380803140c1824500e02542c2c580d51255010350f010343c0c2e0b84607001090038074134125416a0041036152010380180801414110 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 924480431 1250 924479181 924479189
    0x150303110106030f170712020c0a0611030301030303050907082a0904020a06030e0304050405161707050715140f0702010606140304110d080705010b040c1110050703110406110610 78
    0x1a200e001c4c00041154000841c0124106402c00b614140a60769510b040d0a007080354200542c1080820151500d4005558402491541404040005c3c8441e20540301d10050100405041c0d86c0c1b008200000410400d03507000c2d00c0c210046540b410010740b00c0c950302c00d0340f0014802001c00001082c080c41e00b840c103c15400745501809802d0700f00d00307040c5c2c2600a802208440182c07888180000542c03a5541c4c0a15802403d802c06405103070701500394018480000c940307955624481030320a20904c558450112043c190b00034207101c81d080c1c0c52208038005400301110044108040b5014000380d0010310b0719080c01481113030002c01003a5503d00054a100e21107a021301010b070f00a000180101e408215007940301c90740100100390800556852a03196080108141c880c0ea54411244060381068407802c0a29802402c0a04600d198903040a0345c03484800341c3c02540036151000700f00b5890281d04140740e60703040281d14603102d6840388001000315400320130a1403e4441c010124010344c0d02191880251 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 924481681 1250 924480431 924480443
    0x303031a10020a021003020c0111130b0307020d0c0309120813150e0103020c0a210e0316350d020601241d1806030c0a050604121515030311010603 64
    0x3d54040e000c020014140300c1050080c182c0070000484c481100307210782d03561408108031160300c0381c407800c048100c2e00309503800c11401000100203121690740c001070007100d500c406141006801e44030b403800b1203c0c444e10f03500503050301d0b403044841d004001c5c0320005000c103480c4120324904d00c6a41d0740c0381c0303c524001d111708600120f440300802d805036510a400400341c2010744070071108500000e50342d102e00d103c8505454071000301078404140c600b6501c80c081c641c88003011802016881805032602c200b50303526201e44000003103a01c4050b002143c0e144480107582042400c0d560000703507807210454950300c55a07544401401203030008075080090074030a000d0a807041d034240402c0d040c0d400007074404400010488841454007084148251b0300d0400600c4464914244e0700114103160046c1442c01900c0c0c95243d01c5001d00b110309002030707280d09003680d084405480303510700c2100a5042c00c401030744a201240112a041c151380c3c601716450b01d254541240d10a54555110520f820075079401c85a09020061034 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 924482931 1250 924481681 924481693
    0x50c040815010b03010b0c031b030307121b05211603061d04020607030c08031306060501052b0b120102090315040507140f06030403090e0c04081207050f06010303031a1002 75
    0x1542005501509429000102301d80c5800c03969607a41481c0301e41503909006e180c1c400020064903540c00a150508528502c40038000c1100000c3d41402c240b40078400c59081103004603031501c418182418100b8200b105011040e003c0c285450503000c241d5883c50980d000c0b90070240002103002c008852030400602c030400d204081d80b00c0380c0c01c000c21640070140907030400280c00804400709000c0300056008560040d440310315446d861038041c1c25075046621403818401e00b4860400d00c08525400030200c20156040c10302a10200e0410000401c0b03201d19440c0c204a64250044400c0c0f0158000c021140301281150b182d941126000d49920300300b1075004049800000d001c01c2003144d01c240d030307911145005010f400d00018400c086201c5400c1145e0580002d601c415082000c055482c200c02c2d0002c10001500c0d282a003800051603503030224200c8101803c5001441000b0300005008440c51000c400f002d4510742d594a0034000c015101e00d035441c910002004486032020b24040803100e0074807000b90050a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 924484181 1250 924482931 924482939
    0x9130b0c0c19170d0204031707021f200102030f010e060312030403050403060504110420040e09070305010501170615151804020d1e0608121c050c040815010b0301 71
    0x400b441c0c56800c21681c82400b04610460b0151032070160502d005040801600c882c51410f01200114400c045242900c004203d60405a10303010040b992140d00403008038002c62400c88201c440c5071401c00d04e200342025401202c101c0c81e80640085015113040e5440701d1159895070203281002e10283e4020f641503020700320700030391580c80703401840c1c2c4540641082810030307669896034400d0322411101165a00541411803610b407400d44584010009110098000300313280b076030350101b248140d008502e12480704000244241c0e0040142c00007559000c1e0080c05556560f403030701a41002c0c00540302c1210f01032040042c0c0d01c03103250b002d40c0300301c0034009104c4428014169000580da521003920700200c1480c00848025a803501d0000303141200408100091b2148030403054601002c000c444c2c10b038080e00300f1800700000d1000003501d00103500d81e104100c0e5a0409080d0bc1d882c41e4403c3d04078005140c1c01c0204001a0505400181040f103500c10142c5072141e4014109940c0c3c02c50901994060020900040c0 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 924485431 1250 924484181 924484213
    0x4120201080f060321190f0201050f0c0d020c0a0f0c050a08030c031206040e0d050903010612110108061c0501051506070c1404020c0111041e030309030f02010e09130b0c0c 75
    0x100c0b032600c00d0710b0b0280080d006c0c3e450315610300d01c101c0407031a1030400c0c102c0150309206039580096403004010182c2064503141940b0f00c10400e40408181e000300c0c5a5041d400305200a03107950303034892116501d000c03942c548003c60008611403144030384011203000410600100855108002d00d4010b186011458548130030510340140c502e0307420030741d1404d00d500400400c00c007c550340606a101e21352150001d000301f5080d0340044d00700c400c1c446244009400000d02c004e1000310f01003000d080c80101980c84c02c0208402ca4040304640344550648403452041c454194402801181a401c400815241cac80d8140003ca1055280040c00d618000e4800c20415040300124040c200303000f0f10141c80c0008840d5403d0075516189a0b2544d007000003e0200301c0c1c45055204008564520340c0c61400c00340c50354501070603410307131840060401d4025809003806c40e0b2086034400040000108180c030706e42480b441303550a0005c03081c811940d9a807410081420080c000c429078503a081880010030152204620341 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 924486681 1250 924485431 924485473
    0xd0206011809060b0907020a060b06090312030a11160201020c06070809091009020d0b100c050a06020f071502070312060819050304090e0d030b04112205040204120201080f0603 77
    0x3d55440c4c2d50f602e030110740359807428805402480c06500422440403d81408011240348011243c4148020000c800031918085004031152441000060f101da80740881c980242040c180100704984001500c66480701c030140705550141d000380c1c200c1d21041c03240c4d41400804d10458001500800c401c0c045150755292010140350710946101d45620a035135900060010b980080d110500c0e40381e01c8116005a0b400d0044500e0340000340d030f00e0310b42d10584e0303941c40700ba8aa80c03054402402268001615203200d0710f210080320442503104a07102842c8100c0d400355802500444002c80010b80790320048130381013a0380e018000640b264007014048000f8011011a11460604070450f00750009000008521249226890319080c1240141c40320900700000241120782c42c1c100644610b282c441e12000c8900d0b4036003a54107a00c5020511590701002d5031002040c480782e58041e42d0f006000150200702c44005144003030246100780c8800100c0d4079846904400e22108072000340e0198461a01d0a075100464070030 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 924487931 1250 924486681 924486683
    0x120609020111011d150105010c080310050604060f1214070f030f06080c03210d0c120c02010b040b04090b130807062a110d0e030106050a030f050d0206011809 69
    0x600e14500b107410382400d43d50b41c64a400d229241403640f10420b00c01c01e0000c035001000d00381c200d0080d50706281c0080c0820500182c00780a255001c00000c0701144984031050103001d0040840e9181c5a541c500103000c1800c0d408480000b41ca21001c540d540503160284075a41d00c22500c0d1440c0f142e03201401118179135801c1c0504c4041640310503460380c0e50000d9104040190801c071019040441080e014586002c0e4500d5000c44803988604802035078008000954401e40081c0102007a4014031441c115440301c80c150400341124604610300c0d56064055009110056080c1d805201d4084420100001c581e25a000903001c4c80c01d43d400224a00c4c8000c0f983d1146038850307180503007814141d4480c60102c42c0c4140b40410361080d500d15034507111824144071030101c1c0d014a0040940c1100d11143c90300d90705030380030703400030302254040d060400c0c1c1c3c080d00118043c00002d812250825600c3c00d08140e442c043e400151007502400b010410b00c60710104143c0d044e955100d0f0410001d06040d0342c21002848017101c = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 924489181 1250 924487931 924487937
    0xa0305031012080408060117101a030f0c010f0c020a0b032802030702061302180603010e01020c1c02030403120804020f060406390f0602160812060a1206090201 70
    0x5030110b103120b80403042c6810300b030040541d103440350706044525242200680140880040d400710800808400148203181000250008181300e024629110341e11558424030035850300403492141588000002d083c0d81c0320340240d0b100c0442461040c020742c0d4004102c94003030342042d004181444070341000380c01190080e00a076511280b11201d18007650541c000360342a810050740010a000d20582d0411010b40c2240309070745540b140b03041a0380082d10f458422282445c0009002000440717540e0b007980700150164401000355a521860948541c440c00c10612041000f0140c1e00c072583d5072403002050350152580010304c0c50f03a40001842c19142008010300803a40700c92105001b00310780e110305018000405440e1616105900130415800340c6894404614801042030001506040e03a4001f4003d00c090b045010f98a242e10a8245a00a84a00d081c412150004940d42c0e90070010410020304d640490049401c0e0152281c9040280354002489010a808181c516010115036030ba4415009244141 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 924490431 1250 924489181 924489211
    0xb01080c192d0c0506011409060d1502131a0a021509160311040e010507050f09011206271a01030f0b31020f030f0721050403030c030e0a030503 63
    0x55000b00501c80d18603201070018409603140300412004100e00360141c0000d011410a60394800e01003124400001c141e070b03100c0d0040107256400c0c800d10811105004041440541d542da9160925507040c3c003681c03040800c00e41545801c12120081c00301035507894545035000d0f000607148003211034040d042c058201001c0f4040c2c0b1000303841c004901f1000900441c412999440085011070400c0708071600907480500709e906110410100c0c070303448002ca80c80f81e01d0381042e060310f45181200480b0001614514564020300c3c110000c00c0b00001408000c600e94645c0301d12815004c2101300c41e0f0291507004582c1071100401d88011841c9602942001c81112603034400001c6100e40540041c440d5140030b008242c6070000702104910019016000d03e0003280400e5003540380c0000041c0c03c90003031100901c1c0b01c04150515010820003442010401d031030344c981c110001c07a500000000d90340201800d82d0200c2c0400e00c0c01c0c1c1c103103114038043d00401c8214600c1c2c1002d0141c01e038003034600355910b900007810340700005800 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 924491681 1250 924490431 924490487
    0xc0206040f08010b040e03070f12090504050a020405090726060d0b0a050a0c03020a02060a02210708090d1d09090138040513061a130b01080c19 63
    0x384208500600b0148004140c1c10b00041c14003003143c0c544540f41880f90403c102a43c003159182c10100f07483c42e4400207121800c079548200b203800c150103400940e8000d007401c042c001031740742c55000381098070340c22210041c840e00d40c1201036030202600f580d00d03445d43d000b0b03105900c0031043e003041e01580000094003c01e500d6405540701042c140e000c8034007150381c0d43d480007440f070541111320610748a00401c0c103085180c081ea6041c0070750303901c1300284501400c94000403030b01060010a85283c00d414071000d158111400e140c1c002510f404401c40c2c0005440c8214010f01d2907581c49410b90803085c000505203201c1400d4420b05000308094020f1001807959255960f08070300526284802403644c0c0600c46101c00320000154420b0341910500d0110f200e141071809110000100005504881c1c0c0e02201c0010101d120503802d40e0041d483c0c03400c80364421b44190405400d41c4098201c404013420990315100e89507a00c4510700c0d0300740540c000821004106124442120703004110760898850702c039109880740142 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 924492931 1250 924491681 924491699
    0xb19090204050f04050c031b040213030605101403060721090b090a02010207091b120b0402070602040e0601020a050309011d030a141504170d23071713030c020604 71
    0x429550308000d6400700c004c000034130609100340200010100c2c00f8094852120078841f040034082113520f0b21455000488080c103140901003880155800401400580f0b4064050360f48080d1034440c0302c400c5036000801c01c48510700424236070b01c164104c0e21122003500c03006040140c610842890360801a5950303800802241c1542c100f10321407090a030052801200d40c0c03000900706100d0344e0140c0d074400d08141c001d500d025220794250480040f546010208440011552070141200411180c0c00620000742c10091100a80092041d9401c02ca60002961149c1f401242d94801d8071300c0142c10703900103200c030900c03640c840c80e0401601d004400ca000d4070710516800090238036500d481c003100c8000d01c0d00100780424500b803141e5004080c49060100803031a250300c1d007031100c4c20010ba50240e90440081d4114950740f03103510007400400c1c20001c030480d0454030001000748440c25903106000c90681000180e4911050390000c0c40780d40f00d04008011070083c2da90a841048882000306d0707000c00140404290620 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 924494181 1250 924492931 924492941
    0x18030b07120f0204061b0506040308191107060b030307020a091509020c030703030e0d021c1101150801062315120c0301090c050f2236090b19090204 65
    0x303101c0d0401a69907141540c081c003094401c60146c10f20003c00404400810400700e442c9a20540500340802c440d62015010303070610344006002d840e50391415218040140c0c05101401240344a40c904210100d041020117035030f070181c0d041c0250b002408840a000701080c0350080541c10b030080c000503070015101c1d84280240d17080400c41c14038a91000c15040c042c036616001382a010510000600360040842b0f80003500d504600000b8404010300300c0c440114188079022031204000b445000708103410000b45400d807006214881c1008560030850f0211700c070985042070025a2418403031840c1c09800101c180462a02c244034071402000341442030105000c114819680701d40c0304807400607500c0d81045064003c036080003d0702c01c00c103c1c0510800030340400010840e90201944581204031f804c25207032643c2c001100742c100208114140384da01452020b01d460240c1c12000c003c01c101050701a40c500441201c1c00003101a03c030301003030b00114800b03c4128040c0d403001216150086041c4445e0b0300440c00340c0f5 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 924495431 1250 924494181 924494201
    0x2160e060d0302101e150320062803050703021812420c030f09120d091709010c0b130b13120c0b070e060c06012418030b0712 55
    0x2600010001da45009280f02e42082d500050146c101e51a0854443c0c03404c200d0300070094501c071802aa0400300959030f9100350b4a4400300e50800303900b1610800d03521464990754500710000b2030709200c0401c0c0010301a0003605d180d01030140d08801558521b03020000b03c0343d04800029a01c3c080d8a01c04440c44c02c0c1e8100c2c00503080c40c007034000151041d01d1305041c00c11000046031225918180e8003846100c004202c1203e4024140f80c0105000381c81d5500c0080c100b462458000b00307103240000760581440c06c0b64011810090041c1e041000c1c05817691000401c900c610900c1c030340000e0402d07102da0009200b01030100d401c040d040c1560308119040c0da503605102d0100742e03031041d900710000c1180c0c8100a1001e100b40000c01041c5490700407050310740d907030803c01400138000344144003880202c0303030003a1202d806171a0460100011105d1550b511030351030900300601c01454048100078503074003002e03900034851070f10031000e0030405c02900d5145455410b58601c001d40b00d03208114103414031340420081d6028444c255 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 924496681 1250 924495431 924495461
    0x11010b1f09150804120c031b02060c0a03020c0414040b060409150905010212060f150c0c0d0b0702060f0f04060c111f0c09032001030b06030703050702160e060d030210 73
    0x81e007880d08000c10469102d0200170100217440300b46100207580450504000a000240c2c044407100603c0000e03442d0082e4901222648140e1a6003000d06600181c6204022402e071401c001101320100700c40c00c11b80c02254094417490fa1040070800340e0030a94081500c1070301400040c83d0350710422201a080c1c070a0504140d4107a9000315001071034840c81103510745c004008903060380c02c84140b035010039000404070f07000e950160004694180401024002c8282078580100300d040c901c41d1900c0c003014850026905440184160b000007202d03c0103503030b800380c000c068010011090340d54a54507040a440440909001c00c03030400e180c42c108060821141282003641072284403a00d0140d041c42003181e9194242d07a0802c070300104100041001c46401181c0c10b04032503590280c030400140140c0107801000f0b001d9030801000030412842641c141d004a02076416070382581c000c46030182c01201c109606002d514035203618200400c20318642030421082182c460f0040d01c0c1030151203102c80088810a110344901 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 924497931 1250 924496681 924496697
    0x5070f030203070f0e070c02032419020301240e100206250e0d060b1206010609060503060a21021203040512010c17130203010603080a11010b1f0915 65
    0x114030b000d01620001e082c000f180d00070085e14000003000000c00140443c014040c0705a266419074400b84007846103260001c00b540d0a48444104464501d8011615500005103407110a070048404d80210b90495040e41d8106801c18500380108402541c10a602c0b02403100e420254945034071501b949400401c2039801500c0c1e64030700700030401607003803038031008126401482c0102d6911940050440172042d0f81070326640086880343c500803000b003014042803544411000d40d550b450a20010307019058480e0ba41e40c0d841c0d405e035520b03001c0d52280019241070703a21001002040c00707032510184074100040300c41490003aa414660300403c2c1140365464510a042e003000a050080c2d0928a07101004222801c00070810012287c0c07004004d080d003001e10030b1104c2145000f02d0346a07004524040d01c1a07400600030062940d8924003041c480d401960000c01007070004140308c0f417800040c401c07010611300107003448a1100d227251b1000c1c44e00d85900b40d40014802890b50200c0d60851420181140c80303107548540070 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 924499181 1250 924497931 924497933
    0xc09151f081008060112050c060c070816050a0e09030918070917071403100e0a51091b12080f03190c030c091e1404020705070f03 57
    0x925000200340303949031503a5082c10046240c00198050441d1303450000a40fa1040b81c0c41c0450400c03c06540d000c2e030201000c01e1f00303406d8440119059080316151400c0300d6981e69100000741d446901841020381c000d42004013040350641c00102d06074440701d1513094902e0004c54000180000410184808900a044041006044d0000c0d00ba0016144620441c10070f10341001480d503443c1803a001d4036603000d10f120f0085603503071030030096103d424030014030138400c1700c00700c00202c1c1c0d4814009406540b8110030800d180c007840300034500d400a01132404003e498040f00590500b0b658070215011035031943e43c80c000c4000b1250b40d40b08070117480740f14080d0b40300d00c60110208000c211410390010400c29440d5001c000c0065044011141220080f0402688039a200e849085c04459011350603d45c181c1800e580204040d80b59110810780c48050b11003005058031803200b9480c000c044407802140b0f84030080184601071918500e82c066040061002d8944110365603150704140b42540080380650b1580000c0c0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 924500431 1250 924499181 924499187
    0xc060a061502010908070f0201170123011d091017030712020102190309020f060a050a032d11040b1902010b031c0e131505030c030a02030c09151f 64
    0x914090302c024080c182e0140c42d1103010f4810120000c00503010450030004690145003035000401610b45854119a911220130050030408440069100c0c0c00b8003202e41998001c030200b06074820052400f410003e2080c05000c03045101908100c00700b10f51803000503140105401402d420324039807002d181c43d801d9500d0103503a1807d0368030701103055900600051201c200303403082c0007a182c3c101c0c3c9008143d138555800841c07802d0700021661074004000140e441486038200c0010100d03000035a07003c1149126118044e000b072480d02011a8602592021100e100e00a5411184400a48008052034107070380e101e6000d07240e803000d0100282c880350380189110f010340a21640c15080c4003a00a09041004010720588591007260b41c1e00600c2001e00102d00c468407101d8512035030100640382040241d510550f104804c41c498858644a8411a407820080d411701146c251100c1d0760107401414003400c048100300403040014009404440801100704031584c4240058410a240030741000c1c40200c080d03001 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 924501681 1250 924500431 924500459
    0x70302010c03150e1b03010f0e09070b190909050c0301080615030d050a050d0204170d0908070e04050f01141006050403051203041b090203041707020907030f09060501080f0d09180209060c060a06 85
    0x10003240e81101b001080f070909103804480c1a644a100501d070907a08a603404e072013b070807a030080c41c0c2e1280307000100000480360701c005605031081841203078560703642c1c070410020700c0c0c2807004202e806402103801500000d000e60050032202c2082e0400d907040c880d0b5492303813900b260800d6002002e850b101c03985080160000340f0428140d00b07407a25001e0411814001b5043d520101446091152180400080e0500c001804004440e51110340248080c13007030015200c5604006903000b014200c04100d00081140c0900c0407141100d5024000d041c80c411501d00c9200203400c010301c00d90b07004002d03040c3c140c040003a00442c80f001d4041d1b4140140c032400c0a0901c031003440c60850480d148400104076180c0961f0f901842d440d070005681c40e0124514952140743c1000d01511417009015900384400802c0c1d6400c0825840020303188141140d880d00b00c407040403074907001940300e0b051110001d0303010091841c60f550001e001c0c03280050401da01e8080900c0b102e034a010011140030b090350381e6801052008044c0d031000 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 924502931 1250 924501681 924501691
    0xc080d0f0e1606050d111b2e050601020f0a080309100b09040f08041d0405010c0305070816020715030b01020c06030601020c0d020d080f070302010c03150e1b03010f0e 73
    0x28211904440640b145080c0c0c41d000318014088045900b4a4926684e0450b14000c2141e03040345442d85d4031030011041e210001500c824882c060f0401611084061105003420320000c1c800441060069181c030381c00803d03001e41603d0450083d0005080202030801c144400a03110315051039981c174002029034141032900b04038900850904108410303070b0380c0705007080750004d4201e112885000c09503e058541032155500003800700f81401803e010441101c0d042c144624018402030013181400340d801c4003101e0003103e5100204640c540820140004001c400b84050031600450790034545480f03051001804240301500001c0e02c6440910440d641400403139848002542c2082c1181072140c0040c0d22143c091104034003030004d0f407001d40d05569070f4a40b040410358104860340e968070f0328aa10071407554487c0c1c106401640c21310600540d9184a03200d0a403110803400384841c1000c0c104404200c881502402e15070180d1050030100f0680c00c240c20066000384444407201d00d5140ca0400c0072a441d0320001c2c9 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 924504181 1250 924502931 924502933
    0x6050105090103021f0c0c08030403061508030403030c03180905041208010819020409020d11011b0b04030806031e160905090a060b0d0f0f0b090c0f04020a0c080d0f0e 73
    0x70041005031124000c9090a403c025100315940c0c03c0440211070075420705d04e001e44007c0d0503000000d07004038088002e00c140d90262100340001808044405800006c41c4a00d16903a0710401007000400d00c1842d1440b0f000d0b02c40c0c50080910003101c0080c07202d40200d9000050407030380e40e10078007003084040055000c0008190034402ca207507141181442d03c4a0301800030580710707403c107501d0302d04650341e56000018190b0300406107001c014503030809008440c005406140400c208140795035500c881c540d4441e2089500c4900c403407050b6a07681d402c80700f1203400351015401d8403c1e02c070943c0c0000ca80300c50a2040d030140000901d0f10b151421380890010004d03600ca505102e1801d82070110070b038408a410311000da001000811410214008220411a032400180214541c051a042040302801c0b04d0310040780100310b0350000f92180c0c1c2416071500001c000240e03009640400f5902e060a290300a444041201c2c20840011a015203c0c1905039100700d40000c04181c0d5202d501300d070b9036054414440e0310b1407160 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 924505431 1250 924504181 924504199
    0x40b03011806050c0f0d050f010614091c0b0a0e2406090421030509010f06061b0203010605060c01020c0717030706110409060602010b100201360506040c0306050105 72
    0x3078803108800350301c684060314880c2c0391000284022501e00444030340e41551407415550b015480c018a0043c076056608035044100c03480009249031080701891822810842c1030740c0f034041c00780104468001d0302100c256a0514400082012031954050184140460100851010721283e82d0314200704905004001440104891480109aa00300b00d40e01a01c2039449026940b194104094418440003905901909d046083c0843c2d42e81074001034060300c440301c024803020140b5411030303065134802d006420009030303000da9210f07605201c000030015030350002d400020200d0325603020948550114043d081aa900042c41d10b03040f501c1040020000e000712840e007031108564803086910703031250308400b0b4080394596000310a50b1401d6402c030350080c800d8035030800210b551804081d01910b02d0380e001078420303e00313054017048042c0103001c0d0314965071f4409100382d40813105c11101140740c0d14606560b03103003400700407100000a00421a003070186005a2220b01c41c20302e1440c107601030341d405802c102e00540c100 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 924506681 1250 924505431 924505451
    0x100201050a06240309060b060a18050904080d0209150408070501200601030b09030c07060801050310150519050d030507141212150d03110c0f0d020409240605040b0301 73
    0x101007000043c0c109454007081c080091305040014200902e0072650002000415481040e08100b10070460080c40c4540342038540d44104100309220103c80103801100100400e040a0078954002e007140b020003000c6d14203082e44582610350742c1d04190418800da51180200340001c0d0f8101c942e900d81070241000c1d080f02c0c3c0000c102c1e560f4940c0d13818030000f45480301020124280160510a03550390003209011150030583c1d800000305403007800c0c499240070f80540610710540c1c50142c0958035a071840010314a40451415050201112031102901081019403c011420759245002b08542600035580c00e612427800e03090221201401104403002c9510617114171000c06403050540e6180364094200c805285e4480f0306890b09444182c40d256485010602c0d140101034100070f014a004d003000c82151501807900c010301c0720411848000c075070320071080d1540000620b440d410044041e44142818881a0f00480c5403000401451000c168060745548023030286040503c81c603a4944401c070001c1c40b205c508 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 924507931 1250 924506681 924506729
    0xc18030a1203050c0c030f090108070c031e0306030c0f03030306080d0801140604090203130b0a11040302100201061806030b06012a05070b0a0c0b01140a23100201050a06 74
    0x3581c0c801028107071180d0004000c00f1103a426503454a5680c1c0a8a036503030380008040449038002031016011900303080c04a5811071180c3c050940301941034031000d012810309821460003a80c0030b1820b008158580c003001c000511030000e0a0000c0020000c0380400b5400c1d49000b0302990701c00d0300301c410b0680c4003040c2000c0c0107a000c21014111039a40203032030300b2499402c0100d101e03442240c0000651500000034052185c100d410fa81c45540e020302c5403c841900d8008584066403040ce9030194142c13018001400503213000d50b070254440001d400001843d43d0390f0a501d40b003c1040d400d030201c3d296900c1e10200300348880c0b2214594480303000d00e0000303280d01c0c1c84207150000041d41e0785040b03588810016030b1010440c0c1000b05001408418060310b8a514500d00001c1c0f490040c19412038481a10000003c0c1460804c0303031901012030020542c4800c00c0c1441d50460740802c8041150b80b5441800c6280344007074a90680c1d113264a811035001142a1a00441c03070000c1c0d842e658007488101905e01c000103141c1007 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 924509181 1250 924507931 924507953
    0x2120106060804140d020303010b0c0102090a08031b0115051201060e010b030f0a05160545060307080711070506070303020c0d0c02060901230d05040201080f0403021914060c18030a 79
    0x1444ae1103094542c95415400c41c024010041c115800201d0740d40c0118029a002010304800801e100852045070720f07116189090302c08105d1841ea144610700002c1c4064a8490341103120282d017080002419940c980440e40c00300000e82c0907030a02403000081c0300200032004481944110300a42c01c6c802420200382c4174105081c814040740410501044140f40d40c1380080b4074240550040f0025404241c20303a441082c0c3c4200d10804002c1490611407094a07810311500f034900c00c0d0000d481d041942c1c1e0310340c02c0555800582c0640a0210700900c4408207050b501e90014005a034040e03036006844854981319180390012125040c03041c040100e44030401a0f44030021180c00036005c2c070300722111240c41c044a0368032000e080c3e0f104000e140c02055070030108803141cac082c0b40704500036078480c822038681c50351000903e40e080e07030050010b0300054552035401ca18071070710300c601c144240d400352042a04090310720f082000c00d0307520000006000a9101c0c00a408007030890650340f00700d024005519960341c0d203000c911 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 924510431 1250 924509181 924509189
    0x280f0f0513150306120206070b04020d290901151a040503060115020d050301180216050307202d010e0d03030b01140705061302120106060804140d02030301 68
    0x14081002a5458403510945540101041100181d00d4861115500c0800032515000010740350640006a468001090903141034000c0c202c10311b4078411351140510500014000e03038014008240d05800103c801d40342208241c800b86544c0100030700042e0094010b04c0103801704040f40e042c018005021015801c000c811507880303603002014160901c851850b2402594011903140c05508000120250032043e1205a07403a01c0d801d44010040054094036903000078081d00d08007203040070403036407503074510b80c000e156049806034905d2038500650303101ca16660152104480c4c1c42c0c0503804400b00c40598014404504004503050805070341080e40c2c140c0710f0348400320032007181c2010305000c014503400f5040d400a0010040e105064040c41400c0c00b1703014049519449000510f44403020075000300b40003d8400c1580c4c400064015902d0380a031003400c202c802c070000e0740e00000c4003880208040091161200a000644960f91646018108003580041c00c0c1001403280c1c008061600d029640441240d041d5 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 924511681 1250 924510431 924510437
    0x1f0305190c0e19090c02101103010b0a0c05010621050c040203070c0b060a0f0807060806060f04030219090519050906040201050301030b04030c06020315040e0f0c012a0305280f 77
    0x2d00f00100b00c40714000c83d9001c9001e00745026078215029a01088005040d61018014003000a0300707419000644024424003c010700c050020115030f80c8185601d1000601820000c202162604a01d040003800464080c1103020440c402d8401c1040c184884250b03c2e6048804508620341310801911180030100010f00041d040d2001034030540d114094140a042420088011151204045643c4040ca8083c6902258510002613510300d8000b049030000318080c403440341407920710342c24480c0e6244811460408900303c4800480c5210103803042c2c52189150242000c81080200311880c02c6030000350042d08140c0050b410000542d17048011681120341c4000814025615070804490b104919500200300d1400041404940c955030400000100300c11a403c1001c0a081c882c0d595032100b84040c000c0c490b412501d08440301c3d6020700c0c2c51040170342c681b00b040000d40035805007034002d132030402c1d000b1008100d02040744481c02410485140400d610104a0070303082182c410054040c4510b10400c50030 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 924512931 1250 924511681 924511699
    0x804090f0b0a0303080619030c090902120105011a0d1e020a14070f021203160c0f150207030b0603010f060305060a0b1206010902070f02030a030306053303061f0305190c0e 75
    0x200e5036181c0c07c00029500107040340d0031141c48402d035001500501005a1050520f60400400e020f8184625412545503151031030303528245142e029810b40004070034400781546c0f5820403848000107400303410741038414100160b0701e41c0c005001400c0d010202c4040301c05000c0c184048800120991030b11440c481c0c040311485001e140704a15246940700369680c0c03c0c05015001000d50400c06403600a00035120382c4905a03034515140c4000c800302c85081700c810b8005038001242003001c074090f0200d4580000005c0c0001c1109189450003606a414a80c01154107510040804c80015a02e01c11030b007a4400850b030503503e02640801e003940c0e0b0b900600800d076041c2c0d400200d020800008103600083c95a000d01505e003050110304026008140c01d1007803a026002d000700214410101001150001d00010000655002290755405907604001c007002d400c103540d480c90502505440a030820421041e650125441c9440140c400515208240d0306000c0c60070402100046904a41c1c9007005100c2600d1210b0 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 924514181 1250 924512931 924512959
    0xf1b0d05012009042a0c380a050c120603100614041a01050a0c020f0a08070812090109090515040e0106050415060f08040f0804090f0b0a03030806 64
    0x20041004080a07024004600c07401640507030707824003501032400c00f1a0100302e0759646814159804c4642075840b07240c00030100d121710f903940c007a4000780011800740d12040c0c42c0c0310f410a18403400c0800410004001d880c9104101200c440000e43e91358441450743d02400181808021240c1d68000c12003031021301120040051041c2e1030410251038003960a060521400d0f0b0756191100c80500909078950185003070070742850091503003100b203072007081d41a550b1924120801e4001c94410241d4041249d01000036500511542d27a41204200900191400390409034984018286044030788094108680d8040c018070b003031680c002002800315041c542000c12a60b031219140c00c40500f10b41e0080c0d43c0240b402c407070035111520540c050003d5030002c0c0c0c2c0420000b41942200d035000720b400e00c0741a0000748020386031503d01d4441c03c0b445401a104105510741c0d8100e40e520041076802c260441c20a040e076072402c1260750040e40c010980c080744140d1b10b101196040d0740300180b02140080040340a109602500030b = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 924515431 1250 924514181 924514183
    0x50904230c071406040f120206070e040c140a08061806010f1407021801061404050306070f021216021005130501050a090801020d02030a2a080c070609030c02030f1b0d05 74
    0x42400b1018090311130502d49443c00100d2104107085c00d031002c1e03035403000f03401049000045c66070103080c0c59215881000250700401000d000440d00380d200b00300d007006a01e819421100040d00c0d413105175403141c540f80d20b4254203002e9026105049042104902424800243d0708240c05128a5030149010302007074200850b100f01c64890048000d411007010583c551030b01011b904640d050f190130b60f580c04c011542d020000c00c1c07036000d54080c0ca0342c076400a0300400d03400b50080d5042c9881e00b4035401602c8600f00c000b004d18a00390440d441c0304845902d9100564114a8512140d0300490721505000c1d08010071300004488012045c0900d41c1071100001e00341e5030f014020300c9140700502480000b5075a890b451101d40d8040d400685191500d20306181c1c0b040c06d0382d400c1c0300415160040c00c00c046000707002e24040171a05010701820b152503030442004603d0104e00540591000103019841d1942c0000040c41494a00003000440b10a150800003050006410405803500c140c0c2c021a59100030a0300e0f42412 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 924516681 1250 924515431 924515453
    0x9010510061e1e020d02060a110f03090a0f0f0303051b090f03100603060b0405060301021c02360306071803080d020c01450b15060307050904230c07 65
    0x20901c3c411982001288107074001040980801e6642c00c0d00c900744c550894581c207481c4c0701000345015407014001154002c0e5104043c5038081c0c504c408075003910aa0fa100c0d14040150740005840600c400441c034002c7c0350305030160701d401c0404240145030821040486038818020300c501d1a115083e107070342d81e0f14250707010025509020350300102001641e90300d2400f10001e010f0441704030301860030400001c41c14501031003030303450324100321414410410b90718400d0030095002c6c0902010100c41f10204d1403890f016414404603c40340c5184144403401c086003058030307001d00286407104000d0039a103202e4103500040030318800c4a5001414549860030411058080c0c0a03019a5100750340c41e20802c00119070000c0701031800c101c5510460036a062602c06800c00810070300042144603804001c8110001c2c0039846480d40c03202c05034140540400b207034400203691381c0c029646c2c100015004900c0003014900341c403800307010f4800d410520f0f100c1d01242e205100300c403034010805208101301007110f0382488807640c14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 924517931 1250 924516681 924516707
    0x50c030f04110f0310150e0103050303180709090602180909100207020103021c050f09030f0f0904021603030b150705070b070305040914040b093007020301050a0509010510061e 77
    0x1914105e416009402c001814251210a00314413284c50014809000b2041c0c14142c070780000155246542d01502c2c071065140021582145116601000a8001c080d205480000f84030300700150380c80c52000700d401d2540140b000c00910800020090000310803002239040b00c00107035140003586852050006074024000c04003030610326440c04030540c0240c0f0656112074820700626130118200c0d00c44c5264640d503800343e05040381511900300850082c0b901008007130048404000d2001d0f140240071031103401d0100c0e240b4401c601203030700c45401850601e0251086410032041c0d80c0c1c80740c10011280c0f02c0d1a620b03c1c0611400110400008454003407522550441c0d002d020513035007d016110b003003403039010240c4048406070355025400002c08c0e62404d011038100c0280059801d09a040389003000c10005000709070380c1440e403403d42040031800584082c0a1284a504041c0300010a481c04036013050030b5810041144660004208091116680000120204040d5400c1c2c0844030f48602e4402e0316502c2103184 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 924519181 1250 924517931 924517933
    0xe0a03030b1309140f0604050604031b060c11240402090402010e031e120301053d0e030c060405060d150f080a110907090b220f09050c030f04110f03 65
    0x81003000c1c0f080b080a1914045001000c58070b0408840041c0b50706c80d44142c0d40100b083d004000428007007440740c400b13101c0005500b901101c8240361aa644030450b08400005004034000b24510110000d0602440c04c00b001c45407102d00342c4c4c1d282c0c00b014408000000300000d100d83d0038074001c035066911074124a01c0051001c2c0c110f48207418100316400304004000d11210703842c800e00c014204034428400030b80c4d04907074014182018001408290b020800203101024122800400a461400e00070840700c0d442c0100301c0d2107011070702c54000141810103115042c2180990400c01c420412a15050201c402c1c0c1c805907000064035440001c441d180820301c1d80d1110340c40300040c0a0104120001007041c005640c0f14003000d80e11072028000344500c1d2001200e42c0f4000c910038640030000c190030200100803548c402400c081900611440b14a11b11545070020509100502804e0116a01500c1030340d400020070078500b802e40c44c00d1550704180d0321004200600d41064020880c00c1c1d516641c2004203090302c028 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 924520431 1250 924519181 924519191
    0x10609330512100e060904020102010e01020406170112230304030c0303080117010504020a050f03070504060f03030207080c090a0e1014090705010c0f0f03110709021c0e0a03030b13 79
    0x320010722a400c5900d04500070030a810201d224040c1e086104400c07203848100300002c03503564008200034504020702c182c1c1503548400e841c10000703000784010000b81099483d0785050140d01d101a40c0700d540d0581140b001c00030306900c5000411403040b000b05010099808141c01054042c28182c2503004a903c014900300111380044101a0010051416950041c81d1a110302c3c20b103e0840d802d840058030042c0d0040001e40051185081c00a0780500e80040038003101c00103691100440c0c21103042d41d20400000301b01d41e405000305a41440381d03400524503403001b00b580300f00100c0054000000902400e14680c1d0740c00000c1c00116007401214014448440304010340d0b00ea000340030070343c01411984d41642d409109404a415070161903001010740e0071550300c07109040d040d55200f00108552005030284072004e00d600180b00c00811902c406000c44034009603c80040700341c9105a00003036401c040b011340c00c108a83c2d42c184400075802c5001c503014640031401c81c0c01540400c80c9100b2040c004500c00d400c0c4 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 924521681 1250 924520431 924520529
    0x40e03040312141233211005060103110c07061b12030c0207090e12221707060e090f070306151d011b06020702030709050403020a0c0608010609 63
    0x20a85103841000f168810034200b20640040d0117440f85c68025042008201107185a020f041c1014208900e010a1084109122610345840c0c9003411500e940026292100100141940c0c18051620390518001405040c141030611135611030307000d0701421003004000d00c0703201c07055506600c00401d903c0e04200800207500180704014003074202507114902510880000288041d1148134001e204030080001c1c1012100c08480c002840d4044c90f40d070181141d42e0040020500d4603580c81c0c5004100c040901d02c8220644202a400c2c900d155008000b4410040c010048948810f0102c6a104010490307294256807003000a0300201090707003100b030020b0400f400e100507a6130007a8003001e503001c0e14092990000c183c440110b541031000303035402c000c400710b200b0079900142440d0058491a8801400c4e00da0180c0c40b407400104550084a0580c0181d100000c00010b04c6641c04009000c1d001a103840700c9998185070000e405c000840c42207000d82e02c0b100c44041c40d04101c480501100f4044c00c1d1b44000c40b5240 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 924522931 1250 924521681 924521707
    0x4020d050f04050d090b04050d05030408060c2d040e04030207032102100209010905130f02072001111c110706080702061501020c0d0813090501060e040e0304031214 72
    0x85400f2211840b0740c2c0d415011040c041c100c030341d04807060300e00200e1410b800e140c140300010341c0c1194101e600c0d100c14032010900c50f8061004501c110b0001ca0305d99200c420340c0380c034510010801c0c010300b54401a6003403540c402e03212101c210b41c29900c6200d60148982c813580740c1285032505031381c4040d00340000108425000e4140b88403004099146a0031569580b490702075070022032281342c9030306000c03808504040085007882201c41030154500c4100080e011510700059090b6030020b0421140c0b080b00d1248903074814906010800a181c0c03c1c07904414802c48180c6543e41c4240d056410014135048601110503680701e0b24491110441c00e00a559109544240107006600d0030750f0314078094003540c0006500b00300401e821404144050340101040403c4505001d07030203080e81800e4407480c1081200c5001034600012078001007000480000e142d62520900031300c03008051030031078030560a1036101c482030007001080e9800c1d070340c212042c0c0480c800c1c0060305540c013204002400082030b01c041303204140000 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 924524181 1250 924522931 924522961
    0x50712031b030201290a030b070c0804180608010b0f06030c0714060604060617040201050304080d09030908010b0a06091404180506160c050307060e031b1b0f060a030b04020d05 77
    0x100403044010143c1400c5004495804441d917081e00201c3c02d580420106a01200d941d40081131810485000440c47d100d900c000e44c05900720b10300801421003403102d00141803060100a044880081000802d4140000e202c0302400038800d10590b8080045a401a0403070125880b6035807160540e60000494070040e0744a640460304180724500c0c0c4200000c000d4045c04800040c501c0d443d400e82116919980151842c2e080a0800d4444d04010b01618001d00c4582c030850003c01c1c0030703860f452821480e1006e5982510014a03005e4003c01620004014030307034000310358400b0350300c8881c40c1d509080b0780a004640148110100d50007943c2e0b40440f00f81c144000801c01c5405041444c481031441520b500040d2038206000c04e000f44507038402c011400200d00d865101403660214281a0f034644141c0040103501d8a112950005094101c000190807c580d0354400407540307901a80e00d0f031010451100052203502a440b039180c02d064940500c0401640d40da811034284c4209a202000745044c1500c1c0c0b22102d078 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 924525431 1250 924524181 924524201
    0x80d02071a0603190609060b100c050714061c02070803042607080307050d06050306182506140906160b0f04050601060c050a020a090c0801090603050712031b030201 72
    0x1d2005400300301503040c00300f1001d040103000c100b5019120300c0c40e03560f100100201ca0040c2c44541d130b80e0140d11310325565814203d20381c1c00c0719503a010703a000395070420310704000b190747c000c0103150651083d00000c1c0d2900d90558900d140389a1310720358900901e52002c1d000e80302c0d82c03130001c10109000040008220700301000035070f90000c1820b05042d40003200303040d002500c0b9104002d020303146c00f0300006008600c10b10003410700f421000404991280d0701e40c00700785404010f903410203d000710604a000e51440c204007985044802021075945861580580d030a1800140207040c20042c001c51640d84030044081241d000800c003400d459901c03844c1b040743c5604a050004125143c01a44002c503040c0c10205649600464003d80a0103a90b440c1010554803044520f1080754103008061030080980c0d2428003c000400c10f00301c000c1500c960038400200103c10507001010814940f0074188045a00011020b0645620400744260742e2858201030b07031452242e01503403882100750600d403410581d0641158100c1 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 924526681 1250 924525431 924525473
    0x908040602031306170f06120d1e080c090613080604081c0506010914040603230f03030f0c0f07080d0c020717060a360201021006140409080d0207 64
    0x4980301d410171610384400407070568240100a020440c81985840195000b0800501c0c1c0008038050491950400040454803000b00300d0300c1047c00100c0503051307981407050000e1b20740321401d850079010245250162140c5c180c0100c1c00030400854410300e03000c11401804109040700c201f0303c1c0524000d5107540c00581c000d46c2e50b5040414032084904d4030302806000700c4058540310700031410100c110554044003107256600980320600000030444035002c050b00042d9468107a841c8106800d241440c1203c42007021005a20401c02c116181199040d0350340c008107849142a030b210f03029400c5110f5402805e4000d00384000001389040c0034891540b0420710708909409480c1c0321681c3d64000d02540303030082c4040007140c001030700243d048446503014004009007509034001032005050411507800311142980242c4410b21024429503804002c1140c08035012941030040904203042040c045101d050307070500854031002540b08100081040c1d40032180020b0b411501c0d13051a0400d030480c01c007014046184 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 924527931 1250 924526681 924526717
    0x60f0e0103150b061b0c060a031a030c1804051f090308061f110a06020708031005031f0e0a0209090d14091014120717070e01021c03090804060203 64
    0x4041c2c000e001c0c031414240000c02c26400c03c5121440a003080c1c00215201d42280203607007800c00e840c1e850703c0c050102c07200d03541d400092540e1624001369450308190340c0140b182d800150503a00d60f54906510a9041020111745030f644d489601c0c20900d418500c00701164048400c40000d000045598003180b2424000d548540294a600d4140708001164a004d00b114200c95002e00030b88501034200b071400038800c03800b244d540700066180c0a0481c0c2210004442070100001031050f0400c1da51a1000500000c9000d4205002102e013050030840040e40707041c00341170303c80d40e0b0154582c200b40700040355a5000f030041c801d0b61402c10000c0e41c50303011402070322010130139290080c02c8440e4548251030a4040190184020003c00c810588000b0440e17040750254120400c5507005aa00040340343c2d010301e20369160318647c2c4d080081c44404600b401400c1d003080000c500146400caa900040c41c1c02001a01014105d00569940c02180603005500b000381c5500000200003810702e50010080403024504013041007 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 924529181 1250 924527931 924527963
    0x2010f090303020606041a12011e060e01150e13020307020118020d1419060b3303090a080301140f102307050a06050105090c1c020a03060f0e0103 64
    0x168400d1900000e4010f070301c00c0c4002061414154005612410310141c240a060112000195142840c41000c00182d4443c40500305e1313030780d640300086001480300d8000d00401d03013000180024507905125116102e1826a030700d621150185100200300704016041100d07000700080340d80c01a52068911000541c43c2010420b41c00c014211050822503004180041081043c0c850342c144402c404807000321030041d03ca044400030541c0e0100400d0340c0c4280804035100280d4010040d01c0a1118600783c2c5400300090590110165204813904140c1d4070f0320100c1d140d4680b00100e40c580014140000c003611000400401c1c1c01d0284c021588003004122580200a2a403000f4404480f01c03103495100410701a500c9014035007900044030549440ca200250301302106501e583d40380084015040d00d0142e0b50380d0051205042c15180d041d40300b02d0604440b860010011003060700c0200720a100c012481c0d001c1102c0054500c20741000c8010f003042408142e80544032525908620002c3c07004a130b00b0b504e00940781c0 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 924530431 1250 924529181 924529187
    0x16021c0b0c070213050a140403020615040501051807090b0403050312060f0913020105120703020c0706020c06040605070f02090403080924010b0901090b0c070501030f1512140304030b0402010f 84
    0x3034801a405070245031148501c0341280d02405e000307441009600d40342c4607501000400006c04138812070299000b001d1038106803120420360101c0700035150103242050014401e60306e900d102c1e420300c007082d1080d041403075580703074012124808503810141141e400041c00006000001018010002c541e040200054076035104002c103003100c044159800c45c7c441d03000a9102907030b0314081d10500e40107042852a00c150076803205140321003140c484c000b207035001c5074800a48100300301c000702515a40c0003e20000a10707000003480d50040b4483d00c400c0040011719202080b0961100012040d0f0203089070b4064101450302400944080300d180c00507100c0c0b00d80408481c0203061041340c0c0140700e4080e51440364240540e103001648403003c810306020406200061400c461002003404400003409080075a080800050588240032009039416013031824140c0c0840400c940c0d0001c9541103014032162403e40c0c41d0400c1c0070b062075400304c803040c0400b140002c20b014034854118032842c401da86240152075810025 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 924531681 1250 924530431 924530437
    0x5070f06170109200c010f090602070b06010801270609060e041205030118020f0c0601090621170c0a050715090e070c0b1314070603110f07030516021c0b0c 68
    0x2e08000c50b144d0781002d0f00f8080303440082049007500000030403585614101941902d4007100d04454040d130010350b00c0b0a000030111000d400c40800d00c0d00f0b6100e540342800c2c20305020b01c0710780032991401c41c05036610300d180030a90140380244140b0b030040c8400c2d035960a880e103402108440a0390300442d90030860412a11075001c50b03040c2c8004003282c5c116111034501c560002d4102c07036010414203104200000707003100c00f00007260091407241408607041e401d028400e54003c019150700b1003176103943c00b0781d00d00140c0112019440e80ca83c441045495584500c0714528080031400d000d4420b00a112001c2f52281c03520424941150180d100e00d204aa03864059810f080c0040350342500044d0005014070003e0705000d80c503508a07102c3c0032858618543d90b125107801107241513452a40f035020b0801040aa07405000d00080880c00b040e0090600001f0b408001c050301ca00c0c40001c081003030005804071404282d03641c103c251034001d01103a1484200a09010148048031010380345104410002030042c5000421 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 924532931 1250 924531681 924531701
    0x321050f04061d0d0f031b0803060906010c0c0f1e0503061302040f0f09050f0303091b061e0a1d0d0201140702060304210e150705070f06170109 63
    0x284500e0945000d004883c0d20014840b500c00e86418400c1c545407980e204a41000c40c18000c00740e012582400c2d00d8094049044654085412007003180f081c00814605802d80b940000140c0301116030f03542e03000048030950090000204580c1342e1740c001240f580342d02a0326500f41c910800e41c1d540d426101d00f00b106102c603410b00c84e0960603403280c80000c080300445152454079600c05071004c110701064010600a0719038003070100340305c207a803820b4080a2140802c90510400c1c0c0c02c0e8040e43c13850415201c0d01d6268102c0c4241c8800348121800300020548819046070326850314400ba0a50961a204109010703512005041d00051090b25003c3c031a80c0751005030110b801030003818481c0e144100e50040d1008400d00392081061b403800c3c464070025860300d1001354481c40c4903000742d07024441c210310494010b50500409070100920007450280030780b2948412001c00b9070545000d600d8034003d2805503d411000d8002c00300d2507071441c10006007250019110a09c407014440b00c45800ea894100c003e04582d08100 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 924534181 1250 924532931 924532957
    0x9031112040b1c060906080f07091a01050f1306031b08010b1b100c02070e010905090327031209151801050a0c08030106080f070f021c090f032105 64
    0x21000001a42400716460382d01103060001c110349a45007170401c00c03a005948508450b0700196030341e05081c0028001603020305071051307041210794a4040c450400401841c40c1030b041c0400025100c500031850380a8a540340050103402d0301140d10f9510040190081080d15404c0300707500264059010300403520141611000c484460a10084019600c039242d20a150340c56140142c200c00288070200f4000d200c1500459001071442d0f40c07038850202c164407416030007400101d15200502ca41d040d00401101c10403074004150700071011a040000c40344104004446500d449000e4140c800540c0e190050f2242c107800303e07241c1d00d005040c85400e010078400da20008a669508501070a4950b00035400b400902c240f0303103051b0f0001c045c0c40c0c0d2030800301d91081c1c0000011407191020842400c1d0018011648000c541c54240c0480c180350101a556000c0100405c0c140032054010b540002d1040104000900d660340503940307101da40381000180320706170850505002c01a000e603400f0141c0214121080b06031441 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 924535431 1250 924534181 924534187
    0x5010206041124040f5607200312040302090601050c1c0806010216030f1a0117010606050a0c0b181e070503010501050a0e1009020a0203090109061407111309031112040b 74
    0x41c003000c0001c18500603003400d11403500c0400d0405590001a11105216100c000001d0002112591541408c0c080c0783d4800c0d072103032041e04000301d801000e070380c2160360580312821107403180c50044c1c905014403145040345100b8071182c441c0100004d00000c3c09845a9150001b55480304401207031103415030f0010800d41000d4072400c0001451112000524a0003503200c0301502540b1001d8408811017a8860038100c1007010440c0441d070020f22132240244024240301d450446c4807d4083e12054902601a0030b2031080000940002c03000740140c10003201070000d5501c100241d00c0e01482c0b035000c0d03c65a801901c61458003040764181441600d0607210300801c41131a2603c0c000b4160780302807000300000b10358030203001c0c001407460460001d0f0400f80c3c4150082c603141c0340d80d6800101b650340140d10120800905c0c482c142035414225007102c0c12507400c400001c0500c64070341c0216040032828803201440707901d0150300d00141603002c410b02055001d000280c1e958032400d400625440e0245001d901c088903420 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 924536681 1250 924535431 924535529
    0x60921030b0d1106071e1a0118050414010c120b04020a1b0303150f090f060e16050c03030f0121020612070c0212010606030605010206041124040f 64
    0x24001c040e658038004c040d589006116903411100e4140714031800340c481480b600c40000c1002ca0f00021207829100c900c031040540c9445100720002c503d091441d00e04540c1d800c04507081c071012000026124141d54000e000c0d1740c0c0e0019004081400c03e1801c072400900e001d10601e07035480d0a0007140c0e541e0320b05a86460085884800380082a100c0441c114103050b622980c030980f000c0e0101e07804000b002d02c110101d45162400c0c41c0042524200c664042d2058540341003071110f508540c6200390444c0c0a4641d90408114045c02500c1c01c0c03044003241a039902c008410880311003502c82000b0f0582d040d028498050050f24421040f0401c034900380254058400d11515610398074000041c2d82c0010b40f481c090788120f425402058159008155050041c1d442da1002d0009540501030080201000e20080400c0d20301a20750f807804182d40003219101d94000d01810308943d101c01c040c55040c2c100110700556a40d5185010780799103aa6216080021240c14001c03c040800401c11440e4500d100c1c115490604a03 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 924537931 1250 924536681 924536693
    0x51204060228122606042307082e06020c0d0b06220903020c01020607110c04050403110d111005040305070605070302040b0d0506191a0306010309060921030b0d 70
    0x801c450b0801000305803405450068581c1c0510400c58026400135055828031000f0700c0250ba2040b4121141072860701ca807071040c202c28041003548401180307000855a00c9a6103821010710480c504e05060201241e08080c00249010351103080700c989808071840582c8140a004410012038006060203014400082a82c10580d20006081c1c40808486241e9180010050110340c0c00e45000c0d001130780410000280f5507010858079810616509001c0042121003d041d952121841d080b9070090351540c0100e0100750003035151054440b45c05003598a0081552001003140c004004517050720300c0b84543d04180300d101032149500840d056543c061070300c401500c0d424003512000c1c08007010944c1c01c000004038113a82d0f0001d42400015100c0c04034075410080104021a40c0c1e021004007541c14100080145422a00501030301003030704021140c40356140c4006074001c003a1094094440c0d82426004000c200301103d060f4045102d40035081c1000340b15520032070032641c5190354560400a0f840309030b000301d41 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 924539181 1250 924537931 924537953
    0x3120305070e040e0a02130605130f0e0d020f01060617071b0b07030204050f0303040605070212120a0503090618070501030e1002040e0402030601142407051204060228 73
    0x15442c00e00302c410310102d90104040754a4000703450126000304074100114034010180c03004020301000180280350030400000c004420840140c0d9010b41d8400761154588100d411107141c80000704140c403c566140c00d0065114010051501c45551803c14041003c60050050407801d0b20810041d1b0455076940c0416250a11814400d5503903c4001c400070000421a8188620134031441c0e40160300c4529101c1484410400049101d110760014041484025449400e441003940c04850a1030442c00c0305a01030300b08854444004120314000030045405600030740114000c40904040700c0c8a03a40b4100701c0e60300c8006020f41c00d082c075000344001300404d61007500001000c400f02000d940442d00c100c00c0d490200d90281d4011500350307003400308001c1585024040c003801000c0051060104400b020700180c0e00001c509a90000c8403d04e00300503520801c0c6606641505074000110f810001d203c807900c100680251080b440180304264a601003207116030b41040712502542140302c00540581da03641c90300340c = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 924540431 1250 924539181 924539191
    0x80d08060316170c01020a1104240303050a0f030b031f0605030304080a0b0105090c07080f0d050f04060606090303080a0c0201021903020408011107260903030c060108070e0103120305 80
    0x100c00c0200350702c1c1e5452180301030720090030941298420f481c90b0f001c01600705503820588a0654204504560100f61255010a107030b11044030009961254043c0744080050005000100908000030210805400100501c0003880d02e44840d0144000c00100300c5c2960000c030301954158209a0b00403034401c00310005907184075111200802c6c0b05468201003031440e001680441120342c451058203007402101c58540c1e016150a542c01850343c58400c003103400500c560140149004800911404c0c1400703070b101556007051505405200508220a000041d40e10035601683c007070f8640030002440c00e0013000300764101d81e815100d000080e41d4440035440148500003d100c25035400300824000007941c1c001c071034800403141d140180c03603900701000d40b82115950010507604050411420010907041c11400d00b4090600307040c2a072148084115030700d0b5016020707080b50035200101b48208502c1c80401d0340c0341a6882c507401c946074555210724180f4000000e00c000b500c0d500940741e60300c86852090700000d40c41 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 924541681 1250 924540431 924540433
    0xf17012402071a030a0609020f031803130b030a0c0f0f031512051c0c0309090b0a030c090225020a061b0f06050a0b10080109090201031103041a090601080d080603 71
    0x4030f541d0300002003e5100344200050745101c0041044418882c41c4200b00c0902080d030ba046040550422400250344000350041441d1681c10450355603900e01003046400081130450407281c45a5500460310280c0c000b071b107860402509100f03480590300e2185651040b0403c03140d943c00c240c0d0641c410306600a10381594041d42826581002051001415100316206032080300142915807102a00031b443c00b2104400c0380c200149854070202180c0c0c001054800d8804e1038034001500b46a100000307081041546c002000700c109080e0000303c140702c1d0340c0030781080390410003401d1410502c0080140ca10300c42400c02540000001814801c89108915082c00f501403064203038100c0f001d546600d404400701003003c07500540c4407810010040c0290050702035001c0252130150319100b0104c07026101310070500414105941e50701c41c440642e846a0805980c80018051190740c0b41080e042100101d4200350100ca07009414002085d000000001c03030358103ca08001c060312031148034210840b01060003402c0345600d = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 924542931 1250 924541681 924541693
    0x21030a0914180a09050a0f0819080103080a031e09060b102303180a06050417030f0a0c02070317090f0111070e06010e030102220501020d090e0414030a0f17012402 71
    0x50341c1c7c2c80346800c8450241035a103860b035420b44580c80e412442d00030786d603040140901c01040000c40c0801503848030102420041520300d201404110721b512076a04425107542001003030004d002c2c0e19070040c50403100a40d8500501520303050103861046480415840c18400300d0140820b80300d8a002a5070040d51059440011b0340060182c2480d10003034200039030700301da60340040c001084082d0500303144500c5003d6810341189030010400f00c0a0100400c600265915607014103a060f109001d00c1d4091540072200d1082c0506000001143d5006030b001f8034003803420f20b0b000340142d6000341d928566464288000307002c464200b0960700600d21005d04007a050100c0c446040d10b86035420f0019284461000c1d0703200504040d0076020342c1217400180c3c080360554003d038500d114132030b41c080e01400a54101d0907000b095519185000d0402042030a08141c0360300000c034001044c00c0d0b00043c412404a03240e680c901c0320092a201d401500d10081c440e000138414180210311180d441d00719545140d41c0c00e07005441c6 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 924544181 1250 924542931 924542933
    0x1f0902130c350a2f03010e010e04031704030e0612040c06030b0303040909030903201e01020c22060f091506080601120e1204030b0c0a090521030a0914180a09050a 71
    0x60200744002809015181c04001800540c00387c904040c010034650107203580720f06282d1805001c00b80301004008801425000080a150040703002600803503014185955556955240100008090700e00300d80010211000151040c4680280103038200003c0185150524103041040148003c103821420b0000320070303000020918200070361044103400e403641c809056040c4100000b6612854a40ca10341c1c1d548554940f081e680000c8442d009801960001302503000301204110b4203c008000c00a800d081074004500313010134a8241085501c01c1d00284400c0c010103050081500c5603008503000107901100168066224244004c40c00d945908006000b10120158038100000d040d0150f070140c0c030000d000c00c20440c101c4a0307140d1150b0f114130707410700b402444000280407107070702e21801c2c0c810596a00d90150f0800010005090312200c0b0045030303518110002d002c2d280c01842e20543d050004d000052884030305084500140b060a0004000b011360340700d8040400601c3d08610941301845000701310f00c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 924545431 1250 924544181 924544241
    0xf2019060f02030103060c0806180c07030504031e0308100303080703050705070f0b07021603050607210c0f141e130305030d060f05031f0902130c350a 66
    0x3d030195000f403a01003101010b550300640f000e14041d01e801d008480c94040820f100c0045106103400c1840e2000207135503003805042c1120240103942010b0201280d82411840032620501034049061103500c0f0aa03441d40c3d52226000000c00328030001d030108403503c0c0090189413103540101c0d0b000d400b505200c0d0504400c0d80b2200c070384110a401c121484500300d0240700c0c0c0c0c0e64040000041d554005030703a003024142159540b40d10b550b00545180305105401e1307000c03800c25800c0c0a10024203c100c440400032024800f4006002d50038802c40f59002c54138042c50000004051002c4407000003c0304403034085101811781410a03a844050703100601500500e000c0700042c014002000e4124a050011a4840c00c20502c00e078840515800b1601c85d41c40740c5203603044890b613543c030124623140044000500c43c8032400400c80000c00b00100b1000541307480722001c2040c2d04125020190b81c100d40c055085030034180070b044481c0710500180048a070800c000100c40380fa40c2d4105111140c100b0240141440303c950f00700c = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 924546681 1250 924545431 924545437
    0xf01290901210603030905060903030d0c020a02060c031213050309090402030f120909010603060807030809040b0a0e070f0e0d02060c070b12070e04051905041a070f2019060f02 77
    0x10b0050207403221010014964000001d4024010403603066181c1210600001e41e2481008007019030551130f15004404280244a030003101303038010305510743c1c40c94426043c0d83c43e98045050b890000c48000c010440e0b0700314104103940c0081c1e00000445c5020b444cac4040044a140c001c000700d90501c202d0700240c80c1c2e00424428018016004407409848500f06000c100700c401e0140c203c07000701441c0c002c041045500001d800d204036074100c02c0381c69851400f20003103070241950001c083d8219030f050b540010b07000c003025030f503038400c108958544c07007030242d80d5004894200000c80c0150f8811915131403000940f5024004080e000f46540860341269542e84810201c0c2c1c00011044110205002c200a112500300082101d1800200c50070001481c000d140c0c00342d6241840080550103030b0300e9000504024420b010100040d205103a50b05091038200c20040c46103504004900020b815541c1d5102c4140315006a2540c614004004d80707980c0c01207400c500502403200300142c80880e100e01c914502100b0034802 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 924547931 1250 924546681 924546737
    0x6030501060e0918032d03160f05040f0b030a0c090e2202120a0209011d1303050909010b1b0a050c0111070e01061e050315010f0212030a050f01290901 66
    0x1122080c080f48aa01800e0006c036030410070712200b04200400800304c8001c1171210304403400c0c5000d00d81c2c074140d07040300c2d80d020719003218511300d140100c0442c0200d003140c05035126841c8900d0078032113011100c1007151000180c3c840c82170003114110110300020f0560072a440314403158140780301550965000504420001140b40310340d03801400500c03007076003481651280075011950030f110303c440079a512403408030b000901c5144802c0c0f204500400b0180724004541910000030086541035842d80106a680d5010700c911000004800308a101aa10003160030f45400b50420003a08520203038000569a00e00c600d00e071485039001d02c0001240740018441414081d24856407464849000316000084004d400071131401801402d20800c4900d690107c4094411075081c640008080d2035180c0c10391801c0d044154100804c0c80210400040d40025800b01e03114884c1420840541d90341d0300810b410005884003034800101c41102e68002650360000203017012241031400e1a6010b10f0402c01090081c40415 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 924549181 1250 924547931 924547957
    0x20f03100608090d0f030b01121a01081e0a05040201050405030718050f040b0720010606110c0405060d03031a0406030812100b1c020d0504051606030501060e091803 72
    0x1401d0001541c0300040507407228024000344501c8068a20213418440314208100c1055150703010301445900c120030403405102c1c410b0003071009103000700340b2840303040380152283d0001f103035003000506622903440e086800c4803117002400340300d8480c46910000741c00c00820a905110f4100000a416142040010001e1119448192041007407884140903078201605614100e0a00c00070301000c0348804040a80100c0f5030b00f4401d496441c0c5980c81d41c0402c80411401c01c8035483e2920004246401c540444a400c580c1425038a6041500f070400c000c584043c0c803090340110b0000c448000007406079100c10102001c056030880700382041030004042e2182a001140c01907008506a00381d107480c2401140c02c6032110441e031141c141070110611141c0508003074005045070040041901502c51750442d6814160014103010340d261604019a84a0309042c3e075655411f20324400044081c464031a850503140290f075507031407100524007040100da6015100b0580c85000c0c06c045110150104000c0c1422a02ca903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 924550431 1250 924549181 924549211
    0xf0126180f0a0b01060503190b0117011205120703050313050c060f0a0e0904020312070c09240803120c09011e230f16241b020f0718020f03 61
    0x11034043d40403041030307016806002080c01840100c11031040c40600090303080c10300040540000b070048402c400341d02c40210541468000205442814080e00c00380710703004404440009030f02d01000d030424802e0340d6024000030070500c041807203800305c0504000c91138040c0f01101c03400c02240c0009500e0381e00480322500c11010016000ca0020741150000d103c090701203605140307516194011a0712035203010f0000040900c000340400030082c2e8152401e020300404201007201200b14041001d40032070310000d2000d900c403102d40014540c6000400c6410f4540d0440c49a0050384030a0b0102c0b285411040d0440e0521448200c2800d40c040043c00110400c0c55650754018890301c22005140b22551220b410841e810f401c100321180042610110307107030300c0010b0880b000720080500300840c4084200809001e481b000c0384c010260700c41960494131188800300003c281c0004904003e0303980d40040c50b90701a10340c0016108102c80210f24000e206d04103035081e00545041c030a403d07104100c2d4002c0354050681c0c0924 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 924551681 1250 924550431 924550433
    0x150105040306110307120c020a061503060905010b0312031501051605010e0c041506020a021e030a150b0906031c050c010207060f060501050301061209060b040207050a020f0126180f0a 80
    0x2003583c01d80050070005040000c810f40c81402900c40c0c60001340644619103811013090511004100100203540099040294000500d030060113440e8841c91c40e44039102d040003611200c9019001c480c010015030b921500701c041034200655050700504041551903a40040f1480810801c2c05802241d10400028100000c0d4000421080720062041301400c40c2c0d040c2007e1041c0390f00029a045034540407190340101201104860314496004e206003a0035004012070242041624a102c00c03808070494070900406e003204081c8614010121055907066020035500245012075050b200d00c141d010b440d1044c42d04102c1c265071426a803201a048405a540d0315000c0c07040f400512480300030308403d00e8003d2540d45001d90043c4040d030742c10f10038040180c0d16003405040210030391000c021500302070420364542e40719003440c540700c0103080400c0e4040d0031100030303c4095602c10300f451070321007450050408620070705034140360011000a1408200d4030107401c0f140645c0c5030801078619942502c2e40101003070059 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 924552931 1250 924551681 924551687
    0x11205060c13090f020d0e0303040c300f170901120b01090303050c100603060605040b01090608160e0d08031611031b030909040503180f0306150105040306110307 71
    0x51028084980c00d0001021403016000d51034202d454004001c281644c5130300b8150b0092044110701080d680ca404041c41424002202441c4a24010103603040b03d2507072900005940700c1904418511003031404500c15429443d40d070040c44c4a170007500401c1c01102c0341d82e0340200034806984180d00703052010500c40c50b150b0f40200e1448070104078480a01480c4150300c0003a00303103c609d000c01000e0102c08150380c048480c0400001004440e186001d00c982a901c3c1444401090180585400740d400c0541c005025400fa0083e1070488031075030341e903448a540303d0030f03040b4001e14400c52070410003844d006410a595078682107045264010744c045a50303400d1079036201c0340d0300d942c004000e030522080d0203004040c0c10021054602c4070003207000154a10030010111425841080704442e4810b404d20240410b0260000140c1000d40c0100ca486070610724017070401c070f01c4c01980340226034568045030014a00104803211280c1460060505501b410303100e6503800c0030703203284847c0110040000301c02c014071135034 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 924554181 1250 924552931 924552943
    0x12020c1f0f02090d4d0414010b0f0409050a1d0601030b0a09030e0409060c0206090c06040b09150a03020a0e011103191b1a071b0b04020d0b011205 64
    0x5510001186003043c4440802e65030b4103120400707841c0c40d440d00050001605186400e076020f40c401c4003403004d030992800440c0320940304010465054880b404658401d07080500c03031450350281c4031845440507841c01c00c20004030351003001c01c43c10840c0240400905c00d19031b401100c8c040d56138403001080b000203100d02701d000a1400e52150f4140d5002a00403c042170000100319081a2408004034049649090a640c0c0c00f1303140e8a072580051a0483da001442134075401001c03400d1503a0b080e60010344030b007100169103450f84030071355030701c1501007100700000d00800d401000841005821806c20100503684015160000c424540229800240a644655010500c032041c00400d0a0400b90350466500d6955207000c0c0940440442e00d01c91101030b55140200c00b107035944a504001008802450303d405407692080306c800b540180143c8020030412405100c141200064118098070b079120315848450500e0b1000e0030681e0072154180300d05d00800d0201c240c0794080c0c0414800c0c0c409171006490024034090f = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 924555431 1250 924554181 924554201
    0x90c0402070515090142060503242d0319060b010903030c020f03011b030e160803091009050a03060b030f01151e0506120907090902010f12020c1f 64
    0x40d03d0a5020440c5074403d6000128071003030320100035a440c00340d0390703103446c03040f60703050030214201140d000010210b620400440c81059420032040700c040c20007001580d01705080154590146000b0100c500840094401000c1ca40c1c0b182200d130381e41100400401d0804032110180a50680c80109410a1124038000c00b07001c031400b072030056111031640c1c030010603101040c40d00910943d41d42a8110469400350005c07100f0814030390007504a00c00f40031004e8010111014170180c14000e41c55083c5103290341c4100c4c002110300781000340d480d050184081041c103561100e082010b01940c202c0102d02625140d1044000d144924000a0040c1d0502e040525100b14003001210760f070304210a1681070119440c58000b1218511044030070032010790a230522000c1150485a006000405c0008010360a403912034000c0621900740c50b00a5103c101140a0f2000b210010b40400c1c41001d50111403031040701e162800029040005081c401841203c1e4107012090440c40038101403800d501c000c00345103210341c6c0084 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 924556681 1250 924555431 924555433
    0x1f0c0c060e0d0f050c030d0513060206010b0f4b03071e11030304050a03090e041a0703180f1518020d14061e0708090312090c040207051509 61
    0x703030a40900246801400c4100280b08007243d11143c010880100603a00211100600380c540c0000c0b80c550041983c0c0003482e0031200e5220401c0c000403807500214000d8183d40b05851010300e0500d01c840c40089a0340b00c3c080f0b8034150200c1c9209015030800c0030580d000c07520360810080f1040145017107903200d0090054004050402c00b0024008101c0e0420010f80140c1900c003040c10000445a00941d54126420310010322400f001042104010000c04d01d14030302c900c01e8890064098840e904026809000c880040029505030402d00030740b000010f50f5a801135140c0303004a03424801083ea0800040907640031a028400700240c84200f2000d03681102000c04030f000304010b6140f2640e0b4850030054048000381c06001c202094105003c5901013541003144030508442e8181040341c1d00070012446a0f00d4540c4034002c24011400841c450400e45005000308c8004ad4141004505608000400a80450207510030f8a659541d6078440c3d0016000f414020030107082d907100d04101000304284002c140d5411 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 924557931 1250 924556681 924556697
    0xe0109140306130c0f0b0903071a0703050c122101080c0109060c080f032401080c071b031416093c05010306020a0e031513021f0c0c06 59
    0x54400280302d6501101c1800d50740760340d10281c00c2424081034190070040545543e00d40100e414510440203000d4010182e08940b14507564800c5042440c90842c000700c00e8030f80422034440480d1180c00504401040281134406c40c004204030a02d171944091006407080c1e060070307a02480b04505044c11401450464094104592600002014880303240a841c00f84086c20040400f80700200f000c0d24071211010b84500d07502d042c0050040428000701c000c400e6108040541840507512580e00140104042100e46081111654603401c1000845c202c050801d01c40502c00404540d0f04a600303580c401681f009400c5c081800034603481c0a0740c0d190854800309040c40d0059010181603160a005107a03824440d034180010308110744e00403a50b0400c0703101d16608120000c024000203030b00411005d4043d0b1030390110031081d9801d1607181c0e0505403101821029000000350280002c0303281c1e980d500e100501d50010714001c11444040c4200c510b40100000e02400c6000041044401080c0064030716400e250301 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 924559181 1250 924557931 924557969
    0x30f0c08100b1305040606091503060e010e0925080708070b0415050d0e06191811040e011b081f050d060603080a08061509060706021303120e0109 64
    0x90450180e201d81001680e002070226100b141c61510f103c00307400018805e0010550754003000303021410138006e2503005100310170700100701402445410200c0c0c070044000c43c41030f0310b0009400031481005000d03003c64013810a401c3d000410882d050a80304003505d4840d09650304000401c2d00d04051500801e205d5070005006002000076082910100d4400514030390750703010b4142c4100c4945c001c409005c2001ca0400c1180c081a00c80030584510807100e1000502d6103c1950341c0d07240c2a14034400001da6444040d82160740410616007181da400c000c0640301151034210009e55600710f070b0112482c805500e403207585015685a006200c01e030050f88643c000c0c40749030f2081002d030845504611865111f21598200f54040045580022008603006100c1070b440e02c0c0b240802074034810003294424403d416901c106881c001c030344e1059941c0040f001c0c1c0a203017085003560390880291b00128111200b20841d61000002861410710315a880401d40c0d6000e0340d9070310300380004d0400a07484d00314403503101d402090f503d = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 924560431 1250 924559181 924559201
    0x705030a060209030708100e10050c0d05060102030f1614030c1903180b030f090712060908090405010b0d050a14040305090a150201090312020408030405091801050106030f0c08 77
    0x1410541d04040700580c0d846581000920302005507021340407d0107002d035100406c83d11a4840e0144402000075100c0c50848050410121182194800c81041050007001a4165154041c95001c101030049920f40f20f400b50800d05690400384c1c018118a00d11031101040009007083c60390302081c404000d609100d900c0b03854680340c0d040c11440f40d48504c5041004018103200d01d800c02d020844142c050800f80c2d03240c3c5200c040316030041381c036003103203603010404a20203440004a1100301c0d000ca8000403240003103a9640005090048800c1d10f01e040d00f4000101c031552a40b040c00c0c02000206103440d0348240b40c141a10541c0c0b03004051810b0320385803c0030440078444501c5280e030301541c140f40c0390341c0d55594000080c0c1d500025410030781d05080d2440f207c1c07810b1901503100c82c01d4240252903009810b10711100741c0e0240d11540c09070102d103800603c004c0050342800010f09410040300755950000d0040207000300d084500c02d03032041c030010751541c9162001001610800c603403442686460403661625441803 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 924561681 1250 924560431 924560443
    0x12030e19110a241403180c10120f0e16030b0a0203040f060902011b05010606090f03080d0905030d0e061b07030905010e0a12050303061516030e0d06151403070503 71
    0x285941200d001c03030343d0b4901c40c42000d107012214602c202980c0c1784d04240c9141c0c1c12005006191010310b01c0384400d450400d2600c216608160a10b030f03501d000090900c0d002d408040d08055411510b084d4840e064004509424048049642d030700100701f401d800d20314107080d5801800a8801080688100140404140b0703110303200d45115005880451105203501c0101e0307801086806440070245502d4802d401c01c90f0642044007125806d5640309001900c4641200b05005d81740310041000c841040520961042a08610000350282c42a2420460f18180c1c40054503808100140603400c282c3c00c10808a5850451542030182c0170100d60900041d550050550006800b965050050001d4120b03182d50303510f0180c2000d040304440c0d20070b11050a103000b550b0303a0001d0ba20300384507590b081510b4000803000703000d482848100300c05502e1800500c0e1415201c03c0640c1e04c00d250440c3c505503062000c20307824050681c406550095078070072503242402c0003441c0c3c00071000e9203110303421507401046030359400036036 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 924562931 1250 924561681 924561719
    0xc010302070c091e050915040f0c0f06020607020d0318060b0a0801110301030209070f1707180b0903160b07021e030f06090601060c0f12030e19110a 65
    0x5980c0c075040d050074801c415040d4800e4503030310f080001c441c015003000c151914100c5603000d400c0c40b45807100ca04c45034440100100d1040300100c043c0004010440b0740c60b000388298006d04c1b03078460158a90020301c041003030f82d42081c009079102e0401c0c030443c0f0b50704005400d00180b035032a0130030802120401c1c82404002c0084003401041d100d4940c82200e42c0d034150007000402d000e0001700890848030b9903540203500244416440f070440c8600150055000300b01140360307000d041c1c0d40d58400718010030690398111030180594040113540300400003c92420350081000d041d20345581d0b5160b80440f07040625102d0003020380072507902034000800a594482e401d036403681d5411a800c0e98160480403885142c641c0c0b58468540c58401e11410100c1b45078040303000b500400ba813000351145680c8a8100b65a00f002c400c00c010196804482e840b4041201120007811000700c0b80340c0450340300440b0a5251402010030301042201c112008054200110705031380d059034003005d80d840b400b854500403d9404110303400e1b003 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 924564181 1250 924562931 924562937
    0x40507140d0b3d03030e040203060907081509070e0f0d121d0402030709031a012303031b03040501020124050d0f060204091e1b050a020a0804080d08060607050c01 71
    0xa101c001074000600381864042c0f611040e02002440402c00c140388905200540224500400c61041030815000b220300c5201c0c00b8000680c0d0703480342c44003200e041c1c200401610b000c0d109500740c0c0c4c416175504070400340100003039a58000780c14980e80800c588a00305203070192103070504e291003500141000300301c0300b0442c080b403c0c0300c0040e034440c54225900d25103803600d40380d02620000c00c1120391a00f05442c48140ca014001c3c211780308201c2582c0e090706220078003c024803c81110b0000314442c52800361001c00d00005010752742840480521150740781c64405000c02c540c0c1002c50f0500007540e0904c03a15010701015800c01d84e0381108885001400121402540e00503054428188140202d0a200e2a525503200804560703855559007088020048184200440907040740c458802501c680a40c01e070442c800420108890209c00c41038610b0740c40440000c2c1540280141040405c4603d00903200a144400181024051002c0001c0c42030500030920380c800c0000b40303d510049240003940c48080403082c2 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 924565431 1250 924564181 924564211
    0xb030f07080a1820030109080309012004150c060f090302010c030204061e020111030c090f04020903030d05190603080304142d010b040c02030705060901050705180f09040507140d0b 79
    0xc50b03204c80d02441d0004040d00356003090304040030085120015842803880380700800c4044490219010745041a00002140030001e000034007000100780902c0381c4c3d585082c20400c0046040d07035246400d841d0000032201c0310340e03a12a40502850380a001e50008004d030303841c0445c40e03d4105100603208040162a4048a2412103036100069000758030480d01070140100564803490124450f25007130303210450341402034003403010601490410b4001d8a0050000601450500c510180d0000041600400003030807070350065003090b905881c521403440614051207401e6500d00d898144011030540255a2216030740c0482945542041080301e820b12140181800d10340d420211040180035110484a60351f000b4070300040c400c03406030000010059140304100f40c501d40d80d0f03601c01c0c580c2201c60032503031040820f46c1000310346440321004052000c102d4000f00007401b40d00d41314010035034080c1d013228200c40c40c1d401010140501144040551201a411108032581030816a54502050780c081c03d00707080a070f160 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 924566681 1250 924565431 924565463
    0x7060c020f070f0f4202160f1221030609110a05030415230402100f1409010909020f0c0f1c320301140109050307030314040b030f07080a18 61
    0x1145c00d10300c0d01d20550040945414452040040c07203010050074015224248009845022841011045411800c808400c861814500405030044d8080440b101841d150f0303078503010f14824409a04d80c100c1590009602405d000f10001292043d88426840368410700c800d908250f400f8080303e910070390040410071a4540d441c520f10250004800c0010302c000c003a503090142c0b4000c0b001c900e00c114000c88242c2c00d205545a0180d403a03011000c100c000048000400b84003401c2c010004000380d01c81850881d103819940c100f40800ca800c1076140c42c41300c007800100d50114200400524000001b00c070003600480703c000400c050300c810090038400a000d082681d134090000801d924001302862a049055280c014a800e0600d56200b4080c5521a40203500d1803001944500f500500f03607040070b0000d00659055803015110b800860003094088001080301045800500f009907014000d0481c406451341440000601700c07447c000c001480081c0b0300807400e1650a070070420603034803540100c0900904044 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 924567931 1250 924566681 924566729
    0x309030c050d0c0b06060921031b0c030106060918110f03090a0b180a0b040501021608071a0402011e03181103010507300207060c020f070f0f 62
    0x10340400742482c0100707280d028206801c41203200d8290710880c40a00d25a94080410a075809101c10242d00100280c05207400401000c0001c1d0340780f8405d008480c200001707a05075403000303100ea43c824401e94014210862040c1002d004004c05031040f07081041005081c200c0021502101d91010380300d6648500da00100c000b0780d80101c42840010700c20713071035981c503107040c0d843d940f0300c41031404603000038103000007428820210003808111031241014164081654646600d13884000c1d1090b02c80355400c1081d6000da210155210014911aa9903181c880819007001441002000740051203224003208100050303a02003031a4440c4502c2110490640035050011002000dc203001100c80d504100600d070b0910402e020300700e0500780120003c0c0704a075590f20003151080c4078806d08640011000d0704501c040c0000601c00c08410741c24150060038184a5241c43c0c042c1c5d0302014114000d0f0300f0074000207041100611403000503000815204d01e0301440d2800d01c50310130b201449a610511126191320700810a = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 924569181 1250 924567931 924567947
    0x50f0d0933020f09060f090a0b04080a0b041103071e0618091e0501170f070501050a050313020a0b03070215060102031c1806021b0c0f010f020f012d020c030406030903 73
    0x1402078912916000c00105100381903007c000c9042c42200da141c40050300206007011101550b14141c040c1050909540c2d03492402c00c0c001c0c0c8115900d04d5070001d240130303544041040360002d003684000600082e9814680704900003140d00030301c1c00c1000341c180c0c109203041c104036040112048820002004609200883c045103245034160801c6810040001002461305944a03040c407040c50a44040b110302c203106070380c1c80e0014450680850403e00c882021280a80040c6078040460800d14200d100d86a00180f20200140c0001104680100500011590400c5550300801700061040e4290070020b00207581c900400c3c0c9a250001d4045040b46070030007054020380750b41d0050350032030042c10025240290203508400704800c10304c090301c1143d40380c10200103881000300700c020701043ca8000c0b00d440111014040441c00ea010352107640302603e4600d000f44107800718910070150900d2041e01107902098104040c4403804441030042c440e02424500c044200c500302d91030340c100060303d40c4651a098811320b0f = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 924570431 1250 924569181 924569197
    0x705010806210106090b0613090e0708010e0a0605070c0c0519050301090503090f010804031209020409080307030e0f0d080f090a1b030302071d0a0903050f0d0933020f 73
    0x10060910038246501508581300351488450140086c1d07070706000b1301081d4090304d5105e00090440c0141000300012523400b9400405001d020f443d14640c9038502d060a460340e00800284552000100c030052094070702c01e0f1074104c6140d20702200c15070200d44958005811602440e4814465112480c000c1100c00807500d0040c80003030001d00034000541841622034104040080c05040e81e402030114643c40381c1d6030340c3d1281e41d15840e14542c0c0c1c42318070310f05402000102000c0360000c4d901c074210404074214201851051880b03580c042002c3e840f00e0586424078600705410009030780b14841c00708105802c00f40340c5910003034034102c1c4501d50f603401304403901d40000c01c000070300240c901da0503c43c141d80003460507500b035038080c1e0201c0b080341303503a1000441c415141c0e01004032110303400408100246101e41018100714003c0c5445400d151652000c0b06d20755001501c8030310b44907521b1a140b010848180c030081b0002c00701d0300700f4040d11410361506221545e2410803218040e6400140e0364600c0040c1800d0340c0400b = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 924571681 1250 924570431 924570469
    0x91501140d0c02030705010f0b030d0f03091a04120503130b1308040308040801060503032a010915141803030601200111030a1b05160212011a1e030705010806 69
    0x381141d00c0010b516a80240d0046d45d095090002d28080d0a00780d005100b89600c025004001140b400c0380c2c02c0341c994490840c1c1c801010b4858880e000407800400d100040300441c15184e0031641050302d8000060188003550798240703d828001c00c02540701001c800b050352070300440030590070f0751030048080d0030100520b03006204040c041800700138050301c80007510660328504d000b0440c4a866504141d0707603000e1007420310040540c4c4000e83d40340c241c240c201b1203c0451810008100c400d541c0c0c0c1da001d22602e10362448402c981d03507121008900d0404401607600040d00950b84002c11420341c15054413480010a042c1c1401102814802101c9a030b50000e880c4868900007081001400304a16034607604c2030f10301d50000c908110180002045036180100400b44648540e4500051502c204142c0403812000707036845014124035181c0c070300080c01101c89510503515520f00304685201080032051003240b8510300150200c01e0b14415450001c1c0c404195182420400300e6559240e0001700c144d030100c0414020 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 924572931 1250 924571681 924571691
    0x70602160602091e09160e0a0924030b0f070c05010207050303060a05010e0307090506060408010e0a1a010f0e0a180c030b1317032a03060f091501140d 66
    0x50003010707805015004801c8800006100754406600c8038512030890a6174012080004100b030680700000d61080d05c225800d15500407070014002032001e06480d0b020100325516000110b4000c00f0b9800098411840400d00c5004070781140c540c141545001440204403d61100c0440c9041e405000c1d1010041d920900940d50f45959180c5242c4a40080d00ea060180102c0300d0081000e601410780c041d051040038005240e2540f511602034041c041c0581000c0e0852070811002c6040c5900780907035658001c03020000d01441180d85040c480c0c0c400340200f8101400c00f180d00510807056a407900d2801c480065034410140d440b02100e06008100c900e020301940c864101c0003a040051642c500703800c0b6802103159410907034982035622080c441c0d0103402004000105007540344e5000c1304010790b800180d0410001c1244101003021034542450052400c415071000c42001100d18000c004500380c2141034a003100c8a00784600e088200043ea00d03060740c1400088100288540c07071a03802d460844801440a001c = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 924574181 1250 924572931 924572933
    0x30d0306084b070b04140d030e06070501050f10180506030c0a030b04060b032419060605031f03020d020d02130609020705010509010b01090614040f061e08010311010507060216 77
    0x40740c149a00c9140d810350050b65400261301c0d8100c410750741212105c10941401009420820903603010f0060110140025210280c00305c1d00d540c00a0f041840c4a80000221420000f601040c0d00034020316a01000c098160b050000c000c00040076640d20401d0310300403415484020000c2d0070802c0d0107115940208141100006014501004a004030700450041100c10448070074561100e5103540c2c2c408007a0f1024022000e0361134a500002d600500d4003004166165160007498250751042e0b0000e80029804400d0122003008140100205800e5051694602d4590380c0405d0300c03000584000b038820204007806000f592100040440355070013640303080106a0319088a20000d4000700c40c203440355841d0071700140c1c42c2101442411040c95058460340304582c90404201c690426000d41039441100c14800000d0080b28000400e000c0c25442d11815442c10402d02003019019560041504005c05440100003081c25201c000380e181c80d0a01e03205a907084241041c40c0030784921002103004081011100c4 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 924575431 1250 924574181 924574303
    0xc0a110c0d200a2304090614100605030106170a0902030a210c0f0b130b01030f030f051914040b0d050402040e06090303060108070306050414010302030d030608 70
    0x996501002440240c0391070b0028000105418014448542c80e981180840c802d0001d034045121640100081001c103556542c103015120145d03c9410a203009200740a01d140b00300d04502c1c040e20700c601c3c209040d9031420b04000c0c9009054000c090791107080c82c0c04603c1c1c82802d504076032103d030f402504030b401240d134500d0300408a280c40580d041803417400e000050052882071070b40d150401e822000d11840c040803030b00c4000b4101400b0307000e45180350006960200140151042d14002d5001e001296076151031418080c1c505c000c03e007040800c0020400410300507035400c0c920742c0d6090b840e41c03410a5904403800c1d01404180b086d5045a40042c2c004240c454002003182c001c14071445c402d890034000180c1c0d40b4201070382c0f44001e8130003151542050000030340c59482851815805000c030b1502050842d0b03100f020404643c9050184030301ca0362408018025402c0410043c4c501c91198502001010302d8210000c1d1206241e400124200c6820004c15602d1803100003a0348030042d180d280c00d0300e0601405c80d08 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 924576681 1250 924575431 924575453
    0x1104051e091b0f06070803070203070b0a0524060d0908090a0f090c050f0412030c14060f060f0f0d1403030f09120304152a020f060a050c0a110c0d 64
    0x225001115241d5062803d007070071240c030b1410b090060716135030801c00700c0d580b002845d81001f000e0000b10300c070501501011903d500c0b101d50042e9800b250002d498180b4401070030541c1da00f600110f10100c107a5070b41c4401600e82030125440c03d8000d00000840303220614220307856104220100f039010703000c0c0e007000c81e00c04101240c00048a042010130000c011a4810540340c501800c011080c03401014042000800400c40c4501d605511074980080314610740c3d5600c400c40203203154000f0090703001204220a0350805c170582c94008000329030382e005880c9400c0004080c070044000440c040e00100305288204912800320306007a08080040d40c6d243d103800b04040c070002000300c030300352a24814568898a43c2900d801124002c41d00a00340d0001099003c0d544005080c5c0c0c80e0134080c080c7c0e80c45210340801d00b0610708040100c141640035101d40f00700900b459290080c050300664001e45000140501c82c0641c0f0201c41e0f45030720307505004490510f100c041c1810b0440400d4416000407112030600100a081425 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 924577931 1250 924576681 924576703
    0xe12030a1a061305040b190b0a031808030702010b0a030209070e0303091c0c090606050313050f121e0f030103020f060409091a07050c0c04150f09090215071104051e09 73
    0x1008280301b45402c001031580a404c403d280d1354000081842454034450041c048800b060401250380c4103242d00011807511448015101500d0100c14088080e50a01608982c1c1c841121200e40303407802c41e00001c20f1605d01808020500c07520b036904081e203031001c1c000d84d2440000141070404040000464400f400100703e821644035402500104015403d03108070390550f001d40c0d03502c1d030540e69091280c1c0f0030b62084203801c0c0c81501c5804031845c03c051080100002d400c5543d0480b03034a91948000100e182450b214545071040710074005144144600c0c41981c3c1140e070101c61144c510610200411154400d80e0042d603401790501c03181005000c00b412840c1d148111103480c03600d90b83e41b03821007140d00740146414001140c20000d21054140b03816003003e4201082107007040031840d40c2d4858000b102d0700d1580040c500075140c00d556004d5203003c5000d030040c0d250820b806807030710303a00d80c0c0c0e200503411403001c8152259075200042004480580b14a2440c40c00042449e00340307041c9a00c00315034542c0d80c400b03 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 924579181 1250 924577931 924577939
    0x18060106050a020a0215090603150f03070528030b07050406020d0c12210f05100b0301050d061e09050f16060906050c1c0c0302010e12030a1a061305 65
    0x10300684144200c03141264a94090040481c1e80d5081220300e01e10401e1032506400c1c14051900603640c1c5000850242264055a5a42001c0c50041c04081c0e14450420361181e04030304010001c0b87c4419000282041c1c100c0d00301d10444000d440380c01c00030b2044d900054405044c14040081c0301d60000020000e46820b9000c640c0300c035200700d0f401c0f2000b40c03445100820822510306810940da002e1600102010781c410f0012040d0301c003248078107044829104050304c1158031842400175011981c2c500d05c010b444d03075101e110310b558181008200700700190540180540c3d40d880c034011100c0d5070b480043d140710f500200240b020b503046003882c0d903940e82110703c00ca4050060010404c0030716019041042207410035102d2802007450410241c803281c0043c2807420b028000e0f10100ca070380c86601c0c411a0001201c3c0c1e11010f98400003428001d0031140450010b52047d40015100440c14541c0016698424030084000c0764514200051000e00c155441ca859004900810a806070f001c60b4080c210581c1c809403 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 924580431 1250 924579181 924579193
    0x70b0f010b27041e0b09010f150804031107030b04060506101209050f0a0308010e0c030108031603020a0b01090e0c0f06070803060d08030103080a14071112010603060518 74
    0x3441020941c0700d031110302022807052404004a08030100000350310000000e00000702c25281103802070204d03401d00004c60021340c1c0c54441c0e40652038000d00050140070300d2040c403030310304e410080c080c4d0649c16507043d0034007440003a4000604051141c07407415030041c1501c0c02e41308c0b640d5403894002e803042e405940440302d00e0704003000182142490300300e400c00c1c00031130f41eaa0700705c0148204494005114001c0251f50707a010300c0325401c03c048810000501058032a58500c0c2180d8546521300c201114084c00c880701d41d03441000108003020000003070f102d0301030383c8445001009020345400da2401049580041406c510607000203004c2480e80d00040c00d026500742601d61106940080210716070103080015400882440300d400401c4084011b503038002c00151a4007106101d07038807840f06a0f0400da1040743c411a000861347c4a00b640819030485503150521683c0c1000c02d1170740d0794403003281940a4140036500076141c0080c2080300750007100046400110400c500d05040c500d004141000124070800e81c4554 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 924581681 1250 924580431 924580439
    0x30c0f060516060b0105040503011d0f06010f03080f19020601060f11061519080c030709051501030f0b15041e030b150a0522050f0712020c030d02070b0f01 68
    0xe201241e20b10207030980303944905100d550310755005200c0140d0b1141000320502c0f0204e81621709201d01441407541030824510203008460745031070407001c50540074468206400400c02d2805040150050300e5021140686600185503103030400d00034010141c10101245c08034060741500480d69505a4241d81d5950780e60701c81c080c1055650000110780c00015520500c000342c5010302e081020b00f40c00c07800034101d00f00820440303000d05040c0501d4001114a03040301c2c140c49403505e8104034800003000c004005001d545001c101909001300684801030605403a030030904d1401031319600c546980d43d401011034580e80d1501c1103020280d0024001e0304018101c50104c14058501a075105e0202e962040c0201c810340e998001250703183c0d101c0a4040e8100c8a001c5000c01c0380d03500d01485800480e041c00300d5040b082d114031181e1055410141068111809800502c03a030303d603000c02d40682600100b5005607403103a854124610b03511601d4010101d8038408500c10007000100c400781405140f030500e00141c1039880b = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 924582931 1250 924581681 924581687
    0x70309150c12020408121602150406031802010c0602070f200109080c0f010c0c0308120a050f0601120c1103160b0121110105070212030d0c03150627030c0f06 69
    0x165016036111940603921201c0c6e128500c074000e0600502e00031900804052030303404109209044540503100d01004070f424080c050b40340c0319225601a400b000541140041c0d00060610f001416020b48000e800103444001d100c0c611280b5146540d102c941c18902100d0750026220072003005000c680000c0f140d070700001d00300000041c0840e06000040c0304e400740b1425200151041010341c18100d42240390107500002050001d000f6280c080d040d03c02601c0b1500c2c0581c6c88404440c2c1c014645450301243c80701340402c0e66404030ba0b088018840030345c0055001b045003002e0b00c041c00f01c07040048041c40700041c8807481910b0a0040a0b45d544a40a00c0c421a41c0b0f13182000070030241080000c141410780c582150108034580084045540f042c1041c5e46003c1050300030411403c040d146111040d4400034041c0c0151040d4400c2c01e41d810841c0c502000b000c0c080c880281d08246c4240320701e80400070796030f101a50b007200c00c16070961000b081d2801d08000315036038500781c0c00d81a8180718001014035082030000391540 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 924584181 1250 924582931 924582937
    0x8010b1203071e2102010618090c090216150c08060307080307080703031b021f1e0203040201140d05060a06140304230a150c0504050a0e070309150c1202 67
    0xe400295000c1c503c401c84491002d01c1c600c600141e4400c210650507260041d080e0032110540c00c00b980c008030b40b850a00b00800341c030034040c0d062503100c036107000c883c030012584da60003003001c0d601e0561025071b5404603c0d4107803100c0d55610402030042c400003404959201450303401061540e425885004280ea285010103480c0e41035481006d03102d070003c01002000605503002400240d20034200001c41d48072003004007210700b400580c9440940d1051003103400103c0700c968000d464904400c01804511014034010007100b07c1d0701020b619007600030000c181107a00403100d4103d100741308440c15032a199003000c11000b0306000e0362143c0c0109401500814440d1240040405001c01c40241c24915280c03540c50f180c48488804010080c50f00c100500c0c030b6080340901a00d090240103400310100710818403400005c891658a0b0b4001b400800c02c41048651140c80340d081c2200c0c42604854141c2c0e5940d00180d01030602101c4c0106024641f00324001410056440751134042d40359501d21114041000c2c6a404900c = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 924585431 1250 924584181 924584183
    0x3102010e030f1516140f1314090a0c0c06020904020f0307120f020a14070314030c0a020115060905060d2003042f040e070302040903030e0609031201060c1b08010b120307 74
    0x580e05144101d006200c170b9000305840b900c8075101510b40364078468100c0f20741490340c001524200010440403542d143c180c0c2c646400030400c40c820480740c006c00c84040c2403480048001082d8540105407a2a2983d0325415110ba100300a108a1307601c1c58500801081c0909003114101120f00e494080004e104031403003a10403010f00d64940a40f03124548440702619005208200c08200c51500742800ca0080700d0085e600900850345984d803a01000000642550100131852702d889112000c208500d070703071000c00e410450340c0640708683d640c0c00a00100c030141a83d400c043c0da00c4d400c40000900820301201c021446075002d500340c0d03c0c022100d44840c00b080d00c0720102e0240300c420300d0781c01107280345403560080c042c41061a088402c02c0d5601d90101e01940c070050384c1a000703c0e955401030b01d8a00b800307100302540464004003442c54104150552500d1600600411041281840c448402c10600d0600201782c034100c170010701c00003991141c031a40601f0030400910b029100d60712040104000c00000e03900f1a0f = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 924586681 1250 924585431 924585437
    0xa0c0e010315020d18050303100503010b06040b0c0f0f03070314030403080c1b01050f04030f021204140d061e150e010e070302091e093102010e030f1516 67
    0x1081c0580b50b03030002c1d401010014200644d5805450740301c524241c00b9214491180000c0c6441e8503080a100b002130110303270320a40c042c0e4144100c110140d44e58108840956041c84441e50304e81d48404001880d007060354483c50410320030303c490703030441d43c000001070f244040c4207a54082140c0350140c1c00380303020701003620300402080c80301d004940581078072000380c10105001e00c000c5405c0302c280d82446003564819a9401850350140c03042c00b0915511107180d0b40c01700c0942c002440040080381c54151036116601c13541e0035141c030046003902c4541da1000c04156480d04074030140420314209841c0c8140d03c117141c940342c1100345003032080c030030140c0304030b031104110307003042048408513803030040000f0341c003800140540e042581c2004000080d9407040d00c0f00d406122141c400c0589414640103020101038060030180d811080741e00001c0b088001c4800520654011980b1000800442d00c01a00e09130080c03030031558180650407084044100000d10f2201a0500d50700c00010750301e034034003001407590740350f1280800 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 924587931 1250 924586681 924586703
    0x606050a121a15040e06040e06040602070204060315050f010807080c040b030a0f0f0b091b190509070e1306030c06080705040506130806070216150c080c0a0c0e0103 72
    0x52200190b0042c2203111090550740a0549050005481e0b100d1044800d61a528046014000c81c581240341550090054404000450b9140d151540c2c800d40240000c01c0325800003007817005c54407290403036401150b00100012800031058040f10103080125003804049111400018080d84006010300480b440c2c907000e40700600882c814400940800e80c00e90390180f0606003104009041c505200c2070305401800c000e403c8600c0c03842c01c008194405070921079242d02c07010b10030b80c091000b008040c5019204907005440daa0411008203280c2d40c40d41d0046502c0315401c4101b041041c1c000c02022400907088649461043c04818914104c581c2404043d00e01ca040c2ca0007880b03580d01030403245400400e0340c18202d00b8642c6e5000001c0301e07a807285030705400302c98541078100030090080006580050690001d814816441010804011214407030460190003000309a01ca0030300880e640c105450304408845e41d80c0313070b2200d16250b8a164080e02165584c80725040080c540b1054000681a650302503a0703060 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 924589181 1250 924587931 924587957
    0x408030711121501092a031b050901121d06090c04180506010b0a0912150f0203040f170d0e0a0b010b0c150a020c01390509040e010e0f0a060606050a 65
    0x101801220304481c102c0d07202d400400c0b2802c2e811b0301000c910942d540440c8400c41002c00b800c42010503500f00e400d0042c24070031400b150780c0042c44121201100240080c904111042d2039038404598403d011440c0110070501001c22030200d082c2c80e81000640301030002e0100344800880d0309031450b20140c00f6400400040c80801e110a00410f440303078040c549682000e840701c1e21102842460030084a4848500280f00d07a1404a070040d140c0c2044803075004c500f185496102d00280032070109008000000d40b42042d4050f026050070b54000e6652440c080180340280e5480c0c503501d40b03035800180c80c03413076800300001106c54014003110030540801024158090407802c00840d11000030340b07007008154081c48003a548010910615a030307503001505540c8125200402c2d48940310b4603007080c00e080f181611480044e250814100d0351246001c0d14001030700103400040c3d600504042500d07460034058180e0503101c5400024200d11150701805003001499900e44003075a0603c0f03800d580401199200b42907503 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 924590431 1250 924589181 924589199
    0x61219080d06030215130b070203100f020412050307020f040506060409050c0f0a0509010807021c051303021801030605060108040f03050919060f090b04030201020304031401020408030711121501 85
    0x404200c241002040b1552030783d001130b411501d1404600c001c024089083c41b05050410f03d0704009080d45858289001581e40104e47c07a45d21490b0f51400381900c070140074418900e654111401030100074400b80c84240f951400a491b1741c8180e10591040520480c4e40d1030520305441214064180104024a440d2402d40c22502802009041144110051003114641240c01004001a0385a980c074144c0c0c49a044001400482c00607004108545c003e642d80d07100598040c20000c413440d440d00340282c450500100c07610300b0401c0e50700000d411005c080c540041c05444504082d050720f11070b540c2440140e03914001181c1350241103601802d1610458503e03000309008e40000c041241010341a1501c0c030a0140d260400c81000c0e80c48140040c0342090041c0045a00c800c0b10f8018041049516140c9459900001e560f03003c0d900004c2c1c000c24143c0740c02d1075a88400d504030b400604c03031681502c0d251318007401c110b41844100c55880e8010320001228168802c00440c01405000d203040c000f643d00e9081201075 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 924591681 1250 924590431 924590437
    0x302031f18051b120c09030d090e100b3901090b07032d0207060507021f06080d030e0f0d03050f090c030a080310030b0c0304170c0c1314040b06121908 66
    0x80e04179281004102450f0328140f284103c06038954540c00c20786440c203100980c0c9078000900d040c540b01e5038941c080c0301c400081401c03a81d4003c251154400154854121604403502680b41a01405031030b8028401c40c10042d003040040d103000361003508190355130882c150181c2d1902215241c40002c0000e0880750b00400d841045920302201200504081f06c41d41c6400480d001914003502682c0418802c4c3c00108646104d0400e8081a1005108951811903107959945440320508241038850001c0c1c03552a50401c404641c0510400850b4150a06230b50b000e0000d1000761040306d4600c16217000035998842c009040141280040c0040c40b80921603220f034085a0800307481d042c01800c90f0b103000004110a42e1946008400c039003000b42c2d403400d040c589100d201145545400c0084400c0c0700302c402e140c10208101002c1842901d4003c10491141600801032103403c140c0c1c400e9550b09030501050041c90410241301d84819682403503400c5002040d00d655041800794190324039407549c8030200040c411006 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 924592931 1250 924591681 924591691
    0x9180622021c02130b040e12090d0201020c0d1a10121b0b070b0f070e090414070f140102010c02060c04032405040b1021030302031f18051b12 62
    0xe0300c02c12a0a50340012010b0040c07a0312aa005500c4408020307061415201d07406c1c2c035100601c01000c0e507031442c0d040c04000d400b0b8404014800c1100c0f01d1040c0035640280014049a440202448038071000392402d01c01a41010441c00080008840041c580000f0b004001003600c001d55a003c40d400000c1d642c0c005400002c3c446400c041010700c80024604030380c1005401042c4c03083c0c0c40d1134000d00e0000000d40039404000c1030328041058000c10003043da115800c03010b8105802c03101198000703807980001498042d20358042d8907851292040042c00c00c0e030010300c0099840c000d0f402485840110102243d0360b000540700c28043c401c1c1000100002115061083c1c40c00310440000d60296495105000866030704490640d10404c410040146d0000160405800b4113403000703040c56001c1140515565502180c400202411b03800008113004010802019400321200040a04215216200c84541d2240403150f1031015048c9004100104403a52846e0140328418540d6414000000c1c1c0c0c1d9106504c0c0600 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 924594181 1250 924592931 924592969
    0xe010c120c1b08060a02070b01212010030911061813150e0405150c120c0901200a06021b030409060302090f06011d0f0918062202 57
    0x25602000504280c4900c01500e440d825140c0b8403854026020706012005114202107441007003c040000d415a103914150382c105c84030840c04000c1200384808a00613240c002c0d009000200b4000741c886a00c41c0d40018840b02919909940c0d400c940c0700340c040c5d8560002c0107202110207815010740d420000b0140480000b001e0080b20544070440c00301d1955a00c0e16210b20b1040c4d1580ea00d03c01070503600e0000700080c10a030382e0a0307e0354540352b1602a1244529040c0c00781034442003001c100100b007580140c0342007241c5110002018188815a0b090907402016264080351803480d04c0b42d00d008003c59103800d5440404041e06150482d965150000e50200c1d4203103020b04003210240d0240b0b581000508080c10301d0550000b00c0e641035004100564800800b10502002c0c00e60400295907070005464580e604140b0400308003a0707078107000a01030034180c04101c0d0400324140402c080b00300040c6020401c081c804094800c207894103048541002d1503a9128086c60951100c98001410050641c6e031629190305 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 924595431 1250 924594181 924594197
    0xa110604033501030c0509060a06081b190804050c010c050c091806011202040b0f0616020418030302070b060f03060127060909021003060f090b0f030d020a0b070e010c12 74
    0x42c500c800714071003138000f0303202404011802d04c03c070b043c8030714a907401510464032245007a00d008002040b501d00100201d14002800c40340b10841d00d40d60741518403900012701e01034440c6a940070001e1000c107003260b007580c00f0b2107030312006019075003d40411140513030410702074048e142441c0203004200c0000707080000c03040d48403070980d40900703028402c01c0d000e04414500800001e68500402040c2d42c03240e40c41e54424000402494240e50360501110a035694020813803441c602e0600020340107040721045030001980b142d9143d810580c0c542e0003092002e2140c01d568015444400a002058166021072074040d8030030740041c80349a18103500014510301107030310705106410944886081c0d450580c0903c92294448440b0400c5290043d1814130451581c6000c0040078504207038142c8104807442000c01456503996904059181c0c03c1c04640c110300d0203000c8074820009040003d64681030b080303099a0740c08080c804544100c4c4161074a01520070160340390742d50041207894800100c482c044045050190b05 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 924596681 1250 924595431 924595517
    0xf0a1b05010c020d090506250c0504020f0a090b12041704050406060c12081014040b09041b08030f0d020c0a05060a0c110a02031b06040e0c0a11060403 66
    0xb40100084082c41e0740c05400c200c1402c00c005410081c4540202d40b20384024020740481080b1282c8881800b402d038094400d0441c00c9040030040511382d50465900a8000141b1401286113500180441e038580e40d501c4003004d80d100d081c140140111019144440b5440e00480c0204d000344040c900e00314003c105e40c514050f40d46000400701c507010b900903804030301c1e01c0700880705000c00981d0200904a4a0034600700c249005200c5d076660740b1003400b8240c54001c600c003011480782c03600c0d4006d541d80e00002d00210000e041c2400c002c080826060341045214a40c084c0110740e0740702c084191090740149018403400c06c280340704510b01070b40041000c038036203101d07840e500340c08984100440c41c003891031450300040241301da4000034210303100d818058020368404400d040060318000b8a5602d0381c05440010b0b03540f40d0044000800f54440c60b800a003105d10f0040c01d100c0a0b40700300000707100e800d110780c44111081e40c4910000340c4400d07040b60040c001c00c00021541460440c2c011a0100b1642c2050340c11540c0c03090 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 924597931 1250 924596681 924596683
    0x15050d140109050a0903080c0307140f130821160f06090302070801060f03060225050d031802011205040620130b0403050307111c0809150f0a1b05 64
    0x400212000310481160041002c0002c510a030760700411200804d000020003528007034801540902501210a000000a072001e441000002c0b1a000071115403940c0380411444041e20350003000c95020000c492400000d01040e001400103040e031200000c10301e030100c4007113600c1007030b81050340503480e81424180310f4000500e44074243c01c07000f4030452000801c8152801d000345004c4158102c0c0031141e01d002001d01c007411030021104100d0780e100401580d074100078640103800d8107005200004099941e0704090400202041c65030240c5110b983c10414010401c0051440703d0500b100640402c46900050b0500f00c5141c1000e80d10601400000c551040344580951403240b400a4010104074040345020408602105010003020700300c40d110b003020f065440c1d05440b4440c0711b0000b8520709080d41e00e00c00c251901e020500041440003e0f000c4039040c142010f48041c0e0011070358620039040d007801c80900000318400e4070b151031441c1010303506084180b40190340022001c8803450311054203a10120000708 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 924599181 1250 924597931 924597941
    0x40213151e0c110303041202040222030b24060d020a0306080d0c140303160513120305030a0b0111031804060504020d0c14070201020303041106120405030301051207030c15050d 77
    0x45603502d03522a0b80c03a0400c29050801e00d0041482900704110410880114a654902e4550111001a038600300300400346c9000109031315040e6500e8113401c00005102e0031040b0b013031080402509030342c00f4500c040f0680c010022804400d59100c0400d12020030951150340c0984204452820001200c58407030440c80d10740141040804000740d03408220390100308080440300d101c541040000c60960600600c0d1b22004030303001e0b121100f00480850402030725503c80c0386038001000c81c0a0014928117035414000c0055100700c030103036245403c103200c101055115041c815440c801c070130040c50520313a81c2000101c102100046240e40b06031605004501c9686501c0180380c1c04005440004442903840c5019040c1608803040b40700d02c603004d00c00c150150340c0100407241d0103980402e80001e004242400200c1c01c0c0070390701940203002030358820801008400001076050341d1003101d80200d10300e00c884007141d0380d01c3c080c000101304910b031103404c109151040303601c64007082450402c507082401c0c074094032007160 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 924600431 1250 924599181 924599237
    0x1214070510051801090f0f170d0f060501110a02090a0b04051e060a120b040602040b0703031521110102120a0c290708060f1e0f04021315 60
    0x1542d2075052000344011510460040c0850000900c0072400b00e866291421404100c00b5040c000b075a006002041003030110300c0500340425070010b440c2c40c925060000103014440d411b40b0105c0c61700401140640c020414004603503141d000500c1c1d15440e0358280540350b2000b44c145421280c4030f241c0b0b10669a55802000d10540e0100c005088020300052480840358015116501543c2102001d0100d0503415002440083e0440c00ca01e015440781c1c40d014000780f1031984600f0740e040c00850080101070741074010f000354044041c40606142e1310b07250ba1511220000c4440c0c0540c400c00300070340d0700148002c400390380083c07814010340e075140740c0381d9162020036072007100c091002034030304000e007401c114120030210464891044045915280e20030303800c010b044060184414000020001146030303071400b1400f01454406010150365000d5a81070712060310b2801c5219200344581c100260080c00e041c400d031400306221100c1610520315088c80c545e900301403190102c0c100062103045481700000004007000d04 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 924601681 1250 924600431 924600463
    0x112d13030b060306013213050109022d0d0e21030106021506100503060f1c140a0b130809030304030c051e0609061b0d171312140705 58
    0x1e01d400300400d030500805820803149004000c8840800c01c481c0803400341b1503688801206c40c0c05030301d100001c00e20b003089094100614101000402c01b01403e8015128064040e0441c11088014100c990001030022020721003180c81031052181d800c0f150b03044410308004a9050342c07844004d403a0304011461101c0c058200242c0000010044644d041001000802c402845000c1d2802c2100015800d007e0704060303002007010100108165a80c0c0004d00e0b0107202c0e000b44000150403071144a0350f00d00d214003000795010100d15814041c0418081141d00b0041e038040420b6003907a50300b950140d02c08582c04000d88141c4024405c0403020b403010070092000e540280d4032408010310340010800c80303000050b80d20301b50880c003000d068181e4036050140d410142013141c10760340b0303181000c0121000b55000041140c0c1c511a0285440e000350700000104000d9800c580000d040e0754903001e84804290a52400814080e0100307030140c0c1c42803284a070311b4584494019540c1c503042440e254903150600c0d01c0340303080c28 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 924602931 1250 924601681 924601703
    0x80c0f091804030e120109050c04050c0904061502070e011a0c030706020d020d1a0a0303030f0e120403050c010804050705010503060d0b04051b0301091a06190f0504112d1303 76
    0x51610b00c090311417910500009203c03440b002d5649035140c0144024041c00f43c1d4540d00403444949866058610f0303040040c00c20483c9a80e94440d0920015040c0818409805407244c04500c1c00d46104038241a80d040802c510710040c0d18180d180c0d1250b00039820581a030105000312000102d080c001400e038038065030001350b25041d800703822a049804c0025041040340c03a020f12443e41e0780700c3c08100c0f004c0382c0e0582030011f020458528079401411514015030880d00410180051003210302c00a0019a4001c000711015a4140700c0103550f1218240c1d03000d042640040e03010841903120300300135a0700040140c07000405030290f07964400780c207100351070880345600195034a20f21b81714a40c606450303000c1e0440c0280487ca102c0d07150104506803583c89060181c0e200b03000951192030390b801c05000020045100440965160041c01e90b604890142c144110f0800180c140c621500d00c098520105d0f142240860384180c40c420b003601210b0b400f0410f40c00360000e026115800e080141d410005601465200d00c03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 924604181 1250 924602931 924602957
    0x60908070c08010b0a180c030b120a0c080d051c110d1a04051504050903120c0408060106021209100306170703030206091908070606180b030d080c0f09180403 69
    0x802d41d2000c000145c00b0311114207042207000f40c1c40c58007001041c10104001001d0b40e40c5c0c0821009844001203494100080c140c07901d8122400082c01c00303540d406540528400e03915080c1280d118201714201d807001032000d01c501c0301c01420605504005004030b503030006580d01100844020703500886240042c50303585400c0c1981d500300035052009000c400b260100424600402d40d4500c9111104402d80102d50302c80018911070001c1003121047e007240c1a04544d5172500c0c0c0200c8516a01c540500100c0e405003000010340389000041d1004c2c0304002d0541141080c096805014a9030300c00034806040544030a000100502c518102554641c001805081c643d03040d41006460300501030000511548403510716030249444856100260768803004490fa100c0460801350701401c40e41d003002540c00c500d0410a0000d802c140d224003c00300d030980903200c40e01c001100a50340b46c502201c0d0b041d4a0101000616064240500104a54170700144511022071044030410328600d0308650031000306e5901d680c116 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 924605431 1250 924604181 924604183
    0x907050a06090501110705010915020312090304060207120b0a020315041a1905100804082709010803070b011401032003060f0303030408071b051206012301020712060908070c08 77
    0x61317180308403801844e419107884002480d800c4284100c0d80c006241c210f189800500c280700b290704020501d1000003160030060fa0080d00c079440ba2148501600ca0900005014440894000550b0341c00c404d40348080d50b41e0405d03a00182d4401000c0045450b55800401e540340d07120311a2400c0d0780c0180c8035000c0402d1214003400070011040e11072550a0160f035204200a0b40d071500403002044a51030420566280c81c80c00c0480750244a11070f003550140380e0021040340c452401d00400421013110b083c40580d17a6a03002944074816040c01501a0000e84014851484001826600150181b50018070030982009070034844004006035a4404000028400286040c41404003000011000746185080c6903841c0e58081c41a20300040c0344440c03083d031101d840d0ba5250048801004040d2413a0400d001c48a041d07501c8003803d008038207000b1018441d0085a0105150240d425101a0010803109041555002003442400021a0110380341c0603d500003c8140b00a001324500c140d100400e2141008121 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 924606681 1250 924605431 924605447
    0xa021b0d030501140609031e07050d0f030f0e01050703030e19050102040906060e010f0804060912020c04150501140c010e0d05030106020709050f270616111507080907050a06090501 79
    0x1c01d10800b001d01c817100b0b213070303070081034003075a00348001c90030344523204109012030078290315a10290b402a1740e01d03104802d01c156145921221442640e403c0c1d03220a005000741c8514000c6241d003070000e00c1c1444541c00080c0a039000302070440954086500d8111641308150009a01542c11507482c4d401140804c150340c5107008210141c40729080260410300c4460008201300040f0314003404120021000c034050007280d502844c3c1e0203802500c0060b0780e0340f007034202a41d07403180d569a00c3c2c000c1345080140311818100001c460184c1c6e1059440614801e6502020b0350503800078424156103560b0344944148a54040101c2c1a8001e60790301d58a44079858180702038104142c0b81c9c0302441c850305000800c0030700071054400075448800c1c2c1e81c002901107000200c2009407920040f822030b49100718028441008014112224180b06030359450b1140d0288006003502c4110000900710365500410204614038000c0f00050f5001d000310044981c9285e4800008150a009a104001103401d405040c0b00c5540e01004c0 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 924607931 1250 924606681 924606719
    0x100221060102030f0a0c080f03070f031415060c030c1c090b1c02070b090615060f0403110d050109390611160f090e070e0a021b0d030501 60
    0x60104a00d00000080d49030310035020005001000000c1d410003650140d000d2212007500817100540b20f4409a45246e80e1703500c00e8403403401040c51081a1400c0c0c5209015855013080c100450a02ca522000011314440100044099000509005d2404640c0041028050300f180d000b0092013402039168405514001c5041a2000c024021800707114120502040301c0180360456901002c030501c15070054004e0085a4005203225600c02c20700030f20300d8001a019000b542c60300340e404040d0010400700b013200e110b07409441d10218000d00040001c07986003010b28040309800b4011080d54140350340c40178211a05002e0445188420102886825410201c9da01c100342c1c1d4810381081d850030b9002401d055452900c03d100403c0703202080c1154140c170604c903020070020510f120340420307a00c480c10020340f0541030041a50081c68503101c010720400c0011340c03600300c0e02d400b07443c5407a549030407c00d80c0c065440708031007001003003016100104c417000800100c4004d44195030000f40950528003030900784101d41c41 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 924609181 1250 924607931 924607987
    0x708040b04021c02040c080105030f0102181302040b0d0603051e1f020421020315040b040b0907170312070338060705030c070b0a0903020405181002 65
    0x1000001800004165040340d0115405003c8400303140c044114144503003402034001e820601c00300003060700200c500e416200200d007995070300b084500d010742c01c0b40945030b080185000800003401d0300b030420381001100d180407000d01500e40390302d03a2800305940d071010f0000e8100540e601d03410402c0c040c0502084103c0c1ca03901c06d10017201c06c032060f50360307981d0b1000c0c030603550b81c114440820101c000490342c100c4008180c0984c0c05050042c441002a1400034403040590190103000d2852108900f0340d980b2500c11948800078512686035501c6080d00f8070802001c6403454440c1d00c001084440c003082c00c5000250000c0000d554903184041c10b0744032400c0c041e03e20030034141851040340e94039110802d98085010340c6100162100c501c1e603500000301d00401080f54201c980007030b50790700744840480108070030403900f021500565070b41c80b800c4c6242d204412910000808103142400140307082c1e000300d50411000c2d80d0441c1c1105000c64424108030900070740c0c1c40f01030750015070150100c4817891b5645c40c0b503403181 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 924610431 1250 924609181 924609197
    0x60602030a02070f230d141501050d05070b07060609060b0315030601050102030d0905160b040509091b220c0503060a0f030b0c130803040602010c030615140906040509150907 76
    0x3016030300340c01240103c00891a01a0301c05c0303810ba407a02d888002c072442d040407041d4140e0000c02800358517258001180d4240380c40c010004541760803d80d1900c50040d60090007803180d80d00d07046030749106800c0007104a0308551030b04030005140b20749000d15000b034550813000c207549040034004104400c103000c4646019070801c40040005a8020094541214401b000850700600320b1070b0590920303c4004850f03400e42041c403004611040c004010304140e4505465518603511414240d5640701c04410304c00507000c000710604102d038102107080d04102854078034800d049100e00c151000070380e00030303240c0c010010b5004810801b0030314002c008c00300103000442440c074010307045441303440800100900060306500c000905900703e18040e00d04c0b8000704020015030385c81d6600c1d10310090180410140707180c00a81050300100c0d801c00c81c00e803994150300342500c1c0c65881900108100702c8603003004203050744c000000d201c0012942c80c2d420030390744610301404039583e08146010801207502d1001d4880000c024081c = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 924611681 1250 924610431 924610439
    0x605030a1502030709170105041109091c09030605090a0213020f250b0406020720060714030f16140c011b061b0810060219030305060a0801060602030a02070f 69
    0x40c00710095540c8034040c00742e52070b034440c00d0070f80701201143e101040701400728120400034034040d40098081c51044844082e4026000c00304540e00e681510350528070b4000301405240200d19000c81d00090005050500d07090341da0b5110001103840484250400f41c0052440504602c0c000c444a14030b11815442103040c1030201240b02ca00b80503100007c00e00042ca00b4004903007024401102c000603600c10b420350601d182c149440c101a400038202210545120a010704059070b4031248051000d0004d400d960401980b0380380c0140d01c081519520318640010010b01020207101c04c014405421042c003813417034107030b5a45010b1802c40c0d001c40c100001600a920b03040c05c20388c0e0148000c01c0d03110700074100300041403035801c0100c01000c0e01d00701150301d1a040c0c50021000b94100ca01b492144041c9406030764096900c28080e40c0396040d074808070b1800340c080d003400400a4003035030246422210240c04030514a4580c0300c401c2c212074180d044400540d00100d0501c4c0907503410400400507010b00303800500c140e460 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 924612931 1250 924611681 924611693
    0xa0b0a212a0f36170a02010f1d0a1203020f01110415050c01141501111e01150825030c050d0503070b0115091a0406081f080607030605030a 61
    0xc2c295180c0208070841c0a190700c0104412041c2d403404030809111204150654501c3c1680201407140702219003944840c0340b42d2600124141c43c441b40c06840c0c1c0f071240700c0d46207000c0b0703451a4035010002e10640c0c1401000640c1c0c4a06a608010300744902004200c4034080c01c000c0d240650324803078010660704000c4045081600d01090303d04803090b0741241082440340340415a200d0041c90071240803903103040c500e44448a98000390354044d05140e042100d40301c2c09a030044801208282d9005126845225541421100204415030440e428000010690310341e140341d8070030b0788240e031084881d94001040c2c030013003c0c41c0300c0c0303000d101010315a610b400340c0307103542d80e0102c0714189840b40c60b01c56421787d00c209003444000d2040318665607100b00000071640e100c50f10403c11500540c0700c0c000151800f100450840540303c40350b240c0000c03170400c0c10308080c6003203c100c0d80780c200200303580d141103404d101101507034000c0c01c407110107807040b40b014200d18907003000003c0c02c40e602c0794032244c0f00742d000c003030303003c0110b05 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 924614181 1250 924612931 924612947
    0x130909260d0f0603120503130605070e1e012a0c03120905030a0f081e03180d05090d0b0402060c0a08030108012703030e010e030c01061409060a0b0a212a 67
    0x1054101b103a102e6030350380940c1c2001d101d1400080c1040e4100010001d04c6940074039000c20645044130545500810241c00781c030b0451490b145203022030406c200d00304903200561000800411541e011400410342c41c0c2c0c0384100d4080c0c0e54412130740d9041c8030038010212a0004140805000154000c000c0450503858066036404d4034480900b018500090481c20880d60700240c1c4c1030040c003925101c1e501e080010711010314642e000a080072600907003110b80c903002d100361708854107071000501c8070203084807070f03255903c03a420081c00880e800007080183c14010070003446001082d500803c501616503140140c03450039205844a2091f020103598010040752543d05404496250149400124002400d200340e004007840c07291341c0c1c4907200202e66188204415000082541c1c2000c410140f01c4071104144812080c1c195900750b809010003805101484401c40586030851940c5840d40c011000d6a20728040c2600c20040358603000d031038400c95001511001c00f40c00d0300c038080080c500703d8804843c0c80148038031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 924615431 1250 924614181 924614213
    0x9060601050a050903011506050901080718050f0402091503160e010f030513230111031308210c180306040206041e03151b0203130909260d0f0603 64
    0x210003ca000030817514254014820a041030300700b0000c15403038074005040c58000c1004280060b0920000074241d51189e04011880c00e165400c01c60481e082404100e0118481383c0381d280c10984c2032201e89076035924800300e0b202d0313245120500d659a0405122036030781d62001e6814031003408000080740da400d90b400000c070003000540b494000f8080d22a15951103d40881d940041c181030350040c0c1e806c0804881c01c2c8950315071344400000300701c2c4881480000f00280012682150f4068a10110ba0041035130311008240982543d10360350849411901c0d03080840d001600c44105041012805481c1341c0e501e030180c3c03074140704110024203a9107803c1d0b00240391803040340180340c01841d0708280b204507044101c6048004e55803000c0244800c10b4040c40d0600280b20b41c3c00c00701014040390303001928650010080327034034030b00702e040c049510035042a0924002e080103080403200d8403120481403807101080c2a940b181c3d5004508029920910720402105450300d9a0480118914100007000046c041d1030a400171030b = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 924616681 1250 924615431 924615437
    0x40906033011420c03042306150909034803093c010525020a0501170103060509151e0a050103050d0c0c08030d0f0509060601050a 57
    0x20030481d21580e0704080f8071542070254004000e03007881c3c00c440c802e00742c1c540d8070440301c81d107074100303406040c0354024450207444480c5203140070404100411040000b400b0340017500c145001030b110211402600d0040100c0e2201d60208c0c40d8040030040d803809807409070300400b040000b50300b41070740d2a5807042e0003007007a40e606101c601e203100c00c462400140e000d0902e14003041c20452008101d2101100e03220b030322181041e07114554071612800600d10710303d0001402c0c0e60aa929074410000b801507601031030a80d0600d6414000c0034440c0d403c1c03c41c0714406c500d4000c400c01c2d00c5412901082d10502c048400250040c2d41440045848070a01040002c8214112030300400045541e454404c2064180f00040d1300c4888e000a108007005281c0d4100820b060220184084207021656520b14100c01c460080c00014442e802008813010080d10a07840e0b64034560103485c0c4503d16603510602545540d20840c1d640815a84070700318070034101c8541c42120351210850703014001c645420000209a48120141c20041c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 924617931 1250 924616681 924616697
    0x1b030f06040b0a0812090301060b040e13020d0b01090905060a02030606070f2d110f090112020a05031e190f02060304170f041e08070521030409060330 66
    0x10340c3c0d22019030340002c00b80c0805907680101c80c1d515902c10f80e44070304c162901942c01c0c14000550224194111011501480c03a0f44409440d807080b10294400c810308142c1c0e0024070040c0c4c030b03000302d20844025402030002440c009a0210540b9140c0c0c00e1040c000c0100702030358810b204102042d00c4220441c1d80c1650300c0085030380120920b00d0462803480c6603d136082442c1c1c248620310044400400700f034500c580c2c0144103000040140c0c404004410300400040c6420100e040010408100041e00c520040340c4000c2074000e9140d11640441d203010380390034152060014802000c007400b00d05003c825411484003459095060003920b80110402c1940c000a008103070020004091000101a205440c1ca04102c9103940741c2030070300c0d01141da400500039480b50b82e11240030071100c944102581400c03101300c0000b4128a500d04020040c0303031400d8210314105501c0c0720842c41481030080c001080030300306240002420b117040d4200740000c6540c1011221840b641040e21031180c02000700701c021001d03d94901211 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 924619181 1250 924617931 924617951
    0xc0305070f0c030302040b040902091507030e131407030c030b01050705031210170106090b09040c090e0a1a010303140c060a0b040f0e2505060711060705151b030f0604 73
    0x3072141fa4001203004501081c0440c0440103600100154501140c0802d00c9111800c0c00c0708940c42082e01c000c002c50741e80c440b07000003814407000048520a5401b000103003011000004010100201c071a900000d030f8880c0381c07a000c00e8043c810515140020320f0103030b081400315624151340340318404c5c54011001145000400c6011380380d1580d00641204918070b45041140d00d5101d001e00054081c40d11014200400c07007540d0f040200040748503503003020303d80032801c0c40c2c030340920000c020ce020a00c1c9079018129541e80030890303035000c204078106040c6000f4115031550500401c0940c280d141d03400d0010041108100c100381c002481a0022500032000801840007030001c1d008004101c0100495130901e031121540300000b040c01e48600306907a11508007072038540c84501101c0001d014040c0c0c0b2010074410080031403403a5421500a0b1005011079150108035215980b45c0b1010026040010359908200400031400d041801000070804000700c0c02c60800c0d0640e0070784418000e1035140215510780c0102 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 924620431 1250 924619181 924619187
    0xd170402040902030304120b0a020702180a0209120a060b0603160f020c04110d0b030f300f0a0e04180318090e0322060e0607050a17030a0c0305070f0c03 67
    0x40e41c0d5540102202d42d12079443c00c004404410580f42070b98460231041c00030300e070366060380201c1303c1d0681d005180e0154070f08900c0c180309902402030900380009a0034008071917580c40704000c0c040c00003021070061500207150f01d80300f4140c1e506689151700403001401440700c1d0007c06400455120068100301003100c400d43c0d4100d25101c1c42580da0b66000d4280b0800c1d00744912810f000f8440144080410700030782401005244d83d4000240400e2400d9015200f80c1c04000c1c5e0407403d0801c4149007015014007031540c0204690150441c0409118412000075608415504884810300800e4140d9061000f44650713a030106030354103085c10180501c8905100c0c2500e041c040e02d80c46d0050440e07420104080385004030015039039040141400121440c020400200c1c028910300c000480324a9998004055011001d01100b81c00c258001c840710b00c54150b61030002903000b18a40c0700c0314582c91030741c1e07101d1600004010030740e00c2c681c90010916180500b885149940075101d1844140507090800905c00340386421 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 924621681 1250 924620431 924620441
    0x2040f0b090f21063108030109111b07081006080706030209060c010e0f101b0f0504080a061e0515010e0303070b04080703020708160501120209030a0f0b01080d17040204 74
    0x9601e80c2c040c0100300990f100361000340c0702031584115001038260b17000051001581d83e00301c5001e0400321080c0b004010b100321540020145060000c1c4150400088880c0c0440140c81d4101034800d036000014180803241c0100192a0040200d107800d02c011881e0460241d00c034005801174000301a00081c01811503102d40c0101d51840c01410003c00c4207240720300b1060b4403150410141b450f5401585045e50050f88980074403103004c650355192905200a8031403e50320b5003540122001841000e2000040b081001d010b10070000d4014100820080c2c039109041030f140b1102e8800c881400c2c50300c0140034003800d1440c1304000725030081c04c1010036041d103440001e10318010120018000a00441040200f050640148c200d092198003114411500c07100c03540d0b2240c261810000b02c20400c01002c002640c8601200e108511205000502d0070b1078140c00720382052036039001521202004001c11007000780e806d408500500c044000780c82d4220f48040020311298660255034000e2002001107003e6580755401 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 924622931 1250 924621681 924621739
    0x1030b0109172107020a12030e03030a050a08010b0a210f0606020102070210090608040f021512040c0f06090b0c01110304030210050112080304020603100503010f02040f0b090f 77
    0x180304824502d0022940e10300900414104244030361602222460b0508159a0010b500400707224405052040151404100b004180c0030005010099070071520140300030302c2d000d003080d940c1c1d07642e9600c2e41d40b01402c0908180d001109118040004d00c0310160b111500490380e07910b019144060301d03040412000944288560700c07940e1460803400064840d0154020100e041c400e98400440814150040c0d614442a2048401003400c042c0080c4c0002da03058200640144010034040d1500b5080000c0c09160b001200d500c1c28034800c800521040c401305003c0080184641d651190036142040d000070405001d5120b0300100c0344012483c103054280c00e400589000f2206040300751130b85010300f0004c0d2b13111100c1c0c56038000a4030303020020400900e4003c01c0c80d1074542003001c030f62445d00c4507030a00440b540010f0a00805144d84803020416950a028001820109a10150b160341c100808130140175015171190302840e04c00c21018115444420100c041d030ba404454180a12000000c154054058154 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 924624181 1250 924622931 924622949
    0x8010510121e0603061514100212030a0c320705010b130c17010803090904050a060c0908100513020105070c0e0c1c2322060501031a07090501030b0109 66
    0x2c07150744804100e5102034212406204180300c594070107030520340c540155014904401102d800a50a103040403a40d07088021380c03902c115007007640024202d4150390815203003058210303150100c071100c0170340c085080610242c04280d420b000d42e41c1902103071f103c0c80b2000c084505034400400d5110512030203601c56120000041c0c50a040c0c50600c8465800605242d088400462108040402048000d41044c1d060b64000030056140c0a5544200484244001d1048a152080034100e000240d0310f40118242a041502d4100ca050b050010080c107050305800703c10300d1a4500410082456005114443c00c15028280165510340038148580c3c07015031134010b545008110030504c0342241c8110b005000042c8280410321641d00b50b00c1c0c96a0030f0b2030080d4900200104120100e03000c1c1c4045c003040503040340454008141c80c0d8040743e52060904082001030344c09035661030041061041c100c0c08400280c04844d5a500c2620700000301502c0c242d11030041a0405944c0c0446e1505079005a4580001d070501e2a = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 924625431 1250 924624181 924624221
    0xe0703060915180308190b060a030c030b0105121504140c07050d11060a1104090f02120603151b120a0b0307050102010b0f0415150503010609060801051012 68
    0x4101101001424824000e0443c5420b000e0607042c0d81d03440d004040d95a042c1d907081042d441d00a07800b041c4006d00406440f000740c0e242c010f03603059560704005200708038168a02041c08c80200001804407507402074054140807080040c50402d030b021488590344501003440d840c2101400030003240040511040c5044000c00800c14009441030050240c651607204404485103d05400400c50302604104040301055000300045248101f0381d400040c4800480c00f5210f0030030b48e0f01c400b000f0a544100100d42c10340d903400141c4444028100f6101ea501034030650041940c0820505030b00c14948c001400194801d00c41d081c40307041309018108a5403150a0f00060060700d00b014885100201610071445209210b0180c0000b910350045c080c0c1d808000340209540c1c04d04d8404010304c1b0141248030414002900c0c5440c1c0031070b040d1100403548040310803564400c0e4603503050810181c038108031500142c05110f00703040108000e60f100140b2812200f1780c0d1820071082c00c40500548040c020301030f094071904800f1 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 924626681 1250 924625431 924625433
    0x42d0203091e150702070b040909050a0618020f0f09010302090403090e04032c01020d0c0c03200307061d13090f080a0e01030515120a0f0c090b0301020901120e07030609 74
    0xa0b000e40b0003c04480c3c3e4941940728403c05076600c0100d4450300d0745902c0d082c8420005100c0b00c0d4041500e0070301401c1a40c5010030300781d4909040300d114034200300120550110100a5007068085e95800c000103503000b440d2038035568009070383c0900510000f40314000b00317400581014807480c1a40000c000c20900341040342000c0c50003405031842c01040c1d484020120b620200300381d1500c0c0154010301010380152050451581c0119191080c031803040c0d540c3d00600900000060455400e00c000c00c41b030b008400081701104003010b080c10480c2c0d100c00c04010135850550900c000d01d2110001008040311005200e010401100300545002c04028108200009502042c0000140204010030b01640e6142c614026a0f00550448105035408010324014500350707007131410030320b224640301509a07003110a00070081c1e50304403201300122400c0315803401c0160104102c242900a5200d8260218029810316992000091064001e241c195400549a42e9110800401480b410b401745810400904c15070f00d003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 924627931 1250 924626681 924626683
    0x10e070e06011e0815010804030f0f05040f0810180b070309151a040b220911151c09031d010504120605040212060702070b28030506042d0203091e 64
    0x8210358046030f217014040c2c40a240e6206400d428840d40e8561074006042d41c15000803035040301c0c400d42000a00c03c0401000c181c0300114107d201c01003150800510002441c0c1400d40140c44100c1c00904070040b940280e03000046d00080d919500ca001480c1c00541d1802c6800c18240c00340f614510800014585108085407804524902c80c901b0803c0d60705015240404080c0100d03504502c0c0c400400304007038400c0211142d5650010000f540c041d01c1d009a002007064001084581854400d60980c0f000003402c104c003c101d9459007846001c0b001040040c09a641c0303000d00b01814119681002860225001c02e2680c0250255070180c00700c00905c0c24072408600d4010000c00007914181e103d1203808424007144800010180e110306500e0b4040c00ca40c51405491810075008602e40398103007400d081d50242c604002122914010440f41e0300400d403400c100003844112400940c1002581010b9044545040e0000e881c00c00a40d906210060b5a035481d4404139085c881c080c9100014011088915002c640c0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 924629181 1250 924627931 924627947
    0x8062a091503070801170a0809241b120403081303080301090608011808122208180405011505220807050307060509030a0b040f02100f0908010e070e06011e 68
    0x649030b00c4201c89030340c0702c061b07907034541099080f103103120751040041500050050010780768000e0007034202244614001c020000c10720002c1c0202d40b100f5804a50381c0b402200c1144140b0116071034602401066004401c0c40b81a44640d0001400d03e9100003254840204031070894401550019a007a88a507158100c400107041148580c0d0728540c2441c4010112810030300c4542c03400c6a10009141c0703042a130006107400d111000300510345251208030b002c00d0000708107414441c03a078802c2c001c2c140c0c0c8072000040c1080c02542d041c1200c1c0a03524107801807029000c4503503000c04d24007450410584894410140910240064072075440f014043c03500055141400205c202c20380341e003101540e030440e80b6a501180c1d50f008071034001d5815401032103444003042c103854125070014020010075483e24030344d4020510641c80060b10f0350014082521540318158004101360260034018004e01a402c41c81c0b4800b503894425014801c00d14070b0400109020381e004080c02e02c06040074058104000d10a00303070242c4540 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 924630431 1250 924629181 924629191
    0x9060d0c020c03012003060108090f060406091e0b06060f13120614070e040c0903051b03120405030714010e0a090207020109050906060d0c11010204090b030708062a091503 75
    0x3600301007280c4140380000700c5d05094030759035003c581d042d5540c41004403038003400603003c190540143c080c110410002401401d00c140c3c0901c0002c1154416481c04042030309460000d013400403150b210250000d401c0510302c0da00000f0440710b903900e480d045541c0c09000c2c0304074a101d11084c040620001080c03030412618000d1140112010010180003107100c9202c007004981010000c0d2070071840802c80d2a0590240d000b00c03101d440c0010991743c5a94556150000c24064082900032643c9a580301d80703000c00c04a0600962009154181454440072036a201c003940207000050b4200141488181d00c50055407030f44130801402036040c0da43d190106002540400420b0f4002402d1401c08902420a000c1080c05040e026041902d403440c3d09980b10020041e801102041044896180c2d007800c001b40007a0000e006e0300000012025000d0f0105460710102d64002c03036140d0403600822801148502040e000c6042412047c48401003264004442c2e01c2614102c6a00c0000d12554090580c1420041e40c401c0f = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 924631681 1250 924630431 924630433
    0xa050a021b1e1f09390501090b0702040207050c09010e04140307030f080603010b1210060801110912101d0606030a0507060c0c1a03040516060e0609060d0c020c03 71
    0x28403007150b0f444400100340c0750a0111001ea050241c039403d5070218041030f000780c0200b2540418102241c1c40309101c101001d906541005d00718003004449640c00c8002c1078242000300a06281910401403801007050180c4600d42c040340da0018081d0500040010200c011300c0650550303101c8030380e00c8d202a030546041c3c82511300e040b906100c00d44000112400160143c482107003030804220100c0e180e010040c1460340554880100c0d142646a0541c0350189101c00c0e4003500964003869140d0003100c1741c960084696030305040d10300400e0480d22013102e0311403000f80d540b8000f03100191150382c03130000d541c1c143d4031009141081d881c0748a5108039015100401301c0054514a4855108040d50b90303040410141068202c0c0b002004903601542c42d900384203101e22450700700345603505000c141c100c50703400f00403000510000420040240c2809400b084009500100d224103090410003032200c1c1d90175203154054070000501e48415990748080e03c3c407118045030144040b41c2101002034a842860510b6030103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 924632931 1250 924631681 924631723
    0x20409060207052406060906071a16020d0201020f0d0e071809021005120109020a0c0218151801030201031e020307030b0a062a030c0516030b0f07080a050a021b 70
    0x160540c5103140a5917000380b409080c500c0003000c01100394044e8104940110340810582c0700f40c1d241251440c0b103160806024065551880006030501c020031610108591042103109800200141582c64003443c05000181e40110f0000d020300d80142c940003030260011414101e201848280c01201c0303518429101d6a0380800c60510030340d03807405041400c00b0203480604c01032002220a5010346401402c03880c5c124100242500881c0340c2c281030f00c170300d6a400744611042020b02251040b4000700d64005070b614030403410600c0d8502d00d5401041c0802030400d40c42d4a03078581046041e403c85c1c048400c1c3c46108644d82c2c02c00a0f0050000e03c406101907026031401400011003501820000d03284000c0c80002004110300e41040380130b4000e40390400c80c144124040154041403082104000741340300c50f208441c5190a40c105403140c0c14004002c40202d014100070855200c0d8800f000310f0300b205021f0008540c030b07110300010300043d0003038501c0f41141c2d820100d4054003078400000d14034850210002e050300 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 924634181 1250 924632931 924632983
    0xc0a11160515070b060405060a150804060b06090102030409110d020d020a0e09060a0e09030d091b0f120b1003120f1202040303020c061c021602100806031902040906020705 75
    0x24035000f101400f81c01d400c11040000e40c43e04050f00f115174010700c002e0815103601e89500402c01150901806500001c502030f00308820061103200d0b10000c85021548542032408140c0001e40d40c0c4501e010f282001911035803100340c0108650305861010356402c1e410f41d20b0303400501d050070080d0446c2c1da5040010300e80c4030f00d929413420f220020314060702c001741c141101c40d8140740da881c50841c400780ca41510f61004000c5c810a041103445400ca02134801c000783da00150880020001e188a0b5811038050301d800301200f0031002080700180764550f030b44600c4004495545550041c8019184d900c082e05400028034a140c090360f10040d1000604040d48030142c070041c01400c2201280228040140940d00000310451185400c8000e400c2071030000c3c254000380852110040c0603600701c0c2207000203e90781c3c0c0601c1002c624110101c2040e65685190081c0285083c1c000a9561031000c0e044060504003401300c2000d544440e00203a50307154102e030042d9500c210600d4071070350b1010f4060324001c0140c50380407514 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 924635431 1250 924634181 924634219
    0x2070302060a0527070b070507030b070503090d080711010609020309010c0311121b07061d150a0b040e030c100506100504090c0306170c030709060602060c0a111605 72
    0x5020b0340041200c21940c01181c00d02c0c85401468003016a15441070403170004178140e1020081c60010301c1600503107840746c41c524000b00d400f040130380b11005011090013000990400041e203c100313400706140c0700c001c54071a0001581c607102d001c0f1502d00b40c1d500b010808a0301010310b8000b0b40c05200d028000700a40c1c10075040031000c43e400c809020025400030041000400112890b40d40c00444100101c4250054501c0013890f50748900340440f906910745c000680c1908244240c0c0780700b8080c440c0a88a0003459254844000c000102650000c035914000f01443c7d0315540d00c20801c15091204590392404c0a10115685114180200e0402400c02c40001c11605003040c2c9180070b01840e40b10103003407906000c4200082d0804040010405a80c0c810004000c80c010b000d03131a180c100c2001402038480b0110605080038001d1b00039002150429030704001155001032690780c0528500402c9488401c10101118100090480c14180b441000d070b074080b00240401c803c404817001156500d44590780800c8030 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 924636681 1250 924635431 924635441
    0x7022715010e15030709121101122307090906060207240c060f0b04050406021801030b030d0c14121917190b060c0a020f0d0804121403040902070302060a 67
    0x558021a00885402d8083d2000e00a1070f0860340c0d600303184510344d4648010f41000000c0c08802d60728030401210b4030b0f003556003103101c1000c0c0c107000384810300150305d1040054810030084840c2c0c508600f03203c0002a200340c8507816907000360886079014042181d0703604000f566040d15000b104041a410515440c4214518140e40c50810881d00c55524440803910343c48003e002d20750090310403580780c0308007404c03656892207501d110741d1003203400603222800d0b85004295401d84031074803410b143c0741400c18100380d500052610039414492030b2a41b240f84440c600b007c1a0f00c0450192082441011260310070788000b18007a117034201012502403003440d4020003c8501ca603a040c0070304280e0701d45402040915025130b000c080117614907100424040d03481404584240c1c80b0864192803504000424011031800c9030440c618904120380c00c035080740d0b01d034452081621852003203044401100c0401c0040006407001114481840010347ea200e0345c0d2402048040e50000c00218014001d40c1d0004025440301d00c0740d = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 924637931 1250 924636681 924636707
    0x50a1b0602070e071403100503100515122a09150907140a0f050c06091605030c0907111507050706060905190b0f03010519060e0c0f0702271501 63
    0x17031030015402040e200d9030243d0024001d054080740040d00850039440410844174540f82e18503000809217032101210310410110869240315035400c0405112081d000602c0968030350340c8074820901100f41c0190886154102e050180c0c102100b0010400c500c02c603650003040888080c0c3c1c446150340c1da029000c490801d0901d039000a210300900c24809034620500241c2c408618500700f9900e00144030304224503000e01200c200c0619400b000b0020074091044400e1001480268000c10410035581d002821001c4010604400c0000102460680403020402201c5078000303824414198240f0400052260303124007415180039040c00000240e00d8a01c0c46144d1140e002001243e080d541c400c910310b0040d10001d190710747e00010800064a090b5000c0c46594041c5281000a8401d6040c80141c01e041e07498903030280d450311620b1010030910030f0002c82200c9150410002142c2d481c00180f0010310440c015100c1011187c0f1500324444190b040501800d0144203080b5501c104000b81d03800446840040103c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 924639181 1250 924637931 924637937
    0x14040b0f09240c04120c29071b050a140907050307020c1002030f0d020705122d130305010509011d070608090c0409030504030c120206090d050a1b0602070e07 69
    0xc2c44078103840001403842d8000780702005803403820b0ba076080c09003070155103e4016a540400594100044200c0342185408000d450328680680310400102e035503140076203c1c0203044844084040d00c4040c544201a10180600820004a1540b141c51200b444250317000c41c1c034020340720170021480d010b00510680c3d2117010740394001e0141158060610100d0008082d401055105c140999440701c40300001030010820240d800603260b000509181d440d001e0042e2290074482020400315601c1c145000790300d02e8a840d440c655001000540000e4150761094001e0580500306207040801040700640010f8003c5109000a00c01500c554402603082c20111492400380d50007013504004480c09020555072100c5014141e541d4031600401042c240d482004040b07000400004040c01002a0310120801808046000341c0d500c01855000c6800e0f4840c0c00c070b000d88078031141c451600400a0400c410800141d110600300c400130340c00c4001e01a40742290003040058003030740c20042940c6170300d1081c013845030030656 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 924640287 1106 924639181 924639223
    0x4020a0f08011a030606030c0d050115030e0706080112060e15010512070806041707020d0b01140d050c0105090d12020303070e01020c010c031214040b0f09 68
    0x42c00800c43c1d03400002c101c4481d402104140e035072290050390300e40d50741d0312440b0400c50300e4040c0310340003441c40d801e010001c60b10010791900340c0c40082d1030362401e014840e0310f1980c0d6600e602c418012500003032011401084840740e120b040020701030080380005490402c50a0f01400e2055000d00c80d0004030640004002038182607258400a241850242c402141010506034490201400240240a6080506480780551801c498501c0c0e4010b06101d1020340c50702d80070007100800d03c250540b03090750711402c00c1c150030140304005c83d81d944400a045920b00c06401580c03540c00c00220703244c00004030401c00f00003d60882d05108507540070740041d6280d1a046000a02401c54025500d0440d00400751b5031100f84d0b00312220300345495140c10700303009549200503014000c286c40031403041d01240d04c0042c042400581401d0394043c44c3e2511072405240e03984191240d490000c0a1080d080400b04 = true := by decide +kernel

theorem cover : BRFrame.Cov 924460431 924640287 := by
  have h0 := BRFrame.cov_init 924460431
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 924460431 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 924460431 ≤ n) (h2 : n < 924640287) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
