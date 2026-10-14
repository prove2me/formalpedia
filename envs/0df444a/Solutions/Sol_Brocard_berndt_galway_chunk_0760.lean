-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0760
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:37:54.315984+00:00
-- url     : https://prove2.me/submissions/ebf2dbdf-03f1-4032-85ea-960269687e23

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 136510791 ≤ n < 136690647 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 136512041 1250 136510791 136510807
    0x2060d0209041118010314130816050a050d02030306130e1c02071a0c07090b0604030816030801060e030606040b0d0204090b010609080d020709050a06050907020a0314070b06120102 79
    0x1d4000c440300303d22804903058840e107103000a00c82a00b04543c54904151400d80c41c2206448462902030704580c000b220441d4580b05441d04401610960401031070b80d82e040e0034804104800000e05451261040f802e0317903038268030306c0c00581c0d8034001900e2255008840c0380c0ca60075030384a6a401800c00c407141c3d40c01c44400c08221030a1040c1452011002001600000000d201000702d404100d103000304003003e603d1901901d4208107468161600480d000184c0340c80c40b0b80051f5071100145d5016580103108240e48961080442c0d000d200c100c4012400714103046e00009141e40940c4c054444500d0240140883d03980b508204402002e58826440d40902040821009600c561040e0b440c0303640701c2c0506420950522502404e0040c444d8804842c0d948241244140c10341d011a005084580500010a031a1a08220103001d48848d0b00420f0300301350340c09c08100303449600203090150035009481c0e454000088220344190703440340841c00307402d040c0158003140341402c225220319a80050300000606103410 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 136513291 1250 136512041 136512049
    0xa110f07110a0f030807021207051f03060b18090604060914090609030310090b0109050603040501020306010e030c060a0c060b0603130308060108070e0d03090e0c130e010e010302060d0209 82
    0x145080d64905401c0c460300e0100d080044202003e4a0500c80050a440c550381d42c00f0300d60310801e28000d00840c20306200310301d80c50b41001400f002d0301b0010302c0701d4501684c04500385944040c065102002900304500000c000e0320030021117100c1c00d40f0200d0100c2401c0d1400500c203980e10054407007a00700ea07582d1000a0303a1503081c0b041c0358200c2900d0f10400b9403402e085034078a14215026011712070f2500100184850071030100e05140c100c0f40d0321038010810062500050740ca4000f954800382d04103000208010400406600079071041400742c88000c005400301c01451b0f0341c2c00c50f00c1015030300000100701d8103a1f0103010f040c0865840e03100b101c001c40d04034412030100d41150002da48078031070000005c05180415070881c00b1541d0007802840c0c0100c25240caa5001006501d02154040c003c0c000460340300c041c0352007030401c007018207400d510071500d034103101c9000c03002680190340703c54110328180d80202e1034601c440503081c100d6a50980b00e52941e42150200035055006078210744140d135013004076400700d4807 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 136514541 1250 136513291 136513297
    0x50c04060602010e01061d130312181a010506041e0302030f0a03081323030702040e0607020d052a03071e0303110a0801030b22050a031808060a110f 65
    0x142d80046050016140340d10300703580030b5800c10040d500d5401d143c0031080142c984040e500001482020700302d016241004c0d55005601008620b2850400800f03251919101c1c03000c40c00d952040b00070340a4000141200002a0800c1c000c46902003000c2004000c0011705440b1100b402d011401780c0c03914955030307030b000074540348e210300030f040c10f03904010146000e00d5040107800d40d03c107150090741031040c20385a491300e55440b003540104d0040e144131107011101c444204146e87d20158090300070002c10300280f040a035500e40403564007006200c0c80800d00c840d103106405851040624014400703900e001c004440f0492000c03100d150701c0da884280321020116003441d451078080420802c5240c0090140d050080c25900351a00c01006258200509092550b100008904480d04038040846544843c080074034020402d1281c0080c0c0f4604040c517205000f40450070600c01403003511070062400340102030080d642454030645600790800f2000485031521a0020040a00d000c6002854001d40300300ca826160 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 136515791 1250 136514541 136514549
    0x140a0209190e0a050c03070509041802090a0504050613080d0e031e040503010c11030a0e12010f1b08070807080709180c0f08090c0607060902040606050a0801151407050c0406 76
    0x144034203000e859900c034820544c01c090f841710601c1c510310300a44060030340c3c419044014011699480640d03004500e030b401070b140880c3d000745005110b00b0400d01d240e02034001545c007511a40184004204041c6820760703051341031503200d007000d1b08021440603010020a041d80c1c000100707010401000e01c60b40854500e52030203080c240e94140e116070602c001d2600b1600129428030900000240ea03540186001003521210891460318098000744080446c100b45c1840100402c60343c00e003191800012440d03008021580d01c40c807400c40c004241e04c40d0807614518140e8206021442d2100812010b40c420000300f030b88150103081c00d4100070741d5200c00da0150714800540e064041c0c2e450a5140445921441034281c1c0405840e118645081100c0031541f0fa90b0300c280c0c0c00d840344a001560340100720310b54202e00300c1c240c0c008004100322035969001600682c04845840005000b143c00402c2d44203074414250003811040da40c06c04801200d04502c4c49076800360200303491500c82d00031130400326655030003080060 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 136517041 1250 136515791 136515809
    0x30a08090d020c0904110f060406051c0b100c0317011401020f0703030509010c02030c0604030809090a18062403030216140913170f040f0504140a020919 67
    0x1518068010034201019800d007001103410000300000f4690300c4041160f00705400c54840c03080d41890314005941c0e2103505d000a0341116000c100040e450b07400c900680641ca2081a00415413400c6007102002c4508503000300d50720105408602d0404e074400e03405030f100c540c03081c10800600c40d1a02a00c1e41c04110990041d9900c0d003244446840c1541d040c00322a504610b0340340180105800c55070f018040e8004c00034154100321380400d000d001d6542c01c101d00327407154402824040c4c2d240e80340c0c2005030035a1b1000c1007580c02204040081040c5000d076200f03044030409000d501100c141559950040030b8410940340450281440c0140000394a00420410081d0f101c0d400500f900d0703101d04049002c00bd00c1b5404002400c03c016039045440d211450399070b23030105040c0c801d41042c0c400f6207440662a4002c8030341c1d441d4503078040f40a10309a110107004100f034800b11000d204001c1e1361001004140e600ba51403082d00500000c0100c0d2200301076401901d040704008048030001030f00880c1d000d00c641d10580c040058 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 136518291 1250 136517041 136517057
    0xf0b06180a0605040b0f030705040b0a180f0c0903050c0609060c0613060b1816020f070b03100b0a0f110f01090302030306090a14012904060c0311010b0120010e030a 72
    0x480e107072510440d008803800343c0c1c10703070550421b4500107511202d55110703060103903491f50004203650381c40c4810351019110140101c50002c3e00000ca0308000c041d80082c00001034501a03203008110f00500078801180e90005c002c01031a201d40083c808590042c95503950404801d011080c4080f409000242c81801b0442d01d2031000e40450800c8801c2c0c495284246004880030541c0c0756501d083c05107096488280e0720042e200540d0440300482c40c2807a41f0651100d24028550041241034909008600481d2400342e100c040c03d849400003510361160220f0700c1c02084804030070800090007031807180c210031040000d65180309244240c140c00d503542980304500603000002005014940f40c50260780084002a00700810300360102112000c3c2010701403d9003d019600c1d42044001e40742406804080c02c004078680c480b80d8a140113403e5000c2c07502c2c1100840e05c07000d00252003100c1403040070b0308581c05a5403401c489401c41c80104440000f0146204a5521040d081c405140c0c20001004055060b03982d00003 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 136519541 1250 136518291 136518299
    0x70b070b0609100b121b04080a110306010e0109330e0901060815090a1b080105070e0303030a0b0a050901120533060301090f031d0d0f0b06180a06 64
    0x58001d00c010400c3d43e44044081050040c00e84882c1958061280170000740d00c60b4507072042c00080c03001d1030202904196000540031980c0c642c0841c040c2141e0f4410b8460034000d1510307208268807178009000308030f668590000108483c075000e401c000d100361392170152040040c80310305003101e01d007802c050402040090310078200004211100f0b125031055051000300701060405951a072100c030805601e8968203032200100e01d410100b0f0005442c4158400208044803210302c1280030110740c5480780109079443c11001818103130180c500c1c41d0540304001c1c040c46c995600d0300400c20041820215041d0018020f000210b820748070b00030254040c0c151551034089821203450030b24070b0f01c0741d03030700c00d40140039648008c0c9418200d080c07840080d074815407020000d04e0740d91540400d0040c001200c0c0601001c1c0640c103231406060b000b066100083e010011040c6400080c079092000c0607007a0140200041c0042c041d203000314070015102504030300c000f00199032800b1401625000b0030026110401215901e0b54100 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 136520791 1250 136519541 136519549
    0x1b0308130b070f0809060408010c0905010e03010c020d200312100501050a02031c0e0105040b07021e0304170c060706140123040504140d0203090a050d12050a02070b070b06 75
    0x3401400703a545007a00c1d10103a03a07981290f6001c14a80101000008100d84640799217580c00d980207000c405000b00036031101c03118000c2040c000d602ca00b9005c01c484003001c1d1505d0904dc005c40031030946980080c082d0b2005200b0803925018100845c003076006400280003038440013400100b5271030340c5c841000c00584c101050341003810750715030344000c0c1400410401305501e00d402000b516140c0b00007403905501c1070383d51101c00001e02803040d1595803079464070742040708120341d802c443c9015103000d90071190349084462800020424004050340203910034003003040ba16100c4894000d84007420300c183c0c0c0e5182401c03000b05801c0d07080880200c41c0307580c450710318150b403401c1c62961a0043c00d2090a000031200c1d40f000700c180c0710b409201101d004503100d10010301070004500e103100071180410100d0700d03809900301c030094a9410802d00b45100c0c0c1650351000449103460300c00841207a80211080c050207814540c19a40782d88203285071015801036541c005855401880900202405002e07800d055280c001e01300 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 136522041 1250 136520791 136520827
    0x30e060f041208061507060504060b0a0b0403080706060909150c1e050706110a0c0b01051005030712090f0c08060610140702010e040e0705011106060306060d1b0308 72
    0x428111062800300000700340081c100c042c060300b8500b40707145240c0b203110104040803441401c41c1c03c801000124102080466400303244514060842004407144020402031286107510a50035020300611050020406040051900503c561400182190f80311504001e4034103180b011380d503901c500a40d0f83e15000ca64040e50b900c4541501d001c445021003272981c42d80324040000e1400c20072201054160400c900c03540642c0d2a4840110b4550b190364070114010480d243e9100b007100d0303c03170b80354000103803600386030100320b0150516440e0103007169510041210742c1c1101e01451011191030310956008602d2042c151f000760703402900911a02424078000b00d19141014101c58081c24140141c0c06209521203094001480b140c46240e42e81e80c0c860004a4600400502070341d8840c0c40c003042c207000ea64000601d01d04a40080c0c035081c102c0f455828103a5103c02c822034109030560403800006200b1f1800c5081103101511500c3d07580015010103160400302c0307803643c100312041200050050101d04900c2c001d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 136523291 1250 136522041 136522051
    0x60b04061205280e060c0a030b03030f09010503091501090b091806070f030b120307051513060906180b01061808070b09030c12070f0509061012020c0d030e06 69
    0xc140681e05250300b5004108110483d03103407003804103881040c012007944d0030115200060400301e4190f810b004e02e000e14141d00c18410800820700e4101040002d04003c01540e86845040000904226090006603100e600003050003045001d2042c1d541d21103400203980e2030203024400c2e4000703000700c040c0062140001c40900110609042000604c4200c14005480c950025141c42c188001c40c0310f40707030b09801a00c095041c01d544401a82c3c0d01d42c10800001000d060440d0013203044400e4030007402d070380018180040ea2505128034562042001003010341e00503800b054800e91000881064021480c880c0c05022001152444490b10040104581c00100c8000c45450300c1b045001c0d03a80740c500303142c0c4e80740703810b1003184031520f408503030701050b5541441120311101c000750000c81e00e02104d1b2a1710303803a0201d6010b007141384030401101042600307000340701d188203070703405071010400b0240d00105030f1340c4800c0d000309090003036003c000380307a81e554061024204503095a06c0c0803a030702403680b482e60300741400100 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 136524541 1250 136523291 136523327
    0x70c120f030e0a050d060e0102130b2a030d0b06040905070c02090906090c01030f0b0a0e0a0515060a0c06060906080f0106120b041202070801091202060709030c091e060b0406 76
    0x9424003255617036501841c0a29840540022101640e040a40c0a4018041c1c00e0030341072201c450018002c41e00000a200d02c00c01c4411954070a041040684802c01c5414044003082d403003840008840f5039294410fa10b004801481903007000e990f0b425810940c0c4c402c0300c0717200026520145240c2141051528207800c616201c014003c681b9002c0c40c2d05039200c0507240c0c00e42c105a22152030b1945400d16511808040703001608020040f0b4440950312801303002641e91461980c0f6200004a03e2020903100090340c8400500f07062a040c0009000c40d4007010300c0c0026100140d4644001401100c9803240708000c000346030251402203070769956682159150ba01c003103451000f0a04010019001c62107280d03105030b110009180c0400c000700201d251403469004107030700e9031800911b00305201603680140b04810a41c1d0854060756a013080c12981040948030043c01401681e0003844015440d0b001440b9064070b1050440000100e2171544054807516800a000b04000040500082e43e00c80e040c2280500191 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 136525791 1250 136524541 136524559
    0x15020a1107050907031128121407210f0b03070501030603150203071e0509040b190b090111010f021e040f060f0c02040207110f100212070c120f030e 65
    0x8800f1503c0d001c002054a0209559842c02001501c0030304140d90302840010452000c020303000d10864400c4191502890124805902d0317000b0b100910301400a020380c3c415075840090b20f41d41001e9071081090080d00d00281d01041440b801c05107103120320702c220b440c500c4000c00d0064041060508180d5681c00842c100750078413000344041390780381d40c4102004c0c3c14440010307075035076542004554601001a84074603400c1325105200000368000b02514101e2000c071410072203141c8130000c101d01c00c5981e562a90700c10000e404c2c00c004008181020b081e141e81c06040c60196103076001881030843d80c156500c2d14070142e0120320040c081c020ba468003d50320b810110b1261400e410480d01d40c08400e9107100d003408110b900c403100d090540c480c0f051109040d6002d0002d54456030030745032000811403102103107402a01110005941032424420700280c050703258000e066007180c11502080103600c0040d00380c0e007041c104000003540a100c091078501c01ca00800803800254031619009144052031a5060310a1400b0 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 136527041 1250 136525791 136525799
    0xe03010e100e15010302100e030d030905070b09030d1d03031308070501081e07020102040e0f07030e010203070507020f03070b030f10090c271809030216030b0105060703090315020a1107 81
    0x681c1c03c24156901181c40003054100503604580440c03a00b050550140914a20300341c085030076030414041648140250b45840d502c90910f200c0500400602c1541503101c061032058650151281040c00f64140301049150164100070900d903038440c1d01d04040300f0350181c1c01008040000e2140d01d024207401d10700207015080c0148488002002001c80201031803041010030301d0030303000b58110340c01403c4003140c015003031400342e00b0284800d00c21954180420300b8400b81110800e0b0602c00c0300d01c100d5054890030304000c025024800302c3d6040d070482039014032030150040b40000c0b0343c03400303984100004d00300c03904e451805c1040007600682c40e40c80b0490076410140b034904030a800414a54503e0400984c68034203106040701c03060340a1013540304441c46560762030300c407030009410740100400c14065000c41d403000190904111a5580c03030b10010303211900c10001032126140100c0104001c41c02460410025502c80d101c0e540801e80001110313090079800200340e07210300d0b0010140902110080050b0084a00d8 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 136528291 1250 136527041 136527073
    0x709021c0608060f1f05030703060e0d03090206040b1303060906050615090907110a1202330408030619060305010e1609090b040207201804030e0d02010e03010e100e 72
    0x101410b005070541d0b1120801016417450300040b0001c5c00020204ea100695905183c401401010108140d5010702c3d404e44040901074050050015405040207140900c3c141c0b411209401c000c410104003105e0510010120b200d601031500441d010303140020300ea091450422005004854600c1201d0600f841040116501c0454407031303120742541031001c04440130402c1e103400c249130710b0310081c0b03007050440420300500d500142c045000281005803c41c1002007000c805400081d028200c80c80c0f800b04c50009000520020140d50070003005804111002c0b400c884c011041503181e0002400281c0c2c42004000f50f4000707126540e00408a40404510007040f0320008100c07140034025110280d8880c400c002298803503034107e9100d19000542e44541d0f600784801e001500c0c40412940b441281c070000307154151165071f09103a00071a4192a010b82440f92881441001101080c0590621241c0b0350303200c070251800c3c0a243c2c1d80011020140c4044a10807101000303c4002d800540032991025102140201c1 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 136529541 1250 136528291 136528321
    0xc1b10080c0d0902010c1202010f0c0905030718060e0103050a0203011404110d020109050406030602030906062b0201090f120203160f030f0807051e190308010302010c02030709021c060806 82
    0x200e01c5400f00b04202e05000695042c6217078100205810300c0d104981000300d5065000b00e11a4081074003e100100b040c0c98103d40969250080781ea2640000e1820009078141d1607180c04070001401d00440e8003aa100c1c2041c1c2084026403007503403141c001480c0f4100b10300c1c0a200d4051000520201c00045040507103c16482d24107548c4d16034008c0010301044410b6a01460100700104002842400008d840e4600200039410690f681951403040c0000b0a04501d4100c9100e64195210544a41005411401c9600d180c400c51000e80c140408031101289a1500c04040000342260b124210854003803807040c58a840544a407001c98854540010b11180100034504011070340c01110101740070321039080c40c03070440c4a403180c01441445007500d143c5444c1030740300141060818081c02e640350714070381c01c200300e0840120540c0140003903180c400500066000c3c0b410004010300142c01c96152507210803002049070702c40b40a00e032400d9407400115a088902c1e004540c0a8405e03e0064410b5041083c98a10586 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 136530791 1250 136529541 136529557
    0x5043f0c1716050d0e03010b030a020105121f030f030e0103090803060d06150806040b0903040602030a030203072006010512010209060406031e0c050316080601080118020c1b10080c 79
    0x103280080c0140100c40c0001804604503000f00542c0d20b41c4101481c00382132440030200d070342d00070350820b00303982400e03d0089006045160107866880c58251080d4000ea42c40a0040c0880c5003800c0e1010000e041c0c1e8407452800000d148548a040114001c605000d002000c601141070f041504000030702000921400540f60000004d40d014000a2085c4c60800098041805101c440c8a401440028440400107040b03000324041d51170040591070b10307155280c9034400c6020b502d025a00800980d0030241c400c0d8011640b00b0036902d0705240d164504e82980702c00b43d5105007401960340c41003005000c1464407182103d48002c0b01c0d0000c40c503111355200403403140e014078402d032800e265070b80642110078048901c08540c2c91a140d4010400c80c2c043c0b01010b0204d410946090400c3c16031400c100b155030b0300036140a4090441611030000503881e04004441e030001c01ca880c0200ba43d003c1c05500c0c028001080070000f160310007100c843d00d07282000240403c50030580d55230010040b40b001070201000c40402164010 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 136532041 1250 136530791 136530833
    0x90b0a06110307061e05070c030e0d031115180c0d020402030a110c01060e060a120b06060f040609080c0307050901210c0b0d0b0108100905043f0c 64
    0x24100321403040c214090780b000544511704010031540110385055aa03401c0c3c100d00c0104000540311054101c400c0c200c120001008110f109a0b5880c2ca072401c004201d907800d20915104040160b8450030034204500c40c58003404042c900e10601c00b40050010140c41404034050003004039088400015940344040c640107801240d000002c240003644540250500b00401414070340c0c2c51500d864081d009050910820380582000000b00318140342880b03600c0c0440700c5900500c00000300c0340c3c80d440940c450240080303034007800c10081040144181d801400c000c0626032100005185440c42c02420209021a00c911036000054148040c0d1340c0d98041505480411481f101417580c406d0403440071000c4400007500c40815084005041080d01c001481c18016103103090021000c8000151003d200c20341e6281c011807500c107800e04c806061a4401c540c024001d55002071140c1c81050030000c0c0c0c42240220711038200140c0c58400101d00c5404001c2945141403400200c40707195500c40802c41c00c8a4405800c0d5 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 136533291 1250 136532041 136532057
    0x102070e060d0f03080f01050405010f050f010c14070806010806010f12030507081812010b06040b0901020309100c0203151006030e0f1f141302091e010f0609090b0a06 73
    0x210b0b459012154040c00d600c0f6482503104100d0b0b080250007407500b100e000e0201060038001080608250003000e0480320380320007030203003d82004104540b80b41a9262581004410005540807404825560030090380e4034001d030040a081550541c00c0100c141c000b905564009401081210383c4140410219042c245020415020f203180485051103000e0002d001000042010040d1504141110011800440d0321046000d142c996080c01d03150a00941a4420b1080c0000c0146103041c900900c805101441500d1411800390000383d800c011802e002c04c00261046850030450404016403005c00402c42241c050918040d094510401c220b40102000c150710344504a90600c0c0400140301d00305090002e071a1180c04421340c41b010748141220b0101100d0070940002603241d101400b20340503411070102215245407075001e00c0018900074001c0c50300c0c8050001c550383c100c8052582c0501078410075094130309141c940000240070071003903044000ca880c600002c2214541d100d072300c0081111420704003010 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 136534541 1250 136533291 136533301
    0xa140405190201050f030106030c0807030e0703020f1302041701240b0901090e0a0c030b0d02030309040203100f0314011b080f04031103040f030212070506040311040b1005070c0e060102070e 83
    0x42c2c01d000703412404170035207000f20012130400e80503001141600107565411001e9034400e0011002d42344404d030281500e420000302840541490b1070420840040642402040c910000f803100c00c0303134840c0e40000e214030000c00540900030707401e0150069820b6082d10101481100400c0d2603000d0a0500c1008007052001640c0601e82c5d0040e0843c01c003d0028481ea66024984244100007402100c1114000a850412036045510700180580c1d0b07080d40160046040c14100010b10000b94005008007a0811132200c0000b11102d600d0140400380d841480700c90040700384050700b1429030b9810f0058441103220f10002608080d0300c60b411580c40800380c003a51103551298101650f400c4038a0140142502002501003540040c0c03070842d4003160303c02d5410320b0300315000410803600c072000d500401764072000c10031040000c9083c42d0f1030000074050042001036055030001c0001e42800100d04c0d114041900440c0c082e0501c18070b1aa020001c080b40003a0742098503003503000030340b2460a401201503410059000c42c07 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 136535791 1250 136534541 136534547
    0x290901060302070f140a021503071b02040b0402070c0f0b0a0e0402031008010e0a0201080f0f19110d0603020907140306040c021609140a060f030201030506180f0a140405190201 77
    0xa000780d0082c0c82c010f00c03054240211783d01c0302441141a030180c50300304155a00c204405040700e100394403960300d101006180c8140c0030841184070341c0680c3d0054492808210715900d070310040101c3c520480e600500a80740158886d07001c0c0e041c2e404468005c0042c03000c01c440075001390788054400c1c401c444c01603580d075442565000040c0e45e600320b64010343c0b034140e41c0600c6900001790040450b000b620340b184240c1d01e07030700d07980c0441d2011103d090f882004a0082038003200c00c0040000181600080810f075408000c02c4080b0a81044213641680c0b501c0d040c1c100706504140c24040c0d0020310703030307d4144600b15007001c040d040c1e03100103040e45000c0d50b074178100e2362901842400100900300b1104030f0442155a0f4503101d101070150a0a403520482c0f4441c00f0413000031440c484d24080b64030450003569158610380054004000051000e07820110403044904800704415556200700ca000c50843e071035040800c020700403980481c046880035041803051001003a0000380e103900004d0012007490041341c180c8012 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 136537041 1250 136535791 136535813
    0x90608060d1b090e1005090a1209080316060e010b0306010608060a050303070501150e1320030303070207140102010902010e04020906040302030607030209040c0f051b0106050a03050129090106030207 87
    0x6140039204881003c81d045420760451400d04e080754003119811624141041d00300d4030182d41c40c40c460f82c0310540650015400403034081e00c10703410f8106017844a5840c2c1510341158041071460320347c032543c41070754000c0050900c11042c02d8003200c4001c2022009100c082551140c040c0030f0a001e001105000034550794070700c4000e0b80070f45006010743e5141e20080c50040c2c007824540c213204040c4026610081001440403d05606c80ca210180d2041c0883c11174a1300c02c1d0407000120700a080300409414130032a034804000445c0211415070042c2440e500c0c107142c0380c1c8a8100c4881481c1164144982c22000d41e034000d0301440c1c070b0082280d0041c5c0c1c46c5d1801000402c03610039640000c0d014010982000015505039010b0284450180c800348038501b480641201c400c02e90309801c00203c2c0092041001d0f528918080850301a00100006200350700c4200054044015601c201c1e07007a9100c0c0d400841c207103020b03426450609041c110070b800001d10400000d03950034050240b1401c040e80420701c54117104d8042d04c8 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 136538291 1250 136537041 136537073
    0x8040204021308070905061f030e0a12020f0d0504050303091201090f0f260d050a0b030f010207030201060911040b07050703081305100c050615010203071b060f090608060d 75
    0x4800b100e40d80d5100380301c0d15840548a200541441d00c0005002c3c2d040050010302011a1883c4504541c05400020307001000d400e030000d0041c0c1700320301030080081c000c0f200705140440c6a8000300900c0b010000240d02d0302c01e00120301030400ca0305010230460b40d20b00000f51042d25204440c000205100040c01900601c0c000700060005922003203000c090090800c82c1c1e041e507600808052815903900002c0e4a9404056003103020700b01d508200381d10350ba040c40e60100b5040036903400003040c05840400040e18100310028901402c0c0d50000300c8104050302481684024011070800b40f141075110801400d9600a42c450304090304000a041e0341002010b0010801071039010305205d440740800c11803d08003e141e0301800b8000c40343c0c00042c8078468020a00002d501e0342c8000140096038801c10191200c58041d050721b81584814404503002070741c1d0781c4d02c0501210340c4c86580520075103030010040c0310980742140a000c2c451110014071030180d2068846512003002d4400c00b00c0e4411901d009003c0c03d40d4225 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 136539541 1250 136538291 136538317
    0x50c1803073605130203070803030103030e04020903152805010509060108180a05010f060b03040c03120c020d060e01050f1306020f07020402120601090501110604060c03090b0112150905030a0804020402 88
    0x1304140507a11940300b4034035034003c2c1c2c11521240c1c0c650b07003415500c1c4802e01001d404184000c079604030320700d426001000ca040002e020346441000c19401d00072044c20076103a00c0002000c105403c006141d24051008010300715250600071b6524140100707040a001030070050401007a80005030888041c4450020b4043d2014110340501106e41001802080b506a80c40241420481d000881e001403a00f6a400303a03800201d0784181914542d101c10b281c1d0009100b42040c07100b1444400f001d07980303804501070003038040c07800030407070001e0031405a0850700000c2039041c100101e50144140242403082003207110343d00100040c0d03103640c010307802c1d40b1500681000035481400002c078004003a201030340320360140ca400e8030344590741500e5078010340b481414001c2d04213859100b00005004101d190304166480c02c81402c0020f003014164031002d0320303c5d5090700700802002c02425424104811010040381c00d80c0d07801003c014038a282da403000c3c1c43c0c0c030601c81c9000401603050049010343d42c95904031000d1000700309c = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 136540791 1250 136539541 136539551
    0x60403020d0f0b0a05070813050f01110408060108010504080a182607061e03090f08040f1a27180108010b030606060f0910030e01050c18030736 63
    0x125002d1a880000712049600000c840d001c030301410581d000d114000e00054a404803543d407140895140074041c01020b840902c03901c200008100d50070310981c0c1c0f0092810703e84507960383c10042c5041c41c00c40183d004041d603a1500d07081001060010095800100403450815a80c0181c0350101c042500c043d0081304203401a05a90f03040f003405020710f0030f040d55142c029610210b9450a090354044c8400b28038031070283c0f00e200c40b074500d9071095010007007051158034a42000911529100c149401c01e410000e00b1003140d0101740700302d056006944859001602d0103516128000b600e040860406110020118640c1e0365000c83d01d40d10085070b01814503403401589565a55200c0c000d000e8182c052000c0d0190040d800403a001c3d0500380111042da0b8062548103152040b40c5060000b01201d074003014040603a1941e517a040d6070350a000300c5003d18120100586c1b503075420b80300700c00d01206e0800c0e164441e074015401009060040340e41e00800200e180582403442445202403d42c07420601800303000c8d5480c00c = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 136542041 1250 136540791 136540793
    0x1b08030a0504021003050601140c100c091d0712020d0b15031006080105060f031b0c0c01031d0615040e03070506220302070e0703090f0b010611070e0411060403020d 72
    0x358007140c0700340d00888509818201908094048030030581c2c0c0180007a41c4506540362a2511200400d42d0845c039104560084200303401400031510040391070b00000e200d40504000b0005c02800d00000b82c18000203140c0b00d402c0030100581034800614038407030156004070704460002800d031f0094400c604041e040398801c2c110303007490140da584201d5058032406110b41e000328419208146032410b039640546060b1804100f100c00c10515000202070a04424200d503500700c0d19034014014148442e404401044012040070001d8141d03200b002140c000b038941c010700c00d002c2c4040000d500e508004441d44190391340d9803000100d80030700f0005082903031600c000241c074030030840b0010b8040c2c8942e010122810700039126081841d08241054006030042e03004200900c0800100040540c20260700d00300004e02c246590b588580002e425407041d5207662500004020103600140042000322042c000b800c002ca08060f81c04030540c5014002810302c500400c2c81601941360901114091600109400d0184800f = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 136543291 1250 136542041 136542061
    0x9020a0306051f09061d25020102030411060a0c1713120209130209010311010c1713081f0b0d061b030b0102030307090501050306130e01060807140109061b0803 70
    0x301e00684903510301072041c0000d80710038074440c030410b5030100c20b40311480300c03101071440911200c0907041d01e18100c411b0202d030302c0080b1007680c2c44d50007c3c4d00c0e1f00090b86a00e0a800e08000c61101d91105500a80d000c110704070f4039607030112400b46020f43c040b0381c0240c00454815603403224083e1036040540c01e0041d850225440c04611403121046108070f907861034941e030f5070350712b80d1102d1014607000307411403150401803002a102c10300407580c5c6074040c50050b80b007000c0307500e41d1100c814403001600c1d41e0090004d0311022208902d04004050031078000144000b02940c900c400010001c0c1c1341a4400751741e00c6691201d903036104000003003160b40180341840000d14010f040424400703c3e600200106c0d10707050b4031140b15400131058034814000c07a20760142042c600401503940c0c0d800144003580c014055031242d5503441d481d22840910060100002600300c0c00e180c545485c0a41c00d821030244034442c04600e00c0c50340e9102c862401641c0e010301c1e040c4030021170f1540e0700e01024071410004110a00c01310130486c0c0524 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 136544541 1250 136543291 136543321
    0x3010f05030105060604060c02060a030209040f02040302120a0c1a0906040b0a12060e010302010804030203090d0605060f030304181107050703050a0303110918130524160c020409020a030605 83
    0xd0100d00070400e036100c180c1000403512035449240041141c0704401e40140c9090000f400718030415040161506440f000024200e034030311168901100d070301050034410350400507080c07581303d4070004c0101800410798540d9081109103215881d203640b100382d0103c0c0491051010780d29400301c082d060b55161501e481d40803025030880000f0100146c0c0401d040c0d850410030703000344000c56440080e802056400c5070011584e0321030050081e07042d407208116900d0903803603007983c504503d4069000040d4604101007000346a00102c0a182d100360300904c000d01580d00700010f00c140650684100051070a28000c000e01c503400354002c068020300030b1405c008280000031800c500914030a65017005201b03000208086980a841991a00100c16601c0300c0102400c0c0c00386290131011000840394401c0190351142d14200781e50004214503429600000b2074184420302003030300001c0002484509510f150301c02410100041000b81c8559155408413055450740380000c0003541e0403000070300c11460040080710381d40c0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 136545791 1250 136544541 136544549
    0x1502040603150605120a140a06080c010f020319020703050d0201051603020436021803060a0c08040b0406111215011107030b060a0b0304150c0206040b13050c0603010f 73
    0x281003108200905101c0d80b01802510b0103a120715040c907030714001343c1c0800311008010b003e281c3c1e5900c1e4204070300801c0d03000c424403a40000c5008220300d4101000e040c03e001e004c075046c0381844000d01c40d0712505031300801903c1c0a170501a91400c040c0d240000100c8c5084450790014005010b004640c07132110740e040d04003034803895584001c880041d080c502d04400724856440b8480c0d100d41a418403a85040c50115901c08200054540a45000102d2811422030b40102107002806c60084854800c60030248902980031070381e06407c0083c5885404050205000204020b0580740c1800c000b4003008038503030005001303030011007610340c0b200f410305084040450180c401c2c0d0070750038580752141032541c412880c441d5151b5a00016041c03461030366031030740450381000c3c007180e920a070010404109002d0220285128030f0081144411074256023540030102c40c1080c01500c2103401c22803c110100314244003194010030125245101e46c0a507041481c00e000503045410b0b4010b07000400010300a021112610945d = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 136547041 1250 136545791 136545797
    0x1091b0e0105030a0b070503100f170106170c01053103052a01030b0d02060c01091e03090e0402030c030a0c150503160f050c0105070c0b0702010504050619060315020406 74
    0x41c1d072207204041c0e035080c04d45002000d003814000040e103030910441c0956081100300c50510002a215607100b06413018540011103841c0c44070f8100074150743c090245c20f004080c680707a001496419511003548800600310b1381414080002400403081c80c07082400e4a04407000c5540604038106041e082032507641a1100b6075680c42030f00c0070340100381c15507800c008103441610100400300201d680103402401110030702d079520076011008080945c5a9100421321201d40900010712204130740351071032901c2c04201000000c220030f12000030000b60000340040c2a1504a0222010f42d5994030001c0e19000c8982412601405814000802c001141b00ca40003600c00c00001d0028184078141d08440500003101c544114003203008809440c10701a420200c0c83c414940f03443c0346407010494409084d070307005460000006101664020900030f1001c0c0441c3c20200d40c2c8000e024604041d10303100e171b42e240c01500d000c20b02400403ea4603042ca580f1ba01000045034488103c0807480b44040c0903500070b400c50f101301804 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 136548291 1250 136547041 136547069
    0x705010207020f040507020705010311070b040b0a1503031211090d05070e06103e060a0b040908070b092d0f0601030209040b0a060509090102130e0c0d050901091b 71
    0x2503240174000d0501c249440d50081a003945030600440c0902800c10040c2d04d80c040c104403030004100212246032165001d9806400d00d800c10740c00100889a07030355200f50143c11b400b141480040d62103001140c1000c503905012500e1180030304100780301e02c52a1412580141701004544c20004041102021107198443d4440599641410b01c41c8201c180d11b000f4000516561100e4200305c800003160003540460407414420a000307841c0c03400c031086081c50301005a44013000b000320f85111400b820200341810b030390034032032402503907100c04c40da0185001c001d10070707440200001c0001c0c4007045a0420740169031204ca40c2010610051080d0745900c0c038443e006070088580c00319801c8030001741d80303040f26409804440c0e80c2e540e070b0b26041d0340e20402805000005840d00e600140d40c2c0c2e1484240341c000c1c2040000180d4514408034407007240c218540c0b00380c0c0e200c040c0e40b0030044001c0440041d40d0135989900e40104032655074604250061101342d000170014140f5611190101e07400c3c50144c0141c540e00041c03140 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 136549541 1250 136548291 136548319
    0x5090102070906060305070e150909041e0f050c040c090506030601021002040b0a1205061c05071d0603060717070f0201090503120f0c0405030a030e1801030302160b070c1217070501020702 82
    0x1c0445925510010f41041040ac503a0603060100750154094007903220a8a108030a101162803440000c0013503410085d50a920700030b0010a00008501c0641100d00704101da444038000761100c4014803c1070311821012000035a164001c2c0802e9401c2d500c0d0380030855886031aa8101030854209481d0103002400d800c008840d12012445a0343c014007008048561451090b0321b0404e15840f9100b0840b41401020000644002c10381e803034000c90b00700521540c06501c1c00a091500e41440180700404001d40c801c403400b000c40d543d080b02c5411050364903104807882c1e020130040c0d0141140ba48002e0407440001109480c15282d4400e0a0040764040c011a400703803503c40f0000014001e80c02415456004812000e0000c1d02440c02005504409000103a0314140d00c040b480256400364410341c00750f003007800409800e42410010b20b003d1300c02590324505100c115245c82c0313008009800f800543c003074400104800c1c80840d000c07503034480c006100c19540d2010540b8156002c0c0d08501d0089010390b20f04016a0 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 136550791 1250 136549541 136549549
    0x4080709020c031806042106050a1404020f040207080d02030103060e060c1204060e060405010b0f01023903071215020a05030f0a0e1501030b0f070c0305090102070906060305070e 78
    0x6060091010003c5081c500c61091442c002c0f6000e075605a444401040006144100300382111640d0400768106607085445041220075a4802011420b20b1458000c103410050070b484070745030700303d038068540c030746140c01031404600240304840020340030b2075002c0740d40416400036400550580784607040902c4042900304000c2e6a500742500c21310800d14088c490300e02c0c00940300070001d40c407a0040c803001c034020203c41e51150030110180d40c251040d0351160402155400e00c11450b801d41c0034288024200c4003d004100250201e110000e0480214402c079004d50341d10010341922240d11008060741c0b2410340d1005c41804010407048100c0302503a00d1050022408200d1081e5503c0f42581e8403800e00d90703035400d6100140a88002e0002401903035a4030400c1c8080420041007207a40003020203941e40d5411810003103100d035001025846110051410814a9980030146620307541d41401c1140e290034041006030f050010036007204640c0303032400000050703007649600480e01440300394a0707055504e130b030071400d03c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 136552041 1250 136550791 136550797
    0x61e210e0a2105030a0207020406030206310602100905030702040c0f0305070503010e0423070909140109020607020112060e0c0a08060d230a020d0503030f0901020705070e071b0303020408070902 85
    0x801c000c540f081c0005030915003150000c00e5000d00c010b00c001403140c0c9a60000300e940c0c220307010604007002c690a62038440030440d59007480300b04010a03030751070107860480c00959034190130008080780e90321102c0b0a0100503082080d6091581d008000384821034242c540205040d5084e00c075400068284070105403014090022a4103a90444012025580e156140c0344840140d8445000a80c40d0000d0202d5021030148154006046070707400c0880c5820042c10f001d00d50041042c181e5140780d140108034401a03941a040b40d04403075083c00d00c400c980d40002e090400820783c56000d00880b03102da10403c00c0e400c140400510390a400303901d03408c1c0140c4400b000d2000c60100c140b002088800c080e040350004180c2a030001018001c1b0800312101c0b409640d0200781a001c54143c111420350011003800403c1428020440c0d0119118000310b041043c90f49a041d0b45172968882c039210f00803c040454a00b0f4461038030b0004e40640f1740d44005030039045141c02002544144904141805030050100b24079202c0d00031 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 136553291 1250 136552041 136552103
    0x31614120402090709060915051e0306010e09010b03040b040206041208121f030213020c1902030c15120c070204090302072402120a09080f010501050109061e210e0a 72
    0x4489007142061070404c0d0088e654100b42c42440b1042c07104c56042c1140b0070b603008140b40e240b10402d48a040c400f0014040300c008a001c14071440503c40144000c8501e00183d17075215410541d20441a1030301d00101d4800e00c44d6410100c0108035100c0e42c18140b01384040144202d5101085894a40d40d924001404000c000c200d50038511038000340400151414840c0c80349109071b494001441c20202030455440c002030007030340564200d890704080d01946030922a003107401505980c00080042c041051c103a0500c00e0a07400c4000d0126400400c0484a29074141c039800350303020784200040c2c40320b03040c042d5640c040d42c8504180d542a0780b05035241061280c46600728000d00f60018250b616450860b504660880c0c02e00d081003000300140002d00c84000c0040d43d00038401d02d00006081c1d41080700060181003160001c40910841188d0011980c0345215482c824021525124000c524401042400c440c1208040b000c15410440d520152000102e03080440d9807041b00c0c030001548181000e03407203800314005 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 136554541 1250 136553291 136553297
    0xa080403170c09130216110a06020f0619180f020f060901021203090c0603130308060d030f03020a02100609020a030501051206010303140c0d050a111203161412040209070906 76
    0x11403015030402c5541d80385113020245000d41080c0d40c07142c11390390705c85502c0c10941d00580d90f40f541c481a03040ca01910070240140d40701414283c1c1d40111803a0b900c80c409052004044010301541039550301c02e030711491118803044021048242c490400142000d001d1105910036855098a03140d81d18040c17045807500780042e0083e01f041c02c500f20b42d801a5410003440c843c1da60040e1103c808075541c50b01e0080d80700712406619103000c0703c1ca80c10010031b500300042c032441c05820401c0045000c00d4124001241801c0c540c0f5016a451803060400c0f0309000e440d0b5489840f8505102001c101e0341070503001340c400c1d40301c5940c0820250382c1e24810010b000c10030404200b07068000d80c005001280c494804414224001c4e669145450b040b200190300d0035045003405000a000805c6110b0300585c044100350040c8203440007004440b1141e01c480e13041d807001900d26440c0c1ca840ea180c0c4503003d40a102c184070700d06161845251540d441d003070035100e007400890f8100d00c00c0310301100080000e8003071135188040d120259 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 136555791 1250 136554541 136554547
    0x705030607051305030607081f0506070b0703020c0106080706021002040b030a02210403050901031119451707060302070f050d180f0305250305030a080403170c 70
    0x10301078401d40d2003450b1002c00d07190b0b103d030085103a407030810450340580c12966030042986804910f00c0c0844400402e100301030403002004001c5580e40106403420950820500c00641c2c843c1c2406600038070840200002075403c10000241c00c10001c00c0240883e9026004da900c200840300c7c10b50201e1003280241da400700320910103c2e44603107050780509440f0b60038200010310384145a0ba10150760390111b808600060001605209959150181c454040b10946202e801c11103003911503202443c1d846661010003450035038000d1541441200c01030152600d2401005d241044184d00302d9014106d02f42424100d00100b00081d41035840c00050507010003000900741c0c260500000314041d50060505840010b24400e1002c0410014000d810062042d81c6803c00c00040c401401c0030704982903405000a030344080e00801c040307a00441c186545020388003020070640d40150317020320200103a41000c2c11501c000b1170790009036500302040a002d0750081e10383d15843d00c2c101c04507070042141200c1c1d00c05100014 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 136557041 1250 136555791 136555801
    0xe0a23070b0d0903030209031b030d0503070f0305040507180504060b0108060a141305090604031d030a0311030d0c0f0207050d030504060305071719050a06210807170306010f0207050306 81
    0x10f5002c00e00413032081c40e01502e00954200060316190070400c40036003001030130301c105140349410000501040a83d003026401d615050a002d00b0701c606014503807092544440c0094104802849403e014013a8204205074070928505000028003041f40d046580ca03240c0f11901c1c45e158000c020322881410018101c921250604000610342020258865040500303001940c8441c1450f02520307100d000c0f0750300203003558a012b041c001d0040602400100c0c403460441c2c0081c0e41c1d40c0340415800078040d05418500c14000c0c8602c46180707103200300e0260380007640ca400c0398914015072003009800c0f0344c05150b085410303c030740b540100204005501c0006010074401c02040140c540250070242c1d0003015800d018000c0c818040c5d1441070400200c91004031402443d0300307480c40e4441031282d503400c00c136440c0f401c1001500b400d40d0354001491a01041c40058a00120f100400074804202d81c0030b030b90311140e815040b0110f1026640d083c4c0003600c04902040c0307562900004140300084900031580002d004020513220 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 136558291 1250 136557041 136557067
    0x10c0810080a0f0c0b1803010b040501030804050415030605270706020d08090c030d030e1213090504021201060f0302010f1805040507030b0904050309090c0a0f050306040e0a23070b 79
    0x551a4211030340680d04800003084024003000e0000111040344006040303c5450415003141d0111807801cac8207d1905005101050103c4103482c1036500c1a10002560041251801da03440c04e2a80020415420241004018240e00120044060380c3c41041c004111955a1035034440e03005010303000060f030010341000040b80c4030300d0035076411074502015504580106008281400000320000b0007194640700030404421003003003a104007407130800506d070078014800c0da0412001664402d02d1000c0d500e650214042d55100e5040c0f9540860b800002c0100316582c4010391181c91281c4030580c003182c0c02800d50910140958208204200c00150401c0e040c1e080508210080102500642c20103030b46103100d8126480b442402406140110025902da00d402000c00c020404002d0480109800900001d0001600220036055640f040d0500320707169075500703004c540203040c2d03203042c044180b168618031024001100c420070851260890807001c058260904e036a0b5508491140810b81e9204220411030705c41 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 136559541 1250 136558291 136558313
    0x1b060801030f0209060406080f01061e0602030702310902010e0103050f06040c12020706020301051207081c031503150507020106080c06030402030a1a0711010501151101060314010c0810080a 83
    0x5c00800000712a0b494203800d600d0541030100c6001c1680d51a0000e22851464555180e8903030f05450919450750f04003007009440c1d02900700000e01822141900d43c0c42e40c5100c00001c412007041180c0383e52817003c2540a94041c0c940c0e02d00c280d0100e128541620f220354440e01403540700305800410006103480e050103001c0200860b01d0b0b01d108000c0300d0080c10209103800c0c001000c005028500158a0354140810030401e40b855000d8619594040b04040004001c040340c0000300e880202c0d8100303c0d03c010a00198050200e0242c4141543c540442c0401041a5000351000502d07039200104145d61300c0c5030090b8226a02c5000304587c950010030214079070728004c00199031152003e41903c02ca603c4d1562008049284100c2c0d40c0103540b58201080240c980c0700e000c015000011000030f014035454080184544002c402c01501041100707851118203207000d4105100841d40400078003402c11003070307415038020722440e10f100c000a0b091402103842440d641310003c0c1aa4140030180c23000400d255203070041c002d = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 136560791 1250 136559541 136559551
    0x4030e120a0203030d02070b060a0302092802070b2e091d060106020a031209030905010c1a070503010501141206010302130801050405070e1806060f0d0f1b060801030f0209 75
    0x31140507801c200580b010310250000e881c2c02c2c900982c03070ba042c9207040000312400405c55401111407007020000341c0d0764030402c107802140080705941010340d00411114400c503481d48400302d150000520404000d1a01da040c2d1040312040e03203d103280c8000f84118145a036040d40807420a42c00d42d0f0041c00114a10b51080800d0000c400d1a85e4151501d0401141480c009a00080c0982c014003002401d154100c10941c0c1003041d8910100410115544c0c003400c00c8a482c024141042001447c0500304005501d8410180400005115407483d020a0003486903000740141400039005045240e1081c00d254262140480814600d1080d030750b030800114029041003800003100102c40100140f142001c0c811b45000301d00400142c0501c80c1000b9410304a180080c12a4807100640c1e0050381600d40c2c041440c036001317030080390101d4140856400040b0490240c4001800c6001c0c01c0b8890820442e8007103841c81d0388001c281110007860703a5000c040e80d20b601d00340300260601c2c4074501c2580051500c1c0460036408 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 136562041 1250 136560791 136560793
    0x102010207020a0801230f160e0402070b0a0b150304080a140310031109090d0c0221060118020906040911071a040501050901061d04050f0a0804060e010804030e12 71
    0x142980000fa10f10419038030910382655a0f403140b07008070844030003102c1003002944a54540781021344143c0402c44004051582030403c500722012154442e0b00284c0400c00010320035034440350380e81001c09801409aa0070300c4500d18104494071281044500616001caa40c440d0303e0450340c0e19100c81d440b40c0c1c000503209080140e04c1a181c00001c0d151405103001e0003000c0c20400c000e81c1180303072407a45082c0035a1118415003ea408001490030005000160142289400031a01c2041d20116200c040d1160b14407240da41c421a541031080000201a030480c5c00d40d03003000e507049849404034000c074030500d8402071308200e0401060051030859004043c4805003802014600a002e03103560f111002c002013001483c0c0a103100b4042400030074060150041600b030001c011480c07600d51141c03445030720074202005414000000405014040c04508107444060b4140e5054466074a40002031f40e000b8003411002c07840380d882121030782d40701d94481442150b0680f103450641204804010030055214001401 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 136563291 1250 136562041 136562047
    0x5041404022a12030f0103110301090503031501090909052a06040603090204050a050903031302010c021206040213050c0a14130f0801060504090b0c07050a0507080a0606050d03020d0e01020102 84
    0x98081c5003042540e506000ca070b480c2d41c4224a0528080c205144001c003145544030074014040c9034081444030b181100d80c0140421401603182c00820b01500110740044c04902001c8104280500d4000308201300403000d90358440c919803203510f040116003116001801603440007138203040c95541c03861800068001044030110300990b0ba800550940e005030019030010b1703107406d060300440c01e050054540042d86620140094900021074a03500d000041000e40300d00d08640105c029640119082d10826402406003a10440113191040e602c0c00141c0703003240900801d030220340865503130340320b91801620f0100c001444c0c03680b402c000f11152140401c19a02e135000800c1401d030070460400360f0400401c1120020700c0300c940303401c0030f0600310b8010340e00180c00b0b0b9040c14101000121030302207866001c20000d0081d82c441d002401e24030300c0c1a5101c2d0300140507209580c0c2c00700f001d4000064100f0124804c010074030204e611203090007035940803008000d025a00c40d0f401d41c078032a4040d81d8241483d07035041c400141 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 136564541 1250 136563291 136563307
    0x7030311100e01060509061f031d06040f051207110d0c090212010303021014060405090c0a03080c010f0c020c090c19030207060b030102040b040b16151401080601060504140402 77
    0x82102c0a450a00314142e550f03c80400503420003c4800d548490215080c20700381000000c0071010030350440e921410150740c0d44031040100c15528040703000804040c11504145080c0c6030043c1d03101800a01a2421701c1202e0755005d150b60303007000702c903000b90f80004a010040ca45905000b10420480400c403040400c01c04003040904003840541f103c078408140b80c8040b9450344c14003030708140c441c0050400d281e0030311030581a84c4200404e560340008007503070f0010300d0340d0703502400d54140600301c80300b654400342c00303071000051150700d0303001c0e080f500c202e40000c0241c402c03020100710448001c600040c0241e080b0101d814803501d8032120190f40100049000c5181520307814a18600062030712a010200b540802c0729000d22500d44211114582c041d00210b00d06030400319800c0c4180120310030031a80700c1000079456601c550680c1c10b00e8280f81c2c0010580d150300c680a020303001928540b02e0810780f0a4880e800082c1d8002c0c0011042d040390800d8031101c0c0f4050601c081ca2400105008259801039003c100e511 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 136565791 1250 136564541 136564573
    0x302030606120a150e07050901050c07090501270b01121a040c05040e010b090f0d03020102070c180c02070501140a02070b04030506090d020d090b0304061503060501052107030311 78
    0x5115000e03a000000d0313400280d20501e01e600000d50005201c07009100b081140c51034020742190003001c0d0034203200fa168a03800c0049490003043e03400c0103110380c0c104400003a090007010441494130b6003920908000c000800300000807140d89034240c40c006040c0c903800969440c2194000c071050201684c201056040b000c004c81d05554880c3c2850002840000701040388500c092070840c0074140f80102031b45041c24010001c2c41c05040046594490b11088140004250003581194480c1d41d20081c138100e01541c0e405803c030310489506a1013042c1c1d040c42600d0080b0f51000c1825020350f00161180c140070200c1d03154046032502f240c906032003540b042d51400f14030914698041d000440c07141e4010300d154a0220801800d2a410740700e8031081d58400b0a81c28651600709554406a0348010541904c1e0790f81c50403c800586456405a00b000984000c00b0050000b65080300e4140d98080c6e4071f4514205a00c45a40070404044101e420b0f0360f0070000e41480040e1081c0501040076019004503840031094041d01 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 136567041 1250 136565791 136565827
    0xa09050304051c0b0f16180519150c061121060d02300609060402010c240b0a08071a030705071a1f05060a030c020106080a03020f010b09160302030606 66
    0x5c42e4031510010b0800003808580c8208480101c50b9182401040c45a05001200040c40d030048610460754072108000c0300007042000b10040c06400080d0f611900b40c400040d04164171440c060740c029003010380c0c0055901103141151320980f0314405000550010310a51010448050b0800d17030304c00310340c15040300542c1d2400100840c0302c684180107212604c03ca0800d20130440350310070190b081c1d0088400c200360640080ba00b42c2d4055020301340262407459502d0001030700082036000b1440840740c03400c0c20110521a074414810020103030fa6200030b05450701074183d0388100d0361040b40c04100c1000700030b4031006480b20195030000d410341040350820202c1d03a580c1c000101511140034003640c5001c204907007603038180110000204504440d94155080501007000c501c242a683c40c185603e84101c1548203100f540288000c001c0041903a0300b054051500a441c1c411001001e20190b0814060341051710742202554014841100642c01c80d143e907c8051700030350002407000340c0c402c20a2210354489200220a = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 136568291 1250 136567041 136567051
    0x20409050f090d0504030f020402190519050c0703020d050f0a080d0605040b1c140d020109032703030c0c050d0804061709030901030b0d02060a020c090a09050304051c0b 74
    0x316151900901405040c031000700300e40400c0c2e10800440c001c040d00007007101c003036a41110003101c1030102400818080e00c1100240040703c00c1040b210420b596011024001500c84503900e50022026803200320ba1030702501c44010204d03044240200018640300000d0540207200d41e040d2000000c0507171079130782800c0340288242c944002c0050a03c10017045071044001a15040301c00300410308011002c55811100c0700b04e02c6501c0c0020113408424801c50b4071400d9002e860300421501d103510494030090213051b09110860105003000880c41c00c0d03401180184002d41310007000041040d1035600d04441002041c03205071901c030072008000c03170709844903060800b02c43c5c0111341040d0341d2454481c005240710700d414030804a6007400300a115020b0004000c03a2019182482d0201d0510085000240c58910015000358402d01c00164420b0b110b0300804d0741c005e240401c41c1e14034129610b040b0120240d82040d00c004007950000c00042c0524034280d0201c0c50316202511003c450004583d58071600d00e0006c1c3c80c = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 136569541 1250 136568291 136568309
    0x141012060b0a02070801050919050f01050a020a090f080604030f1106090d0f0509010818101e05060d0c061416060906061a070f0302030c0304030c0f0b0c060a090203010605040204 78
    0x400350b0b02182c04110312002054000000c210138076140c0441600c401c0300122404d54040c03128209814132004000440f94011200c008000d00d00701040c0c40d2000703501803ca284003045180d10006001d4044000c00c100300d54103030010b0082c0e65503c0d5002c0b41c5070f400140c0d032141030045060307096500160402425201c0e100280c0100120500382c0c10144c82d41c01516214820000c0821a040081c1d078400c901c2900081b905c1403600c00c03020000d002d81c6c20305e04910301184500b07142048501000104100814040d0204201048191035071000c1c042e440106240c0a081980325080c10002c2c18820700e00000005540000c00d810103801c1c1c020012944100c00c81502c0981d12180103134144002407003100002c003180c0b69910324000c1126103000c824090040051311403d150009181858024001c440b0841101030969a0319902d0386801d4101c0c040901545003422a48403011031800e500000301c0c0c00b82e509040c000e0401c0c0d03030f82022000190048110480e015520389a00152503140c50000d40007801c2207207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 136570791 1250 136569541 136569547
    0x60c1603030801030c0b090d1101030e12071202070b0a0c020a030c0303020a0c0b1e0c10020309061602241503100b040e0706090509130209010608150901141012060b 72
    0x810070611300c4001b6000040796000401422000b40d03a440d2249284903444480020b0104c6a07000680050100c4003411070640a0490484803030324140d03000f807130502e128a49a84a0b100540c1049940321001c3c00340180181c41040181413460240050300007a0744000c0100d0400381c0c03030396151040c447d481d520031005a803004140310100106000040e016000042440e810018030444203903801e00d014400e0815218000380c101c4028409210010710150601015076403400e04d05001556903908454060003007001e5440c40d180c0d94400300b08642801a5a0661003105541c0f01c1d00c80c03802c1c0702c050440150380d40d8001c43d40145803401d0200b585407000003000080c3d4101e00703105010a40b403900003a022a9004a60705004c45c5402c00030441c207440b400c0d076223000544e80c0c0c0c45440701015014038000e5402031941d4000914550b1000e0543c2c415081c0042d1200c047c40704100f8004449400c0c0a2000211a80c540e80c0103942068541d41801020b585009600c1020003009041101d48a4002c446110400 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 136572041 1250 136570791 136570793
    0xc030a02130e0a0513030207300c0e07050403030e0603150301140702121303030807020f01020412031214041e08071202060c0304030905011d13050708060604030503040302060c160303080103 83
    0x1e88544c591080d8405021000b61002d03540094944109005080c01084448111480000740fa40d005407996070403201201d522040741400d83c2402c41602ca20918524600002080d00e44030b94156801c40340d00da26407410100d038200800126400c010711040c507021668040d0b40c8030f0395003400307060004140c07409281c9441c206958002c0c2044100601045607140c104900030918841110000c00c6a80500d001d10081d12001c400728100b075005406c19150b503001140c08540049450000307407603e8841d07101c0f9400705d4031090015060300d000c44803001b0f15000500010300480c2c0d1140800d954140c14404c28201c001d0280d85d901400d070001c000070f072a840701c58200c1d0011950100300311504484100079890031442c1569004241403041d008603070400114108100708840182c5a130308107580001c00032102003001880000c005c1c00700f15007000014001e00080740183c1440b85c00c95003030300d070414045d51a00c2d08540a115550b448680c00c55a00d1081d42c541c68002000f4400100143d80309540342503180d455 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 136573291 1250 136572041 136572061
    0x150e16180f05180c010f022d0304060819060605160215120a0c05030910110706060e07021b131503060c09180501050a03020f041b210e03030c030a02130e 67
    0xe104c0d0541032112070059001e809400140c80140c4c165207520303020900c40b502000032080020300c0c0301070b581d9100202e004174800341c1100407035105a01c2e404520040d20040d18100341501d119200d4135011590400c044a8402040945c3c10011400600240c85180e26404c9180b0b460340202600c0c01800488014458562454001c019059566140003821401c0041e100b81c0c41d074030941c1c1454805c0345e40d000034078984800300c000d80780348640200c0c1c204101981c07040004044042103651100500400c000c40012105a03044e8941c6520042c105000358000c100115008100c0d064625054084d217000c00000151940114202010280d8580c980380e0f142040d10103080c44e07140b110042040c00d000c0140400d13201c8407841000c50f80c0440303101d0300444205d00810001e10114507415024840c14202c001c18a4008400c10308c0c5410050042e214903030408014030485103501d0706092242c00410100c0c16000992000d5074100302140c1c00180351030041c0036001403401d4564441d400d10070b0104100700b2040e2b1 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 136574541 1250 136573291 136573303
    0x9070e0f0301090206030c030a140c0a0e150307050c01060308070309030b010906050315060609040501171009080301090504050316030201150b09010807050a02010612150e16180f0518 80
    0x541600207004a00b81c03a4001103171400010441c4800c81004000500201e220b50805000301841ea0300b0500309051007400c91550380e2000d0000004a400c0d000d00a2050505240c150044440701107150f0440e200c1190403030b144e601c8102e103256030350f407100b501001003000000200350051082d26584600c6165181140411a05901402c00d10340303025401c00580d20302080e0b18201c001c0203402002540c0d03d000000b41c030303402100c107101e03001480c2c180003041c0d95004a505169010f003050840d140070700d2103109802510058a001042d00b1014001048510341c40e80009800a1052050b2801c0411a02d000c100d000c0303c142d41940180e44403044103174195090717402034000d0322050403101d107003030003c80c000382c9008000f030803180410000180c51a8031901c02e512290140460000740320601d4901d0402c91109161101032800d020700c0c042c40c071651040c00003001c50881e00000c030760b08680b0f0f01c2c0450106c40c96642c08001101c0c141c0300c0c82e851003101d03400d00c07a191041189590b0320700d81851006590f4a050 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 136575791 1250 136574541 136574569
    0x70305120a08280203072109030806060715090201050c060406020a0f110d0c06060503030a030605040c08010302210307080a0c06060f0b09060c030702061b190804060305100509070e 79
    0x3070b080d20044891420190800324103c0380d40d440035a407502c580c101101c2da020000407103403403982c090703a0080480000da0084000c0502959a221507138940c0c10030004240300d4801c0c010300361402102c620400790a9500040031032801410030900f06644480341c41d00b003c0c0d0032a800c482140d40028000c070000e4009c0c6c25001d4441c018640b07034541d080e100c06c0459469040768105000e0200d5510003c04200040e0860405460050180c98840c0702c00507014016011500510344500d08000400221501c107178856412240c00400d0280010703110740c5054143c414100003044280410401c05012400840062121040d15074594125494a041034011225640c201800240e02080100301088942c82a1103201508460b00740d9540070714840c082c07171072281000c02900450701240c1c110f2001104201e042031b18081005407201d60305405001d15081c404014024609801070105110b402c1c46a8407103a0710a01180c08401c03280d4540380001c1111000321044c40c00110520240c1d005410101e80c0f0703072101 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 136577041 1250 136575791 136575811
    0x305070b010602070e010320040c02100b0603041205071401020301060f020c12060a020f0d090c050a080a050d11010e010e030a03060e0f0105010e18040848070305120a08 74
    0x4c1d6003001c0f03901d107100b1010322000d007a04016944954800b41131000040d405000100100009403602c1400b0b91078104141c4c0320302c0c80c5e601d0031031505c241c1d00742001200d10481d0b000c0401c1500036a014025981d07a040800240c8065200a50910500c2824401980601455201d103032460100e00b00091404802510740d9000b000c40501c058080c0c20001030347c41c0c000402110150702d0300c01481c80041c00f4090703000ca51010909020580e018415040c41401c00d0b2101500d40c50300091300c4600d410f66410314400c0040c0b190b400f442d61103200c03921565110103001121800420301d00f88410800e400c3d00c0440b584035960b40c05c00a22107007490303003601c100c0c4000c02109110202c145010100c0000044052280b58103221303080c0313490a03d554640200d0f2641c00400340c07541000f402c241c20030141e103402c9408000da0740844038840e451a0806400d0843c2041c40c00b0f005642c0241c00d00d010700301020f9080c0b8203105640325680000c0001002030064031202c00c0d039849410740300c54032030740b000340700600280214802d = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 136578291 1250 136577041 136577053
    0x4110403080403081c020c21120f090105071d15071a01081c17060d121e09030f0609060b04090503090a151b11090a020901171005120f0102070305070b010602 69
    0xc0300e0b101007000810303140c5e40808c1743c00f07060b425030111503144070b141d402d26400354803102004001d1a203503d00900882414008002503900c045041d210104401d115040281282441c645545010b04169000d000c103031240e1402c0c0403056071a0401e000304501ca4040307602c420001801040020042411040d0303481c5501c0c00001b00111025000c047c0d0910208d070b0101c842400104030380c03204410300e500c540d4000741266a518046000400844001d150b076000c4802414642e0841403144140200b07070381d0400b12412017071031075541c4d0400811780310b8400c807074182d160a80214280d80d10700c1090764550140d405035603100380200810065100a40152074606265030320109903c0c0c1c840900807140c0620f101068180c031300c6050601d1400c0c1e61302626940003410b1820840d5501694000e0441c24a080c6c98041d11403140c42c00c03496131079004850701c102407405007004003c14a031110f00d4180760038640007075450204c90076003240c2c01e9070700821094020605c0054440b00b0020004c105900400031031000d409 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 136579541 1250 136578291 136578307
    0x103050601180e1806010f030b010603050714070c0312020a0209090102030c0301031403070b0408071209060f031113090902100e0907030b03011409060702010e01180204110403080403081c02 83
    0xa8012164002c08100d101108001341c04030b44c1024501500242003c200ca9403980d50398801c91402c4441e001c1207501104000000500783d001340111400356503c0e40340c504018100c0d020107180d6402092082d40c1f032812070306001012407000301c2c86110003086c5034041c02c400300282c01806842c0d50041d1511240f07070310410400c98a40804810303a41543d520480103402c0e07044800c2a2481c50103001c601400d800780083c04c0c0010441e50400401c00030b8800c404044d00e41450340000c0d91090ba0714071542011804d4402014078092003503104900b180522854281000080d0054258002d040c1e0001d1400642e1034000348158903281400118565880c034000c2d601c00c01490200350259006815201407585942c80c1030501d1741c081d04880700194bc21000841245020511207036212000d54400f0059440c010340b080309501c0c18020000c9140c80c80c016101e105c00540c0c00e100080450401090741203400348004030000388108014001036000324241e81e1540c1c01141c10085000c5400d030888049481080050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 136580791 1250 136579541 136579577
    0x4030c0816150e2b1110110706050a090305030a050901120e15100e0c0304050106080d0e04020706020c0f0610121a04080f030a0b1c03210e120c01060b0a051e0706090b04020103050601 80
    0x1030681b5270514009440354003009040c3c1c1c040d21a40c10040141c000890309800351948000500f2004c5402d80e40e1a10b503880d0020b03000100d6031071103200f40e11034001078440b2035080c980a0035540c00843d08020020032039682c0e6110805080140e40700b0102c54400014001400b1003401003030040d007010005813101d00d0025802a040c42000440907003e96000f007603420a015040d410f4803801d01440007614111b0020400d425241c0104a4803480c0c1002d036502d001c071352101c02151303c50b03e00764000034101045550722603140306000b006004590754030381080b544500184070310156000c2d103104540815120310391350810a0541c2c601c0d03606003d141201d4020408a980036402018181c000a443c11a034030400b5041b0000c0c0404d0783c5044a2480b40d83c120207100740950000304140c40c0018020040c268547c00001d4491143c6103401e400901c041c4070320f0011b96444810b4000008205070340c1031a00d032032a524a0b0643c1c0401d10b00f80d8170000034500700415940c0501445610020910b451030320144000100 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 136582041 1250 136580791 136580803
    0xe0f04060f090b030a1509141204050103110d0e030307020f030a12020913020a092303030306010f09030b0a050103110d02030d050703020304030c0816150e2b111011 72
    0x46016200c0c80c00103a140c60602201c001c481c1c10141030300442580080a0010b0001e122048840391404802c9010b1000c022030300c41241c0c900441a2403410b44bd00c001140507210360561003217404c900f04048110b48240c3c0c03245140401c21540956201d141c2080c01900b0104400807255554000704034800143d5405510f4510250400c0c1d001a04e44041101064280c0b0300c41d00e004003400e200041c910085500810024100c8000c04005184c452404190780c6e40c2c4003071310711a030303802d6403092000c40d0040d0f02891038081c10b2842d81c80c0403440c603030f82e030f4407922036052081d2401b8180360b5a800c0180207100c418010702010220643d0440c91a030f8682d1301180c0e503990099980d0b03040000102c0d44101f0103100f80304030703001107412806186619840c0c1150a0301c07800511310907004070900000002d14075092082c0e10515080c651120710f880a440c80511181e4444c0710b00030500c0340114003201c40b5504022080c4014180683d5101c1c2c5410b1208051000246600c0108014401d461507005006a400100c3e = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 136583291 1250 136582041 136582049
    0xb0601080a020c01050901150b0909010e1f150806030c3006040c06030501050102150103021905090a0f0b030a170d020918060301050f0f180c0604060e0f04060f 70
    0x400c008568030540040000c0c0556681140154245810300c4a225015001080b2408802c140c2090b507130b076240708138006c0344996070055400451040c010400c1c0303e140e000c0207500c9a980b10303e0304070400d03c000004203023200c142c101e1101d01c400300e001c00e008594801049980040160000d20107940400002901c6070101600c400794078200e0340203a181820480071946500d00e0032021180a1f00b0503160100c180b825a0141100183c076000000800790710015418035580d03d042074142c03c903401c41d000d00604100d264040000410013000024445c0c0340c25401e1031207044030600000e02020052400701c00d4550140941c0d10030b6001114090125010128011110258004da165944492402d06019004d0000d07001c1e44000d0104004481c2541c0381c910303a00c21801240200265039451400c0120384070103840910200300c8030b20000d140081c3c401c1da598070541446040364040800d0341c000507140e5110307402c81c5001414180804015003003c800e5034003905000c44083c81841c2c10035664800720919486 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 136584541 1250 136583291 136583297
    0x1e091a07020309030f06190605010906050a020705131d030f09090a09080301083009060703020a02091e060d020f010804080d09060b091003030807030b1207080703120203070b0601 78
    0x2080040d8001c0088400f1400080d05441100915020041d11098100c0d542003400510141078540c101c50707441201d0a603201611410285401c10900300c8060700f00031118029840346141c042800e648030703031040d022540c0450010410080b48035640c4102500ca6440380781507441800754445040c3c0044c250740170207130166001082c0d81d42e00d40040c00034260240000e401200000000f04142c03d000c641c81c800681c15191105100e42c0c402d965031044840c244000014103014000101540f0306500204270480c02717403040300c08103401034001407000c00050710f802604614079a000410f22003000d010300e41c482d400311070803001001c55401041c064401140400d04005000d0001010002040c05884009030108010400f10419140000040c5088104144039603002400150180004860740c0252a41580c0301c001c1034550001c150003a280480313010350300c140d601417001400c2da0100070180c010f018980041030014a103003841208a0490307250310003190010010714012030801a501d0b80c000c0e00a01e = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 136585791 1250 136584541 136584593
    0x40e010518010e07030b1302040303020604050609060606070204050405011e020c0d02071a0702010c050607050901140705100b040225030f110606220903170a0911040207030903050604061e09 83
    0x1b10005402c4007900c590100303124400f04010080c5070340040c0c1c89228511480440c0c0c003e0b02c9400642c0d985003c01c903a400d0f4444020041c000050400780c00464000303101d4400841d03440d1541c041c14041203004004007507084e83c04518429000001c1004c101101e500d40003824105080560604a001400500380704000300001d16500b107910801d900700c0500e80200549a080c14104030041c01c40e445400030341d001601f5002c0205404411004540800e94001c00810442e00b503caa41d4014000c03800394194080e900f40311049120624000303202a40c4d254002544948409146c007a060207800b40071b0000304800c000346012140e40000d6401d0b0002400c40380c00480d80710b46c4001c034422021510564103080d050050036020150469286081c40300c80e640340c01459951043e0f80700c11203400c081d0140008000c00c0b00c445050509074000d0246038060701c0c4c001e08182c0c03a92541841c0c4a01590100e52455840d074040c0314924400a48a025503c00348080c808003465458103001d0400091003045420809 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 136587041 1250 136585791 136585811
    0x6090c090c040506090d05030f0a050409050105090c0304060e0c06160b010605040302100e0609041b0815010203070f0f21020601050414040b190614040e01050402010c0b10080102040e010518010e0703 87
    0x1002618100c0210036003032640cae005100c40042454205110b0b603103484d410100003042c1403820000305031140d8561036156007107940f141c84240c098002d40c243c10040303000385c0d1408030b102d1f03c4402c0107100185000c1c00c2201000d10760310b006420400140c3c040d004012061101303100595494035142103001803031820003440303041c20f00015007500c500d502c0203074040d2134821038071486001907000c01c40c00021a00d0740095940d808400e801c6440b03600010b2401a0010041100024021070b860f1135030034054034104e1100341c0c0c1640c43c0c06c541000703464001040c04005c012503901c03540c10400c0a001d4a030646090040300c0302120311003861240500000c014000d1400003d6180341d121350b6910050300644000d0040388d0f0b33204403000340300e80c84425440c01203060900200aa1405004070f0f402103a040c0c0d41d030240d21b82961507240107950003400052210804580c00a10b40e0801d0000d0000b400c0c00340d0004005500d80300401549002c6112151180709001340100444c81e04168020b83c0407045080106422001d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 136588291 1250 136587041 136587043
    0x3210c030712020919180911040f060302090a0203180d050406050a0c02130509160302060301090519050403020c0a0602010c091e03051203180316020f0402070506090c090c040506090d05 81
    0x200143da43c3c11a14520800f064031110210110459410040841c006c06480094000380c62003101e000d401e10115803120b8605050070b50000c2d028107204800040e240b91a5400118450300aa8247c6d12964001c000c1c88a11400d441e088141050600001c2c4000404904013500500031403083c0801e003d000710719900450b0050f0903083c4019802001c4002142c0021180d50007082c09031241e00c014807819100d00c1e02c0114504074001038980041085003903a2814a01c0d03005090001e2901c541070741030042c54482c0e4906802500c0c05144607401520708000950103001240f122580305004580c188542d112989411940403400e5030701c41110203800c104150009034620006501c0145944200d45031800020800809180561000c046011000340d60a198541d42d01901406c260400d00f8003800c0001840c043c0b5408142010141c00541016501e480703060400808550b070181c0b03030304440e10510b018a0f1160741c40c0c0c0d200e4010740c4040d003844c3c180000720b036140c01511102030007062221508001c3c000 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 136589541 1250 136588291 136588297
    0xf03031a0d210207080a0f03020c120607080f0403320a0216050a0605030c09011808010b03011103090a030c050a0602031807240302090a0806010803210c03071202 71
    0x40030705003101c001c24a20b0082601c000c180040c068860040d80e0441c80c01d4070103e03507441154000f0300117280307043c443d0722010840c3c00c180c2c00860952141c3e1184985503254800c05900b02d415001c06000c00c0c0c90040000b0745180c3c0028610325424500c04100300000b60410700c0c0d90a4200b406055448030004d1181aa94070709401d0f0b940e070000745000c200c2818640e4000303041d0540340c103e5081c41c10925034071000e004a95405004201c0418400d0000600e0706200c0c0b0054143e142c0149040c1c00b03d140101d498980e401090303009000e07907944400352034941d800c00340602141c40c0902402140f1390b01d0215400c41c0c452800410003400c20008007203100501c642046503c00168218800315582e04081110b001008a1410024064020058002071489806442040841d1213044074041584000402c900039030025540c2588540d168001294002d030400400b400780c0301d04030085da501c001c00c80d01c041c1101c15603c1910803240a15040041030255102903c2c0c0002081c1070104040400588407000f80c0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 136590791 1250 136589541 136589591
    0x3190e030f0d0605060306150c0106051c0b0709030b3606010f0f030b010e070201020d09081317100203270705041118100e0310060f080a0f0303 63
    0x40300115503241c501003040300611004006000c2008107a90391300c2448506d010444083d1380c494040700303440d009541100010101c56202e5000001d03015200c0002030050000030700c01419440c8050090380400c4101450070303800070040c1c2070000c1081d10355501c484880c071000f0411080d0125245e0092100310001341000710b03030030015a0065641181410711a9140c10174860018100d552000015800c2c20003094141560340100c200d030220703800d003400c8481c00240070700048110365007000399050f100450b21500d01c03c41d104045e50ba560340f2100d65203045c0880d940c0c01201c1c0403243c0a400c1309006900140d40100402031a90268403551041c000720380042d0382c100344a1142d000c2c411380d50460300002c1a00c0003a110111010448068160451500350043d903081d00341d401110002114645000400071705500722500d807510540e5034400c0840d042810203805090915101d61051000d1404605844094800c030001054150601d84411490034004240542819540c542140c0c081e515840720010742 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 136592041 1250 136590791 136590793
    0xe01050118180609020c0307020916090302090402060702041a10090f09050604060302090a020309160e061315060201050402150a02030f07060b09011203020114090c090a0f090f03140304030503190e 86
    0x45140010007030301ca9120782020ac1c4a000d29400140e072f12005170070f5031918164613588402e041411a402d0000a000107042603034040d030140b103002e005940d2806445949603501c40e150404450b1b09050000a0720050116401e005007401c007030105441c000300c107038121351100b800850240c42d0b940100e8001c003500d41000e50042e1150007088030384080da4005502494240302141c034040c0ac10305110f6900c001c01c0c000d030340486d490f05c1c0c0490114540902500c8100c0d10294000640c0c000038440310107181347c650311010150b51681c041005600d070400903001c070000844103003403a0014042000b0340f00e11817104000c11220000c102c80d8207000141d130040800d0701015040c540c0b9940c40c2c0500245c0040001c00450044d030916000c0003a00c0c0381c0c494014046c5280100030400ca007541410803142d984001c02400c0c009030749135843c2d61407545038010303c40c4480c0108030f00f0b0314141403410024206a01c10320804003241c010824000060303440021250b210a44001034a0540d10b40c1004c8809400501c65035042 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 136593291 1250 136592041 136592047
    0x120d09050d080114091006080a1d0d020c180f070201090203010c030609050604140106030b060c01090320011e2714010b1c0f1e0c0e0105011818060902 66
    0x951504145101d0698182503044201d1107601020010740f81c2c0111b5410500c1c540400c01000100c1c0252100f40d080b48042c0b8011841440030f09203128214403c60a03078107a60322180d4403840d0301d0340601500f5150403013039611002c540c0e00c882409489100140548800381c07071800000700090f01c01c0d440b98411a40c010001d0190f0104842e000b0040d00090145050300c610b0000400c034035140c10320a8120f040350380e005281d8a41c2c42c002080e401003207400c4482d600b2400c200070380d542c590b00a105807020380344292030311040c907480b014000060b4007011044040302c1e8034092100309844105107141c1051100060042119803080802c2684503103000c502000c0d54030640851030070040d200c1b01284250100d00004c21a464a04041102505c6003030b00800424690005160115034180740d840b1100b401034840d43d000c106007912004008108620988110641d64403c5c41080d50b40b0f00e00e40d00402003407902900615082e60510780070032042c0302d03c98030b01c10603c00310552100a500b2070001088441804c5403 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 136594541 1250 136593291 136593313
    0x618030d0203010609050907020c030d1b0803190b0a080705060d0f05070207031713050906040608060702010506042316020106081212090d090b090604180b01031d120d0905 75
    0x8817103802614869155480014091440000c900b40012070040060404a41c0c41c10309a8034a0900301203640d881100254001c00300303400744001c600840c051010309550030701184402044501c0c1c503110070301c40c003e8107100f086564170010b451000d485007214166a07880c0d011002d0030003007241400c01521207040c0020420990303004204407040742d001d958610419841d00d10040000d12a994403601000a050814405402e10310b268946c4002c01030720000d0000d444020040c0b034410211881c00c0140e44500c20040329080601034090500c441403212909200480c0f41c00f04107070401001014110f0b00150785aa4951007504050020000e00054606a16000d08181540d0340031251502100c86040c0c0428181c0d41c2c009110500c00700b0503640e80c800700d414814100040c0d031040d1803807540250284400b00c1c0780078029081d00d0002c4d4600200003440a249000903003611a10800b80840764100c0703405501082020075045101280d103010039503107240842c2c0043c020946068090914866250590 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 136595791 1250 136594541 136594547
    0xf09060e0d020d02071d130606080303040c08060f0a050601030b0405010803210105010903140307020a0b12070804030e0d030c0b070206100f08191a250201020c0618030d02030106 78
    0x28610070503642c250b03807101c60b10001c04c1e42d8800084c81041081584401c10700107064070b484555801c644c1c504588401c1c04240d0703c842c0140e4046400c08100c5410020600040200e400304440c018041d01010344610b142c0001e600e40c6409000702000340c829280c0d000546160701ca988802d050b050010020481942c4802e402540d94125980704d81403600c01a0340ca586083c20f5600881c100c541c16035814248908554501c040d030344041d210340307001e440248060401681c0303000b076000c00340c580c490806032195a0b603640c09004d041c0c080c0c912814041285e0520004c25840030000d940c00c4030079560101020068981150441c400c02d0000c2c242c02e40040c03d11400e41d40c040303120b900441070400e40c50340356034440090688c030f04003920503048580d2101c540c0020460920040c0501c0b40c1c001c080c1d555900745200a0401410b508549000300c0c4050b1b91020701d4105a01414128100e01a01c000c608042ca2160310965400c8003030b20701d0210420018000034003440c1002101c0e8504800a8155102d5a4039140a = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 136597041 1250 136595791 136595803
    0x41407181109031207020102030c030a08070e060306130218030a140105010510020703120e0d0501060306050109090b15030f0f03040e060d0b0403030c12060b09031203010305030d0f09060e 82
    0x444018241158140c01c48912810b541140400802402e1602207040d0b03601c610754842d038022415400f042c00300306181c078801d00141c8105a040d844980c003618003207000070b01c03c0c404461b05074417400c810b10600400341c072401040c00c04000c414000581e00c40c8800d1054009600521146174503208540720041040710b60781d20402d204402c0c0c0e0007440140d8847c0f0810050010301008080103038001e400400110360380400900031210356050500032605124045a41c0d0b01d001c10301a80d2030f83d1514010010000c00d885030034010306614004004200580da1181c0200d01e016001c40d10148081d50543c40980d002d0100e0010b4410344001c480b800075612621903102d812602c101c103e40501c1c0c40019180741440340503042213650010801034603981c0d50741d00b90001d000004041c8200050010a501c403100b0503c200005001105d120580f1002d8040c1014540402c2044041100c10140010400583d000040da85500a0014080780360314800442c1802400e03007401c060643c50401c1e1509980f10404039103 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 136598291 1250 136597041 136597079
    0x51608180301090321021b0c0307080303060609040e0102040f0e0406050705041404090615230a060507021002030f070605070e0103291f02070608150105030a05041407 73
    0x90034580038100c040500300d032a96030010700455041d618200f0040d0380ca002205106107100c02c01810704004001c180210740404a0444981d40031540341c020500d420003a400c010041140298590300d0582d01180080c0281e4503032a00894440021018840342034050f10003401959900b030f2442d5645d94500c41d80d232901980c098a54038580320116603000e124804460903a04000c41904110078400c06120040caa4100e0a449060340d9280b60003080d200282e00500606108140b010061b58580c040c0c1c0c0344805910040344100354100c0b0400841d81c03c041550641d54048454040c0c05e100c0410607811480740071a083c0c8004800102a42000318903405640129501c1e039490410082d40070054040b5030016414000d0381c540403440684100c004580400544009051401e5001410207a0400c5020100e100300c0582c01c00d100c1446140d62044c400c80e0b100c0c0d002c2031300318001400140041c00c1c0d0301c806001094038944443c005070500010403d4100c00201c01012100c0c0565207040005850444c100 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 136599541 1250 136598291 136598317
    0x140307030b070324050d0201050304060b1e210618150406140603060423011e0605091608010303180b070b060103050106170f04170a0c02130e0c040b01051608 69
    0x140b81e18001809001170b07a5010380101ca21007025001503410341c0000300201c840c04c0d100c019505103034484000701c5200340011640307001c070101014100100190420144003c460b1101700003008200e000500d5900a00911101039500d000c0007601402c6c01014000c030140c15042d0401d100412250340d0280402c480741070b041c02241c6d180c4200309608c44400748c1d009404000790401180e092407000054050716040d000c00000c0421070102c04000381a0980380300d1955958500e0200110705080c4001382d406801c40d070000c10007407040d04004d0000281800041c00f0401c13211404d4540c05155100c09010f13114102c00d1a1312000907140080c1c441c402140d1140c000303401c1c2000002d80602860848003103500f811003490b05542e402c0700f0f04460344e100a0080d038401c0c040034240c4c8401819a401010300f05815075991074014454010711038503050006081078017034581a074411400c00045111003540c0012140070902485000c0126503030700483c4000c1c4c03e114001881c0c1d80401c0307681002012074070aa80 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 136600791 1250 136599541 136599581
    0x1803050f01060e13031215140307050d03020a06020331050f0705030a1502220e010b132303070810050901060e010b031b0f040905130c140307030b0703 66
    0x80000364115007600c05284c60955001c0900c0000d01696140d000c0c006091000521031940d03030045080d10391141c0c0034a411251100408019003800d01254021f040301703942007003605000303942c000e41c0d41c0700705032001d0019076022002c0b480401009040d188000410302c200301b10720100d01d030203c0e840281014200c40922800103c0c07508450081844001c543c00100a4000403011ba100e509032000000321600d0301a82c00c102d00340a620b100c804514a0080d0000c04010041c2441d40d002d52076401030b00645403d480602031450411400907038039082d95980c80c0e441a00c4000c140c00e4405030303580c448980d5030501803914081340170500024101c491080c020720030302440e03c3da069182e007255818011003174003529038030061140301c912a0003160400b1a406501c0a0710558100c800703400d42040c400d2614000000504100701b2403507010f10360b040038003840012006e42ea16034035403d03c907503580704a118000d607584801e915658244040001103800000c0a581c524198034002c0c000c2c8040b0204c241e50713800f45 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 136602041 1250 136600791 136600799
    0x6110d020c01050f010302240c0607091a030402060409110c011409191a0c1312060b091003020f0d06020d0c020d0c050c0918150105091b040902030402011803050f0106 73
    0x1464100c5d0480350054188035800c510700060201c0c8400441d02ca10b184801001010891082000076070b11900055445d07242860410101086851030880c0740303100a0b0061090001503a40c2c1405ca401b200c0324102c3c0059400b0410072140040c0c041d940c0390703415552810307010301c15440300e0245662152901d941030701d0811194400d4440b0508041e140074041486c281c1e0280d4a8840034081d00d60410300060055082c040302c0301a0111808140c0c10040c1e2140247c0c0c101010044a402101040c50b412940c03100c0625256003503102d41202d0b88000b900ca0103400c5c9000c8801d481d00a42c0032406038100400759664668451100301030081418114018802d0580d04518540300d11400041a5400005015541078220400c280c000010341f80b15100380702a01103140d0b40c0400c01202d84082d25580300c02c001076140c502001f507000760050400c0d0403104069203541c0462a040119025076200704001a10307921203000407290b03584001e020703040c0309009003004000c4c003030001805081209214024440c0300d841e = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 136603291 1250 136602041 136602061
    0x91203160c091406060c07150207090c0c02010c20060f0304020901120b161707021b0a12170904020a050315010f080f07020a060f151203051606110d020c0105 69
    0x8032078038000112646001113081850540000c00081d09244122a02c031a1150b0340106800310500700c40c00903a0100c041040502028080e9496105403800e181c80d03204c010390000381c50f442101c840209070031140750b800c207074050440c11a030742004409002c1c5074442840001a0701e4952040d18240c0c85500a6000042c034a40032070920041e581d40040c05c421135072903003421000d8030310220a00740b0911a6024801c1a40050007101030f12038002640100141c1d114580c040c601420401c5245008205020b402d01c903511046202521450303004030302c0315585e00c19403142c0510380240700c82564098000107941010b42c1d8020042d5008005a8481b8400d50b03580000645074111103448840110f00710f000024800340c1411b21840c0c3c00001070042c0d1b8030340a6603666000c202c1d00e8180054111683c2e40c5020540440c0700d41504c0702800e48030401280700203a54502801600980d066180382c404000c020404108103038200304c4880c14007550307a98941c0ba4000e03041020390066a4140d025620f440300081003015 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 136604541 1250 136603291 136603301
    0x90303010506160302030702030105100e10050303041815080105040c140904060f24061803050309040c170103150e15010504020318070b0a03050c0f040b091203160c09 73
    0x300240120f15100801c0704841641d00c400d00160250700060081e940036031028000c01c1c0c8210282603498184500700303c0d8000b200d41000d4004070014000003002e000b991400821035051781e012407a842036510341d2205001c040d11440d0303404820300e00d11510002d88000150803580c021303882014480b403080e44500d03001c114140c1804c880e542c0803a01d000820007141041d030010f0311003c103121005c100d881151458410b0317510505409600b800491808001e029404152a40407403100d8030b03902a4545152120380d0303a030142c20521032041d5990041010365900440711a000b6180c45480d014141d0b0f501d042c005e801c1c50303801d41003042860400716041003000000c100f810b04000104500303a001d900b013506110003500000c0102001c5d070340c9052080c40c00c081c108101c034018a8035854081c0d840c400020b0043c25540d002d0503000014000344a096050500d500a50b000d49034800002a154008200002d1607400c4840c0903400900001540000282c1000c000700140b41c014012214020760b0f070107078001240c03 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 136605791 1250 136604541 136604549
    0x120f24080f06090309010c0c030605090604030207060509030606040c11070e1902041d04060b0d0b01031109040b0415200307031406010903080913020a021005011202090103022205070f030509030301 86
    0x900100150222513000e140c0040042c1d00490f00d1a040323076269a10003040781c80a45050318942d00c220100403c040c0d041100f0300181c106860254103094030840481d50701d84002e00301502c25074a62810000c2c20323103d00c8031850401506401c440d021070b901c011100803d00240c901b00900800510007084514042c000c940440e54041d00c1c0c410100f256140700c1c040ca42000d001201d80c0d42d1523000307100307155480f102c0c2a041c0d2030203007140b02140e5240d494107034607107110751811500820010f4200b1010580c46229194400e400800c1080800040c5800c00010042084079800e441c01100c0301c00c0c018000d0901840c0f06208a840802c0045440141034003881400c444a900103441d0002c02e1000a886501508a40700d02400081c2062035203943c04047e0b802611042006170700580f2401c05850180c02000c0c014800c120b42c45040d0000780e0089003d0040502019000e0700501400d04c030346204031040411a250340340b00401450070450001416034094020210003e810140459401480482228122 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 136607041 1250 136605791 136605793
    0x1e1302010807030e010b0a0605040e0f040f030f020a020916020d0801030b0601030e0309040c02031c0c0c03030b061902060105030709110711010c080d0603061407120f24080f0609 78
    0x50b5440841c03c9010300aa00c0c400754140d5200d8950300410f0b100c16070200d000c0c01c1d854a805454901b020701400190000804441c003031040e031401d0102080702101c60410141d0503103000105003004400c02da151141840009400141c12020814500c43c04503080007030551960a480080010540031200c6400038040500000d4003140880d409600961080808520110030780b41071000c80c000140444a128860002503000021122680c0c0d05d000c50f400545051220108403500d10900c00400c250b103140c1e8020103240c0d9840414056945001c184e441e508010204560382e0206803e0094960001784245400b910500e040410f841890f406034142d08040d031704000e070a0450300d845001c084100c0034100380c144201c10521a000c11071b031000070f00344c1180d041f201003180e034603515010b8200d03021181d980c0d4a10301c40d032050118240d40b0010f1485a4103100d0804a200a00d100324003004100d05200382c0f05280c1030b20320141001c11440001001c545c100400d403004400c0500d030181d26101c084450f5012 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 136608291 1250 136607041 136607057
    0x6030a0210030b0f03030304050d032301050904080408010c030912020c0d08030604110408010e10091e080910080402031612080c030405061809061009140f06031e130201 74
    0x510301c0b80d4000c1520100040491240000c42004213085071300650307090b62660000c06140d031a090705402010101d00b42001644024030b041004004610818001c49108066180c0030509001800041d42c0143c200d030300080004a0321103501a008108800003161001e00d802441142c950000c5443c08004201070442e06c09850b196444c51104e9000070a03240d40305a607400e502500103041d5018101400102c03000282c05201c0040180c03410502ca0120140c2038206180c16001910411030710284c0300042c20b01c00b00988142ca800003482c050344062079081800307031035220302240d0300c150120b00450003a000d5400c04600001d820807421090700503041001ca42c4110700d000600b8600040c240d048121040c0c90525842d100000ca255010450b5000401203c5100002920709820400d0f005802200d40b00720176500f41d803021300070442c6446910100243c11001c0e001d0390301c608542200844009100f584d89150203400d40d000446145280080c43c0c1c00c0400198146c0b0456003c546000d80507114004 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 136609541 1250 136608291 136608319
    0x4061a0d030c14150712060f121a24061602060a050c0a0b0a0e0705030705060a030204080114010806070914040c0315090f18080409020f04030803010b1206030a02 71
    0x2201c1c48059402c50754041a540c003160000340c1406040c90301340d110b4611091600f44414020182002c090340d500010f450f080080003103039620070b0304004864640c01040050a00360815402c0c181c012121552500380c850100014000c651001503244c03c020410100d401c111801840164080c0d802031110b40980b80b0b030000e0140c40e01038081c0844000c40c2c81c0003071520000000301070503c0908241140d10354065400d0201020325030080300c281500304002044140c2c0b070000000d07030722043d0b44900e502500c000207061641d00e205c0d0301118007408680001380403800b020f411549840c0400d10800d5000e025080c00304650a01c25041d09040b80c118510f0b40c0d1156940d141080010180c010420042c0342d65018924000000502c10300010422440c000031040035041000041c1c440340da6000b0700784c00e0181c10442c000b400c0d000682c0c0a68030100c00050321005103840509441c491500040d11040001c0000202d4500903002020041e1060145607030702d803a000c6c2803540d50895900d0081d03101021103110305c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 136610791 1250 136609541 136609547
    0x60403030203180714150c0307050a02120a120809030c070b0421030203090f061603030e100606171e010b040305100b0d0b09120a08150108040309030b06010e0a0b0304061a0d03 77
    0x2031500e81046c448034940492089803519542c0145001ca0f4280c100e02100000d600c0c000000182900003072001c2c1405005582d20035920a81c0c9035001c42c1031007920804540c10281c20000d81e1609801c400881d01040c0d15210100650b03041071180c605440c0e002d0802e544c11400c0e29000c5a1340c160705030002c60410381144204460307400190b8100e40c2011041c01041c8851940064444600d4020349002520491400d03c06060940d6052601445401c0c00340410059074010340700311200c6151102d404c8140c0301d081c54850610603c40e042118003d8201c00452203d000d24028000c407440f4404542c409858241c0c44e034280d408001400b03520140b10800c000210300c4101003c1d502c0420036003524080360b801c107900525504213008500c00211400c0c100310891585164024000704242030104071842d00b40d400034006a51030200900540722103010505a9005242c61090902c0040548230340d2529001c031109a908100c41c1954090b081556154541080030074845031120090003007107410300662130079 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 136612041 1250 136610791 136610809
    0x20a090b070204091703240a03020103091505040507060908010b0906040c020c091305010b09011a0d4d09060c0c0406140307090506060714030c060403030203180714 72
    0x50703821540380e01442d400a05d8011004018414103200c160704d03401c192010030010b140640d009021600c000303a07111000e03540c0c00d0060048031750929000c183c41003145400b04042d90003540010009040c0400d200410401190410958001c1e076519840726a0b00c60425003640c040c1c02c4526004001030000c200d0301e003850342254000107054011100002c0303245012605075402244c48051081c101e8404404104080c062000241422194941154182583c001940b610b007280012003000029051094840903000f03d01d954400940400da401440000020807ca0004400da001c242c030012040700c407091114103a8099404c55002c0e407c20040c5001c1c000194000d03929001144921142c1d24510303a07a0340100c0001c0c25800c804081070b80a102c09161030f100325500310140d014280340c1002030581304e01d015034901c280c00a6154045003120f8072541d00310312852002d90714600902d4100700505400da00290f0040308580c03401000c1c0d500512545482c0c680034003a41c095141c0c051154a000e01e802005 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 136613291 1250 136612041 136612043
    0x3020d1803080c211801050708090d14010204031a070201051e1b040b0d0b0a210201110109030e01020f0706080f092508010506040b030a200d0f0213020a090b07 70
    0x101d904d0148101c003000302e1050643c2078007071000300002d140c0c816001c03441142c46203030a00b030034860b0400d50b0ba940c500500b4001c144000d8018940349003071205003c0c220200385409804d10f00215901c9889040c0340005910807095443d02c0d0300c0505c085240e5510500c2118820f501d00034501c03041a0016548407510036001d0a50501c0ca0342d000418070300e9101d150004d10082c00c0501c14681d9034504041c504003036600311009103100d148002070801c4100b507500c0e04251030850800c1030a181402c188013703260001104044010b6620b400c803420205500700c076034005908026000c46034520313001c0d013003281d0b02d401a01590000401c46000b0400410400003281d411400110645070303101d200c140101003125038121054030b010232038001005110803c0c82940d07041803041d00c050218000ba9000309980f002104c0000b400015181c0302c07000d5550444084081c843c5000b011948000e000b403c00030744484219806070310a16025401d5030341032510b4170850b04c1d501104d8640051031403500c2c500000d107400c6030748 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 136614541 1250 136613291 136613293
    0x1303030c02071a03010e0906060319031b03050706060503060c0a080405010b030a0b010e070207060c0b1005120c030f0105040c03140c090a020a110c010504150c08040308030403020d1803080c 83
    0x902090f0310140c200e001e40c200441c0d2003515101e42c035080d21102008009051002c0c2d40d0842d2080c4903558030003040c6901407403210342c1020301198144ca02110741c5540c1c100ca141c4500544950441007507030220040c4509400f86c0c01c244070545c3c64400305512402c0590300742e5050a402c1241c0040c0a001f400c0b52588a801784000141403440700c00441d0815801d02c40131921202100c005002e48041903908a0308400c41d4402050300909106015100c1803050902400300d44600d00002d00300346001c006800501009403400d1000100c80b03200907030700e212404e0124400d000e01084080303201702c14031030317284115009034069401070325546886400154000004040e0300810b00c4002e40ca403105020b190103140e096000595a01442c1c000615030350006940000d603811155031101c0680c0d002c41a1400c0e40e01000801d4040c281c1c0c582c09a44d41c02c64080c0c01004600c01080000900140402031807040c0d0281d021740c0d01459081400700c0fa10245a4008400c26586080520206003443c02401310907082d44 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 136615791 1250 136614541 136614553
    0x70309061d060f09010e0c1203090a06030e1504022107030b070e120c0d0809120a0807021918050c0702280b120c030408040302060a08010905010e1303030c02 69
    0x8284070407107416000800a181e00040a2041e621804060703943d000080d00c00170410300856510307240d26445143d600c1c51185c142184228110142030040f82d541007170080410302050ba03212000f5000d02203a081c02c0049000b10070201d03501c04481504603100d158000c0c81200c80c144600300c165100c42c4580202081c42c4107254001c40040d01950748071f80030b40c41da41c5644010390810010081c1c0c400c02c007800c0944176000300a0f40c1620b501d50b02d80c89910f01d42d0194015440e8018a00840c45124024010150030310403005040e09001402000304181d074002c0c2d803c0908066a0040d10034080706521600502c0f0701c43d0341010902c9001540040d4100800720103040c544105900022611148041610101c018030031155080d04c3d40e0464001c020708181d2491420200c0e0503800c581c030050001c0c0340c0221030380008001410031111a04440c0599402400c460716080d08400040891509004d40c00b1040d292800119508051071800340c0f092400b8040019071190a23a000c5020f080c2420346202540b20340 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 136617041 1250 136615791 136615811
    0xa0c05040f0b090f010c03020613330b01050304030c0b1504050c030a0f0b030726120c0f2b180603020a0e061905032a04060f030605030607030906 64
    0x1415640002e1218000071500c44120b2010070058000c6036142505024903043d000300082e0300492a10392003101450b10402002082c1030a03a07542c10110135244800005c403240310280b141c0719210080d10288800200258003107840151528407042d2000390101e504d2401400000b4a866170b8154003400380c21a0364072140c00200420156181078500055031400403040110a244034072889081c020a900207000140d54540402d4a82009000d19a661018120000020119207804170140cdd071410040744c05032550321214038142d4000840a0082d806100740ca025812400110070f2503480350400130f251802d60303030400041d941c171a50030f4400520500b001c104030040c2d03022040708000d1105171409070366040ca4a0008050700705c080e00c428800c090500502001c0e50750841d0074030b1007842500b0100c2e940e855940315210b02e4000810355000040c9004c4142c460304d0700f800040d104840c4141c4620900d51090003040d8141d0f207090241030b800d40d00038400241114400d401030300509000320b000042000031 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 136618291 1250 136617041 136617059
    0x170417030415050603010501030c151403040809030706020307050723040e0105060114040f030201270801060e010e07021b01090e090a020f030f03070201031505040504050616050a02060a0c0504 84
    0x204403810b9a9292102401c0e611011203409410391152040b00200076030b60440d035452130104198003841021502d0443d0301c005250040e8228588400c01110454807071810785410901e503801b41010500900980c030b8006442c500000503038855542c0b0401412030203040500a002e008600c2c4140d02d0075100340e55503042c3c00d80302c61041c07140800f02c4800220b42803900000140c080e01d02c0d20041c0c198240c04010410002c104e849028007500d44c2460034071100100701c2c19407a8080d4107402082c2d0405600140050003c00540c4602c080f1060510460301e541e0b030751108104045400ca443c4005600100151903414004c8905405000c00c141403044150f0744410b501518003404460740801540480103103c1589001d00391a40b0001c13084004110400400c00703925200d00900d4030090603d80c441c100c00402401240201014020281c000c0080f4501401e0803a500d21054600c031546124116a03156041c2c46841110400301c1c09400802d4541c6030340740e8110040c5144003180017003000c14031010132084c1c9 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 136619541 1250 136618291 136618297
    0x91203020615010203072a0e090706170402010509190b04090f050a020703020304060c02060d020a0201020a0e1c0b0a0e0708030703030b01022d0a0b0a09060b04090201170417 76
    0x40a540108054945201e504040d98082c00007a4107542c014460400081d9108601a0310311030420300e0300e68481c048801002c40850381f42c0240d414038604100300140d001000a02004075881d0b0341c1c1ea112907000d180107643d80010b0a96010340011401c016600d000e06101084a1806000c100d411640301e5444641003403a4129070802251581c944c0300c0703d030789a15140035850f00000070b10340440c5000c4c51503801075500c2c800c1d88180c005110074041c0d080190768401702071342e0925403101780070341d0b0300c03c0c002c00c1c028001c2d403000c107540c804180981c1040d010b508003481e0302a40d4814030700518903c0345035070f25030501c6200018040d118058903401040940c2c0002d0013000e0052601000450301d60400d4038015003500c0002980034115406a41003074240101d500d40582c16900c82c091079041c0c40c400b01007a070305141143c00080c00c1840c0780d074140b04000e0480e030302120036a40030b26002c00c0350149040400c000d60b900e80c00f0103400120001c1280c200700009803044c0750030a116481c0041c1b90010801c42c008150 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 136620791 1250 136619541 136619543
    0xd05070c0b0109021804150816060c1403070c1401170105090a020c03070c091e0213060e04180c170102090f0f01120501080a030f03020307020a080d06050d08130512060a09030912 78
    0x86104a08104050081103040c0c0072700d0341800c1460b2020700f00741004058458a00d00689101a04a440b01d0151414402c0ba03000a801580c90401191a29100c124503e010070140740020642c00524103c03018400001d81a9400108540b03841d0b15204e900102035002405401d01c0360000704035901c00035900308400c0000b17281000010800c0300036100b21901840c0148030005100c2c1c0104a5042240d000901c03c01c02d6400608003040400010804a402410a8203c101c0b004c000080380b2001e00141c074045508581c4541d059100c3d00403c01c00440c2070303000303100010390002210b01030711056103400c02c419541d01ca818584400001e4000b009801595420392011205401c410300355414190b20540c0f2012043c1582810b61650820f000c00a688203031404000c1c4c003681000c80c1401c5c84c0d000581180000700f200411803014a191800c120103e9400070380b2441c3d080301d40440016060810786500c001541504000e482107903500c0210300064504510200d0801501820104107144450740e01041c01d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 136622041 1250 136620791 136620821
    0x30f01080601050d030509010f05120a050105131109090402220c0806060306032d010e0102030a0b04050712090c120602030928030c05150405030d05070c0b0109021804 73
    0x5514100da541e04081e81a000b01e409802c1158010021039005411204696820318000e005004001c4003141c01c0e01514940316100d900301424000c0c2c0700c0c02c0384c005606942c4100c40e115118086040070000300d0307140120554181e10700707122000325490321220183c0d10034005089401c50010360091312001042e4452510071240c2c0d80c040d143d1a10341d11a190640c0520251400c80ca541001d03000a580d56040420b24030f00d82c203101c41c8155850300402d40c3c60070f1540074034009016001d0085881e5010750070481c1c904911345e10788403460b0520700c0c0038081c0c0d60040e180c6498007544030084402c0c5002400d50b140040d0b03044c05440c0b0307001481d10540201194014000c00006072a0b082c80d028003810028141009c4102c104030013441c0108540c1c803450318100a906082401900d800c61404504101c01140d102c17000004100411052007000300043c007120074451810021a900c83c8800d83d2182c1302e014001d015030340e0403c01840040c0740d681c0103149495003040303900c4450000c0c4000500341d0340503240c0d00c051 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 136623291 1250 136622041 136622071
    0x3050406020d05130b030a090c141302070b07081315020d0f0c0206011e0f060917010204080a020d150c030608010b0103050c0901080402010c0b0403030207031103160b06060f03 77
    0x44a41c140150507511842c2d18101d8070740800e481c00d403002002d06000307440480b000013007c00c1110f58982d001c0b500840c0d0080c01c1c503a00341d035204072440c01320000140c1580100382001d0811031250b10ba20840d919594484e500e184a601e400e0002c0b0b034103a80080815401201c1d41e181d800c0466581d2803074039066144228096903a03100b942480f8151608416104500d41c00c0c00050413039503801150050646d00101c0040c010000341c42c0480000d10010743c42403c07000c00c42000840d0329a4459465000e840d0000c0d81180b411410800e050700703d124034419040350b134000c1d00340742c401442c22400c08030440f80541745544040e0f1080000c082211281000e0202183d9105820041d5030000e0040c40c403203420909007007000d881c2540d031440c02840341204080c1040440b200181c02c40e07014500c0400380c01d8100f06081142c0c0340c9840c0280003584807510950105403101c40c000c0311a000001158140180e441007130000040944e500c1e400e02402030902c5030b100105000d03280340c405e000c101441c42540b41d2801604 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 136624541 1250 136623291 136623299
    0x60d14061e01090b09180a0902030f0f060c09010302120901060f1d06130e0d05071a0402030307030c05070b1c0509070e13020d0609051005100f0b030a090807030504 72
    0x71062941001c8400300d8185540c40000ea802c800600202c4040c07100381c540e20182d1900240080c050b07200210000c1c00c11318103110007041ca81c1e1201d09118425000c4840229080040c0d41c0d81e800342d5800042240d11100020788a03030700440180034020018140076081c0a00d58590340c01c2da5008079000500d40e0740d207100c1045a4039003a10054014025814445a50724210526000c40140200b8090040c0c0030b00010009810041e4000503045000320306452051028072401050f40d4800c40e4161086081c0c10558052000c0a84016000380d40c0180118541100d640d4241e804100400702903d16001d20a0b000884447c1280200f14842070f2038454490b102602c005031080358005054002142d008c41742c04c0c400483c41c3d400103900f041156960900b210510310000740008161003000304628102901081040b80001c4d2411411402e42801e00807a07072000b07194660000e041c440d012100c0041542086044c03060002181c110060b03003808500618245c4485040f07a114441c202c00003400010104 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 136625791 1250 136624541 136624549
    0xa02010e01140a0c080f0a090314030a050a030f15120212030307050412051212010305190314070f23100603081206300706030510030b06060d1406 64
    0x1410040303090030000600001d1802c03910350742c0a0503200d4802d01042c1d15211013880650815140c54018440340141d96440d1920b008091901a100171034070b0b0312030f5084202202101105070b61009d0150b580d6070b414003004c5007044000d0a0f00c400b00c40ca80230f42d1000300c0d401c070f89034150581014100e4200d02060251031441480440d02111400d100b15410a1040c40902903000c0110340031608002204c0140f0001803c046003002146d000c000c159082c0041d1070f810307919004844074126405034080c3c81c1030780302d4501c04e207981c510346070b0001340001c100c80c464500340c100480c06059414025181d40c85664529624241c00346882007101c0704007811a0407080940d10104039040c001c445414081c80350b58a540d070381303040c90b00a00000003900c0203c2c2002942c0e40d100c26646d400c186925112103030600a80b0307000e40c4514400c010004600b8010048045042d42c000d008480c02207281802003103209281d503c4101030f1100241c12903070302500801940000000034026152002145040c3c9002410309201304 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 136627041 1250 136625791 136625807
    0x1020405180619080c1005120115050c0102030106080403030f09030e010503091e0a050c0a0e040201030f0e01021303020a0614070609030c0b07020102120f07050a0807050d020c070f0e01030f20040603050a0201 91
    0x25810041e0807c500000740312340c00f01c05811600740d200c0558030704e4030000c01501c00e40122080c0060542c800310000540d00d511811041c000e9029440402c800015001c001064803629034018002c1074140f16404202e501c1031005650000071001500c0b1528950081440d181d610007050705015480390403a40b0a0090a0100005e8404220744940c209403400c82500110400148068107050340c40184500074038541c1c0041c000e280030030008540d2800c1c50701080e0700003003e6002c244c0c00348000e0500494454000c0c0c0320691400c007080e0aa905150040d91680c02070541140c1c00c40402101c0d046540001d05112011402801903800150311202901b9030b56010344401400d480340c07490b0703000070f20158640100445524156078030b031000081c0d0b01c0340c106603101c1c81550f112008107840090441e80340c0350080b86510035500402e00501090b584c0b1000c11240711002c0c040030b0310074442010ba07200060400781500d152804480310008100e09100700003001c480403a4030650351070b000f4003007003c219a40b040038 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 136628291 1250 136627041 136627069
    0x902031b0a0207120302070f06022b0507020f040b060a0804140a020907030506040e030c010617010b0a06050c0703060501120506160806040b0a03020303030a15060201020405180619080c 81
    0xa03090610107100c1d802507079007000740326405840d00314071080310516100340845400b40c44142410505a0342e80c1c00c3c02550380c0c2032a95054005040c11040032810840702c100d09440c08a9a40c1d580d080c90201e0b020803080e00c01c007442d107550080d5100349003041a11000094120109540c80b0540640713080c3c01d00490207514501920b419401521401c001070361110740c0e09410130a180b800090658032840400e00504c08903005004502c80450703007000c0150150801c005580315092030b008a03881003000c0c503090750002c010550303105640c5002406000e11030005860012940c4080710f00c00c45e645e481d42d808442080e04441184138202c00410107100c010071030704d9041003600c10411240c09030080d0080840b4070107000c0d40e11494403002c2c2c005041c1d41e000c0d10700001c1e6030000c040c2d954905069013100f00138808a48860348541c69071500003000f03401031094404454000d8480028404080d2008951260082210b58008220700e43c8407580100d800c0307101c1c0500888001428401c21403070030050000425a5 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 136629541 1250 136628291 136628341
    0x140304060f080603070306020f0702090a0b01020c0405060d081e0c0a02040c05090d08031902131409040305220902070b0907140a0905070215070305040c0b030c0a0c020a0f090203 78
    0x100f03200d03241d203000400108a903082400141c41d0941024240358611400f68080e500490364405d1040060740c560000c001c04001742c003152a004222010300040c0c030340440700103601083c03400e4103601140d100d40003041c00501070181c0c082821210030200072260030082c10162540d000009640840c202441410388020703581c1001c074148188000080c03020481c82c5801824502e0101c0032406c44080040072a01c00070b03036003c082d511440c48003c0e0060404c118821500803404c541986c600234200340c4001e600540e00f6030340f03030b074500025502032201300088200940d015299815000401c01e00c940b010304444e40c41042c51540791f08001c48100d2500a05030400d1544210115202241d50f0b225140340007101c409001c042071641e58000c0903800e100c0c41e0340c010302980500004000c00554994440c038410b13881070500049107a15010214032a000441e005040440100a8641c440b8040c24003408041d100401a060540e20341c0c6400a030302400c0e50195001940110038803018440ca0b2003890401c0031048 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 136630791 1250 136629541 136629557
    0x30f0501080a02010f020f19060f02040b19090e01121104060b0a1107050603090706020d02030a0e010e240913090c0b0a1206062001050403021c0507140304060f 70
    0x16076034503901c1c101c000030305005481310702c00314841c002e014031001e281d1030350140c81000c60382160540300d0046001003211181c1c600411211589028070a460560b19490b01d800e0506518142001007403016028880c18400505400113503000d00600c410b0103000e0040300c005420b1034a140c4049126004544148610f0411200740701c1240008162444046946030440c0c048441034140c500705201600040d400900010400803200000510132080b1065a4200c0381100100701c01240c8a00405140f40d0000b042500c15185a610400c02030703040341801040e40c2c0c0c1c6580e91110f070214156182044401c2100041003950003498041c60819842d041e07000240050110740e0388214034061503006007046110301007900c4122a2003010020726110058000300b2081c2d0f246d660280040069201d1454590f051450040d040740d810b020710b030b00540e4107400070641d28450041080c0060500d180200800c5401c2c005113020072400a0001d0505035113201869840b410940b00520003280403001c042401528 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 136632041 1250 136630791 136630799
    0x206090111030601031109060c0106080708160302060a111005160c0203120c0712030203070605060105070b0a050601050c010204121109011d0406020c010507170105100203120403020a0b1006030f0501 87
    0x41c50480e640402c003480c00048641070b090413180b15000c2d015401c0c0d00a000032a038800b1000c015403080040e07507031460445103065034941032144d0343c558910081c8000c003a20503040005041240180003900310506020b4075207a10303001c03164a04012010b2440c4200e45030b2041c0010200721401c0c0815032581403408500b0070303000b42c01107035864041003018040640c0000f0380030002081800200e01800d0400e5802c40c40000508009650345c000484c1501c80c185040b022480540c064011112405d500240a2001d540c8800454004040081115060100822070011002020720050014041344011400000001e04107001210800c0b0142409240311000610104248602c2c078040e00c48440310014942d540c0e440c014005e0301442da1000c1c04c40d801c0400f8400015080f41b541400920502c148d45041d80e641c004000c8000d001000d1180507800c01c003c0c185014210240c042e50043c024011640310b000c4a80e01c0c0b40d039418088502100101001a05000e0180d050049901d41ca902d00b00511040d418 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 136633291 1250 136632041 136632071
    0x10f150206180a021504060806010504180f06090204030c030b09031215010912060e100209010c0201030213081f0f06150e18092103070912151b02060901 67
    0x2001e0042c0c040103000c0740d00941d210310200003210403242e0182448070003440300000030303401da005402154017003080400000c910703503c100250350440340c1c0d020040b044e803000031207400000c2141440c060a00754640c02d000ca040402800104002d61060fa07012400c6407a50808a0320400050001c528540041100901d00c5003544c04003500700d802c02e1200c8414050303640040e10080390591110f188036071580408401e011460f4402400c41d4807400588500b113414070419401ca110301560325011503000c03100380015502c02c0d4090858400360140c54004240c031103521a141c52040840c8560002c10110b91a03108002c90250802442c00f030401845443d051010222411a449120720b0401110400c1d60217030350303550b906000a170014003000210500340f0f480f0300d60f02e955140c4054951005420148184488404216403194010381e41e4030035a94180f000d19450300010300000d07660324a100c01311801c80d2403a40700783e0180c81030004060000a010032130290810078000c202100070b901d042400c4004c0c6403 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 136634541 1250 136633291 136633303
    0x3070f050918030c010c110105070c051e120705010b180c0301141801090b0a0602070b0d0e0312010608070e03010506130e0f0105010e1e1012030e0414010f1502 70
    0x28070200e101d80700010b0b40508902c1c6010f00300d400003541d800c142c000c000f640e42040d414041079103107a00034402980c80e0b50041d1100d4260180042090b807000e5550311503d4200784008144410002c01e403a102050b1460000300c50704010001c0d1540d95481e20b04824904c1e000743c029900002580713030001d0310316028240c8019404141b08101c1104401c1c000c40202c4e41d0745030490294603940d00d10b44406541c458411800900034a2030203409100040d0020074607900000c0d01808587d8010f1a07240fa10700c204114002030b0812266402c010300c8203111003101c4061b0605550b010700440d40d180a034600c1d100b04010b00c8004400a8180240d140000b03100680e00e81c0a54076100c02c0e454040460106840281c003407400081a071600c120b5440c1c4030022541850954035540103a55502801050034409502105038400640c0c0707001c1d03c1c2c80d41c091b080003c41103511b130500216010b030512074040080300c0c000c00c040d9807611022407802d080c41070041c407903680d402c80303258083c0483d50203010003000041c00c0030755a40 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 136635791 1250 136634541 136634551
    0x3050306010507060212010905010b090a1e0f0303030e240730020c060a0b0a060c050304090606030c09080d052a120304110102010c05120403031b05070203070f0509 72
    0x1040020004500340d00401c00c407107481e0b5210008540e604000352041140b41c5080c0200d200c2c15007050000030b16040f00509407445c60034004c000038011460500c44c00844028807100c603555401903400001d60500b8074055500450280d100401c9504282202c1070500005c1d2044000c82e24180042c09603d10401d030a20360302503070300c1c18030a000340361a00c1c8002c81c40c0b00d43c6181e2510104421049058096140c01030200b8200c1401162120b489600c451820b680d00d640580350070440c01f88040107094443c2d000360075000c0c080e0060346d103030a440301040e01c181ca0003034101d0300c0170948a18030603282795030008154000b070030400050000340c2e4410034014103070300c121140c17880d40400c01c1c40840c1c24680d12100c40b440306005981102e1140b411a400340c070040d001210309980c00b8170044010f5919500600518050300c40b140d899500d4042d080c802440c40c40e0000c1d00950130541d503003142c03448000d5249001c0344031003401d071103440d00c80d00b840c4105072900d001c0ba08507240c52070025600308026100c1c1d014480d008 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 136637041 1250 136635791 136635797
    0xb030411010c050f0718050c160816060c0e010c050712060f09030e1806010206010b03040305120f06121906200d0906110a020c010509010e0604030605090f06100303 72
    0x810403580102c9442484403009403050041c0f090001003c82c0014116003118101c184e1142c098290b018400119402101c15004611b4100240e00018403d000c0f031000c568400c108450402c1d01032102203507403080e400012601181c0d1040241034203900300704c1903807100100b442e041100ba0129620152545c204e48181a903070b541c1c902c4c01c1d10400016400002c042401404100f1141000e41802061002f0000921340600001101010072100ca41c450605c101d1068005003003591800402c400f00c0c2d84024015020808180920652044d440002c1c1e4064503003080c1d00c10044c14110304010019142002011140d8000b2800c17a0301d1240d2982d00b0b024450b007002001a00c00360701c0b8103c000b2880c10749049042040000740c4d0010700c0fa15540482070460098004100c42e948083c002140345c40f6991505c005a0702440301410151f20032402001c480c2010324020300c0544640f00441c1994203d50030444c0c240e91240b0400240380802c004a11620072003c0c028103260501c04010180c0702070500001d010 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 136638291 1250 136637041 136637063
    0x110915010e0114030901050a061a040303050918040521041a030a0e030406020616030203071b061b020604060c02070b0409020a05090607050f0111030c09040f0908030c04031b0b0304 79
    0x740c0d030b000340e50340c1c0403074460361004656a150504400740281001c60703c0411b02ea24002012680740d0400e020810350684a008140c5002c0c01c58070141c0b0780d41c01441010b64402c001c0c040000402c50900800c0c0e000c0c034410300041c039103002c512758100340c1a0402d05c5007040c001e030180700400075020881f100740021078140400b02d60340e40b01d600404000e00000c400b01c43c450321000a0015a4550000e032240c403418074442a025000d0308203030704400340d20007690000000740d0194012050502c001031000d921605c1004006100c0355080c03804640040400500d00c05038112408110500c803035030041e60744240c104d1000e08003040c185000140309000f140a0b89a50503808640c520800d80640300700e6a14440090145488524a02c3d126a0b5101d0605036000300e0350808451020340058042a40d000b0341c0200c182d0350805a40405200c0101810308107524804e1301e901e804404280944015402244901c007400c2c0c0c0c4a080d82400b40d012002c800c840180c0641d2000f080160701c0c00308095036002130340040340b004 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 136639541 1250 136638291 136638317
    0x5010e03010b030a1a0c0315120a0203010c321b010b030a0807210e12100606032009010e01050304050a0c0603060602070504060506040314030714030711091501 70
    0x80144610385600703806204d280c03d100240582e0400e00300250344000c134140003c0c0d951140b40180c0b800300f61082041c0340f11542c0280400c0c5880d0943c82031050301030003220b8040c9456000a400e65004640000108440c4c610760240c10100148511704921a559000740c2c44c180407510305c00714840c0c400e035170011500400000801000039082007510f004000c040301d015020701d091884044d8480d40307080b0b814000c51503144012800508030005107600c11740329440a01b41800911100c43d0714101505124040c100d62140003442ca0f2289502810740d55034002014050215155000303600c80d940140d0724001484403418a0ba03110000b130200507420f28266441c2d44480c41c00c14545400401c0003817421450400205200c2e6040d0702c4981194050703800c54140e281e46206201c100c0e0707060300625400250410040c00441d06103a0302001001040d411286044050380305c0a000485014040c07035181c00004500060041d01401040700b05000c031090005c50a000031459220301c0f00703008403418480c00401500c = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 136640791 1250 136639541 136639543
    0xa0504020a08070b1803010c0c1707050102030c0703020c03060c04120221010e01062102211b01030c140d0504140a0b06090114060409050603120403060c08070509030705010e03 77
    0x2001080580b080b91945912081100710341d8102800241c600c55200c00c014105190500400c940082182c13a07440100200d9122101e0020b902109907407054000c00c44000018024402940301e4520826219114a1b580ca00203050440300f2a0709031003544154144040c001484003190112108410f0415040344c543c030101d14102e940154800c4080900180f403107040d02c4c103400404a00c4280402005080d4807950419003540b044641e109043c09031140700401400c128498090310303079014003040040d80e01294a40e217802049008400040c030b11201c2e869080d43c0500403514500c0d01420051524101c0502c007110078080c12842084054071000410f05229800c0004038440032008291030144401c0d041600070010191000ba0083d40704000002c2c0d0184201d6894010100c0140010b14203850051405c0182c0f0001c5c0c0455814000c1c54aa40100c0c40090010700007184601c0000c84c070b0390104170018128081c024a00d0052210420001c00c1c6035901103804000d860090805a02c8050513501103 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 136642041 1250 136640791 136640809
    0x3070306031e0b01090501150e0303070c03050708060c03010b0a050d0905070b0c1203150d060b0d0f0510060501020304090f0902062212080406030c020a1709011409090a050402 77
    0xc0c18240c1120030009a2800b02d1407000c00d6540103003609940c1d0f07680c500e503035000c5500912540da2076400203031001040c9841540324401c1c0340e2005040301c1c184242500c1d02c2c40600301d09d0380116915840f01200301300100d424000664808860390585040d58504200c0700440e109185041007003140000d030500c03004040c0c5e488415015002000c44a000341ca59440c03e007250310003600400c0ba4443c60010042c582c150b03208803440340b0304070007010a07414444014040c0c4480032500450b02d60ba12440e10301140d80300c0f00c46020580d0300070443c6035903900d05814030314108082c80b402e883c601c505000b024042a41c00104403405c031149040001407000414242d0b030b0040444040c002d5114000161b10901300786ca0b2901c80f10800004445110000d0f07940303015030546000314100600c00d8005100c2040702501980c8590a03900d41e600648008041c256905420031171909501480c440300451245015680301100d500c80c01176980d181850030f001c1c030000902159008100030811030b2100001070840d1200022 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 136643291 1250 136642041 136642043
    0x503070216090b15090a03060e030d02210f0405060f0c1201030507090b030a030804060504080702030f01050103030207050a0b040312020304051e01030c0804020d020d08090d05010b030c010903080f0307030603 91
    0x5070754074603031640c044202500524044503c50604401014603070524401281ea996a0040408007860301e9595144090480e09004200714001030090074034003245800100448180000074141140c52030480c10501c0c8405030480003a03c2c00b40313007008002000010540d40005600c805d20410340e6032001010014403a1258110001503003c0000040001c0042d200302030300d6554406100702425074042c981d0380c021807613000d0000754011002c00e000c180c10f6844075801c680034401291502106030082460041d00c5020302d40c60360365520041092544c1841160040c1c14112048903840d4a0300c18065000e001b40d01015042c01c11100e00456071038001c10885008101c06041e24a004c00c408440700c175100c2020042c14007003410180280c0300b5511605126100e158020301c007000c4000c2640911203240c0d1100400c8884000803c0002000e50782c0c007124a40745445000040342d10100c0400341400c1c10523400045041c000703d13000901c0061940010b841d15064504005c5490f0f40d1201802c4000c1c20490788 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 136644541 1250 136643291 136643323
    0xa051816030210030b0105030723070b0f010905070507150e0601060c030e0108160c03030902063f04031107051908012d0b06040f0e0402120303040c03020105030702 72
    0x14040303000032944008202100c2c000c5034040c44019080c07078250203a0b1181d40040780040c13030403c0020001402075480e0300503142030702401240c3c8134903520318010340da01c00030382518900c08010400810303a40711004a03000d0071a41c40300303100724103003801d002d030040c0559080102002c509010902c03000070720380d020002c1c15142d001250007659460001800d100c82d0800e003640050f508100c0042d00794010650180503e5071840b0708200e18524a50072103290f02030b0741c8101c08141c0c40d02e40318805661001c02822100b81004030b4444d114410000b0710420b0210101c01c02c105c599512482202000c040081036489074050601d0040c18140ea071449081008540040f50b12031044048041ca104000050310203071008880200041111020b0390300e171000c504001c1240048100b40c510503448070540040c2ca80e2180600b49034103143d141c1102d140d451955400c00d10590b0100001c000c15454a50000200c01907010003440c07540c10561680c410f0301c80607010103818080000301003000c56200f00710540140203111 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 136645791 1250 136644541 136644553
    0x90b06070b0f18010c02030a0f1e030204060e190504020f04090504111503060d1202010b060d14070c080301060e010c050a120e0103020a0e150906040f050103140f0a0518 74
    0x3440e880e400b507007521102506107a407038008405120512034000e07215003540003036003084400441114120402154a01002034110088005140300400e052822a980d24007685039810b100e03000300f20b180c42e0000d5034400c0b0b00e08240303200940c1030910003006442041e5000f6946c0c01600e014041c07580304940c0040340c8180f800c0c0403c4140300000b100c0c0c1810f41000c40f0260040800303c1400881400b0540740c240c0d000191110f650700290407542607114845440c0000b103202101d5030001036840d041a003640c68000d407504d1071903803200d0402e050550302c6540ca041044000100380c845400d1404140215024019407900d2200079038006d80004908a5002040710414922490100c02c00103021440d0b0010501c58000300416601a0003075913208802231340c1d02d10305514020100301c210302041c0150304850381c04002e18031060319901d0040002e042d6070382a4000c024a41400181141c00743c4a5070481c0c0e41c026400d00c000400c8020000703403c05207d2201140544400300d03500d2983c0d60304010303850540300d48 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 136647041 1250 136645791 136645801
    0x3020604030f12030b0303030604050403110d180501050307050a03020705011401030f11090910090206070215030f01050d0308070509150406020705131b050c0a06050a0504140c0a090b06070b 83
    0x190320b0b0841010b102d240d0400c100c0b6414030040d01175491407080b059054100b80001030a84c103144d4406c2c0da000d4042d02e0305441c1c010119400c603003000803501c0f01800040d807060402c200b04590541a400502080ca0103074a0f500d000b480060847c00390305400420190001100300500001350880703810420122608051541d507840d062407042d00818045a8580162030207049514081074400c1c41f51401402400020344002c803050300420644004981c000e00070310000016850304c4c0456160a46004003050b564140710b2003e01c640c810503030169114854081078a0001780d4842502754000e01d05050580c0c803000081e00049000d00b0f070002d4510420808900007a5281d800640d240441303105603124010401d0302042482030303809880318446411000304401c14594482c0005110b0101c402c410f0b181d0506c141e5413254103480c0292904098151500103100510102a80110080b40c007070000301442101d800c080382c3d42c4080e6204070012256110350884158035810219111542d01c405c0c004964a00 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 136648291 1250 136647041 136647053
    0x2030f0304151b02010b03060105090a0905030408060f011d04020303070803070c0609051c0e060301050127080616031506030c030204080f01020a180b070b0703090b041101020f01151e0302060403 85
    0x1400020f10010341c01d0000080113070802080b040c0c142c0d5406040c0010a54580044c0c0c40039011002c01142c0d14803041000048620084c40424000e02c0071103254595135140c10045281d11742307e0307070044080040f80c0303080c400140d40000844400d20f9001e00401d03120350b5800310544042d501807502515541c01d1031080d80801c000415000c0c815034074444901c2e141290342d03904441c0030ba0140e428540004080005000641c081d180e040750b1108200c1e402221440001414003415401b58000340140d8414028071104400050748c4c0340115000b80342c20440b511035080c1d0214117101521034001410f544504e05610f241c404c0d012980a46003441c00c45036049000c2da0210f00075441920143c000821400c0c20808084034403184004039060501010700701701207602e8a00381000060a11014142c3d07e5401000040000918511a03401200343d0340304503400390000380c00d00c905980da040480e403405140d070001c00300d581c0300f4100b50b84481e40c1c824400b20346000007400d0144590030203503103c14007003000000c0211b = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 136649541 1250 136648291 136648331
    0x501060306050c0708070204020904092102010b1c02010809190c18090201090b0f071202030309010507111f09080f0a1b020a0b180a1d150102030f030415 67
    0x40308800410040c0e464400038180380c09241c13002003917040100070080151800c4d4026141c21980148001000c0303d00340c0d101460050040d807150000603848810b0301c5040e8082c41034103c03039402501c00844400400502802d0280d0307000f002414005080b01090b1020b0003081201c4014081d10406007400800e030a14501810720f52081045c0c841c402d56218150814a00485036500da041e181c0c403880c9030500032829550b4028152002c80d181d401d00400010a903001c1c403802e01000243c01842d501d0030055001425580010681014400880340c01e002c1c01d14001400c5d10404c0d81c554014120244080c01e0401030111000041c15400001c51020820403416004000a081d50303129101c410b0ba00600707030801c6017020700002e50303c010780010400031000341c0f4008040d480413070442d620401c0c2c05000020340c1d44107545c104400a5043c0380106450364180340c070b0160048082e000d40d0340102c040d400000c2d83c80c400c20181031544800440440c081110b01044569140c01c2e516050025011090804440700 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 136650791 1250 136649541 136649543
    0x30102180405010807060203040e090a0804090618051603090503070206030f16020a0312020d021308010b0a0b121503190312062403020903070302061602091803090f01091205010603 79
    0x6480c1c40000213140d10005840c1d0f0440b501c54005d54101880c0860540700803000400300c5916000d4001208001485038008202400703442c50000340081c10f002241e20195400d65190100c2858041485400c4205082e485003800d65403501003600c0081d460428214044c032400250004000310900403400110107000c0d2240c103604a071581d000945041c100c0e6101107141029004c6024501c12840c42c080980040031002d204003030141c039015550100c0d502c100110380c4103503000d954592865115181c40c020140043c45020350144c1007150100d80c0d000810405000708a108072403948808890b2402c0c0720a60900c0424104d484202c00b440c100501700314504080c5401d15803030450301203541e08101c5205401101c4d5199040c81da04d11820081c0c00943c0040101d99040c42040d00000040c1d4a54004007460104103540c10007001051040c011180030240500451031400d4040140c022000002e5a500c02c00440d00b94107a480540010388180f03000303404c55403001544d861080c00340241504001f04507 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 136652041 1250 136650791 136650799
    0x1103010c080408030a09020a0e0a06081c0503160c02090903090102060a020403051c0543030c0f06020405040203070314060306010501050912030c06070914010302041d041103010218 79
    0xc101224030807a2030304402c8400800110f414008078480e0042a445544041d10160100040d04d0700c410441a03106c40c00c4030b00c42c40840d21403005219200080c0000d404032601d900e512420b050441034050641e000060898620200d03050300400020b120702102e100080c1c000d41642d02c80d0811810081d01c0707600c1035803004d001d8800d42c0003083c1415141c7c402c603000c0700d400c1130240044058200f440c40e6003000c1c1e1702c103100402c4020701920103240b045000f040942c0e400b00011841071141006800700820001c0101c218548002d074900002c00e07003148402400f664483c05000401c066441c0c00802400b9603000340b0b4000e071010007008010b44e0154000351009800c01041621030380c60404144c0d40c4c000c01d000c0c0900041050041c0d6041d403c010160040416840043c0d0341800414000c040c984001184c2440c0000c0441740d003009903002d000e0ba080e506200a01e4107610306414207008c00c50340c50f131100342d80713100000c0200040d09114491860941b0080001e00a565622143c88560b0035103903110442441 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 136653291 1250 136652041 136652051
    0x503090c060c0f0c061c050910051806370603080403080703030e0d021b04020d0924060503070522050a05060a0501030e060c07051212180109050703150605040603110301 74
    0x113145400b0094404400d98118201065244051404058940a4000c65003445402000385800f01c030341c080ca500c500c0e129084124409209050185080310150942611192540d0204a5600500010b440b01e002c40b00003c20700050b40c0f05040028412544050a0030802242c0401005a031500403c900f5010b5a0300f444014481107465440741654181240941e001001001001c04c244d924200394140044c001410090340f400701c5802c4d60b2084800319110070303406a00341c05d941c200240d449029503250004104544c00d020129a4803140b0303008080c07203854076803000700c0d80320ba04036101c0c40d020800c41410320042c02d00d03a0000001d800e007600c60a1007501d010401282c1c6506c80d02c58030b9064100b03480140400c0c1c0f1140030100fa40d500240058405009083c50240c00d0b6032114001d00000f50b0414a001d450310305002c0c1128680b5025401c9102641000207010103d40c0011703549060b203030070024171004a0402100400100b442d903101c2a040350500000001703001e1000a008601c5d20164006d102c = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 136654541 1250 136653291 136653313
    0x50106110f0a03120905060901091211060f0406091401050a06060c0b010b09060403080307080a0b090610030c0504080f0106030b1302150304020d0209041b0f0f060503090c060c0f 78
    0x5111104018482202e030700c00d008410100f8030801c030109803541090700000704402c0d113880c0c82e030801508030f5045145039141e0540c0b404003c246010540040d03200d00d4000d2070b20a50100041d241c48001e0071010403204500c000c00c040c403100b9403061118951154125410020703010806001e050221068440d69180c5000020413078016203603c0603e5511040c80001c580c00e144130240c80c0e0b04070628054000c00c00b0f202c007000180e1100000c0d80038540a40f01c00700300345007c0480c94181c82040c00d98034000e04030380c0300f4420307e41ca9800400c400700445080c04a00280780031000c407010b0260343d01054140c4103400c01941c0070401940007000343c2c0c0c0103002004946d6a46910282c0046000c0740c0203400c040007904d03070001400b048010b550040d01c000d0a1070765416954000501c4010143d40a88900e070980d8006c003040100c004170030000b01804000072410300e281004800c000810752280106124000001541d00c0307d043c490a00c40c1a0700900709604e441210b16034a036034980107200d5428501c039054800c0 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 136655791 1250 136654541 136654543
    0x303030e0609070b160606030605010803071b0303050f070f02100507050f030a08070c060e060709080d09050603070e030c1309030906051804090204140c1c022d0c03030a05010611 78
    0x282ca405070790040c501807026500110081c0705030310035246c1341d46d64000880040d02c2800b03007600908194006503240c41c041c1c00c040740d00e881c7c1141c1d20300c40ca1252050410010741c00c1419214070403100454280c1301d50b000d040a15500000030030082d40840f407002d14002c4107070880041c0007424080d0b405c489060204107111341d9284101407641000c01c41c020f00085e1118490703840162054403070352012034032000b1140c0310340c58148141c80340030118a6000041c80388000c100b0007504141c440c0d240c02c184803490280400d0032484040c3c804d80c1003080f03620440d241510200003800c031144000d001000403544c0c3d031090070000d000380030b82100083c2000400040240c4920161025400c0ca60380048440114000300320003070009400032a0855201c00c15a00d0000c0e04103404d5204050b8110307855031301d2980f0f40b9034280b9500790400d80e40c0520320520450300360000005044100440c501007003400e4455120304400315001d901ca00540a200c0041001030203083ca4008a04171001503c0e20710880051090303803 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 136657041 1250 136655791 136655803
    0xf0204090f06140f120102040b03160302030712050606070c090c020d022e060504021303031112030f0705220509060a030b04110f0d0602070b0c03090a06051f0303030e0609 75
    0x1818046a07041c0c000d03501884e0109151181240007040e040e1145401161603003aa041a404200500400700030403109c40010001415032000d0f0f8502140381d441c0421f400740050001d203100d11622036440000800310703110407089503111908000f0340410f4035030342e240c500e0150850111070300060141a41411400b0700000d880190b0b081c0780c507600040444041252134980d40304025600381e01c2e444540019080d12644010140c20714032440d211031190a50402a0052009441400940d0b102c00542c81d50b02c91102d00f41d075002400076100c2032007601c0702002254140240e855021041658003c091045800c0f01442003c40c0e00c1074659412035036a02c02008050041c40c40041d0504940e0000180068403482c9940c05a240007070051002d2080703240840c488159010b0304441480e170000301c01d011f0103c00300311298000b80d2213000c0d52031490100307062034070b54003442001840591a100070038419030b0003100105440c003001840001042c0e40c0c0c01c00801402c039510700b51905018a01c00304103001d202240c0303 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 136658291 1250 136657041 136657049
    0x605090403170405010b041103060406080f070b09030a0c170601061b060b1203130602010b1e090709030b131208060616170415090602150105040f09060f0204090f06 72
    0x1d1104101c0c95035010203129100400484c0c0c0741d561a5840102544d43d0b102e0100214103c0385440d407246010000d000c00c03202c0301d410940c0706621001c000034403607200040f07460035151003d02c3c95803125802400f0034034200d003690b00103100c00703513124020500f40300745507001c43d980301c07118115a442d0b40d072128190703105002241c4076600c100e042441440451015002030405100c00f510600020740161016030868010716a41c40d241c15044c1c004118440e070900542820b41d0003110b10703c11240102c0030000e40351441d0f8940600a451100015070070a0081b40340d4001503402060b400302d0341c9032641c144104c404440c1c1044401050000d2240d110303c6c820001c9030700c40e05014000d03e01d040d0f046102c449410750315140c11640c1c00c0282070303040103c0101744050030040490014000e01178404080240030150150881421036110030748008200240d400b42c581120307400e0724000ba07914040f1207403001404804401500160030016001d4900b0020783c01042160411541041010340e40c00300313002039480d9441 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 136659541 1250 136658291 136658297
    0x60c03030f091b0907032c030a020115050a0510022b1413030b10080a11030d02120307030c0c050102130311013212040507050901060c052a031603060605090403 70
    0x40f178a07030003940500c0114410000d101500c0809800e111444902c00300500d0403500049044003104e40c090052054103142080451602410320004c035450341994465144203002c2c401e000c001c514000e2040414901c19199003468400c65039800922502c84040e00340300090680b5641000314403007200340d40400a035141c9528901c0d07d1620350140425000d1b098260a00014400045a04042080444882c410011300301b2841c3c0c1d03c0c0c02c050a200804240c0401e54001c2c02c3c944904e0080b20701100c2d4030100d541000545405c90040448200b62500801000c1d580300054803175490b5070414000044921030389960000350140c0b0011180741e5144003e95040c4000c855402c0d03660315500484e03032000c40c0000c9e07000d42007100214503103051040c00c1e642625150012101400b0034100049100d014102c2800c01c030f129491540d0b07401c2d98541c00032482119817002d0650603c000d05c0111180b40c0c07180c0c80103044034440b200c031602c0c920310314070180710480781c0341d251690000719070511584071485190591 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 136660791 1250 136659541 136659559
    0x702031606230c03071506050a0303081801060315050a0c09080d14130f0801050c0304080403023c01020c031603080d091208091506030c010c02060c03030f091b 70
    0x72881c400384030b441400101148107000c568500308040001d4940c050183c05900f84203840c00d152070003140c14940005004599148081c004240c1040c0318540010108140f40b1440403000c00c00c50051400b90001080304030b41c1008000700710115040207000d11048002000130503804401500c1c03140c0e05208a02070b0b500440403c1e50340c42d000d4030021940300795580ca080e00d007103c0c07408042000c000035080300115460184090041c0b50742440343ca68010250700030030349541880c1c2c54844450040d0f1100920071040000c00c013a00900586d18903400500c90107491059040000c260951660680721060040c41028250407962400180028013241d01071200e2122508503260000107a021804020407291100d4941001990040250180119030b960301712441c10001d00c0c0e5410080d000e0340c00344600d0240c40501009503000306000e002a8400d003050185035010b0b1001c64900d0141c082d846080c0c0c00040308212042200903078507072041c00b00038151007c1c5030345456022140c002c000303080b41d04100b8170 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 136662041 1250 136660791 136660817
    0x109030e010c0516170f070f05120f01090506090115030f03050c0307080a030609060b090a0605180604030609051e06060112140709090b0d02030a060203100e0c0702031606 75
    0x142c1501003407030340280c0a03140003d80e001e442c544400b18590042100c030301818150302810100f8445142d4054a0102400e0105c2ca0411030110030305c034902440b840740004c00100d6265400c01c00c100c40d44681b0750002408031620a050036500c5000455403017506500701065003031b2110590382c8581c1681c2c0e0018003040c905c0400d49003159190400c0806450601c42000711390080f4050070094650030314503030740100b03407541407161b58426548168081030b08440300344111566560f4a805030015142a4079006132105007514208420916840d010f5130005000070380030041c410280c00045070180201d0845490f0015402e0b482142482000740c1000340d08a00042000c5602c01d480b54050f0103480d24003c00d20a448120719000804142d0305d45000c9814803008000c0203007a4050080003400c1200ca004a4015940100f03844918041c0018085d550000024140181c0c080984014020206094840d0f2410001c01c0601c3e501214007a4420b1050118040320030300e9101140c01a56900e5548030044101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 136663291 1250 136662041 136662047
    0x504090f08090a05030727050103020d14010b0406141206071b03210c0905030c01090302090a02040b07240b0a0e0a111c0f0902030303040803090703020d11010807020109030e01 77
    0x82c0090682c0f20300304620026195404104e640007400e407030000e10042c0043c2c110600c0705035a000c0d51942029041000400250b50340302104401d0540114150820f58000d060240c01000d840b01c21980c403504e844404600c881030a40d44110140050343c416416050400605079200d4040321110005440c0815190f00040901c1c1000b01c0300703100742044881c407440404040035400e0700314241320038560781d4800c1240c0c0c1684501c001d001060243c0140c00d48030340c084002008202c003400007a004008400118508908540c12140100f11b18100c1070f841d1a40c625040c0f480044001c07035a0031908a108811040034018030501c002c00c50020414824207140c0164415402401800840307a660341d0700402a41040c1007006000003540c000100c1ca40389071441060342207a54107010040194a042013110050701d00204070390304160059001a1269941039485141c4615508002e420081080c0c524003004005490400da1803001d0b01e0b00c0c410741da107190341203080347c00308000940000c0c0306030627000303003940 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 136664541 1250 136663291 136663297
    0xa1d01052b03020c030613030e090403080a0b060f0f071502090906010c03050c0d08090d0201141f0f0b0304021309150b040204030605040b06101e030b01170a0e06010504090f08 77
    0xb100c0d00507a600454080c0000703081c00400c880549504050110040c01c25503c0301000c2d070340120807580a601c504061320000c140800050003900b0b4566501c8c0020301c5982c4150584660254200d2040e82e82d411400e000c002d690002e040c00c403140415868010f610000500030b40c1d0810001922144481d40e48600455507161074600c15001c3c002c2c1003124200c4080d06000740e06000082e17403030f0201c1c14180f405086107030000740d1008000b1649443d00048542d10000061600201c40c401070301183d4006052008020312542d020500c00314000e01d000556001c2c48000c1c601c100d0080b191010300904d543c0101042d110901002000c0c41c1c451400240140701503449101c50400140c0018103058481c0d941c1d07800c070307802640e0540c2c4499248041244503d4421000c004031045443d180f00107400c00c2114a0510850040c440181030712020700f0072003648908a00061070218400a0016041010005004000c4d8032034a45103801150000314090905001d46030405910075000741d0714030b8194841207050f030 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 136665791 1250 136664541 136664543
    0x70b1c050a02040b070f1203020f0409090c15030f1d0307170c10050a1a0a0b0702151602010f0807090306050603030f07140607030908040302120c0a1d01052b 69
    0x295003400081451381c0f281004e8a940b40c4101540d502a0780d1038100f5080e48541e030000c1d1000c1500400004004070a104151800c445d074000010a03040114035003203107034240c590420354480c5900d4000140440d03054018074204103800600300034041035500d9404940490400e45070565004105500000312855501c442151402001d241480401c3c0d4003c1e08140c080000d04c060103450300c0a000103900c10307202c2c165600200c2146401c5007035010300131600690b407a05c60488403100201e034600a540307071140110314140317102c030800c2e030b450303d0340070107441e1488440314180d0004940040843c0310901a01001d40603008640f2280203840c42e59603031720081c000080c903041e0103000600410224013241000780004522413100c00c1d68143c041d503c01860a90014908070401d42050b0480000c18082021501666010749428100b0906040c45500d04522484201d40003100c8080001c0c0f075034200e80d02e07185110718040300480c507a40d81c0c004000040c868548040d241c8124114107841e084005e6120202c02 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 136667041 1250 136665791 136665811
    0xc08071e080c030403051b032a030a0303061409040803061c0b090706260c03061207080c0102070f0e06100903061401031103010219051803060c0705070b1c05 69
    0x5a8095840c01d2268000c00340c03041e110380c00454244100f040621040c0144503101d41101c4680d000c0d240040d03030f12040310301101400340c00600c20950a10318180c0100001e10060100c030001c10113441d008004100c04c3c82010180d00c21000d02d0185840c080c440300b405940c0002e03816040d0784640e004c12003184013908040b030007124108503140000f0044201e01d84a0b4183c11302400c1d4041c507004015090f01401503034000183e40400c2021298851060066004170740340c40e44d80e8890b910301010a5200c400410108403500c100071001805000020702e48000910070390076a0903083d6074440784800502180140d2000c1229000000e01500340407441217840030f1503142401e100317540c0b61151000c03185012000584005218018401d2000700c00b86800390f01c0d1b0940c001c5160014603401d610b80d00f115940d407001081400500c0010600910125100905009054403200d00b040d4003030b40c08651004904950b01e001d10000040e0261402c2c040c1c0703807800001e90b900c030043c0540c42e910f04010003000300b401401c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 136668291 1250 136667041 136667093
    0xe0703030f0504081f060b04030c0312090b18040c020c03060606030a1104060305100b1c050603070801060e090f0a0803010e041a0702010e0c0906010c0204090c05100c030e010c0807 79
    0x35403010014412205e01103000070040d640016800350a07104a0b4000240c0c0303031410081040000d140910410440750088450100320310040c40496003407089500540401c01c0c045a5801c00708102e1406d03003a4140304460030084285a01d5082c1d8443d2078081e111540347d00102d00080450401000859004422140020307440320b0000b200724054105800090000f03503250100142e42c020007000d040604600d03031030f50742041c810390901440b0000b80c3c100c034010a511640030cd5110707182007040c90041e000c0c07403000b844041e85030340c440d405001e0308460080c07040c13103103160001d50b4400c00705100350181e800092080c0340d0313824141c2e00902098094412151050182189101c0c00c1000b840a4010412680081960340e03245051610709103102801510810b290030038480c25a07082625140c165a05480101301c2c003d481c1040d044150340d6a00c4660030802070000340303c41651080d12514010b2194591000c4151080011114041001c8000700140710402904002c65a5004001d8500300000488c3c60 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 136669541 1250 136668291 136668299
    0x7030c181716060207030b060d082506050a0f1104150507050c0312030a050709080601060c0606030506040804050924062a0f0d0203130303030b0303040e0412030c02010e0703030f0504 80
    0x904446543d0200c401a0049030082c0100644040b0047c1c2021040300c603034000c001c1c95160300d11640301e28200556440c140e001c04800c91001c003070204c00c046401800c2005949415000400a40701c01c200d1607000c10b2500130417248220040701501d0a0319800c0706420003e609542c2c0c240c52551000205840c1d600c11079000902c2030341c04002140000080c140100e4490410980500503903801801e44c2003440b010580c14044241c001540c241158154617110b1031072061820302c01c00904141d00007400750301504c000c09c01440758100003801140c4003074032811855510700d80703444000302c0300744101603019446411440180c90110007808880f01c02c3c0242031003102144188145040c0c0c10280071100d50020702d05c0390824003050059211086180c005189005440d07116825102d2950000038249507032400100700c9a103040042d6000751401c0e006951460034281052200202080d40600020b410010f6000c3c0c564810b02540d4440410a13000380030880c00c42e0303400d40d540102e070900d0004000050000007 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 136670791 1250 136669541 136669573
    0xb0d0c0306051e0a06050906011b02060a03090c0e0103140a17071a090a0501050a0626120703030e070603020a0516060b060f090a05030a1709060f0c0607030c1817 71
    0x1340a07000b0120001001460134050103040c1500034062414024107648074020f03110000d4480e40020390403200340da9141c1d01400150024a440130000d000e690031942d010404184400b012816207010b0b024170650f81040303410540d03551000160003402d280e25000c00403450100d04e0040e00d40c642c4540702c1d042d11918406aa14140c240494811f1542d42c01400c0d05003d100c82072061640102204006205003802d004032803461080790f00040c0c0d62040d0301d0700500104513082c40102d044024500c0c0355642d80ba000c5c14002c019045500210149001d01900000d401d8000c0c42200c0800c01162503860500d030700221507600c1042905030650b54203403a03c45420281d511000101184400802c1103a1905180b105100101c1c0c000d8001c0c40c041c1c0e026480c4040840d4000c1020541000c10708245555904080046060f500882070744144801001c91a80e00c0c042c1e020844912038649903400700118840000d080312981c0003120440450040660148030109214449401c0c803d4113604541203030810a5000d = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 136672041 1250 136670791 136670851
    0x60b0a08040b0105060306030a02150702030d110d1b02010e012a051c08060603090a020d0305030a0b090606040b07060204030804090212011505032202030607020c01030b0d0c030605 79
    0x10000060380d8038104020031403940e0525004d4541a03c0c854118500440829500e07568581c0c081d11482c0300d4102c4003042d60f00c0e081207400081e80070b010765566048005010b0400c881301140c220090040760320000500d84030740c0c00103410f207010301c14040300180290015a46100580d0342d6030f0400203016003904038502c82440342080c90340503040402541c0307a1404d146092074200240b80c8820342102c8402c100c41503108450941114084540c0c1e03550b5107960204529009100701d00035008030005000c8014150010095171207000b200106000d40d0041030100719162508485c0a030b841941440280302d20b91582c2c000d011074034890000103140a031283c40b041c1058106138040401143c0019020704401991030040740100454a0840e00401c1e40b203901400301c0c040241401e206034501c4628542c62087c800310321540580181c203032580381c28503000094994000d551094007090400400d070600c0d08014400200413038110100d0b0f4020303401d55640a019010141102d51140c1030348a0728030700f01d0401004 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 136673291 1250 136672041 136672057
    0x110703111513020d0b01080d091a040504150801110703080a0506011205091015170307080306061602180114060a02071401030b0613081e06070c02061605010b09090610090f060b 77
    0x81920307501c41c01d0f004001480c0d42e04502d80b5036441814034411484040c0540c2c00752033080303070042003d145400050200110681c4408015170070100d80414030108400140b030b047d0300903512902136a50781c0e44d9110a54506540050005811124040314010140e0003650404c2185050b5070f001841e00400d2015038506802000402030381840c10440615048007216800c03804001860400a1940b10a0010300005203c07500510000505401c04014045038200c81a4000d0510760198140000108004c60034094544241c039124030480c2c070741c40d0081c03d99021a02a81c003c104543c1019002079480101c1b480d020f0501d030320351480305101c3e03071104040c249120100094420840c9010302191808074520124101c01040c00c03050030014038040b89480d0302a01718140b04280409a1001c01c1b85449403c101c0c85491800100102c100700064000402c04482140c0c070300076540398098155103c01050340d010494000090040041440d640c0141c43c401e000314100003201e50b61082e0003100c551004074 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 136674541 1250 136673291 136673293
    0x3020304090c0201050c0f070503040302040c110c0420090a121a101202011b140c04060e15010f090f090b120d05180d0501110703111513020d0b0108 65
    0x40500240846200b028454601ea1000380428146405251801c0c450401010400500010f415080c0002081100c00855020340304120103403001d00010031203010112038500d2806442a404502e280c1809240d0860215480d2942d0703000c0780c04500082a400702185c543c0000a960002450302c0403190603005603801880111803c6c0d0840e00a401e12104c02050000f4142201d4814852600d8102101c04016420b00305040344200c0c8441d94070030b000403103200405203100c2504000070102c0c0850000000c11081d101032054540340c20300c582e0041011505a0307524500c0702c81ea004e0300e40c4074503c021161583c2c3d0903d0080701c1d0326010401c081d420640c02c40c030103850b1039448040603800c01c6800782039640311860143c44001c2c07503498000c00c1881754401240303d40c00062654400c0d0754402c00c1d264891940a8000c0203601c160701d031510002c0d000300c10181e0102d03912030403160100e2400b0a081c9100515000e54011030768424070f07144c07940008c01c181681c029211440610000b01c1c02d031040c9010344a400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 136675791 1250 136674541 136674547
    0x1802030601030f0b07030c02030d0c030216140c01051e03100305060a02030601080105031908031017060601080705070b060d17070c0503060a270201032325020a03110c030703030203 79
    0x30404141e0241d01170b095000b0580341c112200d0745550b0100c19140040710302800441e0b1143c22080403000fa010b41c90145034000d1480c442c0c0d10811108003440280d007190203080d144690107000040d9020700600c1e00c10b410121202017200300d44585c082c01158020f500711506146143c072a01c92514240046075400a11035000003030005c0b940c2c000c1403a42c0102400c0b40103081c90103101e07407041c08489248600a1961501002044e01c0940301c2c003100d009003650300c0c10340314100859101039554940c243c03855800300b888180410241c902c00c1c1b0440d02803a1300100035200c0c6889030014003c1c5520a60816507455103814240302459424100a1510344d0142540d45611360400c1c08060410340058042c410780d034940202018182c2140240e000300300c14041440c01104c1d4a0f000580c0646001c1c00c6154003004001140e0301100c40e52280d040c00f401505201d56541001c1c0d0303001d40020510791058802581c8008260400244181e0310301420824241c25151618010b4000c00e140c0782890b04100c000d60004 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 136677041 1250 136675791 136675793
    0x9050d0c0215071a06151303120305010807171905030d0f0209011709030f03010e011703070b16090e010605120c09010c12050408060a0501050111010e0c01031802030601030f 76
    0x7096a111000030342d6049189484030980d02d0404001451180d110003016660000d00d803555020f8041d40c01c4503960394015079540c4000c0e120744001c0001d00040300c11468411061484030310a11520341600c68a0700200882824815050362803a80048190712520805400e2010000301200b03222090780720384025516040c80520040030340d175a450030900792a01c18046030104e0f0307901111003610840c004159041a407500c1079030a04511078400d140b20700c180c0c00000015010b2044803198100d880000d2031444101c080c4048644a124000010300900740000c0400c0442c0c030418a40451691a41000f203226070750b92010404512099020382c0102e4000300300429186814031107568070610900c10359182508490003e001345040c048090407450000b414000801c0c004c900722030144c404401210014901b0b892008003600c024080e035030002d00c0c010100b40d491001401041c242c180c40c90080c080c000b00103401100144131f41340c000d0081041850b844800340e1801d00010740a5070040010300e0580c0d0003 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 136678291 1250 136677041 136677049
    0x150c04063b100c08030a09050309040c0504050108100f06080c0d060e150402040b0f0f07060501030506060f0904050c01030e070302060f071a130f0c03140d03060f0e04080c0109050d0c02 81
    0xa101c10210074482421020b20000c3c90320350417298854000800002e0000380c90601034a1406040d43c40c035000391030440b00c484080c0d0820043c00444000b43c0e03404c5847d5840300c192802c40b11492040d031041c0c9103011002d000301402000708a50142803515440d0826003d600c40701d00b91801c4d5484046051100000d100600c80741c101d2182c4d003001c05481c190715103841c01056082da4031a140080c0e0482a02040c1c0041480b202000c5400c010740160003402a5611303410f0031a1501c2040d02c5881c8102d01042c103050b01802e003e11804d10881e042000b41410b0b10b140401940a048500c015110728024941c000c00141d03030b00700281000c44603601d18541c60f11110300c4c0c07001c80d50742e01040f00042005041c08200d4071040e07481d240d0401039408800503282d05440d10704002c00c014a6000100100e4281c0e090000200001824000c5008075580030b000311607469403140755408641c01841715901040700010302160500004129820209000103a20500e50b1683e5051442c1802a4800154148420019403038 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 136679541 1250 136678291 136678309
    0x50c043803041506061409100309020d080a2d030b01050c0d110c060c06040f0204290f040608070e25080123010c031211040909020102150c04063b 64
    0x11850038070146d8401d0b1018a40c0d1a0300941d60082c0c41442e00491203441d4a07c2074004444690b030240c0407010a51091601c1d60464110841040005400344c44200d21480c00706c00d0307020085001c503104058030f94100d801f1409042d100f941c1c01c0c18444208040302d2400c004020285142d61117540d40e95003452403842c440c0c200203a000c44144580014031a01c3e9010b83d01150464219520038198620006036101140107081582c0044107282000c051001450a000209280c0e43c0c108032841020070200108201c02c5440a00540700d80da4070040090103c41d402000442e0010003030301080c5115010f180310400340009000485000910300303401006190342040401d44d0304803100840819540070580001d003c01c60845003e8100680310040c080e00300c5041e41300c2d07000d00b210404010740e180d40703030810840903020714041240184115120004082031040d0402e0081040307403022441c05151020451f54403e0a240204a9040d040410b2411071030700044880410411103074074119150b07000030401d17514 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 136680791 1250 136679541 136679549
    0x9052101320c04030203070e07090b0a0503090114011406070f060c030912110d081509011e0b030405062706130209010602030a02071a0405060319050c043803041506 72
    0x2c2001c1c44140016500800c0601c2904c0001c40c2492003075070b841d0811031707086042d030b40304a9540c140011102d468903444001140308901c05c42c024000c0c5401c280809242100034881c604145c64a0781030204580303000300c02441c09600404e0310040440c1030341c9070b000444415054100c08a542c0d00c27801c0082220080d40000c600381036041054000c10b00460141c1c9030010751803020208561480061490410100e2a04058034054030340c840560311030318104100110210707041e81c5032800820020300448050120b0b031142d540304018150585404030301880e0900c0c01c03205500000b071120880180302c10100306491040072102c410280c0850300b401130003c84003060304030104540013009034a042c1e54001461808546005030102d4114800b281c60700780c90302454000300c1d40170394004144154005130742d8500f400d1030a01881009203440e407103d502072600c5180304554401910341102d00079032002c00400c5c48801040100040b410702d05000d50103107075100311000c80300f40311022018502d05030548102400b83c = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 136682041 1250 136680791 136680811
    0x506040b0603130201140d090510050c0c03092b0c1409060f0f03120a0306091104030201020a0605220807150c0e1306091503050606010905210132 64
    0x541040c424404809007440f501a041c440b04041c4482241031034070407030b80703103c0a16200b0000c194a602d007654660b02c02c1030741070380c00307074103190200380000710b80d0303040f41c0c1303e4100b040c0103601c1c040f110018040092400720600221000c0708040721082c00700e481d41c0f400020311402c0000e00c10ba08014008081141e001503190288290104020b09500d42001122840790708a0b0350303504041002d40020b29001d031041c201e80c018180480c2e8440e807560142c2000081d40c2e07038500b00f0b00641c0c1c4803022204480c0150300c00680164030041c0c110000c144103900c031a41100110b004100c003680c0ad11013206a991300e50318103c606a000042080600481400740f40384a901a0000d0000b0100010014100f0340704c010fa0b41d1080d5041d06801d8034007001940910020101d6090034400740d10420101102400984410380e01c0b800b5400000303103150302c10b540d55400e458000f000007414a0310a404440041002c00c400c8001d0f6595400d0b20b11302c41600038916400c020b040c1030000c100e0142e010303148002413001d48000c80c4 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 136683291 1250 136682041 136682047
    0xc06021006091401050103051b1b06090615060c0109060612030e040b01050d0f09022707080c1c09020315010906090203010b0a030905070b0d050412020a030e1c060204090506040b06 79
    0x10018140303281c3c5045a800f441e002c0b90030389a1001c005004440317900007406a020005a100d0000b45030300303d4908025003035003a12259600c207401140c5072801114542030340550306e800502d0914041014141124420000040380300c8559242d01c11076215402c5078545a1034884080209640440080700c1064192010f01c00c2c01030110000c1c1c914040c000d0045605038548003080440c02d403e0f8400c00c1c00030340040000104183c1c451a1081d03234880c12a10001c1440000700081c03803903000b8076482c4d00510b0405070b620716001401c00303012080c5841040c582c10742c1d910346d0103480259404000101042c01091000c06c1594507000d6610212051076005491080c010f100412068500c1c0c000d5502c0c0c10554100455407480501c0d281341004501d0f00421000b650100d28441c091000d0341c000c0340704a01c07910b0030301c122481c052400d0303035500e0712006c00078005691030000980e681403140d0f40e1502c60300c40c209014049100365441c0d0f001c1e070f0440c0c1c000101855840382002483c1c541400f41d6160315406a0750246 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 136684541 1250 136683291 136683311
    0x14011a1603080c07060908040801390908010c02010c021c0504050f0a08030316020c010c050309040c03020d0218030106091404060b06040b0f03060f062b02070c0602100609 75
    0x1800030396450103014812003100190020803a601120001c5922003030404c444203072454598080e401600a1450942c40c140c103003415010070604004800002c16016050400e00c641d010655840d001481410801d59420014007410b0034000d00208610940012400501d540d800038036002c6d010740881c81c407102d00380751440c980e50030074121000c0d80d005031649503404050001186540c4060b80c04104140300c00000c00000c542d8880070031003010b03016420b907015400c2150045880101d0401c0c0a4500c1d0410041000c031441c0540c0b00d0700c00c06d0300a05000d81016902907002080b6040b82c5228000d2a11b80000314580340703001c0c400c000c058180b100003041300e05400c0480c50981400140003c1a450b41c480010600340d0780d65095030001c1180b42c09465442c5460250f012164200742d444034040d150b50f0b6007640f6103240c104280e840400003004503100d445d100080901c50201000c910040c0903a08002000200703000c404803002030085500206032600c600412401280c0240c0c0c0443c000f42e00d4502080 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 136685791 1250 136684541 136684567
    0x90c0f01020601180f14010602070311060306060f0307020f0f030403060e030c0303011a1e07020f030705010212091f020610060504050a0b0f120916080c0901052214011a 74
    0x1244e440d2407401c00290131070b00f0300f400d80010044e52100441c140441c0c4000a00640d00003501c1c0d055a00c07138252f44c117060024100340103850005840b01903004200b80034048014400a0146a006e8920b2046403041032a0003801401e010b0812050200c2e038000050520901ca110b00806e42500071020007146882104500662280818010001e0b0054068a000741082c001404c1c2ca1101d007a07518a03107040356000d0042041d82e80030711030890203400800800c030075521f804681e1104560b03040cac001e00100d100c0100315440940c00310f94180d50006881801e940407082c1c1c501030001c101c800b0f80041625007008001803103002d07450b9001340c0410000304014062500c8000c074800c02c40307910080464640d00c600e41c0c844c41500071010b0110300c80384203008001104200007075030380380008500d075106405510f41d031890352a001c2c206480754000c121071300104000e080c070b40c000c07810440002580d400d24070b14050205043c0d0740136000e0082e00c500c0b1003005000002d0341e48903100d442c0c40030310f021130300d00401d4107409 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 136687041 1250 136685791 136685819
    0x213021801090e1302210102070606080102090a090519020d09030905030f0c060f04081006030c05030304050604030b040501060803030f070305130b07080c090d0b040501050105121b0102030909090c0f01020601 91
    0x18000e13007000004500031512501e0032131040c1c018072180c50030703104211342c141d80c002e4008500a48402d4100302000030110818400c03035842c21000b40c0080c500504000c0340380007412010b807400da0140c00c540714803460b00b60f040c400b800041c66078807404200b102d0241002003142110750062442034110080036140643c0008510071045800c0c1c030602e88804082254052600035035010300c0c01401145140c0d140300c0000e0b402207055038446c1c02d011a0449e1607400741540d90045004443e000070f802c0009101146012a4035a03000344610700222381a5110080d2074210342054850403c0069034100340f1400d1034045c02159403229a08141400c280041d8a5a41e510000070382611305000340b84d4080703903440302c07031008841070300d10054000039624800d403402100c818801c4500b40c2d103a5107004000b00d0a0b103404034032004241c0010004203c080004074038640e15610031951725056120820011001e505c2c0c50000034802d002c01e03800f03407800540c0707041440280365481000b0b0b8110f40244e0011300248480a0300 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 136688291 1250 136687041 136687051
    0x81203130503160f02040524010309050c0d0c080601090902010f08060a0f08163f0b0f010302040e0a21090305060103120f14070605040303090213021801090e 69
    0x101a0030a481810308504502c21a51600034111014000f0414060360329409290a44296001c10982d42c5454031038014070200081044815141c14a0321280d601c03039009510558041c9068070740d065460f41c0007030312a08190100310b58400c141c10081200340c00922540340100b9140200740000352082e40001c040c021090840300900403580045a0789880300c0b84604060700b00c030303042071840a44441815a48034000011240c0500810101088081042e0050482018900c18404202000703415485890010070000c44a00207030384981d80101d540c002e5110f0258040610000b440e5056006001c1600c000440840240c2d0014404030001406164929406041140d0003c043c01c02c120084030f4900e101c1e800500b46d845010000304c00d110500074a0030320f4025907150100a4804000b003560300f5030108802420301070081c0712000104240350069a80180301e8940099400c3d46503002032003010718444580c0700264049010041c2000303548031b491641e0b0090a00340d1042e03240c800704010094000300 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 136689541 1250 136688291 136688311
    0x70f0e1314061918020c0115060503151212220609090e010b01091403010906090503030f180303010303050a050c0a03020a0201031d070b0904150e09060726060a0902040e060a081203 79
    0x303210321a8820170341c051680c441c81e001c088043c0c195141402406030300182c03807024014511a8cc1c0491910b05412045115803407400600016401c140c4008016040100510140c1c0240d41e0343e0714040e04c0c818400b030050225903ca4040f821700b000c6600044901060b01507500361315050318102281c1e0000e0022007144d03c002c403044480103000e000309024161910300104400e00700448030301080000f2024612030314600d0707421043080da82d48849044280b040d20380006290400c03c01403002c203100b10020000850302e070400318034101140400500c2c1010411080e4010381102403144110b41c0d0500400c0c1c0340c520b410110b403440e903252401e00c0d030315414188107200070f100700052030310096101d5400c103c149005510110074a9569407803109000715040320520148d001301c4002458041c095826942d1401109a803001c8008480300d00c1204864060040d80d8080201000050f50314054001400540441e54448145080c08020300c0142001900015a940c102440b48004c1440c85001e6a40c8098002 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 136690647 1106 136689541 136689547
    0x120111280e0619090b0d0912031a01180306140403030621060507020a0c0b0903010501290a0e03070f030506070305070f0e131406191802 60
    0x2100d001d0340502d050000c0098054090f0210903101968200700d808280c8401d9003419030b80026059130342d03d54468204400304080e00200740c1c003104440c1002d0202a280031001307824250402038850401510b5030499542c2e40120050030002d540000d420010240d0794103100c0b2480501712801e030003090520b03500091448035801c0d0900c0b2100c01148841500c2e1040c1c2d100c0001d0b00c005041c03041144030f03500c0142e02056005540700e00500341040c455644001c010149400d6402c1640700040420182d0402d80c40c80e030303805a00c1150741c41e4800340550b452011140a031810b828040c50103030544200900800c00700400394408090b64090303402c941700741d95208002c50a41d64111800d0001480e580d60701d0100c14000c030500040e0100040c00d5188404081e5102303c01c03210001521054846040c042c000c40341024290115065400e410106d901410700c40e6284001c4103240e40c0c092556400 = true := by decide +kernel

theorem cover : BRFrame.Cov 136510791 136690647 := by
  have h0 := BRFrame.cov_init 136510791
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 136510791 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 136510791 ≤ n) (h2 : n < 136690647) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
