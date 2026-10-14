-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0744
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:32:33.125606+00:00
-- url     : https://prove2.me/submissions/6765c1d6-4e83-492e-8b5f-cce6c90c1fd4

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 133633093 ≤ n < 133812949 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 133634343 1250 133633093 133633111
    0x6060e0d060f02121e0108071d0c07080a02030408280320030d0605040605180c0703020c0d0c05210712020103021605061e010303020a02060a1718150112030f090f030b 73
    0x1400020b01f000d000c20440140e030702c5124500e00c1c0c0d800560300b54116102c06081641610802c2003568086008840a408100040c0d4060341d0754500e010a42894a403811602954211240200307003002400224080c101d5039150500030740240b0201c010519a060301e05400b00d2034000001c0d113807071880240d070005059072001c5034208145620340f400d0050f01c0b02003500d6500c03100c10820101e41d00058240c042e049036032003441219541d9408001040d000201200e08031940c800424041c030092500d400102c03083c510300030807030302c040402e1900369035075607114031542200f9065000c1c0f02d07007564403e030100c40f1180f094140743c000818652500641d13071441225140b07190100c911a0800c1204185d1406040700d17010740c0200801c042c90303002c0260740d600c4507034010f0501c0400c91001400100006990384500c004803080c50250002021060410510910449464045500601c6070031001607004071055018500b42d044400050340235540311001740c11402d1510a00840001004204108944140408 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 133635593 1250 133634343 133634401
    0x1240e251701030302011d0f07030803040f06020d0209040f020a080f070c0206040b0a090501020d0e01080703180b06030f0304030b270601090b100c020f040f020f0c0a0606060e0d060f0212 82
    0x740d45119211000000c1240c00d270b4000400400106614201443d0002c0c0070345103000c00e40381c1550f51001242d201c0c800b00310031941c001c280000546801e03c140703003028500c00c00a40c41c104012100070800b000003420142c0840c0d0700c1020400051003101c0c40000158080c100c01e070f03200e445204a1006810a9002c2c10010702c149030041619480422250855441a20750910f80b240c00300040d140d07500d000b40004105941c070008220b611090201165070180500d5020b203081c101601890b04101c0c08004070b8900c0c0d8001c200c01c2000030812141d031588a038032000e02c200844a81100850042c5560b10100c48506c55a80040f5826030250f01040e25603404817800d407070f04240c81d41c041e04c0d0144d480d40069480140a84c0c844000d09050b04070040041c60300500502d03200407040703003c809800600141d811944040c20741c204009261003584040c2c0710074181034401800410000d1048030b122180105140c8d01c440711184030807019010340790690b80d100c00410742881c000c4541c070704003440403c4070301102002c = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 133636843 1250 133635593 133635641
    0xd0f0303020d1a030c1005030a05070311071407090e0309011b12020d020d0801031a151e0a0906051f0504030501060611210d0905030c01240e25170103030201 69
    0x1000340c0030305099031b10751602403c503a603418a010050100401400c00e050721444038100030035082004020240c81154000401305510300c80d01d00d861220307040001d84914002ea0601c4100c400005c0c1d804d0402e007460907104211a0803c1c800e903060340c00030020000e5207111301030814030741c0208540c100c0d04140e0303003261070a00c00ac0360300320b49284c800e1002038501c0742a0426642103580c0b11038441d0340850b4240314180e0702e108070302c086400103405100102902c40c0c1c80303080728864034000ea01c55005240b00601840713040e0404000881d050200180b020715a103030702008100c00c5002e24191401190050000c100c45580d5500c01f400150010b0f40020320340c083e40181c0c2482800082000c8000c240300340074181040501948580140322040c4181c07020310050007806034910007400b550070717000701201e03644142c801e0b858070b46d115500b041e4124500341c021800400501020040b058100301034585c0401c038814800010035501400ea0b4206910f40d032520300004024113405403c01c00000380500490141180 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 133638093 1250 133636843 133636849
    0x100b070609082a010506100e1f0809010c1d0d0c03150c0825050f0c03031305010c02030a051804060305011b0f02010c02030d020a050c0601080703200d0f0303020d1a030c 74
    0x5030481b0a0b6511050306507112924510079940e01000706805455000c00d00c0c01c01c00da58414065591320440007840c1501004684a000e0040754070090032810072020100c0d403248000001d0003c20016402543e4164000051021414041c001940c00901190b150310b09514100003a112800140b8041201c082c041000b000c104240540c956200b40000400d191582104071a2548124800c000901081c81004401103040c001180a4203003500b07003584424852404038259601402c0c1c06040d034105008001030160071804603410107208180d015142401c0c0400540205030542016085618003007403000420882043c00765440c0413900c074480c44140c40e0900301e00b40ea4103000400d005030001c0c01400707004806500507024080a50400a0a01400c0608a49401c41c01d900603055075204510070030921040c4045134207440c074000f03250505000030b6030100701c814a983c40c0c001c2080c0401d2021800380751213a4181d0b0648081018148503560303a0701442e002100c81880b48a210740601105c6020b540703 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 133639343 1250 133638093 133638101
    0x4050105180c090a020c01140118110a080717010806070905030c0d0213020403170717190c05070504020a1713350d0f0506010206100b070609082a01 65
    0x8800c1c01d0040021500640520644000181c8498000b607000d00c19061103200c28050241203102020180c1000e61415010303000c480d50b00540c8032001450540c9900f011111030048914160356401c1811f11625030035400c454600c0c829118251105407280003040301d440100e585801000c0783c0c1d85100c4074944070001c02d1303110a034500c0419408001105540c00504040d505181c803180c00b490011b003006d542e5180da9403260034220000303001c05000160081000b005a41241c408a26201c10038140780c41c028011107c8440d8031b00d00000d01c5580420780702000400c20032500540030242c025904e0300c00b85000039043e16102c0c40071a1015542c803001a1411202595000c8055085030001000c0303501c0c4030f2110b10040fc4241000025640e404406400044580041003805c0c01c00342c0018000300543c0111040f101e0103820340e41103420030018021074041881415043e01e00b00c0341600d61b1814149428001800341c0c000c018421400410b40010046024858806800c034001c51030203e0004a0855400c03a = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 133640593 1250 133639343 133639381
    0x30406080711010f020a031524110105040c170304030b060f040f0f0b01020709050f0109020708070b04030e01080603010504020d0602031e0a09031e0c082109060610020c0a0b0306011e050304050105 86
    0x140903020034211507401c0f04501c03441e1010080c100f928206c0ad9103070446094450442d01603500f8150312004000f001c1003200da0105150703424010b9803d20781140c1e81c908030b03c00b028000e207200b0009200f48000319a42d83d40618001401c5640400003c0c201c589000b01502c04005240d016009070a0009116207441c050340b446410001203c01c1f05a00b0408400001d40200300159003026003445000d00280341b1440f0340380254065155180c110070464001440308070010031183c080e074100710070301005803242e40e4a4ad022990090000d6103075a00c2c01c04041c94910388190030314480000c6001d1012500559200c1822203000e5a1814040c00d900c40b801028007030f990380c1c1240059440b815143c0032980000181414800da981e500c3c0c41602c01c210b031170300c0e962800d0760000c05ca40c0102091206d41d1134041180403051032a4009000c0726000b00001a0140c0300718840c0001040c0c00200050ba50780c07040b001004074903a403100184c14407107402c800400c950011541180c3d02e62034003000c034040001c0c0018103850 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 133641843 1250 133640593 133640609
    0x180207081b012711130213061205060a060804020d260304061a0307060302090a0b03010303030e0606100c030521070207080706021b0d050709020423060309030406080711010f020a0315 80
    0x800c12110500c19545c0b01e059845220960a000b01250803000b40c03490340013424140e1303c200d01c402c0c0910102d01142c00292035140314882c03c1104215a580105515500603011100d0012400c11410b01052000308a400300340385d01010390501c0f80e2205940069405240103903010040c00380802c2d081005044203401c1e02c1e62552080800f0461540b003a0001c041c6082d018000510481c2e58110380366540d0801c0c1c00c110701207912880c04e0000b40c8010005603070304c10822108aa500c2c0c0c49004041d0120740c0c0744501a0812100044411b0f0385a03200711010302194040c1d851105528059030029242c965900440403680201d48000506610006165820b0100020026080c40c03030039040203c142c0e26000120303400c0c040c8900003c0c0108841c40580000d007401d28003841920180410801030085000c07110f4030030b80c4103006002d04400004295000d40d40d05040c0041c058440440a90b0394502c000c1107003001c0d60800300385040d041d900d50050089082662070500206500c0401503075103800e14014221 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 133643093 1250 133641843 133641863
    0xb191803020306160903060c050304060b04050709050f030f0a03021f0501080c091e01062012030402040504030c08030c04090e0307240603051b0901050901180207081b0127 75
    0x290b101a04d1601040c0d034100d1704081c00903550b83e907034090560345601c60305004220084100700a1202d42d000d02c3d200a44221420001898840c00140a642c2603000705402000d01440c0c80605890820041c08208101d204840b2003100e1460300079603515803040131181546c50364101c40c101015600070b02d41600c180c8006000300314920002d0003a0441c005100c00c218162502c800324140c180102e10038081c18550391640a490446038607003010000b04814589950b100c03204041d4007100d1802680e412a50480300850180c555007001c4440c450050b4000c3d096810000600c48000d480c50300800440300310480030f0080301003483c15242c4a020360b45019100700c1100c0c1c85000d681c4920000032102c5076074820001200c940365214a841c191440007240814142036070007503014600300341d030a070040000b10303007114540d8102a030380707144200c140941c08a496004070700c850401083c1d800741c6208c00e00a24010049031204920f041c0600221440d00054180e60900d03100c85001d07002c130524000d600515028 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 133644343 1250 133643093 133643101
    0x204091a151806090609040e2514060c030c06010603050402041422031b030203130b1e0702130e010506040b0306061008060a1205060901110a080a150b191803020306 72
    0xb28032503205205055200004200094a0b82d445115003108604004002c02d204031210427211081500121109120100d9a50401503620b6198018184030030a490540d150504070144615601484408a01c0b6020301d40010648a0b03041d40240e105600031101400006040f4881c0c03080fa6005451f03c2208103036080102217a081c0703940b602d02c8054424a0a10340340c00348491100310003809c00e0411801a00002075542c144204181f460300909030710f0080301c0c5403503858213004c0303e0502e203040c9092400801045410a40d82e81c03458140c0c0d5450a610280900c000c07006145000700700842d45d80d441750313280815030045418002400c610a120180c2008544c02e202c0000f42c0312030500606c0a5403201c203000000c41d5130341c0402804554a4070610003003815040002d41d941c01e450100c407920349050720601030426240d42c403254098001001c1c000006040c6c800502000103501d80c0d810101507038100140040c091292209120780004055407040d4482818800d0311305e055440f480040d5040c0c4c8000301003 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 133645593 1250 133644343 133644349
    0x301120809030705151305030f0705130f060611010e011e09151b0206011d040311010b0a0605190305090304211e03081305100b01030204091a1518 64
    0x107081d00840202100c0206641d4000202c000070055103443c4075042c041482d00d02d068800301d209000d420218050040c03000318616003a80c4000c18407410344105040d42c402035200e2015407203014030480d80c6000b03201c01d540f60500908039040c1c002d60250150300c0c0000c0c3d40c041ea001845058104141814100317405148200c2020182038181c409407444d454200300d01e8603800c41c91280c031484500031600d0b01c0d1080c01d4040040d0410030168000341c0944001200704410016040f42c07954010f5040c00c0c43c030903940320941c0c1c00340101604445540c004407412008070380c042d00500a4483c074180d00300210304c2035190b0700e800c80c240d500c15101c01c111580144004c0c0300d1601030801c840a8140f501091168901c0ea41e00c440e41c1c0b0b8006001049583c00540c02c0e00001e00d13511040007540030190f6404050800c2e82951444e5445403043e2400654507550026140d00340e1090701210014940c4c06024040045003118414070406680d02a6106d4500c1c41c1c1001200280c3d00d007543c1038013140c2c10411242e130414800f4 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 133646843 1250 133645593 133645597
    0xf141309020a0219230d0c02091e07020109110a0807030f0201033e0309060f0403021e010b040f110f03060d0b0a0b030d2a080d05090d0e01030203011208 67
    0x1400550190500300c0500c072018061500c03042d4040e6200f884200c042902d030061170900c140040c02503030400040d6016094110304103001d080e905480c610003070307500c80002011a00040841d100c1084446040c010402c0d0b0542241400d50f01403040c604c09070108a0410001180520804000d600205820000320b00c10b292450401e6006040220714115440c1414103032800e400070381c102c035002c000c2c0d0388028407094aa0b0284178103a20130a4901c1d5007008100c80303581e1038009044081c81180c40000808040c800d00ca0a01c9401e40784103c0a14a50480360701400703840203907200ca01651030002c42006400701405403c40814110703072042c4ca032505032820680d0690008003001c0d08001c4084022002400300102c49110350412840050a45405002c043c07c220041c0301080800c8120014020f600640e02c02d840c0844007003a0303000301c021a41d807500ca107080c01001c2103d44000c3c541002c00000003004035038061b00340c01c1c82d503440350812040801541280800c3c021074070301c0703c840b1070850700003064000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 133648093 1250 133646843 133646857
    0x804090b1e150c070e0408040801050108010b06120403020f030324030303010509070f021c11061e01091d010e07080708031306030207020d0609051e01060b030705090604030606060f14130902 83
    0x106403070300140c580c100170002c41c4051324200e5a82000040400c0054402e00c9000d002d01241070007444044800000106980101180101c01c80041008681094000c11041412840340c0045c0d0f038032441d11202c500c440c0604403e041048012a660509091a010040301d05952000341030304055250f0309422220342c08050781da0340a51040b402d10003080e9440ba20495154003047da50304030b14441c480c1c200350803c1c6001e8000c0380c8154000300f0610040004030b4500f4103480e4540d000054241c46414444291842c480b091341095180c050798090340c0c1c0002c120380094403c4441129260750390350030300035600d2060155101c11544264801d004480c42500240708840c001800d89400084540f100401c403005580121503a0b030140d44141c1c4010b11540404681908007402008010b00e000c448074400e1000804c0b450402c07200090340784595550030180c5015503000141004900d440e1903024140c112881500c5000c1816102d4801c00c808401e005c90f00c00005220b8005206460305078404042d400c045d0b = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 133649343 1250 133648093 133648117
    0x501230a0c05060103050703030f1b020105030601050403060e03030412050c0601050d0f050f061501020c010c0219030b04050609011a030c010c2d060b0f06040e06030106030804090b1e15 81
    0x3201d02800b080c82004001d0295000d04080c006907861498013814079041c03007407000706110044410069800e02d024003140660f4082c00d00b1079a0755030f548012a034030b11071500010681403400c1490b652000c400006503100e0307407141a001c14181c0b0040c1040e41c43c1d0007004401d0409600600050000e410600d0b512800d81d8480c034451014580700741e503040d05040c00240c003810598002c1c010480450800311b030201c510842030000d0502c94004c00c0c0000d0103104070341000384c0104882c000f001c20207041070a01c0001940c0120416405040c140303080c2e80c65610550303000721250308028003060031400c0030070701040400d8010006d15034004040700551341c0c1c0540402c1071344c48030301641310f20718802d620380700c0810059404001d501013100c2e10316040007210301c40395040c0d0166488001e03106003911900c003110240c43c5007a4030700c545a0b480324002400b5007450340000f00500808980060500d80350b0b0031002582e08104c452200d4030301c00c1c02000244c2001c1c100e440ba40b14906a00c25190442100700030281c030f4101c4 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 133650593 1250 133649343 133649357
    0x7170411061e0703030606140403140f0a0807030e0108130b04031e030905060a2309010608240f060306070c0606030215030415060b03150112060b030109060501230a 72
    0x1200d1041d00032803180012031080000001c0036001c145e032510400f0702402d2241009030710039085900641c014002c90000034240c40b412400640313642d40130403c0000e0784030b001048815405141c42d011005800c940000c030040b42c00c0c00a10b0000358020f1000302d224009200761000d4040c1d103a1a102c480e06c0c2c1c0034000303070b007400031000c40702c3d88005400030142c0400103203032004549101c051800603e4510010002c40c40c0f1880e2000c5428542c104480c0c0340d4441c2c404041002560b155084218010b0030943d00070200ba21034a9000c0124004086640407104a40001a6501c1e0742c0c07001221810b00b81150002e40c180c001b0000240a14000c1e5070752203150f4041c82d000185542c50303902040301a83c5856286420920100c100720070008400c46402c16040322440502c1821700d0030301503ca81d030101821071004090500d090070035992088503414165000241c06002c45030781c81c141000319a0003806440e079070b2400d003d0302280d0307035002d11042513000106540c22905082c0c44400c400258101c901607230f0401c541d07 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 133651843 1250 133650593 133650607
    0x801120609030c0f050c0111030903060103021909060e010609080a020d03030c110102070c030b07050a0806010c080708031314010605010e0d0804080f060604051311041a030106120203060717041106 86
    0x5400503e08030b485c81a0020800da05a02001504414080c0c42841c04d075441081f002190751008101141120b5041d00c0c258000700c00c0614034035a01c21560405400d8520b80440091212048101941280c40507290940915102c2d844940c4401c08080080c0d08403654868032400a4420b0b4400300c050a602e183c54211030107000400d50a9070302c581803c0e140d00040d8903050042c058100440380c0c00801c0d50a00a26040301102e0103059120002d00c20340c18001c03000c07203103c2485004800c40d1600b99201c21034990300e280c01080003050300b018010981d82420851100000180c0511400050311816111042034640140c20443e09007840300080340d100205001c005181c050801130410500851000b4180e5450000c0a010884200514003240344411044a9001c601016006400d042c0152000301c0c011340202d4031030480b0100960896010f600c1c0400c00106005031a0102c4d0310707a88220309840e05915810022030740c201001e04a40c0d003880441c0c004c5400a16124042d000c081000741c4480d0070849 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 133653093 1250 133651843 133651853
    0x150a020415050d060501170c07050115060f140322020307080132060108010506130e070c050114010506031314010c0503190915020c01110a0903030f0801120609030c 72
    0x41c1042000010440200700c4a111021030b0283d10003802e401c1c80c1c841024190b980c010000d810000d800c002042c0f10008482c01030040a400c24010314000802c0f00c2c84065031550020202c101c10707040c4400081003c40f40d0015400ea51045078007031b90310b815156032445c3d0081245080707124141d0049038184a07920f00054844420700440c0311080340e8034000000c0c500202d02010142c0c10440481d00310b1811030081044e1682c002031164150340080d50b215880388004400f030711142009401c4100e03c0000d8030108241942d11030010751a0612450090084905d4010030b807608010a0089945c000c5003030000410380d802c07443c1801003080c0240912107504110341009800c40d0f484101c0c420000b035000041002015a01c010018241101c1000700042038032900d941c80c0094038144900301050300001c6407100c3c00e4094019980031184110300c3c81c0d507020800b601030200740603440101c0115108840707401402d8040c041d064100d42c000c042010036107155170350f49401480c101000b08c0070b0081c003100c10030105e0 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 133654343 1250 133653093 133653119
    0xa0306050601080c120406091a04060b030f010e0a020907140307020a0201170402010e010305060a0f0b03040b011d0c0a11100e06010b0703050f0c0c030609011406090108150a0204 78
    0x5008050004690501d800010700d4200c008101c200600420000030b0400207501411030790068100d0000124202c66241640c144a007180182070754035410001c0c0000e10140b54040e094001d4105c0481d0a1105220386848c04d8820007101840e003074014a4002d000b500b0003426450f80324040340783c82c0940700c09030b100002c51034000f03681000042e40080070507002c41d60408840041801610404040c03446c1550000700b40e1841c40d95214101503d440c040303411038440b40f070036401602d010656040c07003039141c07030045a0540003103034181c3d05c8400c01400000e42d685000c1c240c0d039610003c8010441c956403200b103400700c079602180b550340420807000b1b12107182440501490034464450791022501b00300e5292a5480c0840c1030300301c00d0748043e080241c040082d400500310b9074801c0492a0040e120710f000f80c042c60509408001d0586c042c0203940410483d04419401142414292201a079a54541505000e0004424014a00c040d48440800c41203070008141d103ea2042018002500e444d44070606880e05c4 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 133655593 1250 133654343 133654349
    0x31501140705070305070b0c060a0c0504080a060906062403020304080d180501050703020f0a11010b0d1a0702240a11190909020306010f050c0a1e050606030a0b0a0b0d020a 75
    0x541c102407814405c1000c00e00c034001c01004030486a6051103081d84910fa1100009000341c50400d81c4c03661a00d8220b80144180e50080050b800ad65034200b20a0500d500502480c02c4220b8400c0c1c03070400003280351003103d01045020b0004504c08250284180001c4e0020340c4058800ea411100510003400e40c0e036014001c82b21880b040000003e0b01c692a0320300f450940b80080d100c0c1080c5401400f00c80b8002a00c80207480c00d030795052403c440200c10b1210349500524661400307a42260240c1028000e0012a10115402c0c2800c20892140c070b0b0788014040340c4410b0a03540d0b8500623008003119851600d42e00500c16000075404100082d00c000c28040d181c0d040d40440783c01d81c094505001004c003695004181a0018030307406809526501e40341000802004029a242c018404041181c4800b940e081103107038041039114904486106500103292400c440000d402c50703c51181800240050a010980c0c010b030645c005c880034802d850b41002c46c2c0180001120386600003040c0680c2c44003581c2c50300440002 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 133656843 1250 133655593 133655603
    0x2703030a020a030f140c0901090306050a020319050106050301050402030c0c07060e040b040506030a02150c070b13080a030917030c061f05010c0302030a0305060d05101406040e030315011407 83
    0x15400b00d40d00d0107004d5030031581d0101c19462810413000e60110449030025800103001003403a5a0346140d20040e101c0c40c110303030000340401d46044200136600015500442c01060043d028104450482251070180c0f58240118030000340c6c103000400042c2442e802854000b030007842d0f8541012030300814540307006000c0d40568006000c490203170100342400d106510030540c058800384060b10b817079000f20790345500725040240a039580443c0c106284000d04107840031000b0b00400d44803502d6032405083e40c03507008031901c203a00c0c0800c1900083c8080c40000d00001c0143d25031030710510b50b442c200c2c007013011402c4112428058002001550341100c07050040324441c0490565040c0303a100d0714801c0c1005960141c0140d070611480e1080d080101e0740003c03e4515051030362070f0210f8a6541e4502280d200056408020f0951252810203841e04400b9005501c3c10803004104501554501c000c200c01d40d0100590040182c0041001c13880c0c103820080d400c8012071041c102424081622001821954800c03001501c0f = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 133658093 1250 133656843 133656847
    0x302060415060f030b180601080c19050d2d060207140f061602010617011b081e090312010810110702010e0d02030703020406170105130305032703030a02 67
    0x20030040441c1d02480280e124010801d40c1e00308440c0e01c110301601d00019040001c854000740e0b1192003a1511074068107602e041d1201940e60b0300480d41e540300e04001041c41a1407404130000c0000304100004101c4400512002e8220000c0e111800c8030070345036078001c038468222520503085060f00d0342e41c1c84181e40b0555005035500d280d0b09001400c2d48603410400101c1d00003414100040348001001f0360400401c800617140078040c1403080e070042650b035015404c0c102051070404d0390002e0641c00b454241c02030920204118610010032605030008680704039203e01c1c48401c0348440400401c14543c030212100491340744c00301c00510104100c200340d1107003078541c0c01030307004a407100f50501641e00340080c200000c505240300303036002038250401d00c5416406084100b80304400d640d41048520025500900704001051f11803030741c10541d904188200c0c13207640c24000440c0c103d0f0319800101e452180c0541d0350a045869040c48010b020410442112b0084001031044083e0403003031000718051028000c0040e = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 133659343 1250 133658093 133658101
    0x1502070305070e0f040b100503010f1b03060b0a030c0e030604050d0915051206030307020d0b060102121c11040b0a1d09060307091e0e0d1403101a090d030206 69
    0x20386007081036003020020f041c3c848180034a1001d01000c031030704141c1c80a0704282654a2120104000d412680070551560801c2c0e501202d008007680081403581c6280c3c48029180720604054040c2c7d0a20320800d00851000c00c2040a144d00c00c0d03001010440c024a0000030382840d020000c0d14004055a0076103150300214210404a230300701002c00c00815071104034a050300074800c005450360241c0030321340c030140c0d100d18001a000c0d0b070144202e4002950080445030300300c50f1340c2010041c03c402101d0b218050300c204d840040c4003e1003c81964030101c1c2c986008482034980c80d050314041d1140c402c1000e00b10005001c0421040c4400300604040d084d20741d282643c600000c00f582d280e00604051003405124444248003164801092a40640d4190030740801e01e2014150b04841010f1028500907600d03213017a803062622032010945500c40c801d2584d1344100b242030000900107a11068a4a400804480c44100003156042c1c01001c0110650f514440c1048084400720b9000007064000701c0050b04064104 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 133660593 1250 133659343 133659353
    0xf0e070603061d01060c060e190b0109060b03060d0f02060c031e04180905070914011a0306090403030e03090a080c0a090b0303090d0c0b040e09010c053115020703 71
    0x80c0000d1442c80d402c0c040801500050842180d0103000d200c0030885a000322005100c0281c000c08c05c0141d000089580d00d006201c140341e00c6400b200c60880f0240c8000d07000189016041c0950010741e259010000e1560300d400082000c071412002c41205d4030b078803107249003015988607005040070383e0080f4091907441071078840b403071011500024106426241404103001803401c148145c826a00f02800000320035846040a6152217030b268000c0c000c0c0c50504159048103515040902d048071004a040c90302a00040381445290200b180c080c1c2d048181180024046407090300210034490082c02640d2800301c90001182140550f5044119142c1c80002c4101841c2004020b4000621444204011007101c00d0700003038403881030800c028411416440d140701880604000c00d801840c112150664465450161030f0240340101e1305a84554a480e24000c02c00b8022401c071520300140303608400a1582442420901d01c1290803480041811508081043d2175642c402c1482d4083c0758008004d007520714986 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 133661843 1250 133660593 133660601
    0xb0307030b0915010f0201060f14030111030f041b050d030818070602070b0c030f070c0612020f03040311010906060f14030f0601090203180a0309230d02040f0f0e070603 74
    0x4001d025150110070010b10486001c5107a103c80f03c00d00e400322042d4640b4074101e001d03001d9500f0180300c41c2c6200400203031002914050000c050000e80c028044004444458002400116581c402d00140c030000600001c0b080b10841403852011050444082d854501151283c3d40440c01100421001003e00c034028070324091000100c5110030007080074a0070450001e417540110300c180e1203030304004075000703042c0300f0103000350780443e0700010015450b0041070500341c034040c07a5449550089182a1045502c801180c004c1310425641c190b0036501d192a0740e80c04492440d100c4244500c1c0c1c4d565218032030b0001d50140220f1000b00b11040c141e524907410400011012032003454460321036400a00406011200420789034111115450010780301e44c0e542d81141c00700c40c8030703c2c030b09086030051380040c0381011f400c5140e80c802d68000074800302c951011700b1719403030404a90b01462503120009080c11070040c6080d07080304142600002e00400c0c214900100b038816144101a906440d070840c0500f404140c1d07151013 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 133663093 1250 133661843 133661861
    0x8060c12150f040e0f0604060221040c2702031e090d080f040f021906020d03020c0a0f0615030803010905061017101802090a06021609020c0f0105010b030703 69
    0x40311096031850800050302090b009000325020380c2d04e500c000c00007000d00707010b411001400c0f80d080e500c01d40b80600d403100c000c2d80001d00c121203c04420000c0781c820300300d108141c2c0c4140c0e805295800350900b0001c11900c003e0324000341d04001c0c19062460500f09000e80013560088428100402c801c0829250340c0c854614014040701d00d80d400005090140340c3c1c4070100f5a0042c0c10074076242c40702d881d6800d03c0460101c5060020b50820701030140701d02c08080f00c0403601c0c1110101e80c295001005c0c00c039000ca06a2289100e101ba49501402e001404580d41ca8003440d812403251400149950011410070082e1407294020388100d80080010840c00c6800e01565078030103812a03202e04848046400030b02646c9a04210720a40c1c3c0100002890403610075482c00003074911004119192405100ea42003e0f40c8062000c501600409100040c024000500302120200d0408005102e03403c050a0b00020b4010380c241c0c1c2568494070402c20f07000c200a114060281a003544601e540e803034200806429664900 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 133664343 1250 133663093 133663111
    0x4060203092409190306090b0109060b0703080412030f1b1202030108030301030807080f0301030f0203160b0313060f060303080106080115020307150f110a032d0e0708060c12 76
    0x3241448406151a003110f00040044a000030100f510040420380d40c070403500020050307840d1078158024003180740c0d0340b41e040f51455207090254a4035103900e0051070241c8840140894070f08408140010300c00d10450340a0011864005030416a0000001c107881c01460702d0b000071034040700241c860f994080390311002c41e14400419032555143c05101d903600d2105210103080d07070901041400c2000804000c60f0302c4180c80c0ca03c850340b20358480c107003100b450100000881c80b0348600896522108450701085023120681880141981d492038107001c02c1c415109021540350b69112515402c103950351140c940a14007940d208085581068005425484182c00070300c99010613141031421250b0010803aa086940001c040740e04c01c60001d1000080c01009004404841c02d1110f100d41900d509000b618a030300032076400b400598044a844818805000030300c80e5000804c8070120307940d446d0781c3c121001400d0600100c2d28110f0342d480119090400555042c1050785000911a64690034601c0050b0407000413 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 133665593 1250 133664343 133664389
    0xe030a0c0b0f0d020301081609090309060807051b060603010c02031602041a030118060b010509030712050a1205030702070b0c0a0b06041d010e061302010c0609170406020309 76
    0x1500c561030000401c1c401c1c86841d41000070003201d808120802e448141c18002030554032561074201c4280c8034154076007d8800000ba0480000301110240226800640c0644414400071f0504c10121005000180b0318400e1090402ca5103c1400070074643d074144096500107080c140c10140d00700360956030482c109908640c02880701c00e090300769900f01080300c103604440c0003c00b10b0b0003018010b400151400340030340c1541792660344030035110f0b40d0382c1b101c040f5842040200441c3d03074000012344050054240440d01035009402c1072212403848541c0301d8649000c1d1b8102c2d002c101295646802041c5449000c4000800c08010300070842d4041018002402c00301c1129801c00c48900000742e82e40600c4400034208484400210303105858550080449888682481880c01400301e103040c00307030a25503407240c260f109110016807901d170001242c14016605a461004035030b5192187e0300a4600c0c008207941141c02d07828645a015101d41c01000201810307005180c070b81421500f0065107001841307001c204041b017 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 133666843 1250 133665593 133665613
    0xb07090302060f0c0a060609090516140f030102161202070f0b0306040c0c0203060108030403021908030a050d0b18060306070806060301090e0c04020f04050a060309080a111c0801060e03 81
    0x10b0b60302aa07a82c00083c0c424035803140544000b40340303000a90f020140079185880c101003040d0050b6004403070150b020b50304031007595058000c65240c0350714a200355600031840c50f800c0b05251a080c420381c52074003030050000d800c0030551402c0d4002102001c2c411100d000003405101d49080d01400414020000c54000000c1c052030504500018400180500e11071075480c43c002c0d00050240c101c2c2c04900d500641103032125a101e40d60207989502c00d000581c892059581821200c01c1d1403c1c0b2801500c0c0c00802440c184902841d0644198021002861155803600c4c1c400354039803a200740711a03000d09501c441d8291401c00c10240740c201140a031000342007050b0801040403680310b80003228116554440c0026900c2c1408410905150b42d00424907401800001c0424604030420060002d55104039014007600f9520303207080c2c00301d421100000303103032410902542000d00d0181000d50b07070740f10b801c0301643c1c40c406038001071155080001d5600e0300441c6143e0010b01c550343e0b01010785040041c05030000c055100f1 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 133668093 1250 133666843 133666849
    0x501061b0b01030f05190b2208040e0601090801020703030f0f02030601020703080d0609060801050610081012020612090616090e010e15030307050703060f0606080a0b0307210b07090302 81
    0x120500010b0a284400341c3c9850810000b040b160181d1465403560b200124807d1509007096070041c6e8003000125040340c410701c3d440c0c1d12000d0102c136640d030041307140c1e03d49447c16807882c3e100c10006060a040c8074801100040c441006e00041005903c643e500148034400d07480954104c4003058102510170303105004000082e40c000407100c003a06e4000750841d441d000409540c20180c81d5640205403486d044c07400000e02c0d5141504810300412048a800040c04d000f88000c03940744104982c0c071b284480060000300400b5400041958000e800a4801843d00d070100004612030711007980c1c800a03580c491030400c048400700c240035460000603840d056072054503101005201d0081800b410584001120204030140600f2101000740e00d009819252141901d0805075142d602c5440103407101c504024214000694610400064410b2a2102c90700b903161101780c0c0004041015409406101c2c00d03802040c9242d03101040c481d015100014410310b16a0b9240203810340d6009400202032204000307042c40107075 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 133669343 1250 133668093 133668113
    0x3040b0a06351902030d020f15041703130b090309060702060f0d06080a0302011b050406050a1710030203013606060e040308250519020307150501061b 66
    0xb0403445180d6412441c0c800401004001d460b6035220503200392180d08881d000b45450411509008030240c030584101408166224805400c08070910742003401c0085043c59080c10140d00107008109072611040100e0003c1c0281d40203454607410560105500010451001d8690b980100e800015500b055102008a210750041a10003481550040381c131070140d600103010341d181030302c00600034010182c1e41d5105540b0740382480d00580c01542410301c21104000e030721440610309885991858541407401904441a80001e000b010800c55051080414580e426042a0042080d1030710030000518520400d42142c0e10700c056800030716001200201c0d85103403c2c0c40220514030020001c600701113a442e09a00924694000c500c1c0c11640800f8002416440446280300d601101e1504208956004e01201d606032403100d840c0000700104111104140e6110902d40b0b04250790040304e080449075541ca1401740381402500d030704140d454004116065104000b2000d458500586542445a80d111280340d9 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 133670593 1250 133669343 133669379
    0xf030a021309080c06041a0a05010303080402010c0f06110301060f080903090d0f05030a020c040506011107050111011d30030c1e0c0616020d170705160803040b0a06 72
    0x16554040c28080c424018111500d01304d48005a41e4a40f03481d2401c0780418040880c10000308425000190445c81d40d0303c43d0302c9c16a03405440da0041ca07607039680110307001c20b9071603011504500d8a000c190001170721409909248410340051984075810103400801944000007a10100b01202c3d0500510310408011500300d880d095865480040850400c1d00081d0382400004006200014201032140e0f40862400c90b075100c01c4500340000c2e15404011940030a040d1741c61420360b00b0140301040558010603c4c540c01107003c1d000461640c5140c180f0001105184000c089503030001d01c01003c40b102c3c03440c1c0d1100141d06038090101d0364500c084640d200d90100400c20300d20b40074000f076200d403444100c102c0400303007100c40300d0843d0381d0317081d030100c1180c0303403482a22840240380700130710303e0940d0600104413403003071800c6640c2d041c00004181015001814000d00b61905000c42040522000210840a8083c290040d01a26503d051a1903c4400ca0f9401000d01414030b1510300d00303120000c6281904841 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 133671843 1250 133670593 133670629
    0xe04090c090b0a0806010305010506190e130320030403120822020d0b0114090108010b01020c0105160b040807030f020318040221160e0904081e040803180f030a02 71
    0x71000c0303110210320300d844103070404c100c03a11a42c0000000c0042c150049446104c0c1a5165031701c0c01845d89070158150603a018184c00403006600245a18001d5000007041600034039200010f00380000041c01c0c8601241090b207401d42001505105201c40043c0e0303801105c0c480d2402c9032980c5080390b0078240c0c1480380c814440341084001540000d543c1c0d400d14446809400805201c100d50392640d918105602641da030501030004034000240076841032040840d0b00c0c0041e005000c112004800440c0c481d80124075440090000c455888045a04003403003522480c482ea0800c0d80d00c0005003405441482908000c40465108104d8044007042c06804c5a0f00c0d01c80559025854400c07004590003442c8011101008650540080181b04280c3c50000c0707424580b00e4441c0d98103043c07040140400d4031001c0b43c014280701f104010581d121010a14a502010386180c012030070701e0b4032842070074159030020501030501c45503280020581d1815004810b5605003c0b0010b00c4440e88a80c049226114211030042e6 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 133673093 1250 133671843 133671851
    0x3030b0f1008130506010f0305010b09270102040806010e06011e0c020d140105040302370f0309091a0a2111060c0a0b0901180f020603060621010302010e04090c09 71
    0x44140c02c070f0fa02640e2826030000580f400343da182d403014509030061b48410b654540c02d080300c00405060007041140501070210b010307059681c40c8050401c0030b12101c0e480304d0040d98200000a062003040c000346000e000c0c0f6810701c4169042043c0010070240310a00b010540c9002c2c10001c203d0709401c1240b80d004c03154150303000c40c40d884150170412860140b42c1d401e40c0141d400c210410080603804627050750300c0079051110282c4e080c051100d034602c01304c0c48826081c400c0c00022042c0c021803a01c90307a0001141c402e25091500e40d03110940d010a0f10060300d110800700c0070342d030712a02c1c0610307040d00700202910081010250301c00313422942854428801c840a071a001d416075400f01c2c1a161001162101013030742c0e0450304619090701d0400181c04044416400b25403034060604031090701c00030508010b0707401604112a015aa4081201c00e9001801507a40240d081048020840a40d0480303c3d051019062048107980b4500016010b021400c1d0310910561814508000180c4424856415035030f102400103 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 133674343 1250 133673093 133673101
    0x405070302090d030206011e05061b010908120a0501060804050c040b0109080d020a060506040b030d0e060d0f050603060604022104110a030804140609060d180b0901060303030b0f1008 80
    0x3900038800c0b880781e60707082280070544506142c0c0006540b4100c80d161031010b1001481c001120002c5107045c060342d98451420450401c0203090b106070708014040e501e00000c1d00c803102d9035440d0125481500f10f00c0300c0e2044102040302307000301840340b18010007090405907100c2c5402d5450a0b26001030202c080d1145503510f030007145e41d07480742c0d02e244003510410084030080c20b40040c01a40d500031108048071300d80e040030000345032402c081c000d103850310350041c004000c45900342d0307000c0d203510381484c4c402d80d0030940c188481c1000e2900f60080301c06803203600e100042e207030a0510074581000001040749020324010451661108002c48c500d0700728225003243c1d60203e448915004400c03042c502c83d5258882c480110100c24480150000e00441f18900c14000682045000340301c4113008d001d0b540c6078030203414000304481800075005481418001c00f0503a5015040d071b507030100c0c40740d0f040c0c850b100e0b140c1d550041401055014411000d50280c211419003a818101000078105400c00b4903410401100d42e0100d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 133675593 1250 133674343 133674347
    0x2060403060f1b0309111e010503070302120a060806070903020619050c06040b161107092403050d090e010b09010c050f010e0d080f0702120912010204092307050405040507 75
    0xd0950440e05601c40300c891843d100010054009054240d403070080a507800381040c40c0c8030051890081400208600c0c040e4040c005440c4e50700002e0801c0103260b001c002c01716603041051407461080c0806040018214100302c106031503c0c0d0000c20703000034400710b500180056907c10307081e00c034a030030042031903100c180703608000300c1d030a004103d0150200d1007101c003408100482e40382c0712031181b032030040d0301202d500e010308046a4182460032050446e421070002401840d940d81c200c3d01da8680884030148400c161030b0b42135098900e03190300542d182d40140d0201645103074000502402800c60421400c0c055062112292030b611a030059141031103107d42d028010000d09008500880d00c114000308410000c908030382d52202d5480910390001031030b00700064407111224012038040e00e1183d00804141300e8440985a150b440180160307400b03080c000014000075824001071015040d0820041000c0360030701840b041a91130314034007410b80400c81d010032071526480026282201c0341120701040c640c8450000b = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 133676843 1250 133675593 133675601
    0x6100308090406120609170f0f1303020325120221210409060b03040b04060509100c030605040605060403031b030c1505090c040203090706210c02061b0702060403060f 73
    0xd1311016400781030890900019074480140b072402030a25520300ca291541520342d038400c016941045140922411b8183c06911010b0300b0084180202e4404058036900080e2400221078075500d6581c8904102c5a0310781822210a8010142c0d10500d0000c0700702580040c540c64450401045500c103180441d29583d10100640c0946050000352600f50084070030600c0308582c0315008840343c0604000000516410900440e4461034002c001d01c4400d0305c2e1a500d8801616000e044070350307540300700c212000407040648159200640183c400181562902d014041a00c2441c2d0206226210502080001c00d410152016081901c03141828688100e407030301361001601050047d2038608141251301c03085e041e652025010322060000c0381c1882d17404400b084147e101c03c0701e545403550020842004001c0c01861450501008003513400310201e00d01045508036108a194040180d201006000144034116828201e030034510610781d107014440c2e004aa102d100c1c0d1310004007855540c14540981100540c0 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 133678093 1250 133676843 133676849
    0x1703090904080f070c1401050906040b18090702070906080a02030a080c01061d1e0c0f07020d06020c070f08030315130f1e0f23040516030302070f0806100308090406 72
    0x550581341c0c0c209042500103040c2c02c1c011040340f070448921a58040d801102507800d100d40c000c1401d46841d0608210000740c0c0c102c4501e002c419143c00f01020b03031076a103d40c03c080c415600c9500074100da0340b030800031070103507983e5a10400b015003208880802688010074000c80c00b6800001440d929903050840a0041825505c140186800b4003215401c40111000850080c43c01f440700442080c0148900c4520750400d4480d40c4a0810400c210101c3e4000d280c064a0300c207000420458407121aa2201c81c00d1741e00c48540d0002a8000c3743c0103209012142400c0006001e072000214154a80780b10800044041000038910840100150781f01c1080c0356000151040c00703241007400050910101d4541000c089041070340c401d07080c9100e61150388001d100c4d4003191460907018000d0407440302084030810001900c152480d01910350210141c421700c0074907600a5229500a0641742c3c540300050701d00c0d03c0d0382d07044100c058002c42c00b0f20407101241c5c40380341e0540350000031180e0303144c600000113002040c06034 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 133679343 1250 133678093 133678117
    0x6042a03230c0d0c020606101101021309020306010207170d0e0607050f1b032a060f07080304291803130b09040c0206060306070c1106041e170309090408 67
    0x4003000010304015003e409000c41c05030061001d88550081aa00c4540498103107410450500000400382d05c10040b40b01e008002c900018a00b1140c9094a402071199030002e00c0056000010701c62656810042ca10050244404034088000e0302e8800588031210400100d04004c100c3c4038612880c1d6460b421100602c3c1d0007421110081c1c0403480349a2140d0301c80110441e038609405e43e9101a04021400e140d0700301404201806c03042140c3d030a049400da940200c03c0e009041800141000c0c101d9100820609000700881c5480e8900303803424421600044a00200003071508030901085030b400c03841150008800e070404100b100100c030781c0c5465805112010244c0c128401030000b05401038100621200d00141c90503c040160070700c0590f0348510a55949405a20010004910134412041e642455100f140741c0d48103403101100103240f40d0001c0c1c0003003039410350500248002e0401205034100900004072507820103164120006d840b80156980980100e058200060400c030005003142ca80398541 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 133680593 1250 133679343 133679411
    0x3101107152c0c0a05060403060f06030807051f0207020d0b1302030304090b03060109060f0e04110306040303020d05090604150b0d0c0b040f1d0403050703020102090a060806042a03 79
    0x28101002010100070140701c041c050b40302d02d05042c4c140034220a055a10161a980ca03141c65a96010010042540c50b40d481d5940d4001c0840003c9902000b450700500800007051165200000e05401d1000a41c0d12a001031041043d8030040e194915000b68543e000740d000f0f40c3c59603504c9030501c18103016500007907042c00000ba010403241181da00a900c3c01d60250100c07109a038130342244130102e034400d01661006082540b000c101e440c50380c0074035982c040c1c030410f0400c0e5151440400700e45802e105640072000b10b6004101c0e03000119052283d1030340800f501005060f68141901c81c13003e1a040c0151108405071a0100010303161620306c1000c15866200085642280d5100c1c104030854100c4e028014038000c8013400010f05007140c0c140c200c02c03840600e03010541c1d81c4845e50191415400240201c0a554007800a094075584048112008050b5621040c2461070030a04000440d1440e844041c00c080050404410740e869010141910041d107080010320840040d8001302c01e0810241c05d1000500300d = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 133681843 1250 133680593 133680641
    0xf02090405010f110309070801090f020f01051207030b10030207030e090c0f0f030105040506030d1403130506190b0102010e03090609030102040314030a031d030d11040b07050106050310110715 84
    0x1480b0f000314072401100042c1c501143c0c5890008d4281c80706500c0140c002149001c0c100098641403019155206050500d507180c0806150100032046089a518010942d260202280703418580b585201c0e04100d4501149481d1590390013402c5940404141130007080d40500055181003500b0450300346140300c80100d510f400240c01c40b080213520074026207000b1070a21b004030f5654100002c3d05000c0d8407240d114682d01c40184005081c0c607410082c807030b41d40028550750040103d8010f0249600a01625000c101e440c1d21159194040e00c2502d03056604581c13601072504603868020085d01c004010880340304d903541d00303900c00081c0640210b030000b501406030300c1000d2050403400030040100e261f05880a00410581a00400001c0300030114100160410404806402015440344846550300d0411f5130805032101d8202e180c40d04003031011034860799640c100b1311803440c040100c0c48481071803410901c182101c600c03041c6924010001c0040001c10380f0360200c1d10701481500300c5041c41401910104400300 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 133683093 1250 133681843 133681871
    0xf0905030a11040b04110a030b1306063c030504060b060406020610050d030905041503060c051c0b030a030c0602070f03080402040b040b01020303060d050a02060f13080601030f02090405010f 83
    0x3a00c5003400303100f640303000640001070606000d030320668000c107205a03083c1b01d40342c04e0036030161003510405a8000700310085140c0c200703040d10441000d08916a0b0742907000a850980f800e032100c0c0c0703c42840c843c00b240c28002141d040c1101007110380a0081c0b50200c1c1a841c3c1d8038100d0003030001031046561100000c02e001c606a03500140c101d1182110140b4110740710b0390342c018800b0151071080c0c0900040c80e036910a11817800c040d006a00000c00c112800390020f966901c0303a804440103010000d000070700004050700a846030140c08176100000c0c0c0410480d194100c40002e81da801b50314001028003c04105070400e214465065030016a000000c0300030409481c5030080c00610101d404910071440d0400b100c0e0682403510405800c0007041c1c005600d1138503500100440302c4c00d01001282c0a104440620005031942c001600040c858120195112a0342500c030a502c600141c1003000c05030b0001d4010408900d8500d4510112a0152313007440c055100c03130400b180034000c0c0071300341d26400d400c1c04c009245441b = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 133684343 1250 133683093 133683113
    0x3020f06040b0712140109022503020d120b0307033320030403020a1b1a1206030d020c011404150906030c0c0b04020402180d030201060801050f06060a0f0905030a 71
    0x401265510645641c03031a42e4a405c0f50000c5440e40e80d4221000c0c01449450030301c0d402040c03404110802001c44041c0400c43c0d414030605080d044006030031a401c5064800d4205aa0021b14021044244a884809404280d49203403d21000e27280421001541011110146000b41d01420211060320000500d42d542400703090140004101200312090038500082a242541d0240d81c0c1540034058440d40382d00c9140c001480043c030070811034404800013403241007003031084801403201c00d00141c4a410b02c8106240260707008200c10b000790041184509420b5000c102404101c0c0b003402c283c103040d10030170300310300c500e0281c0d400c0141907040310302e441b003402c9030800001c10032601c144d030701400580e180d02001c441c01c45080314000c0400b1240e4000c1401850a80c000c2d01c030301054030355850b0103086050001007001d00c600c8401c1e40540d540780410300107850700303006607903001091001c41d0070181131000c04103030740d132140c28400000c1040705040303442e00034850074000c001004000d04884803190b160407c2c3e0144 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 133685593 1250 133684343 133684351
    0x50c160327060e010c050c0a0617062205130c0602060402030d09150c050f01020406050d050709150f0905030609010204061d10050730020d180501030903020f06040b 72
    0x40e422601d89003407155420180d40303081c1d50324440203070b8540042d00c001103140350441d01c034090303489400529126051400e00030325507591042d0351034807141086c05000d2005082e050144c0c0100400394540541c10701c0c181803e000c3e510300000c86544034001d03208403010030b0350000c1c00c1c408031090000b42d441d03000460a0060b8002c80c141c410001c50700c3c1066176112114450981115020315007540c50600175411550428014026101400500030071075089070b210360855000301c0e10104074031424002d0740c815242d002415080040c0d0013803d003088000c0d02022481a403040043c601c1d154102c00b071003004200020080903045598034184061003074040e401c180180710002c0c1901900c5d8205603140c2c1a5000d5484004d00242030120035860203c60300d62040b60151415100d01c0780c14440b14035070201ca01d10100c0c1c1142c0901074901246030090402d600345a12030200600840c1d080d40c41800c03940c000303049801c04d084c0021094410320b803d03403c011050300f5141c07603802035104020901c010b000b001ea1007 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 133686843 1250 133685593 133685627
    0x1311090c0705011a10050f0409021b0709110d0203130c09020d0e06040209010504052206270b0a0e0106030503030c04030c06020a0b071805041d010b01030b0d06050c1603 74
    0x802c1002c1140d10615646500d40d060f4044c5c840540080303400d00440c020030026000c0d50140d4540f0f40c80d90100000da13408455042000c0b06180244406020280910006840784040c01d0000e41034038a0000e615004070020900d200754004041007202450400c07254420743c1c40014030003403540d00c00424000b0340004902010090070102c1d05103456001266061259a0044c243c551036400e110510005040007048461415075a001d0f2a103c0c051a80754914854030407007006c0b03541c0d00c6c611071280000b0980b401d1040d08029032520303040080c1310034034801c5c2d018129020020312000305243d09405491603a00142c042e010020920402c141480006c0054a000c0c0d00f1100c840f96a455040303030b9413a40c01c1c0d405009046028081402d2602c50640f4201800e403152081d4012612280080d080314071a101001c01c112141002d0074203501c086c02000d060b10720900307041014074031170b0b40401e140c9040c10784020000743e550400188407031508401c1d6400405108a03211084640b480c002d0081040381d512500 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 133688093 1250 133686843 133686851
    0x5040c020d030e0a150c0903021e040c08190b061312140c03030a0c030212041205011103070e09040804030b01030b0106080f0c07060c090b030c0901261311090c070501 73
    0x5450300005240041a5000210456004440c0e01d240c0051091b078031110100425440d001000d40e4840b0b9002c1224101d19017010300003202c0714100404c841841220905101494081080c18184c0c0d0b00c0b40d00044001c0d16000c1151250780b00011094400d0102c002303a51070320300e5804501c1c10054003010b007403140300303e41011a040700100310075501d901103046554168030401c6104400d910942d41c2d0340d413181c4280102d5040f0069510364009541041d0001c0404d441c46100000134800240a4010740242e41745e0014550700704880010310a11241c00f1117400782040c0c40100c1c013000080c1040b500190342182a442e0070756100d1800c41c0d1381c1002031241000040c24880828502200d5100240c000c0200e0050706103020300d16580c0c1005048007012800c1881030442001414a500304015032040d016001950344c0c2c1c051a800160064411003a24020f100c400f400400c2c1d176140550485410405910001e03001c069140ba003000c90740d00403504e0740d80101c0100c2c00d000112203800d01410141c1e1158000380 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 133689343 1250 133688093 133688111
    0x90c090f110702030d1107050d0b0712060f290403061401140105250f080c070b031e180d080703060b0306030c0919020c0c0108070203030411060f0405040c020d03 71
    0x69524000c030724010b941340c1c0140340d001c001a40150000c0605201c62000d690720aa9031388000b6555200e80d9809581c1c13100702d8010040340c640d00c01d5841d8030440c040712040040e103040840c100d000c0210340c01903da61920144000769051280c54ac0094841c3c841228240d8880d220300c3c0142c080c1400c01203903c5191281400400d0040300c41540b000842d106964450030000300b6025804102c03400390fa06509141d01e043c01c3c10101d030000c1040c461040c040c04100b983e808001e6000c03490f0444c2a48a121000d8040c4180081104c0c2c44c0ea041c64004880b00c0d001900b41c44030030120910f1150491101400c0c801c0f94440c03c0b11b1504143c8580c8222036507142000401c0d51484009820b01c030807140c807545900202c014040c986404a14142c00030030314800c0550060040c3d140c40205e9200c007001c150164403031a81c07a600c560740f20488613444401413014508504090343c80c2d0b459100b101a90500c51074011910503c1e5940c0c2c10103030b40003002d004005009803c030010001c4c3d121078040b07002100180c1441a14 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 133690593 1250 133689343 133689371
    0x40e0f060115020a03051e03070306080601090209090a090203011803032004060c020103050403020c150301210b040b040f020402030a020c0d140a1b060203070906020f0a12050a0201090c090f 83
    0x29044101d001e0f0090014404260380403951540312131541225002016204007003004201c0145200c2c100940380000e0703480c01c00a605207080c0050b4008031055004020420940d2102c5814607000081c219012a0a0409100190244c502c04000700012524000c914081c10fa040d04200201400365090032104e150002d080c40a51040f4003562000c20210810344006510070b41c051a8414043c0c810b5880c40c0c03842100013540c6c0419001442d10703001c000b10051203480695030041c121070301c005401c000d0541540c3e8400150303240c000c2c405855280b040d00005c0070f03c10448502d40140b64000c1046580749006100c09000350400c00c225006440b804062452040c01142440c2c10274800140c01d5003440da0040c401c8940c40845c001c00c10161900e086c06170f0024000d400039500031aa5500c40e810043c0c10403c000b4034149a882e4958170b40d5100710000c0e00070624900030240c28030071514080d03076586100d400030381c0588154140144181088600003500018070b038006080f21130021400c0c001808480b0078 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 133691843 1250 133690593 133690619
    0x305060f0a0b090f010605070c0b0f0d0b060403020a030f030e0301020a030e150c0d1512060204031a060904030c1b030b15060c1005060117070507021c110609030309040e0f0601 77
    0x643c4c03601d0709990040c0105401000982503440c8200074034055140c850000b08015046111990380000012030301d1440301000c1d001b81484070800361200390402d841c41c0c0004c0d14900d854407001e480e00031411032020503d88200060b03660664003500035035868940d00350040080411400720501b070b00030f08440c4102a44081005406031508201c040d084c80142e402c002c00500c00329811014000030500001740c403a0f1501204108a406a140180c90304d02e54100803090421105991200484035410402d8a0351140c0b40c20340c001c2d400d403414441e801e1542c5060002e4102c50400b0054160000d507002041050500c0141c6c4244013200003680024881018803202d0301031003880c0c2d4030039080440f070000b142c0c040d907000d2980810140750120742e900034214190b0112030191001d0001480000d902001d40c1440341c902d1260500e6010054404407580c0c441c0d100c1c04004e198058811500000c0646240c1d90400585034400c90041082200580c0406015a9410003503580790482c084c69000140012090324 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 133693093 1250 133691843 133691851
    0x2f2116030c020c0402090103150305010608010b09070210020a0e210f0c0f1c0803072a0302030913021e09040e0604020108190603081207030e01021815040305060f0a0b09 74
    0x20f120030041d07041003002075000303000c10604056854602e0410380700075203604001103001e14000204e50741802c01d880d00f552845030819026540c240c0c03d01a4543e40007565000c0120f41890060b1510b00e038010894044081c2040b20740c3c000391100d11341e01010f1034a8100d20288410a0880300c400d01240c0510303403a0a500b004441e031014000604440c2414100107400b0910600290010158007c3ea00c45200790000e8540c030000039010340000790502032200c4102464940c04401c1207502070760760380080d600d1142c01021400740c1c10007101c1d110841c003690141d480a0384a002c01405580c201c0114034a95000070f0b030864810f074200909400d05201c0820310314095a0103039100c0038281c0d940441c00b290480500038112445940e11070000101d6000f9014148502070303518034003590704150f01c008003564080c0118440d170303920410000c12424120201030304506400d41e8885c3d601c5e00c04865010640c0616803000e44240181010070501100040046108161203c8200492501e410a00c010340320119 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 133694343 1250 133693093 133693097
    0x61404051b1b010f0203090604060501081603060f2a080f01030c0e0c0c07060f020d0f0503060d030909050108010501030b0a0203161b020d0b10092f2116030c 69
    0x11024000c071031442e0381104407a140c0020812036505030300e400482e4000c4907000c2c269003100007800f041203a1409054014141440100966440e900c40c0511a03119480010003895403812120202030b469000001103001c500c4891082903682580c4200030079006002100080e808000a189060070f40c0b4264103803134000140c200d900e03040140c4d481c8031840140140400c0841130200c0c0104800400c4400301130f104640d00c4100040c114a006490002520b485c1d00501081c0d5001c03962055000c07042d03d92148040744e0300701c2641040e0a095a480c00c25030003a840440c2810000710741c5c02015000503040f03e21594820642c3c0d07071281d890745c00304d00040d2100c0c1ca074a103c000b01001101e00c00c01c50400540c00040d54007044061750703800907440c005020412240c4200c4201044040000c14070400c00032301c0403103000e00c80e21380302c1c861074800448020080e000e1a40b800b0700c0390f01514000310641c0e054490700d0990541c0d52102d142162800d9404541100c8140a803c0c0b40c501c0040c401d0250301100b000365 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 133695593 1250 133694343 133694347
    0x40f140d02010f0e100209150706140105100e010e060d110a020609070b0403060506040f05090604020306060402071a0916081c090e04151e0b120105060d14010b04061404051b 76
    0x850350f40c06540810030307240e0b08c44050258005403607060001004901d20a8000007246040128006c03d00e81050f40814031030410820110a40c51300402449142c130f0092030003041c1007040500269180c015003021002451401400941040c60f0400402180c4d140e03408640c000d0f91055005c0340c1d5443c19000d01803000206100c200005842a0005038006800500205207412201c0b030321021542c080362554920740c0818103020075801c0500c01d26070044016a400e61402e400c40d16403080d4284407064040c520740c0790900140081206101c803440c800d0011185c03031601a5a096615500c4245030f810030140c0400042200e14140261400c600321340c6502d810150301e80c2c42d81c4465403400c00401c865102c00d511140700e0381d00241c8240d4070003142c0c1e1024000040c000030320403c2c8030030802e40241d145010b0b894541032105a83e2002d4403400b600d5404101c0810420b4024005800740520075803041e0081c0c10400041490324000380325000100066408004994035001c2c04407441603404484c100c034040c2 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 133696843 1250 133695593 133695613
    0x140a0302010518061e091806030a02060c15130b0a0501030b0a0504060608031306120605030601051003060f0b0a031b1b170406051309020a050a0305040f140d02010f0e 73
    0x10301ca4060301d83c01d0b0014203550074540c00c411380000440e0f000c040440d00043c006401d480901d45440c81e450440081c40d2215002c0c900940070a076100403194001c0e2003103034046111150b12600700607141004000c0c1c040b5007a035080c00304030301c11084d021200032590804444c0008280d005c1c144038940c1244e401104003030362902d031000c0c0300c1300400018005881d42c2ea2242d2020500c030508000410030100e526481703900c0c2510b8070038001c2803052038a07a080c01c4141000410000380e13400203a4a0b0542d801212040700103400c80c403040d0b000340004d81c02203243c107040b05000a050020781001e0240c80d20151401e210522185000500c0075501c82065004281006403421074a0510505040c2d0144581f901e200e06e01200034407140d103504076a1104000172400541010043e1000d280301000301511081581403d68090000e48a0300038071015004140e0385030700060500c04c03001d09050f0025000021611074070348100085e600c0d40b94043e8842c0140d8240000500c0020381d42c401c9e0260309001502074004019 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 133698093 1250 133696843 133696867
    0x2090a050409030507240614031209130615030b090f04110607080301080102130803031003031218060b03071203051b0c130b030c010503010605070b0613090c140a03020105 75
    0x2d01203400c0e010000d060000400050740c5000700032049000401c00d50810340c00386401c0065500680203840148410301c59207070b0720384001460644401c41c00c0034203900c0f48910404160840c0d440121841c01d6802c14600099544805a60740e40c00366031a541440181c00d4581880396181090300c00144260390400041c003c2807600901c1c440c807040052400740b8041b10740d107d8040c0c64200380c00490559600103030300b103d030901403020714000f04030000c055825403416a2564052800a200240a00c9480070400a4005070765000d003080c0300300c840c2d40007951145820103e0041c0124618103000b8840d504001c198440040e0700009010f90607074401d0701d07199034034104105c80c0c0b48410890040c0d02c41c60a0030505542c0707150309541c0a8500c04000038504030300804061901c0000044203051087c00c00043c8030b0307030b64010221180c064202003060611388602010030000240b0701c2d003005d1880e1803d99140304005021800b1011110502c4084920000d60780800021144511000340031070010002c2001760b00c = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 133699343 1250 133698093 133698101
    0x23090c1204061104081e0f06070f1202030f0403110c060904020906042105060a050c0412031e0c020a0b04080303060120030301091b030e030409092901050901060302090a0504 76
    0x81e02c00d80020400020840242078a90850703046408290090308100b5000ba8014245030349030a60000101941300000c0e0600741c4504000d4442020400d46000085100e03004204180004c10802c02c1195285440e1040303000b0040c041e5400ca0021340c814101c845400c4c40046d9044040c1e0008040c1880c24180b4010031000358010f0801a80092090000050028070f828a03510415056003480080c840c06203000c6042c400c00804100b03d081c644428440c2083c450300c203a505484034021248141082400e0075141030443e0540c1c0c014400e1000e1010081c01e0303025840c940d00703c1c800e40d2a40c0810707840b510303108081c0c0680e004801b81c5038030a00010307642d903104203440810a1201071804a203c54410322150540d80f09800007007096841d200203900c2201d20b40701c552441c60303851508000080c4408002c94580c40340b8882d1001d5591106580018004001d00400c110140b9403885480601000312401c0503200c01d205403031041011320000a440e070f01900031103080100007829006d0003814502040010 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 133700593 1250 133699343 133699351
    0x6010b13050d050a030813030905060307170903090a050109050d0f0804080a050102090906040c02070501050d060e0a0c0f02160b16060507030902030105010f0303120c140423090c12 79
    0x41005400300050310380b9a800005030550145018003845945401e000e82441d0b0301602c01001a0240f001c42804694400d4182c800d98404990302650390300c40220480c0e8400c45c8801411008808006001801c0400030040c010400240c1d0310303810381680c038001962208050311400d85c0104804000b50001031250f0152115507108159083c2069152144646018075161040f140740e940019007040520304004a00e0340810100d40a100d441401c0314000d4544a00e8407955040c4080841c20082c20089034104401525210040000ca0b1601191b00c038054025540030802060040040746851840400d0050301101800d08045001d0710b00031035031140b075001c00c4c8200701001c140500e1000060280c000d0301e0188a5039034000c12110100d0042508442042c0d0081c1c1225080f0441003000940140010142c2c0f400080d000034200c007888000c2d601d0b0800c2e0581c0603d5000002804a510403446001c00000ca0015a4180000701d07041c040c020040300948181044840c02c4c818501c43d075842086c02648 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 133701843 1250 133700593 133700617
    0x3050d0924140a0c06050a0b1804030332090304061b0614010303030506030105070908101a030d0807020f0a020a0b0c07050a0f0e160507020d0305040e04030e0f0102010b010206010b 79
    0x507440c0792850310b2034070380c01c5184424005a8100301c00024081c05000d4542c102503102c0082041c1d40c0881d0019008120341c1803421441001d050001e82030502a500138260041d00c0c0305140703048902140c51884d00607868905e11030400003070020071282e2600009a4081da11291541104515459800398021904110403540540c948044030071108003c0c0707059008611a0b02c000c40c1d94103100c030805007543d800420311b504028003d1010091000c0c0010310021110421400040c400220341000940104000446030103209c1c9000103031042d6841b9001510800c520344c03d60705d03a000000c245946403404510013940c800c1d071070030081c49030026590082101c242143e081b01c110300c0d9178101155101d411580144156103001e8000c00142c80030200d410352081e13079a040725034481c2c0c04400c082c016006060300a4040c8180c5410601098040c008440240510b28003a01852900380340052108204002c454000c2081000070032040d40140115244000144c000d402035a003051241a030b00c1d042400c040d40 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 133703093 1250 133701843 133701857
    0xe100b0f090a290310140105010c0c0302090411011d01140309010b0901090c0e0102160b0906071502040f0501020f0d0f12020c010c14030907090c030e031303050d0924 73
    0x1141d43d0a4034480c1c2805840c81950b4020b00c012007010300304404510100d00650401c001c80305c03203031a89411541542c109081103070340c041240c02c045c00d9021090b00b0094010441c0300a000078045960103070411305900366111403440c840d00051001d460032140e101400b10b02404901ca001e010300c0405075512035078804c00055500000b00c0050b01c4083c0030382c00550015540c0c4260744580f548008035000001081c0020002e4140c000b644624200c1d02e4403c0c50441d66010030b189141e680d81100300c5580d550040340380d41c40c2070314008418000354800d02c610a8040700025000807594004241da8000220a0020b881500c54050065400819440400341041b0313542d15020307040411071010f011003840d4071000017101428044080c0005245402908040c001030003089048040001c800b001d03900f074090045034a86d00c3c1c040980c040e044080e28210140404a04c100d00e1850750f000f1002101e0151007141e5510030100010f680405803802015000c003003d04035165024400d6070034076420502894280 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 133704343 1250 133703093 133703111
    0x40902010c120c231e011e1506110c010f180e100e01080d030905070e0f25050703031a030a03020f0607020d0804020d06090203010f0e100b0f090a 64
    0xc84044201010000410403012845080c002d544250605102800420560b055071040c6134a03a01c3c451022803010822008110518004003900100b03607040301d140340c400c1001c0c2c146095070080c245501a011405404440c0012036900c80d00d0310914aa121030084c0500010102c0116644100404110705025507008084180705a0b00038010042c00240c80750304d507034100980c0c44080a400d65008918682d02e0000503c601c0d603002ca141c5042950b2428006404052480d00c070381054007603032080160b200302c401013203008010f002031503104150a00100060a441e0781c14004801390128824000410900c14400024040e81c0440c29a04203145490038640200000a01d400300c224000c030700680040c2c90464500c8402c1100580181490000e85029040540c0042410304001c08c041e1186c110180b40c0e4080c001d096008040c03c0390060000d00a078514440031001820314010403800750b1045050010102503d4880e81c1c00d400402024501182d10010030001481da018101d002d60554608000c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 133705593 1250 133704343 133704353
    0xb0c180a060315050a06021c02071e030b0703050727081b03060f09100209010e040f0213050108010e01030303020f13080601030c0902030717090a020402070b040b01051e040902010c 79
    0x11600810582d0350206403403544181c00c01e064401584500d004540b204401d001c543d0700031501d52094080030070442d04004082404030320307100344d540c1308919a15421024815103001c0f21508000d80f80503004801168562440840032039608550f00c800058085040702c48403101007044454505220503554001034803540800d081c58100c10440e515180010140c060307608003800000c3e40440c61110345a07907480e00c41c215503110451105880310790755001600300ba85a024403503491800034003500401034554603080e044007e600166880400c52101d910004956110b03413035050581e20b01c00002c802e203903e5039800343c0103900600008920f1070024051016459801d0f0300400081210b60014036895256080a003403203a1070740c1140d1100c500400030449001c0d0441d100c2c030606445013203011080c1d81d510b40100d051105040300294442c0c0006100414000c00600c1507010714018403c08029903642c00400000c0500100c408012120000c7c41841070701c3c00d940000d603054010b0500740c07406130b080daa031 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 133706843 1250 133705593 133705609
    0x100513063b0d0e03010f1a040b01020304030f0b070c08120405120a0212070812090313050111060601081f090501090c030209090a0c09030209010b0711031612020303040305060903030403110a0b0c18 86
    0x7c032092142c1488030001992401d1b000b072030f420b00340a0020b545081d0454071052118002030305c000c0c0c445003030f02340810355491280715031210203500803400036121001e00d6400c5c4849003040d00c4c142ca503841400c5a500a1441d010110f4281c02d0050b0000c3c03070740310309212105109030494030003922444818085441050780c0300d1022031007401070b20b0146903034207082d001c21250403c0d107800035030400c002c420000d11041400517070b15800c40700c00d00700440c0c20f507284103c0c0b0b05028000c0f0b00c56000c0610100000034488000d070451416150002e0040c40901d45020044081307001e0004020f50200c0136a01080210b0f8a03a8407003260808a0f1819140e403139200c0e0045241c45900703921003912504005040000d02241240d0074040c4441103001c0d00080c051001d0541018040740100c40c0b81a503505103503421541d0400454004542c4041511117a02d03090345030340e413a50801c840a801003455125241d5042c500402c0b004540703135005c0400b80840d142d0011103071181d044030141840242c1460a00e502e943c1d05c00003 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 133708093 1250 133706843 133706861
    0x13020f0a09080f01050106120203091c0306030308091204031e061109040f06030503030105150d0507020a150e03030703020901181e17100513063b0d0e03010f 69
    0x100d000c0716a150a142a02e4510f111000000d280d2420006000440e40300040486c1703036220400140e100d48440742ca517410710022075030003613850351103244541019400d504050f00316402619401c00e1913583d002c0c0561143d24000846140030410403050001964101c11804603190403880507054400c0fa50350b04044414810601d4850f0001245804592529024030728007101c007004c06000c140c0c55a92000c0e540d00040c002c06100b68050030b00500010070f07000c01d803007424940d00c4d13082c419801c2c9200042c3d00c900400d001503c403501403020781c40e0100124003460460a02c240f000354516034a070281100250840d1507040d041084003403840f0380e100381c100c152501800005c1000803c40100003000c0143c46102d07440451843c051400e0740c400110041298074480c1d402c40d001084969821a16117002e0620440c000e104038544800d0090511075201901d075107142d4206042c00300c07008504065030030790149012840a07481511004580d9225804181d00c183c5e01500210303140c1040b404180582d04181 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 133709343 1250 133708093 133708097
    0xf05060a0501030605010501030902030706080a110315310902011b1202061605040302040f06080a0b010311040203090a03121b0518090103020112021c050103031106010503060c070213020f0a 83
    0x8401030060008500c0785ca80105401d0904110a11184c0d0120392a1100d81c0b00b100b00348206200001d00c0252a500710350001e4242403281030356072a0580b034000100302504011400b584481c0d0300c2200345030150422000030005011110b111410001c100d40107801308020480c10000d039001461540c00c1149034501e65103114048241003901c80c1c10000b0720f000c8008241e2400d03271480074810712131540c200044078240c98056034045160001c0200c10005045194880e6000c0c0c401e82c40380c003082c061103842c07542c103032071280b2042c4403214500010001a40015146504140c0000742c0703510011340030f811001c05480300200c0c007040c4a444580c40940003d9030001c84c00104200103a203076007030351010b03088855a84080f01d6885e02541140c00080ca0722400d504d400d41c0055000502c01c0c08500d11030640c0010300b941160a20a56849190090610503007064888071031240e10000700d11450081070480c0300d04002509941400d40c01d07000c0040140100c0100c0110f02d601308410040c01c0704040040080306400c1d = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 133710593 1250 133709343 133709351
    0x2040c030506100504050a0e060a030203120c1207022d04021602011106040525080a0f1a04020603060103090c05180f070305011211011701060801080d08040803060d0f05060a 76
    0x1550500088070100e01000c002c129081100b440159030706030305242a40c081c0d2041d000180c0d508402b244030580c4940003c1d42c1803040c0c2514144900c20f9000812002440109494000118074504401c90056140007035224441403070315506100c80c0c0462116005007201c050a07043c40420210301247e20403c2c5002c500c000e0b044080c802d65030808c4001000d00d04c0350005116a103855140e690700d440e04a511a40500c8281030b2002100b00300f40040009007c0700400d50300041681d00d0f03e811545502d9504480e0f00b40b03030382d008080304c40a0010700b0b0300c901e4016250f2499aa1080011001000030308000c940803600c1681c045415110305166800b0190b901e28041c6640c1000d0000c54400c1400401ca00d0405003440b0040c000302ba40d458040e11803075030001c03116010400c044010384003107906182c180c0d03084000300c0000902c60b5203c40383e581210004425038105212001049810352401c0b03a000d490010200081042400c020384040e80d194060301540d11201042d5862a050680507512002c0c580d4503 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 133711843 1250 133710593 133710601
    0x110d050109020a021908030412111c030b03160510120e0601030b09030c07030f020d06020d05040201030e030f040b0c070b07050307021e030606090405030415020a1704030f0b04060902040c0305 84
    0x4000e645184172660803452991801c03903541004501c40100000d1910000c0c91401c040b55000d1511099801c41d0f610a503082d5030031501d0580b612203000008039001a06014425615081c0420280f40e01c01d45c5003101e000b8542000305000e01c40095a00b20b00c2006408640c10048440511514002d4210840504010351444c100441410006801d01216800400100e14056030000313100c0c2c11250310401251000c201400003400212948501070030441c0001900300d107014296101c40e100c0c42c402d880030442d010040740c010782d84c0d00031031152078160642080305000c5c0c50501006003000c0801c0c181151b2085803240c0b14108180c01426044409a00c0403505908518000320702090300c5401036040c4410f203003940c00181e034405c40580b51500540192010a09004083c822100613012521001c4030510600400030340d21041ca00050310f00700b5102c0420325503025014111401c40340c0060100006186680340c1d0080c800024004032111a0303075010a90040c0c4035402040b450300365549000a00d0300d0 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 133713093 1250 133711843 133711847
    0x14010b2704020d051905160807020a0f03030c0f11100b0a090204030309090b030d080f060d120905040f050f010501050c0a0b010308030a050f0912181305091204080709110d050109020a 80
    0x4217111030801440c0c01c1c10104490180f034402490708006107407820600b90b0303c80c000141d00b00543c11301c01405100014450f2400c0c0340d0180c00c41d052113243c0e0b99806099001d11402103540300659400c0100d9500614111202d940d155002481b02c484018281d005107aa540140012a80301707600031030114941c3c4808101d103454520440701039a501780c1c09803c581c241040004c03c9035000401103002c0e00700070300218500792240204008196882454040a4000703000003405058027845254411800e02d0507800500388240112070080000364494005a400d0100641d80d1303401114041526100711029a004188000f101500031409100c659030b80e4100210300105850004041c1c6043d4030300541801f030515000100744001c05080c94940f6211008101941550000400300551041c5417a1500149542551049009921090442c0c030006020410311000b0b010354071070b0523401e400c120020030041920303800ca5076142d000100d555182c528a00a560b04880e800e0700105152580446e001c00303030075 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 133714343 1250 133713093 133713121
    0x902120102040816150906080a0f0c0207090c0302070506040f05152805060d11060c100e19080d0f18030c03110111090f0105070b0f0a14010b2704020d05 67
    0x11181460780c5602e0036400311701070128242441440200b0604200081c402045644080314031914a001402011199030340259601060700a480d062450448020b103524003074403c031400c1a03800000340009580710345507010800d404034402e503028040e9400403c100f40c0b00c040400d00ca80245000103c10a41c407204a0240316152002d1342102c91524081c00f0080c2e60f0021000102e540c02200e0f103000b80d107541e020032a1401680486030316489810003440202a8030b030080c00d0442070800440e0040194003190300d007040c0758120b010700110780402c5000c000d8000c2d6000301000140c546808070300351030046110002440d1240d000d4001502c4c0302168010158401c820142d400aa18001c7c031204004180000d03040c40340743c4916100b18008140c003055039004100b92000c0c56044031180a152030400000801a030702102c0811003985054407142100d001d81d12407034160703880c0e402038a040c07405054203040c01880d242034030340628540490b2a4100c2d0395a000811041030851408070f071504112094105d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 133715593 1250 133714343 133714349
    0x230d12091d130813080709050c070305120408160b0702060c0a05090105130807030c090f02070305030a050411150c0c060a05091302070602130e07020c0604090902120102040816 77
    0x10100031011007140c10400c484a90001c92100b400030451502d0329140e640c510450034400c9204069280000d50002d003c5041012104511800d020554407404412013500c5100001004560140003400ad40716840480c0ea50044c0b080040c50302c1d104980b000200d800f094194100c03003107400d802c104195168103006094011030140a080e0038585103c2c8091b0007409030750280c40c1007080110756001d81ca03000d00b5842006109180a0350802600c0f41420070480f8002c1c00b400341400d0078005240110540b501c22161076580540e1460300b107460b01100f203006000d001d4825540301e03c031511840300c04d949203901042246198040d01d03a85032540c192071800d0548030f1030300d90301c0350105115001200f508030003111550041202e40c040c01e01488000303c002270066083c0a4031461001ca4030349412100380c1da1410959010341c0604007542c0c0c8811040f6660108080b25640014090104002d1010316802c000321544c13005080d0b44401d80815195403c90700070b42c2c8205035940c00704541000301c0301c011600d4006 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 133716843 1250 133715593 133715609
    0x50601030606142b06150906030c061806080402030c100206060102151b0703050c0d1805041e020309010b061206090601080f010e0a0b1807030c0c0c230d1209 69
    0xf104100840f02c8950348000c202c101200300c4140710410007540b9030080031560f080b0035840c021b20742c070341c5c1c0224014200c0b400300302c0301c41941640209265002e40c0b0640f04030007501081c0d030485410316404580c42d0301c010f00126094031411a40036060360390403041c420300754080c0d4001c1065103000030009240110000c000c26052400d9000d0142e200c4404040604c000303900c055a03541c030f1201d881c2c00c031101d1041600c200c0b11402a0010a0800d56000000f8100c8032004040b0100164844080000315000001090640c030110700803891208002c1d005075500288100c0009245801074011400e00c0d8051135440d103000204408220040c580009040d800060a07c0c0c012031510705020340000408041c020316503900344030b00004041c0c1480e03030010a02801d02038075240c4042c0e00d418000c441c0403402d07500304c000300f410050704d5a42a0722403205100300b03540080404403c0740c602414442e88080200409003443c51301642c00f061511540c02203103400b40b007092252084581408000d001d0002d81c0c000003c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 133718093 1250 133716843 133716859
    0xe0402071218230607031e0504092a0f021c030204090608060c030c0304020a1203020f06011e030807060204030204141801050403171503061006121b0503040f05060103060614 76
    0x211510844070f00a0101034401c0342e6140c1250900b51001240c61400c0107200e0010590000740307951140c003900c110307a8400402d00120400d4208009080c410311441c00901c4414810a030005110b00c80c0080c01c00070b5401a01d02400030a003441040000f034041840200741c00040410840b8820301c2000010550840940510300f041145e501c01d41c8806450070390141c50100204095540b8111514000c1c501c015448204825170300c0c01079142d004a04400295008400c0002100602002c00e800b03419000c00c1c0340f81140341503658803550303070b002503009485255080c0b10210041c0ca451103200c3c0e2300c4105090311000d91500e101103108907502da1004550990504041c400040e40000c4e862442c441915080d003c0c41d0b80c1c0e0b458001e000ea851f40100c070340c10306c544428404210150004074050f2100c1d50382d846c030405504124441540e59040e1703c3c1529182c0e00700520f504512482c09107030820b2080040005100349900c45030300d0a0420303081501c0c5c55680350010044c0500454151808a1059400f91 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 133719343 1250 133718093 133718129
    0x60908030c0d05030a060b04030b07081008070504020f0904020304050109142b03020c0a0b100503070b030705090d060c030203010e0708040f02120c0d0f020901050a0b04060e0402071218 81
    0x1da100d6001210100c14040c01201103480c06035240c0095014001c440045500c031603413400c12100b00541910b207400400c3c041802314846165161031001550040310080a0161910052100a5002203072400e19600144203000840c1e640c1e00055006502841c00407518516600380101d1802c0c10645009896002c4804101500d60000300d201c25100056420203900111401c00d038064400c2d94400ea2050090b11001c1c400c00400325400c50043d0100401c511748241c8030010b00d40c2c2c0e466107014043c1208070a00c0000e244900c03c0c00140074013031010b8040710304601113a0301e02090710501d000301800300340c0110050000b278030756000207544a0541d2030b02c540c0d5828035031180007050007083c0e006405450280611841090208605c12740701c0f6015002808288844c1001c540c9081000f01c1207104425000002559180c843c00740402d480c41a010181351a1074000141c9500402d1120250800c0c2c084c402800070407018801c1812210140d03d499030401400c40400c00664225044200980f10b04c0d1144 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 133720593 1250 133719343 133719367
    0x30f0c080d020606040b011103070606140d1110020f060702150a1806091115040503010506190e1902030c090114040b040909111207062a11180106050406090803 70
    0x1c80e002079041d140020040c0301b21004a65a102950781408140300018190341040a40d50001d0102d4940e801c09616110043c01040714000300c10201500c508220310391400301e4030b440c2c1090141ca0b078140c0104d4410700301c0940140e0030520203c0e00d46016130000303410303012529441c0070510ba1010b114a4100310158600020b1601c10b4000302010380a2540c4414901c00c00c12240c40c0b012002d64003d1141070044203100040440d6405070040ca80a0b500302004910755080c41c4400c4034002c0c46885001000342c0c10505003440b82c190003003280d00c0100c11004104d40107041840118043d002e0a002590741c2c12a10f00003410503400401284c0000c0000c00c001c02c000d00348441a1820348120840200b903921541c205110045030300381500c0c0d8040e40b44458501032000c0014500c046480c1c40d25800300c4c1883d090040c04c10346400c2d0661004801d200804100050050081c41c602114010700c05e140841020403070f050902d009811800c00b00c1c100207410700030150809001401406a100214a000a40440 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 133721843 1250 133720593 133720603
    0xa1214040311011509090203100c0507080c150709050f010f0906120603050714100507080a080718030605090f030c030d0908120c030703110c060708070216030f0c080d02 74
    0x805010068910b901190600c2c081d040f5541407030415007080013040c1c0340c801d9000208030804c0124481d02c503412803100b8215150040e00d0041d000c6881c0c0764200320440c0c550690b141d100596803041401400400100c507614215814003031400796607074003100e500b047c0031712086a04007030032039043c41800741000300156032150082c81520001d00d4600c59180c0f03511254000350805800c000d1050040c0c1d003010503820724080044000e681c013210480c00c45a10303994107603000c0c8540d000180c48110308202803058180540c0c030054208090340303440c0340c00940409145112006640003158000c0e00c3d1814050040402c11844861a000c0009540341c01c3e49100d1243d9240f05905131030000a40f100d40c0c1d00c5c10700040c0e1090300c1c6051050020807001c0e1401440380b131190f6004580e03140120340b80c654880c3d01c1c4001d030070545002c080c850300180256100d0050a0740c0000c401040d620451245440724802c0e0184413a403038009512071040541041064a01105035248541200301ca42d07010078050034030b0680c0010 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 133723093 1250 133721843 133721851
    0x10e01092a0e0901030609170c0304061d090a0b0405061e04090524220b0601030b060912010204030506060108100312022b0e0a05061b01140c0a1214 65
    0x3840d0380242038802d88010203005903030b9600400f00701c0008107001568001180007482050312502e40111000307007d40900034441c45084c90f034401c0c0305c2400428003401103280c0c1c00001c4031054595021601c00034a40b11812207410034229107c002c02015418a40102604440b088481d408004c0c000355030b030745004040500d110301c10344c1c4581c980018414184504d45201e000d0b48508152018170000c00e040001080d20402c2d40d024003a411001c1100203d81406802544482c01082640700e02004401401d0084005d0364011420400c0d205160b88865242181c0b554460016840c5c07071942c00c189003410b1004142e20f045c040c0c140100240b92011813002c000792075208920140c7c94002c1002280b804e0300c58024450892000b0107100f0b071200110003900c02402e1983d4030801862690030078882d00b680544505a00840c00344000f0800c9803650f04c0d24800d001c46640001080380800120308000c18090f0380c1a540084002001100076900c40d580c1c01b064138900c0340905c5081d81d101807860344400010 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 133724343 1250 133723093 133723151
    0x6050d0908040b0c0607020606151206010e060408010b13060e04080a020309040c030501170a0308130503160602041703090d021002010f1d010e010b0d03050a05040f0905010e0109 78
    0x180c11004112010050741d001d4641c020040f504c80d024038a089030f4810080d1100c001600c5180300040240c9081685031041d40c4020382d00314101007a8185d00010804050b20b03041c1408961440d006c801e403a5070015000034500d240c0081840d40e0301000380161301d1a00e409a079010741c14030000b409882c803c1c6c405940c11541c0310301220341e24400b0b04400c03411400b86000032035009051068a42c0c0702641900980d041e2516030303c80b100500b07698a40642e440c0c1220100034003140800001449240d00c031041b540515014400380d074036203035508006080801d440340c0116166a804030b0709100d003280c03610078440d203c041500203518010700e623000900c00f0800380304000d21a81401c2c81c48920300d8803c0d000140340203050348c001e002541c051a0b1040710207075242d1030101958a4411036141001c0c0500517805803500140144c01cae82001c3c0d17202122940e10810f0910140801013100180384098105444024550070301c00140c15414444007d0543c0c0040c1d03c4800b2160034218011842c59070709048000280c040 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 133725593 1250 133724343 133724351
    0x30a0b03010e0c01050708040905091605180f060112050a061e230d0204050a0f0c09030308010e040305070b07080703110403051e1609020d0b090c0f030a0f020a030e011506050d 77
    0x21f4540b030111445683c0103207102c54203100c1885131840c80003411100d0b0082c2102c943e4100740e1100103022547c00380800320980c040000000c95a0080270921613504120b042c50a1280c1d080300b0b02c444016240107858810720036030340c1d0104021900107843c1c010140c80b06125880c61451402c454030a00018219020348290081d196030203042e80c807103180894269010704140316600d8543c800780000d210588a1455042c00c1000c801200d510410303131001074035850344690200c0d13424a0011895100018011400e2080810582c004141041d00d21031169880f81d860010610304008001c0c103035a4500001e1944017002c0c8070500000f140880c1001080248501705c1c148440054030051501c42881c0c0c00e408680c01002c40481d4040e0141c000300702007c00c00000348072600701641400342c480c0d001c50340c03030740a030809222072130903207200c80d0055402019600000c0f60300c00f2091001000c0ba4804002030300820760307401386115040001e0141c2d1000c0002c5812401b041c030302d004806401c42c8210300d90321184940d5 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 133726843 1250 133725593 133725607
    0x109060e0a1521050c0d201611060301030c140a0b0f09040605030a030f0f030207050106142d0d1403040603060e10180926030a0b03010e0c0105 63
    0x541030741c20340205540391002c08120300020010b442504a20b0901c01c00505070003040e00c50303401130301805005603d0030f0b84140c80d2110212182004102a4110150880031710080300b6055850fa0050490b0386800034105520418502d8140d9964080c1c58589004401c10320041012a00f003250100450341500c2c041060100d0120010704a4482500240007611000c685600420705060240c904014162020001a5180c804066440f8080140140026210780c0792862003440798900c140d00300707007600300941450310550343d8070b003599200e8100410680000e03070080f4041c078084910307200c0b5102884914200035038480c040303400d110031111a54090324000460b070041051020030745800c14002820f070707901c503611040002c001d000141701b800100c03401c80e40854050b01c49c105ea400c0880b802500e00c188a202c805603020082c0450600c10386240c100d03081c0c40101c0ca00401d80e140000414080960350300c1c509601e49030101c800c051011070181c0e01d4810070956100d4001801c904020302400c1242c0c0700c9007 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 133728093 1250 133726843 133726849
    0x90e0705150c011d0706030b0907200a0b1e04020d0311101b090b19030902040b040f0c021c0905210316020108010614031b0c1902040b06090109060e 65
    0x40382c149412141d41c0391455146901c0020401c1d039012441803015280f0383c0e0750f42c0000300c007a501c00e01081c0313901c210f00a01241849004078044501052100c0b80c0c00c044441c69007215003456200101920480544000c0100c14444090098032100b5100e07c003074a0307814150041a6015440e10001301880010220807041c00810041b5080340b410941c018003400c803000100d00c0000c030300d0b15881d00c0442c4040901080038a851016260626900040c011070a04038071400c50280089110580c0c00c43da503140e209175551198081d90301202c801220110f0421003039100280f9000001c064002e822201150003091964842c0d4101e00301e4004440c440300f0071f0307080240790040740d144050700034040c44002244a51640c1d0060074110035170007600c910401d03030303079809042e00c40c0f901c01f02141c040c01408000081d20101068800031035512100d10301400c100311186414030b0014858600700c03e1a40b0380c03200780214078003809595000c0c0f50982c1c0d410705140901c2c1c0040c01d10301c42801848c09101c2c880b01d080c3d40a403 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 133729343 1250 133728093 133728097
    0x5040b0a0c02030c10030e060702120f03060f12150604020a0c020103051f0806071706010503011725050a0918120e10050a0201050f040221150f060901090e070515 71
    0x10a000b0180c0c2e0f175680d01e0a41c00307001070460300d01107030b0b0314007030300c00054443c030b0002c209160f0000d10b410301d040c58002c04044980c247e0b400203004640c04500d1000254103610740c0c22a40c001b982c0c08800030180c80041c041c980c01d40e030500410a0381b0890041202c001090362110542c00d4495082c20082140e071181c145501160082016a10103107640c424001205140018503c1c040c0c0c0075038480f4140c2035030700d03d411035501c2d100701d8026000c20003c0004010494008080c40f900151140641c1c1c0750102d007140c0d01c0c1c0e004001b03445090340c1c41b071040c100740450b280c1105628000c04401d00704011070049203c0030b4542d813402010142c980d0f19100050160140511605c292602c8006c5c00650951640c02000d01180c0188010000561030240001c101e4100070494a0245030003c0c8100c807030807412404401200c18455200302d150040d8002c180000c4049054140610307103030030b4103c0041c5018400e00c500e9800580c02450307401e040003a002c03110080456101e007590410385180c21aa000c01c44821003074 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 133730593 1250 133729343 133729363
    0x10f0b0a15170702072c13050307152c060703090813060503150306061503070e0a03290f130303090816030809150c031302190602010c05040b0a0c0203 66
    0x140b030100c0100112694041103000503542e40700c51542d680e0341480c2c10b40c40c030750003850707071003000040a0004500d010140c0f0340740320750f00d9101e042101e2524a183e80c0c3c20361202441003107013102940b59000082081050143c05100010306001c40070820150851140d0340c0303101815403c14569501032680510007410125010310b0304031066020340b2540c80340e0007030665000316005070340c3d0020511080c00610740851801e003d03040c000c21114005401c800c0c00d4500c1d50014180c00140582210195410b4965282020040d8091503844030516a0501000802501c1080c044051012841007165411035400880d8026807500c141c500d00f00034a01d010340040803a01c101416954002c6440300110088800182c00c2a04c2079903404c03800c0d1102d042d4960350761b4846007440072a00c241c000042c10040068051640110081030030036175200e0307a0300804d002d042143e02c5004484009001407042c250240942103040c2a50b14155140c10314002c0020319900545928404100c810300600d41035540401102c440 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 133731843 1250 133730593 133730627
    0x105060307030e191106031e100807120c15050d110909150a170a0206090414040506040c120c03030f03090b01171209091b121503010f0b0a15 62
    0x50014035090a03600d611000108072292075059828481500300042502e004403075584800e15230a001405542d440c05000f040401401d16090000412800c1004118000c06a580c40c507240014039051101c1851400c3d000b000d000c0304007403050b000340e0380c2c48011a44441d0b070400b0001030320200ca010344e807410710624410b240d01890a80600000ca10302c1068090480030803501c07001070301d598103e08503440c2d0403c81d8090b0143c02240501001d41001d1000707103040c20008100144140c00c2024010482d001038805071010752080d81000f040144419200000e4903c1074440d03001c8200307da4840d801c510b40c0340002400c00800284c9011100d010340c0002041c580c2c8152030a8040d07841d6003003101a0403541c083c000b4544200750900d40401072840880354030707000243c0702e202d240c0d80340d41415003104007650380780c40301100410a0804010388146854090041c1e00d48049128000400301400e5800e02c0c9100b80030103140c005446020b580303a0400b401203c90714040c4081c074111110f4280d43c01c0c811109080c02c = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 133733093 1250 133731843 133731853
    0x7050d0b07030204150f0e100219080408070b0c0d0c020306010b0c100504080a0306050a0b19021905071d0f0109050612070b090a0609120b0606070f050705031e060105060307030e 78
    0x2401508244200c6c030319480d96645142c450281400c001194880703803e0240541c00c10364103000480d4588000701561790081d4201c503e000d5a4001380ba18050156000ca211004085250711100c0024410740440e03003000c0c0b030321213041031240d00040d4441c003061060074549000080c0720000404140808040040003560800c410320301410280625848500507400092910310701107158074140c80741384103507040c00100ca800c0c02c022542440840805d000d030401903102e20202c6030380a05050744a40340b064417a0020301922407408000c2403010031342c881c964429030030f19810050314504542071181107030451040410540c45401c00b06260f14180038000126026100d808126801000300600caa50029a0585070b0180c0e5480d041b107240380e1341c1c0598030560351944240c3c40426a03000d00203412980c002c141c21b1a207070709a40d409503404003030703031003160310781c200e002c042055140c00c2c0300100900ca2002200d9182a960a005980740c000500407240300c0c0340040301107421207100341d002c490a0744403082114 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 133734343 1250 133733093 133733129
    0x9040309080d05040b03010302040b060c070902070c0504060605070605070e18010e0106051611030c090a0c0908061e0408040902031e01080d080f07180f08060907050d0b07030204 78
    0x8003091580d0060854030300ca030755003218499104a084508451020900078116403d5a0170000900b02244c801a445001031141c0e441d01003051005200503d404207006035240c016203010743d2226134950200b446a4540030040000b580c004048a2115500800003e1079607904081900d01e84135468200c1d8002c0c0050522183c40030b210140385050702d040c201c504d03e850382c0c0d0303490840d510f10803d01c1e00943c03000424584400138400c1c10f0580c0b40160000c00b9940c0c2d0708840da000c50b00c20f04041324240520713520340c0004513020342c220006401804600c00500f089280c001154140c0362410480480f10182c1d140020302445501c41c155006000d000b241950307207040c811650300c98040b5800850520686250002400b110300180e049444200f5480d62046c55559120707010315040000c0404051140ba10780c0510115000010b00019210050090610506040d54a0300d000d20052581846034400d890500c0303c1e586002d820700040f68000031001103a6166201240a40920340c400c807a06800304102c0 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 133735593 1250 133734343 133734347
    0x1302030108010b01030e0109030203041205010605030a060902040c0305072c030607050a170928050115080712080d0c020f070e060108071e0509150409021206031507031802090403 78
    0x16100701c091707a061041c00329404140b0b00300c0c0c102000040243e4020001006620142643c2100050241000007a65640c5030042410002400c80c201c582654442000d030441c903051251603015000c0e441c0070400c42c40c008402134100e0103440d090100e240b40381c4409410050707212901005906014041c0c0e40315082c0301c2805481da8200e048042c01195036100712041c00074003020102e10902000004010403c10032040440346041d400300d10381c400c04d01d5000306004c21024025194240440003801f08000c1c42c0403c0c407410714240342c202c603403421021a40c00700030688c00340070b941d26145000c10002c0d400412000c285c1c07614100041c11005802004e000084840c50003d06510a08081e00c8007102030755084d0080703e00d02d104a1a440c043c240c11000304110610420242a8800c00517115085000015030b00c48290303001940855000b070380010b40350710744880c07032404a42c2000e4150018003a91086100e5041e181d0002000c1e402019a51228481c2d2030b400c81d0f400486050300500603404d18103181c140 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 133736843 1250 133735593 133735601
    0x60f0415030c031a040f02040504030903020316030606090c090b0901021911031207050d0806032d07080f100209190605180102060907030f141e10061a09130203010801 73
    0x142e42800848402131441814407100502c02d640c0120740c074220903465400c10004120241c410f600700600c1140110041c3c800304804504840ca02d4000070b00720b85189800025566503804c140515030402400b2040c050700002e00d241540c40d00440706854442c2840100e1070044402c207803030b070710384401d190705820302144003c0610038074400da00762100d51001c2c40c1d00584134490004002e003680d0040d20303064041442100c080da007140000f8180c3e0841030200c00c20301040c011216200060b1711050001c0c00010004010480091401d40060803880c4082d0360015120503c44425401440c1c00080503c3c0da6951501c1d11508171502c04511f0300344940b503050003029604010300f074090444c3d4124a0130a15800003450a21a024680040c04181e0860340d452031109501142100c4805881c076280304004c0701840046c40a4084486100e810007519081c10300d00b82c02840358035103e500e49841440521102c030002c1c00001000c00c1030070342d03559070440400c908000000d41d5030b200b1440440081205001904 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 133738093 1250 133736843 133736849
    0x110c06012309040308010e07020705121509060103120f030605030d1110050118020c160801270c06081305060703150504020306060901030b03030412030801050405070e09060f0415030c 80
    0x1d20391954864201030020510b025038026021074590780c01040141c4001e004a68480450f20685017801d0b900d01c0803030310151030003880754104d4100d41c1d0004040300c407505680e0b80c414003020060205514580343c00b80d112105084050812a414a51000481c0290850750007000b01804580116038a0480140841c408de044c000d110300807050040500c0700c850080070f0586488480c40b17000000d126003440000d61060909040d140646225140e02c0d0748460329210052507005d00114545a40701409a40ba040c2110010f60356101c0f48508408039a502c400c82041d2802030070101c10584903080c414040c030b40d03080001480d80c41140200440707903034560407440030044804442d4282c3c644500401099010842c2d81c2a00450240300400380c96200383c0000741c8000028041d240707040d0300c5050800c02c0d448051015008a44080f0040020342054410954040c1c41803515824101c1c024002030303c0741c40007034811841814045044642a9250fa00c40d024080c0b140c4c4400441c07903500d203440c42c19002144 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 133739343 1250 133738093 133738139
    0x10b040f0b0a0905040c0e0d081b030c0307030e211005160e0f0d02130917071e0302100204081e030403080d150306020408010f0605030705030c04110c0601 68
    0x600005003480341e41c81541d51960307681c0c40e4818280d0038030b01440010440383c1d15020030030065100d8040540c880c50000100319000e0f039180b591b10055401c440d244000811a1803007294020421103168810200c00e6906040e45850a1200720a200d0300041d0281c541c0003c1010072443c44050ba1000030000a01c9141207094034000e00041e5100802060158200d04100340450b0407807a000925190035128042d00c0c0a0040c20340100c0201c5070082241003071407121901203a40d44100c45e40620410f011141003c40b1040380061524142e60368107056002d6030510011186400441c3c40205802440504800f02000c0021520f850b52a690704e95100c144c0000307034a42c090006061100600d012044500383c0e5040104030b40b8110800100f003006050302c0b490141e40c200d0030080400020081c6c0020300091070441c0002c034650041e41c02d510212010b55016501c680d00550f41004180c401292010408004450001e0001241d0011400d907200e0300070207100e03034003d2500229070082e0740b05c441102040c2030 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 133740593 1250 133739343 133739369
    0x1030e03040617190c0c0302060c0304020a0314100e071d010f0b0307050c0a1101180e070302070c09090308040302120406020a11011806032301030f022106010b04 71
    0x1002015803a44602c1c05000c00288140ea46420030925500d0b040e60000c0c4080004400c50441011180c121070440e0108400181254040000d1660401c542c603080301601400b50314605107580010311003c100e100c01040d00d0980c080214182600348040808180c040d80e00740511501c0c070184503110000c074061092081400d41c0303a56149801140d519041c0d880c0403011a00c9541081443d80751908010040800c01900b041403a81d50f440500042d10414807d000402104104500141200c01a00f0540c6800c4140e0741080000142008410342c00c0403442c100182c5e0f400c42810000109800380e00142c140a0501782c14504040c0c0c0880c0c41407003503000ea400d4598155400380303103c0c1031f44038900c0b40800680c480c56203e808030300340555a8004280504020000d24010320583c407400d0082da200320f001c030fa600c0f4204a10754014403c100031303a0350005400f60280d811540c8018a101c60f410380030307010b05103084084009244100d80315045014581c01c94800f90b9460000c010144d2042c05a285c2031800 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 133741843 1250 133740593 133740611
    0x50a14030301090f050c040314030c07060306090c020c01020c0108100320040b0306040506041502040e13020406060e0a031401020c0703050109061a060904150b0406050403050c0d02012007050402180103 88
    0x41e45c07144034090320100c0d100c0381c40c3c14a1900c1d1781d07110280000d11892680402c020030640c2640800014004150540b0007040061404548400f229840754031282950007980d01e402560380d0102d07402e064a1002d0a10030401d1312002c5491003566136a8200510003552828500c1d003003810211421803401d0200d03020302030f000d1b150003415124102a90000c003182d014cc0040b070002031038082c0f150122104140018146581d41c4419401c40300196041003a50490490070403e509050080304054a098201007500c803003a00003040a280d054400a003101148142401c0c80304401c0d011110101b03520fa044550340703616418414024101124111443c0786000450610078401114544c072a0310011300d45820310000405001c080c00036481100384040707030054003081102c0040080c00240090340e40d1103844a0035860442d2410020701c0c1518440d0741004296030050f0383c0b0012010040c0400c00304040c4110b4032590305441d10031244c000c01c2c0c0c080d00102e04e0034024450101040b02c141c0c2c0c240d905002c0515 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 133743093 1250 133741843 133741871
    0x2208031803060a14040b06060708040909020f190501110109140d12050606040312090302100e0307090209030303010302060d0912110c04140a1a060f19020106140904050a1403030109 79
    0x44245013580c4000d003010003c1c001c40d103ca09802d90010000c3c2030f540c0b07420070f0750740c0c0d4480c60b0b445500000c40707132130307880c0e002109500f015031340c01c008a0303010340d080013021500c001c43c2c0b0009030192044c5410003280c201101074800e020b402400159510031210007800003c0c0245a0702c036a000540171001510f030aa03501319501e2680205800f4002c0078005910702419500c8030070f180500078400340180710f403a010010050f1140840007500c1401a5550348456150300c1c00c01d410481c09a03c130301162401403007800c01c00d50307010085904582e4101c1c2d01c01d40d541130740060340019202611020384441050143ca000c6e45420501524040c107110041c1c5129510307080c00c1004803020001c010030000e0101c0c0001e41030102c1c030740c00207000701010509180c1c00c104010028850b94440c1015151111000c102d0381c60802d010341850580174140e00091000e107040594a042d40000080d59602c00c541040101e81800401d20440034017640003d0f400c603082d06003042650783c0f40e2081c1704258081345022144a1880 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 133744343 1250 133743093 133743101
    0x2031005010515070f02060708120103030e03010c020604050616020a050d030204180510090213030501020d0c1107060f050f0c06070e0306100f14061c0e0706050903032208031803060a 80
    0x2561003250f170300c40f41c4455028400c883d00700b40001c503000d01c03003001074802d4402c41c8840d10b4002c0d8800e90f2101001d0071b00c1c1e0241802c0d102c2c3c2071540025540040144400520003050160340802070b0752545981c40c0c4101070484c83c007030710b610000e0b040e4010500700058145d0705400800690328042a010f4420088222010440344205d07550881440300e00700c184000540d030380060a0070082c0315140b503101902c1c2d0300ca19007241c0c454201030196594032404a1800e40d04807000302141d003407040c003929600e407800c84003510b0064540d4580c0208180050928082002e51051302c0414803100c0c21030b4014501900094440d4803002d1419120380305050002704941c0422507041d0035541400c414100080c80d20310840c0d04804401d07403099211209202030710107080344020720503e11440c2070000c01d00550440d0240c0c1060469000402080410000c1c0c400580b0000220740b2000203020218003421580e00a825614102d9041030001d400001a402040d800c15140b0341d200742421420340d80c41d5112038907504115 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 133745593 1250 133744343 133744357
    0xf09061b03060f01020c180f090102070308010303050c210714030406020706140c160e0606030c0a0507020a03050d05071a09070b0304030c02090f011410082202031005010515 76
    0x11141040001d20900380340a44103a01e0740f042c012104516500c8002401804001106a040700b20301350804c00c1201d0b99022441d006500c1ca8021031074841191401000710710140006810b1000020b400980030314200040c0101d001401c01540088400c9190003440b54010b45007901d0031520381c000082e17859008400c860441350550010b1482c00c1c42c041069034244481007a068002c1818009000015000d00c1115800f0f02c0b9003040e101c0007070501c040307403481c00c1010300460700918040c0204020305c0070110031070b0302c200c016040c0561101120310000d44041c5454100078014043d410426280b1a003241c0502041481041c1180307244041601d81c0c20940d404699012466101001c10041005c00800460b04103019103007162041c43e546c0c010402a600c15103d10340c078000002c0042020740340c0e90300302a40c4140c08640182c5000c1c1c442400502d52036020b0043e001c0c1c3c030350640c19140b1180c28418025407455000c1d050b0b0f0001320340d40600c0001003600740b18241c01000e9500d404000f840145085a0903 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 133746843 1250 133745593 133745641
    0x40b04170114070e18160909090f060f09020d110a0611070e09120403051608061014010c0203150f090a0302030d0507050c151609080c0405070302070b0f0906 69
    0x21956510012a0640700c080c208a4020f85e00142c81480311801040300c1c3c0c8604001200c030f40341200d09201c010700007440399002e1101d95240003405000078200890301c2c050700760810700c0440d050303140100142c0104150b0038000d5000327110340040010051041040d5566004c103d03051400161344880a0751115002c041c001c3c6190000c400a00080c1801c004468000d003000c0111602e001030010740131460382c403e40040d075035603002c0701d10b00d1050006140c008018000d580c028042c182841c0100b6406a40c80d4000e040300c4402900c40281d03947d1041030a5501190018201e800b0114800e08440ca012420788004031004c00030000115144800100504e10f01c2d4107600540c82c01c80740a0061008040141c5038034100002040344e1000604100503a985004040e00004028213207040c06c083c0090601c28074109006a40704100406480419558105201940c02281d2030b507482a0441c02445072060041101da170140c00d012a411240141c0d5105900b204111006030b06e9050310800d03107094030049040 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 133748093 1250 133746843 133746881
    0x40b01080402121903121b0f030b06090a030f061503051b030a0c030506090c101211040b0f19030203040b07030b12060a0e011107030905090417040b041701 68
    0x50034146400c520415140c819184c111000198640d04d20b20030007001c0e00018050301c00070354071003a14440c0d02c801051510650200000c07400014150300c020700a074205040c0c0c0ca030300010745c41d11014100e56000d00024044613006883e032030b14119000c62040c041c3c58644c900519844070800f00504001580c1c1c110008048004c85030303110784650306d05440c2c026018040d02407000d001544828a1001852080c80504080e1403c61001880c01c81d882c2d050601c20030352500403064054001e50383d505904040c010110f9061110b079001203152259a000030398484000640c41d40c24404032001d002c034803c2554010b41720410400f400c030242d010070f0381c02404103881c0c28003054802d4003907402000311a801030054500040c200d4603050501900320380b0310040a0b01c0340e85281d10340d00280306169040440403032013814042e141e180144080e60740d002e81c9018503103c40c041024070214175558401c0a202d2220680e40d81d45130120003c16421a100b0030003c000083c05100c80154180218510388128458540c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 133749343 1250 133748093 133748101
    0x302030306093c0708071e020106050916080702030915160203010507030f06050603010b03010e0601091205100c031b120b03061302100f0f051b0a031706040b0108 71
    0x1015102c0701410f64645400112005181c1501400814801c00b0400c941403010381d6003000490031a0b10001c2414040200346030400000b6074000240002003600024074040b04215050140e0050010f6000307180d1111900301040f51f08000c044001d000300145944030110303621604d0023641c0d00d01a03482c20903440306030a21003d6030303802d4141c050700d042d2203990003101000420f1b8021a086440564607035000a07220300c406000c6250a0080400416040e035209285614283c013601e2940818002d040036940782e100891110b0b0301c109030315400b50007040000d0418026524106503034000040400c40e00300d0800c11440a82030281c4617194030708040340000d00a60720307110803c8600b1400003503100015a51140340b0300aa807000c101061103080c951480c0b200344185801007003406c48078448510b080080d020070741205103038854102c4528206034180380e5100c160f0b0403911840a241148640b900e07116006100e424590310005c040502c001917070744c80403c0e40380e0406200950348982c0c59140031070f1010b0042 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 133750593 1250 133749343 133749349
    0x40b0405130207021008010509060102121b0a0503040f0303080f060607030305190e010f0605090601050703080714030c09191203050325021005060306060d0b070306090e01090512070302030306 84
    0x4040c401c0d004500600d4500d02d41d0018000c3c06900c8000d0300007640c00e02c014005420040c1c800b0b60060300074001800301e142c0412021085200d098000349100e52080002e46041c51300300131b58241d04c3e130f10605032034440b07848801c007840a9403548029030010b20780d600841c002800f980c00160084001408040ca841a1610190058a0050f0100c00340c46105d4002d4100720741c2520440703a10201d04000803d10001c0c5034086015076480e60009071255a050051064980e00f06045507419035050501d00c1c04e80d41c4200e070075181000003220810040b900002045143c509240081654082c200d8a01401102450303000900c00c0181c0151050110801ca00d80c0210380600c01540e070200380d01400440e4440d40c0c525280c09024412003841c00750f440384d001052000c5407402050f40c4044140c00420705403403e500098000b05c071201010b41480d00d4040400e411512a0304990050840007509002170b4060b110700c0c5000b48440318054a80d0b0003011500d401d00c507040411280074940503801181161240303410 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 133751843 1250 133750593 133750609
    0x12020721062003010f050108060312030115021002030c121302011d0a0f0e0103050d180b0d02070203070f1d0408040e06030a140303060f03030c06010b0c0a021804120203040b0405 78
    0x4900102c1189580d000c008075082001140604000c0310404203551070301c0c0015001882c041d040d6440b0341c000c50141517402c1c0030300b02039904556030403801c900d00209025069051003100101000c00600000c10030071165004402484080d4034403100a040e0391700c0f80c519150301c0142c0b040080c006070b00039004007510304003040c01c101c2d4104000c0000c11190303968100c05002008540c405039144c01a00c00400503c1410b0104048030755041c107000002400c0e100c840803800481e4001c07507407500c1e00030410211624969059a8030a64003400319045161207124000c24640944070340c404600005c800303403a001901c100b001707014540c03100c0041d003001e0070b02c00520f0030000000e04542c0c143c41f98a000d000450a80c40c1141c8101030700030059503582c00c4c18001d01c4030100c12010702e203010fa4020040030a0f030440008581d4112140007022a4640c100200c600d820803000c00c0000e94005444140711400a40420320710313000b0b40c45840c6100c8802d43c1d000050303031640150300c81d4080500092000700714509200310 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 133753093 1250 133751843 133751861
    0x2c06031c11070801050a0c080c160602040905180606030c01080f07020c1e040c03020a020a0221011103010e0a050103021f120e030304050705040608030d0e0102040b04031202072106 79
    0x201072621854100c003080c50000c940d030107500a69140c0d018052400c0030351081c0304540313255103001620740ca041b20780c00d00d0314401c0c0d9081108000001c0400400e206d502d60548002d486400c1080c821424002d549041010521000000602809000c0b6006e860300003002d00201030107071540126565080284000001d00900726419405031403002d403072030303501c5400189400d1022150b10405c40800000d0208892403c2d034003400303152040092411070768001517130100042d412036170390f5410001d150b070800c48000b2100140240b5824420028820409140618140c8031404c5030340081f6a10394508a00b80c0d4030a201c041e4129107071030320001451286001003901110a8280740c04c444820200d02c1084442d80e402c03030000c031b410200a100803c80140074410082c07e085900340080307800c090100c0e86a01c21b0610044805549040c40b2440900030340540300144841146179499a640342085005990f0103010403006000742d06c000700d0400c3d00c1d030151100e103005d183c1c404101e29149544000044c50451 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 133754343 1250 133753093 133753097
    0xe04090305090f011d22110a0f080c07141002040602150a0b0f011b050303100e0603011104060f0e0402040e040c12030f05220311150301121113062c06031c 68
    0x41346c000c461410601130010400ba00c43e041c555503002c03102000b40000a048500410040302c44140000903000d803090f14070f2150000c0c520407060300740400ba146050003007400c0b6000640081070004001c0d4000c110300d0807040c02800c03403804568640d43c55100b00ca03405c840540e40900254035008483d44520918044202c844164040c184556101c50307156030001c0342d4002400101250a20000761070880164015406030024031488144502204080c01140110010843d06141c03482d8030324424003924200c0007019004641d0b85880c2d510040c1405800c1f13906450340380010600081c1c03c0e8031451407540352501943e858004001e01941100e00b0b90094090109420300c50004081030041c000d681e00c0203504ca2524512084425030511089254070042c2c1014079000740010011801e02043c0d81c16199401038003814003001c08000141003440311410404075502c1c1140208250004184492032103900039810844580000d010400c6498126448c135011341180711060301c5801c035080340018540480c = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 133755593 1250 133754343 133754389
    0x806010c0f05070303031d06011703040b030906060a0605130e07050405090f0601020d050c0a020d0c08060109020301050301320603012306090603010c0512070e04090305090f011d 78
    0x140c0703030a40c0c41c00700c04409844580102100704100f41d003510884104030501840048080c02400d0030b42e488a1051045160340050000c81e041130b440180112000f802d01c00d100981c80341080c44043d0b94403070040311b42078004c0b0510780300402c820380200706594481c14a20034185009050801c00d04e2000c2000d01a0002c6c46028800840c4035616034901a1003800051441d540740e15100c1d00080c03034440c00c00ca4000901104100c2c1020703100d004641ca8400c0c2d901a00c105a001034030b07150440c43c40445600c030220354040daa0000c81c00c0c1a03950000d50498000301c009001c800015500d000400b81c00e500c011611090010000705a91414002d5a6114500078000500c1407200c00801c3c16007070610803800000d02840080010343d02d08503050035007040c1e00344c2c020420061b1414014059116148000c0910401000000d82041c4921143e039442c000280c802c1c40075482c907160103419030b084000c1c41071103250020742c01030065200c0c00c0000100707510076a84031481e45802d0705101c04108010a21500e003048 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 133756843 1250 133755593 133755617
    0xb18040f090305070b06190909020d02060417370f050303070203070c170604080d0603060603080703030e010c02030301090207080c0102040b031806070804031b02130e0c04050103050706080601 84
    0x1034811601c546000340c54081c0d07502124a00100240c000400b0781d0b21400f0b00d0181c4150400405a80c034050340c06a502c00034100d201ca0000520100301000300a5000c2c80000d030201e80c0c0401e842c1000007010840c4c5c21905841c0101d41504860030f141e05c1c0155900500d142400800001c031003a070075402c2d004d588404141e40964880d503085a00488035480940e0002840c00d04020481d000c00005040c000411644c65242000e86070300d41002401c0a000c0ba1400300d40c040c1880030590182c4001c5130711080070800b0507540c3c07500041301d41003040282c010070300c0c090380e51241c4003060080090340142e40d40030f58a9a804e100e5020000c4d0403039041503a041c00184560b455280b005d200400140544c844140e450f480d28483c00f131803000c112408500c49070080000c3c4880d842d0030030501908107030315050010345602d940c9001403042108550295111100030055809040a544507012001c04a0140c8440780341c14824081602c80c01e100041c19980614400c00c60300b842982c0b034580082c014548802380e030038 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 133758093 1250 133756843 133756871
    0x1303050d0e0318010203040810050720010504030e010206040c17011103010b030108071a12061c0311160602060c1b0d030b030c0409020f091017010506030609070b1804 73
    0x4040d092005182d480024411070000100c2c8600301c220034241300540c079103814040302c140c640e000004410905170700c03503001c506c4080c00b0341c0004c0d44a03000e10300c007034231501c910341d14441c0602000c0e00c050380403403000d1031031964951020a00c00e1080341c1000c003e1801c00e207003400c00700309150003500c02c120030356a03010008040c0150703000a50082540207003050702c03541001c08040c01c00007190f0000d0b805019001c2901d110a4403101a2004108000c002c2440381e620700000c036a600741650600d044200c065602d0380e08154012105004102d0040100c0342c90317110b0f40d0080580d07022180502001743e44100c00180325000d400c0b00030000d0742886103082043e1103201c5001480c00a50014a00c00b01e41c07550800c2e0803e00f0100700d000d141100032602408200796a401080d1000711515145000310b45950000e40396a102034448001881006183c454400f5009801e42c002d08054032810703c68083c09001c140d5075200000e624068441584041c0c1c0340485400d1181310701d040c042302280e0081e4940c60b40c115100c0d = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 133759343 1250 133758093 133758101
    0x10e04020f0d060e060121050402010504171509010203070c080708070b09151f050103091a0117070f0518040606120605040b090f101802040f060512010902091303050d 73
    0x14800b4800401c0311800e00024074241c42008010030b04024a400c525201c404065a514540030f0010034000350b41c1d180d030700040b14948143e412944401c11514000c00180e000019006e00700e0000c52050402034440d1425503083c0d1109407050000a804082842c01007201c1d00014034449100b50260381c5466129038071482001c100f19882d020070f81100f1440446450984e44a91388440c03203c2d1144c4840d200394404070b90310002d5001c0c242c10107568020113000c1041810212049003030b034281c45a4a90303502c030176280d50441d590641d8400ca0040b80000036240c80046014400d5a50061000304008200c4103151300d58480100140d41c11500c40707500040b400709558040c41424001c28001c211403501e410030f807090100240807050190300c0803803603002d60741e0085074000320500486001b1171010f4400d20320610802c00000e010303502a150140101e0160130395484802215800d9403070b03544503290110641c0c204c0341c00c0c0801940102582c1c0c0040e030400354140507000e0340c5e4843d040c4141480180c40d032a00441d = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 133760593 1250 133759343 133759357
    0xa0507051501051003020a1b0f1a07090b0306030601050f0a151214060f040519020c030d1103011202040203130b0a090c0f23060c0313091404050c010e04020f 69
    0xc0c1c040314018807140c107000034040099051030400350300c0c1c405201401011030f4052008000d400300c40890003010405c84540540250790000c007905010300111100300010001030f504030002c1008030800046041e030703000c207881c03044100401a180503880c0c181801014909aa4600e5102604e80404501c3d07154450348440a05416034500e4030140a94055108598a1160002c2843c0c1c441d01082030560f1482c0349406088010340f00812182c84107003e8502400300641c2d02d4590b503001182c1c100f900c80700000030741302030380e00e91600f480603000c040408541e520007030103107842c034048140300c0c4805170419400458014010302c0d007498001d10f2549940003001720540d100861146c85454220a101001008102415000c000000c24500d00403602140c0c0e5040078400207e0034a8000c01c150aa039500d003034508034080d06081c0d0340e407001e20704501c014020450140c00b411610b4000744414001c40c3c440d000348541d40c030000421f1034200c92001521042c5117498003c1d07009400b003018190344c16108004d0206 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 133761843 1250 133760593 133760623
    0xf140105011a030f04031d120c030709060806040305090d02131406040e0d0c020d08120109050a1503060213091505010806030604030e100c0206120f24060a050705 71
    0x3241d41090316603180c400301841040b0040c007042c42404200040915526042541410282d16600e60b4051025044070355006460b4480c80c111501d103030001000c55401d080003030403429500d41c0c51300c582c03034401162070a00a045840d40f1100c0000e000900a0000301050100100480302030324083e40080c1441801007490f100e51510303210b00e8584444d41c00e80c05c6411003812541401403121220000355500112400c4100300320313140c1d0050041d900e03907d00a9041c1b41e0015400d030b68410304100420f02e06002807040100d224a01340020f640980140714489542244002d114040e52540d00e80714013039048881041c8062100c0356001440c0861442550081949511426861403500b00054000035000f49040d02079004101088006588a140340800d454221041e40540b0401a0700f101e02030341e03036440207400100010b20300c800103022200052284145001c0700140d5030b00c00002c581c03a08050b00c0c1d00e62030380c01110006036061401d0700142201035200d240880c00c11a03035480711440e240c03580801310f00d = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 133763093 1250 133761843 133761851
    0x90f23070605071407060e0f0406091409070602011a040207030302120702100e03120f0903120405150612100b030c15040302030717030403110f030312070801080d08130f1401 76
    0x410021078407400301c00303107504c0710141241d60700d0040702420443d09200c42521600400303e4440f080c1d44d03683c4c001c0000c0e10215604101040c8035445a1120300019a90780220780300325036001681a1050103400403400c0d420031003e98501560f400d110280d041401c0031410700d5000e010000c41070510000c4039115414a600400510002d1001c000485c0c0c1d4124a8407410340081000a40b20540c040d074460708a0340ba0078003050259034013a5018114000c05002020f000700744010300050080006404007440d20304d90003c55542c680c00c003002194040503882008542100700c0714440305009901c81e1042290107002c3d1340c40650010300090441d0b0280140907107030f0901140500c1981404c0014401415454002d544043c2803142019528051403200600740490ac501000480d01c40c0000742c0c0e0040406001c8a40300c1c0b8140301c45a4064400f03c0701c51001030030300303000002c100d1400600e840821034207071500440e40d1102c0e0f1840400d000611025201050b0801504001a84030141030881c0206040001 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 133764343 1250 133763093 133763107
    0xd090209130b0106030209030c0d02030f031b1b010206040f0c12050102190e1e01030902060304060903030c020102030c0a110708070602030406091508070c0309050a08010207031101090f23070605 85
    0x141c00400c1a00410101751050001082d035403070004444c01001c8044a400e003070000580300182c40e10071402c5281006010115030105550f4020a2510800c00320b1801c0d034040c280d640070307410385d5070480c84289401a44002c0108001c598406800100240206034802c14070761140c40148410050380c00440d40d60303600107003032400443c0080d07203541c2c4921145000020155100d0001d1000820104001c402654a802100c05a8029070181030415805050700c0d4683ca0241015001098078440a81c0868101056901002d106108503841200005001c85c107048181d03400710384154402030300c00003e2140c084082580c2e00c0800ca013034024030040e80110340d1b0310f0401600a0019800303512070700c6806440d040d00205250000b5010b5441841440e00d03080644050800b140c0a080a81c031a94100c144c01601242400064000b0b001071406619018110003409072038a08980c1003070f501800100f030503904c02c4002440d0760308118207007440221448501b504809450b0070040e06902240125100080034 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 133765593 1250 133764343 133764353
    0xb070201031a030a020603090c0a060306080c090f0c070312021201050a0b1303031b0f03020606100801080a0b090a1209152102030a020c03070b04030923060d09020913 73
    0xc1c00c40d64038442c4507100310b040c1801003544c03940d110000034841d9030003100040908004120798140b4500003481c031003130300341d8554024000b807199008403001400b0303650503035025040c070303a61142c0105d4401203089525520310040c45100e4108240c00c03070400030300302c3c41d4070410203050000d0141d00b00120440804c651605080140c1c52640341d20042888c01c05000c007455200708075841c9821650075007001982e00000003070186450a180100a01c01c2641e40300a10906a00003800c52082005441646071001003079410381c0e40c4a0244943c0c002c82d84481880d400141c541e05c803840d005002c06040782d40e400c6269036034141070591030141c080051050402006181c0b04401c5044880380d43c2d01381186111005004000c101c8441c0d4040594190000041480e806203641160542460035060b20348030015803500200f821400e0702c0a800284442c00040761041106851803004809910f1181c010008031080c00401d40091028111450f660000d074405030b203802c03900702c1c4a212144803644070a4620728107 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 133766843 1250 133765593 133765601
    0xb060a060f0807030b120f010c11010204050a050d020102030909040803060102070608090a0b090f01020703031407090b040e0a0914010903140a020726070f0303030b030a0213090204060f0b07020103 86
    0x8001c0100101264584541103080d00b908240b031460003040c0346404001040d0000e455980468903840b810103659000c83d01944218544c0d0200d9440f09030782c0903900d030360500b40d0180d03005190b4081d40b241e10401003403500300140404035106005a0341068240380000714948002c0f501a44c080e040042000010740c2d040c08010058042030409280c01c0c204030b00000e0b99003140d02c0c0c0013031007940a000805c1070000c0400001c06920880030080d907a455451400501602208510b040e1032401c04011a034468000ca87c1072042e02c001c92116406d041c80e0804280044c2c1002d80490b00181e6038503070003404240c0c100d070951000305001c0c0000c11054610300e00207154400000040e9034100703003403010700380b10341d804241e40c4202c401080002030400000d840c2c13503400c40c251311a03001462103130b48400030381030440c1200e4400302c0303010b52010000300e10341a050540b6042c44040096214401410100c00b0304040d9014141842c00078000181d103c2d1900240c0051151039041040c0100c00070841804541e41402 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 133768093 1250 133766843 133766849
    0x5042c0c041806030c0b03090f011e11090102060403181a04150801050a0b0a11010207050a051c0801050d03031409061005120d0311070b1e070e010806040c0507020a030b060a 76
    0x4009003451358403581e168040340d014440b2401c80010100718140307000c11241d4001c282c508020840c01c03592054401c800d5149503d2810014101070a08020303e038600c080d00d801e07071070680140020f0f9996a4048645040000300d600041407200700c00701d00210920203092a0100510710696542c3c1802c130300006003081c0050880c10031002d50700602464440030510310440d41550401038071485a6441034807462280d05540300c0962011640d4070920500084d103021030b60080c8165500040c040c40c0040504400610140204141400401c10b0341005141c078000640a440c1c0090405440a2403c0710150141c641c4e041940c441414400300562148065000342003c03143c4100c0c4854140c1c1180d1901c4501e0300b4001450340d10101403050440410480b00700990010440e082d0b49028403000b104040ca02d4881c410802c006000200590300444071020b0b8400140c468000a642c0c0204200180520842c2402044000e00c00c00d0016102e071000100075612580c2c22680c0c5141c508188640741d100381e4 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 133769343 1250 133768093 133768139
    0xa0e03010c0c020907170405011401080303090703110f040509060612070e0112020409020a090501140604030317040201021c020f0c0906090c250b07120b0105042c0c04 73
    0x40141e02016030070a20102802d0f605a40e11401a9030307400083e6150480b142c0c46010031030030242004100f02040d4020f01d0300183d0301a8490f16a620340310400d82d03030700045a04005c42e074416042800802c405160305078070200300404480c5800b8800c000f03d800d84409440c10f823070980c0004103001042c640310034810340da900d044000340015881c2c56621403181d00184503480d0410016100002591169000200e442d50054040500c2666901c00b09004240911503d011031701d2000c803407181c41c5440b00487e07044a0309903450418910070320750a01d906032000f40c803c9040d40b080e56403c1020b1101191255034851140d009041d40b036101c884142d0602d1503150019204040318010403003d665070043c00f070740140c000428141c80b101142d000e180390a02e401d180c42243c015841c61941000360516155209448030380d41c5448040c4a031040c041034030f11500405010a105000a00c01c401e0f2128480904504118802c610000c043c5100038044500f0386582c6041ba10002c3c052041c0180b51b07140300c03064000c107 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 133770593 1250 133769343 133769351
    0x10203090d0303020d06080a0807121706060d0e250f150c050c0301020313140a020a12111c12020610030303240e06130908160201140d020a0e0301 64
    0x800100491401c0700000d0500d680420325000264503035000d2000f400504084400b03440341030a01004a03004000100c541006040426200c0c600c9140c00e11602d1f0380c0030945586c1a00c1d02e84c100141030308140201200d295460203002c140900820143c482c1e40210360b80744984141c0341c0c4041c00c07980c00c503400c401c64440d80c14908100103100300c0c41c0c1c6c48241d107a0340782240500215141140c00c0002907400b039945580044140308448803038171034980c05240706484c44540c458403000712988905058001a60100c800c134010020075401039a180c1140740700e04241c00e038405040740000c0040d5440d494100b640225000054108010300114a00c683c00c1400180341e1031400e00d1a5020b20402404000c0406407104006440c0d04100d00c2e40b1013080e4464030f041d81c0241c0d103418615075114011030b843c034460300a030616242040414400c6000d501e0f08200c0c80b502e441d000301c040a50496080c01c0807030410011840c207110540350343c8060954084110800350b40c65903a240c00902585500f00e003903200b6450 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 133771843 1250 133770593 133770607
    0x20408010c0c021305100b070b180c011d0f03070909050c1e060f2a010c030903020a0f021f05070302100b090a091104061e290f07170a080105010203 65
    0xc0c0284c3c61080307007800c507008030316942d07210444046011940c1c000f81c40380401080200401c1000124a80b080c07100d43c1e502071041460720030503a900c0c20510312042c081844507510000f0200e014920b12590003000d00324100301c060001c0424a40a5940e000c450704c01c0c2e690a0003010003806001c01102c200c0c2c00c66510111000d0051600080100c3c0c07540d103480b03450300044003400900741c10160340c10f904c0b81030300403c18281224903c00480d20502000c000351351a05600c1c0c100180a44180d0304029003541c014a01d01005a50b40942c8081903481641d000702c001001500641d01040c9446001001d65145500c1d01c50030701d80a440c046c010403021403903074200507000c03540791161070a095200c04400d5010a40e10340905085c4801c1c3d1940400e04c1c4c0240c02c03c0ba003c80c01000d1920704403440c03010300c423003910342a594a20004000c8040405038140150700c1036250070a0b0310110103032000c0d80785410114a428040e9684041c0301207009920428001c01042c9652030f5a04462941d00421007800a0740ca0942c0b = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 133773093 1250 133771843 133771849
    0x20309030a05160f03030e060a0606050406030f0204090606020a0b01080303040308040209060f10050403031713080c1c03050103050607030e0d030e07150c050d14071e020d06020408010c0c02 83
    0x354034500340402c000850401604600d21030080c60b0540c0000041040c10308504008010380f4448500040511500c0d0100765560700314802d400480d422681e40d2824076061100c110080c1c0309503543c50341c10540920012a003050648201c00c0200324075002024107680030700e040c0c0c0844030140d01c000195081442000042904088916485075040780c000103a42e403040c0000d11040300c940c503e103401c1601e0004e403054442d000170040040e24001e0b1640050450b6900b01580d0b8041d04447c84401507910404000c00504200040d0814150710025641c0c495400030386100d044210b41d0300b41000030384130300040050100500c48260803e0413454248800c413203004501c3e907900b01c0f02d0340c400101a920920080c0d1300d5010700c2500c020b0017581c00c00d00c0000e03c8100d0018410450030b0010f6400e801a41c0b0403500b10b034004c0844541440303c3d920300031708040705030b1501c1540110340344415000030305003407903c801669645000c0350302c140301d4800140c445040904003801c4415400c00941800310018160015035 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 133774343 1250 133773093 133773097
    0x81009060506090d06020c01051512071d090a080f0a0e0105070209010302130b130f0e06040507090c0504090e0a0c08071202060f091011010c05190807180303081902030903 75
    0xb0f80688036440c4800c203914180e8000e1182c07280c0d00c1c54035460282401600e04000810100340e40003180c2c031115074103581307042507221036071885241c40c02c3d24501603413000e0b46040d10301a98041c045100340c44419150b038542c4082a404030175162200d00700080e080c0c0035035070007a00052041e942171030020700b8011076501084018006003c06031042c980f4283c01d01c17510965411178140e0790009444100c2000c02c0c0d0f55190f02130515a0392280c101401e19003241441c000008400f8800c6030040002c1c03441c2440c2019a600600401450208105c801c00c0085001c550501415600540307020091140702014100b1015a41894201030010740124101704003111924908550031501110055a2000c0a0000c480244152030701550000880c9020889982d040004c0d10304440000e00244000740f41703a02c00701e1f1640b00c3c88402c03003211905d00400d008528461224240e11080303034107208030203a00f080c484240f030b01c2403540100d0020b20150304001ca1000d40711000a580b041c120340075421802d042c2e003138075264 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 133775593 1250 133774343 133774357
    0x50601020c090f0106122c100e1605180a020c100c0503040507060e0a0501030f09020411190807050a030209030a05030c071e03020315071b1203051303050d1a040c081009060506 77
    0x9100902c11648540c7c001d216074600090b5010017004591050035100761034040301d448601407200c441c1c50025586c20032115042c0800c0b00e42c00c1c90031041d6503046480d4000d4220544a490750b01c201b0b030754030b01c0c5d091039171207000b021041a0300d41d46d4491070f0518007140751000b1741c1c0180041088200c000d4020b07407505408076040d0380c000d0038045020314203c0905002080200c0000c0e5100d403c0400c10030b400684d01c0014030311043d03442000710320070b8030002050714442810b40300840018400c10881260500c04d0b400b038a07040400030159503c5031000c1c0c941a1840d0010717001c2e4481c2d03030002c58003003044517546941600401c202f10269442289141c0019880f03442940504407100c1c0300c00001103185209120300034060610412400b112100c506103a00207100a00b9180042480c01c00419120210401d51101650341940d401345081d61814000000c0e00c140c43c420f00c1c1c01c9400808204030b90f6030364060105c400041c0e559118562500c10400342034520030341c1c070620000f49880750a01c0140c550340122054 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 133776843 1250 133775593 133775651
    0xb01091a0708030a2903030d020c0f010f021803010b06070303090c08030c03070b0112151e020c0a02010e10091e0b0c0607180e0a050601020c090f010612 67
    0x9119180c0959100911544400034880c410003c03c1001c0d000f1168041c216800f01740c0812a0400d410700c4c2c40030958903461605c070b58541d0043c040b920301007650b038000700614030030182178904508030000c3c0380d0b0a6406036400b41c01c55940210b003041c68000450048039010f00110024008000c0e5500441c20a109101c2c000e01019120b00c04441840a4a03030385000800a000860b035880b44040c81444d202c1d00310030b00407114050200000600e845d803041e001000c09421000401c0285240e10303410b001080403250541070322560a4003a0040742040c8050684900780a020340300105d840c1c40014015540900340e14400d01001c101180015801600031087e19001d4184000851440010f1034100a03241e00075440c9150000d141c4400103804140180100c007280c0b203043c00c500458010501080140c040d04c2c254408200000b143c1c510743ea0040e50f085681801540c905410307200108516507400c480340c9040308007490042044030350106602c03408000d040340c100841c209403104000f10010050180c0d007 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 133778093 1250 133776843 133776869
    0x609020103020909090c04060603052701111201050f0409050316050c150a030b03060106051e0706020f0403050609192405190e07030c030b10050301090c080d030b0109 73
    0x108590003a412540c0d1980b00419004103450706407560b543e14a2807a00b464001e03801d1040004800c0d01900945001e900074810f81d02c0b5011340f9005e034a443c60801c8204654540d22402c400001c0c0601c20020001c0c803034403010010496040c03030180158146403035400ca02032403501c920700c4085140481600d00d01003500310034508245050034018a050034984450742e0181040c1c55000c1e1a41d1a01c00401824070b01d501c0a01c00f101c0110101904d072036003445100d010a40030480d100046010298001400049164260803c041511000200e1f004084004c08000300002c0030320902c50300300955607000050b00000d2107450b544190300c03003d40b07200000042552003144c03010030702c1a80700d0b600441c1e6a800d080c02085a46400c2c826001c88445611880d00c0d150b140c85146c4071100341c0440c0850075240c0041085022a180d5600c12248141c01041c0c01802c20140001180b036030303400c1c050071003950702400340c40b4038444c182100306051800642d400c3c4141071401c4c18400781ca98020307150208176286040505 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 133779343 1250 133778093 133778111
    0x30307140405030d0c050f010c090515041802070b0a0204060e040b010201241401020708030a050c030c07030305090411070f02100c080409140718051905030105040f020f030307030c06 80
    0x20224000d03500300c41e516004401c12010010b41c040804008540641c01311900c7c824281503042c00c80d81070081000000d8140c200c14031450030500140e203204811548e055103826611407c0c1010b00b52250b0110100c40e80000d920304c103209175808480e40203016180c013145041d160400141030600c81c074006d0350190340c40b071158002980c002e501c06403a60301c1c06981c00098204800c1807108150607401200e02c0c4c112950301c55052544000364010995011000031440c3c00145801a0b8541c2c11269400c0c0007807004020801ca90081880075100940c402d03103a43e5212034100c8100820384070029180011840c0074403c620220313010f07442510a01d81c06554030752600c3c1d20008110b4004545550144c045030700001c0c00201c1460607800721034040840d510f0003a8548449008891000b051804c08003207c3c01c2c00010700040c50a00c03400103440c449419940d15580c1d8480200b800d440e01100d095940700180703180710080d424040f1440030341c500b00701c0240d8a00b18090b6000b0340980d21855014001c1da41e02c420300 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 133780593 1250 133779343 133779377
    0x41206090f050105070c02040c030216110411070606080705120a03080702101a03010b03060702031e0910020f011104050d0f08070605042a030201091401141b011805030307 75
    0x40705019070818000c3c0003914003540054100001030404a01540c035260f0700600313440c42032080d00c0c0d154261450901d030150060b151903a28210703010550303078841d41d18104c5a0a40302000c0091801c54410500826014a480201c40c00c001c40e5511044c0200a0b80b807504400e20b6000c6000c402c8150b040c180190030340c07a005400c03458400c1c0c0416140b00341d85001c020103030490080e41004a2400220001c0c0400b060b09000d0644076081602c081e03015a1090044007418040011256451031100c1c501c1410114404000344080110701820000f58202c0c0c02000300c490740a00840c401819045052031402d4a1b200200b0300f0f40b5505400a402165a01051740800c048801240c002a40001c030900180c2000c2c2051044090034220804140b201210100701d61582e4000c48011660142c46107400c01c0e2400124020450452500c503040058112800641603440c0029251602c0e1084501c40c511404501c10f50844170401c118441d800204101c7c1e030700040f00002220b52016581c40c000d17020311005480 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 133781843 1250 133780593 133780613
    0x150509060424060f0803070c0b1810030b030d0e0102010b121f09080c0606030607080c07080306060c0105010305010b1815041d060f0a0515010207030b0c0d0519050c04120609 76
    0x1e404502c480718000b17a0f80d0000005090540c0c0242800c1c0162651202e044e1000d1040c45000a485a04081d4000d02442c090130281c21a042d641008581e0441040003c0d0170b243c18111048003280c0c441e03d103c501035034244503490319030780145d50300d03648030084400d084c1c3c1d51420b49407030b00140300c424080d00705200070030740003c640203901210305610741e251038065680b540c0040303a409009105a4000820f5541320b024a240201444440b151801d461626800ea25600040c02d0940040301000742d141b40a00c04d20402d8000d6001c6e80c000030701008110100602040c608540c0c0c04040840340500c444510a0210014000c104860018a0840c020a054403d06c9000108200c60180c0e03001c00141201005c9554400d203003428080000e81d590016600300c44290039401030060b448050b080c000100c0c40c000b00c54008100441a80c2415074562080060716800c072070346004601240c10a035159000d03401066007108410441070b04050a00c901c981c412542d880d0050f24494688248c04144801511 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 133783093 1250 133781843 133781849
    0x5180604020901140f0c060708070f030908120406060e060f0117280b090a0603030c02092e050315071b0f0b01120c0f060504090906020f030415050906042406 69
    0xc138151a09805090701d50f1581140c03100307900c240a030100040c160fa104158940c491b0b0401d498851704a041504110014840c10400715540103082280c5001000f0500815115034030800c00825054105000c410500c0710142c074560182d1000380c3c1600075680c000d405100601070401d810001503039210850380d030780c440400d608403414010201e0046200c3c3d80380c220264220090340c0000301900d440c22080201c1740944009400100c05600c040014038144001d1034001a45043c15014003002c944076941701c40380210751100c48011440208103a050500002d240300343d10bc00314038180d240100c2e01600e11804c8000d0700305204440b400c1c24040040a0a00c450116040b40c2a0031441d80c60740c2034101e0392861000c059415440f41880004d03031070303002c0a40c2d90586a565503036506052034082e15201030484401c0845115401f44008480c0b003801c1000f4600c21070080a10b40c5002420144802c200c5101400040356500190100000301d88400740f21081c1c0808807003100d6a501100340544010045a0 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 133784343 1250 133783093 133783127
    0x4050c0409051020040b0913060f050301050114031203070516030306061106090c01030207020d0b0c0322080f03090c04060b0307110609061812160c05180604020901 72
    0x42590002e00000040390410000c42100400c8111144804840407005110724000048800c020a100040030b20002d05580d14001c0d2082502c0d0740003850f038130140c9644c1e41058100100510040140e4074090042900412500c4016414107c140c0040703a01c0d070040001411100500002107820b40340300b04204d4500d508403040c1400c00c1c41162800501520b19403041000103480c416284451400108d02c15020f50360b4075005000c1c0140240054010b50085d240690740401c074800d1402c003042541c81c4451094820031404c0d907407032622400d5010641c1c208880384030301e40c0400c40c044d000182e03010219520503c0e020b5000e6140d03925441e6035841d0182200c0b00300c4c1c005090500001e240782000700518068611a119100c0402005c401c065640e6011510016a9402301000c038003291401c0c444030000088940035100d030000b6100d00340025500002c07107400c1407250240c0c03074000c2c015400040c10280604030385070040c00350080540007014602801261150b540001d8000f8168001d54894200c002c1e00 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 133785593 1250 133784343 133784351
    0x60f0906030a170d06090b030d0f02121b0601080d02061311060a08150301020c1509011b020609010b040207080702091909060207110a0302011b030201060b0409020a020c010306051804050c04 83
    0x51081034150861000004e401c0d0030b001e8082200c00490141588a00b4060010202000102c504a59400b030304100c0d1f01c02d600038400c442600c011a10020408042a01e80b40b035030628201c01020f01d8100160710403500c50b0440100422000c0c0d003c602c490300200d0040405c4183d12603414800a0900b440300590750000b00001c40b490b200e42c2001e60303e80b00d140d9081c191100b12031746a042c54282e03c111a02030140d6000810403201208004205942014101000040350b6103404403100c60045a15440c9015a101c0001c01a18180900030841d02e554165010b500f0808155241d207218090448024481d103c5900050461038484a074101c02a40c81c0a01b404590380e3307414400d0084d40301000580302c80d20303050148011800c04121010840c0c0e41a9500f0b505140100201c06c912142d083c411070031135488500008400c81c8910240010700303121400103079101c0c42181d010303141001e80c0c001c25050500b0300c4800c10081d43c510260a01f100c1080100c1c0304195114900304d41041c0c0140043c0c0d60040c03030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 133786843 1250 133785593 133785623
    0x4050a030e0303130306090201080105040b180a0e010e0a120212030a0b190b0405130509071208121005040e07060f11011b05071a01050603040303022104050f1005060f0906030a 77
    0x187e040421158000e8a40d0903040c0d0b01c0700144010354043c40c2505800c030422a105134a010090404540c0c02032201200160454840801c603003541c2503070f0101c400c203521041618003400b0381e0320300032205800140004e1401c0b249008480c3d44500005051a0f044e5030b4030301d008900c50710b8000c1c0404e2010340c000b0340c40c0101d580b904980c2c64290072500842c1c0c02586820003000d204800c23441006d00030304001c0005c00200e45413044401015511100459402c0d04c1403080c69a9000e86c0140d041c060300900e942e8520240c01c2c2001c0c00700300c1c2c1c60300e00040455440712408101440d000221240f400c4050325190b00031009420b00d1502515011341e00301003595019103c0415550300001a2103094400c4c10664141e41070350140303200000342801441e9015008001050000703000b9802840c3c0080c10940c14002d4110340011420320900c225020f0792580c0003421401e100f07440501420f41c002c03109100030031090a01201007144091507a41d940c2c01400044082049a0f904012841c80e09500460202c0f291703031 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 133788093 1250 133786843 133786853
    0xf030b010224160504180b0a1a0d0b041407051308071502010e12180f0303070303050703051803031f050d08070c0504020a050909040303020f1809090604050a030e03031303 75
    0x20203c0b081081849441e644030303091840b50701120f0880d4030900140a107180504801c40091004074490381d032100c1e8240e400111814040b030b00b05050f00c5007240d042e860304c450710b1741c030b1b4241c130100303245644103074500701c6078241408000386d406400a5452a0203620340d4807580040000a82a400586003482048800525400000300c00c4c403d19100754024403945c1c0c1c2c2d4000345030b61850b10705a041110b400a0041ca103581c0d0602180803071031007000300151042ca9250780400d0441e44a01000c0d8002f940340c204000f1001e415000700d9801100d04442070802607d8250640c0e142e02019120b140809840d554061201c40d02d0303a101c90281c54001c1a00000140b28076160b0040c1d842854100d40b281d4910358001110310341407090f47c10b6815030b80c644518000e5006c1c100703d0000001401101816070a02c03085109800c200c011300185080900c010400300d03003003010010291002805500d40354006000c0000044010400004060b81420604200c1036003900107415406100040451100c0c811400001d000f = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 133789343 1250 133788093 133788163
    0xc030f0f05150405010e0c090a03020d0308061801271b1e03200a110118060e030a021903030908030705180f0f0f03150c04030c060302030402010f030b0102 68
    0x4950904200201e4141d00f400305890782482a0403201004000145080c4194401880f00c0a40103081210301038403680014980070700e95900ba000604482d04002250800c0440902900d2903d21000c40c60341c0342400b10342000205842c042c00c8000d13a00395070a46800c0c07640041c3c01c1c4e0000ca05110814040c50364004000f58844600d41c14010311100a80b1842400f91080c0301c10401a03440140300c840401001c00e0041d4071a40d03003a8104500000303902591102845004bc1c401c88182d04091190803609210007502c4003000c0390441a001008400300d12500004c1d40b61000c0050480162030001504003903008202550014184800010030000b04590120082903013085044112200c500c24000b0300000c2440c0190b1542c02510003181c0520174a401644440c50081c000c0480321401104100c4d12440f402c1500c0e802d99440740807405008211703c1000d50009000e06127011421480c094000a005d8465803120909155950915a034503900c01d015145030030510a5018000803044000d002000c = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 133790593 1250 133789343 133789351
    0x2030603061e0115020f0106061d0301110a030b120d1e0206070f0311090d0f1106031308130b07030c17040302031005131208100e04150c030f0f05 64
    0x24069000040c450741c00072850500c04182c40314451042d603003018400d0b154070452089601c250710032600e130a0040e95003401950b014141d9541d902501e231900c85110350b507840490014510030b9050040c2c03008621504c400b4ac1d030001c41c891502068880116000c074035040a20031f24040b090040d84a6452101c0d041104104d0808040b1302140d6000d1200100304e03261442600da800000340000046554644a40c002d031820309400340c0050718025000303001400c80700020200f15615602c43c5944003d0100503184a60302079401e4035032074a140390600b55a100c40d040001e0046c101c100214600c0b030b40c0030302c6504245c081c046803c0760b1a60351640b428040c084150500003290003188692080c024004030509460480350b001c0c000340280c0b4000555100942001081d000086807070507510390200b001015003403404a401c0c1c4503910301d41040ca10f0300b000c41106800c80f868044018060000040295000890500710140000748181c4145800ca02034500d0a501c1040c0c9420030b48442121444d55002c00c2c05 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 133791843 1250 133790593 133790599
    0x90f03030403110114070308240a0609090c050408030d0e03040302040914010e0c0d0201050c010b092401140a030207020f0a090605032a19091a01110a050c0402091201050a020306 78
    0x40c40b05c0c4108881550321481e00001c1c0000c00e09030118824500ea00404904070310806281060700c60760a01260100489500c0f60001031000c02003007013000080e100e1511003940c2c5280c01031507c2e0074601426030341e11690b41c0842038141d4844007540030340018816900591b900074801e102e0a0340c6410440c3c0c5804107034041e15203c0d4a00100c01c00c1e080c100060601c10084060003461068900b030300190b0341c80d0405440c8803400e54949081d40c550b40d907510780c03462241d5640d003505c8141d140d4580d1580a80d400c0c0054aa0600c50060445420f4501c95410303900322442c1e910300981e41e940c10f403001c16001e04560b030015410880c1c102e004507843d80c650f080802624429401c585a04070013054103d44005c1e52815262404540c0390320704040c2c2840507106594020456590030559a144980c40c100d03103110508140c02c000b20207528072207681c4050700340300511a1000034003440da0a61a05621003103500309c110320442d4000341d14185500c80210101410720b00350000c102a10701186140003950040710341c544 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 133793093 1250 133791843 133791857
    0x7050a02240103051e1f020d0204080a0b0703091109040302160609060f050405183411060702060c031306020c01061e030c05370315060303050f090f030304031101 71
    0x2840c00e0400c40760f4014286000522603080c02e00400640075006104d403151007902080302d03408c015054002440101910b01c010b00c00550b40e41400d8510300d0703001e0912020035040c1042c684c085561001c00d002d00320001c44118546864a10b024ae03d0412414014840309481c20b200044868220b40c02404460990301d44440a0b0f00455040742c3c0e52090307000f40e81e400f105001e0182100070722401041e40c401008041c106404061118440202c009102a078035045044070000e600d485d03101c003031080d0300c048000040130541007000e00a5100c40c1d00501c9400c80c0c242c08800181d8000c0180424080242c1101c0d086546804400211340030340010f0107000c10401a50350418001c1c01444020402c80350043ea4820b1181c1c24203007000b8440301c0f1646441d50800c1c0101e030003010300c8142c4007128404074900403070030f0000d07156103814036810088440644160346071400800110303030003008989074a802c1851003990380b0b20010004041d2085a08801c3d058480410040200054211000340800702602e03208 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 133794343 1250 133793093 133793113
    0x5010c0e1201060b070809040209030303010f03170a0c020103050402032e060b0405010f080411060d050406050601031a010c020a030b0106021b030a0f02040207020d021203071b030b07050a0224010305 87
    0x10742030380c140340b240c414220410402000440e42d805c0103006801ca002340b01624010180c80020320b9034000307801481c1500410041003040281c0e071101d4611001e1010803e44c1450714401020301700209a0001a06060b15500060300319507042c85010540e801c030128402e41e03529901149202c404d4441c0d169865603141400108e44101604103440459030165074003120300003144021100b901014008a0304900041502186070380c4000140010a000403000035a0340741c84c1c28940700740d41020300302c14141441d10703442403030103c50030307a229003002c400b824510240446480414003070240d40d840030b09461031000011407025800300d040329082c40111842e00407042e843c030070161182e109000060180034140c5101d03006007451f4025250a40c0002c0160404003865000f08860402624802d07541d50070000d8040b080003120b61040f140d10340390700016041c641c1140d881c144281c01c040c14082c180800400e0701c1031458800c210980c0703e10308142c141c0d4a55040d50109142e081004e000448a500400f0b8000c = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 133795593 1250 133794343 133794379
    0x70801050c0304080703050d020301030629130207080d1113061106041101031b180b1905030916081b03011407050309070302030f0a06060b0a091e0305010c0e 69
    0x12405106000d480302e255884070342d82c0d000d03940d0100d41c0c1201440018440c80d8184880303840511700a502a010104806504920302c0d074070414068900803209600d00306e2300c0d400d5200e10300d000100041103200140e44003441d0900c9a01340c0212110b40c000360f420201d805845070180f4010b043c035002c5c1c114070102c0203030b01c0b64415a4556030364054415941e2000c400034000c10082d4001188900060500203200c26448290030706420708021418040380d2801d901c805081140e113051785c020281150100d0406500c6c100c51206c50b10403640c14030402001001044210805001c074004101400400c01c414035030300e95415864540b0000801c96411040c100d040860506000f01001807d011036099160f503a1200103581c0b07174101400f0450320384124140800142c50030002d141d4108481001003c8a080328540710065a02c1500030700c034480c5082c4522400182c0008203001654010036154151010340314811000685c1c6900142a0358204440b0740141c58000c4004004400207461090600e104e41c000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 133796843 1250 133795593 133795601
    0x601020a150c0c0f0303050907060e0d060e010617010e010b0402160204150801020f09040c0c05030313031707120b0616080d2a09060e090609091204060e03070801 71
    0x9411404010a001c044030107941c030000105a443c10440d07280601901c502d000040c0c02c61007100469940e0043c81840801086a08001d0480e482c0a0f040c1c4a2800007080c00c001461400a10207138a80c440c0450952003074101c04080c1440ba49002e081d000050495030181000070440c2d00107501e000345400355400c00c0e000310707240d1035a012079110750001c29a080c84018540301501350708001c00e034000442c6100080c001803061a40b4000f1041d1a07010240c100710840ea982c104020a0000c0c0c030008000003080802a29071110b000c001442c0d41c400709041c1a204c0300021800950aa41010100000547c121400c480c00c40c80352a02000280400c8003480581e104004025500e014000c04c0440080e500c07100a0080000b003c002180c500140080030a80082d0112424903a042e4640074540b0a544030020320010803052810403540080c01c07010135040ca00c040d0400b4042d0164000051020381c080003070b8031988595080c1260f840e50b9070580100083c0494511511a0061210005204205000e = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 133798093 1250 133796843 133796863
    0x307050403110111010f0c03050c09010f230714010b0901210516090902090a1b030c0c020a0305010b011107080c0f01090801060e190e0706030e03040509040c0905060102 74
    0x150903190a095440d40001610100c224034104695400c00c0d6106410030b018542c0303002d11840d0b0215030048501c0006d0300b9118001d04100740501c00307020348072450ba8000325101c5001101d08003400a101204000c00090802143d104940c1c0e20024880d010004940b40641c2040100c100802c80303402224104455540c0038810210f11104980e040c95020304500e4103000c4491254040741d02c00b0744480159801320f00c8135030040c0d030059a151200001d5051080441758031100d140c00030410340e0380240300c0700c44601c0612360f420109542c2c2c1e10030303000389406261140680c540040100d8825a0b403807030000e01030580d1841c001e000500f00030b1040f4068034002200402d17101014013800c02546a4024803002c94020b402450410a01581c005100042882200d019140000c003c2810703142034240860f034004003d141150700c81c5002c0424540c42e00202d07460064030680c1ca0046040c0c0f200211540c0785000c1c9411003607001074101c0900042050f0025101c04440d01c0240502081c0e8a090059071540400a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 133799343 1250 133798093 133798097
    0x180609060411040c120c02070e01080307030e0603040f06090f020306090706030606020a03050304021017010b0a020118021c02040e0f030d0e01020708030411030114090f0f0601050102030403081803030a090315020307 94
    0x1084c0340c0c80700c5c03180d500860b0900311248100c801003942e07460703403d41c60756080e4000401c6410018080045c564082d0266403843c0065410525509143c0d8555044252240004c0e1501d075403100c1d10070801c10018a4803201c650010308889190508020042e00c4074402d10808000ca40780002c0041c030313140003182c1110116015202c0c1ca055aa5980a0102ca22601c180000c1001000100d403501d412a00101c1e501030003c040400b0b840340c00d8020081d003114004001e170a00c410142c481080180d0320000700d60000381d03c0d0301c0d501d8034503c110302c0403070041c0600e51000401401400001c400381d50b4000040d001b003030200c0b0f9050040a480707001c1c0e2350807482000b03405007040c0010000180443c03001035411007400c40280001410b00219504002520310507141601103406c00c0d00721500140d0208000c0d0031181502d00540102e5140c1070010759a40b107144402015041e020540740041403008030429000280903054070303175654252800501600d4a4001110070407044052541304504a100b501c3c4214099 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 133800593 1250 133799343 133799357
    0x30307180f180f020403080316030b150a03110c0d08010f0308030c0a1215090f0b0303030a0f090c0b0a1709060403120e010f0506181e180609060411040c 67
    0x800748a1400b441150076220315200d441407006a041ca200600007940200392994607424003034480385500550220502c20181080d101d1981c9aa0703180c120300049151000c02c81d82c45840c0d030b10030b402410202640850780517000c2480d50380040e001c82d08007440a01540e802116a032103130003600f4400d038103010240814000f48002450340082c2001007030245480e042064002003946c40220598101034401d00c60001582810000c01c103180c0240c1240101c0c80300248426540b480110b59a8000241103101a0351107810340320181c082540603100090300809110344581d105c2106000da40c2c007620481c000503204001d426207100d42020150b00880035000617080645981e00c0445540d03c20441c2c1f40041c41d6501c108001d100c0c4c091291784510081c0c080301040c01e1816100700301504001000c411144281081000b440082480020700e001d40c0c2c0840348404c9449640c1440c180b40b004101c280006d224400074406089800542940300b02c6c400c41542103692000380502040d10b189111ba58007103142 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 133801843 1250 133800593 133800599
    0x60e090c0313080c03040602160b0c0c01030f200405010e0306070f08040201050f03090a1101051e030a0b15030a0b0406060e01030e010f090c0305010b0301020a1205041a0405030307180f 81
    0x103090b0410085401600c0740350405030b5040d66107046078010303841103000d0380c010381207801c10440190301c2000400044c41c48078200201240d0003911505864610744c1050350311725a01c0350810b80e9a114000700c1808542c2044844000c00400400782d02c140580b82c042441003c076105540b80c001003039841800c1682e10340c00c401c90741d00c0b4103a5101c00042d000700d06110051000076007408500c006188241c40000c01032509045605040e0707001d103039050750035042110810100d060042180041064280c0030401345a40342d80d2502c0a43c010002a81007651103401e02c440d4541c9205614040c5004443c84801008104410020041200c40318480c600100d801590202c5aa41c0030f1f90114207034032519070000c1809a807014200c2d085480781715085500541c000c07424000d02001f40b10390b501e40b1001350300861401c60896405000c2c802c10f000c43c40e0400361103000117020084c0301090781d0035055206640040368242483c10030389070f40048480a000912100d04510145420f042c2038080396007401c0171030344d244e007 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 133803093 1250 133801843 133801861
    0x30603030d0b1f0c03140c03040b0c0102040b030c030a15050117130b012606010f1703040506030106030207110a030305030711191b0f03020a0e19060b04060e090c03 72
    0x1510020b41e403010a07001035480c6003c80b0800004054180d540d1084c15803824980030701242940945001101424400c00024010001c100c1d03091f91107214075145c07100310403000180a40710f19004643d005001105001c500c905110255009400020007032007141007910326070381030f10382d144103040c0000c00302c020280c115981c1207182c1e5006201c400d0315490200a90326107110042c020fa0091103000c1303081108850541d080296610003825510282c107071540f401010907a994101d008019440b03407525940f040340c590030011036009010141c0740a4480d80e5a44000d0000d40103904203a429514200c01804a07140c00184402541d5060310307028216115404204d88150150041c442c807449042c159401c11034250180c110305510412103d406010707140202142e88516600c20054141e240d401440140e0303c2040401c1502e030142c800d41e885030f5803920510711180e2803011850500d031400d280860b107000f40f03c00502c25030f1450703100c411000c070f43c0c80140b1800800440b160881d0030014804146040703 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 133804343 1250 133803093 133803101
    0xa050906072307080c0a08120c1507020a030f0509010c110307090f020c0712170d0219090e010609180902010207030b0c0c06010b070203031801030e010c0e0301050c030603030d 77
    0x380550b01060480e0035010301000c200d0004640d064540d44268030400c9000d608101c50926088159040c1c42d0303091500c00750a0380c07060310704040d8524040104064650388002c012020300000b06040342052400d100b036001c0e454043c41c0320f05900080805200f140d2080c014411a2402901a5103808030381500da21030900c40003061941f981e15000c1c40c500020f040480d0f000b880b101d125886801640d803003200070854946041580844203101d0f202d12070002081d144008249080c42003008981d80764403071281c0c81c000344141d040006c044032480183c10402039001e1120400e81c0c5602110380c810b81d89a000c2612014a14800c0021140c070350402481c20070000e4000120062041c0101d5004e680c0f00c0e5640e009204041710b1400e081c403c0482c9800c40414100302d00c80c01049d841040a207401309075000302c2d4480c49200424115040d4071401e03d14207034403a5201c0d9401243c250002c00800130504801448411407498943c401d608081c041080c80c003403601164081c4000900030740c903003096041c0d50301c0a0 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 133805593 1250 133804343 133804357
    0xb0d0903020f10060f08063c070206040209070525021c030c0605010906031109060f0306130302010b0f24070f0c030303050906061003090c0305010c0e030f01020a050906 74
    0x5004114528082d0001040031070020f1284140204450b802c0a80f135184881320365024008643c840c4061107c444140d64a581080c441c004c505181d61040898505002580740c2410170a0514041040845540400d0320760003144200c071030a14070340341c081c0704460b1400f41051100d40a43c15000310450b030440140e4040e101c510150010f00c0c59001c400c0c0101035682140000e40129104031480d404010013407060034050a8003120400c00039085841d040300d060044a15923002c3c01e1880c000c10b42c640e5a1140e404401c0c0d2000741261101d00e051105c0c8401448805011005582070804d03016039450421484487c4400240c92184008412017030003000b0200701c441c1c080c100c07000300a0700011459075090007650034040c4881d0b150f020707e140b800808803035004100b4400c41e0400e00c240101690b5408050080c40c405103400726101001c0c6c1040c24051485500061a962820384a442c225030800100c00302108118281e80d0368001245c0e40c40d09038840c0400704c3d400074504025544c02490410054604 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 133806843 1250 133805593 133805597
    0x15050f0f030a0515071202180904020d050607031d060609060405041a13030f020307020108041103030d0e010605180108070303120b060a020604060c030207080403020d030e030a0b070206060a0b0d0903 87
    0xb020b0015100c060030820040099111951030008105070349402c6089080c1090150000314503016815845c4c216902e180f00385a8800d6000c0d03800301e415955540070008030103410070240e501900300120060003c1c0940290700000800d5200d050300ca840c0c010803038607c981400f601d080001d13603900080000500f0300610440d001140c44091b0f070b00320211003c8440c070400f00b41d0386161041a03d070802038a00b800e080440000c650040002c40c00603613002c100a504150711242488031410070b040004d00790b004001d029250035103801584540c0d9101508800b04944042d60742d18005080074017042c410640901580949502c0740e4070420020344a032004c0b000e40250140001807241100000a4031a032050141d1001a4401002e00051110601c65a00c1c10b003446c1c00d00f180380020320340d50091580205e1202a100e05603414105051500500c02c200c0d0611005064075404a664541001c02d80b40c1a940b10006101c1c2d41c8c0066083d04008603894180c0d035101c50100c4c20641450380900c0502010f01c000ca00f = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 133808093 1250 133806843 133806853
    0xd0305160804020409060e0a0c0807090e0316030207150e0906040507020d0e0a18020d050604020a2709050414101e0b0a050a0612111318020f030c0d15050f0f03 70
    0x1807847c0b0030320411210300d01c51a2081890351602070384500d030003040e030041096180f411002c004007a07400401c070ba440880301d090f138065001c0d903403d0036420300d015a070000c01104900c0e000410610390000a24120301d034111512516a21032506120403a00308480380409a408140700c800300d50701952100d41c00300380c01004020502d454000d030081317006d007104c4598101c540125403e42226411f01645600541c244c808604040707803100024175010207800802e23078030322011000c2e60070002413045c00c1c0d014000101043c0110705180c40c2c000c50100180e070600710b00c0e01801540240c40c0c00e0368004d9960007c546050308411880f0901c004000b080e0204490b54401d000e13010000f0035271030303640c150070050440b40c0b0303a03103003d00c003103020082a5a5081410024094100184006407020b00303098400c0e0360f451800420890121441000240700d00d0f02c000c084002d0200400100d441c1200081204c02c44586051080110240703c020350007409001c0d0507401150840c0c10400c5003401e10110000c0c0c0001001c4071 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 133809343 1250 133808093 133808111
    0xf06020904110703020f0f0304150905090106090302130204061202030c070b09010e0c030606060304030e0d0f06020703030b0f0d02090a020d0e0115050a06080708040204110a020d030516080402040906 87
    0x5000c9502c1c001d45045914000b207a0301c400d05030103116404402001030094401e6902d40c40c00c040c0c0f40d10542c0070b590030b100070340b030019586075114416840180c00e000e001384166584415001e8145d160920049110702130480ea021184c40060090b10200d071038903100c5610031001c0840000294100401500f072442082c01307404040303010354407140d00451a00c000003841040b40c210641c141050110300900a80c801030610101d5200c0c40d084981c00354151400800b1a540c1c40001030302e4600000015164103c8001c40b4420300c07940d68010610180300b920100700d6030b2600005c2c001c4107142a103a00e540b018601c211040907003809901c1c55442503848070018504220b4401035401c1b604001c10721411603550380141030b0b00c0c0400b507179014054003044500400040c0f91400041003402c0040c040070400583e03802050071911a07030069134920860304c04686c0c45030500a40290b95001c0d400d9500c2c0000e0070500410301c0c032400f00c40d00c0500c042e0182c1c1c0b0203c180c2c0e0fa44c0c0900010344200641125002e42e00d102803 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 133810593 1250 133809343 133809349
    0x40810020d1b081b041a03070c170307020c010f05220b0403060603230601060c0807060606021005060103060b09210604150c180302010f0210050901090302011d0a0f060209 75
    0x36010b0b03120315448251190400d20031070f02400210740040da00d000380c10031091005103800c145818800c02c0d4110056900d40d980101110944100c034001401420f100c0030010030107035090301951050010707508940c500c03000c0d4001150b90301d0816081c500801c0d010040380e154803104d0a625206282e60f0341030f503c3c0490340e030807044c9a160b22035401940c00c03550341d00d030510402c2042191865203448402105460315410101181c840b001886280c0900c03501441410400014400755030942d90420702c104400351ba01c4a0207174a51a04400300003e591415001034842c1d8064800c2100f0b03035000ba02814102007242d014850702c0c205080b00c5030110390341c001c10008608030401003184168407401410b80d10b504400030100c260382121100c1014045400c3c880e4017480410b03000c8008498091800700c0114890340404d03400c000306c00310306840d02d608200030000000070541000c0746081c469802042222100b944d6407030142040d20034082c081e085807042c0d801003040c4141c0288024001c3c100103103000300c40800 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 133811843 1250 133810593 133810631
    0x50a0e0706050904140114060d06090c05030414060702030d0209010507060c0c0209131205220311010e030f03040b030606040f0f0608150306011809020406030b0406050c040810020d 79
    0x1801c0014400900c244290405028417049034507001000b10040d410290800d0840c40000c3c0c00034052080814101d541d9506a003001c8000c10400d001088456024100104103500c2200c00b07842d040508500c00d4500d80300050041e2007050241c0c06142092462040780029512160b101410402c3c140840f6020620034825000e0b40f052648074201d84821078070502a000400a14000844510101c1000400e9100030b64002801c0c1b0b61030000e0740d070b4280341201e03409a0900d140701480900014000f1040105800803100c2601c0240c0320107000911800030580e603208803400b10711141c2c0041c4800c0000b100305001842c0c11000080000d410a41c03650041c080c06030040d80522000c0300c503610704210303c3d50000c2d9141c3d0041116802c3d142c18041e0280400e07a101010300c6150442034004402a40c2d52000f54804442c0541c020000e100075640ca00382140c41c10400c4e039040e40e0a82ca81004200c24010403021541228030440180c00d42016001c00030000b134000c0441420000d4640302e0b800c03101d00403020 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 133812949 1106 133811843 133811849
    0x1308210703120612110102190f0b0702070b030903130b190807031805061914040b0615030c1908060d0609080c1f2409050a0e07 56
    0x40700300c00400301980f04d4181400c0441c4c090b41009030040081e40d01d80800d07402c403520340c0c1082441c0781d05c140021000500401c0c148481304006a1844000c652084060040c1c910303c940e290840c00803903000b03c48680a58000203a50241d0714044501300300500240c0002c58240300b015104100e44040b07080c034603414007000c80001055988070740c01c007110180f0b04c1c01100440074cd20340f9010765140c130240c50709140382c000f4078000780c0200050b201d41c0303440e5018054049034588031600d45014098002e40660303084030a1401510b41707901203100440c09440c0842400e1b60305c40b42d1b0f0307880c0b84080d2108000113013040b0142c424820031380d42d0b0104480f0301030381010f8001303240308591800c2a4188503004000142d4040c4520030f400e4045000c24a03100130b078020b1f138240b15600d034500034080b80141c21100c1c0f8445029a44061150706c506600080d4065802d10380043c10308408071209251190b694 = true := by decide +kernel

theorem cover : BRFrame.Cov 133633093 133812949 := by
  have h0 := BRFrame.cov_init 133633093
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 133633093 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 133633093 ≤ n) (h2 : n < 133812949) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
