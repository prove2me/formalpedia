-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0384
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:32:07.292644+00:00
-- url     : https://prove2.me/submissions/7b024d2e-3620-43f0-b721-dfb766dba0a7

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 68884894 ≤ n < 69064750 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 68886144 1250 68884894 68884897
    0x2903010303030515030a030f0f05090301050c040801051e060103020901030f092103140c07020301090209010e010905180c010c02011209050609070b13060c0201050405040903030b0901060e01050708031803 89
    0x31400780c1d4011640d0306080018910300066180d5250103031700884000000302e900900720045040c0b03d440c00f0313441a41040030443c2c43d4018083c5050341942404144241a0304000140c010b07654010300811043d150301d201d4082030211005481405101e880010350698005d9026040100040c1804070310b011405a1138400c8503200502181e0298000440840118a601005d00c0c00c0c100b03420f08000542d005602c1d52441d210040900004201c0050320104640303007900041040c0b50b019011680d15616204030f0303002a0400d0103101e4040b071500e00019072207510303071388510702288184014000c480030183c01101c3c60446010183c0c1400110081c000c0c0c171072654400d0461150245002c1c000a007881c0500b142403c1311a840b03142ca40c501800700707401a4512022820841c0c9150071321009401c030301c2c4016138a90182d0343c0099409031500f000b100c01d25801d41c221465480046031001c100f41c0e21580c1c1500c22407a5250740e036001074010300c405c0b000924105d000b107400410303240d200c420008440003032a20b503 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 68887394 1250 68886144 68886149
    0x708040b0619080d0f0e010c060e0c04020703020604120905010909021b24100518090f01090305041d0702100c020106090e01020a09060504080c0f01111c020c061201290301 75
    0x2942c0c08007100e01c544c1070b4400785402400d21a0f01d0138541e0f03c8408030000f0000b03159010087c003030325500d114001170500b003001000c0844401070415500c54070f560170065141c03041210240c546d0982c0c200b5105c00d25100745010f0080d00e805071075006059080c0540c80d0002e4100c00401040000301c0ba071000380400081050f0200486c101032003d00902c20001ea000340300d48003406a00750f842d002c0707500b440b4903a1903000500c8854540c02e96545c41d0fa443c1140c65103000360f0540c46403115442c00081d042031603488001401070742d91958070b803094510344641c080f0891008403036410058000c2004900705150b02d40154400c0011440085200c0c0c1cac503504580102c40114008868a0f980001c4401c44c02e03402843d001c0003040181852818285888a080c0e00c03007912000003840303001c1e007500022882e8051003440001034041c81c220744403408000e140514401c00300341c5190142c8142182d82c4001d1400754221422041e942c4d00408030390340380c42c0704400c4410801812103c8003a9040c0262034004014015600 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 68888644 1250 68887394 68887409
    0x3010509030406030c0302040b04150203040e040b011502030903100209010e1534122606090c07030207050d020102030c0d05030a050112020f13060f0906051201050708040b0619 77
    0xb6118a4103102034204e400ca01415014180180000c100c07088a140c04d84044886c1c10300040c1049048a10072411480380da000000a02c006d01d041c0401e2001092055041e607014044101ca80401030400303907a60701039521440e07419030110407006c4a0544c15009000d4951060501612080c104070001d03000c40300451000a8403140440d807001c1610000c900c10034a001034004180141c02c1e00c0c8151401101a01c60142c030689000325800340c0b03030388a0208030307880141e442002d8200200403150509402001e03500d01c0d02c200218004114042501c3c021148034036819002003041504d08000d000c403c070785001c802d905601050085d00c242510901c03214038648215604c85540f403502e8900241141d030f068201280e01b036520705840005885c1c206400c42e00c2c0100311580408110a0389d2032001800082c3c1000003804000480040c0548803900318006881c41200c03250001845414203600f00d0788101c2d02d110014407003802146c0401c0c00d41d5641c03074001e54050b1050001c0100c0c201c0120301c8400542c040310 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 68889894 1250 68888644 68888647
    0x150403050c12070503101b030e0a0602070c0509040807030f0201020306060d051b12090111120705030604060302150a170c07080d1506090e060a0b0d0b0d02030a03020106030b090105060d030e0d020301050903 90
    0x80704440b403080c5401007a00707e820104480b0410304c50550f62650080d0000b820f1582c000b42960600038010151002090b00030210343d528070742840c11818a0b000350314102c01040d00328144000640c01030007520f1068101070030351414080038407980000f4210140040c04880c00418501034902d00e00001440f103a8051459840305051280b402c608548004612866002090251810b20050105002e400c190b40c1d01d00f441e12030b2200b40001d030040049501c000d40c0a100c801005201e90072441c05032194501503294003003074007065440e00c10894012036034000045006c024184c0003412042c091305d4440001030f07002a2040055814042c00640c030381280c40800c0f4885800c11040f1100310003d540440d09031072864503245030070070042c000d0094011864006803a00f509941907211962000d2219400034201c43c8511800e04010303008100ca40070070ba9118186038001110f45205008940c00341402508541c001d446c82c0d10b003112034018148099602254807003443c0b000d83c1c3d0900690340102580009513 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 68891144 1250 68889894 68889911
    0x1b050307120239070e04120e100306081009050a08070f140601180b010c0b09100f060626070c0305040803030a1a10021510030b0a0209150403050c1207050310 69
    0x820b903000c03d401291800358002c8105104152182003440d81041d403143c1080d011000a07182503801060a628050f004081d060140941940c103801010032180c034841076606140f142c0300c2c0c403010344001c00405401c0ea03109220b26000240000001c0c4203241c0120311284441420760b958004035590710642456030381c440d00050092803c240725194080086d000c08120584241c000a840d001040300041d14100c5860001522304d141406000e0180c80412401c021416444441d44000c004501030304001030341520100b20b01520418140030200c1c540031041d401c07660b070031404859941c01d50100702d041100030310000803e07100400145015084c2c03404041035800303c02480c902c134255500c010a204103046007000b10341c15000326021052082e001100d04a95071000702c403011032003080d44003c01c00f1500c4010041011030950240c0300403a41141c4102d410103003041003424501550001910076004071134001100c2c6082d5000d10880c00f4108113a44e0429500d00009007010340740314000320542c0d02c4983c003 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 68892394 1250 68891144 68891227
    0x6080d0207140105030621070803160506010501080c030c0c030f1908061c030c0204021201030f0507050603011503050a06090614012007120f0203060c04091b0503071202 74
    0x100b0101c4002840c0a604614080000031040d101e074a160005156070600a5400200240401c101070321100c030449940d01ca0711101e010910b6200701080d603a50003840004902e070340c030030030201c0e00810b020702c801c50441d100c4049010305e56100040c00545884104007410070704e0b0000014010004c10071510a00c0c0c142402d001a048807070082c20a849818407012406042000d0540f07601e00a4051500414036060b902c0814000d00ca140140c6090042290001041200e010241126284140265000b8580e50700601c000c9001c28050052a05031008048103194071076071080354022680c002c0801c80980c1d034403124007110919044400582c1203000300e1a0156008038800d800e481c0d240052020801106241a0b150152409032021062056110500b40410121010700c2181c0040a0300c079241809001003c030369000b445070000c00c42c106010300d0f9100300302a402d00640040d9480f03240c0756582d1544111400b101d08010440d18640c00d10080d002030210114203104299200c52070502041c04012 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 68893644 1250 68892394 68892419
    0xb030717010c090b0f090109030c1203020d1d04091a040506101d010603022115010f0e0d0803060a0b030c04050a080d0c0303200c0a03030608010b0d0b0a06080d0207 72
    0x12980248056810304204c84c42c1d24030121041890070710145512003c0200040b90001714660000d0010b0040d10004075820f03000d070700581c0d03003144a03800b100c0468888003800e407080a00080c03035240f1805003403204006070a1503002003881a1041c4a07118070030080f101c90022020068505849907442542000300440c820902c400180c09010344045550302c040b642150a824140a02020140c001c980500c0702d604d010a0369000e00c6007a2116045880c11041c40560b9501c0c0e01203444c0080e140d01d8840c001c50f070040040c5082100094003181080d21240c0f544c003003d500290640d500240d94500001d103607980103010318018099004207070b44c0c0314900802c2100480070b5070010740c4240c0244800190094002111840750381d85802d011942c4d042051480081d040d02900751340d51820006158030302a44d0104000640d01d105c1c0e01d0400c131040c3c540351100d088a15400003941c2110a60070540c0100d500b034048030340d00c010014404506c803504c944c00c060914204484c0540942d00040d03051007443d03034001 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 68894894 1250 68893644 68893661
    0x90906090f0605010f0506161704030c060f03050601170f060105090307080105060906060a020d0e030109060c0302030403080108030a12051008070b0a120b010c0602071103010c0507060f050c07030807030b03071701 93
    0x681c11400c110075111485556842c455005045184089c00b445400080d80261802540c11150b0580010350340d0720054081c42040d00c011000a00c0e00700003407a10743c060101c1025401c00403100025581e903000d118458810041c0001d03040c80400d12001031540d60412400014042c16030012038141007032030900c0070114010f00b80d82d10842d02030084100440d400203907440d0b01070080c41c1c28072000090402007030040c000050090800c5040100701100346805400650040d0310035958001560303a1560056103c1c05001440000501090710300010001507170042d941200c10840036a803074640c4c411040c2d280000c198000e0880b2000422801e0318107400c000080000310b0388031030078800f02d00c14500080c01c038200903030000c0203564049a170005000345400501c207503800140080122105410003c0c009800900f800c407002403c0840b81c0160100c1402002d02900e030000c1002c1c2000c04a94040d200100300904a00c20590349141c481d0965908201510003072801d40c0020406065080d412804c0d14030300b0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 68896144 1250 68894894 68894899
    0x21070309090c050306013c020d031a06091807030b030d090f0e0903070c08010509011a060904051b03040f20100503070e04060902040807080d0801090906090f0605010f05 74
    0x7000514000740c00a00300d95002e4801d1034681500044201d85c0a090020040120142181d42c95200080c04c1840d187d40358062a0f902142e003c44400301045055818030094181078250b2141c0f10545030600c100500941c0c0d00041804504044108a02480f20b40c101ca5460000351a624121503d080070b101c6c20440d414076150252100c0c0c2001c110b00d051101503c80c42d01c1083c1d244d000680c9101050003616803c90b440002500410b544608040c0609070030b503100c50044d483c10941408400e0002549280e10001801c80e41c00c02ea48002004014007005141d6214106030324110303640024200011480b4034448c50303554000b440c0c3c508114a08400030942c054003d01e214042d032466170340f074005988002003103186c0a91740341c0c0c907884102c41c1c540d400c6010503081801d06502140150180e00070700309840c016400c5070b445903541c42010342d481204440080110304030400600c841012034102c84c409502484000c0340d0035480395241c074842d42c0034000170b80742c03141c2d03503001840700e016010002002000e08 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 68897394 1250 68896144 68896151
    0x51903050706080c0910020f100c0e0904050109050f1f0506010206060409080d06120203011406060a0f020c0901060e0f0102030f0a2307080310050103060b0405010c02032107030909 79
    0x4540e596603550440b8024207042c00741aa001545920300001102d250320405060801291106a40a5955642010210b540340211510442d1078140c0384540032001125550710400040b000d01803100c9401c3c0603105071825504c82c00c0032404030744100609042d03034241000620410051203c0b80c0c100d4544014503084013070512084c8401d03681c1c00649a0f07000742d003c0381c002521901e6498500c80d03034130500aa60941d80c9c01d110380002c3c5d1043c00080350321114029802030128125220f50750304201d00440e00315520000030b205192001c0e10074480d44207802041e00480f41900318000015805400c240d12500028003420403885043c100800c40914005080c002141411210841d0342d101d80640c0c940719080244003c20364000790714491486001000001080c0e540300058100400c0c00d5100f02e8500c20034801303944000030103501c24450344040340d080c0c40340c407410b00d801d1400454003141d9540040c1da05124580a070101d040c500c5408031001c1400e441c4180d0307034081c0b070300c0c01a0944070b43d031b81708908240c0ba = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 68898644 1250 68897394 68897399
    0x1020705090a0b0d02270606040501090308031815010302030d0903050601120c0302090906090610030f030c050309040c050903071a041e120501060f080a02010c080906070515010519 79
    0x1107000e10a0b4114203940700101d2480120000b00f510302102004c06540071030f403c0c080c80c5880288644001c100d20900008010366a02d0b0320a02c00b003880b5a1240c1c90011f10340c4601000445e00c104003846d000030007c1300384041102441c0d40113240c01d001c0084040414a82c1004004500d010407044a800400e414040ca034a440c6884940d2581320510801400c03a10034101281085100c1d40041c0103152300600c900e07924200b944000b5070b183c40c210b0380081c9610071003003ca0306441b06502d0102c126944016000d200070301c2c6940c11541c54241000854a51205124a4051340e030395003c0c10000c43e41964034540c03140c1000042520b0000c440d4007514014a41000880665200d4802c541c02d03a010305144400c030080d107000c826007508007a444040e091120b024403504210041d0800001c88415500078020591201089600c1c2c4030703c10310080c00f00e0307400c44a0000042120001d4049444000c064034100b01007515494100601c40e8107400002c0310400040c041880c01c1d501c00708440f000c50004420160 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 68899894 1250 68898644 68898649
    0x50f0408011e1a060a05070203010f14010f1217040905040f0203011113090b0a03021009140a060c0f020a05030304170d02030a0903030302030415110304061d07060804050709090c1401020705 83
    0xb84000c04242c013500c4001142c540350380c0a0002c407000c0302e80c0a0000c11000700c900882a0041c502c201d91700016802000000440a080c40341a200350390a507000c2c0440c844650b511a043d1010088121507210001d2000091a2080f442918030890040d5401c4105107940c0c41010b0031200880c83c150b031038036030a01c060050a0032034003080c5c090304c50b030010002d00510301a00140403185298402544440b50000d40d10101758886950030440c2e0708100c000d02a0000c82003040048500ca00a10001507440da1074940032510303500000841c24000f4000da0002c3d43c0300c1300880d003940d001c1d80144100c00032401212120740c008003c801c40180080c0302550808101040003000ca8119101c040c2c1003580100106081c410b0344d110529190700034130000c1004c010005040d05554208840c1076600314a40a02126900841c003044003c0d101e01c10050800c0d5400c0101c00e03900201c029000792418070690001040e000b03258807800082c18000c02c8001d901c0c0f071502000a1103000182d00310350440d000b0000c10020364 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 68901144 1250 68899894 68899931
    0x609070e0906030f0f030415030603030f0e1305070e030708061e09010e0102030103120305071409150712020c0a080304080601060302180406061116030503120403050f0408011e 77
    0x310086480100e141c07070320800a841c1c00c2c907401101402d4090301180c1005600300000030700855403280869030340c09801c418247c0880348a17210150105040681c0062071500c01d60811b00c0c59140200700d0002121030001c1141107840c00c0380c8031808030341c2c0c490070b40c0400e203020009140140a207000406080c50031032410300c040c9010701305621880041001040b00300d8401e40040144544450003103480c4d6a503801d00d103443d41d60030424440841c0c900404605047d1007510706060320b0000f070f00540d19004a4000784001d4480c0031840035208203081c45078100007441104003a420f00000d50007000c12040c0d22040121b0744002e907120340c1e4a075004110030020800d0104050f0b0454034107003401601c07264560408074101d02d0340980d031548a4600840403882c29004040103039009040000c4840001048182d41890a0b04c1d00028016500034041501200700102c80d060741304c0e129280036030910b10384c445025900d81294001e003660b40d44640000000e0030740d070591022210785654091000b01c40d0000c500011 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 68902394 1250 68901144 68901167
    0x51006050304140613030f0f020d0f120f0501030c080a03120b01140a0f0305070f05040e040f1e060f050f0604093e030c010f2f0a030206060907 63
    0x18050040300040910080c40c040c0d0640070355040540c0c000d41740044900901005c0113104070081200d8040803117065104044116030440346030010800b0003071400050300c1c4190080701000401c000c000c0c40003040700c250f0180e0003000402a8000c181541141b03450a100b0b40360303800c001003039400701c14580082580115080101c9050050014500c0c038588012070304404040791001c8002800940c0400403540312240c0300182d0301c9130f41c0800441d110640202c0304064602640ca000a0b4107010900030441e1961003290040d05c00c411180c041c024603900c410f100340b241e070325241e5107a5292900720140302d1103025100d010542e190003000340d0b04e0202d04035074064501400c0310b4090b95880d8400d1007001264008850100030451401c212200880811458440c1151112184c0121040a11103608000803a103550700016120705080c814441411520421450b651400a010407501071019101401101c1e180d214140d0103416070040a0070007910300140602983d000b02000e104101d410340e0300c25030085a = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 68903644 1250 68902394 68902397
    0x303030403020a110d020a031a0f01120311101e060e0705031602010b090c22080a1b0506070f02030d170c092709060108010203090c1005130f06030f051006 68
    0x1c004e00c1c0d400415552a40424001d4000c440c040f03002c810300c440204150000b81c40c0301401800c60341c0340c11925030080401c1c46001c0d45c2500001146000a00407500241c1c9102c0401c09c5500c21040c100000e02a16400424035401c076a000c20707180d1440c3c5842c050240030f090340030f01d240d070385c1d0401c010b0003070051000910140c0900e0300804001041d5100b0f400442c0c20500080c04007a890511080c4154280c3c0440e06603203034207807480900e00d1070308890011142141c0914000e807000c145a9155081248100c080e0349a000039081d601043c07507641c03100a00007480c0502c0c03842140100340d20500d03103001c16150350791041c44264100040c030790700710381103241d4403048880741c4039211980030000c0b42070340d50640030030031142ca120201081c9040c1d0b8400d00c40d100340400011a09140d80e9414118200d02c02500c00c008280c015070300315010fa05017040001100340c01e40c075190b480d100ca0b0030038001002c4c90380d81040d5201c01a2100400540340c0c140181101101400b00400140c00c000b294513071442d503035109020 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 68904894 1250 68903644 68903663
    0x50405030607050903010f0920090108062205030c0312150d0210050f031821030112020a03020301020d050a0b0f09040209041110020a03030f06081510091a040b0303030403020a 77
    0x91845e01e00b0f4000c44544040c000c1c0a01c038244440ca040c0411695101104025240d81843c002c01440c25200d068120740c4a00041c04103a180c00300b260b140c80e080340c550208255610058000010b404000070701070008098082c40c0c8904502860b1744260401628090000390b9842100080d40d4501030707000c80d03440d8101e41410a840c507658003954203015800c07100003135042c04400c000203481e41c0d4034800211412070040d620740b00400d50140300c0000c54814400180c803010700060003019422004011500d0008050403c55562640080e081ea40081003c44040352580240603003500309005e00f040d00b42049401101505e0000045240f83c04024400307071103104080082810b01104000c0c0c10480074000e0300e82499100c204801a42e504c05070342040380001c1ca0609014841e0700305104880a84001702c01030103400c0d250b26400c0070340c004080c051301b1001820070390010318100ca92040d52014151840e404962040c2d14042000302c600f03800344503010307070400c02c100000a940800c0c06031308280e02c4041392 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 68906144 1250 68904894 68904907
    0x10807080405070503010216060f150b130e090c181303080a0e0a0311060a0204050604030b070e0406080d020606040c090b03100306050a050f090109020a06120b180105090705040503060705 82
    0x649032003c0c43d4802034065100007140c141400761091045031050092209010700711262034040d080701d81101c11101d0000303440800348200243c0d04002c090005144440c032035121740b2109840425103040e02e02046582c45440c40784a6401e000c900c000c07202041c481140c0c20352801b881411004610108000c00b00900305000a958003500c0d4055036000b0300c5a4201c1d20440c0407854003a22200d4168101eaa10703203e010001341007411603008440a64102819030b50400f80ba40e03603040b00409020300100188446145100c54a403a20703c908001800340400034a0f402e00c15031401f0f03091060260405000d581000c601e0341040da08a40e605080300c0209182980c1d81d0f5038030780b00c4040803140d5040140901e0412050142288907a0021801180d04202800070b940b640c624036401c94001c010000e42001051000300718660145031200c94071102040007103004500c1c10001012440c2413910000c0031080440103000600b40750184640c800d01c07030b0424a281c6418880000c1c0e0b200c00080c404001c200d400a800c = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 68907394 1250 68906144 68906153
    0x31207050a0b040b010816080a201816020312130c08010c02062211091801140103060c050304050a020d140d09090c0201020a0801140319200108060108070804 69
    0x15000525040344071480241070516004d0318000c002e22030b2034800d120f001d41401010b12010764003c2120f0034400200038202c540e540c4c050034800020a40d100030030401550024540b540d140c4100c0801d2944250001440c103443e80c00c100012169159045500600882c04081d160185c0a50402202450440b42c0c40c050301c0e00082e42c2d54141c01c0f401c200e5082042805030650005942c40c01008103070705801081030031325440c60740804a0316000e405400c00c81c91340f07200341c14807880c85070b04501008032041c81c0841c020310050075100d5031044840210f45d01030041003801894030440a4a20031440c0a40c03440c1000d844043d0748034003800380030344140d0b5813030450800c0241240c2011401e0701e031481541c079000030b1a40040c100c5483c0380310340000b45041c290712802a92040c402c6403a0300300c1d2503c41c000340340d003001c01e03000250768007440721605445004614030b540b4200305244101e032442207007001c100d900d6110170120800d00d90000035051041d008284949a80c01007495a0700544a1800c150f01d65201d0a0 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 68908644 1250 68907394 68907403
    0x30e0105070c081b19050a120c0b04030807020102130b0c06070e060d020a0e0a0602011a091b0304080706020301180e031204020d0615060c06150803091e131b02060603120705 76
    0x8000341174046101028100003011034405005802105000c101009601c025146c0e4250703404010042d5215000180009005141583d00702500348001414001c10051070507003900d05405c901d102c1800418409000382081105a5200365189008100780342144003080a41c000d451913900e0294004c039580401034455100c1c4c0030701e03c5000b04008007495550801074000c1403040203126014444290521041c109104c219000d1900c00c0c940050200201002009030340010b0000c07503c0e19420088140420605c1c00a50f02800700f030a4075500482404a000080b100440c015985903002405085c00300c4401c1000b80741d03c0b0fa016a400e0098446c01c1c9007070801000c48103003070601d80d4005071000c10000d521031807803e2600d20036038080081445504400f00b152031680301d6020386a004200d40501c50415070305054841c88620101c44400325820001000d40c542c50114001c056925407490007585407002c4101c0c020313007041c00586568281f60003ca5100c0c4901440072500c520300142d901c007004010032 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 68909894 1250 68908644 68908663
    0x402091f02012309101505010e130908030106020610050303040909060f060b0c19050c10020307060c030f06050609010f0503060312070b0609060a1508040819030e0105070c081b 77
    0x3034011400646800308400c00d440550301a003480c85a502c11700740d0074a017840703429190701c044c0481e04016803400b40111841e184c0003241a801001040850310080e00d10701400702101e200f58482912036040c0b8000901c1c084000300621034024030204100301c242c501004030360136201c600030b0200c1c00b00b01c14240400a0f1101c1002c8500c154607114000905000341e4000d440e80055140c280c40349024010a0070b0440158614064070642107070508420a01c0c18080714242c04280d4015241085c0d06034582c1c01c1103d111850b03a4020903190103462220070150722a51001d04000c541040c100b411f000b000901020714050f800c42803000000c00b050709036400300274165811000c080120381c2d800e5180b6061090303100550780c031030064000e04040390032031602a01380015a00d0220400300c9803030f100b041c1152040c130060802c0d60f280008016406189a04001d0800e4980803920045040b00219000703034210b4800502580800c5002c0c41e0f01e80c0003881d08401c0b5441e202030704c0800340c0344c07070702c092507080c00d10000d517 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 68911144 1250 68909894 68909921
    0x3080a021312060509010606030b03100e0c030f060403080109050106021b010212040803040509010f0302150a20031c052a040801021605010c031107140a02091e060402091f0201 77
    0x100707001002c0200036048503105c1d4198100078424155100b5060f000d440800c1c1c0ba0340d40c96080410800160031542e4000d201c482101812680d200003180003013810108822034610312074005d0400c000034503070448034035401000d00007070400040d80741200094482180e00d452501c040a813041c4229168400c0255a00710108224101c1c3d48660300e040300c0355039500c40c3c4104c9006205020000a8098000100104880e0098020103849140d03944c821102e61040c9058070510000d080c66201c0c0d041035691003000d072220300005564810759800e980d034101c905070300781418440c14802005600810b48600181c40165a0103d104840c81c10780034804a000d50b030810900d41d84003080700070b001074450b000d00852a00a0008100d920750210080342a20a00b01595100f110b0400100001588200c0c4940020540c541a24a04080c590004181e45815241c10510000c2e40380c0d51000d07201c0518546800c488101e0707045103041080ca0204e030940d000c2d40c1c000b07910745100d0305040103002d00039080342c81058080c = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 68912394 1250 68911144 68911169
    0x405040c1a0c10060302150d0906020301090e100c1e020a0614041202010c02031213170315010816031509020403032606090411010903060e0a03020d050703080a0213 72
    0x11102069a001540c6015951003021403c1c00014103d20507201580c0d0058400301c0d03d4203d00c440218a503226000f5507006a40d40d0281ca0013094081c07010b103001e01760045012540f003500c071511910701051048410240c0e4681480814096004410081014000908a041900f085000ba07007840012800070b0710b000d0400d02d10403500c24840072424442c5102d024114a60301d0102000c90032549c09041c01c1e805171340208804c1060012400c00c0541c0304c00c0c0c5c03039140b0780c40046036900c074100301c41b071807800020080c00032051241b240000d040e80c0d502c8030801c0ca003400300d51414211503611170192003520814107548031550788950382940303003040142c1711081d0f081d56959564940100714541544440c074154010b84402500600c415142c02d004500c01407010805440c0d40d2500001013101e001210b043c00448040080000c003180941108401e240e4040c01804400d41000390602c601b02c01800d00b001310030403034140061b07080210140c00c44085800103890b5641d424005800710070982024654451 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 68913644 1250 68912394 68912429
    0x1d03070501090201110303010b0d050a0204080a050109030e040e03030a0507112b0f0507030e03030d090c05030c0108010302090f04050a02090c0d1a0604060c050a02040e03040e010803030f060405040c 87
    0x40c150400c508140c801ea8804001150400c2c816499010038007840048071400c00c40081d40351344c250082500300007104001460159946841c2e4176000540c0411a00da03510380c440002496008600c9801805045d1003c4c400c2001e81d08504d512440014402582030340c1d190049804113100c0c0711001d01185000c0200e504000070f20300d154854100000b0740101e442c1f070841444402a01c14000005a0b461a45500382055100d6409032202c55004d56550341600c0144020b45e100141c50145510380c42c0500301814901e420813091500307006200041c00e042c40554401000141c6403c64800d0744408007070940e09050b180d5141c0785007040003944002c2c1d0300c4114842400980d001c114000c0800303148a15080140420750004000c000500b58800e907807002043c001000801d0050f00030a00c414442c03004e4030040d03000c0b58009801c131030644041c60001e510114082c00000040c5520502400c03010b00214110f1a007100c0c1d1055040b0001c2c80c03c0e0080351610046000c0103101200200505031603c0c03018004a03 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 68914894 1250 68913644 68913653
    0xf020c0a030528051e070c05090a140106050a0e030304030503030105130e0a1103010507170c0d0212100608070302071e02010c05060a0e0c0609032e0906020a08010902090906041d0307 80
    0x2c000c50700e02e005d40e000f1001d94056610080080701c0320290312424400c4d15500d010304014250310000c0180c008240c0b204001c0340600340c0396400724080c050039107455480b100040b60040549143d00e005e50700950003044144041030002080d01e0441d48112a80792604603103010b80c1c2d0250500720784011040c0f0a00c41c64104000060750280c800038000e5008105030303aa0440c0c100e03180384058001303100d04041c03130020a50a42d400c03002001c81ea140c00c2405403904a00c240c1e0301c00c490004842204140020703241c24800180d01004181c2c01c01d805140641c1441c40a4032442c03050f07150300704100940d140c014280421640201e840c09041074004041d00c00500d05000c102e03001d019810300d15000c50081c0713088654607150480a031800d000f80a07005080404003003162a0f8503d01c1048080e9000c8850840c410010b4258010500124401c0c440543c03501542d04000e0003580c01a048541e500d0f005010840341900c9207003050f03a1181c0100c4020444a85e24207541c61803104a01c001e1250340400200b260600 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 68916144 1250 68914894 68914897
    0x50d060b04060e032a19121202070e060f040605060a17010f1a0c01060b0c07060f030504050c0112110705070f060507020108040b1f030b09010f020c0a03052805 70
    0x450458680950081d1001c04168981180d1445091041d0005a20140e660702415030314400c100003804906c59103600b0710290400c0c030140d50101e401070b00168007550810243c3e444d001d001c00024002491414100508503014880040007075019461808000486640d245c01c410010040030b0096a95403241c1720004200b601e009810f652254065000081c1e841456018141210440760030b40040324503007021b44600e540240071800d000c0d1b403102c102048035050900105429100b034001801400e10f4601c000c0c0003905414071407420f1610b02800c200c045603011403c035607101000d21340300f200d119640c18003100801c280524081001008100f000821000092404c01d842c02e5042c070980780c40d601ca90440c1c880c0b140d40c10081c0000c8101c00400c000401081229401c1110750b50341c4044c040ca0045036400aa2959005a4888000b00213204150f00c00f07104100d42080c40e03010a5182a00d0f000c9415039031303906803000408108000030180c425418011030b0301e15652045000c0d6441c82c54807000103029 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 68917394 1250 68916144 68916149
    0xb030906061002070f0902070c09060b13080d05040e18030d06050906030c0d1b03080a03020d0b0a0506271215010e011206020c030702030709060f05090c0d0c050d060b04 74
    0x2d0006010350300312040c00000c041040303855481d5a44107503401c00d410740010f90000c00c0201c4003645004c0d1702090b41c200c10f02408000d40f03001425941c548010303c0d4031a01c00c40541d88940d800e9040343c141c0f0446141d0007002c171401c1e071b40c5054041c019612111101ca403100200340084105000c04190351200320034075000401140c80c12903a8002d41c1c0c031004205070b1981c5000c580f81c1ea00241606100000a0b4203c040c690550015000d95401c40c1c0d99894200d003c0d0b10400d41000080e500240c24402d2416900c01e09102840c15960010000d0608010070803d00c100b0172101003c001e001044080c402c1a00d040c0340c407007a0007030f14090071599000e81c0d0981da2030818160014009504002003500c1001d01403950403115100f95200d00e8102984502000707500c100c1c04001d09000410089001d40c60412012004204400300042e9882c80c00001805003082d6401107841040198141b000041603101964400032804400150303003600c026094800d8803590340100c51050a0000c0020b130840400040c104 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 68918644 1250 68917394 68917399
    0xc170103050d0f0e0a050d02010c060c0e041a1e0424030c0b03100e0c0d051014030a0f060c0203160b0a0605010309080706090201050c01020c011b02030403020a06080606040b03090606 80
    0x1c0300c0303140010540c1d1210307444c1041600f0640e160820411440c15100d54500a4010b040c4000700e80c8013512110305403031101198030045001110704c8403c50400d4030030742129511074105d0140d02d80c004000101c050724041c0c40c8829500400880c1841d03a07840764404260003010b5900030600946c0a41a580f81341c1180c40261102d002c600400200c100041c011244664661b8080810306030070f140400700101405002c031600600103010804c0228820302c00c1a0141810382641800e107450000031100140c6e00300c3c64613000b900644890b00c000380f8411181901a5406880422041c1405004916600a00b101c0c14a02c0d40c00e02c14140900c43c1e200c50580c000c0030454000d1002c2600c5400540a85449440052444030200030001c04203020b40e00111400d071051500f41e24003008052180d082e40c201d4452001541d541d1910b07022000c0340350440d1902c1b05281e002560402c1d1035074000826400301c91003000b05010001c3c00080c51740c0d594104640191010078116520390802e542425030703130042151402d0 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 68919894 1250 68918644 68918657
    0x21206090105040507140d020f2b060b0708090609100801151403070810031202031812070506031902030a0501050112050c0910020a05030a03050609280c170103050d 72
    0x42d031400d05008143c0704003102d803200810190000c40c0324009078040c8070640e51300c0f0f500784050120f0824140c02010006d181007c0e0303003480031504884031546950385074894581860311707004010711440d950075078621940100d9070750f4030743d074520727000c114188a070307070085903100e100c148402002582103c209070685104044400540b4040c050030780c0e51b514501125a80703200148001804030f40f06600046e88a1000311841600d140d0300c0c0d6580a1002e0080c03d01c0b0003682001c55690031003c60308400c0d04152400710395800c0c410101c02d000b60f88404050282502034900000060f01014007161803824038030946204540c0c9113007400411000340002c3c0907060014850042e006015a0b04e4042c060007840050115454400780804000e40d0818140031041540103c944902c040396040c0040c16200d96141c03004503892401c0300410031813160081c0b00480c0d4131940d44e01040304910300fa038070f030000c0d041c80c0200041102000c20305803000c0c04120494164240d03024004000c1190104110951414030344400 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 68921144 1250 68919894 68919899
    0x405071808010c0c020907021504030816020303040c0b07081b03040609090203070206010e090a150507080702030c10020304030c051014060a0812090a0815041211061503100212060901 80
    0x200d098412003003d1800003691950850090303d410403807180c2010040c0100d07000c44910b602e07043c801940488007900852024002c21440030307804074244052900c00e1025600e14a4169034480e090070250007140c25480021400f00304000d003040803203003c010716000000c0702d40604c1e8a0700382c1d2948280641400240188000501800c440c02624061841c54016100c66802d00035003628801c0000c00142c058820b00c81000c010448444d10005500c2c034654000c105850401800350000501604803400c41d4001c0000840341c0402084964422609034005070f40d80d03d0b00d080c01c85203034008a40142050003010450508581681e016a0040141c9140c414080d075500d81008901d5805100f41241904502806603007404040c000b030503030500c01402008503070b0703c500d40f1a14024918600384401540703041400b080c440241140d0b21203e807a881d1800081000b4030b0a19129a07000d803498034403062100000c00180e4003130140340c042c1050b44c80c045441d5030050000303001170102504c0c0d0900031440310002 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 68922394 1250 68921144 68921159
    0x50301140d0201050d090c0905070203040303080403051c0606030b03160b0403061d03040303022b051909050316060314041e0804091107031d03072304050718 69
    0x55a04031000d00a29059240d10403080c4000824414001c9040010402c4400030041a51284a14090140900c0c0842c0c50504060a08481024010009551040c042000040c2c1d000c10083c0d80654980703441610780081500000d0410392004400071080d0801d880403948c107500d6800003042c04070440031241000040c50040d008039003d8010340d01458400c11060010402c55000001d080045003940d803540704650030414110b403c0754100b01c0040e0041e140344601000003d41c105c5151141c04010f014080d040da2010f0140e1003001510001e0080c0c489051488030b0180003400010320025080d84c500d18004c2072600c0380d182d010300039140032a290512100410300303602403017485981e202510305a04d41002c1c007200800942c1e041c0440d80c01c041000046000d030300c54002d0b050084241040c04e41ca50440c2e24014040000001e461148a8a992000300996030000303011000c55101c008038254120200581c900700c2301040c01d100c1e030043d0800060086c030720307403024074001e507100e209003500445034a4400 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 68923644 1250 68922394 68922397
    0xf0318051003140609100b1c09050a05150601120e030d0c02030a03060602030705060c0f0403060c02060403030b18040b090114090d0e1905040510030b0f040c15020303040f110307080f0d05 82
    0x31041000c0018500c28004602440010192044112000341c08401d00308c103402c0944003982c5046403160400440c030f000b0410100812100800003400c00009450000e00082c40b40842a0700c010000e905d414458280010600498880044a07081031020083c0e0035406962680081c1c15100041c0ca0070000140d041c0c40803055860881e1300401801150f1035111545030940c01c00c80e84110305940411000000500034450655000b9058004c0c004603d064200a0122100707118464000c0c4006030036103500c085e5040c02c4c20341c0140c3c0304022205948440100d2801880b85800308206141031906105403c2c8000a544203034007440c0d500d8410140e02700046c030100d0704412074004248464041c040c0b03c140350076081b541c1d000c8108101c1e5048542c0e00c0c0c941d030b1111082610300c1410041050144814045010100d5020740300da600000321003242e24000a41d60300c002030002d08603074980c0c1445410082c01e00096101e1150050440d900180c403841941d0b03d84044004240a0344111704582c02818000c10 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 68924894 1250 68923644 68923651
    0x504052707050a050301180209060408070f060302040e04020904060e1603110604080304060813020a0617060402131703070b190c080c07060b01090b0f070204050606070f0318051003140609 82
    0xa584a0841c0d03e0b000d5038a04501e0452841d031f407025028881111580c035070501910040a03102c00602c03c01e490035101030b200c4081c80e0022010580108401d01602c130705c00b56485d030070960549080b1110ba45500b07000d401071501d428150721502a0041d115403032014510403500740c3c1c7c003650842d40701d01a0a020402c81307224a1040003c6600706000400016009201c0355a0010400070b00a0041e410340e40012007488660f080303400030940d100c40e040c0020741d1000c42e0580c0108152001c5180488400690140300d400c3c0c414400c00e690061401400e00c1c0c4140b0581d54a240d112034501c2c40c0e07080030502c2c01b1b0200b03030107140c041d415440c1240420f00548901e00d0980100130203070034140380140a0b207841c8003030b0020301c10550621401034800910346d010a001003d40788081040783d604c0d101c403481000150341000c1d00d03062154005011500c0407401c031545202d10b840d41418601341c80c02d0044404c0c40700302c0d0f2560000d680f225000c015a1912034040e00070f90081030303401d03540c6a602c0d52001c0c200440410f00342c = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 68926144 1250 68924894 68924897
    0x160506151c05030f0a03020309010f110d0b010e06070c15020309010c08162a08070815041407090903030c03090c05090901060e1801060609030b0f04030504052707050a 73
    0x1d000d0000e0603003828510210050040d03058a141c000b980c2c814840d140d00030900800025800010018165428807408141c18824281848003c9110741245002e02642c2c02c87c01a003a5500c12807034841e800b50800706444440a055075840d00c0490800700140c1080e0711400b280a03100000000e0513134804002c0303c0f04c0d66016121282c20345203c0e11201e4403500104000d200009c60b0400d500e020488103061085038100b841108003011140007042c40460b000b51b880f035443d59000702418042d0800c0480ca01d5076a460304181d40710180c1d242c2c01c1c0300000d4020314969112074043d502012030030740a26001628668042d407424401030f0701d083d01c110200c480c0c00d00302411144011905020303514001c000141c00c0385e180e10000c140741341c40300064100301c0301c15101007144500385115050480001e000300d000401450034500d008030300d9600d0300440d100d80146221503c4034608006020940140f094a000d008081c01c840140d4804e40105081c943c8031201c011484441c050024980611880c11904582240e = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 68927394 1250 68926144 68926159
    0x40501150b0703030902060906130f080a051506040b0a03030504031b050f0d03020c040e03090301050a0e0a120504150809060a0c1403060307030210080a0605010302041a0306011416050615 82
    0x10b54900f24020008008201c0e48030604200d0080c9540d1a40c01070240b0b942c1c25000080a07a282c4015000c1111050307002401940240040401148020400307101040c03841e560301c00c15030356810019000703001f04061030350300c0f10b4060b201201380340e8040701610580b4803901103c81503040384a03040e0012007281c45210340c06030313105840b0021820040c251307a0440d0b11900440e140c119585000509564005e81e8206965201280d152250310707090184c01d41200741581d041081d01807109013107807590b04c42e10002c0c2c601c03c0c2c0c100100c1c03580707441039040314010814114440043ca06d5400000d10042c2c040e10703202d407140700d64408600d48544900c10b854141c1305075210310b81581c4100d20148855000101441e915001d000000000b50319181e642200c2200a5910781009280c80c007040404c40760207800240c101807040c0024041e0a0700e08000300c1d6005004802a0b0300d0f55503010040f5140704021103017040700f00001c2400c4450b4428142c5100d810b92103a020f96800c0d86e2072401c03150300d0b0740040034001d0b40a101c = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 68928644 1250 68927394 68927407
    0x31d030106030b07030f0b03030d09020906060403030206130819051911031606021c050414010506030a0209040602091e1302130b0708040e07020c040605120a06020d020c1005040501150b 81
    0x41e600541c00854100008642c02c0380c0800049c2c1035800c9202c0c05649540c0303600c0720904510386451029803180b8122031450402e815902c009654030001000103414800001c4000c00703008030b00c425200a402c0e162500c2442034804000101182c20203480c4005040080c03601c082041e01401035440308108190003035041245a10b035412003a11600c4050340c0c029030802000041c402100032400740c2522042c000b151608261a24041ea1080c51104d0003881e4944410700400c0c0c7e0300451804039031501242c600c40c182d112030400100074030604513420303030100790304800c0c00c140840300c1c0c94bc4070485070031162180001d62000d001400d910511b6000c1f2080951a4414400408804050700c4600d0043c0ca1003401d007607c44c095a0408071b004e80e6200e001d64040714401c500c91a01e800b465004e07020507102d030384a40300100390700360f0b861501c940014090b075004a107202d074442480e81528894200c00c012039902440703400005000b81010354050740d842d42401c0d660b652641143d4a64400c4030140720440b8980319 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 68929894 1250 68928644 68928647
    0x509091507030b1207030807260a08220f0b07030b01020606040218090406060801060f030503160201020c150309120f0f0a031e0203060a060806030316050a02030604031d030106030b07 80
    0x103c0c0c41129444094040c0e400e40c0b142e000c00c05100903612802c41036944160900381302000b03108070480c0503064008544c4018503168054140c070701c0c0080e1401c05511540711040b01d4861000c035141401c0c5190344442e0001e00303012120790000a064080c80c20301c4480d8807001000c50549803c100c0c3c060140e48008007080e40380c141507005000b548000a1110340f96005007000031051030b42950f056541d00c0e20f880e0248a00002841040002d000398050310340c4903803440d5070301a180d000d071000107580c500c001c00b100020342e402807009805803c4024880c100c0c02111407202c0c40c09401c15a4075151078801c0c040b6804030504c914080b201c039004020006c40c205902049003800a0b03100600d64400c05032903107281c030030300e20500c0024100100c9000c405a03ca103408401d200002100c0d5001c0d10400c1028414040c0c140c03004000c4410234100d10b103100460f8138050a20500d40b0440b440000d400d407054004000605074084103a1040c00c42c41d40030a10518488802c1500741ca207a400050f10300070301703000031840c000d = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 68931144 1250 68929894 68929901
    0x30e011e05070f08030106050408070e150409140d0507110f15030a0e0d1205061509040c0201060503120a020d020f15060f0a0f0501030b061204060504050a08030907050909150703 78
    0x11445443c0104503084a0380c0c54100c02e030000e90003480400e2000c20b09020440d002d002c644042c0c001040841414502194000c082d0300e44062480d000d6076903142014140005004c014203105030001c1200c650030031540300104503611441050304c0ca2404145640c0aa10782504080c55112008200440461603100200344d80e0303101504140b000c43e51400101c420200c00e0140010480e80c41e103130860492002180003040c2e6000810461182100745041e5080f0220391098500080301a100025101c2d2031032810785c010420764100c03907414412071001d55103d0000d54002d0144101c10ba0075500c008800e110140c0e40c491198079561040d8200708500050111204030103903000c4001081d1910041420f4041080344800780c0218191402140040c4800d580502a040c1600420780d819031030080c2d146c6000010b464080c10040c01c5030f40b2000841c00340b0004001205520b504090007a80d80e04161150a03030f12800e0f8800e903400348003c000001d00042c0302060034104030007403100780040303a902c0071b06c114010f = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 68932394 1250 68931144 68931157
    0x11041d03091513060e12010b031e010608010f091202060f06010e0414090106031b030f02090a020915040305010506120c010305090304120510200f07080405100804030e011e05 76
    0x840a06006600000da50407148100401c80c030b4590f88003100b50385090285806c9100b80d0052031b41e06010038488540c5000542103500583c80e00c00c1d11000c0c594a4500e4050441640010250f41c03c0510581501c0311a40c05000c0c0d0324031894a5a0840700b40c0001662107503070486244a0a00d8034600084095014000c8007031484002800000d200e42260301030819080700340c0d000410b0b46c2d500e55060081100c81c1c250150410719040d4440c034414a159607100d02c01030070240080c0034007030041c0400c0c489110f40d01641c0300400010203015220000700002c00c4150010f00c029540d542c2014040391150900c3c820741801d41d22510040c0120f0501c1900550140c40040e10b400c00c0c511041000013056114010401d2005100f003004e0100990030800440a8a16040601d510590304610241000424034111440d000e001001d040d00e581d01401c02e007905000e035500c8070780c0082c0329106c3c4981041d4000e148921892103511507050400000300110342281c2d030316103904003000e48080c407a44280d0184000c1c041 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 68933644 1250 68932394 68932429
    0x1404020405040c020d02010e1207240608160515040e060d0605090a0203060c120115020106080102040605040509101a0702040b0607060c08070c0510091401060311041d0309 75
    0x2a165595000c201211141c3c040000141c01102c001030790340b942805134090940c0000003e043e4401100e480c15064410102c00403c0d004500794002114010700100340b00e0f80c50661010080c6a81d501040c40e25070600b02c50001c1004203000340810180780c4000701c40010307a010400c80e4141400c0030b4890050310307000b52000ea4400c54a103d4000000d40038003a60b0f00c184941c01c06003807240c0c01d45c418140342020241410b1054101441100d00d01840309a081d41140d41010040c44811130944042c1d005000780c0c1c0001201d540000350110f10b09401c00e00070003c4400a44507aa69070b50f43c2d0259800e481d807240202502d81c1740c111000c0700000d1103000a0001c1d640014000104159543c00003049a03024940880301c640d1113030304641110750884001580019203040140301499a503945075103c92000301b1004031542d90351001001e22400c8030300071b00d8409441d4000c115458a030304200d1a80d032904240c040c880e9003020f4a00f10f03c20020991071428421010065007000d5561082107503034a001543c554 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 68934894 1250 68933644 68933647
    0x6090602030f070f1109040c0f1205060402060924040f0803070512180a180c0c03020d0f05090409030e0f0d020105030c1e04060c060f0203041e081b0c10080402010207140402 76
    0x1c0d041d558071034824001d910507581d81c0242345c80c0c90010380001c0c000e9030015180612102c481004102c0108046e0340c03041e812a0865900d0703042000064400c2c0103200c42c0d0301900109d03249025080b191000820640e0311824018088582e40d0849a5880c802d009000700143c00000045010300f0b004006080f1544800b0a030210200d6290082038414050760b01c0000f400b460303000c010402031580d10610031525031b1440c1030807185643e903d01a58aa040032490400c000802c0791801489100c0c406644c4031341b500a006000d00c1c00750342001009001884d0368544140c01d8070300146954078044549203047c69040c6c450078250303900d0b101c101c4840d0304400e66007100d40040702c21550b0030030910802000500140d883d08005041942041c4048414203c0300800c414410424400455500d03900d00003400d030710160301e00d0000c0140c0351500203401000811042c0c00da031071f0b400d100764000214500303841d0402900c490032103881c100f800321040d40d0b06480207070250304111070a0180e081c0d2442c0e600c120800140015 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 68936144 1250 68934894 68934923
    0x1091a0d09033e010b24090d030203030f01052d06040504090506011a030c0403140f060a09151512050a1a0403081e070e01110d050406090602030f070f 66
    0x44524070f0000e007010050301c42242142007001c0011541034800300c080c00200090003000010505c0415a4200910103c00300c0ca000c01e40c0f088680c04036014014058200780956040c2e1030081d40d01d40050740d00b01c0c0803c0d461000800c050400c0e07030748030441d0004549210341a0308100c1c2c4008d0540300c42d01d042c0380c00490402001c03555441e1030007220300c56885000100815072420b80080408128103003141c107400c0042052120700407428007542d0540e504180901c00959160244ca890000e0090302c1281d580500010003004100ca0340c40248001c0c01013408241003084101c0060480d00001054aa0402c40c001c09000d0044039080e200c0c0158403440880714401c0d0f031600d4107501c41a81c500d00ca00340701c01c00c00c2000f04266104a0700c13500b060080000e00324a80c0184081e10000200900550030070590700340000290b031140c441907185035500020b862091b2072032040102140d2180c0103d60114002040000b12544000119001020030920460418070b26542c1c240c1d59080380c542c01e80342a402800203 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 68937394 1250 68936144 68936177
    0x12110c0d0c1d090f0307050d0806030c0405040b0a0c0c2312030a06151701060311040e010b0d0507050304030e010f0c1506060f02010c0507151103040f0201091a0d0903 73
    0x21150035401d542c0d0280c03000e01e030a10f44180341201c03071420060b041d0014020381001550004411080126034100350060340d54a10109180c8103641400341d610a041c0810710046c4050f0005050060800f50014081c6089842c402e4a0b9030960700001003080080380254074451106004851594a581d41a240e4440104000d156907070030950b007800010b590f4200402ca448803182400f0303200146402e2012143c0c0d0b03035903018100440148940300505480309500303d01044480300322005440030040c403007511750b10b800b01040150080307040c0503606441e11020603c032034060001c0d40c0c4200d5040c2d40300b554641c07484d40112008103c0180172000e010080310210000350442c00071140490000500040c05440d000009194141c64411401564505000d054444d580402203c0b000ca1b0002e15000500040d160004003c1100c0400020413110220520082008108052003414001d070388010020380c90340506480e440c500c0c420306500740d0b02041034000641d80303600070131013150103824107400c4c0c002035080 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 68938644 1250 68937394 68937419
    0x904030302042c070807170702030408030703110106050414040f050a06140402090703020a051206030c0306160305060a0f09230c07050105010e1501050706020c070306060312110c0d0c 80
    0x884181207802241c80411241e4000c403c160302c0001480e100c5101d003880ba0020f45010070600017000304240700000640300342d00800494006055400c04c0b255550300d0390500411aa961034081d83c0d455081c40c9002405180034000c07100740c00c0701944106035a40701c1e80d82e034a01d40795030007400f0ac8031400390540d07000120f0294413178121410a1144101001d01d800d104007c405480100b518050610510002d10141d60110945000340314503e440803564030307540002031600610101c0303598507104e803408020495400307492188201c01e180c1c03018400c07901d0710070801500031000d015a400c030801e5040104a4810180c000000b640460141c0c0d101c140c0c81c0c9001691101801c40b001010050002100001c00c03000b4401c4a006040070701e4040c0789401c1c030260030900b0420003004141004404541d1409000e003d03411606a500580d0456040a590b4078142015200c01e200175074240501d800304510140c00b810741c0383c00c5c40755400c0c05400060076081c2040803800d1100f00c1501e02403803d210100b102e814808 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 68939894 1250 68938644 68938679
    0x1050a05070609061a3c0d0203060916060207030201020c04110d0c1e030b1005090a09050124110706030f020f3f0604050a1404060b01022109090403030204 68
    0x10045038200312541c01d000c42d40d058072080c2e81c000341501c144495203403050b01d06c160303a02c6d80c480c11600344440ca80000035040020040041c1d81030081400b0311081d1b01d4005540070140380f0302c2510350112561102c050361071ba040b5206c040d0140e00410300209080c68550f102d50300001528009074201602c82c40c0c0501180c1b0081203880c049038100e12003180348007180364000b0f42c1c0c4180d49014054002c281d4082080080d40300c00a40030301c0804640c070f04042c2d85442e400006407070000000c1000307694408801c00740440c0340000e134000882c442c81420710a0b201d5a11001c8035090b0b14010038132903242000c120300521040e884100c1c080e81c01c1c0300340c0c2001021040249203580b03c1d9260a08030503c1e40b1200d10070003100d43c000300c000300054018080807854107109117a000004840c006402d5545d448090f02401c4142e03402c1c841d0010240402c02040b46076800700503030600a070b088808080b200d03204a11100c0c1003041c3c0e4084800d09000700d4804e41b45c592074030f0344c5c824800e1601500307040d6100c6000c0d040c484c001 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 68941144 1250 68939894 68939921
    0x6050a0b03150a031202060604060f12060c1e021b040c0203180307090627020405030d030b060d050403020319020105010f180207170d05070c0f020f0a1a04180b01050a0507060906 78
    0x420238090541b0b068058180600341034054482e60354903084800c186017844003401418246c803000b051019034040d064201000040a004507000482240000e488903120180c2c0e0000f142c3d080c000c0b011a0500b403058103001103054004514058403016406c2807045100a0140d06101e141c00c0428800b0b618010400100800442c40e80c04c400003042581d010504001100082071040c003040151350b800062020030b1240d28100000e0200c90680402d0b0107100360040070700e0306800c3c1800c0c401050780c0040200000400950007003500e03414140101c0c00c1e20020701c00c0390342c080440502840205504c46400b851600e0381100185840e440d95911114000e404c0801012035101088a620030602e034001e050f03104402e4981020ba600290356200104820304001a0103420600e890044544a1407031150281180b2070074552030b070822003880c21860b40b2078011701700c43d08540c00c1c51108458460084281b542016128a0309185245108032043e8004510540709203448841c48000304800d8810040641c00700c = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 68942394 1250 68941144 68941153
    0xe120a02011508370606030f0308090105070206150a0f08070609080102030f0406020c0c04110c0118080406030207080d0203040302010b09130f060b030109061401080106050a0b03150a031202 83
    0x4502c6408100c5001d94040807040c0c101d407101c1d82d0f105410a801911485540030420003590704840500440250000024880c3d45898004002d200031400d21851142c1f103079035001000e5842500e12404da540503a207207030150b8440030104003c084015000541c0c104081c2603901c1c01551040c1e845400c4940f0b60150140360080c8006000d150761050f554405407030f501c0002d40c510b04020794102001c880082001c0c06840d0701081c0750b4010b6200b405407102a0318020800d000702c80c48050b18001c2c07540319201320b4025600c0d1040908401d5644108048655001000d1905052400e03805401941c80031004072070004082100c4050403810f440a0b6010724001d500004446502d1028490190350280021421900c2102c000300060b0034019400c0103e944840c005c526042110042800f400c82c80c80020000d505010001c0e610152012000e41200e080e42d00074008503075142c00340101c001440c01410000901000000d581003140e1a10800075400a415900c07690303a69241e545110320760420105c0160403 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 68943644 1250 68942394 68942411
    0x9030312100b04060f1209080a0e040e0106030302030d050a090203070e01080706170601030c1218020307090c081501020a02180a060506040b071704030b010b0a020106060f05030105040e120a0201 85
    0x404004680c06042c4a600c55460315050010103000584500e05074410450707000c9a0350800f44841e0030024403507a102e14440d032900001400608200780c1c01524034000c0e4a0201300a103400014050101105e4254014514103808100c0c5080a4032008225507541c903100c00d00e03030b00162000c000d090010400500300884650404c40e40508040c0d9990202080140856403002001c07a41d0324400e800c62800d080000300781d2a404400d60740700e49070f0720700180103525101c00481ca110110003051183c0344218151102c05803074014a100312200389403407000180c00c140000318480055243d82c1c45034101401110036640d001d0b800501e0340c410090a91301e14074010740038064070200d6400b401c0060308044801d903060a0401780001101e001d50100500015101c001d80064854500112406150017049158003580c4445800c030407a4000d0000a0042d80b900301e001032454415418052a0081c0c0d0750342514591901d400c00001d08081c4e00698460b01070354038140100c00e5010010208c541441d00041201207 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 68944894 1250 68943644 68943661
    0xa050304110a0501080606130801110405030c0a080a1707050d0e0415030512130f0303090608010f05130c110d09061706030307080c1c0210050601030e0a110609030312 73
    0x103448010a018000b503010038012a0b80142415900402c29a006603c8a07810002d003403070351005500c158195441c0014240744503045000800a58809034203d452040c1e125007070140e040c60510441c0806d07003001c4807010005440060072200c034500c0e20b038103500704000e070b0711510308010042c140345020400000c0582c02a007031501070119880200b4000000151868480c10740f074044c0d12200c903810060005d140442080058000c0c1701130908442010340168480c6009880f54006010f1440072510070740002800050701030850003a1080034000002915000e1403c00140a008503128240030655509080e403030030801c03e0001c00e082c255181c17002c0e14641600608980f0541c6400001e10075840301304030068030004211041180c0c009082a52140e6a0f120380303003010380130503030018074006451315029142d034005880300540701904420089602c940c401501200c48406480c40c454004804400100d101c0c17425010304024017078412450010387c1c030002800c50340850740707c83e48000036006204010 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 68946144 1250 68944894 68944913
    0xf0403080c0306010207030b13140c01090f080d03020f0c0610090f0c1e03090f03080108010f020304120c0501110d0e010e0a020619021608010b040b010e010c060506150a050304 77
    0x45041c40540d20b541040c0000035110401030002038400e0240c0300212300516407a5440b0400c00307400000300501d6604003035140f0749036075042c01d666001035810399010400e12465120030007160031040c003c0c40054541e03c4146c02a410210038262940d1080c01a940046002e00c15144122565040d4000c1e80c0c3c01c000d1010103d400a4248010aa152480c04405190804000000d0710703440ba0140c4410b0740b0008040300178008810300201400603822207042056000a4080d06031410a002840075050384200c0c3c0040b4001100e000d840300f07090a1200c880103000380c6885a100c0d006000208003001e0381c01040f0f41e01c2d8480008004600c5e512110801075a10a210304464000808064076840d0401d40000740d15000d48020412041c0c0528a19003c0350300070440d4155082c00c06010005040c1d4805400d8001c107a20031806004030b05000400700c05611910201420840584400f40c40c0107040d103500d001824014455a00b01051000540b2500b06680c0503124030f4030165201079491405c1c0c600380440 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 68947394 1250 68946144 68946151
    0x6030e01200412050a02060708030a051302060405101205090c121603080a0c0203011104080d0c051c03020c0708070f0b0f0d0207020316080105070906110606060f0d050f040308 77
    0x2122100107003922591812044400311840c1aa20310801c40d110305003142071100c0342030001e5102c1d0b40084c0c484100035018015501c500c06101007006130344e480381c1c5201c1d1800904030000f9407041d0204002d01051500007a4245148000c0ca05020f196025100000032150261b407103021070b50010580440b24a0807071242d074400020070003c0c16803031050441c503030381050f001d01004052a82c007080e030507421442001d1206045030024002c0c40810809100900b80c0d03807040c0544903050207100d1811383d546001382004081d0581c050003c0c02c40115020a600c0c2c1d01c65598000070800d82c007000240042c540c1040404041c0c14888081e0102c64581540121f40198540c00800c0300b00090110103150140030003a284500c000c1040907a841e04288000b81c00c00700184541c0341d080807404408964903005500403403240101d622013200d515141d440030f8480e060101011320b941d91052001601c582050400f804218207001b48143c02d0001508a101c143ea008a400030304110140d0200024554003681d071580 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 68948644 1250 68947394 68947421
    0x60609080f0309030601141201060308030f010806070f03020d090510020a020607111903051b07030b130f021c080d05060108010b0412021005190201050910060f0e0a0f0606030e01 78
    0x20f0041e40c1004640c0344d54052185c440c000141c0b071403c908540356950080c3c2102e10007002005403948900c0c1422080c0c1040d032303504440010050002c107500c040000d00e14040c0c000c3d501c5024403102c02c0e19007200a54442c200300002d5944841c50350000840402101600041c1d0540160b103134104100000e2400000801e08010091420900c0041140200343c511614030b01c0c0e0302064580e0807508040d42c10307200303114417400c200000c201d8200c1d0303d2202080354016a4442c140071420744d12480401341940004074005440f1642c1400d118005181c00c01c41c1010381041502c000d520720300c240d207034800c2c2d540100c50311814a0b500e500804c03040e9a0b100d4541405020000042410706040121000c20b14884240080c00340300d103090303400c410794010015201406010704054031000c0c14040002c0c080c10040c3d8001806105400f00c544070740c203c030f0007540155003942c0c07080c0718100d191100723492241c103000d048014520398854401403812280c1c0210b4001d001191004103c04450785001402c58550072042007 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 68949894 1250 68948644 68948647
    0xf090b0906030111030109151701020711010806061210050d150e0726010b03010f0c0306050609150a0c021804030f0215010605090102070e01030b071403090d0c05010b04060609080f03 80
    0x20399113928003628191039141000007034200004c000f403c4502c4c52500b250108025811880700d600c44150000d0955a1080c02e00c501029802801502c042200ba900e00364000014450f2110690000d001e180e48551300205d030000320b90362100800c18420b0a0b041c107681030b1000250040048206004080a007402403006080c071620303000d212003a4200f0118035500c8404400c242140b482c0f0250032101d003890004000300000e10140c41864014006140150082400c14100003001c1c40e200d4240e4a01940c0070300040000142e040c11640304d58448440c0506200b9440c0c61140561600c03682005410800440103107142001c0c01d0241196048240e2001103512869007002240125065070341124000d0811541310b06048006030304203402508201411403024000001340200c40103014011006600c03030098511540c00161b0f0144400c81d04011164851809506094884c540038003140d0700807400052511398580c0054180d07903d40c0c0c0700700009204d21405100005007402144031007506d0750000c5 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 68951144 1250 68949894 68949911
    0x80403080c0d090617040609231002090a09020913020309070e0114030c0108060a09020f0a0f0c050604150915061a09010912030201060305030313050d03050405250f090b09060301 78
    0x7045c422060ba82c3d05c40c0c0d502c03c02c0106041149a4001860181d0311424883c400e10f41c00c00c40b515080f08001c58100343d8414100c480d2410315092084520446028040300400f604021303a48001e50300c0b100c1c403160009000e03c1c0b402c14884070352003c0c500550400700a0113140703240111400d40e103241a007161740c8803c0d202e5400d00003030303400140180300380c00d0a00706445240e0324031f40080c0d5000696404013801600005030304c3c9010300c0c08001803007000000c1e22200d20340d80000104544444204400901a42c4540c0120300860000c0072034054524200d2004541100c0507130b1600d241c1061108418143d5844600a00c06101030880a005522601d03050606000c0045c0001f0300f0307005644210036004082642d00028140300b904418091a0410112941c81c10803000b500c0e00303815205400c1c1c805000710b01c65081900e00c2401107500507500302d80200b81000c100e6002c0241c0c1d65100b40318004164443c2c60000d480c64a0f0700aa400420b4807100c0015540040014401180b6006182601c83c0e490724481c03 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 68952394 1250 68951144 68951147
    0x20108010e1302090703110a03050a05010e01030f060209030a0c0b090f1f0305040204020706141f0b0306060c0a1e021f050708030a09020a030c030203160e070f030207080403080c0d0906 81
    0xd00b100b68044035091915103440000340c00908464642d825400800146045031a800d908030602132003000307404005136a40c0d10007101480300d081c000103280d999085c180c240499a6078003c5d011002c401000d59690112540e02c0d940e0740201588039681411011031345900c1868400503544891004ad50002503c00c007511444070a4482000c015041c1583d503400319056498581c160b96105901c040300f0800d9094035643c41c0a070b04012603600182c0c200061501d6400c0320304880050485980071011805c6803207407030400600d86c1091041644a1041903150700c0070031b0005402c1210b20711008001a4515800c2c01840302c44015110100c00104041480121259101e02103071461a041000d03941c0726162106102301a00c086800650300920641010042c0071800c80c0740d4040b42d10071802c41710100001c2c403102d03600402c0b0344100918004480002404217008221044040c00d06280c010b00d80800e503503a4250b9500f00b070300309607181030001c6003a207100b4101300311400c000c1c8400c2c20001144d500c1c1c40c00 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 68953644 1250 68952394 68952421
    0x904140f1c0507080d0f140109090c050409030e0424050307050f040b0109120b0a0506010206040c060806060f0408010204080f0f060123030303070c03030606110c1002190f020108010e 80
    0x201072003080800120803050240d0310303003a110300c002140d80c107100b045c5050785c044d00035010040442c100d8015900001581c46458880d10b0206640007100300d840b02c0c0f80608100c0208820301d0182c0900060b5000c034489980c42d441088050304100346965088216541034445c8104583c0040b4060f50003200241301640e1842400c00c1e00000445002c15107071180c5004861503003103684101041510038909008204044032505e2142c10509010405030351404012a41c0d00e4007510040c2c241c0240070780c107000301c510482d02b26500c20b4024201c2e41c070b4543d51035011402540540d000244d943d601050a001c030200c00e20145480c06402e134000d00440344c0354141c0741c1e244e220600c20342e046003521100c255011003d036000a15052401800c2d251a07180101000d090804551011400240781c01c0011451502596040202c429403900500030201c255040c811244140d20254003075109039155071000144e185070302820308c3e00c6035000d04220034491001500b025411780000c00c00513803d10412a090501c10b8 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 68954894 1250 68953644 68953693
    0x1080d050c0a060b120d0207030510050c030415020c03160c0f081009020312040602060703050c2b0b030604030c0512090d08070c091107051c050901050703020c0904140f 74
    0xc00202d1455180000380c5ca581034120810b000d00803050b9441d0103c6e00443c4a0044901450aa031740010415040b80e0031a503085803a510f10082c1403011401142203c50088019902000018540b5020859081c07a540040b0310300408a65603419a000f0800c44080000040001c2c0584040d02820f1a55440e00c400103800ea490603d5500d84601c07047d5981040051400c0c142481001e9607141c9480d802034907803808561280100b4145000314100c0340124040324408070b10f840200464510001e508480c01c1145410440501d8a030280f500c00c940d01402a9402988203807900020802c09103843d505100748503500d40004601070060307007034544400740300c0d2150b903074421000c5036140094640145000307411f0b001541c085113015801903c259440000744130103400340c030482e152801c04403407103452001521132301c10004a041c015420729501800150030841e10a0050341c10110b500c102080b04040d007150b084d6844126420a010112001e10410400e01c9043c40501b12403074004d404c0341c17050000c84 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 68956144 1250 68954894 68954903
    0x5040e0a020d1b05150a031b050901050a090e010e041a010311010e040f050106030509070503060c0a0315080a060b13090302070312090f09020403030f090e04081c020a0801080d050c0a 80
    0x200f0742c0008084035148102422006080340008000c04241c04500d80104d114200803034908111001c40c2200d10b04030820040ca80e655070391070405900c00440d0250003007202e03c2c00340905e804002c03602280941d503481c0a400a0810322500e0f00d05814480000c1c45000b000c1d0303d4004000e03005001007800000407070301c04039082c2044c900d01c10b0440013190052078072122800703900e85844008a20554150062809100c62170111003945440c0d508154480d078056985405a039000c00000c43c0943c001d8000380456481800c13039684050303a5000d42c504240d0001403c4031490380d144a0704029207400c01c030802140280072070400c00c40420759006569207600d800041c1110900741c1041c0582d605ca000c0407400307890780c02079400c0829034501c0008060b401900089002c42d075410383c0c81d149188030b41c026508899024550f56070940340d684070000d10b0b50103035a01c014072400c8200001403002c810300040074170314242e40d40e8030076540c07510b0910b03824020109201c1c0100a41001038460f40c442c009100905660403 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 68957394 1250 68956144 68956163
    0x20040603110903010203090607090503011a04090302010905070308120c07200a09060f0807060e01050301061404090908190203040506091c240605030102030c0f030a0603081305040e0a020d 82
    0x100c4140900c0c0e000302c0c120707154150700001c2088118900412028050308aa0315074001706500d50f801c040c2a90f200d031822041920800004000b41d01d065001800e009019000028600b2025100d070f82c18020140c0040d189083c0005403000e01584090309141d1200c0140003140c2840c5c0203554190005a0000300005501c2d080240008241d5039602050700171303c1105010002030b81d54884c000c0d4980301c58421025507025079600092010301400c202d4156403816506c1c01d146a00740302060340d40e10b03180e80c401810031a091101042100d480c1c4100500c00340520b40b003a49a0018240300b0811480c5c440c0c0728030440d08240000c01c01919124161000c0c0441143c034030910f40e4100e03c0850f800c03460204050400c2d80c4110000b81d18910f10341c0c0b00d504003c41c0003801d00a603522141403600f031b0f10040d40c03003a2070100200980420b280842014642140004e0804565640d03252101c02c515080340510300800d51110804102038549846074a0700c16207031901414a181c1180c000034840b8210240150403030782c5 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 68958644 1250 68957394 68957411
    0xf03010e040c0f0f030510060503060402090c0c010f0605120106030210030906090b0a020c070608010e010e150d080d06083c0a0302060a0b0d02150a090b0c030d20040603 74
    0x804402c400081d201c4003200a545560b201c0d1135500070704039440207480d07034062031882e020801c005000f180e0030744130007a00605c40c5849644c2071240040300240500b4800105001441c40c064007809101840300e00b460707002c504e003403c100c00c011520b2200c0c1b40410360f90303160000800050b1a240c0101c4620401802c00265800700e50520783c02410308c0c518024100e5804c1d001300403981d016940074000c0c0308104400c031a1455240c0744213485c0e8007020b0040c48034080003103004124950b120381945510401081418114101860200d5084400d1280454001101064200750b10a46100b07500003080941d009101446030981355200a2015802c0c510302e82035044200e291402d00d8441c003149280340e400032108146001d040094641d03005a030740c0408a42007807900180d61401300c0e0724207400c5400804051440800c1400c0113030641c0041021828003041000028506aa000113030500c20381c007a000e15a24002d109454040318902461a901504001c58a441c5040c0f130701c00759400d980045c10b0001d030500 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 68959894 1250 68958644 68958653
    0x815071e180e041a090d020304050906011b261309020c15040b040501050f06030615030c03030703030906061a04090c0306031e030f03021801030b0d0f0309080c01050f03010e04 77
    0x407a5802020003940010103010400c401c0081d203810307080000044411603120f83c0361aa0b1114020025900180e20901c014030031440c00320f000682122050509520740e1040d100c103403000040b454015100c5100b248041000c2010f0b40d44515440414446030b00e240c9507055400d0740c0c180c011030042150265000c0755500c00030b0010080c844607500c0c160076222603403a080c80e04e6000303840200c604668550903c4080348000700c48188403030007220000c019208951f40d038107100c1d008180303100c441c40e4140704400142c816910706200030a44207020f9500800c0e07000b05c50030050180da00c998090700403440b981c40201e4003107007500161001d80342c0001d0b000c15080c902640490280c05103030005071101c540d40d100450301b5030410344800c42c650f01c070341c850045061300b40000350120700804040c0c0304400302000a100380e0358420380c0307c810440001015107440e803516407034024011202074801c50100300010002e020f40c1104101d0408010002d182045c42d102d03e4104225250006101c0c00304101100c0f0049820403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 68961144 1250 68959894 68959937
    0x20706090b0d0e0715030c030507080106030510050a0b0a0806120a0209150303040b0901080609070503060f04020705100c1103070309062016180506060301050d0f0506010815071e 78
    0x2403c1c1001114001e40d102d46a10309010040048030000c80c3c900011044014001e0040922a2041d0f44030a4280d070302c0d2035000c0c1e02038000100b110f1708190100c0710200340340e91940f010380c1c054504091100e44400014801401172000135000900c00c034684414030000e8000040d0030b03800030b0350540c0c007144507840703812100700310400300c0815a900d070101040225440c500c10024000342002642c59a000d9100e00080c0300310b0780350554548000500c01c200003465420b0442211200200c0641b00504d440d142c1c2d1115410050380d5111a80321a0b250900c09030b0042d800740d0494402c01d1000302640c5040d45564020b4400440c070300c40d2006000700b910450b842c0c042450f8848081000c8002580d14200500180701c542d80303502d000c1c20750840d141c0500030100030b0042c4a524428100a8922407031a4200301c1040b890100030f80e4100c600b0380ea00c80008000a00902c101402801280010314950b406140300000721100100f040082020b800010900303484280c211254101c114207044290a07043d8100d40b840 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 68962394 1250 68961144 68961161
    0xe04060b1909030c060f1d130216020d0b01090b0a180b010c0813031e0302031806160501050f0c190305041b08030301050411070c0605180d05010e0607020706090b0d 72
    0x502040c480005c2d4564000e115901084211b0b507a14840303028007604003400c109000c8405070084440201402d54402d62303070081c44100008403c41c000d2540d550700081b61908542000c8a041c14103000400c9059824000c2005101007100c20024150500b10341c000c040c0c44804680300c0442d2600d44804503640074078650003285401009483e07643c15200401e1001600902c4100c0f00c5290750404080012200382c0e0644200750b15901841c43e000243d111410846043c0c50401d500c180100010021055400031a1419034803440000c175243c03520329002500e6a400030003000205004000492078411030840a603000802c40c10b002a4641701d60901e83c030756071001a40040206004080458001800005181258801c49041c80345002c6868031814078029100000c140c0f038440e91041c801340340203d001c0e0282402a20002901c03c0c03034a80010146c041440040c1c44070307551405241900f101c00d04c4581d0340640180000c020340c40c07920b54000e000050301c2c0314032201c140c0c0109151800001d42d400c045030 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 68963644 1250 68962394 68962403
    0x50406031a0702070b0f030907120309030506060402090108060d0c03020306240303090d150f060b03010501030c08010513020a02150a060503150c0d0b030a061b0e04060b190903 77
    0x512600c80c41c06211488007011045040c075694000911014800601881607400d04240c1a090844507a00044030360409400410030f801038860101c0d86010244003889158001d42d036005403549181802401d011000c3c040c40c2c0524010000c0040c00d0342c0000c0000c0d00320303005503800d168211441c240f04e200246150802541802001c040c4170713040303090b0068042070480f40010b20140340ba004007015524810900c2407030b000441d203003403040812450482e00070300c0b92601c2ea000c102040ca0602a03003c031501a040040e070030350040018822568144184243c3c1c80301c50404200c01d5041c80c00141c1e500004000244030241c000030b614010504c28000f0412070f00040c9030500242c1007440c0010040c12140c01200d02130300c11039030003040454401d00020f01550b00b000c450b034581641d01c1c1461003d0400060301c00d4041c0f14015280340000c40502ca9280e010084420315008088224401019146614015072199050400502800030214101c40d0310810a0f90800c0822850300c10690300d11181e94070180 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 68964894 1250 68963644 68963651
    0x91b101107090209100c051009140f01060f08010506180703090b010b0403030809060f070f05040803120f06030c0f060a0306030203030c0601090b040603031e03110d0e070602030f030403050f040504 86
    0x180c0c0e42c403d401403e10303050100e445c8040028450380481c0c03480105178010f0b01c80da11000a2055403812903000c0003200c0d02034120900c00c1075416400920b0820203150041d00c0369503c5d10b04020754801c3d424100d000d041c100000740040d040150000b03103200b50000a03c1400d00a020206070514000d0340010200c40d440f90b1110103e694500000b11070b9041480705501107581e040018a07418001718010307114011085034040c498880740011030306504865418000d1190401000c41c0144080010306105d440d58141c80e2030903d444004d5000001c4080d0159029901c83c000c414540e0341d030444814a602d40c2600c0081d11035050420440280015500194240c04001090340d148c82c03010540343d058a0064105118010100d010700049502c1840003800292072001417011228102070424180d00151070086803820400c1e4450f0055400304901c9040d640e501c140c2100450303002d0203900c005000500103182402e680d06c0c500c95140c403005100401f001400600c3e0100903000d201a40c1c081d003400707031007003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 68966144 1250 68964894 68964899
    0xa050d0303360c0602012009031011090103150803041701060b0c06010e130b010510110709240602030406050f0c030d0b04051f050111031e12091b101107 67
    0x32500210a043d6a412054030020842c18014083da500c407400d01c2c1d000045ca01e00822014050360002000507600d401518042d241c088a0342c044e800e240358042e201141d6800100002400f1980841c0201c0e18524010008008408010003580c0446422201100503800340c5800d0b140184038642040b01c0341d10020400704042100098086c2c1070314000b6003010041c0d03c682511001c1402c0d0401d0040820421100500050620009200d44c0800c241003444000748040d00503402e0002d140c002e10309017603690340c02e440c00300c1c4480b0810001d00e140443d100c9266080200003502c910940c054001442000201a1003100c06482200c27660100441503030b032241444c0401c1c001525444580521650501d03020a00d030003130442070020455840c0202d9041e4600e428010764220303028846001c0c40d800144035100d82c0114a0f00c501c5200000311070450359501d40d003c401e1462503400340800000b41c0c4004920b48072005800a10700701c003030341155288144288080b08689a0120440e440f496004601c1d00 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 68967394 1250 68966144 68966231
    0x20d1107030803041a0c0301050a0b0903011503150c050306032104030f23030a0c02010315180c0f050315060318010e1b01050c190204180302060609060a050d0303 71
    0xd4145c240a0358a44c5a0280c80c0c00d168503249010a004e4140d000140b902c0400200000c074004000e03c0c2006000400d560754180b0307040342414110392003036440682c010000701d1040700d10308c51060480325606107035045041910202303544002c4042c814110b5950f07003c20316800d00b480c200769001541e200c8000000041c2510f40b0101c2202111f220070160101008440e41c400d90202c01d840016071913955022031003142d900110041c00d030141c90041d00f0078200002003141216002030400600601c48045201c11324030070010007295240540c601042400c0c0f060100c030601101c94250000300c02c071303003160f01da8440f00f00707015103030143c51141c0965618019030300034501e00100c3e0441114680190b01c03640302d581c0c040196840c5c0719400540d07a01c0d81107403150717070b9030030f140c0744207508403d400540f0004480c0400038200307800074103101081d00541d001100308503c0f450a10744059101c403050350390341c1c01140307040082a030412400c1c00044c240b40c1c5403280f0385001440e800040c074a14540c3c442c200320b4403114501 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 68968644 1250 68967394 68967413
    0x1809080415020f060c03010501020604150e0d030504110a08070b0d110c060603070603150603020d0b0a1e210204020c0c0415031401020c03030105010c03020c090a020c0d0f020d110703080304 83
    0x701d0001e004d64000215181e00d0719013aa8121401a0098050350399550fa800026201d1107059820107540d6185d0b103018800304101b00348200520391800986030410382050250f50f100e2814003071054a03441c4c0c06000104002c150310b007c452041c0c0000341c8544003503001102402c840c0391807907850f200c0030444c031540345000513240340680740950549040980b25407044090f03440c060710410b10201844810480f5501c41e5000b0301c1548106000050445500c00000c1c089040640c09410b030701c6c24042c1c4c00e070002403405a00200801d25101c026120303a500b0340840540320380600002c1c1c8290341c0442d403d18100414040e540304500018000c0107072040020210010600601081d526500e060007413036404e4105108031100031500600560841e0320f00001100c0d140748a030300c210f04601845103200401c1d29183d10b0607000b03690907800542c0f105d5100d800782d4944006a0312150030801d2200701c00b29440d070085032555100083c0c1c40c00403252030176600d600b07107044003031343c8000d1108e40000100f0040c01a00c88 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 68969894 1250 68968644 68968663
    0x204050a0b041802010e0d0201050d0908090102060106030e0601030b040813090e100b031504050a08040806070e0303071211030c1c08060a03030806011805060313021306180908041502 80
    0x120100500d07203940d80034910182c3d030100003d001c01c00d040c04000c114139144000c1113140384149030140c54000ea400315681034628034082260050000302c0d0000c620760b0103000450141a40d0700d401c00001e00c10340880341d03440d1818840904950851404a400c0c013944c10210703051944800200250680d4603405180244440d0a004030300d1f004500307a4024801641c002c0701e44000000300140891000481c003035001620103042107905101e130360f0003400010100380107400240b00040140c00380e450a07203009442e0728a05211b0f107120390010880003000544501816104600310b24040100040740301e505440e40c4206e03a06440700d44506800e9404802c03640c00c050404808540c0ca120b440c5c1c8a81c0180b120303860303d034040180400c8544000070302e130703520030504100504c45680d03201c0c1c0d0265942010600310382c01503442099000c1c6c0d8a4030325095080000400200b01c8001c2e0040020030310700a000c42c499180401498826510b540c121310500070841c0c1504d025110700040701c0d8001c81100740181d90340540da0b = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 68971144 1250 68969894 68969899
    0x3062601060506040302030c0f040902030604060c0e01111b0433051801030305030403030624080117030d1a030102040b040e01050609130510150f0314040203071a070204050a0b 77
    0x2a0021540c3e00300390041c0c408503035000c0c0061803044240b40401081f0014403000b9a0002e80d510740f440090b9808201c9640500d001e120001030094078020000c024400950301c1ca0b0511502e017031006a171550001b41040c481900d500c12b860400d03070480014001d4004d0504c0c02d40340400180c1580ca101590f4602c51704151039200b510b0900350f40d61024031010010042050a15491140c010070100b80144002c59110b0311900c1d00240f090780750f080071215000010303c810301d20003190301744c405441c1d0411903590240c0f0044102400c910b00643d4296524800c1c841003045054540c400c180514001401082c4900001802552169150008251644c00c00d100f00b00e0007000500000038141440350032503a0011000c0c1c15445031400003001e0402030000a880304907001309584000031048032050790041e2404c01035072100b4ac54451101d0086c00c0d81e03034444a040f1030200340e405000059400060003030403549800385001068405010b0000c80c1c0c054005c010b504141032004112010100da480183c01d407904 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 68972394 1250 68971144 68971151
    0x102040f050d080304030f050903060a0501060807020604051b040608010e030a09060903080d02070f02041e060501172a041d070c02010c02041e0e0601170307050d0f03062601 76
    0x40700e0400101071190346000e0001e580c1000420086403084030b078441c6000440c1011890180a034003c6803511600315010700304d041c0d0f40c80c010310140390300217816500070b4602d1000b4041420316440702d42d00e80c004031108403031451440c1e542c2103054075250003403002000e011000704000c3d1010102c0544035800450440c000580c20300b400300d220342c0a0401c040907250001d0384203040007010700310031000354080d0405030b620150f00d850032401a0340d0360040650101040c490b843c10000501c0b00c42e400d40300641c1006060003400035002d0340300071040c0c0c02d05a1006c500340600084d20301840826a8038140481c0402e8030080004000c075480038855526580150324800c1201d4a60f600202105d144040102c001c0c00200c01e414201c002d031402e134000144154801042681000800a51303008036039100c0d0706910181c1200e4010011422150964000d400380030b005136180150b00d0396459100c141d520704020030301c001402c0c0c07c3e0420703120f50721101c080d0541038004044500c144010302e9410f240952884415800d = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 68973644 1250 68972394 68972399
    0x1030203070b030f0c07020f0607060b04050c0a0e0d02040216050606010f140a0f0207080706120b0301020a080403180b0a05120a06060e01030b03030f1b1b1e0d02060307020102040f 79
    0xa40c2c20440348a0f804000d803068035900c0d072000c05940760340f21400076684044510302da0101c9a40d45001024640d10030b240004481da90323142444107454001302950070820060016403c015000a040802103204407601000203815200007030080c065582d02c940124000721a0008211001030407900800003601d0310001c10813118400c4070f02c4c00900c0c500c054002c400303204154000e030240c541d42038610700d24015115807a80716140c0524002850340100c000644d9900c030303102c080065115590001400782d009500d4020300241c058007040340600002d04021048180c16034055440340c41002800139a0740e500d50302c11400200810a40080503c1b007070758960203000c1031a0b00d503c0e00c10300048071034a072614080f0101d4000194010281304809541500003001003811100300100140440aa22080c0c0b0060f29058207810b4a4182140798200d0300101c2520b0b411090360f00e008020300364003c5441d00000400380040850043c200036100250803141c040180099960190040e1003610400070b5040051903 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 68974894 1250 68973644 68973659
    0xb01031505060a050d03020106090e030a0e0603010e0708090f0d0e0103050601020604020a050402070302010209040207030306060f02010c120507030b03061006030b010203070812090a0807060504060513050d20060a050103020307 99
    0xc0c0181c1c2c00e00d43c00794803540b00704410b007002c0c000c1e180100d0182c0000180c195507032a100d01540d101103403c2201b0b800000303840d18040d402c41010340e03d180083c1c0b40c050540d030400c5813100071180058100420b0141c0e82002410303540003007141d5810354211400f580d01c0c180060310060650701200d0140360100b030030640050801e502c00141d03244691f40082240f641a490081880001c1d8081e0000354215502004001e00c40d03100c038001441c40724465035001603140e103070034130051841f0030107202c100031a41406900443d0075841034020106e00e003204000155525500c40903801002415010798060290700c040080c1d020100b1900303c03c48000791010f1003181d0680004a07124840e4640060145006000585400030507003421640181603800f150308032903481d110030041e504003c07811130b1003548402c10042044110701070aa04494480b0004100240340c7d1b44898444202084480402c00a20310203094422080801c00c02d2041100c180c81e420308105840e880070741030074002a80203204140700000c40d075 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 68976144 1250 68974894 68974901
    0x9030705031909080619050c0702040e06160809030304110612180105012c04031b050105100906030302100c090f031110050a17070207052805031207031b0f0b010315 72
    0x45407842407131b07020803010303d91359401480c1c05840c28424010910010005841d607200e561b5031688214020400f40c80c2c0b0b007619484075582d950901e000c000c008000e0218600e00003098940040d800190041030007080310115603a030041c440200c4207090b14400303000c0c0308442c01e00002c42032210040207102d42d0b81c8545000e400d209064640f050900403540082c01140218054660803030b1292030849d2a8400c072040c408007881c244402a1090f0350b51f07000f4840351030340711180107000748014842446814034540300a51180302d20307103c09105076218841c02d18814842c01809010f801400011031643d40c41c0d0034281802c460303d6401a01588084c074848103064001c6058806500c059500c4662509040304080701144019040000b03601c1a00c1c004142c50307403a441014502501c4125142d030001c581300116040140d04d502c454080d40001d0160440e01e07104c0c00c11614500c0d01800c1100c1d03020507410824a1304101c0d44005020307850380360700e60340c204018085254100d0380909200b032002080d901168046 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 68977394 1250 68976144 68976151
    0x50702040c1b0305090f03030f0d05070c0c05010807020f0f032508031305030904110a080f0115140408070306060515120a0e010f0501060906090911040e090307050319090806 76
    0x242c082e100d0140c00248280000d00603000e01422014906981c800401d20b1a00111401d07005010081b40d07105540d4a54414160302126501d44070f0b8000c0e28a442d9008000003d008640c10031045000054400b130081104560401c3ca00c4100c1310b0f0030214070320701c903207a41022444941c400505168000210b84620704060025048410b143c42c5440e1061081482480724104070b440340003e0ac03074403e0300d5541c1d00c10f8400c05c0304035120271541c41c680c3c802c0c024440c0c0c03c010314540c002c0e664003005200c107008800d001c1c001941103042880380d00c1044900b03d4058003e5a000280d18481c180c004000c0241d281c0000003161003e40d0011944003c3d1404040d65000b11444641c4031000e003c0011100c00c640e401035501c002c500800001c14a049840d48070903a02c003604000d002c229000070802102e07921400700c20080c02846410412502c4105070b000700e6210b18403c07d030404180e4404102c0001090040710001507008007140d0b0f40c0c02020441c48007100e0881407030310100b801481c00154a04011841610 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 68978644 1250 68977394 68977427
    0xc0a0b090906040e15010b030f0606070b06040e0703081c1803020a0b06060d1a0906010c0506040f140319080a02090102101a0316030203010515030607050d090b07050702040c 76
    0x700355210010b020041c040e2540d1140390b1701c02d1544841003031400d15441c038043e0910366881c96980c50a0103a900d9402c0c0e0141445015003000c012050101d40c1e14000150015012100820b490030340f194190324001440e000542004800590080300b030b102074000a16001800c002449286450082d0784248025000043c1c0540c020410140003d505422a207a21060080410f410300000070a00c408455000030100042521031b1003522162500c40011039010909184c13071001256581d8480340c90700005000101000080c1e02e09500700000c2a05403407503a8804021240c40e201c40c0801181c200003a030001202180010300803410556590089034150001a0000c2403001c0d082c1551a00820058000b88030ba00184050071040d070b07038240074000045d114001c40c40b14407402d40c01010708413807001c1e11440031009409030041103030710049066540003146041103529240b00c103403050080c002d501001001801a8400c21000c5c0f5046000751120030300a40d0b0400a8981c00241a030b180c1c0c018000405 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 68979894 1250 68978644 68978659
    0x17060102121b070f080d080105030118020d06060824060901050a0303120603080c150c04030203060708090c0402160b062d01050f0304050d1403010b0909130b090c0a0b09 74
    0x102ca403466508802c100d00103450840d03c005950302d1041c1e07540e04154000d00c445800c420b004201c050f500184180c0074010440003008025076002014115440040000380243d200c9a079240600c459580610000c10130001500e51b40691403c0c0c642c002460b01207041c1090204902080715030516820082c1a9500070340070600c9035042d600e081e589c030711105241c140400e44842000c80003414020150401030400b600515201c0d8510f402078150445c000d255241c040f60a00c01000540e41c000754040d00300c101400c00705c0315512804051400e004080e10502e8020703000269080c4820340c1c00c03d48002c080d0003280b4540c1030383c54100402c14103140c80400e07684004488048400d00310a00300c400400c80005061152030640c10f207441107002d03001254155a183c00151102800320f8110382503118102c2a000300c9451581031051200803406074020090240880100140303110400c0e007400e220060300300344140001d1500405413550f44000d40c160070b0080340d02000001d00c442d125010f6072030080d0010801c6 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 68981144 1250 68979894 68979907
    0x30b04050601080a0302030906160512030907080c0a031b0e1006090816060806060903010509030d050c0412111309050604020f0409050a020603130b0106030f0b010504050310110d06061706010212 85
    0x31080760040c20300c0d000c825500c0e2401800180080183c0c0cd039011401c000c030b51320b0349829041a03040c8049a445040740340c101d41090126a03449042e860152a84a52403401d45082100c20101c1c1e00d256400c900071140144092100c0901c1e440e04c080200c4800381d07207101c4c05a86402e06a600d417080040000005007440e001440302e1030243c101d2a41c4664040c1116081c002803c0000f82941d0080c6d4000009400c00602000045a9030060705e80c058210911245058a0040c8500b0300800e954000ba0030420b1029103504107942c1e5018038400002c6424080c011105141403003501c03218140c40c1244907181c0d007500d00a8604007030040003051a0020003070011000c45400744503107540010005070200c0c13a840c4e0313803100042c1112201c034040c14003954001031116200c150380c800c0fa90042c901c64140101488104510b9030002001c0c1503103d80c001c000303d4165034460240c0100d018040d0182821810404045002c0398881c51580c40e6800044409006e0f0312074074016a01ea00000341c0c500b00610040011 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 68982394 1250 68981144 68981149
    0x50d0b0409080d1d01020f091008010e070503070905130c090f080a030e030c0604080703140601030b0a09050f01020d020a030b040e0604120504030c0308091e060313030306030c030b04050601080a03020309 89
    0x55400c4402c02103000c0d14044c142c0c2480383c00c90703000001101c402000881c1050140c100443e001015492a04240e082e650521800031921180140f8000c100003000000401d40c511900c4034100411001c0c01c26442e0608000c0c003100540340e8410214002000303c1c0740012082c2c81d000101c4101e620b4031024220200d0207403421242c201d1003112494262040051000094948000401c000c141100c00b61081a0440c6081040841241702d00c1c1e40307039840b03000180042400b110681d5042201c1800009189826207085400c0281444119140b540b000c40c030813149154640080488080a0307408005203030002041000700e4080305800da040d0b87c00b580014001071030184081288200e241452410583c0d603903111654840d25400071191040041283d0b1082e04003008085040d2070b0301c4331002c1c960076800000c40d0150000914450b0420000c1c40d000c1c0506000340e00c48406150401440c100c400d4907410455801841900d080711745104000001580010214186040c188c1c03541c042d52410104504 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 68983644 1250 68982394 68982401
    0x3020f0d09061d0901030609050609030703020309091312092c010605090d050a080d110717031003050708010203060321090f040b06031302090a090201120c050c030a050d0b0409080d 79
    0x11012012101c600d4050f0b003079656145440c004c511402001c18201900d20384241410000780030350040b9801444002c001a401009541c1400c0b425900040035644029985d402e074616280060141c0610b40d215811090384a00301c04255a8410540284d447c2070244140080d100190040000c050038401800502d06c00c034000d2813180c0b0b00034803610320303406252a81401e100000c14212100300e000a401c070404400c5000e0010307082089451345090000c151140c0c040100d402e1b0750450100e40010014641110405081c0c01031504081210440340d103405845000b07510645040d0b11070711810f01c81012941210100c611080100956181408204810301c0721040c425015903900545400d1801e010391141d41c0550b100b50080c0c520700c40c0100060040c07140009010342140001da040210283c0586d8000f070000712261640070001500c024005001c6800c1d004601c8020442e0100150710a0217541c04409404806c181d040c00f044035001d0704c0100801c517040410700910104050000a00c0001a5032 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 68984894 1250 68983644 68983667
    0x11b050418180507080105010e0121110402220e0a061508041502070501150b0901090521071502060c030609060d03020a0516080601050301060303080402060307090302090c0703020f0d0906 82
    0x2c00310b91800b0095616a42040103540191109a554100400004040760b01103401851031b0303402c6106200c541280360604e42100000500745236000342d000d10160f1610303030485031803049880d030b00403203036501c4c801100030340d5031038030032088a07021b140040f4050300f40707510a5108462024019107030242401c24190b511181c010410b60f000480c2d00111001a00c060006041c458411400000d0350003070018801c10201d10b503003180100d10301c00d0041c2515139800030140c509660007141d207003c00d0314060660b142d444074034400040c00c42c042c0c8840099070b0a50303101d00400f407000300e07002c0d00c800c1d0f82c91104425080c00125030b4154400da602000c1241402c101101c1900c550080c810340351048800d40f40c641ca0501c40c800c21040d185070400b0200043c2c1414400d03540074203000c4000b80480d928581b001059142c1c017800180c442d50700000407a0005003d106038800645d4083c00980c1c2e1031600e0300041085410410b400d60150184030145d54002401040c0254114442c0d2542c11140d800c0110440da0051900d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 68986144 1250 68984894 68984921
    0x90901030b180a080910020a03141602040c0203040e09060919030239060c0c040216060e06040309090b01091503060e0a0606030c0203040308030114010e0d05011b050418 74
    0xc80c42c031032511400c1c0065034501d130140084039038070340c000c60a0062206001150601b15000003400c800020382c00441c000100c0f00e0030135220386400c00c28288241c990400c1c00029802460005d41c5184c071034010020340102c030541c61013200b00d40e46202c0300948807401114003007225049820758601584941d46c01001082c0240304a88480211002b00e0f04124001c0c06000840322800402d8007128036107103000c83c072024056030314905000300034184a80e25400d03001c1c610304c940d4000c642203607002038221640c8030641e0080420300074440032007215038030392400382c405130001101000b020502c007005000d034451004060b074841e40303280c0c80c0150404054003055501f5042540322040015180c48440000340038945180001a00502c1c102000c0c08032640d011048056410520040000c0b401c4030083d24111007013002858055804840100e95004c0343d50302890740250b15040c1941442030540c4424451410703508500b9140c4580d54058610b401980b20b2a15011100c0080c1100007000d40c015200c482000b = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 68987394 1250 68986144 68986171
    0x512070306110702272427011d100305030904050603010e01090c230108040f0201020718050402090c031501030b040e0a1b060305040206070b04240b0f0303090901030b 73
    0x240d034000b03000d402d0f10340c006080c401d1701d052402c1c0a00d2040104607822219880c5c5401c0012031240c4100c800d40c840c0301025200f1000f14410054025420705242d021409010000750b05684030000e100880316041c00840b641c490802c00034113a00380034070040c0140e076003100045040c031080800b000041c14006003065055522900286640c036424002d0710302c100d1180340341c584d0260078514402d409982d01a0700302d44002440e603c4402c0d40e6005800c81ea046174110359030801110311400180e10b058100d5002100500b040211551030f5a2180c1c055406903200300ca052200343c4400000e60072500090300c0e0018600c192440501c00ca6000ba8807160f18100f01420100b1441d60114480c0d0525401190981c0c041020003180910001c90303007500009804d284c01c1c10041402d09401041e42405010002090000e2001c00328003800b840808490060050008180c503004d03070361740781c80040c140c00d030b01c141d020300007000d21100b09140200c1a0b64040c40d0140416045078695101e480030424040d000b20010480e = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 68988644 1250 68987394 68987407
    0x90103060216080d0605030f0601050904031b20041803200f03070605041a0c0a0c030509090106180e040f0f031b05010b0906030d0c0b06040e010f05060406051207030611 74
    0x5440107013400f1195048002040e42c0f4020505013028031098035440943c20010060207140d8424070155000b41d05450199043c036403070039682c0c011441d050700c0501035101c20044203042c0101d20349a44e0b45000f041c2e40c1808400f2014505061420503c1e0700240440c00700c80c490312480c0e0420441c184051500030132156160b50744240a1708581c000e000644015490b03600300004c3c802c003a42000d01004008180000c607140081c0d2000aa000e03001d104001c001c1c07040180c000b41881601660700c4c0c080010708000705d40d40d403140041c010701528840702418000c510000a503000c41c0c1000c45109540013010b804070309642e640c1d0b071100d45010326021824007114522030400d0320500c80da06140284602d00024005580ca0104554820000c008a00c6070380890b5500304540d0740400e46c4000709500c0809001d003030310b900c4005800740c0500f1750220300940c81c0009011401c03016800240c05510f081c1ca08001803501e5805000200881c40002c03002507101e02c0040000540790f90200b0900003114038820304010 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 68989894 1250 68988644 68988653
    0x1003140c03150414041103031e0d0e0d0e03011b0509041d160306140105010e04090204110706020d0b04062904050405010e0403030c030c0f030b0d06020a050309060114090103060216 79
    0x1040d13401000010091041084104460110354071004001200118202a025040c511001c50b10381c2c4a41590280072030004c41e011029000b250100c80e51406503003020820101c0100f0003002284138a10035801c1c040d00c4a914501610010100e00c2244c0ea41c0d49000208000d22014002001107202c0d4242c0003500c500c0000c500780004078007600700c1c1d0f05a80d1020b10751308214081d80c00303e0b920b00c0603803035028004000d140c1e000401000200c0007076802043c058144e0001800401c803001c01c4040c1c00e040080e0040c20062141d00401004d00310520800c00510f400741844200d0301c2c140545104400142c110800d505610545119400d0140314020314207500c034004541505d8082c1e106061240440061004040d01409100e28a003560300d001c2041c0d41c02090001c00107030010a81034181035950554490b03945855040302e40306900250259556104544003c1c07103a402111104154001c010020459240000b4100b4210310004e000c0d441507402d68666000a40c4141c5c07040d4052402070100300c0024 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 68991144 1250 68989894 68989901
    0x1020406050705010b01020d08070e030708010c03020a020f01050702070303111207080a12090c0b0a02010603081201030203060f060901030605071e080a1112070e06070c0905061003140c031504 84
    0x400c0340d952402d84881251804500b99101021410b065400407814441246c0e0301c450030540c00403d13031030404070481c1c80d03d000ca410410541c002030070079420007051000b41da801d90000d055040140c3c0c00c0715082d10840700c0702800c8400503a10700c1300582010804101103031190700c5041c0c8a00004060726030303500191020100d0380e0700c80c51084420000200d04900c1d8160401a070104c0000c210005019601c40b40d55880c44400d558001d0407400d450108080017514401d500c56006181d2101070269602da507116087c18058003480100d103c1e00c40d001c00201c0d82d4107400003003802108080e0002140d030b42159100c00c050b0000a001a0130040125070200c030051107203d050201c0b642c1911491000d00344043c000041e0b0b405444030f4401c54100700700304d41d85a4110844503511000741d241c91420301c082030000074554481d40902805261041d0b0f00480d0840d5180c4c0020f00800040345c400c925115846d8041e0203481c0c2d60002d00a0360070075500000c1c1682d040d40010341e07118000c1100110182d90410004085 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 68992394 1250 68991144 68991149
    0x1509090f03030b18070f0305010b030f040201030e07050307170105010609230f031603140d0c08180a09020306040c032c0f030a02070924060f170f150603010501090e09030408010204 79
    0x36403030380e003040746151f0540700312400b40400103c19851440d240a02c01e007000c8000d0002410565a907a010001c0d14050180d0405000003c0c140c0d8107042c3d48000064003100b08190760001d6500c0c02000107076540c056102c0c2000c0780c402e000c9040d14034491039010718950102040c0d1541108042802d40e100b41ea00780160070b60031503070109a055150a60505592070300c0442248110340e440300d19408100b50b0881c07000000c2a6002c80700701d0b522071584450009000c1c400840541203980301070701149078031468000c1c40c8584003d030740800c0004181601281541c46014011a034039088903502424040085c45036407640602004554040ca1011040e5107140d01000403400140c010981c10f014039001c60048001c00b104124510560908000c07240410f042c2610500003484464280d540d55180551142c2c942e0380c0c4016101c00480c42d1004108155040c12200c41252000c0400458124586101502e069620613501d180308181031068941000b071001c0c4c101001444244000142502c003400140003 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 68993644 1250 68992394 68992397
    0x61707091a09090d120e12071401060315050a060605030105090402010c02090a060519030305040b0d0612081c050c0a05070204020c0a050d14030103030219020402070c0602011509090f03030b1807 85
    0x60384107a13100414000300110807584890074800741d42030410001441e025511642e0600340e642ea03145103894019407070300658180055003800c000105000001d503580c1d0030441d1036082840503503101c0903d0f01c12035481e40151070105409000500144c00c061406c507520900c18104003841005540001d0b00c5241c00322070072501c041d01c90109101900341924800e17114030211001c0d10301e0300c2c10340c4e4010785580198021025074400101c1d0380c0d51020244d030000001050303800903c00030301c0d829050410895008041c40180e0171354500104e03030119154404c00d803040582200c1c0a023025503410b0100e503903034418502070f6409030702400406500382c824050700d411240b00f800240309840a03030001401a4411444014100d6001d00040002c65000308400b4060646001041e09038821840041c0090040a80c0a49440c0c3c5901001c42d081d0340550095281400a80b1458102d9640f00801d100340e8a0040c0010504204040120300180c0280c120380003006000b0715000c00b074030701c2407055459498115104170 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 68994894 1250 68993644 68993653
    0xc03100801200a14070804090c110a0303020c07030b0c04050411030c030604051306090c080705030106060e060a03060e04080304030806010804051908041805010306061707091a0909 79
    0x14040098024005080a40003403040e0910114501ca986a1900318112201800180741146501c01e0315007103000603007000340540764402410030b0121030b0441d001d550039851070802d01e1540b050181801c154032102400c014041080c003a03408401039004080015003034800c244d00400018040100d442c46400d0451041d43c90740d01d40b10401050318903064082501600c20405e00030350401d24002c50b070703101d482520080781070380300c491480e07407444124880944818688416141000740c0c0115203802c88283c98101c8203401d031100205803c8800d82e201f842c0c00f1035040600c059284c240080a032071003990307600303001440d283d0b00c050010141004032422601c0d083c00004200c105074204503426003244007031074071000034038050791800c0e80d50807803512108080380c030a01c1d00020032010b402144c0291482e00c441d12481000c002561001e45820300088034241d003000d6011030343d905420304500f0a00d0200000f400c2880c602008000100840304003401d2540000302080b542e034442601c01d5005403545002030 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 68996144 1250 68994894 68994901
    0x204090503040825050a0f0905070e10020a0c05030f03070b0c040b0c0312010f0b030705070212030a020f06011a1207140307090501030b030703030e010509010e09010e010602070609060f0c020105070b0c03 89
    0xe6030fa4844c80c1d00002c0c0309040a13102400040c1c111042c0c3c0e001e450074410009504d8840e10015140004405240e80c2e02006482d2003a000650214030840c0481c810300c081e86d18503032901c2c10181c03150504860381c0300d16402445868003081c00160900d4202d240400154a85a00e44002d141d003540700800981e1150310020305a2003241c4c01c0d82c8035500401903d10f403684024203265410045200c050980810010042541c42c25544c50100104001103540d084a540340a40d100c0a501ca03c1c0c00034100e82240181000001d142d0322800000b10000c010044c154500104100034408640000c0d040c68104200303202c540c583c4454010046000380c055468403080d440c684000101560008104280240c10403482007000039041074209210081c01d0804030746945002004075039541101041c44d5200c4540800011158182058941603999603401e03a50749a80301d0b01c040c0e900c5001441001c001a0782011020a820f11480610301c0c00d030710500d8402c1c5000e0703807034840400110003540e07003244050000050 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 68997394 1250 68996144 68996203
    0x303010e0703020405010c03270305010b01140f030f100f0303030209040606020a030801030b0a0209030307080307020d02070e1b2218110904111209030a1d06030402040905030408 78
    0xd1a4030400c03a10303041d0314140c00c020000302000c101e1000201480070769002580c000902c1e10380981420b09000000520643d28104140607100c040030300c9012502c0059602c6c96101d88408a03031440c6030a00e07c01e0f14640f0f54101446817400010204802c1070910080841d9101207060f04000640c001d40d0056102c401e5201040100ca1190b40500d0556101c45081e000203904400610f044035046100c2c2040342d690700115001038450001404e03498000080c4a00030001003501030340c003c2e400c036402c03540020546d4206036035030b00d214000c010040004400040002006640e001a007046082c1c08030b0804c204103020215407440228a00d0a18580c284240500803407401856500c500c410f000348045211080c10301300d188500b0450301d00603501c030009041c3d00c1c0030920850b0b0b4840307030014002c810b601d0442c0103e0b03101d402029000700090100000041500c521a03003401078603130024952451601c980d0300b044020b0a9100c2c1c11103190000f4003000841982c07d2040d400940c4a0704484101411200407 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 68998644 1250 68997394 68997419
    0x315110a0e040605090105030d08061f021513021509060d090605061018090e28140d05030a0207020a1e0810060e1603060b04060c020f100806040911030609030301 71
    0x11318081c4c50032000401c40c0f81d40000700060a0b138010f0130883e9081c6c88010200ea5000340000c41826500302055070b10004c254005507002c11102040a07680c060f07240c109500c88403940b407840103540a10100000b00425950304010500c1c40c030000d000d68940198074a03602e0680e0380560f0181c1d0015515002c104090424802c0c40c1840c03185c038075100f48040307a41c858405050555000f0558400c0c0d89508900724038030304200c0b59a8a0000e000380290b09482212640301c1da9540720000c560303100c169844c0d2508004c000031103030132241d0140c4580741180d807010451340094000354801e070f9001d00c840390000b501803001c80e030300c00c1e0039404241c203031011a007404441072070454405100c0c61350a00d821003c0101912a1004507009070f0080903030194200d110b070080f40501841c1d0081e00010300700140c0083e404d60070103c08840c00d40300f82c804a018201070020031061030144500000425008070000e111842c00307621003206a4070074803d08039112644e10200c0d181003c12200b1014940c000030043c8041e040604 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 68999894 1250 68998644 68998649
    0x121050a0615080412140405060d021b0d050909060d02090403090515160201080601050403050607260603120f040e010905042607080307050405030102031303030b01030b06040315110a0e0406 83
    0x1003c0d55981059a990b41a001c980b18400c01000071300382d140308084840070202c80040a004000507120b14030410490000c1d80040595081060070491144164001045195440941d5203d090902c0c032481d082c40610a03005102179400050300e0140310042c0e541d1003165015502a03900d82e14450300341010b00088100540300d202d00e1000902841540e512600125180642e081c0380c058069140c010042c0c40324051500010000c4c02a83d042160040c0d026001c1081002c000d046100140ba4040c0f4403840034a0545210350540c02c4220403610004005008161556100103501e10303056441039a1140c1840c20f802c109050358a480500041c4503401c4c1c03050302d41040c81c800f80304e901ca9500e415030415200352400141103110100004003400c4c000d4080e107004160140095540303103004200c48080c000080e100300e010902d0003030251020b5220303125041042c00e01514082c13425041da147e54500e030790f070012900105034a444244603104001c8001c0d290386c0e07403180c45202c038425100c0100015203135581c = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 69001144 1250 68999894 68999897
    0xb28050103050607031104090c05070b0106020c0f0402030106080a0911060c010618020906040e0603010b0904051c03050907122109031103010b011403041b0f060206060303030c090121050a0615 84
    0x4802000521006c81120110f40c1030a5001600d00680e00e01568240104440034105250500000a5240c2c000c1001100210201d55030000c4444040070230040f8002130003440f0024150800040c00344800750b00011306107000e90505050080d21400045141e0f00c145881040c80e5101d21003002280e001d490740300706080200ca8203606092100001c20b0b0b0b58061886105984000040410a151001c0d8007a000001000c0d044074410714042c108142d41c0e01140441110000c002c11800c0701d800d1003446850b0144010303401a1a007c0c1c40c01044cee40c0c0e04000d40100b61200c10340b031421072440b00c01c05400301c400c815941e11a5201540756040001d20600c0902c81203010303034148201c0c3c05050ba03201c20000300c1902d2105030079031242c80318180508541c3d000e200e00c3d4014422042d000c24440c05012001c0300301c0304207908a8402c0d43d0f9110138503450340019aa640c1c0c03000401d0000042943c000c1b201e02d400c0c0c039640340d90701603016a01121082a5801560710401e015030b1103c0600c100f03540345a541804540d20b = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 69002394 1250 69001144 69001151
    0x50603011107020d0309081e0c0306060f01050903010f1505190e01030303050c070c090b120703080304060e10050a060302010f020c010e04050a0207080c0c0102010c1106040b2805010305060703 84
    0x28940c012007034820b80800a2062050380058402c050060240d030014050600450b8058506507451000c078031200c540380e5103140f0a4810a1110b03250000780c0070300c00e100c05000714400395002e80054035550803288600740d15548503510b4a1030044980701d40106511303106a0050f0f034030303c2c0c5410b00811b907103010b03a4007445a00030300b000d2200400050050341100c0c2d142c03400146503035914074580003e000f815401017000314541e40000b1203480903040308680d0031701120074000030020808043d541c0c2d0428440241206d0003440040c0114002d9031000700700100240c03e55001082201c0113800b1107100f20f40c01030602d60313074400c00e00565030f0214200001501e14001010303403003001e00c0068500d6100d0069280300d0754980303000504090080c3c050f40c2c2c125500007510707034507007072414895611251108837040c0158681407030017001c0d03446449025000200d68010340f1054440d0b44503840b02003001400102850200798079146c01d10001d50030500c0356001040000742d02d5041d4903082c0d00b4000301608074401c1605 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 69003644 1250 69002394 69002411
    0x40507030c150e13110c01150b0a12020d06050319050607030b09150103020c010f0518070b030a0f0605090412090b0423040902061204031b030807080618011805060301 73
    0x410054184928408a1381d2035000580d1901e07010252010030110304d800003010500030300ca00015040036982d060003040c90117165440d112801490702a42c042c000006042e6154480a166550700070039001c204001c0200f401d640300d0001c40d1030480010300d1401042c079407818400070300000340111a0005058074040c030544811100190003003002070809505107082442004440e8040c0d41212203051045000780300c1840340320880700042100b241c00c054100320404043d80100c20120b41c0d170003502c8003421001d0035512003407410b1004019190b00903030800c0d5120381c046402d5544405040c803c40c40f0307986a180f40c90030303103c00a040720f1480d800103070705032001d11003800201030b0b551220340100d090707065002e243c452010004006c0d2a01080180d00201300149511100d920a016548250b00075212114480700c84510000f4600035040003400040b4840c0210b00420712500d00180c02600c000c3c05401f401e1a503d40340705402e0b4081c4d100c2200c004402400100010150003040d50080b4210000c025030710 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 69004894 1250 69003644 69003647
    0x90109030e0603061201110913050402150c0109023106030201051c020d09050c1f1709010e0d0f11060603070306020f04030501020a0306050f0f150a031103040507030c15 74
    0x407205601d40724650100c000751940c0c403145440100b1000c1d000003404903469580a100107548107603613150207222010602580e114507802200d000301d6000d001901f0031400001800055002159220307069502d070004000941c1e00e2161640074103868400c0030480c106294401115002e00580c2c402a05040007820000b503a002000e846000000c4600f108180b20780c50f41e614001d1094000e8500740503e8441080b05210300006c1c1c10300c041d00c0076541e00c1684080308102c00f18004002d200b40002648400c0c030551100e802d0140c2c0740d000b031078007000819000d51444015090843d019400300004101102547c22507906c800c40300c0c044071880000e081c0c1c84c1020fa003c252500c04074040036002c2900021030380401d05524040307600664010000715121003280f140100508418451148030740e00000342d10409180c20007000580b040300070b04540304483c0d07200b8200302a8012054403014155120722051600c1c80c01e400075846144284c0241c60410305510340b407040c0700c1854112540c0790481c20207140059 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 69006144 1250 69004894 69004907
    0xc0306060402030a06030215041a270a080a1104051509060d03020f030a02010e01140717040c050607110301060902030c07060527010b0f0105180d06090b040f060509010903 75
    0x860300356805039803696100034810140400740c1c4000c1d008031262900c00e4025032a4009002541c4450a00822141c034101c0d21881c28080c02e45112062486418094007032840c01c0c80c000c46d010740140c01500c000341c1e01d543c510704003910300c2d506031003560950b00c220b0401d1806201b01c9501c00c1c1285214040402c03060b002c5800d08200500040c024181d0800050074903008211f2501c00d50088011170365201d82030000280a45440100a0b103103600746515150302c04545000305200b01103a075502690702070015660285058050000c6d62440400311001ca0907445801c0140b1516001e503e400c81ca100c030080c20315085a45a42c46021114814002c3c03000108106049030240ca4010101195680f1031407060160340d084410840c402030032140d0303044048030042d00008040c007400c0315440c40d07801040f401944c4612810540451360201201d0340c0c0b4075450000f00c41e10380f490040000080550081e0b99640a659042c1c0d020360f024042d42d51070f101041b5482c05003c1e4040003440007031001200c16900680075 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 69007394 1250 69006144 69006151
    0x70e01030510120f0506070305010b0706021b030f1209030301050603041b08030d0501080c03060115230d02030103120302040f0302010305130501091b050111070b0a02030f0a030b01110c0306 83
    0x4041c1c0790400314249914401d618006402203082400e06007802e0326007581e012503042c01c12100c60040710300182c45240284100340c12151424250780c501641d0f136542030001c3d80004601c5030f40d8030b40340d0600981c552081000d005041c42d08903510355500b45034100b00b40107100050003078880ba401040103200b107444410035213070415408500a510883d60800001041c0e1280d08503581520001c5a10100144950801030403541c8540982e1358004940003415220b4400740030340080e25086000140245104200720017103c0b100001809105109484001059021040680010790044014028807807456072803803800b98181000c514003481c0c0280c20081c08400d10001e4107240c1c1d25000102c005000c00c0e504541c039580100208110071052030001c0d4448015140d241030b9481059021070b05502880806003603105020040440b1483c0107003102c15070340582c4103002180014000e04000094843c00307000700845584000c01e01c3d5410f1800101b0308502d1182006282d80580521201c41d10701003501c0742c0 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 69008644 1250 69007394 69007397
    0x1201020c030922020307030f1107030816020a0503070b0103110d1505040c0b070b01080705010c020a030b1302030303090102030105100309120c0c05060c0f0d03020307090b09011206090207050c09070e01 88
    0x1045580e1820b60791282008103081c000f4540000704020405a040d440003181c0001c48030b00308000510b1103248a2140100d82000300407c0700d0602191202030130943d103810104180c4100c2c0c40340742841d134a181c1141c000034412903803501d041005108020010202c40c074440300076200a503140c0c001ba101ca81280002c03404d2544266505c4012800f4041c2450046001e800c107120415134441c0146894601c8203024491000d11340100c050200da80d40c4a0106050010707002020600454110b860b4030f00d0300c0c01d01401c1c1d4690241e0140d40d440c01a1420f101542c8102e184100050f140c0d85810103024094455550860802d8940401075000850a0031600b1450600e03142959040d40c06280c1030401000715006654007400200b100c824040d0000b40c0703c40c9030300b00b1f10309039800c403d180007040e000c1e4082581c0150104070401801c0c080000c4150103821420014503100403180308a1000340100c2e0707a43d40018065a8000800c9000c0c0401041200400942541d2548052600391001001ca01c6c40c10031030360 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 69009894 1250 69008644 69008659
    0x4030807051b10060920090315040305070309060c080406030c1101021c14090c060a02010f06030c0509060a0e0a09020301020c0708060f0928080705070b091201020c0309 74
    0x15803107403040c800d440080003415401e80d16500d6030b03410981c2e0303010340386039481d031071030034840c001c5200c4c0102e00603443c0d07142500c0182c4200d104000007404090b0031130514150103210310035202d0501c0304035218590146004c0d8580541d142100e050051100215401c90b60a2010540c14600051802e00031a402c480081c5000129860800c004641c5e000c1c000d1036241c0c10b50b0002c0703891060310704800000b0400541106003040421203222540380302240031070b14131040b50003201a24a41303040484c014551aa054800002c0404240b0b000d001140c2c0590026a041600c03aa828450f900b0000100d68001100315500e009c0249841e250b6402540000c1c064501d681d180c2c1000380443d203094050b540c0b186000c038240c1302400e40300c0b12030954450044541500246418000c62010035010902883d010000b00c18045880c08046004081c2003a00004460200c8100507440100700b003800450080c198840140350b54005040070420100b1403880e4040030383e44108101c400b1054000f04540c500007042e0b0b00c45 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 69011144 1250 69009894 69009901
    0x708190207020f090412032912070906180b0301050f06010f0912050d0305070512010605130305010c230c0715030603050f06011a0702030a02040b0a08030d0905010b03060906040308 79
    0xe2001050b6065003a0000110000c2c00708028080c02c1e0407096460555082003031202224032908000180120780032500040c108c2d06449007840390300c4459541c0103008a9011641d243e00b0b070401c42e400e40c0d00078035118003000811801a0301c1402200c0c00c05200320020f005030304283d50076003804503001e007a01c0e05000307084544002d03a50003203009000031b00a07160088005507040c00c040380c5070601100c40c1c40000f454040000d2959004005903502d0a03002440d15043d603080c0641a642a0f2140341c41c0049a20495000000070b8024020300b00480e21654403020710102e4100c3c142c03405031601e410900080d0301444402c89085001500703408a80c41c20550310720b05041e4500c150014200360700090000c1c015a40d441d94407410000f4440e0495545056215403d501e0707002207420750149400080d07160700320030205005850681c00c00d0312660700042c4854249580d074400c0c0e070b00d581c0c020307091200015102d42d41081848004c1c401d40200d06030941c0607101510b01665a241c5034600200010140310481011 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 69012394 1250 69011144 69011149
    0xc06030f150f04090302030301050907050301030c0b0c01020403080a0315050a05030a030305130b1807060207030305031302031204080123070e010c03020a0c0303080610020d14090411030406050609070819020702 92
    0x840d6003000d00980300f00701303520150400035140ea0003402801d001e819540c0100b049a031040d01101d0407241c00c8112410700030f040c00740486041d840302c060311000390340901006c03011588200003486100c01d507880000300305107003001c08a0381c000c5c694130481c1308603c4c6500400c0107440100f1102e00c0603074149000107041d50754800820385150f220b0380190040344418200000c1881074640b203008a8603460444483c0703580c0d40300481e0b45a505002c0200010410300c082259a400c002c15407003654070040030740e00a08021041012203801c164002510b682d128407101d0744100d4140600d11441084000c1c442042c98282d04c0500448242155141040400e000842c1814401e0100c0040729900003903c1306800d40c0c030700b0000c20901054500c40d22894070400c000c00124000141860750151a440d05060014580080d03400354210400e101c0c1c11544601e000d40490007410001c61050380320302d074005440d041003010310505102c020300341010b100c40c401c10312001d603000b000796481e206030001c8096502c00c0340744003 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 69013644 1250 69012394 69012409
    0x80304090e1f020c07090c23090915150711010c1401051315020a02071403150901230f010308030a09080c01050402010e100c02060f040b0703030b030c06030f15 70
    0x81854600b40400942492298a9001040c4c0c058030b0104075107296481d000b0450440d1107000f0f501c00419010944c40c40851b0406e40d040710402c4a054909091a80c0c035030215183d190200c0f07d09002540b582040741d01481c0030040c00d8002d42020061500f440d26964404000700503482c40241400800c404560412500300070b0405840c504070000c0c03003641040d1400c00c00b40d81d86500100c5103040f800e4290b1011110031f200b0740d440ea10066006121107450604401c00d8964038490550b010302403426604401900c0c9012503002e046003600014071941c480c1040c8031110390700300c12648103180400034400140c20020540e41543e400c140c00a50360348602d600500280071000d801002600301098403100d010041d40070f2445103000383c8640107141070307600030000d140780403480795004120b8140058000d810024040d2100c000391019662034603440741e502c440d40f500041c100710002610307200a40f0031810148246108004261241ea0441c1000948601c1a940044ca804030026000d005500ca076601c482 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 69014894 1250 69013644 69013663
    0x50301031e020d11040c0503061309140a110a060c0b16020118081803010605060724090507171911150a030e1203010303080f04030905060f04060e040501080304090e 72
    0x3844581d969025190243c0040c04c2602501d00c22440e021120700000d004008486c4511801010794001d10803031392803c0001c2071442d130107645540b80301030b1101401c141041010a00341c06000c000c06615070010030040d02e1f254130b4100808101129285d14005441c0c802c3c0140c012401c0c030420080703600107040482c01070a40005040361081111064010300c404e41d0024148141803201d03403a2210035040a00d0f00340c1e85d2a1144941200c03042244030046901c84880c40540c0e4180d08402d20081c910900c42d6054800704807060760305421081d420410680020045000306090340060311095a44c00c04d05941c41802450280c5910182d801441aa6590b2040761800038080c2d80229103400c50100018010301196145030300c58800d0368200780b40424010150b03812650316070346001c05a80c5825580d00041c002070800c6041c000384800c0454160f41e40d10281008406d0301480d1510759107030200003041404120f00c0c4901540c0703824010b100e00798010080b5000e0700c4e08d005000c80c1d5100d80c550300b1480e008108 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 69016144 1250 69014894 69014899
    0xe012c0c0303040308030105030d0903050601050d020604030b01060203220e04020d06150b1308030c2503050604030e0f100e0907020c040e010f1b050301030b040305090306100e100303050301031e02 86
    0x2d0f020003005689130185050347c1302a011100c4000b4130300f2085d20381c0e181900000d042944044010401c03894400400406184094400380c10075a0301d41d1810f525071020380000c805078001188920141110200b40c3c0c10952082a524100c00d1910b18072000403100540083d00404191120740c0500060350880c045a0640d60800c3c0001c680d64084200c564000c9048403000424840002032261400001d07a600c0358a040c000d01001d0106096809010014041c00035650020303110000210f038041c0b120301d00c07032402601c41105040c40c441c100130104980e4044140320b001544186801143d21203040c00d8204400c2c2ca0640883d1500c0310264601042c20100c1030b80141071800e0045c4984041d008015400c15880091007130306803500d0707040860100e41c81d1510015100703000400205405100d1150002e019003041407030a44200f020905040040f03a1000300c940c00001d003008207029000c507003a030103003003051220501c5040d580e000f4458030042c030020f4040b920b1000c40d03900c0d0000a013142c18001d90b00 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 69017394 1250 69016144 69016147
    0x3060c0c0807030306080d1112030403030e10020a0816120c051b100515090a0f020405060d090b010803040503030a0809010e0604050d08070203040f05010309050c04020f0d0e012c0c0303 81
    0xe0780340044c0030b05424014502c45000341500740120fa4040c0600c9480e412010002d030800e4028a41c4850150300010820790406450710300c50f007040c8030103005040307003030307000810250703071196a07c201400061003d09504000e40309907000043c82a40312a00251000400001089081841008a65a028048211074481403101014100110000b4074078500d0b22142c206000136540c080d010301c407042285c01225082181480010701001940c0d11880d4070290640005041544420100700c00340c00011a603059165980f84100c240440080b160f401418000d000b58985420032021988900502c1c00c90010302942001040601c2c0080d00a60052110081200c0b41c0d0b1400f42880c6941d9a00742d01000046249030b4081a06540f001c400c179000c0d074052580c00c8c001c40e03207090011401042074003402c1c0e406008001030185e0316a2207000500c580801d954017039480e8460220031408a072950011114035030314000c054100311150801c04120340a51784456101d0a480340b00c01c504041a041807503616000 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 69018644 1250 69017394 69017407
    0x403020609070609050108130212061513050601080705070318060c0201020f01111c0f020a030b0a061112030705090a06050903010606030917090303160c030c15080a020f0d110d140c0403060c0c08 85
    0x801465541d0000089401c379106d07a0140300540100d4900fa24450300050f003041c00980482d01900003031116600c02d01d002d00d0800280d154030703a05161207801003400142050319a000b0340d80d04101400c1e1866102c0020814019401190840b502c94207500c13180310b4a0906510021540a9000c503c02214000e030030b540e06da87d00b040c008c004182da441440d200d10303120000404e0071442101030001c00d10001d0000c02e0b0003603150140c501075030030040105040103020010550039886d40e0801a00600d0310f9200e00b61103072000d40030142960081d4000070701301403800503850046070742440240ba03041101c1b0b4840e65181e1030381e0042401d6110300e07035030003400100c0300301060200702030043c00d50f040fa8010800c0d83c002da9103450010000032101141c1c2c0002444940105080025070780c010008010071702401c44c0740c420501d0400c42510349040040c10b12003004a4ac403801020140030348500e9200904882c542e61810724081062070280d0b000151459903942089080039016000c980e40075a00308070455110b05 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 69019894 1250 69018644 69018661
    0x120901060303081623220303030608030c060c09030c0316090c030b372709020d060b06120103050d0207080606031b1305040302060907060905010813021206 68
    0x3480d0712044000402060003e400401e81c44015075042201d969602407009405542c1c42c84844905d8a505503400d0420505e1038040c1ca20300403a500408440980d082203240d4240a4121012640100c03140c1d001005101030054000c02c810b94042f521043c001c1d140c0c03480c080030920340110050b80542510860751400c2c20056092040c074101c4003055030600148103a280101c013a590300054803500444414203802420380403c0190407440c0195250742c01c00c5881812042640110341e014802102a403000001003010120447c061164a100c042c04964281e5000c42c3c600000041d01130302072a07030352546091a982c1c00040310014603000790402c0d6556120f0138590307143d00c5240b025001500c58100002035030f900219005105190003006090f0f54410380000c01c3e080f0041042040d032080107409074492003140c911509020728003e9008000030300c4c02001c12807030000305400c60030602400342c40c02c00540e070780816459403049007581c0b99468a602c510200c0c1908142c41880a41405084200701914 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 69021144 1250 69019894 69019901
    0x30215070c0e0405070501020a020603010909020d05061602160b030f070201020c06070f08060a0f0b1315030b09180a060f0b0a0603020a090f081e0f070f05090f0f070e030102120901 79
    0x20b13401101500e00d0103542d003005a17500c1c1c91070a0002c3d040181840104058030440d400074480e03030300251042082448030b1780c600342421001c494289001c1c20750740101c641c06030304201004104003a00e01c410201401d0080e8000c2c0ea00005012050012000c1c0024182501c02e4050315803a10b140f42c101c0e041030800ca100038000c0241441c01200081c28400060380d14500301156604855040f90000b51181c100320340c401c590381c03110980c13003d0300c00c0d407010005135000700500c1d4031030a09041c1d42c0011654110000c04c03c1040c405401c02114004c00003c2681d60100070480460081e407203200024102001040d140241220409480e0300852a180c001071464050300100508491942d54020050710b40141162240080c024420641c0c014100e219130449002230f02110800c1c01000ca0f00744c20307000c3d1a180d261001d140c01c0454a510008410007082c14403071240d0380c2102030080600c18524207209030000102c1c0041944080014600e890040e68500b0340c11512a00825082c0c540c6c80d141031030080b40038 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 69022394 1250 69021144 69021151
    0x80a0b010914060a150e060d06081501140112090b1801060603060b070605100506030c0a020c040c02062418090609030703050a390308150a030215070c0e 67
    0x2a036007005044000c0c0c16440840b0380c455800100b080f00c019091041c075403003032108800140c0c28080d240d107030181070365036aa02a000c500f44c90030300481d00a0900c0581c5040000740d0f4105203030f08410030018000c010144090102010007840e00510b1070780d0407102000500f20800c0f010b801c00240e0b4050000c00450a254504040d01d824024001c555480a08500b20303140e61055240c080028403041740001c3e901e4020b2900135003081d19030145075498000007400c41c0e1007035a51582103500010300c104041d030140840000305400700d0b0104401c08401c0001b0f901c4910040240702d080040441340d144210308600081c0030303440f0107400300441c140104204541d00030152501d05d5640b142c00c000540300d880000403920182e925a80345818000351900a80c1c0c00c1e0b21000b038000e5481d80c2e448203521050114590400c0381c0c030000305610500e240609000d02245030203400b14004403100c0d401400191100000310f41103a80c1912240c80000726400c03807a00714010800c0c010184200118000b40285146605600 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 69023644 1250 69022394 69022409
    0x809030c0d0b0f070906020717030c1e010b31060833010f031403090d03091d04110d0809060a0305010f0609060905010e0409140303190501080c0409030504080a0b01 72
    0x351982c4d03400f525441098030034600183d000c2642030000a00310750000b9902c000343e41c1200c1c1010720a049080c103082051115088620300401640100c0009002c1e640e017420060b07407058051000c0e5048480d2503800748800c880940c1d2407a603c80d11a01960b840000103200503410707186080b82070f000c83c94441800d2404e202c1d503031800050702c0c4401170f04109524101d0300d0303030f940c0f81849500e550b60707889602c4060120501240824040603144d82c1b10070616400d0359202c1e50382d1542d1741d814107001c2e03400112002501080d00e02e1031400c006c00101c000922441842c0308454031810240c403460010624450b4410280d00141c011a4108040b42c040c1c104a068500c4074003000300c001d481d824125031240180c41020001103e0040030001c650085180d207940301f102400101d0081c0b13150b00c070b04d0b41444c0c0d003018100703e9a100100700702d640d4041c510441c0c0401c2b8450000d0046516103000d050b82d82c1442004c2510403a5204426010180103108850040130010b0030345011b968503041500d4250800d00c900030707 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 69024894 1250 69023644 69023671
    0x40b0f0d080d0c050909070f020f030d0c08130c0e0912070c0f060203030c030a1802031f0c02010605010207150306050d050a02010f0509031e1f090507060804020d0809030c0d0b 77
    0x2c03c800d02030001c1d6014810007030820105541e409508a42d00c2ca44412400305500450001518028060009101e021031260020441c4154048010901c802c02441c140034070100820031400110208101c504031240c0b40d4076041d0b00d4842c000c95034244400c6854590074280300141480411410b1205181200c0741410700740241a035800082c0d84a20044a501000000c108001a414150380d40b0049114001c0003800d040c0c0c00c21940408d00e07110062502030003036010031540c01100f2400e8058011640c00510003448003501c3d01001030f6845110f4080c0e00002000c1e074203040180c6220341d000e5030080c94000e00d003e03140402c0d401c20135198111000181c0c00690290001d40d03000e4001c000b2200c0422003e03008000c2e9010f0305002949418010364100310b07030300481c60b04210307c6000c1c002c000c2c10315002d01d0000441e4480c0f85022460650690f0055061040c0c4038104400740ea101b10700e8a4030650022030362030355110b0400000e81041c10351003042d81e121650388600d0060010345100288105900c61606 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 69026144 1250 69024894 69024911
    0xe0708010213080609150a02031e19050c09031b030a171314061c15090b01020c030109050c09040f0203100204092a030c030905070803091518040b0f0d080d 68
    0x40e5206c09203255920040303091000414441a41580151707408400003642c00c42c0760350001c18126006a00351910203d6582851120820703444a00c1610b404c8200885401c1c5406100b1020a0325408403000701104031032410311107120340e00d041c40103480f9154044000e445540b04e000814920fa000004140c04101e2455404512004000c0201c21144030041400b414045401c0c480c1c03641480700c0c80c003401160303196411006442c51422852000c2e2420001c04985211150002441c0c500c02410f0940700b1713818604102c02248000c41c1034114010140c0343c0d0035880d0354034182581211a4150001d400d40724070380e82000224403d42c081c0c01580c864140910070050080b00b04002e070070355624031526541e80980540301590095200700403802c0c550402240c00d03540ca880d00c0e41030100a510140c0160000640306140349003900c0080b1021820000e10b60401d4001d00c004482880756040480c001e95807034a0480140e80e9041c10340b00c0609004210200b1240d551400c05405d03040a1a520509402c00611 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 69027394 1250 69026144 69026161
    0x2030a03091802040623090901090b180f04020d0311060408031b090109090b011202181203130b131509080c0402070f0204180b0c0c0606010906020307060e07080102130806 75
    0x2210221801651600110045c1c180400d588104400c17540031b501c00c04000d0842d0a4655842441c000c0100c3d10000403110b500c2000d022403040c0030301c11800ca051141d0b0402c2000801c1c007010941198064521800c8c00384c0381d140c16201095104c461516504c03030340b0104010050000001e40c411140d1036a8203074400a403c11800b403034044c2d446418041880c0f4a02806012030940c070036a00880c0500d040300d840509201c03020200d90048100c2a120f0b404400c810610341405090b0020f9005110300561928000c5802010820742d54004d2100c071340000180b034a829070f00312540c5d10242c070188641c4583d903400040003808900306889044254080c07400c0002203850f00703100b0340300c1c040d400141c05c1960307a400b40c3c2000010200d8013591140059607003240c001040ca07030203c180c411000c1d100030317a41e5410b104e003410346801001000d00b0704000c00c40d141402030303550100c192000d00d5030114021407184041c0d0040342c03c265051b0020010f941c80450070002074684881040100c0e40c0d29800d80301c49403a05203d = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 69028644 1250 69027394 69027397
    0xb040b0123030d0e3105010605070206030403030b01051b010c080601050408100e070e0702100b09061c060f050c040e01080c06030c160c030f1a090d05090102010902030a03091802 78
    0xe401e40c150841d2003030440140c00340786413107241400180701c00c0d00c0d0070203ca02c056250080844a04415059950010351903659201c0c40c5d025290300d050a90820700d555000440500c0014401020180c035034185018503402203059401280f0b0375440c855024a0780343c2883d0080000040b1000059420008a04c4a5018100f12420703500c07440090098081021120f501a1400e410501c04520943d20001b600c02c220740c4019000d81040c1c1d014000c0303004840a04801e441d141c1024620900e00901400001d640b1389622484080c0740032503180b15803905041c014003c21400221070422824101002000885030000b4403ea419040540449980302d13a0711035074403140d402034540c01c2001003021501d104900e101400c2000c1d40c50a030340b20001c0c0c0d41d0391837124031112680101c030000c083c451709000b0000d0100140d50741051a50724440c42e498000c5496503105100c0f03400a040c060300041a0085920039000310201c1c580140c1110704492003407a004004a400f0311446038401d64907201201940390500 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 69029894 1250 69028644 69028709
    0xf0e070e010f020d0f02070e160207080f10090201030e07080c210607050304081b07050418020328020406030807050705150d0f0204120501091214040e040804030b040b01 74
    0x90040c5003a80c1303055002d48003d0010f680d40d00643c41a5100051104402c1100d28428441d82e00d041d030784100d40031000f0740b41072941d4101d5640d0790400542c80c001c1c82400603000c407501d1103070b0b000410341420314001070f001846500b4a00000303000f01e60f0041005072000902400b09401501c1c10141c03500d03961000c0d044000000c1c464101a0480341c0803a41d500c2c4140059a0803078060001c2502d800462082d80180c02806206141c40c0e4001320300802c824a4070303201e40f81c800c2c401c40c08203141482c242d50010f03888001c00030005d124400a10201e60010b450505113518195010b0b000304580c80c0c89040406a64000001c00c80e6503104a02000c40c171800d000103424004686420001d05004501c1004005000c1501251402d030b03a017031100107051100c02c04110030950007071000090005580c10320301c4103605a04a03940c00d11040a03000c80c402501c50b0101c0d000c507207402100051365111031074074051a00c52a44050001103061042c07009200c0c002c0440ca0480b10806c030305038804078000d0288186a038580 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 69031144 1250 69029894 69029897
    0x30f150601031107020904030323071824050f0d05060406080705090103080306041826130504020d0f020a08090606030601120204020a090302130f050907030c030201050f040f0e070e010f 81
    0x61001100504011b00e80540152082c1404109501c03000311101c0b2150344c0b405000c0c1d2148045080c001c1c1c1680048401030b20100000040c0c5007541096944203441a42c01c01460109400c1d0b52030b400034070301c034100f6110544015048155294583d00c102e0300540820343c2c0892145140200002e00c1507000111602210780141c51240700fa0300e10b444001e41078000a0600750050b48440315401c0f905001095621054814080295a1103501d90802c0c401c0110402140340502c00b0000108030031030862035442114000c0320003503550207070080000040c180421410304120b002144c6a1003245c1c0040c0510311481c900e60482d00306996580406035200d0080c843c000220044880c600e01508160f0020803d40345e10b428050301183d940d0340410300d88003020313418100f032550b070303101c22001c0c0c0045004142d040141c0600614982d070840e210001c0d00c5c0d00620000781800340003c4c07000404021031090751300500301c080c44101803640c0c3e00703240b5041c04011510b540c0060702c145d07400062980661800c00580816 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 69032394 1250 69031144 69031147
    0x406030b0d0b01060f050d1107060506090405280507080a021003050f0a0207140d022a0f01210e0a0c061d0f0f04020304150b1c1b05030f1506010311 65
    0x4c20800781c424055801ca11000c005040107111001641130158070160041c400040b80e41e03c1050405000301c440140c542d52203200802c007444040345002a07490f68144404000c003081c10003500c2224180b079109031005066010700d100010340d20401184000301c070f0f4000d4074849001150340c8000c500700e42c8215014403200d241e450200d03030400e445034042c1200e148110041030580c00c01c1c0420314902410041c40400607441042142c8000003400a00b002c540c510203e8044043c0210000690f180d0183d0200350400500786881040342030504100541c007880304804020482c07501b414039864002021080d035449041c0c1e1000901c10b0700c00c02031040c3d030203000c9220404900d41d60b410007041e03050b110041e90b448a041d00329940150f850f0301c010350040b840303400d00c00d0740240b210f5a50b40c01d840714800c480384100012100d00075005050004900c4042d03008480401d010742c01c1e0303a40b48013810146c0002d509441a61240d5407a244001541042e0b48182042034041d69201c0c001102a204002c500840c600d00 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 69033644 1250 69032394 69032399
    0x305070512040b07180b1c110711040e01020901080a05100f0b07050d0912030e0301061d1603060b0d0c02190501020a02060123060d0b04090f030f0201020a0504050d020f030d050406030b0d0b01 84
    0x7c8141500c01090342c1c580118000f00d4207a0880141e81000c00c050399400c81181ca405401d26261180e0504004040020750500c4a00000a8003510380101780d596039a8490002a0310500040800d4016191581c80003442d95101c1000036000d030070500b41101c40c0d03c1a40701c1d143e100d40c001c00d8000c1c00c0310010401c008800e2126a0121146040328412a81642d00c0d02d4012070141000900107000c40f00c0c041007070084d40f4004003400014000241c1c07843c00d15242400500c00d01c02100d04a811001c1c4030400480c4183c00340100f2450001c0c038180340c0d520f4618100c4600f0402206400400b070b240c0e242d034225801a44c036025a29a450fa034138402c5020b00f018480014803500707000c0c0c0500320315080ba8400144801001c40440c080d90703100c00c8211404010a02d4410405410035280f0328100c1c2c19200841c1000303040e80d00500184128051a03201e085070540200456440f8100c1c24682c4e5005004d45041c812510800740854016010b65400300c1e040491101c8903090882c020301c141d13608503030749455591 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 69034894 1250 69033644 69033667
    0xa0e040f02030f030307120b1e061804110306010201050718060309030311070c0e010b0405090a051503120a1b02210a0602040b0307030c0305040b04030305070512040b07180b 76
    0x8464035000c0303030903000d0f100d05118420414406188944459110b0040d401050080b020484001c0d516462240c03400626036520104940104171008405480d02ca64401d0210101c0d10341c03003055221640d000341001e6400c64420150409180201c40a800900c00d1752105c440640d40100001c540c00044160720703c040007110310076003080d030f6014081d007000941504000d50b003580960105005484407010a0170807c6002c0d8040d4a0f5401400440481400d1a003000c0c00602000b01c007814000c1c22130345501c003140340040340344407014036540d00074201ca01c0b1061100000320141c0180c00300fa004151300b000c040c1c0342d140c82d19500c900407070341c0140395000588054010190424444240802034400c0d1104280001c07014802000a0b018594046403603242a4100030b040d14080360002e010075052400b48400214030180ea55040b6a041c140070455980700c20040b540d0380a4141e0295003552681e05220922240c10419806022150f440302000d90240031070b084211041d208a80151604121100e03004 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 69036144 1250 69034894 69034913
    0x105060c21090319020111070e0a020f04050303120405070f030305030a0507090f030506040b0c0a0f0f2a05060901051603050903040b1c0b0f030703020405040206040807080307110a0e04 81
    0x4030895030603080808031000300e8034010040e50200c5040380701328400e106560304800d0f810451130322800248030140c1480a40c0058032030140c41c00c40c4441c0c012a0020b04e10302202c0546000e414060f04803a11250903400703040100a0566003039510f40541c00d0003040c0c840780c0c080381e802900c0c0c02d91205880c2d620f41001d20001000d0042029041080440002c00d0540c54030910100440c0100020280740c01c0c681410600500302800c510015802003140790102134204a0f880e0301e100d85401e00300c100103003501042d034454084013540d415054602c0001c801003202500388400e0640290116084c50343c800c3c9003a0708aa5041c1c4580d0304050025803c0600b1910a030000d0754080c50402c2960f042560760726044134103030040015030f14200368000181000402c00c3c85601d040300d000319004200f007210440440c2d1220800d00010380100d488100003410742d1210340c101e0380200170003c1284d070402d5590344100d88a0300041c20031241c105035002c2c050828030f026582001510b0311160206540d4883c2e0f0303280d0703d20 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 69037394 1250 69036144 69036193
    0x2271b191404120506070206070206060a12060f020c0102071502070206041e081005060909120f0d0b060a02032505060601110a020406080708070e0906061212030109020901080105060c 80
    0x4078101004081001030100302d4030892540710360003c0400e42454003002c1d00703002c0d00034011130444d40000100000c503511040e0103402c4560364130503113200c0c0015041c0380014008240105522a00004903240380300d5056008041c1c9500401e6000716a1200c800c920003640f16480c0040d61004060000b07104032000c542510811b2800a1000788101d650b844100b0305050b007c260702c850282d44c0c2c6041040c18286024299404000070b00a0070401c060324070070b030089010300181050180c038042110651896540e002d00080d1000a00c01c685030780102500039940d0348000006080c01c030811880000c442c40c00aa0502ca565125010b00035030740c3c0c2c00c03004560041d44c0080420180c4529946900561181c0c4507070006041001e014091140c02c002000b885d2840541c4000c001500c8201000703683d1001140311500807008445100813804248116464a0b041128011460100100010f0f40364603550081060240a0b2900002c60781e0b20020810381d4054400b01c0c5d85c5581004001034031011070550005c04 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 69038644 1250 69037394 69037427
    0x1401080d050a110105040807060c111005070c05061f0510170402012c1002161203050c07170105100302090a050c0d0608061503010203040c060c02271b19 67
    0xf040315407034641e5003960380c10340c0c0540303041f00001661001e2141c107000d170480d41c034a503091001d01c6245080400360b0300d050754005d030707040c903aa1400441c088910035802c514019801008603845420b00c64a981700c6c500711500c80210509004500041d18184014124400c400580b80c4c10f600001c4048001c0e440c40000304101d0400503000c0c1000b00d40805901004001c0700e06800409806c50594144499006014040019903020f540d240d040b0307020011591054560b41c118003003003240107203000e070385901071079051800d2401075080102d42580c95114450840c1d03140c80081c003264a8078803000c00c0c840d00a0001a410400d2000040d000c03012a8100d01e81001180107810300c3c05030010340314801c80d0f081e41c10040c103c0d0840014803441420404481550381c400324021440c1d42403980c3c400c95280361714401d840600c040301100c14159604d10071400b0b114500701c071040715400000e1b0140340c0301c14411a03001682c000d000303a100c1009444d207000d40741c4c1d60700d5410a01003520780c2d070641605d5410751805e4100 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 69039894 1250 69038644 69038657
    0xb03010611010b060301150e01091a07060902040c080406060506070b01061b021009050306220b0a0e030d050610030e0d0c0203030409180b0f0405030a0e010507170406031401080d050a 80
    0xc41c2e88030313000110b0007060440321503030412454080040c200409152554100320398000c1c00e00c0920500e00c0d503244c00700c0c402e0208640d22506403900c48081c121205010354000d2904960000c02c41d00b04080303502c41d900c16441004404c1d211010440d042c0a4601c0c058420300c0c07480c00500c507c5001c7c10b00c1d006181c1c0c125102100e9101c1550008c0d0b1321a0710440c003880015280f200800060500b004216085842564900009a640c00c0f5007002c0e1903400401a00c81c514090100380e4090142d0301c8080c0c81030b041026030340d64203070580700b80313002d441c0070b45405000342c0344501900207280c0301f8490742031202000d07030140c400b03020318450440e8103000121059070315000c10040040d141c401072040360103420f000d00b20181e4158090406801d103c100a1069200c85024400c200000d1008070490300b60680608000e9044110100103c913540a42807004010420015807180801409405402100d410795003c0c0410088c1401d8011042428410300f40c5644c04000d000c058980100054400010740e0b14011 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 69041144 1250 69039894 69039911
    0xa0f0303020c0a0c0801150501050f180d060905010516030506090a0b060d020d0b0306010602160b0d0e060a290d020d0215040609031109060303030403030e0c060703020114010806010b0301061101 85
    0xa10b0846903561045c00d20340c5d55250340100d100101b0708520010282401c000c2d0401c54070315207a0b0010f104440041d1310f984284038922819035601582e01440c41e0f0840820440d24080345400760080ca001d484102c4440d4481c089082001d12a00405104801c064003244d20307501c03a0300b400c101a05031080e4440e400b190038460601811032601c0a0252200c125a001c40d00c01a610141410f194040e00b202d41150042c4100141c1480c980740c61404544014a106a960b1880318011005103c91a00740c20140a04003d0140315040c0350040114100080c0600f0004031304140c44205000c50900425006001c514410000d490000c01840d4580e00141031b41420810140c041c495a611540003540031600410341402030107011800e000c60b0300350645840c4564104100020781d00e01000f80010101901c84078642c18200081c8400891550090445500c40c5070601d80a03001e4501c1c910800804601c07100001b6202e0000540e89048030500c103031441c5076909204c800c40344100701c059001519034171540103 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 69042394 1250 69041144 69041153
    0x150b010201021e0904060803120c03060301020708070303020a03050a05100e04082104050f15270303010f031718100314130204050702060910091403070602070b01080a0f0303020c0a 79
    0x1001c2e00f20203070394070030b0744c0d8402c0350204021683c0c10313040029030b540180300081c290229900425000400003006a8803a0344000000b40a4400c03000300400e0b10001081b02000c01d0b070542c01414950b0b2807a2014080c5079240303403868045a20848040042c8400c90804008414118107032039005030190f1200c6280c5000807640201101c4102107d0007054420700401c03061010038059114444c04035005004c80c0000a420810712000c0580b00ea00404036240514100000ca011501c0ba03045000301920788944e5603440c804403808040c84180c5078461380580c071140200441040b40c240480002c40c0d10031040300300040c4503c0c1c01d0310b01491800c2c55a52500d8001c6000000243c0744160410b00040c0344181103841840143d0310068102c205660080007805a000404030741c00701ca0644850000503c1c41141c03c0403501d035083d5000ca1506804009005400e100f07007500200301d060300410300b080059aa0320341403a6a0007901e500504250485042480001c4c42600240080b5890000300d03142101d05465 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 69043644 1250 69042394 69042427
    0x603020402031512010903050301030b070c020a06031d01020408070e0606160606050f040e0606060a170f01080c03340b12040c0f05060426030c0706090e04150b01020102 74
    0x740d90003c0c3c114441e448030149030601e180300c5010032442c000d20900310b2a5030060910b00040c0402011442c4200001780350a2154110080c142d4000b070884003ca641c551001d401403034640040001d401c40340124071000031301402140c04850342c01e8001d000d213030314152503603407000380240c061940000104a2030303081041381000402c45c0c40c0a1300e0700040f1a4513001c2004122810300c0070701401581040b03094142d001d00816010761000046d00c1896031401a10b604aa85d001c00384e561741464810601400302d12980040c28506a50b07440d1308448d6090300d1300341019a40c18101c142d070917020f0a000741083c10406141c0e43c03400d4025040043c0c0b135005440310314811403501320f82c05203c00d038000001048103110300c0000a0340101605080888100e00b0207011886502c29030065003c1c00845c4050104410100c510111440d84c2c50015651100f01c142c0c400e5844204901c2213100117003e407078000ca6000c5c001403250303020390f07801000c10407075512104040b006410051900c07415950309114440703c40b0020013 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 69044894 1250 69043644 69043651
    0xc0a030503090112050c070f03180e01080f060108030d09020604091a15030c2b0507020601090c180501030c021510080613240603050706030203040b130201120c03060302040203 77
    0x1071501e803210000010710a0009500342c03418603050800b8000108494000c03a81c0140e0415030355003517a0380909043c0c0b4409650003070b04040c94082c040000f5400e005c08811410703160781304152203a4005554a550b5940000e006030700c1140c0042004550000350355001c000030b2840a8407071340c1081d680d15155003c0320002003401e207842e40d030300c46081d075107244c1540303001c1c1c2000302440700c07500b18101a00c02c0401c070f00803da401641c1e104207031034050f105111820b2003075511448180910482c94001300081d200c01d0207200d0b10f110f8509198604841c1070146180c1603105a107841440d003060703d0138004601a00c043e03180d100560041d000300400359844da60034544900103d040c185000c615286406250801c0186200c003030714210850000028641c03001d01000c3e07414641800c1d030020040060200600013580003c10364450750500250240e0941c0107540b0890007403503c442c02e640c400c01c00b003110185000e002030003c0d8403141c8080034400380d9030000c5103816071442d002400d552690f001ca03080380c0c003ea = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 69046144 1250 69044894 69044903
    0xc190c08030a09060e0d050706030c03020d02071a0a09020312090105120108010204082404061508030301090903090501030507170709050d06020c070b0f0d02030a0b130c0207290a020c0a03 82
    0x288400c0c401c4c035402204001c0382020a031401d8941d004179850f055120605401503404140d11045008601407181e01510424103035070b5030456540c0650700e03000c01040c00b4440c0f035011084807400040d048103110703c9a400c0352038018018107500003941241840da584405812410f0240500c9444803a03503113001c3e00d50103052900001070f80c96040403180351418141c01015400120340101103d019502a503500e6000351340040c0220385111307142c0080320454155004158036100200c000a2030175140e4003d0341249000e81c80300d214040d15100110241e4000311084d801080e00c5512500328049400c990326801102c0b4604000040e4a82d400030380c402e00c074010142d0751580c0106820300c00c00b10030712004009044d600740051414100441201c140c3c0140710300c05401c9540440000c01c1940d0a4203e40305100008001c048440010b0716100000d00031010100014419032102003450b80206400c0d6940d51400854103100c0310521201c456141d000b2990242107010b81d540034040c58582c00d010303901a5114 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 69047394 1250 69046144 69046157
    0x703030e01020a030510050d1115070b040b07080f0702031b0c0a0e0406110901080c09040b040501090906060812090d11120609010f0b010c0b07090b040b040e0c0c190c08030a 76
    0x71141c44541b1035880c0c21480c03042443c071155800087c0028800030a2a205a5034580704101e50300c110a200e0050180207081a015041008208020b20507068802c00f102c0d221601583c403140091451514226517200140c1d00400031196481c0300c214140e0745c60b403031440446410803040804921200c842c0c0c0e01c42d0121b0fa001205000030030010340900e410b48140411414106030701340c0c000038954000030744003a0030408005a07901c6180c42c0c44d00200c01d00e8101902c02c1c0400d5030364940b0703080108007404042d20b43e980340c100081a4440049180d25080f08001407143c1008400c01c100210603008540855001540d246003195a40760001d01d58401b1400c440517244034a007990255007580c21500d1185040c5107010090b981e96038002004003016134200724841501c1d51020702c00e48401c000c036040403243d02c001140004041c0000d80041c0181e0f0039031040800507460781a400c0c0d5140c011004508a29084000c98070301c410210000c20304458041d60100149030356400c80d060a5a201e1058440000e00 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 69048644 1250 69047394 69047401
    0x6030902011d090c03041b0b0d0b1504090e0a0c1203171003060c050c10020a030e0606061206061c0203070f020c031506030109080d1a0d05030a050703030e01020a0305 73
    0x1c0002e81c0d10960b01d08685010218606100000c10b6aa00101060450040400030a00740400391a02244c1a010055585c082640fa00f804501a0304810b60b4102000d061a4001030039040640c0303512600c641346503d207400c2c00d060070394502c09040486201c00d40d9200702c00110010505e0380c0e501c040101030064044800500c6801c0040c0301d07801201c100070b0a00c2e500c4080c4a061200c1c91808822a900700800103503040034048221854420182544202e04c50780702c014141052030303801000d5405181d10104240e0541442403620341c0c004072209603000209022120f040c0910b0004264803000003031510303190560090003400d002c1c001900342c4d00441d501108021210b6003100c0c0042c1c2a00b410300060000801000000740d980121000003107003c048640400e0702602e0941000841641c0004140d4440c0702080302d02c4018049504440700c0788000751051020f900340100005482038105020314a00761040304141d031540e005d5031040b0105a0790701d0003100309000a02c0540034520580e54003088071704 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 69049894 1250 69048644 69048647
    0xa020307020a1506030c0b0703050403030309020a0302030d020706030516120903020c060304031205010605070f023307050d030203090d0302031012110a0503030901230d05040b070212090609040915060603090201 92
    0x503c0f60070814000b0303000c08c200e1012030b402400b51811607506140109200c003040c07000c84e0302113546920094162082d0000304010a40124800e000c2d108241c0c1d04001036a1406039942d00081030700185004240d840038454400341c2e03d50008034505004e80100d8034841d40403000b2801e0381d4000c84060b00043e450210200700301030a070051070300400d00b41c82c3c042d0410070345031a040c0d000f12000500074828000711001213010040340c0002002000b03542e20403078085130106035940540e48822000c41e29401a20300c5a02d40600a209803405082054000c0541e0000c440064000b0b500240400c80c60008040700058003c0700e400c40004002c0c41260700484e200300348024000401420380015220342c000b403081d000c40740d03488142c20740c0b4080340d2483c4407840c100308104420584102c18041003002c3c100300c104410b0180c020f42c03450240007107071300300d810007600124192501c0c0a01080103034824030400042409151681140d104c1500030404410a001440d600c4002c49540c6c0e0f2145003c6a2210034070000c1d903 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 69051144 1250 69049894 69049913
    0x1a060903030f0a021e07030308011202040608030406110114010605030403081504050403050408010c02122d030c0304050607080106081b0d150f0b0408030906070807050d02160501030905060a020307020a150603 91
    0x71781401c0028601c0900b550740c003a01c4040140030b107080c620180e194082c00d558450300401c000b0140d42d415640c1c0c41c2e4580c18005d00c102108034007010b2035070070000405500c491240006040b02d07602d54500781162103d64040714001000307000d0540c00140046031442e65913480c420f8601642c80703600c03403951b264508185203007920566940b680c1990414000e141c40320301900f00712400640e841f1484c840952801d02c0012102030b03407180712220b0010100420681c4000f80f40114042c5005130111b409590303909400700c940c40f80034081c9400260f180720116440440c541404800801d41c071012504150303031545c064007111703903881480038001848003040010107000b141d2a405040c00b0640d940c541030074008515035a1095818050150400103801c409210064080d6121a64001d041d1083e50100792002075903a41d200ba09070140100e070850002d502e6000e4414910659030010180620766100f01c03229000703410080c410b00c00d5007c1e0711100350015441e030b01e842d000c54189550001d2a142142004841d6 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 69052394 1250 69051144 69051193
    0xb0403050f0c160f170c0f0102030d0203040b010e010b0a14160b070c06050606090f060313020a090c030b040c0806100207122001020a200409080408030705101a060903030f0a02 77
    0x650071701030b84000c2c00c800c00300b4100303c602029260a1803201040004034514400c420503510310505c04404d000030440c0458134a4100c07103900b02919026600e9421543c0d4505c903065100c00402d0700c40d0720075602491694050300300c1072034000c2e015030442c28a1703c8407070200c00222100c40001c1e5840d1b00e040c041101b14170420750070800c151395180c00c0a504e83c0218811982c0030309074038841d260120004005607441c808420003664042d20443c0582c0d03072846598083d02d00d100d02c003404607040c201076030005e06152055000c603800998500c989a22800c05001e90414481e01000460086c40380120382c5800c581d203007400003481503072030488606000703c202038105158803100341190400c822050108a03003004038132030344030503a440040c2c015841d40050000c0004460003800340001140019000001201030040a80600160340216407500340c041c0c100c074101e01101d04598901e00700c000c80c0d428114040d042100010341100d282000080103030180c1c4d003086201c0e4006034040d154224035143c1407900c4040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 69053644 1250 69052394 69052409
    0xf0708030601111f09050304050409081309050613020d060308030709061806051222111311031302040906180302070b1306050a0201090b04030306050f030a0b0403050f0c160f 76
    0x5606026980d4060342c40da040c403003441180e00c4500030011b100080c421103006000c0204100602c00c101c4c9030001c15a0054004868040c90914001070a110306000d0144035010041c001680d64140304011002500508040c6076596503aa5000c4001044e06c80158060103d945402843d5864003e006100c0581000c008900000802c0c04110054112064880030b0201ca2220882a56400120041086c5802071601040d4240f03001c078003800b08104e613003141000107589010b601164a0680800e40c2c00c14074140740070120401c0000e00e590318080c0e00844144c402403000c601014a52502d405840744c0c40c0700e80350707418500c3c014402015010230200e4020130903045150304015900510700612590b42c490042840000140200514401c0d40034580c0300364404250040380c10300381070040062810707004080c05440b01100307158103441c002030101840c0741c0c094143d07001680d4540c0c003185d03a034000c41030810500502703000b184001d81081c002c107440726a4003076541d070b46186400d600390755104c1c183c0c0c020070 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 69054894 1250 69053644 69053653
    0x10050c010614030c010503071b0804030309050f0307030204020319050405010f0b12030301210605070e0301050a1401051e1e010e0901061b03090f0b03010311091e0c0f070803060111 79
    0x6003a03c011542c82000310003401d10076120380e903044068510002d0001005461070072a0444400c1051a6010307206890003a640c040a86032140107020551403440110340d8103501c44d030000c0005203031a400542e40040664080050800018520001d85500b5101101e9594540c049000046000d214400701c600040395012031403052204001c1d100d20040c010320480c02404c451003d040c02038519079120050b8440780400c46464181001403004006040040c400e5013010702140b00c2ca0424084e1045812102010005036464402048020401e4644605400c0c50011400c0c0403a5200c600309158545201d4444034080c2018000404000c88031805600c01e58481005002e4568052400040511191801c2034148841d04084e00c403c101503104840440080001141100303001d8050350480744141d2814607110b1150082014802c0121202048480c450185818070a8540760864004410140952500083c1140d07418203503c0a00b00782e0310300d2000000d00c155568032072110b0710882c007024080c2 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 69056144 1250 69054894 69054929
    0x90402010801120809221a06040623040f0608061804030c030e0907030606120501060e1c060c05040519030302100b010e030d02060f0702030405090601120b10050c0106 73
    0x40c00007070040c02079540c8140e00d4900c541c20000b0707120489141003401800a0a109041140c0d5080e41920403480d00341076040c0444400800e284101c91080140000d14981c1000d0801030101c070850000008000c920540041c4540715101d95001800030300f8640b403003408498209000907010010240035039020b2250f800107100310750f10805411350002d03810f00d080900400d15040442c3c1c20b00c259841158000c951030b09000d200e0750198060404c030b800710703160f44484541d41110201161402d00c108000700300c81c00402240c6181284014403100403917103c002e6481d0203610f88034102e840c031307122140206100040503c15858180c040d00100c0710000300c0305ca0b07414207587d0b0003900c4000003800142e085d81c45400b10f001582c0290401b96800d28003800309c441c07502902d10020b584140940d07113240301101000c01300d081d00b403021044034180e40e406000200e40303440b000c0045030003806502091f00c01c01e9a450110666589640c4800d00d5079070030741d881c59181c0c401c4001581c00c540013035208080b14185280710 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 69057394 1250 69056144 69056147
    0x803030910090303021228020c030702090c0c0708100506121c0903061103040b07020304031e030c05010c030516090305060f0405010209030601080f010501050a050303070b0c160c1409040201 83
    0x1d944458040c0240803032806150700e019406402002e80380038504c030400d820420401341e4a020402c41c40c44101c0d20354455030a040380b42040b0b2140d102c0b4a103240d00300708591000740c10483c032083e402c0341d42c0c8a022440c1400700c1801134141041504503034240e03041150000103030f8419001d2250000402c4802e8801d50694031500340c1e4034585403e103a00e40703001e50040f60040030700803180380c1d00540d00310300144004401084c00048981c4111030440e00808180c001c1124907200105983c00c2d41d911400201601303114042201d001c0c0410308048040201031a0203e000500a01900006e403541c0d0700c01041c2c3e410111801c5203580b12802c181401c02408110800124100150850300a031320880c5629041e207036030034050f02911540d00e00d550148103070000024100d000060720585150030100800959032030f9410050010388e1031180c1c6a0603482404002e010031041e4101980000c0c0303c1900c2440d1180d984031900408180c1d4001392100031024004000203100d503640030b400d2a0003121903001e1460b0a500 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 69058644 1250 69057394 69057403
    0xc010c1b060e010605120304050a1e0e06130204061107090c050409020313020604063b0603070c33021306110f0106090515030105040209060f0a050604080303070908030309 75
    0x1014000701d450755551514401c0030360041c0040c01c0c02514800f03125181c1180d25903070390b01a00c00d581c000c4205c00000035142e12202c141c0c940c9070700c907640114507191030083c12048121001c3c11a039446030502a40c0801c0248038801807008102c0364581c1e000039105020b1103410517125521410780c080c203028a014407a40c0c80402c840a451b0304000c0141c07240c881940f905600784004000031b400200020b80440e0054110355014000c14804070f0482d07a60b101124045003204450040d0803500740480c0ca204498a402c0b400b0b943d11004a1526031b0500d9601e440300800701c1d040040d1460905031030480c54640c0072000c03008055029191109515042c9548078a982e400d50a21170300b001c00988103605a01c0d01000c0c0401891000304100030b1041580b9030041c2d00c01420241c030651103280c043c080d24000381c04c060261a03c9140c00511a521a0380c59605210003204850768069222841440c0400c043d907a10780504043d100c124000d5031689042d2001400020f120341102400d07501c1030040200031900002c = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 69059894 1250 69058644 69058697
    0xb030c03030d0e03070b0906010e0a0b0d060507030912081905010f03020f01050f0f091804021003050916121a01030c050d110409050a03090605161106040810020c010c 73
    0x4000600f0140000649045010300c1600404d101382407010710169160000b16541640c1c1d9010040c946621464688130071141c1c400c0d031080d000040000d40303001140e09544425032009550901040c0d04440341c0c0c0d11090088416444c0000c00c5580702480100548010104505d410360981001b89504081c0400648141480020300c100c0d40499605c80c00c0c2d104e5000c0d00d04200d4410009a121500442c1115140c0c1145c05100d00a00c00c00485003a10080100011300440c1c02524400c05040782a00860103884001c02c85006841650310f0440c81d8050b07140310320000c000400401c0c198465a1500d120074544a124004200c0040401400420003041c20001125002c032032030601041c03240b40564014500c10f51099101e407520f4551018010040781c060400f81c820341da0940d040b51941030030745990141c0c600c43c0c60151031035651200040c201407491151540010b00c0d050034582c0c1d03030051300c1c0740411b50918910b01540106281e1110b00d005d02842000c04000d003020340101005402e103e00c0c08503000b = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 69061144 1250 69059894 69059917
    0xf090b0711060f07180f030201020d0915110f07030b06040f02030f0f04050a061103160f0c060b04022a0d0206070c06050411031903080f04021503040302011515030b030c0303 76
    0x4021502c1540104000e140c5e4041c003000c50420903a503512903400c030068600c02a130141c0115110455010321800003103096413a01712001d925400311050440f81d0b41c1c1c520b66400b0040c801e00f03440d00c810001c10841540154421401358845103060307010310081c0c81c0d0740c05001c00604d00501c24888140c0319101442d91040d50321402d0001559a41405403420305000c40c0a44000d00e00038003201c1301d000d00e50040d80f0485444110306484010981c04540182e542c507986d40c005403401d0003a100040c0d0307580262604081c000c00c0541003a1100da10b070490b0903800c035014050800918882c90b105030341803160900b0603190740081d003850319016070051f0901c8140d40000342101d90b268009810081d84260030f080201c0090100d5100386488000310fa044140c0c071000703501140c0c0c038900041803140c45141c4030f8861076020b04100c0d200812403030000c2c00c81e00054030403000d42d500c8448940d04d034074001020300e0003010000c801407640084540080d0441d550b1444260003600074031a60390705901c0000880380700581c47c = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 69062394 1250 69061144 69061171
    0x60b0a020a080708070f0f02030606030703110d080712020c010f020106030201020a030509180a050709050307030807030c03090b0d0b0f0904020f060a050405030604060e011107050706051303060f090b071106 90
    0x58580302d420352080c5d41d0700901c50140d1111480a000d141005210024400c4e01201c0446c0c030368000f0541e40d07001174800102541592114950070381040d0141d09030051080010fa42403046569900841c43c40c2458403400517070150683c50282d41c2d001d14003031640e040600007089000c1c21074000035126082c10001405000700000d1090341038940b000322504074a01480002130314100182201c003d05401e550490000300c1c14003000c903141ca4040348940440c3d610450b41c0d440c09995580545030f0b80b04004055082c404001030004810400317100903c0c45032210b0600240f0740380407004216200b80085c0b40b007406640b0380000c00005885217107000342c0c05e160488040b41c84444103601201c46208a40106400d801814107210402145400c40c10400d43c00c2e42c000d010000e07250060900034005d5010143c06980981000c21503280210010702e00c0d40900c2d02044d040310384a0b103807034054035644900d60101da5a40d121203418480c03000c9500b42c0104081ca0070010008060306051b55690000d88a645050701 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 69063644 1250 69062394 69062407
    0x506010c02060c0a020405090f0304140301150305060115110c1908070303081905040201020d0e0a05060c0f010c02073002040603052125150e010e01060b0a020a08 71
    0x2400505522607000b055075580e98200390407140c40780d103101400c80c01541018082598820003181e02c0140707900140c02942020300d0540310181c10141d84100720307015580c80b4080090540f20300400009140147c0003060351f540b40c040f101811440149808080001d07a00c80800840004500c0326001c0404407a0260024100150b400f10115030350300541503032044020010400d60010b0045104010340710182c041d64031929400b4080c0c940c00c690080c0180c102c031031140f8043e070080402d5116400b0150500c0045034a4134085901c03503000744459a5554404403259868410900031801d0208003032002d814030340c0c43c1c03501028481c0100c0c1a694803445d040300c144590500e5030112401e000341c000f001804400c2d0f07281001511400c03080040c01481541c41046051401c16400702c4d00b4005100d21100c04c00110503d0600c00c9441c0c00e0f00803921042ea5050861801080b400b840c02031000c0d441c00064444d40c4007921a084402e02c0d0b100f81400c0d10240b0044205c190040b03021094990090300a035079980 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 69064750 1106 69063644 69063647
    0xf020f07060e060d0b0307060c0510090507050111030c030301060c121b061d060a020d0e0c03060c0a050f0c0a1205031302100302120a1407140a03050601 67
    0x20342c1c0100040382c6007840030080840042c0d000700000c0000403000043d08160307142c0d0080300000c4c2c20301a4001407100900c4000300b84102c2c00e000300310f2155280d8405454124500c241810300100701001080403005000316155100384000340c9550703607110b02c0301510140c005a8141c455210341114800c1d00c0c1d0281010b907100307400070a00808030b80c10540e00c1d0000750200810b089940e288003981c0c10789018003001024018005103d000d6141c0c0c00300450a422160010844092a032044c1a40c40050300c004c075005400564100a90759224a039420540d0741d0310030031340300d042c1c1080c001440000808000c1480725011b07201302c0c462160138a60300c0c002c4446000035a6540c00444120000d0720051800d40003902c002c00b5142005810300d58800141403010108541001001d5141c024103503d4a104401c025030011103810010840c8401b10f000f035a05001d0f088016081c56511400310322903a = true := by decide +kernel

theorem cover : BRFrame.Cov 68884894 69064750 := by
  have h0 := BRFrame.cov_init 68884894
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 68884894 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 68884894 ≤ n) (h2 : n < 69064750) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
