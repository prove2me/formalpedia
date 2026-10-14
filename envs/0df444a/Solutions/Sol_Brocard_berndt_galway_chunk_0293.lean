-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0293
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T19:01:37.878359+00:00
-- url     : https://prove2.me/submissions/df99d2f2-c2a8-4f47-b217-ea8906684d5b

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 52517989 ≤ n < 52697845 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 52519239 1250 52517989 52518013
    0x5090a080712021e010603111002030a030903210f1d03041211060409020904060b0405100302090d06020f0307080a09200307080f1f090209010b0d02040e0411011206030203 75
    0x950812040400c0e2040301c0c4e5010300154501014007200700c000c03410f0307512000b00308144500d50b043c400388444106e50303a219142103d00081d45d40e1103491122030038140c555101209042c000c0c0d85540007000340b001c0d10403030349000d0001d01006181ca02d004000280c07034080056491790040840161b0508010000c600d400d04050589194200101c0b045400d950800c0440d0010780300c80001c4c00040c0b1100380b000da2995403040c20002030b95200c0e00139002103001031004208642d5500f2040366400051700700180d4500b40e580101d00c45540a01c2d000d0300300e07400055505031000403000210300c500c1555842200c3c0e030712036001c8082034a654034400391411070681060120700e00d907000300c03401c0d82c10000c1c1140c240c9560750b40c9007401c0220600c401d8074550822008031500007d09a44299414000d1208004240300c5600144000b5018025a5800301c07011036140e4000401e641203e029240325644c089043c6014500007141d00f66680526000600200304440c1000460240600b580d03030050140070002825 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 52520489 1250 52519239 52519253
    0x2304030f050106120b070201050f0c0f0a03021303111306080a080903010b18060a060507080301140d08070c170303060a140604091103090d0813030302070201050c031c05090a0807 78
    0x20303120544103550b844100280448040ca80003118520400c081072076450071440103402c4800050642c00040762030000c0100c4a40e141044130315110500303c0140c2c44080c01c07034084000b030095047e015401900f0320808002d10451041500381c50034100c5103000500e20004100080d00c00798410542d999011700e14050019003648003800c02648064000100302c185038000400494284881da400c0d8501c070001c1c000142009030310752001d00501d041c100d1070400c15540706046071205200301103402145089194181e510250042102600b101c54141c681d1501d050015040352244180361040d0400c8010480440c1c001c01901d118103001403801c0d43c610f14101881605421500d44164070841c03c01012a00b04034606c1031000549907c01c426480340b0781204124600a800c1d14503d041c040480100080307144203200c0b40412583c5881e004d41c0b2140e40748010703902d03030003009200042c9001c049020000c4001d40405142260000306007441a81c90300c4590907215060610080c04080c1c2c200300e0364000c100e11b = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 52521739 1250 52520489 52520513
    0x3030c0f060209090412081b030402190807090b030105180a1104110a120b0102010506031c03020706020a210606020c09041103031611030c0a061d06030a0606230403 72
    0x10760300589003125840008481400c02c960444105284800505509030f11003522544446231a9a002c51a000b400d0f08400500004200900c0b034222410f281d1080c11103450a02c004101c61070440f04400d403194000c10103409542d140303c0c025071a000000f000e80500c03c41e090704031510440a01000d804d01d0b21801c4900461203020781c0c020fa1101152900400045c0003010092072694031411641018070a034400c0d9124038100a046a040c24240032140e600032581c84101d11140307600c420210500c400c290064080e0120160a00344003141c03c0d50100d40044210f0940c402540304d135031440d080c104041003100c05134002c0d5801a0b02440d40c0078200d041000c1c1c0550018000c0c0070351216015030038002440d60b0302000741a420342c5c00322034074542006806001090990000c60150407007a54100c00300d12000300e144140400c0142040f455000310031216039071840c082c006044203550b4507200c1030500241c041c0d485241d0015803004811803100200e180c10028400d0f61000d50362515155803541e8440c00700b = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 52522989 1250 52521739 52521743
    0x1003020907110c03070807080111030408030c1804090c0512010903020601061818020a1b0b0c07020d0f050606031002040b0a0f05040e010e040b06030a03120f14040c090506060403030c0f 81
    0x114042e1000444e030380820180e03008242c481c0040a0712030030300c1d410b507007902c6003600101ea0b440002c0c01440f0004042000b0380e90301144110352540c83e8a40401b50000b81907100d035400380c1043c500400740c03081c0b00d0b107800081c060701d1054640c150b41241800c41d541c01c07154015005070050700b0500041c40603e01c00c0e003c81201030034000d10480034686130071342d540d051a400103405400719400101007071201c1d0802a1404000e141103140c0350080e074580c90362070310408002c250114cc0301001442c00c00b19512a5021103038140c200358611481442454040d50b80ca00985042d07100344111484164040428002c40b0309840840040c00c7c1040849401540d200344280d4208003403040502010807541001c1803494020511845040c2d007a040034205144600c8001d44024007903000314005501080d0060b0031a03500700c84030640080c48504500c1c594000b040600c20140c902660117040c4070074403150302c54240c142c6405070700c20052a221f0408110482c42184002004034544549040100300072011806001e4 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 52524239 1250 52522989 52522993
    0x1e0512030c120408250302010305060406030b0a05040528120903120504030c0927170a030f05010e041203050408040f1d0703020a1205060307050405040503040608100302090711 77
    0x41e449507541414550b29220302c007a800000b250820003248200107190740030042640e2400c2e6046000b0b101c6020348100d01000e410315807076030080358640e21581d2116005541000c84445c01d4181002c001b0040e14081e01c040d03607230b03224005640050300003c600e401c1c00708030496031038020084d00303641e0a000300c9044e10000c030502113482000008141800444403a40c40641e4595665a08620b01110100480d402c50304c1003914114800da4035241c210441e08140740c001020358119200342c03a00000040c2d00d5028120b0003200468884503541c0c00d500070500d000c1c440c2e002805a44e0700d41c4070403d5281d50446024291550a901c50024140240e00c000d402901600c0c0c624030342078998440342c81ca00c0d0254040024a8804140810780c4240d115403160003e00310b180c150302d04040b07900300034211048116030703400c0c840da20b00108185590410a0000800c006030040c1b00620703042c1041c507200c0d000341c070811010a810000140c44020409101d4060301d81c000e0020724a52030711141202c4000001c068040a4 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 52525489 1250 52524239 52524247
    0x50a0306180503160b0a05010308090603040c0b041d09060c0712020705090705030a0f15050613050307060513060e03030a2a05061602010e0c280306020301030308011e051203 76
    0x1292060001308604001038008800002c1c40d45090494901c00505aa21081c0352034011710000e158442100c142c0c00d4111030080e102e8a441c200646440e205a200c00099000054000782d03c80351030300c102503e40c1000d84045a183e4070904810344564044a802c200c401041004800040c2500541e00b0040410301c12540c410f03031644080354000c0419520032000c0388010082004299007409142044d00034040140420704600350420040c0c2d145000d0b852043d0f401040000c00104102c41d01c00091000504441c282c681d161000342a50f80f00082201c416404480007040660240c40c1d11007a080001e0015403500c0c12001c41110400409090782c0ca04484420000d5000c80310340784407264072402071020f00b807203040400c203454a01080d405004296410850f94080d880170215201c040d54206450440c00081d0882281800b07489520854510a001040100901556a000d181640e10075200c045007640ca42121008480c403400b209241107034800814011410703c02600003665400c0012039041c = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 52526739 1250 52525489 52525493
    0x7020d17040801020d0515090103021201020705031201090b0607240f0f1a150d020a050c0a050106080c090402060318190305070615030b161b031701090501050a030618 73
    0x1041e40250300140e040d03900803841d6003c003440c51041a8024020900d03102140c511000850011401488061f1058607505407290030060213404440f00c1a502030140c1e17a4a48448079003464909007030081d45551807501c5030600a90828100320380c2c559401a006110300500b541c01503101c1190788a11002c082e44428158142203c0d17402125041c001141e4081031260100602c285200d03010b40b041032080343c40c04509a01e075842d4004648100011110240c1d031081b8a8400356218030940c1c006190601ca42c0b80310034144401076009800340d804441c01d80ba01d60b12090200314111702c042d10040c0d4880c000700003180170081d01c18481425403109000b038840508078044c0080340c40340360faa400d40110320002a51401c016842c4035190500c181005980025420754440c1d40411400404c24030486100721080740074075014a07a40d024800c40b044802aa10741d592030011b00c0010790304800c0384c600310a00b00200b00c040c41801200d0581e000070b0040210140307140c45d108041e0030100c0c010070701c40e07000c0512180 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 52527989 1250 52526739 52526783
    0x30a11030a020a120c09120606080706050703090603020424090305030a03060905010803040e0f040606050604030c060e0901060f0f14030405060702190b011203020c090a0506010306060c020607020d 86
    0x4400c0314079a00c0107031200000c04014101e4034486030541003091911030b01c02003c9400846000c250380d552101f2101007851454113900030140c1c2d070000c0f01148262240028200e82c002c00038014207100782e0b203a0502985d03d0000358240c4c002e9000b410b0941d00080111040d5500d4210309110101041c07a100800607540d40b42c0500711b80c44503081c44002a20b5070420710440701c10303001d00ca00600400d402589003503c0d0204200d1084405050601180c0b6041e010030b042c001e50303411003800303414002c0c01c2c1c9030741d2035981c41d10b03042e8454540300e0321000c9080e4022240e510302d403131640b0904a0310a5150500b1ba0380b0308050840300702181380c481c5024003e0702102d007284c905440d130207503100e14410001001c0b030f800d0600307010385480f0f01c50b0f481208130007003100740c840056442c410850466000e0780303840c8111415490103900300403200d015603801c40038540802034062300c107130022030082d802038a08200e07007611131004884819003003002070b40011080000c900107041285111041c10f004942540a8124814882c0 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 52529239 1250 52527989 52527991
    0xe040212010b0405101707032003011d0601030905060105060307021f060e01080a1106090d05010c0e09060d02091f0302100504080d08091e030c070806091203010614030a1103 76
    0x150200c40b001c42d09002d41c0c2441e8002c0c1030780c001e040c1498068484040201503082c10014005410103481e5007040641c42c0b501c1c61040407541800c05002e81f2580c59005030065031030148030b180c1c0c2031a030100203e0142c2d40248a4407610704d170072a01a00b41e6038201b0080c024030f903001802c4d1400f14440c0d062000080c0030812210300c01219502da000c64050b1510000310901d800c1a00940c3d1503411441464000580c00a040c100e0000203540035038880646070000b4882621045010301107508065554800591040340082039940480388120349032603000510988202c058402900f110501e0085a0000c2c0307007c1c05e030300104100c848072403a0561640e0109200401d01c80121002c50300c00b0900307103d1850309010a0701240c1e8240703002d1100e40750031450741d0741d5180d0709440c0078030502d40c1d003404101c0c0c41c4c414411a0022507051040703030001c2d55202d0b40c4d541d9502c1d00715080504c0b80a15100313600100c04100840e4100d88403513546800340c2080c406201c0143d0b002a00c0d00032a41e548000640d01ca803c140051 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 52530489 1250 52529239 52529249
    0x90114090727240905100309030909180b070504051e0f060c0a110301020a0905040506030106090e0c0a0e0708071110090b071803080a14040b030406020306010f0c0b01060e04021201 79
    0x70005034400740c07544009191503100d08004d1000f440014091134031041d00072011742031249404a4280c80500741602d1032001038220100103814480048900429049503030076a610403003031201c16a07201e400450301e0380503034000c581c2d01031000e10040e022038a41d12020401800001d00300a6800360303003c00100158000600c460701c0343c006020242c14803031a50007402003214240d000b540f41c0290000c005140c9a51400384500c03899030f40c00860341c10344095100c5009406145010403041d40b8001c2c0c410b03602e110700b9000d0f900c20524a100854100300001c42e113402501d9645800e0300a489014060b41c0c1c040c0e041d062010a44910a08000208024055840a2070103882c811000d03082403200140b00f501c90030115040111851010400a503c140842e02400d0321407800006101004100e1010382c40307a503012174148134010091005001c12030780110300400c0c09032580e10002480d564281d0b04400d000b0300c06000006418010004507000c1e480c41181c4c0c00c4000d0006103446180840552070b0300c0280c1103 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 52531739 1250 52530489 52530509
    0x204080604050601060e060706050c13180b010e0a09090212010f09031704031d030a05100b011803050a11060d090c030209070201020c0303011e051002010506090114090727 75
    0x24442408814031103d80900420301c0d0003d034a01150b80031400a200e18200103084955074400284031645100959121042c0e0404c0004031980d01c0540b0003070b108a945400216618203120014250300401c40705400c2c02d4040c00e801078451400c401000141300000c01030b40c00224400701041c16902c00c0c03040300c0c0c500084003400244400d65040080c40504026119054010400c3c14000480c2c0c000744486813442d0445c8110003034580d0070303010a05049004200070114030624820070442c00240d009602881400c1e42c0d6000341d4a80a12000e03801781c2107200280140e009905040301103030000d914001c005c4405006149802c032002c598208444541a0a0f500312500440600440ca400041d40350040c20ba84000e6081510503040180c0b00c0c0f10601c00c620b5a03d6010550f0400480b0070781e03028009110091000c0e0440720301e004060701910b400c90f01940300d13406000000ca80100c5140442151034030107401e030074040c0d50700c520540d01a8075a61201290100803900d55020302503240b44039010b0202c0e030710 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 52532989 1250 52531739 52531741
    0x501020702090a0603050c1c11041503030207031a06061902030702220b220504112e05070803160e091501031401051507031202030708090d031406061c02040806 70
    0x806c1400c1ca022800d600d88100380f0340d825807030801c05085540011540120095a04100c494001001007200224110a050f2015800000d1503000b141c0407040f00c3c003038001d06c0340d03605005a582d003450108841869000c6400d000340400010301d203801e151110751500440c1e140c210a81c001802c070300c500c0360000300d0070b24841c19143e0340410a4010080450801d81380c0801100c0302d20f5802c4c0b13a10340c0101510720300e1f558400c0001c003802107024080741420000380040850210140ca070252480d4142111f16521001c010140000b41c4980c08403100319030480c080741d0858440f000854941d46498000f00204810400990955a584400107000701c0e02c5a4070841e000320040005015249881074050600f030100004000310780328413075640b4207000c0d10044070b581c0707070702a1400b502c40b1300c0d5404445011030b1000c02007004036a04041040d00540506003113400c0d24a1a039030480940e4480b481d0031aa2070647c0300450003504040002d0402e01c10000392040c5d440c1401c0d082ca00132a00326a00c0f201d00c5500040c = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 52534239 1250 52532989 52532993
    0x50306131104090b1602010b040903180608010f06110309100302041a0403020f04050c0f0310060e0301020316050a020a050a06150503070803070209060a0e0f06130c02060a02070501020702090a0603 86
    0x3091441d03019042d10180300c5400262070790740510784000c0c4036481c44800ca074450841207100b94064205914010010031070301c85581002402c614038100c0400c0a00005400464100d0040300c06c3d40c102c1f114081c9100340383d41006c2003118466007a0354004443e2105001d880900d9841070b04194865110390340058642c0d00e0140b040002e42412508e0101c4080104814805030f126208610062002a00d0226854840000382c801d0751040044c060743d034900c0441400035025416046200f01d038260ba594000400060041600300c2c802034940c61a49402d49440818540c0184003416044001d4010f42c1c2c4c840308a6102c0c3c40c28222011803c03500d0b1640c883c0d0030078916600b03e0000c0040c7c1010703001410254200400c50f6a02d104003880640f14a50080000b0716903a81c0064100162840d000c0d5040a81410344030440c660306c0649840303105500d6500d2000c6403010030301c580c4480081d95801061680c0f070703c3c0c10880c000d501841068800355001c000d01000758465045d01801144512800a0040d10714 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 52535489 1250 52534239 52534253
    0x50d020d02100c0e0d0f08030408130902090315100906180f0905030324100203030702012913090b0708010f0b040b04030809030106090e030c060a0c0203040b070302010605030613 78
    0x504103640407240382164403000c507584003013684085407095511110b5140700307090a8251218000780200b81c03450010801c010000c201010b05460007074000003440d030700e85500000062740100f8127016055800404221a00c0f00441205900a0011140c01812603190003404003600d50761f402c04c004150140c0c4034640391510a1141034440056084100700c4800c2569a42e40c803844040e200c5400840324805908058050105449104c01d00500082150a5440000c0e4403500112107400140d4a440c003c3c0e890580391900241119003014140b601c014800b40c20080b06200322680108010f80c2d441d280070004060281490041120b9210592039601d0500003e0200d0400e8100c0e2601d80c0c070a000421000f1000c609540982e9800090152900318041c0828010b1100da44801c2e6402d0a15a4040114101100508c0041c2e0480c059500a0380c134990040e090740c800c0b801940050388104020071003004c4420182403007520a01c008108181d607100001c0c60008150ba200c200080d0f01e050b018200684 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 52536739 1250 52535489 52535503
    0x50f0306060d150b10030501030b0717011811030103030801030c060f0e0d0f0b010303080a06090b0906190e07050a03050106080702120a02100204170d110307020f0d050d020d02 77
    0x8800030000c92820030045002d800001c8070041c0b0f8000c02036111514034031030350810003907500060401040c0d03108031800100900400c0c8000d4482030284008215100d03c00c58508128500c2140e801402e0303440c00b010b00001c4403051194150031941c0e19960010b04139420015170003140645e9550545506508001c84644c5c1e0176482a4144100011103a10301600070707103c0b40c00c8450403152102c92656030306040805000c940c030f009101228100006c4101130300090041c0c0100f14615081082c43e4407074204504a030000210301e5809035055002400c1c0b8a009010003090300a20700020700b0f0551340f480001c11240090742e0080104178003003800c0340160b616110b154010410b80c60200420709014401944500764001d28603a0f4900000b03d00e003880c2c4c000c00c021144448800001c41d07869030f8039901d40071407500c1c000c0c00c465680150920302d00120b12800340c2c92014034895010314a0041d80e60300700080c0402c40907100d40c00c050010a0031010500c2445480c41c4084903170050400802401802810458 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 52537989 1250 52536739 52536769
    0x1e020a090b03060c0310120c0e090106090509010c050904051807060306031209060f121b05031005010801150309050a020a0b0304030306150c1b05060f04030506010b030403050f03040c180605 83
    0x13414000c101a44070342c440b0200c2100c0c003607203011400501901b00442c1400e103580210910b147c2e00404d1010070381c415400708049800090040100d9100e00c841242a07901007250302c1d0000b0800e004400481c901503101a0704001a4840b0100c00c0351007100440c1452000d502060101e980c1c6c0900f00103000858490b039a14001d01e1501454041c244540507080111004164080050180e80325030401c440354071840c460b0705075078050404003080c0c81c4000c21399070003102d050705081a2404002855409844680d0584a149145844801502c1d900300c0c002c08402030190b8440c8280c8600318056200c50944502038103059004c1d40e5a07150500340507040d246943d1000c00080541d403201d41c80c0a6001c00d00b604040c0c1d001c00b00c10044401d03110641c1024040c0e80003a81d0040c1e0001d0694189030021000f841141d12880031303100580c0c0e840d004000070f800100c80140c0490003c100801c690b032000c00c01542d0151145001010194990004081d40700380307841c0d44140b040e500c00040c02103107040d5403104401c40f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 52539239 1250 52537989 52538011
    0x30d05070c14060d09020d020303032706160507030509100801091404080a03110d06120308010807050306011502010906140a060801020403050309211207030801050405040f1e020a090b0306 82
    0x2001c254040f50f01c9100da52516540f0720f584d203402104540d070344004103500a800904613034484c20010010000307a0840381284500000d1040b00004480d00400e400380700f0107240c24000d2032100d415034161840d030b000c1d007000c504000301002007000c00d61f12021840320020440c0e940c401558100350701072045880303c00e1041045141d04040100007200c0508440914a1902d00070a40041101100d226070281800c0400c0340d90802401040c03c000615101d600ca1f0f00039070303078002141d82c1c440140340c88080c140561509508010014130280b6051142c10034a49920302c00000c2c003480c2912080104c1d0412450351108a00003424448407021a0150030080c00306c142c000c502c1c081c1745554881d1381c1d100d0904c115004244018a4043c03c02c00756074502401182b01c002d485401100541203411503020383c4080300840c620500114407401e00d03104040c4610340c042e07100040040c445e200c10800c428070714595006c0d0fa01240c50000183c54166400d402440326010200700c80e600e070010141068002000c0c401d1003 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 52540489 1250 52539239 52539269
    0x1030e07060e06091503040b0f04030c03051e0c010f0f0e1f0608100903090e070804020409060e0a0507030605130209010308030c0f0f03060a171203060f030d05070c 72
    0x800100e500d00031503100741402100511454041880d81c0110580d040e848607031044c5030704207207041200440c801c07403141c4070000c00f594600c504414455070958000e0001750310651001c1c00039005000410841815000d20f54040c29141d00f41106507108885504180e51280d20101c00ca802038060207280c20840d41c028000055501d1102d80c0d074a010445a042903400c02c1000000c0c41080e9100700c02400c958001d4443c0340c11600e2280c0d01a0004000480000d0890000001d03000101e050080c010001a514814191a03903002c000190042c60025109540d5130400d45a0b2500100011141c00c2d1144000d44507031882c6080107811604014098044490001d1490005995900c4d040d8152030b40102d405882e600c0720222141a0b0050000052041c00000303a01c009911180018610418084485200942e143e51030842c4000c0c0b144078400f559031207114000d040310841c4001e5a440304000d0318410340c42e036203040017030314024803502034101080c00011f41c003050201c80c41c0e441c030141c90301101c0f103284 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 52541739 1250 52540489 52540511
    0xc06030c0a0804020d02040507170603010b1323090a0605180309130e0106090207061805030d0b041503030507050706020303010f1815030b06040e0c0607060c05070503040905150103 79
    0x280d0310401d04004108514900001c045542d2a100c4e14103060b0003800800052804684c0680344003040190100020a41030004100345014001d08410240140c400c0c5001b02c040041c00015200c0000081c803103524002a402c0c41d00d1640c001ca0344191990300040110004908080c41204c0d005825451450400e0645400c00000001220200e190a49600c1c68603c00c0c066648001c1c20542000400c550034544001200c40c03641c0c001e40b40042c0190003c20240214a144480c080300c000d6000f0150781052100ca0003081d4207510000c0407007809800400c45111043c2c230140416900e07042113010070408606c640c1800f0080090401030318a40c0003c603e5941403072111100d00c0b180b803081880281d5800b4509103c088250010321741d0b01c045881c007000381c80d1a85081c0c422040704484482c061490320300c002c640a0000940191070b00e1010386240d141c2440c50300d5100c007038101ea01c000814400200049000540104010030003010300d040009258200504081441c14046004a040604011f25010 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 52542989 1250 52541739 52541761
    0x181305090c13091e2306060109080a0302061b07050a0807061415130e0102070c05010815130207060e0a05030706050c0f0d0c090510020a05190506070c17070302010e0c0603 75
    0x4c02d502405046140349007140ca00701440324405d03514204150300c006540303001880c0019280e40a40f5090300d40c1840d8581b03aa507200c0d5180d003580c4012b00142c0c40f07900440c4600007a4400440c4041c10b00d04640c0c94800d80391245c4d0701e066101841265460700c0018880c090103818810313050038402610009030300e820882800780d600e1a0784200d10b40f0138814038039190014106580011445400803009540383d4105003400401c2c1c5c001803003840e020444600025074803003001c00b03010b1007002000704000549540740b0100d134000e4200d15001c8071601d55904481c0aa00e80c00c001141e0030074070880045035108400c1c03501c24255403014001c0c8010034000c1c40015021800c20381659002d10720340740c0015082000f643c2c221807007406503005540040d0040c2185800c0d42d0702091f10040107010302c0454405840d40c03a4130654084011030080c1964002d480418980d511400900100502030754801c0700188824034002d00c07a5102d564120050f0b07540302c0f0003924881040c0042c605040301120718034114584860048 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 52544239 1250 52542989 52543013
    0x304090501080c061b0a021c15051b07050a0501090f061406010f111c0504031106040602070312120213050f01031512020a1503060513020f181305090c1309 68
    0x2243c929040102c1030443c0b003007000580e0610360000c0241e2035500c548040d41c5100041380310151034100c1810341032070302800c0d00d014060045031131007452f003150b000d000749056040d000104111850b0050b6400310022650901a484400d070051001103264140e902d000d000b10307102c3d015a00309260481041103c0740c2e80041c245082002c003801c11103a181441032019080260a00d01500c07281080c00d4034418641c0d0040c080e100b41d920521241c0c4801850ba410809036001c0e0f4403130b0500581c40340b0b0b4148001003840d102c144400c0c00c5810300c032404242c0000030387c00366000b15141039101c1940410420051070849140d80100c1c10070b003020800d0410b035601d5040e54408a005980103c0b0010041c2c0f03086480344080c940c0104101c040980c031050342c3c120001c0c050103103407040500c41d4120200796411224580301700c41800a224607098a4110f034500b040d03103004045800583d20208112000b03192000324003405206400510103070a00540403000c01502034000110a95541c1c5003090000004590300408 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 52545489 1250 52544239 52544257
    0x180608070603230c0c010e060105060301030204020c030d05090a0308061c0b0603030405061206010f171b040302040c080105040f0b0a0306020c0f030703020d02122713020a020304090501080c06 84
    0x10500c20b09903880d0b100160f0500b400184014240000c00c10030845000c09450340e400c5040082c8400810018201d80e96402030103419130225040004000501c1e0a5000741010183c4006403800d003051910060200c510880e00340d87e2640100d000b13581010b90101e5050790145007155607049100e01084280780b100a1508000c00c265103007130104e5507503136080040d10000c05000b022036648895410265141c0c8000b0b4440b1030200f5154599000000e00900082c210301202e102c0b0307080036942d6140000845010710341301c0f810241d0708001c0440940c42d90b02404041109544815000d0352500d0140000c0314034082c00340101c00c0c0780141005c41966107082d00c100300e94000b2005a1180381e822040d0741841e40e02011007041e17110004440d4109a0041020881c0140f0b54003038403000c3d0446c1c81422060320548024020141c0c46c44003103e9100380a080070360310064060441c0c000c407150300761810100c0e0b010b881e60034090b07440490108940d06203405428003400031200a031101840000c0460340301e01511081d = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 52546739 1250 52545489 52545491
    0x11d03070609060b060d020408060a0c0203030c03100314060412030b01020312151f0908011e090c03060e030408070503010e030a05030c0c010203150108060301090c1202030f030a0504180608070603 86
    0x100006004007134002400d03001c401071041d0f9070303003001d4003d1100951161040c1d40f00e45c0158400207040007914451480c0855035a00654035680e00d10480c2407050348000c182e420510404000800401c03003440d06041d415024000034006401c090502c03001d4144403107031002c105030030440c3c25415641e011007a940c006004640040c0f054030b07040e00d8294481c1c2c0140d0851b0300074411441c0a10110702e4421038145000f0161101701155441308086801c0e102c4040000b00340d072522440310308a60b42254031107030889018411030084c0c26225a500f01c165203e40c082607000d40d001042c240030340ca10905c181801494120000c000d0413158000544d200e000e402c1e9a5400c0c01000310014900103101403c54072031039000b00c0210368914110b00d000007140b9082500340e000445007030006200341014481d140059401c501c0b038500c0949000800d192202c000e51040380c2600030310200351020082000944440c0d4030315110580c459041840c002103801011541c11102400c001003005884004144001958001c0c68 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 52547989 1250 52546739 52546751
    0xf0916030f0b0303030901090c0e0c070f0f12050903070f0e0c09011b05060703050708040b06130b042a1403150a0b0c0604020a08010902010806060d150602060405011d030706 76
    0x30301c88001e054681820350036020000400003d900c06500c00c0409500c40d14213503692949443c0c8400d00203504440488019408000000105e120010310307400003803041454000b142010795030b100e014010320340180c0100314040742d0907a02d45030600400001c3d1045008065429140400060400501601c1031070164400601d4040591081c040c0b40d9058401c1040ca200c0d007680fa03d009590713017a0454a20000038600000310f642c00e842980014001c6810010400355600d51200b004258000626210350a03640c1d600902c0e219282c87c010745a81040b4149440d1020300e40107040309000c0c4080d0b080c1005c001c9503013150000340103800f050300d4020441c038142150f040c60314408a40d00703006c1500f01880103400414018072a900000d003441c45544251540740c0019924440c0724240c0300b070f40b0b47c028007040190300005c007682001e030050810181d5807100490200011400340c0883e0120350042001600000d00700000e201003401003418001c0400e075440d44040307140703207800e4480c001c010000308000c0d1209 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 52549239 1250 52547989 52548011
    0x3040602070f02060301080a05010c0e010f18090e0708010b1804140312011e0603020a02070612140403020f010b01050313020904050a080d020c010e0c0307030201080a0e0304030b04020f091603 84
    0x104241d45103c0e400f50146990396156035040e5a10070102200300c84640c01c01000c440002d21075540d441c1402e40684501000c84a141001e480711070958049100080010b080001e000015028101d0210002c00191120900708100c060958428648141c013030004010305921440400b02195401500b0031518244a20b040b1a01401d6100348903119400410b01000070a2540400e00101c0000f192041c0c00d059055450100f40e043e80520554238015800141c010408240125880350b0880d1124074001400140600200c030002e006503015401a40b0007054280000c40c00d1150b03d01c44082404c2003401c0d49410514030307603180c2024400034000c141c0b440200703080003810414007180e154055601500e07420729101100080d0018404040950300b016501d00c0c80c2500455008001c60028003e88000c3d0304540055690b00c6010302940c1d44940d54044141950100b440504091445500910f03003074245401001804207a45460511a00b41e42c0705001c42d150401c4003022141c09241404a0b510b0404 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 52550489 1250 52549239 52549253
    0x8030402090405070b120603010b2d060c0109030503060102060c09060304020d0303090f200a0e0c1e0309070302040e1621060e03090a0e07020a0206070c05030a0b0105090117030304060207 82
    0x585c3c4a403210304008a50400c0700300368807562603c95082600204094801d040410020303550b07401c11000214071116031804002103041003943d180001810340c51074690091003480c01c50f10124025000a0004000c0c03169940e41840b00903048501e07151811304006510740080c0c07580c84083c00c0244104c510104c00c8040500030740040c15080d80180d00544071140303a04003d0800819501d6218038030304048040740141c0740c03c024001c01d40b072800d90748180a41c3c80000b00d058503031000003546c00e8900c9074504141d071140e401c8010b5100c1c100d40c030040c0020380d10b03610500c0240c40780c2142003403882e0041c038103d042100d02d41ca050821a0a007041100c3e1011041503101c180c0000694081c2c0a02d082418040a0b00c2d000802801420300544050705141d81c0c0b4421200c2240b03040e102d910042c2c20014108000d03140800140441030700856109000582e20340000703103000450b0f0700840354482c1110042001d443c0c4600624014108800b184d000c5098401c0469124440100000c161a90100d0710000344500 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 52551739 1250 52550489 52550503
    0x305030a0c0309170c04050903070c0510020c0d0809011b1203050604020405061303110102160308031e010603050604140c0f07050309090c0d0b04090c0902031801020301060509010908010908030402090405 89
    0x75032040b250015000000c4e41c48110b010a50b50140b810b080201300a46400400c40f598160000f1050f032103133003810100a040880c07035031900c085104a003986110799403104465201d1901c40c01c44180e9031803001c00050141d00040c01655415100d6465103004140b0110b00103800c0390315464005500c0d540d4800060081c050364200942041c0042441ca0b0406e04004c007070741c2604c0c000c42400307108010030001280e07601e440c0d540d9a090422506800c01c0014004009150040000340303507819200b448209407000350380e00f64440300010340c44009104a505141c132506004050351707603c0c240c0c14070707144c103490000344507406003140038001c00580f010503c00144103562860b0b40041419003141807100b800700054019507906905185495400f883c10300c0c00384506652168014001c0801c180343c19005002500001d161602907005001c100c0141c04081c070003107002c2e0031140c5580c0c0d1503510071b4000402000454000981e10780c548008a008581003500356a0300542c1180c42d2910b44d9030703a140550800310 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 52552989 1250 52551739 52551749
    0x3061b031f090609050c03010f03030c06090b250914010f050c060703141e040803060d060c0203041502030903060a0207080c0a030c2009040206091507080406020c09010305030a0c0309 80
    0x1d0108404502d49480d9005070b0200c0c1c0000000344225114400490140d00c020300c200c90240703c0d00d8504200103400f03a5018442c880c0220720000b00416280c84a1504400c01c9416034501308503c0d0010000c81401c1e00c0b00140e45189250504490b402c00140c0407a50020b04101e07414040c400281c4410700e4411000c8420082d1044243c840380d003001032000d4050b200161341024481d2021001601890500c690003008944190404803d51501e844044040c1d2026000c00c1e0451050070040c0c0115009010307002e0200e9040d8020759a49240100ba07400c035010f15540b04085410400001d505c0b0b030340000311290014031501005035280b106140c1008c4c2845000c50140c80d50080210079028940c0000a00c9001e500950850700d04012400d6010b5034900c034485a03a5100300b940c40480e004d0b04018001e8101c030705e4054000c02ca1070300c01c0544100b0030b801070f03001101e42140c0020140040d545c10f000100c4100402d0303c45101550559a500303450f4019902c03500100008140c091007414810002800140 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 52554239 1250 52552989 52553041
    0xa0201020d110f1b0a060c030f030b01030204030203061302030d0512041509050f0705010f09060c24020403060902271b040f060c060b010203030c0f0c010207080c03030a050603061b03 80
    0x3204000206600c11030b07104c000c901c01e0043c804c00013401c81c066960005a694150b840030350910800c04180d0090091107105410154248000700050318100040c0740580110240d002e4501103510416192091401c040000c001042c400405408064a540b9400c0b80d40b010150800c030b440e016800b8010455910090161720a0303400d45110038001080d8174043d20001e9079109415000324405442c5654507101d6140040c2045141d40b011962012080c420b940c903003005a031404000001000076a045601306503095a038501c1c0341c404614014103800d11130f41e400f50b1026a5a243c0008044440400408243d0b05180e000004020413103000104c134007501c1010080600c2c40e460700000ac18904aa0314200c450511700040b0a40390760001090f06c0c070035114254003510306124074a0030300081c5c22055402840750f400340140e00008140b040504400c228a5000315104d2034541c1d01c88041d15000340005002c1c1e00700300184402c4150700d510700c010a10844045640c2d0740c4030110046040800100e46500311 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 52555489 1250 52554239 52554253
    0x607140c030304030b010f06020706090b090f0a23090603070b161a040201030509120307030b0102100c03051006030207110105031312111203010f03020108060d080d050f07020a0201020d110f 83
    0x7002c02181c5a051f02c04c1c0f411815544c58a48100341c0e9602543c0c080e403004a110720400f000b10030a004000c05603450f0180c005801034100744040341c0328a959170007031049079003002c1803401c1d0a00c0c40703a04800054000c407149087d500300341000c280c1716407135406082440c0d000090000e0054400d014524401c40e4884480c0081a0581003801017800040d18100e00013401e02c40072540840000400f0032400c450981e0351131441c1c9907480c040e4020100c0300300780c40c154007402e11456203680262194a43c84403da46021803903207000c012020401c101c0d500807505051050144070042407140c680c40000c00802c2c2040c581e01d454140343c038030400c038515000801c0e40d88907124003d6500d503c40c4903d048c0d074440104489101c1c4070300320416a203010902400d041d5502a0004001540c03054010340d0704603401510000d100b400c99185e4800950007100c001000c5500c0e0b000384200c034120342c43d04540c461403e00c09042510000e90000703440f4050114401d040042d01d405601000405120510710303880c40a04039810 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 52556739 1250 52555489 52555493
    0x303080402090603010b030d050306030109060e010b0f0105040303050409020702120d030f0506010f0e0d061e0209012c090603100e0a1b060c0605100b0a1d040b0607140c03030403 78
    0x2004008a038200d0146008001003807844c00c05001303541003004001c0c0648039810814408444a03040200480c0d0700d1b641720040b40c404107003d4800c110400a019002040d503e1405040c0580506e2018407503040007010481000031030781c0042a103080e518134040140c2e803842c0d42d00004080c500c20080d22100c2d0702950344040d0340660194000714168007007103000e1105070790350001036541c1413180c0d01410114031031025540d010f16081c092121400d01c103c1c0001280c3c00d2a4041c0b4146204ca2403e800c0c51950018661303055682107040c00364520851401e034011900e001c4035074140001408482806040000040f40745680d050094480750f20500c2e0341040407900513a61241c1e100110301c1c0503505a21503901d0710759080b0860060300151003064813603410102655449100808000380000d13001603005802040c0e494510700105403150300303542c408005c1501c500202d000031244410451066241501c15900c80c2c1300e503002d946c8099000b48161900c0503254241900b0408125512a410f000000b00841 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 52557989 1250 52556739 52556747
    0x60a05040f09020111030f0406030f09051c02070f0b0a030f09060515040b0f01050703081005090406050712050610050904060f0b070c090e0604120c021207080f03120f040f08040303 79
    0x84224000d907111030900b000c081c00c042e1a0b207c0c201c440080c0d404100000c2c060b041c003d07001061607110b00e480008a24556460b20340c140448040710021240301381d00c650355220f030b04000c00e60182003900030341d882180c0b400007001d1107480b85078030000900da02c90401d402d10024170707800050002c1d00840280018030b0401075803882e0300300e15109107103d9403620b4510001810520f007945109181030b1102c03454103256032400d030b8829400030a02008000c0d0300c28081a00e49890708a940101d225640128241c207040d030740542031000d2803d03c0c0b40d909107810108031141daa94011106028550304040396a05c9000c00850041c294907004044d804056190001d26542d03083c009101450280300040c1e6441d86440c05101a12213001807089240d00c60008200802e480d50003007000c0c01d2090401302040c9203154041099442c2c00c07400840c080c0c002c0d18080114400902c40035841a0350040a14903040c00d840340d206480c3d1000c0c00310045002014005001c0141030070301d68416941056805440c1c664a01d0014 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 52559239 1250 52557989 52558001
    0x108070c021207090c03180b0c0319060e040b06030c0f04020d02040801060f0e01050105070c0b0901050c01050a0c02060907180e0c0312091504031505070e0a0914090a030906030203060a05040f 84
    0x40000b17803400112140d5184032680c4141415031100c0307030180a443d10409c4081030781000c0d0101c4641c81c030030440e41c0300c0d107130b12807103002d0003404c14400c03038503803883c0900340255031030070003000f05000e034000081c6038a8590302c42c021070000a0003218016281d013242034658000b0702454100a501e50729040d404286160f4125608040341c0100c0305140d9544c1c0c8375801100d690098140042905030100030038041080304902600c441c82040c54240d00b45004003a166082d80c805541c400fa4044d514000340407004c0e41481003944c0301485900400a1901d00300c810300c4c0c0130000203251480031b950713034048114a035014809210030010013811070703402c000749944201c9503030b000b1000d1500c509448050206143c690000b66003c03a40c110603004141150400103034054240280800c04006003010030344020354824254030003074880407000081c1c0e181e8101460180c010040d1400c0c0300d0307911050b203540000e40e00440040a03150680f070f0140e140c0d2250b4010403420403940c1c1100c1c0d070083c240000003042c007401e64054 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 52560489 1250 52559239 52559261
    0x60503010606090812090603010b0d09080a0c060c050f1c090506010f090f05190903090b0f0406121b0c030c05060f07120905031603050405030a140f030301050108070c02120709 77
    0xe140d483d006408a000148031b01d680a5812400c11300040045016842c0a005902d00d26500890080500d9807540619403141d4400c00c0171651040307142040c031000740318450290700f80d4107055282240c030343c1003d0414043c16188050402449207034007010005500001070301a804021105256115980c0190002d0075008581c626450003080140c0100f4034043c090040a04d8000301c0e07011010340c54918080c0c500d000c0181c060124070103000400c01036000c020a0309012148160303440310304040005204103402112190058103045401100d41c1c200302234903a400341e880c1030506001d540e6190554441c0065100945240600010050445500400e44c0e10840c0c3d00c0e5561850500c404d88034030b00310780c240e6074060069441030105440066803100700005960190030800d09103903644002903e00b8104003012034904200400000030308108112504240f00c1601c040d43c10f560422000030184d02c4007d00d600304000d0340805c03e01c103544900c00080400070503282692001504c0b1255800544805011 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 52561739 1250 52560489 52560493
    0x70c0201020d020a0f0f0812010305100605010905090a051003051207300509040207051b030607080f071b060203040c05030d020a051f180f0204060f0b09040f0605030106060908 77
    0x2c00c0744803074408958a81d00340d51002c010041600300c1d0300d8440d0300c3c4200030760490300d21004004c01540d41c0c0501245034001c503c0341c4001c4c2645040c6860000aa4046911190610607000d8061101d9651f050255511001110002541d542d820480d20107440e021740c0042c005004502250a0002ea110010070400b4028071003424140b84500380003091110050010030200c60003c1e203080014030803401048044001040503061803110740303405040c1000004010901010551b80211a00f401e0000541c040a5810071000c0c81c50304141068034044014103180401c401041080c40c0e9a103442c13040070080c3e4000c80308540b203242503d07000500710440c0c000c80c0d1003846020f02c643e0703a040c40001c0c00303451544d01c10302801070756042c01500107541a041400c0324500c0d03114a40c056000a014640080703040c042c50490f9007800c11030050200319180d03034102c44001050000240010710707900f011074449400a8400086412011a5442c01400650000e903455420b2a01c0007500035441000c110588440b002 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 52562989 1250 52561739 52561753
    0x1a04050a06110717060a0c02010e1f0f0903142b020304051002030606090d020f0303070803011509061706040e0105090102070219050a0312030f02040b031e040309050d1a070c020102 79
    0x50302c40d13100220b0702c122115030f601c050300040340b00e6166000103030a885140000701c0c02c030011589081c1045460800e850040d00e0701c46030701c81400307264020010054501142080302a001d610300a001114018000d480207100003070740c042003c0074064082107213085520380d016520319644040041e500a840c240d0385172080120700301c80c41a0794401c4a0007444014010b500e800c594030180f000b0403ca2181c1640d1011280c00c09080c00c0d242800180b0101d4400c6988540d40c8d810300c018640c00300d040582002c200602c1c1003041c44500d4008090a002103030300910201c81e0707038030180020017030030401034000c480c0d500700010301100d60750540152690920807200700700d241c3c00d280f0120320442c50f54030036581d001641c03040030004201a400b000b51030468601c5c01141c0158102400c0382681e00640c040107017602c0c00420048040c100c00c024185401c0c500094103420b003816100100a5240350240610030040c1e03255820420804807802c3e402070104c0541c0c000c407031902e0070700031304000d0181c40242d01500400c4 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 52564239 1250 52562989 52562999
    0xa0908060a0e0f0601060504271506020f030f0a0503090c03120903010605010305040b070e060d0213061205040510020a0309050106090501140a060219080d1a03071e1a04050a061107 79
    0x894685d0503907072659500c9051515184100d000866140038a85006600505103208502c00380201c8100f054814541004ca51500f2030091901c00c1c8585141d04540040c003910341d900202000312048803500b40b601c56101d40740c0100c0941850700c1da0017110b07458441c03120600116a810301c007524000404038001c000da02da44000560903200d003290300400c10b0340070343c002405150046d05c0398001144040c02c92030801810303849100403680f01050382080d840711603104100050f0701c0034820b00d17940f03140c07881400181025074030303140d4408018054294294000c903226660a02c240c1c004110369030443c00034001c030351b50b40807880d0003000c083c0141005444000280e110900782290304900b1602036a005114020071049000c0405000b410201c40400c0108116901d081050080c5c2c0782c2c441000403113074003c4074040c042510b030028650081d80007846400b403449034095820981000c0b01c07001036880e00120300e412075515080c0b10340e801850381304044560100d40f903940450702c00440f80d699004c4800c895218 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 52565489 1250 52564239 52564243
    0x10f2703111203090d030203040f090501150c120e0f04110318070e070509010c0b07200f0c0d0602040e01060504090b0904020d020f031608011e060501020c060a0908060a0e0f 76
    0xc0001c00340b180d841040000c0160510004101c0810b0291040c2c03420706840349013400200c10198020340c881e6803508014807403007010f4500074080b03440300d0601909110043c2d035210003664101190f041800020350300f0200d25200c01010b840402001481003016000d140244a034070b0300b0654240c0c0c0d190601241c0304064010004001c01078540c4034245510079030f07800c4012500d03644021070090410000701c510500081e00425940d01a130b0b281d0302c2d060032501400050088a41862401080652081d102c1e000c105030080ba240403400350079224240c0c800281d0504038040d1085620400d144248a0000100c543d403100142090302d417210001e0000705058420010b245409960103544810b14551400041c50321070301d41441003201400307031420403582c480c10346007100240d413107900307180d444044c0c2050080a4510031840a000d03c0340030048141010b0000f595194810f100d9805014000780042c0000c1c06401c42030001e00101c000c2f1595882c100c41c48402412400c642c2e0a481d2103070000c4075400385e0700 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 52566739 1250 52565489 52565509
    0x3070c061d07030b0a090f0f120810090c030213080a020907020d02120913090b06040b03060112030311040e1317031513290315011202010f270311 64
    0xc0c41c0105245801d6459070f04a049010b8525030415940304681c00024401c1c000320050b441c0114044030b25403805040c100041045425442d0401c10750b2400c12254000540e028815141c08010000341d419001406a00900c00c4520071020310701c007110300241000000510341e03080c038425140e611040d00c494605aa0740c0501e45034450150304003201400d00c0f00700d20b8018081c0000001c12800c503d408401c1ca80c4106c8094034000d07078800e0808010420181018010162020710a800501d2203624021034445d13100d881a100400300764440e159040c02c11a403109850280680c00d80d02602d40c10308a1000d90707400c0380e04208036400c04554040ca40c1031820101070320f109440705903480d41095203000811050315002e19101c464980d81c0e6402601074162007485900404494030300342a56083d41d800c1529001106500603501c3d4211001407104640280c0301030b80b5580c0c20f003030802c01d203003803440306581d82409052612004106c00d0440c0c51010b540e2010030301228028640701120600b00c000f40264003507 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 52567989 1250 52566739 52566791
    0x30204020d020c0f2b0c0f060b03010b0109050d0b040303020c03032805010501080f0a0e0111090f0a061209060b040f0207020916050a050c070506160b130209040609030207050603070c06 81
    0x7800c4520301d000201300d0410417010300c0840c0b03032010a0760641e580d51402c2480001081d10219900c917480c1d001d0741405d00c01c02d480f103002400c010340720038913040000c1c0855031184c00040130301c54000301040800d4000e8040e1225042c1c9042079940300d2401d0100c00280d0803c0e010864116000e800010744501c10900c21981641d1040c1e4402c41c141e03845415030891454050040c450059490004405100083c407503149946031806003d07a8603a118010032075a0704601e4440c030700c1190592070410100e6003000c0d504402240202c6c0c041140c42950400200400c08810041d030802d090001110f2410903030381c020258648204c0d9006965141d8544e002c0c1582643c0c00f0304408203c041007150ba5050061010307020104e0134100b185d0500303448601264458005003d2a207080c0101924641081045070b085540000c7c4415012401d0200350000343c1d44060107040074004550740e4100005040c428458440940740c00341030595242440c00f07006181c2d2003105070a440d220310341450b03066003140d07014110030066 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 52569239 1250 52567989 52568023
    0x501090209130207030e060c0c010e030d0206240a06080f090114060111011b09030210050a09031101020a0b0f1602011808031003050a03050d05070f17070207030204020d020c0f 77
    0x42240b00780c600095119000170740901c0182d07030442c1c256030760300c600800c6001c00c108044c09410030148005083c1d41d10031101c40c0d1094001c1881d10b00c00c6940012440e0340010303482406800d041b035221901040040340402e003a04506600c4022513110b4000109500908003214250410303560740250300d08131902940000b01c080e401c9008210103600c50011604043d55001c000a03da403a0040c82030720b91a0501d441c040032543c407000400a41c500400c004a481c03803d410300d40d203448480c01004040418a01004169045900d948907183e4420004140711607440340500b6003d0514245064442208032003003619920480c4c0c00f8001c4034410b0046001484208901c40d2008003c1c1c1e590a01d0b540008280e5412110011000030210300100035001409000e511159980c1c9000c00c065010356030300400000034480b400201c0b2152580c00001100215404e1541c02c0d56a2500007080341041c0e0036500103548103002040c1c8210790701440d0300400351805860100c03a000d058180035075403200c9041403c90740003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 52570489 1250 52569239 52569259
    0x702010c0215090301150504150f05090c190c0c05221812030b0306010608070203031305030412080d0f06050d14010f0e160501021c110c10080702010501090209 70
    0x10300b0a44400070300400380d86255402c10700b030403012a084480d4a0303d803841414001c4030812560400e485403c031040f0000c1c03204c681413030400d92604c0c402c1c1c60340d1240038003529203000003481c0002078000f980c450380f1880210b62036808071740324000c0054002d11000e4965001c000800100c80c6030401000c07881020300080500d900404040d804010101a41540110387e940b0065900250400e5010085510f05403030014901c24480d0605280002c160840740c10301807000f09104a50350000162a0302002826111480702c0480c50104d0850140b503200010001100c9198010480c0100103041000c0d040441080f084040c101d844003903503c00d100e040d4104200c1d910b00408941504122641c1940090000c98180d034842c2c2070404445c4900c41000031500100148404002d0b45440c000091070248000d201d0340c840d8494562042c20841c89a6061010342c0c2603c00010b9003d1121010071100205403c288410201001d050324a013150100015480e24001045c000c46d548242c480601c00038141c8090 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 52571739 1250 52570489 52570493
    0x1401080402040e0708030a090b04030c0302060a020f071811040501080c0d061a040302040b03070e0a020a020a020306040b041b06020309130b0405190b0108090d0e010c05010501060f08010602030702010c 88
    0x1040161040e82c015407151030600545004100050080c43e44500555840b005a40003e000c1c0155422074400b01508200c108003040021140d101602e40445910f5500c2c000f1480580c80c0810b948510141401824170009030312050b44d0240c014108840c81c203005e200c2450020041c0c62185000325070100307004a01089a1a0007400541407201080000040c0a601c602801b4611401004010b42150001405000f1401c207400f03403801040b405d8001f049000e0400015084009004100400f2541d01084001400e4801c00400b481d01e80c0207400e82d201c0d400d00d0306140311350440841d415210000c0300807121202c15400303c086c504403520307035024504014501c1700b0048900001d05401041035144c0c4d405405a40d1541310f0700d4015584160b00384c0c400681c0260301002d9440c0032f4000703410b00c10040100030180d0b81c04106100d0092a601d0090301045081005036461400e80038041c00c65881c180c000725409401c141040140380302e81d10303404a20703a61204126924803800f04000d0000f0303542032501c40 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 52572989 1250 52571739 52571747
    0x105090106051207470a030b0402070b0103080d060b2212080a03020a0e040e010c0e04020702010e04090606180203010303030501050f01021005100b0a0207031b15050304050a0f05060906070503011401 87
    0x132814031010140300c4031000801c0000f183c501c4178035480d00039500004480701600e03054481c4070b01c0000300b518207500b040d0703c91b107a0a62048051202504d022400950148032226952080014000c8504020385a100450b41c00389150680171f83c5000104801c600405c001d0380314a061181a03a10060b4140f4104515004a0103074010005440c03d01c0745030302440c5840c1c0d40710300640310300314800c8000180d0a0b000c1c0740c00515038407801c40860b003d207104203c0080583d80c451010039040e2003d80d0041500c0c01da6107400402465030b0340c00b074a882d0f10f03201c80c9030802c1007091b00218100e900a980910560b6214801c0003801c3c05140c1003203000d81d000001a036000c44550700000d41c060188010305841954486907204140c1c401c00b82480180c00c02c9605008000c0907800e000708240c010f07010b94480f00c0c05d00030f240700b074008484034000a11401100003002c001017088012100c90744903500031181200f610704a070381c0d1503090315207802c1070282d10002500b0901c00c005590490300c2c060121400d841c50080150703 = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 52574239 1250 52572989 52573049
    0x1504060b030109180b01150f031e0e12070b0f0f010510030b0d1202010207030809010501050102032d16030305090604081905040302090c04180e0a060f0b030105090106051207 76
    0x1c01c0c040e084c200c20020508142606008001d100301c02e8550003068000184560b40609100c0c049c189090f6900c0b012205100f410800365036500310005103c2040102e180c42d00c0c04c540b8402d88001c600003149002c219580300140d01625210308405401d0301c075104da80742d583c1004d02865070840c50b403030200b9483d41e220390400080c1c214064601c04950350301d916030340c410b0250004202e0241c2c2d0002202c01c00c066103d1740c074503031102010000700160350512000035201c0c41044c50400341415411408040d429000951059145032aa821642c400c210360b40707200c180003d40410b9012a2030315000480c01a000b144041c402c903840f40c54145824131010300410352038840780c2840d01b001402e110200c01600c0398400b03a401342c803000b40e52540b22071420b00c562490400102010b11003a05010300311050050004a4031461541701d403020852180c1000190024910b0240c0507515600b000d091000c0500c0661140c0c06035101654200742c8100e03283c90f010780d244074500c070300d140c0030202c3c1b241d030003d42c03d01261703003 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 52575489 1250 52574239 52574261
    0xc1207080a08250803100501030912051308061e01060f1715030a0b0f0c070308010312050906220512030306100c0807030f0207060c0b0a0504020a090e061504060b030109 74
    0x200b03c50b202e0481c00c0e0200c9558140003180c2c03c010000034008040381c03d65014004000c03d00c2c1c140070454050313507180200f80d018070f0360030b0620034042074404026101d46c28400140018808172645882c2050700710028480b40d020251100c10740303400100f440c3d84118400303450301c3d030f580d165000c219107242e00720b40746e00350000c00540d51f0841c0356081e4261540d00707209403529603000d01c0f13544da010705025403410917200c80030704241260402008901e0020742c102c00e0842c1141d41087c4400c40c9110400c40c250b56622507000c0b229800800010010000050030302e152440b00d21511859410945a8080c840d100f0b200034600030566100b8400a0140c1ca080d030b8256103190540d1904d0084641d103070340c83c030409800000d4110b0128070b0341d140e114081c03941000f40360010030301d9280c042c22004040d110451b030003e01500039980d1700e440703038001400d54684c03250407401024082001c0101c4641c0401042d260a002d4a0590b80c10180110013a802d140600035042540d0070306c200742d469a440c10340c00c080101181400 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 52576739 1250 52575489 52575517
    0x5010f0b07150e011104030507050904021008070c240b090c070b040618050a05011119081315061e050a0e1b0703030c030c11070501050c15090c1207080a08 68
    0x50001242c40030f028091007617086081e040d0300d440c20351420f13501740b103026009580a0118502003101580e0ba07529100c00030010b60600a00517207400348110351002c42503002034402004410581241110103c4081c8100d0528100300802c4d40301c0c00c104041c004d400c0c0e500b05e4a2020602800f40400e200290305a00580324a600058422030502000d01c0c19400d03a0f4180c49903000305000b041446003e004008600360302068080c0b8096030b03c20840e41c00d40c500340341c100401440000041d040702e061002c504900e50410045424a00c0308280700d80a03000900034642040910541200e2020903445160103403540140202049803c180c4a0786201c540281b80d01d40d2200803e020070754020703081d00103241290023039030045120900e4803806420303500c0113103104080011b010021200f022000c9020310640d4001d181007555109070840c82c600d098200406546184e0080c410b104003000009201040c4190030340b0307070b03540000c801804a0b84071070072481801da09402804508000941c07550041203100c4080304 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 52577989 1250 52576739 52576751
    0x317042301150b040e09071a07020301020c010e10060602030702100807050f07060b01030b090411040c0201090b0901060608060603090d0e010309081210082109010519050a0305010f0b0715 82
    0x182810600c20742da48001e03804500001d051002030001742c541c907408404000140b580c5440c1c20342c4841c402004108081c591705002c205001103640039011100700f68a008000e01102c800e03008400c2c0c68410110150380c00701c0c60150001407550020040c1c4004940040550711166103442c01a00d001500619580c10000304001072042046840054520140a40c41c00034103181d0340000901224414400d152090300c42d58200700000300703418407075158160290380120f48102841ca05a0161090260041c07003070551300b0800102140560143d0103e43e1f03a55205041da8039030100b401010300c01940c105440b03800c094415400d00c0c2c040c1541c0e4080120600d000180c00c11162540541d6800c01e11503220101d10a100f4171140e40a6183d1000117010701030302600620002d902d140c100354003400b100141546001c944042203a0041c000e90b803d5003500c1c0101d0400440c0450024680d5110a14510109281c800040740140c00a82110160f860100c040c5143c0340244d100c010024074070032200303c1015217600b = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 52579239 1250 52577989 52578011
    0x4140708060f070e040608101121090709050601020a0f03090b0309011b020d1d040f0606020312070309030c1b0b0408030a020705041b08041103190317042301 69
    0x412030b44551a40a094402424183c0d40284000703201c1400c0c03445141070031400e01076000c021840740c00300d48420348001800e0000008403041c034000c0041e52902070180d4401105d01c5071807212214400c20211041d03840352030322411081c00b203d601f83c4085005030b01107002c8000044006592840c0d090080c18040d2300243d8540860f1035541c000c454414260b5150719051518056401c110114241300b80081c2991101071180200400c580d90400c0314444020901c2003296140c41d800703029038404407603086c00a02e8a500f406903a0b03501c01000c0e4180b01260800062280d0b12900c51000c4e034560603550101156440d8803141c1010480380c019000482e1400b40002d00991148010001062050044c549034810210081d05103042a80f01c42d006505042e0610000c9216540345c43c8031403807a0502800603100c60034900704102c40074459135010700c80d150603900030340e09001c0240301240c440d81d01c400c2c0c0c05000c030107064480041940d00a0000328445880d00e440d2012001075401d803104600006044017040c = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 52580489 1250 52579239 52579243
    0x1020412030c020108060f0310110d0207061b08090a030305060f120606010207081b12070305030703020c04050604020a0801061b06150303020d0228060906020a091403010e0604140708 80
    0x11800c602041e40342c0700c40011541c1007080c00e980f0040446107403c0c11514000401e440b502e0003507114501982e104c4100300e1310b02200080e01d03841c1c459004215102c11141c0381850040050306a900500c50190880b480303154800e41c21240714003031f030700c001d091440b00d160f40c143c000c0d0002601665200b0804070114140c1c0d2601801030101e444628020009814940006420280b20390080d8001d500028010001e612030003166100c048420394030301915070f0901c130030303581040070766000100705000026552040c960300050550b80440200d4080000d901c0d080b040000720700c103104c0644041203941c4010451140103403000001000c03090a8040d0307604481d82d408044648107260f0100c401100710003401815810003d5900a00241c0000c108981e4091084e1802c0400a4100301e00c03a14116184410018aa001901602d90044007992076095150004d0803005180c003030344801100940c0040183c0c9014004d804040c1040006409191510f031188012040074000f019028402d00000090701001 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 52581739 1250 52580489 52580519
    0x9150402070c0e06180f04020102030f03010b0a080a0207020906010c0c051207030605060306040b011509030b0906040201120b060a180f0602160503010c0f08071e120506060f04051002010204 83
    0xc42c60041d105641441c00035140080e02038441c0b4000c15145d010700d4589050503031550342055603988611226999880102d10f184070307240c1c80e080c1021010000080a950000c06400401c605440d0901980d881c0903000d0b049001e03804010b58084890340110b1034079401421002c2c1810b00514003000e000303490740c012682c101d13a82c2c0e0018180fa030201c0800c00c1809064825682c00c214202c001d0103031402c0c580c65500c0c5469042c090206041403c1c61240e62150244126034011036202ca2a81440c0c0b40c04240281c9500007141c4c10b80c04680808440c280018581c0705409015000030003031030800340c041c03804a503080380082415007007880140d000301d000014158003a00406e41d0303900510f0071000b260b000c41e007200b20942c4903901aa0414000300e11481d00480e064858084c50300c2c0c00c049a42e10000c040350006120340800d0041e141069804a089500c0070102d407190340c090805001a440700d000b4020035200307842c13030062044000e21007441a450620384540405030756100150810341c44400041c1c0d0b541c2 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 52582989 1250 52581739 52581743
    0x908160b01090c2303090717030405030c040b060405060a02010f0f060302030f0d0206150a05040908030421050403060504110d0c170f07120c1a0318031608250c0f0f03110915040207 79
    0x7002240803c507033305c1c0030030594205501c00e80f010b201004008010402e68001c0f0300500303104180100d0410b50480c801d601c030004203940c40d0410300c4084900104440200740d1400140d0290081c0d50b400580b060300050024000021130303005218903a51555220000824150281c0d8004c00c085800078a5a445004060200f80680660760342ca0905160856081c142964000d03000d00030314107144c10030764004080d9004c070b0781c10040c04180c9584900e0616890a01220342d5680002600c4c000c6d401d000b0f12410240560b09031207100034031581e0081d9000c2e07460141e40c102c5d00c090340c0304030010700504020001c01d0f110144030300701e4203100949500711110102111066603803100c0020003000480c2155500642d40c050b04900610720b040c3c1c08443c49489281e4140c009805000300043d000610508042001640641d82c44e4040b83c242c5503181201c02c2c16801e220b440100450700c42c0102d82c4804405004c001c0720703400799203138403911041800d00c10703c220020000604090501d403005d6070740d1581e00080c13410314 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 52584239 1250 52582989 52582993
    0x3170c1005010f0501020a080304150207050604060f0e013308030c03070c05010806100804051606050306030609060709030f111002010b010801060206100302040908160b01090c2303090717 82
    0x143c10264100e0300703680540c0c401411035001000f40d001040b0890100d0340c02c2601724095009449100308504041e10546000074000d10450040006108144c2d002842c10490380d41d044c4441c0d802c52148500b81c9240c0413004030110481d104120000c28000310000903080e05105607820241d81d4203000b42541c208080a108a810000d490001c1002c15131441000e0300003406e01c070400781826408903d1340a40c1c540000240701c0e03c00702003410301c04100010300b140e61824001c5422192200303030080c4a5042aa0168000d110f284041009c41102207412485200299100309103d4550b0b00c45050341304d100354007035401c08107a40c0c0110083d00e440000c58044860340c0c0000c280440107400040421405034001400c64006078180036004180340811800c882e0100c03008183d0b203a6500700703039090344101c05031400b103190643d07010340800040d044228100e8218550411850b10007100907641582c4c00d00001840404d100502c130202d034030047c061a00103094808945202c0d48400f212886c45d00a006000300603 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 52585489 1250 52584239 52584241
    0xa1508061005010302030c0d0905010e0304060c020103050604020903060402010c0305071a0402010f03110d02090105040e131203050103030e1c02180a0609060302060a030209030a06060306060302040c050a0903170c1005 95
    0xe003030781019641c0282400e103000c614502d0506100315140c01100c21280c0c445480c0c0c402c40091080035007000d41100d48080913240d61b5a62038001070a03048105a040380841c2c00e01000450b145031510130b440805002030058500c50741c41d83e004550a5441c128228240041032001d500461021003200000c00b0022240c01c001c1d007028000503200320703c98034888080600b40408025600b000f8002c0da070381c4040b8858003507203030601680140c0c0d90707014981094041700068400c00c00100080c0d803540c00c2050081004420030007074100200c003a90300c00d02014010607d25803080340681014020a49000780064640c0ea0422155000409600c4511000c0e160f240709081486214120380c4604401003501d003104000d41855580801c4c902d000311201703542855804940040d0a850a01201e660a6408401041400c3d01da1038002c004000a010507030045103011982406580188100c030306031380042c0c0301d494100d4034581d1402244231984030411141d04051140300030009040200300c01d1548041008216 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 52586739 1250 52585489 52585501
    0x1a010e01050c0a230105090a1b030b0903070201030c090f0b0f0408010f1b0e030705150c06010603141b03060405060a1a091009050603010311030109020d0311060106081e0a150806 78
    0xd81302d100603d5103107645000c06011360180000f4400c15503d510040752084041d250203c40802c2c05141d0001e008107081f1401c0107824030000c00281001c1e4800d0300c080002a10019040b24880414004c03502d040c5084d080c148045802c10b80036010028402c0041882d2030748640c0d6050949501a208100f01070700d07a0400203804000412150804e40f071450044154408080026620b10451280c10302072012002c418030441041011601550b0f00c0e801103449650756450010001c00d860300d206034000017400f0204402500750820300a200000340440340c115200d02042100914002c0e00d0507500102c08000041e0454684a0014030201948440780d1100c0c240b20520503010001c407103020030012281418801962640b0a403030641e50841d1103460b43e00d013010f020900401002d4000b0b0760005ea50382800c001c243d441500010b40c8141e500541c3c003140d076070b4002910301c4141601d0090180410828540041585004081d885021004040b4105404050400c24889507800c0741f00141c01070020015 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 52587989 1250 52586739 52586783
    0x1707030f03050d1b02070b030402030109050f070305060a020306060405190e130203060907080312040507121425060c020105070602040b0306011e05030a09080715020a0e041a010e01050c0a 82
    0x204c034808200071020019201e140c0252a600c860044c42c87c0080d01001150542d202540030081c1e50340d101086607012041040c86507580c4055100c100c80ca0b2140f01c0000c0c0c44030b5114002c2c0d900442c0e01a003101d0805081800f041800b40c4181d144410a8886e03080000c1c0040e22440c0c09030203004001592036000c481c900500d8103002c8010040c402a9200c0e1000b0400c0c140000211801c00507202c0740c0d888c281d1560300d4100e050070b8103540000130080d510072441d0240001c40740340403182003441048a16000c0400040f0804901030401c0c407107074010b2080304100450080c0384c10021184140360203441c08880303658000c100c1c1c00c181c0000451103070100401c000c55820840ca8103012026017900081d03160a000002d06610004064201c990b88444100017000941003d80302e0040d401241c0004d9107000b001c803540207401851a60700018140c410500907410181f040c82c941103482a100681e01002100540350b03845117129041c10440208941c41c00715030244a800107803846030050592000003045154 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 52589239 1250 52587989 52588001
    0x1170106080303040c0e13080d02031602010504050c040e100e0334080d06030f061413050307120e0a060f030b061c090204020c030d061e0f1707030f03050d 68
    0x52001c2d4000c001303000224691a01e44411a02e6055144d50140e940d0700804012a2550070010b140200210301d444202c4000d4001d07600c50001c0b0010601c55800e0392800301e0076940140d030040c0c03003504844e140700030a0510341c028008906100080300c1c02482245001003c564130b40440c00c800703803c003140a80360310707103013981030b001c800003071424011040080441c1c5040150074220060001d0000100514181c1071900844011074100ca40c2481841e414200900902904500402c6861501001801d0244442010007259800100550812296680701207030701003805188020700c04010107c40b0150f451604403005821190744003098103404101c0542940c130b00c8012503204400c10301c07490825440358181d0004c3c040c903120300445c403c292400403c0091003901d03001d103194000010105803040b926080074084a02e140021854003401c0340c800f80401c1824000c0030441100351504201c1001003001180b01d00000da020f40b201669030f640c0301240702981060407000300300049480e1408499510800c = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 52590489 1250 52589239 52589249
    0x5060a0c02010c020601060e0112061d06042007060b0d12080a0204060f05131707050306090d0f0c050313030311010c09060e130b0d03090e09030c0a0206070302011401170106 76
    0x903c048450700c04082c1d103524050040400b005031006100d40a07030300c600e205a00191902400300282d580b5004043c9000c800c41e031040c490204140003283d49400d107032203440c141c01d134100411031031240c0071420364280c0e03400190b050310155210a400b000687e145260707034403880d12402c00a41e013240c0a80026040b05030080103c050700b441407008000700d82e005034590701c00020030320304517035140700010803800d4003800ca4025081c01202400c007001000d00004400c002e44800300e04a464580c0e490030055500c0550072252000110f0070901e074883e5a00403410280c00512079000e0b01d0421a1810b540d41402445030b01c203038009201022082d100603820b00c9010300740c41e094542582d80ba41007150140c207000b03014a90600039843c0e450800300c881410b07170140d2080c000040030b4858004290400824111480c082c8000b0001c0340804a521380c1d0000084444103110000a000300307290035004c000701900401c00a030255500ca404407114001d1508030b940c080c0c00300c440e007407900c2c018010b003050131540700ea044 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 52591739 1250 52590489 52590491
    0x9070c0b070903051504060219020c0301061a040b0901090308071209050f0108010b0a030207021c03020d111b0609060a09030c051009090b0f030a0305030406050a1a0906040e070305060a0c0201 84
    0x18004035a0121780c000200000070882882031712140340050081c0700d03103218082410035104500342c0d02c643c0440c0f0380c070b09032108800a20219403941c08211784c00e11484043e00719040304100070001c400001000d00f00c08001414a0b400c41550303501e448110f907020702000c0b07554039803031003d905d01550440610009003006031811018070280d8000170340b030050103005280712140c0200e000c4c4420b51094046500b41d950250000d4000403c1304000841c0045054046002d80101242426281d100300910154282680d000707008152640b10342d5855403c06201e041c0e0490402c05c0200c4558580c40002c09894005a4500442c0d03440d609001d1100d5105800191140ccc0755101110344140d4440c400300241e1f80c0024000441044c240000790400c40b10310021601401864121800e01d40c016015521641c000c0c00140840c0e0340c0ca04491048030144c00c0710300059904d81031004201c0c103042c0860340d403140300500001070648200c1082850a00710f07500071900c81e0720100421042404c1402000a14801c0f800 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 52592989 1250 52591739 52591757
    0x31309050906010e07020615190902030a0c1103041404110c0c150a020706031d010903022a1c030306050405010902210103020a031203020715050403110d020c0f0d0209070c0b07 77
    0x403000b9143c402c081c1c10300e0b03011234050301d070740c1619655600440424503460f42c04c01140f65880c02d055020f034100b19400d12010b480e000d0341c042c105000382c80440d03c030301d0f10b103001e103107890305200e0610524000c0841c0e040c0c0043da1180c1c80b0201a90f03030b40060071491f4401c401450323413120480401125104030101d601c8500c2051051910654000441d402911072509011403080c201d01c14100408030324000d00c00390356091008810515401007001c0034480b00604448484071585201c04101c007a900040c1500b0102d00709041d45041004980f5110f1944286008204256220000303800d40f8800e801103460b0310b900140cd85100071003404071540300d505124100d1019891a00092035118a9100c05030030486040b00c80402180700e54101c410403070707000035800c1008245205960003007008403005c40c04a100c11202d0702c408080068040507000340740c0d0040001800700011f0110000b60444015000b0002504190043e905d000146106039641d54403c0f01d180094240f4903800140640304400b844541e103 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 52594239 1250 52592989 52593001
    0xa090b010504020901030209130c020f0a0305180d063204020d0308062805010801080115090e0a150c180308090d0807020315061504080604060e031309050906010e 71
    0x1a4200e04640089074016110621000103074080c0c86030010480d804809600b02082c01c0c1001e6000100fa081300764211080c2c01241160705654006025020707010070300600055585a900e807200c04408034002e004c9113191a4640d4804059540f0010701c1c40ba886c18460750300a103243d0f12104595550341c100c1e20041d00e41040c1e000f080d9000403044010b0304110240c0c0000b000b64481c166007001d1082d61121124080b24085200807600d00035010303080c0040e010600000d20b22005008182410510b20120309031030307181203402d10081c1489000f010703080c041c82e0b071140702040300d508d00e078020303004074030350120b200e4172aa44001c0011440000608103d016144140042800e90301550750480c420b8542d82001d04042c14080d90038040c12500a62601c15140e542960b50b0803907110a0013000d01303456081106007d030a60381242c0c052030050100301d80c045000540818052381010701070900b1310b0141da25080d1007026850240e000b0390060300c4244e07225818014000d01c104003050041c00520400c11040c2009 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 52595489 1250 52594239 52594253
    0xb0a0c0318060903150914030309060106050315040e0f0d030609050109020c0303010e150904050a030e030f0a03140d05070f0e01050a170604060e01080c040e0604050703171204060b04050a09 83
    0x2034000607282200c0754004c401c5d820620b074040010150803900c40e0340020180a0125030320b43c41110200f2080c0904000001c4c4c4a000320260f83c0104103001c0d005070f40500100c140401400540100c0f21a440b840d074140b0001030301402a07141c05d440310303503000c00e0781c03400c1028170402e40b601039211441c3d4510403c05a0b41b140d03c00b00540381911f02030004c11070591500907040040d480100800c1f41d0100b8600180810490006000d0022a01c0394864600490201e0205511013411094020180d04403144440000b441504098607403846400c1840c144264540c841c02182c4c0101c81c0c103008640b041001e55152608040d807411030075000d05e0040d113004e10210300100982c034400c04004040b4884000b04da00341c1e4031500074102400c0c1402e1030341c4c0c0c1503940b03c1c01590741d0162411000c0c0950f10303003880884d00000100303410384940d802c500144503003444e69440303041242e80d0900d47d40c02450306101c100b401405449907180070314010300740429603404100c1004100c03100a04910030003441c11801130001810 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 52596739 1250 52595489 52595507
    0x50c03012402070302031e16050609011b060903020c090f01060e040207030e04090602030106030e0f06060d0c0801050f0103031115040303020c070b0d02120f01061e090b0a0c031806 79
    0x1007000d80350045845030907441d1001d00d0304000d505010350244800c444c2c41d900e02240c1c03000a25401c4074a045840c1c2c21500461003e40590380c1c11520802c0491410350049806024040c060119440071014a440354000c4a0070b00c038080b40140c0240c4812501780c50300c0105181c012404c0044a030301945810300141c040d0020030700e40ba00840e008140306003410f0088549003c04800075005116030b00592030070034000e500034040d140100e440c204002070010000200c0003843c9a440000380030a40300c03203007040310301003103064110303085030a518010641d69400c1c007425010790001c0c400328202c1d50540c40d01a09040038404285600c3c0e014644c4061030b0511002c01ca074100c0d816050061f0f492024108280c2488415007041078800f00005940000311480d90040c2461070905522410f45c2e2130703180460700000002c1c41794400042038400984c010740d42c0c1c03200310040c600403410700260982c1d4410000a4a401012403400422618980e103018141c004000c2029580d04c40f403038500d940e083c48800f4210243d = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 52597989 1250 52596739 52596779
    0x901020904050c120a091401140919110402091c03020102070b0601030e0a1103030d060b040312080103030c0303230103050309090106090f0e0901060b0313051b01120b01030f020c0709050c0301 84
    0x146a020000034888410340c4041c540120030000e11868201700901b07515049d0031307640c0350450720802c0c210030b118507000b65260300003035804001603002140000412020f504049000740e48074082802106030394412510929610703129800140e100c1c2450704040d41c801c4170007810241810304000202035035603000b25000485075844a00e00703d0507460b0300c000c00c0c82c50150303a00d0a4125850210089480d030380c040080c0c01200e10035030f012080c0d07454008003180d15030003c0c0700003004101a80344260000307020390849410103448883e030300c03802020803042c1c0d0392814003030b170041c0c403160400918146030742800d0500b10b01621040c10a204420f14054038421160340742d11a0305d200c5003140010403600c64080d00114010882c442d03505460303082c02a01e00088040c0c0c804129581d104604640120422a1000c1c40902c40b058583e511075912441c2100043c0c0340e0044004e04140e40d5461803060140170b44007038915402514000c00c5400d00f490031a404850002c1c2c20352000031410710040010080a01205c40364003 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 52599239 1250 52597989 52597991
    0x1171f030b2d07050c16170609030c0601060f020a0f03030204090b03011505060706020c010626010b0105160602090307030c090e030c19030207030c031a060d020307050909150901020904050c120a 85
    0x30882d80c02c4281403000720031b070030001524000700009000564554584483c010f4106031b8015031640c0310260b50701d00c01d014038202c1d2500304500401c4002d0044084010180c0b80e40181d8140d000c5070754405000c0c0000b80811400b00f5030104051081520610900822000c00d800820010060865041c00812944180343c40790100203044020402550165907091166100a0040e1501d4100203080183c0c9040070403669600e4142c8001c1c6080305020300110100b041c3c6520389000800703c150300388010030311001d450007030f0200034040058504100550095000c1c4c85002460f6081502103000d9454213001d0508a9009000e0f41564000c0822000224000c4080c8010942007601e42a4100406584041e01e0b00355110400024449140c1c100c0804610100c0e07130502c29070f540801c00c2080b421808001c0c1d09940901c10501c15801c012502c0d940110b0402c044600f00c041d06040c008417890100c03400c07c403d9401094148107814903009068110300e40700c00d9181400002030315010b162500918183d075007 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 52600489 1250 52599239 52599247
    0xa06020901180e0108010c0503041205030a02121f0803040806060904020d02030703140d14070b042406030203070b040302150a051603020a0c060e01171f030b2d0705 72
    0x19a002d4085031889608400c800000c9a40c0c0e2040b800c000c03a000d203d0440302d03500303010181c00201c2c4070700e0840e44142d90100c403810200f61841021100c2c3e410051144240e00d508110424199184945542c405d600c2514040004c02d400094001c1404075a4000b035a1540103000074041c80c0380210304298405825245400c2a0740c0b180000303a0360722100400a9010700448001109004090103103910a00c4020211031030382090860072a40c01c0d01d504840030b03600e0804d2004e080020b0100c103006401c103000f08090703040d402d06c0c0040320f2045a007021141c10b08568620b000c200714241800300300000e009074444141024a141c010408210702000560140c0000007036a00040c1c2c0201c060715180809600001a500da0500c0c0c0030f551400d2560094401000d52000025107901c83c4090222507041070b901c10400142a486402d5031084c040d08104444074295040040303441450340d2800250700803601c40e502401c10320b0b1506241d01c441da10404000ea820488900d003846a01d00d12034000c0e2440c6042ca6603 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 52601739 1250 52600489 52600507
    0x901120f02030415050108030313020906120105090c0405010b040f03022107060305040b0f010311060c0c10020d080f0408120405030d05010311150c06061005040e0c0301170a02030a0602 81
    0x2440c0c490280d908281c0701009010501001201c0f00410700c1c0d100702e00b0032140e62685081d90382c1e40006c840508036800b5000c12400142415180c040e080720010b481900b00c010300c0510309082d62000c0781d00c9c08070317903218101451036842e06001c1c203401440b0700583c2c0c0d845c1a0402d858003030500120b01002e800fa46c1c082e140034000c01000c100043d614542142039450081d150f84004010300800d175401c0d140c0070b41c0040030400c81c0030a580c2450490b0751018003c3c107003444034814416507400002c10481c2074003410b2031461550300c604e00c01c1011703124680c0c05041e10301c2d0703000d0014151000251050080f580c04900300300c0050010750403612800c034079940011081e034907440c2142c0786100301d41400900780d0034040000108094061070702c3c254002115002c0000d407245c2c2c00c8503038900410582c0c0e03816502a102080013400c01c4860701248400ca80307407507440c01d5150098500840c00c00e8601d80030907440040100321034140c2102d4600e840b4002405455221215000680d40700c0d14440302a10103a4000b501201c = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 52602989 1250 52601739 52601741
    0xa0b0103020405310203190e0c010c140309040203010801020307030e0a03020c0108040c1203030c08010801110f131208040504061d0f0705040f060305040210030b06160203100f051008060c090112 85
    0x41310f01c580b4002590780e4501415105010a06080a01c2006050600808a005021480d0034111206949401d80f030300c05900c482c0c0c0411a041035420483c00304203c2240180c41c4c81c001507020f08641000980c2d24103221800404860940d04003c4a85c2c0080900800003a40401d101c100d5400902c0c224189481d90b0609644401a940c07241000071803621001c1d00300341d010307085420407a0603501c8607100d5a0303a0310ad9035400d8540b50009044400400c000e400c90311a0740c14060314100012900e552142600e800050100b02c070020000d544400c004101000585800d0140700060a40c40030f40140040d150503545002f803078094142400f02030030b18002a403051003201628010069004a898141c1e564880600184401d641c117900645041c50505080741c060701131f00c1c2c800700c0054050340c175180323140341040c18040000034201c0e894060214402e128003210f010300018252030001c0040d03036003481d0021054115003a4042100340e0041800c02c0301c0c650140040d070b00172110a0134580411010070715a50 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 52604239 1250 52602989 52603069
    0xc06030f1503030c120801051012090813080c0609010503180f370c030312150b030603100b030714010908070602062221051207080a0b0103020405 64
    0xa4022402031070008203050303100a48a034594011889850951a4464221140d410034007540e0707048900003542d01c0507513110302205d0248441d51900001c100c041c0f0ba449002591260003200d100418880c4207000d42c1009020000c1d4124007100c0711882c0600580018255010082419902440180d4040da18600c20b00401c11003a07a503406590102001031520103007404c0682d040c411007207090111004a40d09100e20414003a04601240d059910303543e001c5500f080400803000c14240ca82c01680008034034200403101600000591607120700d408814146031200c165142c1c0012802d10062005030740300072806206403110499419014030764240160781e02d00e6103a100010b20b1050100001f0404e034045100c5004505030075081d00d1501e200407910035401c040000c05044040c000000c403e4215a1652810f44c410581c00d1560920030038003100c0142c0c0b130003100d584c0e0100e0000820400111528490002411802d0808508003410500862400800058981c486141104000b054060416000 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 52605489 1250 52604239 52604261
    0x1106070609030519031107020d0819050d0c180b030912030c09030106051014031003081801030f020c0c0d0503070f0311100608031e160c03020f0a030c06030f 69
    0x1c0c8500c40340c9260041169001c03c8000107401440e8902e411030a11a000b1383c0c1400040000041c00d1040503002c12041c00c2e403411084a8840e410465000c5a001c00d803025400500d59450307036900d032581c0782403040941d8030001c0c101e410082140200204c46118001e04001c0d1070300d0b80c3c00b00791a6616000498540000110000e10700640842080f0044426200410840a0940003884115901c405002e8074041c011040b05c0482e8844600d04071282e0800d0145510040b050019050f0303030b40e40d03100c9402c0ea920043d401c00120203001d180e0340e510358260260701c4001840d108210700d002c0e2144041b60719802582c0405104625003004001400000c20540344066000790b0034039491020341c54003402c1d40164050b4844e160103503503802100c031a828441c01048481c902c01440c5082c0c9114a00001030104401a0b1000d43d0244a1844400998001d0f4098107118582456609042d40104194041e41024141c400c150717000041c030000e0f0480409004036010f604000c0b401d40c411a10f1000039099030020 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 52606739 1250 52605489 52605491
    0x16030e01020f0912060402030303070e0103110c0d0305090601050102070501120f020c0a05012d050612010c0e040e031608070804050d06020901080708060901120609082803090b010311060706 83
    0x1010318000900000b0143c1100842e4580c8110703601c1d81143d41c541c1d0040b44c001c0e41c990024400111460b000d075100d0308400c2014540010b011084082c800a540c0002c025400303a50300c40001d007820b13281c05108043e0003404001c010f1845625200000755200102d00480f03041003554400f50640c1411508000407101c1201e01c15505c5280b01540c483c0e90b0320185100340d44039800d00003201c480300d2040303455101c00c0b00311859446000010b010200084d1101508072500b04001080c1c44510860a00c0750710688a034030b0355030700400300300c0d00c04110a40320b640e109528a508200711414180b2216418000e90030f0744010007030f480e008107040c01c1c00d160003a0b51206400c0440111101c0c02c2041940c000c02c1902d000341c0f00c07080c45464058040303800c800200e034800e410161030001402420380128411070014403a000c003088500b1640e840030500c0c0c00568440c844040c200b40c10480000601c0c0c0c0c0c4031a80401840e04214002c0301c0e0b10f41031081c01040c072020300250b80c011020a42d5440e40c4086490907904680 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 52607989 1250 52606739 52606747
    0x21305040f0e0706090b070b13060c020102090a0f05061b070305030708041508090a0b09030705070906060f021501050603150913031b030903060506060c0a0804050301061d16030e0102 80
    0x10494010380781490250b0040d01843c180820024007565180096035000280e0a003051015615003035480806060a48400b803000050300004095024074090080f44d50300168403080c8420034810300884075000659a001c0041c428401c0e52120382c1600c3c520000c4c0190686036031134100600b802c1135290f40014005000001d651402c0c00010030007042128140c0d4210300404251140880d41c940007074a22070000d4001ca040f034004541000d4000c2e400c01058016a4070f480600c0c1d48040c0307485480e51282000030b482d01010482e02c1e400800c001b43c104410b0000e40b07022170074000000c40c1d200341401150b00c18070020011555200d103c2e020481e00320760203170546046082245414240d800c208904070b00103a00c98070110300028140461150140d41503d0b1208058110303a0341c50050003000b400103406c44820302c0903140010b020403500006a00840c092a0f030307941000180360a5601c01c2e00f20240504010400402d10044084020391003c00381d41d4030310a00e890721004a0280c182d07000e070b10645d580081 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 52609239 1250 52607989 52608011
    0x81002070c0f080a0507060c02061903021c0b0906010806130c02031606021803161a12042003030702010c02091801020c0706110d020d0c08090306040311010513020303090402130504 79
    0xa0070b04c250600a50407214842c1d0340d11003c581007030300450001c1d0007000501140390a2800c0100c03038081d4609030300b000b50501700800c003000d2104000c54981e81c10b458480c8400354041c14494551034008600386403047d0f03030386401c1020400801c1c0c0540d50310080e0707507101140c1213420f01c20310a48681d403400c01c0317100000382001e040c00e001a401c1069022030340507580031044a6440c0004c1c0e1205a0440100105081850081c1440784100c101c00d6150944000700702c0240c01c400740045c1c0d548154803840c1c0c910780240700710918041c02d03400c08034040c0c000d6000300301d9040907030f030400c0c018a15264101c0e5260320b1760782c40c0000380d6039921561034001381540c00820620130300240070611030180c4420ba91441c00b010b130700c000529910b40c0140c0c200000350b008551507540031b910500014110760300900c1d52500e80f02c000300c08130345000000c64099000412400709039000c6a828020750783c101c054445d50030f00b4100140c0019803680708500900c1d03c03880d40002c0d8001c04040401b80314000300002003081103074000d15 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 52610489 1250 52609239 52609243
    0xe0a030806040c0c02010206070f030e0f060423060a02030405150108060712060e060409020a0b03010905190c0f11010603060513020909070e04031b02030102070f0c050a081002070c0f08 81
    0x25980c65114a042101452400e840b801e0413007034483e0140c0c0100301d0794640b92740940300c40c9056411074041585a110480d2210740c100305410317091078110020f000c01d01d4281046181c400d504d03080120204500e8010005101000500e0b03900801a4107005a4a0312181360161410341e403160b40000303642d01103000080045010400741c0c4180e011303031200c03400a40d940700145d00325900f60181e00e071400c0c1000003280710303802d06900c00001288043d105080245e2624000754050304240e014031010b40c0c0790030811612000074050342c41401c01c518420f0008803501302014100400e0f1007440740030860501d14108040c00250030400085800c51010081341c144003140824403013160b0070503805003031090702240c450007001400c00d04427418101001010b85603a6000c9401c203540c5040100c0d00081803803d900565407c0c801410b01da441010705000300c904900c1c194100d80c1c0c03988c0c001482151100d07410050218007064512503c3c450010040e40c803099483c0607004011300340c104a00345854424042461580 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 52611739 1250 52610489 52610491
    0x130f050106092007061503081801181202040b06040b040803040806070c05070303050f0f0a0309050c10020304090902030304031403030a0e0105011a0a02010f020a030f11030c0f0304060e0a0308 84
    0x201c0c50a02c000b440301100f21140c400b600a035540c2c2c00000b0804000881c2580e0b0010210b0130314075803003020296581c5c45104003a04a40c40e946581042203800802540c1c112103116802002840c04d00003c610303042c1d6454110146810203801a82c541100300001d5480c2002c84002d40642444207448036241c9444581c3d03034210303004240851190f5404900010b005a9016400d1607019004103081425541c01302c8064000800b0000380c0102800940c1021032108040c01860030507560000c2d9407426814424130780080740700224021108500c43d0075600e0b034040b04540550f07902490209410142d440441c0c65031084ae400030b808180c0c01c850040c0c5510020004500450a42c00144950818044030f07c2c202c0f0003e118840030314510f8546070f0b071855109c0c0f015001103c068000000e2410003c45140166440140a040000e0f6504006071650b05244594001b003440e0500c854110720701603040d170200d803080000030003824001000041c01c0010503000050591481c800783d6600701130519001c0c0c10404 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 52612989 1250 52611739 52611749
    0x3020105060a150f03021201030303141602061602160f0f14030309040b040b03010c08070f02060105030a020105070203240109060b0307080708070201091a0403020f030301080304030605130f050106 86
    0x400c20011a04501c1d02c4681481680d6141248601c1c090004005449000f078407411341050640910100d08840c070007404042c020b41c000d460102e401c00118417010403994000b412081e1607004000d9a40d41c0c2540095030650000003502220110705912205078130700052402c00540e034905030301d004501c6166040b00002220360304504014900e480311584000e021150340c40c0c50701948184030396526442c042d0460142c1e180d0140c00050064078102c0880d081d542c03040c56030004501600700340003105520002c0c02d104944103101401555050500180c0c843d040d01001030f042050108240c02955014860a40d0340c03154261069103200c6001244c1070844424482c17000410300c1c026001554041720b00c1168800d800782d6680005a540f00001500d1400b00a003802085650b41c43c0800c001807203000300c101c03121500c108030080d5480c01e403030002e103044011495072a0310340051004002e075040010a8a05603680050081881d640c0c070b9020516007040803102a000255140001042c0705040d440344080d50 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 52614239 1250 52612989 52612991
    0x30e03070f181104230105040306090302010b13090c052403130c060503070509010809030d0f0212060a030507030f0615121101050a05040317070506040302030c07080610060e01020f0d050403030201 86
    0x31583da1500460f038000c0c0c0c03080c0c143d0030642402c00301c0c0f619401e074038801a5400505286080c5601d940340c010445130030441c11009130395506004000da24040049081094111109101c51585503545a201e9100c0c0c2c0b08090003070441c004041c800000700030301040c03102001002c04e5103030310701a00102c400d8001c2c1101522080701d090408600c251140040720311038100794540614000f45a00110740c40c1c2e00003040d034001d0303000a01c4403061142c1180904d182688800501503150a084d21041c184100068610f0b40310398440942000000d80100303200007181d400411a0325021840c2c20b00c0800b908400140f8182034a0840700410709801c1c00d10300d91030850040703242040015a40713005590500c0790b10600800b28034140300030000070340e90043e00d00940000958190402005a0311540317002c40039941180035030808222100100c10403c40c040040c20494020611400e0041c1c114040400317038010001080542040d1030007a900070004460200721f02c5040b5100c001c103400000300981c026000440040d = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 52615489 1250 52614239 52614251
    0x7050f0a1505010605030c0703020f0706020d0e060915031009050106050703020d0e011409010c050109060522031209111003060f05010c020a0b0901090f0305010209040507051303030e03070f18 84
    0x440802d1142c40d050b202552502499078880d10264001e580122604808501c182d001503603080c002801070700001c0c42c0f25002064451180d180280c0706038124101035010b200f06002c00c5a443c1e4803019418072802401000d684d603500c660b28000800c035440d801c00d20040b41010000512143d20800808810f40650300742c50000003c0301c0c08850703a240c0c900c0710900180900c1c2021084807020703801000142c0c414184811010a1f0b590380509552001d1070031707115240d868007004400020b4004078542e00e10030340610019110300d540e01400c080700b040300651105a60b41d0803c41086041c841c0c00d46038220041c5070700600c80c1540002409040d0500980760103c0136550b00240c13550240940303400d800c1e4014540741302e150811100c019a50031809000e13040140c0e250001071501400f040400146000e82d0000da90307409014203200039204041c0c1310a04004080010760258003142d04808166545441e025542240c0d480009217486115002422500f69646000804040b0300601c0801c0f01003809080c13100d = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 52616739 1250 52615489 52615523
    0x20f06070c03030503060a090f09060605120307060f0b220b040b182a0c07121e0804080312040203010c0e092a12060301111801030203090307050f0a 65
    0x500030385400816402401c1801c0c00000e00803406158031000143c8128052a540c14000c02529180c11000050340d40c5e80501c9800e20001c1d00404028000c184d405403011300d103e030222640d81c8aa50000750140d03a036034169211904080d0405905103400a00d10b202801203450000864108a0800c0d0038070303850400d491a4a0800e400b409180d80707401405643c4010b21140f0b041a0348a0060003110070b1410f0030301494180c0c903007010240d8000f0b103050300d084d00c59a008040500c0c15155400c2a400503040d40503c00c00240d4581100b006001801d410501108251400840701e02980e0013401043c040401d68042c0152040c210500c01d5000301e000340305500029000b907401c544a04d00d4030750498142c00024580014410500024540040d00030700400080101c03035403240c2200c9001c0c02c0d45140301c011300c00c507454240910710900450241a524221586400c814143c90380d40c443c6041c03540100000364598028000e58201c2c41c0c0002c19a41e030304210b607085d16154100c0b44421609a903512000301c134 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 52617989 1250 52616739 52616749
    0x10c0306080c100810150c120513050f041b03090c0f0b090108090c03070b0406030c02060601020d1409060d021b010e03090d0f0c15020d1b0303090f0f05030403020f 72
    0x6288002e0110801c15001d50f00c2111041001171111600c01068500003443c0041da480407003200303803103680e12142da0700140b5203001250500d814201c100316083c07241a101000c0b4081c03042c11544202c508000308900400400c010703019078070080d0140c81e03e4040f04a04550190048190f051142ca11400000e0710b98188002d001620300400e14030880500028401c0d500680c015900006240f003101c0940d0110000240b501c0d029810803208480045404c005541c0c0500270740e001d0100d02e0010300041e10348240003e5841d400b00348050300700b14000060401c100c3c166000c81c0c04175035020701020b40d80d05090302d00c0c030301940c01641d8050218008140840c0d000c5010700c15000080040809985001c509000700281c000b0346190a0301c00102d100c10020004000209a8001b403403442c0040c10301b00e030300c000041e08104040059405105103440c1051500b002005540d14003503050500140724001d900f0000d00700d03448000010070016056800c0400d210300000904222482199400c03890780d288000e000c = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 52619239 1250 52617989 52618003
    0x601030c0303080c070c09090b0f041a071b20060301060804150f0e061006020a0302060406151203020a15110a080402040b0402120f010512150a1805010c030608 70
    0x191504220003001e00000e0300c40d601880d0859400241c1c2414114113445200e902121540000740b0075942d420003c0c10480352080495101403030308111802440d15459104810003421402145d01911000040c2e500340540360040e5141d40d501074a10048c2038514000741203210350004000c0482036141c408525103041c0003100e043e500c060340c4607002603e6664941750070703c4420303450311760309a2286000e8001c14100d00c07034118607800d040d004100b14144540e03a10752200441d04180115001f0f0003804000c26000580c0c1c9402903844000042d80c5016240351031007019064001440ea00c1c882c41c03c0c0d0051640c0041c0554115019041c114004130807840000e044504500500040403420310a000c1c50600400380715511a00140000c1148400c01c0c0018040386d10404500d1030104100701481526a1115601805000c0907100c400f00d00c50340103041c4e544e94030301529803400d81e030041c000035440c0c07443c58108462010034102c0c0144180071503c0d03c00d01900400c015540041e15040001409080028000d = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 52620489 1250 52619239 52619243
    0x801060501120b010509060a0e0f030f1906090807030507030e0316030303090501060308030108010609060503030a0e190e040308060f0d080405010e01090b03010609050306090a030e121e030406090503060103 90
    0x10b01c070b040e04101d00e541e010b0280c1e4411103040c00310904c0880c0c07260f1200401050041c0786c56480103002006082044100038070b018005001e940000e01940911400040300d4421300764010a0101d40700944c640340c4083e2120050013000340c41e0200b00722041640200203440e006110b0b40b1000c20b11103944003810390f1502914103091180303c40031402c10120780039501c09a9220702a400201d440c0783c9944501e0120380c000c0e4030060f201e83d035a04040000408600c82e81d0058074040340590301d000340400b001041c00401c00c0c01c481c401c154a03008403600410246000000b020f00040c0e186044c41c1c50b08000d8003c540c03c40740315000d0b1520600240d1306242001092800f5a80b100c80325003132070300305401190003040d17031070216061120325000130400c00c824801450003803200b03030788030025581880b050504084000d00384071003590000030b1800002c0e81015640400140940c0c94420400801c1d036420310b44600020f8814140364004076000c6034010200c020800c0d900e0548890404c10750300c0c030034103984d50b03024880 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 52621739 1250 52620489 52620497
    0x10e07090504110d050129010f0306030f12020a0b0c12070c0b0406020a050c0f0607090b04030b06130209061207110a05101505060309010204030209160f0c0c09180506010801060501 79
    0x2c043c0305480c01d040150030990144000207001108042d001c40c1520700d0000f400f502d15440e059008107513a00480001c00401d503881c040c001c441c40d43e0303111411020000e0380180141000240c1002d080d20800c0011501c58202e800c100c2142010540c26141c2ea02c00368a20304003500101c0003ca540340034146103c4120b510074440955556192900d50003074100e4041340040040401a50f901c00400300840001003003450040d1503603040003413002d407032101540d102c6142a070091004002140c0394900282e4091002e5900400c1103100b010703d000244200100b00d50300540110341e41c100c840504002610468064441c00092074403007500343c0d0b0350b44102c00010710691103140f01e008040d010b42c02c4032140f2021080741001c203503102c0740011255001203400113082c0c4c6d40401c040065203801071039186c1010700c2642c1c941d00f21004035030040611008500d180140078910049000b08014800c982004101d616420000300083d8403a10405a201c690290b0700d0788640d400200d40c2d07003018468a000c48005841b = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 52622989 1250 52621739 52621763
    0x130e060d062408070801050603060103030507060e010204050a0803192c061303122c09040213020c0a0629090702030d050c07050d030b0609010302070507050d05010e07090504 76
    0x16941000d80400e914140400ba001c02056030821032106075075010385241000b0300700c1c050a1504881c2120030040c02c2c14803a603c4580104040380e0000100c038906500040089241404042000d0191040b46d0246070000180036001490031000300240c1004840b104d00e16040e500c1541c011030b4500d001c001a5140b81c19620071424442e00300d00840419810040c2010741000400e280e941d40c0c860031a4070603645990200303c01708074558000c1e10101d00a9241801c9a82e5140c20302010715004c0610044034010241c030300102d4150741c0c0b110003000d54514001020341d91650b0780000203882c0c0c010003034100c80c85820024244010741c00c45200601d01044044001200f0380701d074042100c0c40801420700015404200084118a0701c0da0080038403c243c0b105003e641c4042524010785003105200840042501c0c4c4242c5036441c1d0b0720001200c03d004d409180260300c682c8a41405824039000e0f41c059917101104050340d804000041d0085402442490140c51f005555129000c080c5c40e000c650003031035540c03415 = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 52624239 1250 52622989 52622993
    0x9011404050703061a070c0e0907060206010602030c0303041709130b130e0c0d030c0828050c12030a0e0304030b060f1203121003051605040e01060501091404020c0d05130e060d 77
    0x1401405080d8094011f0100345690b0f01d03071182c5241c4080d1048400f035000382c01c0c00d0102036010028640107015510040d440c1440d01960140c50340005000103024070042c03c0c8614241b44d96030b0a6601c841c0005100700c407a03414030303941d44009001c03a0113602c0c010b0f10034400c600205140791052040150040028013800340d100300c2000380c1000010400c4050000701031585000c1540b85014003078211041e00c040e0007802041d403010b03200944e40010102040401c001c41c0301c081c003002c26100c095180c000300303040c7c882d11010701d00b80c0a0860303115440305501c00428000140240902070a0042e81c0036605001d5082a403004d10480d0003103092113207216407080119065211200e40f800d9030011143d412814502d44070b40d6a9030900f1080000300642074144107061000746001d1281d9081052103400800807185008000391a4881030320802121480400b03014200d0348a540441e10b022100f02c040e02d001280000000c1e0140d000702c2907440350451010000700700d01642c07583e0035000300f07401000702803455819 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 52625489 1250 52624239 52624289
    0xf06030c020a0b09010212010306020d110906070b0408160b060a120f12030f0606020a020102010e0d17061801060f020d08010b04120f05060c1b06010302060f030a02090901140405070306 81
    0x14180c09402e6608010140803003002c0403202340070318455080542d464010303080010690304900070804400000300400c84c5c1d1580c1c0c2a00702e440481e400102000c0300d82d00c40c1001040c0d80240e2100d82516112800d00c002040609082e01d480754904135155501c0c0c0d61201d24002464070340d0540240250344028680f0003080f045140550381c400140b8001c02d5000c84040140309440c01c0740c1c06140543c0c003800e1400210b60702801070900d0740100f00b0003029407600e940c4009102e03104182516101101c00d2010904580740c000001c60450000404007940d540c5d0361071b00400c408a080c1c00d14005010754412001c1c41707481003501e281200c80304100c0904017030404209800703c40d00c034442100e603034600d594050000755080c49920b01c503c0d020001c3c1d54481c2d580b95911020f00d41c981b1a846850b402c22001480182d0f6080207441c1d030022100c40e216281d030340d0200201c009100d60560340d5800315040000068090b0911034002c6520015103007070007980c0700c89000b5401d0300c1c018000e80000b0403a85d01401d580703540c5 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 52626739 1250 52625489 52625491
    0x5120606101103090301060b0406081305100902041506020601030510050f010504020a0513080714060c07060c0311010525020309010903060b040f15030b0711060402041805030c070f06030c020a0b 85
    0xc0c0b4416079207800d6240000a084404552000700c481a01180420620382c018201e65800316a224640809003065501d0544501ea520102606150348154004c151740700c5602c54111004400c819902990b103501010303541e0340092000b142c083c8100302c85520709400c0b60140e90700622804411050300d90800341004003941020300150200315051000c1034140c0205000c86008000e010003400b020390030207001901c245101c2c2c56050081808100d09660b0303500004000080350345600c2c1000000780c580c42e00b11070242d0810448030b2550f00b80406e10102014496185444500d4010b0f00b00c050322481c032042e62a401204c14180c04504c00c050100302091058010215070707600240001200c02d000d05080e000c0722200039949010040140c0107000304030340c001c0040d4001c0c10740d080554280c43d80705030450f500d1000500003030240703450703c41404d80000803100d44c0c1c021590140c00e498458120350400e9644201c203102d0008043d040740000201c181c024400c0c42480b4006a01a18001c41a600c418500b510 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 52627989 1250 52626739 52626767
    0x80a0c0312050a0b120304050114070201090812040603050f0106020a020111120a0809010c111b0d021201020901080a0c0f11031204030c0b0108030a0801030b071205100512060610 78
    0x26512410340c00500b845070702c2c0b081e070a0700d43c001001905802801400915610401c25503801080b092101d40e821840056129500402c025034680300c502c01200c0401c401e6020450510480604161500524010304141d5a8560b0b04021903514405c0209505400f0301c034080150700203180e6400507510402580c412040b81c6822640070702c16001990042d60b010250340400140c00030188030283c802030007000c0807941d07149050140399403400040c5484003406002c10b01151103441c0c04149036210b019080124a8000345091005007010180034082e40c4042107050005440c40009540b659141c45200e00740611941c40650480880805490308195880642084d00c424010051000d1a040205208912969031403400c54850b14180020b001d040e004404940c0043c8a4130741d80e02d5228803440d04413a000002c031012034440d001d007a50030804030021240f415042c80104642d04103000303280340448a064550501c990380500740503880f00820348466503c1156800c154010354840c02842c00101 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 52629239 1250 52627989 52627997
    0x20d0b0702010e0303010603090c051e060a090302040c081510050a12090204051807090e0604080a030b030a110a0b04080a081b0307030305010911070201020d030c030204030218010305060c07080a0c03 87
    0x303c210303000d0307469901300760306c6a0f00007034840600104200f440d1f0304520060600b03441800e841c00405628508114022170801e01602000c2a40b6131410701c24503140000315001b43c000c03c5151005e48000b0055101180c0748070200d07044000c201c0990411131180c005140840cac1d5540e0508946030001c0761038417019007503044060b4503a02c1000240e03969100343c034015071340c441074082c082c9201205c680c1403a08590003299070b01d1603c01c0003c000d6a01107400355000e540316000c10759844022105800511000090a40512500c0034040412241e1001c0d146103030030403a03910718941d6607445001c0c5180b0480c05000c1180d0001c2110b1400101480c000c0c0c070010345042c00341c044480381441180d18640000e02c06400082d201c81c01001002854840d01012001c100b44242c80d050a80d00040c0d550049824150109903a40d0340c08a4400e200c3c0c0e0507140034581c014a0175151040301941d4000c540300a000a440d540250000301d03200c003c1081c220b5003151760043c8541e003010322403202980c1c41a4440d405030244 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 52630489 1250 52629239 52629251
    0x70e010903050105010e07020d0807090501080403140310030507140a0e09030702030a060b091003020f011404080d021c0302160609020604120602180105090303180d0210170c07020d0b070201 83
    0x1d00078082c4d81e0103040f20464495a915002e20024a000c881100c007a0600c0502010312544079402421b900c10f46500303003010143e9860724a000c9400c0000c007850400b90b0b03c0d0110910201c40800c0f0243c9046900400464070420384694842c2609015903083c25401013125104008806800760429801400c00d010f0300d00740a41500070074102070711071104a82d0344e5a541e556503541d00d0011403213604140d41c1440d000307440381964040707551100142d101d00d06000703075810040c158110520845019280030400d4460403084070b2000381d681c0c0c000d207022070054072090415016107807213482a5148000c0c44441c41c00b441c00140c8510005001c841c6060380c01101c02c200c01718180401d81c54541c645c522600340140c1c0e600098002c00700341074000854034100a404c10044016543c000203403860707412f6140390710b140b00100c900081c48020880100a400c4101724001c0e2166030b0f0881189041c0d40001707034901e01d00c1d03034840203031401c0c0e403150502c001d40c00800204e17000042156040746c0d652044a6000025107 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 52631739 1250 52630489 52630493
    0x1908040c0b131809050319090b0403030c06090203101107140d05071b270b01081501030f0902130204030b0a0216080703020a0c080706020c030105060d06090201090e0a050114010c0506070e010903 85
    0x25a842447c0c401e42280020b00c42d0011150302c03d40c4c800007030840c030085609050450307900518020400c1406801c46484003804d1084d5039090000c0420306c4001001000f5903202d43d071a2507500e4000460584110174054156070390b856004c640001c4000d655a200c510708005603940110082051040f07404132150f840c0045162910b82041482d40903288090401c801c41c840f925034281e640c0d00d0000e41c10020700500380004800c1d11400c03203840a500f4200860b1a80382428044002c096550001c4e42c4401d10744100070b9881160740c010000e0700e02501a4041d00e5550045e08030a134803c2400000c4120071000703c500201c0c40300b070081d000709442403043d034445084507101d00140c80165000f40041d85c200d00c10400842e0f404001e044a401d41c140e000748058035105001542c82c21030180c1c00341a06840d04041400c581c840da07010b4001d08110380301ca4615080c00c0c09100d000b41000d008003409503404604002056002d0400f92070300580c004020300403035a42c41c000b21101d01c01500c5280c10b11a441c280800 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 52632989 1250 52631739 52631743
    0x50a0e091c02030301050f010c0b0c030a0f090803040203070f060e010f05040503010207030905040b150702040509010b0619140405061b070503010e0109060c080c04030809061908040c0b13180905 85
    0x25039110701d60007191a541000d040110004120407220305200b40a0b04041c00906072030100f540c0030b2403046e0043c0d1640e07103110004002d03006a0b00074500c10317844d00a04404019614011b98040c2d0b0094045425444d12241c3d2640b8942c0140690030210f401407070040010742c130031440003d5000c140d2800b14200b9035114080388c26a0010f4408070b000c84c241140520543c1003070311549008110444032003000c08c6140ca41d20045104d030030f001034041c175103850001d0f800700c02c00d4210b008501e0002e8069030303840180000c0c100c1c420510110034000505e228442e900181d0b015015102a036100030001840d0005110390001c3c040d00795413211106018404001409550a1259120020307a44002148a1a1034548201207d0b03000b44500b00340101d030300900000d41180740c1904c4c1620307807003910320b55501e60b1600020400c2c096800c00e04141045594440c0758290b005d1800d0303006500c0352040d00c1e1020384400722812a40200c2c1420024850440c10400500c02d48040c1111a00301500300000c40c000c3d640c441ca4 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 52634239 1250 52632989 52633033
    0x207020d050a050609010b0109090b03070509070804060605041a0103020706060b03090f06010b030411060304050c0d081b010b01080a0b010c020a030302030406121e23100513020301050a0e09 83
    0x50707a40d0304503002040920009008481e400721109008102c0c0080000004e0085045400354803034460f900c130000d803242d80741004040007400c0000d00c2442d4074500848003c2c60f984046808460550030a80000ba803414940140d01c00c4c0000d441c02c030803410174030600440080d0071550045c1c900d26100d2100086904d156801980107080300c8000e00080001c401e00703a850704106038811203140408000304000729991090280b821441140c02503500e442d14140545046031003100305920216031401801040000c2c1d004200241500801104001030000300a088034111243c41d4041949200012680480c81e07004658200301410a40043c800903001b19988040c80c0e04110050391000606025143e00003140301c10509508000780581034004080310310742088003a003030f00d00f42d4035101c000c040b003400400190340e0003990341039400851502d20303d04941003076071b8400c00f8042c00061104001c03001482c000c0303e060301c0740a0700c00044186002e800f080402c100a2480e0600c0c041c07003000e81610501840d1315 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 52635489 1250 52634239 52634243
    0x207020d060501230a081015082e180204180602030a060504140705040b310e06040605090103020d081b01060302130522020a1a121b030c0901030207020d 67
    0x2c207a5590b025944e0305590208000e814814540064100480320380050080c00c0000c0e242c4d404201030310802c0f00401100741c681c001305564080e0a03490108011456104200c6407080165101c1e1280c09442c0c0300c0c1191400302241c0c82c00d8001070040030150070150090945a207039861440032130b0b0140d85560040342c000341c031441000313600c40008000d245024065480c0320340000c1902003050410b01e00c05817062141d8810315030868400300708140140146004400030b14038020400c03201850380c41e8429400070f0305010b80741100f140c10010502c0c6081a100e10300039184003420380030880e4219003c1043c9100690000c40fa50b0504104030f9090f19a040000607000f8084d01c00816100d04500c1003040460500c10231803240c910308030030401d0190a04444030442c0b500403141c0da5402441d400810f4501c0002e40080e11007081c2d80c10708085600c0000c2c0100360020000b490500e8549070840810004400c4499417940400c0c14000300300001000c0009103c1142d050600600c1c0061aa0208101406c0081c0c1 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 52636739 1250 52635489 52635509
    0x20403060b0a230a0308070605040605010b160b0903040306140412020a020904021e0303030c0c060c072d02100503070f02010e070b0a02070819020a060309030504090207020d060501 79
    0x1001001180e001e2190281002c88004076800e040c04000e8a1007001c0b020118690080800a030501d5100c07810302c3c1019542204245a41e0a020304180c0080c0c84141e07021101e80b85080000180d407001002690252050704096841201c2141c44036160709402810160705070004100c00000200345104078a901da0510903100384a10707160814403500c0b041031101c80c003950492000000160380c0e161030983d210f44e0441c2c900d80700f0307043c03058826200741c0601500d60301803000009008846043e200680a8038400300102c98041da5a40a002e640d8020b4040040c850601c00107001c400071070f40300305da94004018440d260401c01043e000540c1c014020400344001c207000209001000d0744c4001d001424050600007401484c03821100c03c1d64030b1200e4400c7c006404400301c1c9800c42036200b404584000c0803000100c1d080b600031000070010601d04900101d1041076510300002c2c0060082c002c4803400c82c0c05451312270809140c400c1c0741000e50300c0070a00301d030b00c5101d000c1130740009011407085074040c0101c006 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 52637989 1250 52636739 52636747
    0x30914010903030b0310050c031305030702090702160b1309051810020403030305010506070c150203160b010f050d0302070501050304030c08030403020c04050a06030206040b0711030d02030c010f05090606010c020a090f02 96
    0x400d046c01c101c081502000071a0602c410004001c0440d012203401010340074100e104d004042c01c0c69070941c026000c000b584000d40d2800d001c403a0303500044128000d00b20840d84100c035a6142c000c0c41d402e200c2c903c4070308045016504100042c0045034001c80d80001c00d0300c07540c410b400e01c007000e1904002d0400681d02d05941d020030288181a0b02d03218040c0500b4080ea40e26240c90400c2e00c900c04515800d206412541482a2007203145510038002d4a44107d4501c0c84c07880081801c1c070300014250b800b40645000e50380c100c41c0000d180e1500111160340302c0d0b00350700980031441c1018011201ca9200600c190140416403000100181080005511450280d400340c903000195500f0081a140040e1080c4200c070f0034120180056074501040700d04a416900c40f55070b88140c246041042403219446035030307040c01003030070120710b43c1d40210042040c03d0030b07a80200800351104c2041d07011144151070510040e404200082e455501400c11402c0c1640018041c05406a0b6010108140c442c860045070304242c000ca = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 52639239 1250 52637989 52638011
    0x9020604060f030506040b0f191223010c09090c051605060603070b04080d18080a05100e030703080103020d140d0903060e0303010305030901120b040f0506011b020a0603091401090303 80
    0x841902d0700150111b80911118528200103021062900c80c4d05100b0250408103800c1d564841821800604040e9880441c560705e60400381200400071b055041d091002c0c184c0c10305503060601c200001c03122152681740e03d442c100000d0100030b02c1d00300a00014008100030412040e0340c6080864500b9108000400b90303481c0480078581001c1c020f07440304520401c144802c0c05156030100d04564881428074011910b030b041c2441c448104046030f800340c200c6000e2540d1143c00c0c44030201d022500200401e00c1031154030000b440d4540c0e28404d00b0b90103400200b81100500052800019119200340258895244100048422401d00d00c1141022010403480f117001c204105490117160740c10060200958107544c50350302c4013900c0b4071074100840e04201060f680c41c0c030340411a601600c48540003500c01c01405210301c1141d4001c0200303552042c046400703210810a0380c000340c0c04003000594003400d580340043c40c1c59410f40c042d00c8029000c0303421460004a48558180910078668418001da80108400d0400 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 52640489 1250 52639239 52639241
    0x9050c01080405030a0e0d1209030302240105060906070b010e090f1b01050a09080d0c0317071e020109020409051005070503070203030103021302040b2a030711060d09020604060f03 79
    0x1090850520000c80200808900c000c03060f1400182c50b0304001641c0340c1d0b480009030345084103440080c100418507003501103060f4071030100400d80e4031035000c58a8207170241031000b48628080d181d40c117155440718010300041c24004050072041d82c024015a040c080640d8403805075031741c241c002d062003204840c104000b0f0a000c02400d83e1200c484005002516661480350000c407080402040c10b101d00014081e0040d0301c1083c880006102410a680110301d10540c01050200c1c120020381c009024107030003205148092504c94026805030f1112500f401c0c1017007038240c0344000140c0440965580300403c20158403117010f190782d20341c81040039150606118000d8001c03140064051030800078280200a040c030340010840741500c0d0100c846180000315180020082c1c0704c1c540044445071408201e0450304180000811403429200c1c2d40b0724030302034201d0001036481c02902e0024003120352542405c42030341004802003001400400300070807200f1040c1c0101d070469005a10442c005a42e420700080d507186c3c1 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 52641739 1250 52640489 52640503
    0x10030f0f05060310020903060f15060406050903100204080303040b0402060c0307060501090f020c0a171309050405150606040902090406090203010803070317070806060d0b100c0b010504141b16060905 87
    0x40760740c00310f0070103545038003281d5540001071500e00c0c02e030381040109070326a440d01c2b40440901002440036a88a4803400300034102d811042480d400384c0725224500c00d000c003081c000c0c0c80665170b10304011800c40e07480d034551007801c003000f8000f0703a0005002c10010500402c140010607406003c1c410203c0c07194541181801200c810400290039184188090940c08102094000503242c00c4080710000700c0c040c00011100f841204041801d21035100f2001031804000c3e00306500ca60301030026038010340400380d104a003044040321030a40c490b800300010711102002e0f60250000d5400a44001089515115044104d03030080e08082d0700d80e4000b196500c100b503444861b410002c0b901c141c02814a040c41c0f403020348a14005808503114040200741d060300d110f01e50703000c0d030a4040010305040b07101c00c00c40d074098800c01511000342e940580a60002c50a82004e008503800700c1400000c104041d52543c0c4807035045400043d80e64660b041c06c0206c4200014047e8040c1c08560007010b00048081e541e2030494a0000 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 52642989 1250 52641739 52641763
    0x31c08180303040b040302150f09100603031b03050c03030901090c14030706050f070209070e040c050408060a020c03070507030c0e09010b0108060f031f0e070519030210030f0f050603 80
    0x480015504200503010050b00d070801e034003420f942e42c02d456a180590404c145a241d4260003e807180400200c400844032490103200d030501507820045809401d01d0a8441a010140206a0301000482c81400518010120b40e0082c0341c544d0800d07004c042c40307604583c81650202d115039107800c00c0d0f109004140c03850702c000f00100b2501210014000c004691203500511400301844008a040c8400b082e08104680d07038541d0081040034203150080c0c2c05003038030b400f0302c0e20b05029924004050039003601a004070703402e640c2c0c2c01008104903504c034400f001c0a58417000b490880ca01007170111b42e000070010041a000b8620807000d00c441d00e8180100d070394000320b004180d4141d603810400c0743c01969801048998010790291200031a4521960210f40303010600081030024092072000c00d8864141d80e48092140c0140f9410b42d9201c59461081080318444001514003600807030104100600c0c1808194034078642038140840d1006102030000103c0c3d0303200b40386c02d08036900c4408200052070240501c4006030 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 52644239 1250 52642989 52643011
    0x6140606040f03020405100512060a0509070602150405070807060801150801150305220302030d050105010e01050d050a060905090c2809020702130905070f0e01050d12030b031c08 78
    0xe02d86101060118041c1c03001038015030f0b079417020942c5181070306601000b400005e04101884d030003808030035559100850300c20060501c0d04000c28000d0f900410002c0848400f030780240003080119031030240070140076000721440d205681d0000381300a002e114900090066403114215076140182c001410604006a03408100c5028014881c50500d500349035600b842c949000250340d42c81104070010070b1515681e491110700807080e440c04240d0b000000b41048c00c10007200303100b203980c1e50340150742c5144004801e0340460414001018000010303400a030f071200070b01d500883c006a4076060482101ca003911000a2500040d8120f074a604120b004001552128904035040d1021440c401c03010215500030b03814013640000ea040c007555181c5c14404421001402d0420003003285180040c3c1c1d0350601c0c855906542c8a618000070700c580d2451312141240e60103000b005e481005641c0b1884081031502500c0c040c03542c0c0d100d07403507041c1d10100f011241340300d03203211059180306c82d0400145c0720354030043c9a90301da1 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 52645489 1250 52644239 52644247
    0x31103092706062106010201090206031014030102030103020a17010207381b0a02070b040e0412020a020d0b06011b0311010b0909070302010c020109090e030d0e03160308090a0c0306140606 82
    0x10889001c0c0001130000550741c41020b80d203804004034007624007800b019621441c00300a00080d1242d20010b80308a0781c012203000c10b03404241e000c1c1400d0780001d100280d0700c2034400408205100200c8554402d00b80920001440d240440d078402c40304145005c1e650700c070b03186180f1912080c1118448503466041011400310703003a2038041d402c400c400e502403240708215070011440c0b1070702d58007c02440c130142940741c11040e00c2d181c0300d00b031060501c0c0e4120340c2610a189040b5030f084200c1c1c00440c3d1020041d8000e401203c0c000240c0d1100081010040c0086c1d04001c544414010b981001020410b45c40c0d10a903548180d8a000d03042840c2950440105680f243c1c05200900c14490800644001203035828200004001d40c1d500040c0d503409401c6e880540380d10308000314240d00000101c020400d11101f00f00030008112850035066131f80c09110104001e40e8584960140232900800082da4071034681800c07140c00030f02079a64003518044581c4200d50040d162002d8003001d0700e0003826143e015100340c03511820 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 52646739 1250 52645489 52645507
    0x603100302010e0303040b0409200a09060c0212010504140601080c010504030213020909150406090204030b061306081e0d0c0b04110114070803070e120a03110309270606 74
    0xa0106848000e041c400e2000c0c02c141180c03000d100b600c00030010030b5100341e00c2c0d598810707041002d40103442d046e660000c083c1e080d12100030000400da0f40401c1407030780c0e21149a420510140c03403010380b101099900010800d4420000d00090040d10f218600c2800c41c1c03855021100e0800d0b01c0c0c00c0c01038004881b50b4000c0c044034030099904c90240c400312901100c4a5000900105604c0d0081c0701d40b588032900701c541e40040004600130351001100c1500c003074408100c1981e841050904030b0149000040c618110040030401a14242c00c05401490003214005902581c920f10141303440c0c1e040d59070131011840480d03002c00c0303a10288001000404541800c1044a0440c3d4425010040081c8001c2101070020740b5098140d1055000442d00490702c00c05e99542c00c2107040808050708110342220000f058542e002810303040c240d11660013a05d02800510b0700420075541178403d5440c0d0028548c1a1006112061295440d1300c026418880c000c81400d440100010100103c1c040c02001280151001c004c030f0b1207 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 52647989 1250 52646739 52646761
    0x90605100612050c070605010b03071e0f05090a180e0601090c050f03130512180109060203090409080f0f09011e020a03030507120507080105011b0803040f0807050f010b040b0603 78
    0xd000b184201d40010142c3d91442c1c900064000c042c009403155181c40700105907440740200450268105480342c4800f0a490810801d01d0200c000719040081c05240414001900881c050070620030000e00d09c081244c0c448280400141e584030600746400d40301d02c486a034080017400f6036030140490203402c2c051032030300780f201900c0307071003500060312070741c5c40020009064080c034100fa1207413907503c20300b88c44008200081c8401c45070007401c1100081d09100c0e4944615602070701c592400c80e41180c01460514140108100092221146c1502c42c100100a11302c4044138080003030010700c034402c212644554480000500125907141c8600e1120004a007030400341e5000200081103540c50710b80450315940303642080b940c241c5002041c120440c20082481b121640180d4420305a9200fa6944a051141c612840160000d00500900110000c001207000700b6912150808147e0040e206c542c9048030982e0b4042c54641c1c084a08030303403650b50300b00e008034902c1e0502401b03400c80da00316281400c7d4100381c0c1d4000c1c = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 52649239 1250 52647989 52648007
    0x3040803011a0403080f0a030b0f031005100b03100f08190f081c0b01032037020f1905150702010b030a06060512011b030203040203031603030906051006 67
    0x942c607014191400c880d80018808403805107501507000c40d01d4101650703000030190080700b140d2011904120070b05150382040c40703001d030703401100500a1040c1e10410740e40c94010980900000302144444101294003100398000b18041d902124031008000d18150581c400484550020340040d00989103044c40e114240540300b200f95044151819500c4052400b10301c2071044d04820741500f01508080040c02080fa40070003401c1da401c0c0c0742885103070f5010302c80d421000c03005008540510418001950f13a280b42d405200d04080e11805298601031042240030300b102100b40002c3c005074021000882c0520080c0310041302c440801c00708c182006180c4d03488030380b0b4030300c00f0800c50b004070380740000941014800d410640621902030141c034070440450400720013604640c0211800f0707000204401c0224141403184440c59901d188410403225003420048020703600242c03060b0703410301c0305215001d0109881c1d000440410320075180000c859010780f83c08000e5440090000c1410050010304200b0a40c000842e0 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 52650489 1250 52649239 52649249
    0x160513140718050d0f050d0504050114031506030f01081006031a040c050a090b03060f0402010905090c070204020a0f1b0503040603021b010c1106090d1d12121e0304080301 75
    0x100080c50001c410003121004a03520043e4000c4500c9501418005ea1440ea003a0250007081615480e55140703c003621513204030311402d40010b207990340c081348065444c4080c58010039520740441d000c0000da13001444580081e5880c91100e650b41004005e4048100010120340165840a001b55440c5403901e02e41c590341104070101075040c4000180400c00d030200020301600000308001c050b0703610b500742140100314520199000b486280c0c08900040d007501341d20391140394140d4411460700e00b88004c1c4a159100075110f05148400ad1100c0070040e941c900280c00c1c403080658512400c60140c480050002401100b440800f0307019140304c1c0c0200c1c0000c030444003694101d007005030791a603e83e000c00311015414003100246500e4000300503048e9070300400400048415000f01c80ca5910b032441101c1d1640741d582c00410200f40d000d040745d10385030810365510000c0800140050310f013401c512002410045101804040550001006064400c036296004000d80e612103009080d40340c155150070f0248018020 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 52651739 1250 52650489 52650497
    0xf030305030a0b030105091c0e0d02060912060c030f15210304030f060b01390f050a0b04030216030302030d0203091c03020a08010b120403030f06081605131407 70
    0x148914100b03410400540f580600200000c0c6031031002c0d1601c1e107100c100a40c1c1c00c11205d81c1d4000401340700d2400300104c0500240780080302e101c80d50030428541e0041c400c5640010fa80840d40c0030510042c0031040c40303005410011a0b5a241201d45035444240091a40c9502e1090708c0c8911b445842e581198001c140030a080205150381145019185003e00d07400140349041c3c0c5460740040001c0d50b081884000341c00e03250401e0f00d0301c90303000304e03022003100003007424500f0440700090341450f07050403005e0342290081c000341402c1d8110341c43e5142000500c11080d078100d1001e00c00c1c0800c05074100104d040b40d00070f0f180c00c11149400c40c0d400079200e1040e101280034543d008000700f0203901e07040c01030510b04800d514099005490b0070001401940004400e5008540c219000040f410403031800c030b0f0201695071145900c01d42e15a41c050b0000d000341201006420f9640c4030200da1250100a03543d00414400c1941e1050b5141c40304002900c61354506402c4294100455260621001d4181f10780000756814 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 52652989 1250 52651739 52651741
    0xb011713020a08070b0d0b01080403050d1e050a0207121103091212070312060603380a080a050f010c0206011205010e1504060c0c15020c010f0609150e010f03030503 72
    0x41c50034500750050f2003a4011200000f400039040401045072139002c00c1e0900080100c100191101034003200c0c0980440c0c02080f40c08940c00c0503a0002c0b50314807c10540c450400c0d0001c10703000880b01c0c1100c141a00a500040c10300034008481c100a0fa980d003241352a101036495820f120782c50703010720f0368450701131959500741d110502c02c24000c640c0851141d00c5604d48440030fa090092900892904a442e09480d00ca80461020302c02e004101803152102014100c6003561140b10107110f075840800000c201184241c4122956400030034030040030b541001305020b00301400c04500704400d2100703022061380340034001c01d06190081015411110124000450100079080c03240c05802c20350002107050164158102401d0614803005000354054041000304111465050300c02c403c0c60f0002401a040d046005652500c40d0340003450001c41030130000c140c43c00140007050998000340c014904040d2075074402030041004181031002090003084410072540342940403410030713406010282c00c201c0004 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 52654239 1250 52652989 52652993
    0x5060f070807050d08010f0e010b1b010603080309010606090e010302101421010b070b1504060902030a0906050906220206160f021e0a1203030b100801090b011713 71
    0x405640190380c212403802d58454091a009450b00d8110010700045100c250003c01c0e98194484d0240988081d0340600a50340d00b4051900c680c4e030010361074082072400048084c0e183c08401e0080d040194850380006840f802c19400150a441554228008100d04103500b0085080d00505c0340d070442e40c065980c95641c5194600844484007040d12003440c05d540025105240540340f0708242100411146400459807280b460032061312891202400c00182040420b1040180030340500c0341850051000410303551f603801c42401d0744c004071980ca601580e907151103402e000d0b86000c0e0f5a80400c410b009400c140c54142d003104024040d4442c540d1400e90b81000c0d200031500e8a07412502d0359201245007400b00300e076519048090088241007280940c0b100f40d11010f903895002e0214414040c014070341180c0500300203c5c0740152086003c10f40070191074000308011030710f4400d01848856015034404c0b030258100300ea201c00780e5031024016030400c0340c0740030300b04030313072040c0003141d41e04801007200c596040b041c0c0f4 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 52655489 1250 52654239 52654267
    0x12020702060403080301150e040203040203100c05130303030501050f030a0f0b0c070b0f0402010e1f05130306060810060e1302220509030a030b090906010e040c090501062001060b040506 81
    0xd0300300408030000000046441f20401c010ba555440b001d0781d0b4010b0103510042800140e010940b8006e4050b8001b5803480e0ba500d032642c20150b0007404d146403103410003156440c050007802480d032013900441d03580d00052010741040003030002d80341800d030002c000c4040700390ba0b00d014011110360094074a50401000c10038019189003140c0b100c6401808084141c02d0a003450a41004203480490128040302c0f8201003a0412118000207028903003040e840309040b00700142c40303e9000555000c130003140000d000c00016404e205013406031078484c0c002c0c40010403038a072201c101c4426411440a508000081005040d64040c2d10048103506913180041c0c81c0b58901003601206002c6003014406041504000300e5103800005001e00300781c695010303c4400300e031009012954000341c5505050350031a100501c9003601c0402a260403e01c14140401e00c140d4a106070004c541003030f000301c40080c2d000c0b40c440074401103880c0781812082e400c40081054074988004400c80d071003130703100e854060280030840385018400 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 52656739 1250 52655489 52655497
    0xf030d1110090b010501030c030908030c0d09050307060b0a06050301030c060e0d0c0801051905040803040201030b01111203100b03090615010e04060b0c07060f12050411100809010f020a1202070206 86
    0x4080248550790a42c40c140740f00c44000d0140c1070029290a1800e249680b0a020b400c1d04290040c100da444d5440b980032280e8141e11080d010b800094890a40100203601040203002c414015100010161004001c02c1018206a4030074810064240014000305818001c0e801c222450360403c2c0060a0143d00072451a4038551800f424180c000c11000803144c1041d0040c91240c0142641408dd0794005002c0d2030407900c040d600030b01010024400940154001d40c400029804141401d44480c2084060a0f1030104501c0e2402c0e080000402441548028040f425000d40760181d40c1c01e05516120f11410740e40c4800070100740c5034103080e80d040f68241e4003501303244a000d2400781003444400d8462010a120307510000c0741803114415620001901c41c0720703e04080c80c41d900caa4540c51229441c04082c000340801500541b4588900007044e002076a03003a466418806150f125108d240c601800e2560845c1c0f4400d02c4036040714010001c0101941d4440311076400c900c41c0210041c1c540303a860003c0303442400303 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 52657989 1250 52656739 52656763
    0xa020c04091110020607080606040608010b0d0e07091e0b18061f050c100504020a06030b0301110c010c0807021204030201050706060b0313050d140304020906011e0504060e0f030d11 79
    0x504080c40500d0f1540c0450650700c20305040e00d0b4407005499020511140d84510301c60070700003851080c014469106014005c002000d41d10300085200070808a005040074801e07488103800d580c4d2141c0e02c07c2c0e205070390041160300e07800b40c0108020030300d908404200382900c0340d15005040e018402c0002c41c1aa80c40703c0000c0441452680c14a41c103414020151495210500d0045031348a2400b440c0c84400c0ba90244d14455503000d004001c007035140034410f6000d03040e02103001e81d141d52501d603e8404007c1200241034004030707160000c9544035454002030401000641203100b190030940840b03a40002050468044942c20f10b802a034910301c605080c0f00801e455001000d403114000284900d04013008508500030380260103585040140704000d44150701d020240c021081d00910006016290220455520881c1030404400f00a032582c2680710034020518a4000714601082c18031071142d204001c0204e006c41a14070711520000140080da0b00c4902c24004020000c0394600351101c07000c24048044440 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 52659239 1250 52657989 52657999
    0x4110406030b030f010c0f260a02030105040b030703020114090a0806010b12090304260c090708010801110708070816050307030921170a0c1b06080c0a020c040911 71
    0x503150a00200a015560a030078840c1c8958100f80d440c43d074041c440e0544500d640d40b02d68189080d0500141c50340d0031449000010350380b044c400c00002c0001042039a100d0100228010703640e40c1404100300803621000002c038000da010759001d0006036000309505883d01c4181c0b40554459400e800054007a101e1604602e01a0180d0780c0002403220156000c0c0603400c8840d1010515580c4986546030389014610629440b00700707082e842403e144400c003e240d15103410324151040e5944100200d09548000c0d101840041c0d07460340100411340e8288241e800c070700703010b9080c1446c5c120162250300b03003401000000341c140345000543d44038012680d00c180320219070240599403100f20034180a00781005501c01c0a000d02d48904c1079100f00c0d8a60b440785220294804520060141002404d070015000420307940c0901c42c20f254060081030b21079000001c10158070103222085030400100600442014007041024081400b5090302d103074020469a001c00001d0b5400188090355081003007040c0d4032805e03101e4002c = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 52660489 1250 52659239 52659247
    0xa0b0d050f1504030905011206030b13020f04020408030306040f060806090a0b0711100e12040906030c1a0301030f030909020d09170306030a170c0106060c120305061302090411 77
    0x50108081c0e06480005098810410b01001510580c000071600240020340c0e03803806000b60340c002c1c640c00b1001c540f0f5202c0000c1603602c03680e881c1c1c400e50040c0c8501d20889100000784c011807800c540c020040d50410f64041d405c00b0300c0c2ca001c07140d407800041d12440c45540c65030300341c007507001c05944460300901480c0229015801e0100003c0e44510050310151200e05403640061061805501c000c6203c0110f03100800c6802c6030565414020010150403440901500c0c00800260f02d10b10060006826041400a078803851032804030388100d429440000710030403107020081c02180303078000d581c1181d41040b40107101003058682142c0011454001150b124400f00d0725110045840d0b02c282080d511800b054031013110303007440240e00d50104640d5640c1c0740d0b11254a44c0300250100c8c1801c002c07424100f00c1d0a050140715000d05081d540e40f0380050300000c0340305203a41c040c07081010242d0b400d00300a0901704024140540400c0c0c0107003050000920b80d90f00010810740907144c5034044284107003145202502e03 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 52661739 1250 52660489 52660493
    0x6070203010606081801020702060301120c091a120708030a0f03020f03040c14010c050d180506390307020607050a140607120513020d020d060501031b061106010e0a0b0d 74
    0x11303800b41622840c90702d051003120001c00d0501482180c076801c1d0000d04650440c1c3c07a01c0700070310702c13052504012507544509400004020b01980200c520385650494070400e615414001e0003003082c8841d00c0d052150b80704081c1000030220100841e19284502e143c038100b9130201200176400392003011607803600c010000041000340302012644a0a070345080b0914840c68103202c004440203038001c44d0180c0241c2040c003162000034064421a00f04503485e10490400c03a41e074a0010380c558104160042419103d00e5030a0440050b04030f40042c01043c5100500071154400002c41e581d01800000070f0042100140c44400c0c440200a84007119600c240b1940341580b55500d042c0c0c17030740425510200403400c10021542c40f074a00e40034251194110b500381211281e041c3c0c003001800500500240e07000040d04180e000802d00f6802401d0185004941006600100e103940d441402030039485041042018084e910301c819012850034119442003100c9400d688840403440010408400340701e03030040c0038900d1403003 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 52662989 1250 52661739 52661747
    0xc030301180e0609101505031911090f010303030c0e030115080601060c02130c1106040b061008040308040605070e060414030606060909070503070302070c09140105010f050a0305040206070203010606 87
    0x340164100280000107102142940c0d50106030f03004c41c2c054110139081880350b02c140e40101074108680d01d83c0c04020340c0d180301082c2005040c0000d070b001041c020078600107210644540c040e003030f44240d580c1c0c006440c00840380a20003a0601000b01010703240e950200e842c030b100d00c3e1400728900004008000c940d03080002c50740008054400ca1210f801840000103a031800b4012a00301190081c080c0000640e080d51804002d0902b820f4500c00d02007c2609460103103020803503503128901c920400340c55070130600100001e4a40980b40704080240745010040002c1c0d000e41d54503002030b48094080703207540f203050068440381803a08050b074010201046c00a02528010200542c582e000d07020740303005446a40c01d201c5240b1411003056000400c41c0c0100307000c4d41c802e00003180d10411070702c1c0050510f0301945e58842610740d5030340710221083d11410318090105404a10341d00505090070025055030511501600500071140380d0001d06550b040003038155100c500880b03c00ca0345c000c008014558840102174 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 52664239 1250 52662989 52663019
    0x307090e0910050c04080c1908070b0309010e0604120818060c130504050c090108071403040602030103060f0b0a120807080c070e0907051f11121903090b0115050c030301 74
    0xb50400d0500010a00601444007100e00382c2e1141000b91a035040c00a0601183d0782c50301118194240c050100001e5801084c44404003512a6000c0d003540c038140072005c2400c0d500340c040c122019810401c24403002406045003288803807040d08180c0020703510301340300500b0b0400d8180030001b103025031802c000000c0040c0000780303c00c0c101511503c40d020f45820622080302c0c02103400da41e45120401c0104990340c0105d0f1a07661048035407901d00d0503400c038a104400c01d07820507101250401d4001c401401003122900134441c0e03242e08c14100b000080440d4000030f019144911a166460401c20405030900481c41d049818041d00001c4040c1d8802c040e6440759514007040c42010340d180707441300218901c16800b203403a000300c83d0002c0c030081a910314410741d645030700750a901d0a0140019000c3c5515a04030900001c502114000c0e0b22507103848440350740c107030006a070380350345420149800d80c09400241580d9202e8150b031502e5006141528103500c040d5900c1c4034001703600009220200000410714601c01d001 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 52665489 1250 52664239 52664263
    0x50703030e04150f0303210608030d0b010c03091802121e010506130e2503090c0501030905060f06030c060304050604021008070516020a050d030203031e010503070b0307090e09 77
    0x20030a0418030030ba290040c0c01c4a0161035084c00c0b0300d040400101c0d108501070212581c600700d04010b80d00185203002d0895000364040e01c03080d00042107034907601101c1d204003403030104282000e6000040305e5800601d00d840a00400800f01403481010391182c020fa070654020107110784445512781000c07082c001030111f00d2182015107611090000c41c450070044251480148011925070304a8100609034201200040001d080403000040c0342e0400c1d622415640d10304100350303e0000300c40074141085000b40c441a04964103050501e004040007070000645c50f1341c0310b09100e032032100319150040064103001d01d10070543d60045010080c0f201b402030100d2901e00482c400c6030407460b1000300c90360036148982e04842c40004140140840400d0780d0481e032904600e10310060000c4601515040000d1141039440e0302a40180e1010041219003103000080c01c000400640e50004258505070020382d4405250084004183d00407000c02d160701d020f800002e01a020009407110700b46015a6510360381d070695448 = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 52666739 1250 52665489 52665491
    0xc160510091104050c09060a0f030b1c140d09030f060b06030117011803050322020306010f080609011109061305031b0306061e060c1606050403170f0a0c0f050703030e04 74
    0x42110b0500394406c89801d184003408050804a00d00400d0328002c0d411507844080c5521030300440410750b40c840075003260401c900700704100032045040600752600140b4134a2031907800704810805040c2c01007444001c807540700c2046020007802d464060060700070807010b0b641104c0040008100205030685118075885d644000b0000d15501202c0100c3c00b941007034001d400b10340100301059450002c0000c1800e0700201000081c0005460782c003091400700264003403225054070139018088102c1c1030000e6a0000b00080090100b0600c40302100c0c441e20440064910a89000592810800c07401ea207500c010031303005080d0f03543c00d081c85038211442140400c019201c1e010b41e200045035498a1004000076a400c0d81001c9222a03800c810b100712a0f200f0f0f0f80c1851248100083c98441200394070f1440042c0c86c213544c1e2242c65030f20307618000300324000f52520140340d0642406588401000c00d000c1d100200090f01e021031051266040842c5240240031001d041d60003040c0010061507001801c5038142e50080d14 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 52667989 1250 52666739 52666741
    0xc100f08070912021201090b041101030e03040e0f13060e06010501140c0d03020309030c030301031214030417070c2418030b0a0b01020705100807020d080c16051009110405 75
    0x102d528900701d001e180071440030b0800540150821050018040d1070407800010b840407280c64042030054212401c030360311540c0c2e20031420300d5645405201c00c0303507134000000d50034142045a084007584e0003d001f560010401030000d072280044040c0103030956001401000303414040580691191402d015079404211540344d130442c842ca05200720f42040d135201c0081c04080354428821000b039030025146129510040c007030321a242e68140001d50085100e000c41e80203001c40c2d601c0180c0721410140f0102c28801c4113004010105120401c1c000d9120b03028050240e07120502c0c50301d0503009149411000c00c00c02c070f646544009030681030a007051850580c44102c40c003010140c141f90701100c1404002d10000002000c92014011600f08610b4040140140e8102c942c0700c0c00480d1803d40b95214810014145c1c905020519405001c40d203001ea8803403801c0c7c2030b1403400300f6912403180708800380e0603000c446540d980d50070f0040a02c0764503803802ca1030005009a44c0c036401d150b101c092804004ca4811441c00d4 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 52669239 1250 52667989 52668001
    0x90c0b0301030206070204050406110d09020f01020f0303070c020a03060608011406150d0207020f1518060a0f051e0406020a11030f120d060b030106080901050f04020f060a020c100f08 80
    0x20156030489a004101078903101050303003800064080a07000325802a01c03407008440702d061000c00380086c1140c0030000074030b1203010300420280e411754052240c19500041ca84c12841c1e02c000c0304403a80400141050703400002e0520220707840603501d50015001502d007007008500c0301070640040322900710014001c00c2e81d4a80008000000c000600c80c0726071030508000b004200701d140d80280c200540000d005441101c0d10f0400304d82e04441d41100500030752000207038040350001c003035880440d22505641c0e181c10818802d4028080902d0303d10b029041c031030081010b07200720402103204140d045e132079104c0c1c81d1190303580c0002070354806854408882c04454503400300e502d410001011060250800e0081041410031481807075260300455003c2c070360782d1f00d90001080408400c1c0c0298001d103480c0c2da50020514001c210390707003100e1001c0c2c007000c80c030b1185809000140c0c1c0e0b40020b110724400d00b01d501940d1401450030591a09841000068000303caa101d012071f10740e0400c809803440700c102c0e10ed02003507035101 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 52670489 1250 52669239 52669259
    0x6030c08060a090b04020c011103090613020303030402011409030109140d03021201090e15040f11100f03020310031b030201020610060f0309110409060b0f0609090f060409080409090c 80
    0x840d801a080010402c00300b14412060304400720140018200600c2c0c04038000708a400d644181e107000030752502c00402e00600b00400c101031580900516640c51880b5501e41c0040d80342d10018002a0402c10246072000303152100300100c0c1c0000700c000303008110310021403034070026140b03046c9d011280758040e0284813150315003c1d0007121031054081d1880d24244e0708103600c890080000c50840e1200c5d100b42186a0340300a1102c00072030089000d110240d581e00880d00d48000c0703da8001603a54000c60501e8520764400e900604116001c0f00d5500f009602ea03560a00359941c00b171143d0b4009805502c1400d0110000c500c2d094105040c1d900070ba0a0b80d85903610f842c114450305402e03100705000680580042c00e0380611a80c0510b10300c0b441340726286412004000090140d449900e0103443c1296110400701c018605130205201c90341e800c0d62301038144074600c000502c6864008100700c0042510000081c010364a41d441039500c02e9002c7c1003141c9803502c41118000070601c00744d04484100010002107403c1d0b0702 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 52671739 1250 52670489 52670491
    0xf0108010615020303060405131709030d0c1a0714070b04051009031e031509020a110c031f091703041b15030e16090b0a0b0702060304171903020406030c08 68
    0x2064000313501c0c6440300c005020080c000104580c00d060703140d0b2450380019401070101480c110020112680350300d203031000c240c02c0001c0140c0b031805200f01d050b17255002441c101c07030449200b0041105145580d484140940d1a0703000300c101840d05244c00a069010480102ea2282c051070042d403c8a08001c0000c0309041252100c550260208003100c202003a000c0700340c0c514281e14080f034940803c40813160482c00280b4091500722164007600400c92402c0135038400503a0803a6581080140401e4880d44c011945588096100c0100b007507420404400c00700c025003081d50210b0f1310040e1140011001c01d1407244a0308141c0d4100c1e401030342d0000341d106404203003541d6000c0e1928080040b2041c076031060181d0081180c805285864000c00c0f24503001188203600500007171445520110712144644100012840580c1007030700203417014420180541c480030180c03580640d0055425142c25030242c1001e40c54054a950700c01a40c00c0480d52400c0c0c7c9501d6000b5000311000e41c0c4050000c4c0d1412441a914000 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 52672989 1250 52671739 52671779
    0x10905070e01030f080f13140f15030705070305040b0f0a1404030b010e04030e03060c0d1d03070201113a020102070201020a0b18060408030f0702070b0403020906040609050f01080106 80
    0x8540907010000c540e1728002010800c0c1a0384495180010700615920f81800b03960101c5604a00380c05c51001d01c3c00c02540900100d0412148913800303100d110041052404003500074030030402e01103801410035026104950203041034407412a00c0d18018184d800c0740707034007a04103a000145071041c2c11142c01c0951040d941039952044041641c0e03030904000b2420b1001c020010307801c000c460386060486407010310441d409000461480c0e541d91008120399000e45000c1c0c03c14122201601011134031740c000c08429503402c95424a003031310065914500d641d1510180011000e010f4140c0c64035101510b188020724060302246031240c918100002c202030b4200d0284810107409600140a03040c00104140003070341e4480091400c9843d48003c00c00c98526103c401c94003250070490000c24001b04206d0140c03c207a001c80c140c070051080714140f190040c814095880000c2c052207c0c1030128009503110b402c514040c1800c00c0e420406864151035102c1620828494415030f03518054021230348a40100025240c40 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 52674239 1250 52672989 52673003
    0x30c021203040f081b1e0d0806120a2a05060f09040b04020d060305160905060105041e0e0405010c0305071b020f04090614011a0415050a030b030708010905070e0103 72
    0x5500c50b120030650f0f80c6064001c0354a444d0401011108059001c0342e820b10583e64001488180c844010001c3d0480000c1070750300b0907a20016204240781c0d03100d25510340c0107800b907070f15083c3c0d410000152407401d01c0c1008000c014007038215044405242411401e80e1701102d080c074902d0360956072410320105210b01d005400c0760980400142a140c145600720390f50aa03400740006103400c0c0003002007411658141c0040315560460320b08400426000410080585004603041140d401d103c1300180c028803032482810380340700391821140e010b54030070560720004000040c90310466150030700e4030700d000741114881c05010078500310214540c80d100d81d03c080c1c0c082a5001002078507032420740821100711107115850f1792140d1141142030004509010b4089904030080006200d03504006203031150709005520f484000200344030401c0003040042d40110404a9410415603e00fa000001c4018003c2000919014854030700b00150301c002c158054103041d0b0140e8280e442d955260809400e00ca002884058041 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 52675489 1250 52674239 52674241
    0x3030d0f09060c080f06150307080405100e160906080613060b041109011e080117010609020f03040507120201050f1b0f03040603140613020a12091a070305040f0303110f030901060501030c021203 85
    0x2c00d006074400bd8009004800312580160000308060035151036403401c3c04190026000d0310b903130800c0c1100c403001425002409028060502d040706a40b004000d00070354030303510045110800d120307603940920001c01c00070300188031a418402c828860342e408920700f00d00091516001503d0a2941070800030040c906950300d05c82030340382201202007000c10528008155503212000103c4a03404d20081192481c1c001ca203d441b85071070300704181011a20391115074212800b904400050b81d001c7d040381d042c44030403c0c4440c1c4800300300006007000c511001260303900344614050540c60b910004003820450b11113680031b000380e0420b180410020282924096005010001111a208002c0d000740010b2844c03464110707000c419101192042d00d030200300030b44264030084c2c0014084032b040302800e50710107100e040c03d1103181819960700302d010109180280400d0381d00c2900d000c800ca0084122507c1c130104c0c5400989901b090607085000703141c61f02ca000d010034584022580102c2c0003103990702450b44044e81070303821 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 52676739 1250 52675489 52675501
    0x506090610140c070906080706020106050a0e01030305031503030307020a0605011517070201020c03070c030b07090315050702030903010e07091503080307110709020c010917040503030d0f09060c080f061503 90
    0x5030f034001e191a014580911080864043e4603031080f01c004000c62002414542e04e4a14081d00b1201d203504034a018140810041c040010307102c6486045940c140342c0580e0b2503448401c46000c03e0350310140158140800421b1003140e943c00217a01c40201d010b6101040703e640d840005108a80142645801080259052024044460b480710b40e0040f01800050b182a1042c003190342954041c0380c084880d166000d00a009000748803060a902c800301e0b08002d1003540c11512413420a00155001d12103142c1c48000240565109006075003002d5805002404083c000c4840551101240d01410500902d010190382c0340890820041044981003241a89541c58118003158503017268050030b2103d100d50400020080313058030003030501940b18030000609641d02c0c078004081503c28039990010817014041804903544c04000c8520060b00c4042c0040c002440c82c1d40b09001c2c0c0645907010300b07000c1ca00b2110101841e000140e0900ca20f0103a08000c495a680404022400c62400d100580e1600c042c00010a = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 52677989 1250 52676739 52676777
    0x5040527030c1f0f05090a0b0906070905040c021204090e100c052a06040c060e03010504080a0c02040b0901030f0b01080303070903030804210f030c0c12051b01020307030506090610 79
    0x600a01410701140d4141100d050300140c3c2c5c0266a500c2c810750141c114032003444125400d098011098201920290810220040140c0c030103001d41d40c031495851783c0030680076000300517440c0e01e41c1141451070786851b80d805902005004103038102c06c0b11301a03a01171484040040c8100c000d251090340ba03050502d44014210b9a03500745c030281f8028891a00c0030b2040001604026a07440380c0c0c0706054a80d8001e0929000600c040c031155082c40c06a03051005110001c0c40e001c050320544001e500e0545140c92541c0001000361804000307454100c40400300102c148002c0c080c0c411703007180c0551001d416607669030101139030700e00c0116034810000c2c03520704040c000603120f501101e410078010400d0405041101c07010307080034500d032440c8201040181240683c01c9405001c1c4042180740c605004c29010141c0d1143c00d100c00b0030b00104030422000081a101d400c01d80c00c90341001c03d2042008544900e814076020b0018070060310164440d80b03480300090307118034080701c0302d01a640c01c50356504044c16940d90060 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 52679239 1250 52677989 52678033
    0x60903031b030d09110a0617011502100f02040302090105011b060915020c070807080c01090312030e0706030b0a12110904080c0d0e0a0602060403080f040c05040527030c 74
    0x300d540e000400208402c1415402405055800b6a2a2898241d03881c010000d07102d42c0f6a201e0020f00201d1100c92201d0000c00031041c1c1190130721142d840b054420345100301e033403841c50243c800c485c03850004441c0018040d5405482038030301c01e403060b01e600d0b6281c90055461088a05441c604a400032804500282c44c0d9045080070314400c0320100c100c0c00d42c041682050340c06c1201d288480750b0103040c0070480100100446401440c404010748198640345000908000c42800040e01c03240c001140c00017450710030340c06550a0700d107080030b5464403521010014090503011180c0c51281e90101004121080c08c0d01d400f5040c43d9120740701c21034007215002403025580c0d0043c82070352001000e000070103000d00d00340503180940c4803543d2694103a4102c0c00030000b0384641c44d00700b00300b194404020400007075004a00e0b00d8000c03280e510000402c0d6a40e143c00ea4007030100e9003080740c000d41400c040c0001010440c0343e8400c00d0441804814440c03043c1d2607001c4d40c0f4014564000032aa01a005510b680441e1620078 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 52680489 1250 52679239 52679287
    0x50a020106051017010906120204051e0412110c10030e0a06110406091505031b04030501090803010521071e1505030105090703150303080a0f14011406090303 69
    0x801c1d1560780d140059600600c00e8204030100f0000c0c0c01c80710301050344005890251400840801c401d07414031090f0305480c444040001c0c01180c0c1d840c007107102503100034221551582d48100c541c1c40f0745444c1c43c0080380c40c001040440089900488990f0429a010030301c0e04003d034000c0c00000076400f54540c00c5001e0211a02d0b1205d99014400740c0001003900d80c0160700755841c071600b0440d03965160450003480100941e00c10a00b4805010420007401e0740074007201d4110100840702d86800c00074260b60303032507485107600080c0958a0305000700308000c00400610704862048034604564000300c65002d02c2d803c94010460309607004144203010702001500072040c015000d140c030682d25512842d408403c2c1e10707040e030800d010038804001040319180c11f0f0046640100300745030034012002000815010f924039400001c080c00480c40000d102c00820f680703d40000c03c25128144107180c2500c0000c1082d06003030081c01c000c092900012521810104115404107501800451422190307940c144809022000b02c = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 52681739 1250 52680489 52680491
    0x19020603061e040615021203060d0809061c0b0a06080403081b09040e060109150b030103060504032106030507050a030c050907030b0603070207050406050a0501050316020c1c0c06050c0a03050a0201 86
    0x95042d980c0711032044402070466022141c14940788590080d2422285510301200e5420030001c1294903100e802014030002d6200c0d0705543c66020060009009000d61044030510500d003031080000c49085070803010000a0039526038000c41e0b12070300c04407078060f400c4801078046890741380800c2c04464009450846412002080c508000d010340004094626840c000216a4840300051080700c2c0300d8482d90325060550365040c146640f40c40f118903694081480701420681d03407000000c1c14140101034620050704440011a098460724080358010b10050006072118800d00300046405d0401c0c000f410207032780d004000300355198070704030800a0061b8000c050b10101504c03034681469075114500039601403240b83d00940009801c12040c4011140c403640182c0c03103038590300800c1020741d070004101d80d0407003a8044c01c49051940c0c0402603140050700e5a16030f400c0220015a064017241d000c0c1c0200600740b003069003c10a950741d00c0b080310b2030b0040070810b0f0120341014083c1d0300028003580051a00e8203503400 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 52682989 1250 52681739 52681789
    0x904110723011104180b010f091e0f031208090d0c0f02060c070602072103120203060a0312050c0f01020403050c062b0c020c01170a150504050c09031902060306 70
    0x100c0f401260b0865482810360200c407915042d5034075214020702ca504070081c680b001c40811202c50013000da201921a0314880c81d005160382c407070561400c82c1d41000e024007401e80c1c40d030607a4a1405100d940345468405000690303050104044190100781c8031440140c42d81ea406850710b26840304400480d201c1001c030f90292040000303809140b024089900186040d80143c124185400001d81c5550440100c103c1482e08081d50180000c1c0c0040800043c0c035000d11005031a6603ca1011560040c071541007c0e0012040e203140600d02540500200161074803602903c07261401d5411403030903805079001c000c009401001401c0301c7c900f4144041c2404072030b400020006c441c0300c070242240c41044515151a25a16520b40741c2c0541c1d010400e210203031000b0b1812510761150303c01200310160018040c001c00c10f841d00b41034020151000e562202a00004000300700b1803d012420030990340c043c01182e4003d0003208052029231244184103025242c010703003854070b19030300d03d020050f84000110103c00680400a = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 52684239 1250 52682989 52683011
    0x2d0302030a060903020d020d02030f0309010f09080406030b0109140906031c021b010513060503060d0204020d020d1b080105060906190807030f020f0904020705070317090411072301 79
    0x1101c40201d02880d000505030b0010704000b8180b0117450003a00555000c0c2008540c8103500104440d1a15a0480c1890f02e03501d55552141c05050451a041100e41c2007142030424011403100a100b00d4540b91402c205079150700c4d0042d16041c4142c40303848404008c0e118200a81c1c03c010300c4031039200e07a005045c0c890803144125403a21001c20202082c0042c0d0100c079078507996000c056004620700801b400c2503030800c0c4103c1e021000681c000d000385010000040080358071601c0d0041d030781c1000c0e40d00420954030380061441d44802900040000c8181ca41484140c1528400e01c074040e07507c0303848a0743c44031400da0808092080c4d5a05c0a840341342c00c0301d0204000700d100e041440c8400d4072507405035103001090600800c0203007507403031503480004890b10420403880c480803031100701d0703040d0a0709603809a00c92210f4203000342066080d034000380000c07007500e5600001d10300e228001d084540f021641007050101c5103070100407900030007000610180d5000b028843c0c151503100c030a402802c01300d0000c24820100 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 52685489 1250 52684239 52684243
    0x912081305060d020d0f0504082b06060e04060603020c0604082212110402160f0f0b0108030c010c020606060703081302100c020103051803070f030302160f020306060102072d030203 79
    0x543c01c500302c3d90100750813001c11710a000f40d0203501c0c1040418007040c01d02e500c401c8401e205104a07044103283c42e110094241013150181d4040c000b41e4101000000c3e51070002800d0140c40f02c8119108520300380011034124040c1c425201d0303001400004000e10340c3c699803100c4e15940040800c043e008c82e02c3d06040601c8201002c00d00140001c110030b4840300e40140340c28481031074200580c038400d038014000101c481c140003401408150300150052100c3c511070500c5a007004c1920b402801c5990510004034000b40700100030055a40104001c01c85000c500e0012070304d0741802d9480d5944000704000c02d401091242c2c81158200307086600740700d00c4500070b50005a00a005038800c00c041200040c841c010340d0380501c01c06901111200c5c040d000814030020742a1240704000d4010700440d02015100103247c0f04e5415a50301c10071000301d03040403410900700701c900940d51543c128482e02c0b0704000948603500c0811128102d403941c40c030800c070301e82c0c4282c4201c00174000c500c0e441c2c0c013078042c41d13400001603036003 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 52686739 1250 52685489 52685497
    0x70c03060204030203060f0c09130b040f050414010c0f03021b100606090806010e0109050403050408070b070209160e01030209040b0411130e0103030503040807020d0b04030201140601091208130506 86
    0x100d40340c0107030303241d2651062500340100146007140d241030390030412604280800840d4202482150300c01c000d29542c2c59400010f0031512156904145420140a004940d035404980298010540961a03540f01e585841c280d40ca603010320000269260401c001e0b81c0c3c040d4004e00095140c880c443d19002c40c40c1241a071900c9018030a280d41c0c1a1288000c120fa541c110411401805c0c3c0c21014018640c1413042850031044184210140c4503910000503060603c9002540c02801422056030301f02c642d11018140365801813003043e40b15038110340214018003440c0406a0745c515035911801e81c0c4a00e4040158025044000d083c0c2c0c0003511110040a00c0d0346501c26081e040f040001d1517a243e20440810840052054200e00701d0611204010b0002c66089000c1d07a40c030039444031840f03594030840d1011455041d01858024603103d540414441015010b4002c1101c51940a024194954070040114ad10344a01c0c41000340301c84080c00c0c4000854401c80040000c058a002c4140301656100d003c07898540c4 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 52687989 1250 52686739 52686743
    0x7080a09090501050102030405031f1404050c01021209010c0b0622051f05060d090204020f0406081e070e09090102190207060212030106080a021605120702090906040b07050a0203070c03 81
    0xd035821050202002911695015240a10045003841c0c18031002c2035662a2916451404c80700d00901c0700100ca2107508119114000c10300540b680d0300341071400b0303540e41444918030f40c0940540d002c407030280785046060301d11a0405035103190548000ea111024044c101410583e003005140000d0500c0101200c44041003569801e4006054038007001d1644e41c18690024103088160340380030400050b5280c0c004c0d0b03107192161140c006145103091001400910850f084036240450100b0009134003600101003511074030800744038000c240c9103d92221041030045a0003004900800c603600e115050410245074490703d220001031600d0070801d46c58080441c0070314008010792043e05e041c04081d5040c8008142c1010f41d40441c2d046505129000c0c1c03500c0d4004006010180c1d011403122140310b52250000039050700032003512110000780d1244626a0300c00a0281d0042982c60082513610000140381072085800c01d680302001d850718101261280d11002c926002c5100130720030341c800b04100b1030302040198 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 52689239 1250 52687989 52687997
    0x60c1703070e01080a0608120d020702130209040e0f10090302340f052407061e1808030402010e180109050a0501080d0c02040e0307060207050c030c090c0a080c07080a 73
    0x4000c2c800101803280040c4208030541c18180d003000a5140080c41c104580c295049054881403a0140c0000070300400c80c0103503000b05008004006c02c0000d0f8020f010081043d5014840c2c0c512038860a9134480969201148640c01901900031288440e0b0088450758440d00c10b490404030706402d2040f2039408990346d0002803440001d80740b0b6900c1c500307020000070841c203101c8850300313480e00c40015042e0150721444049121100d800c513500c1c41208086512550f80721008010025118075042d60342d88510f041c01001030300e800800503100c0d20f050030304040d00e507001d1056440c41d9210341c011a408181c3c1c00e02a600b102000c0c1c0752940390400b00361154040c00c0d241c0300008a500d03185c0304200940c0c80680c411174071078202c1009414031035482100180004c1d016031380490310380010b0b40d2003851351113020009401ca1740f02003414820480041242801480120115940c1448032010031001080035513070303110900c8007040031050440c06000040d509c080c1100c007290409138079848104035a4007502c4051300103 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 52690489 1250 52689239 52689257
    0x9031501060f080426040305100504021306030c05060f1e09010305100b0d0c0203400f0e07020102040302060c0a0209010608010f0303081003021f0f0810060c170307 72
    0xe50344400300c850300d0b003100c1c0750100c06800c258413580c0c50135410701140342005240c1100c08800d91800c1003250000c59200003140c4500100c85003503001440107640032072046030032001c4030030717200040d0080000b030300c0d0401d80604885141500700021a4812101000300302c3c41442400002a181c14801400d50340c400141580c40404074001411203070002c01546488004003024002092010141d03401e204c21501d0014035a5000f0b1816840d40c050003a0280c40b55004008010401d44c8140151510749800c0310714213980e09440000300030342d003214011400e9910981c402000b81400010100e42c1214003400010328003600c2c0d130042400ea85c4465514015940035544400c21070500c0254680142050702e0503030800d50412441e00c1404001e44005000c00120401042100507007041110085600a000003400028040043c401c2c5004180c18000324544041c0724100c0d9004100c4184980000302d049082141002c0d01a1100ea4002100340c030b200c80c83c913185108040006000758000c0700039803681c3c108 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 52691739 1250 52690489 52690499
    0x31209010b090405030301090b0301051005100207090c050903011406010807180b1605060f0603031801021f0c021b0319060222171501090c17010e07090909150b040209031501 76
    0x41d1400f114009d80039a14200070062012107403024681540c3c000ca0f0070340032458007400b04034540720305038208500036850301440c4155140c02000801051000303800a21011500d44040032050b2405c45815010649040004280340e20440040600d22031145207510a0350f21003003958040d03000f50010030350b4130056100c15402d0003000c01085504c50030f11980d890851030034102094481c0240503c000711081c0aa48502e2943e000340701504070307c460010090340c2001c0103c0030b48042d007075480c60300c0007501070400b4910031b1007000500d24054034800703401000380340420404000702c450000e0040c0c1c2e100b42d090080300030040307900d040c1030380041484108460306401e10302c0b050358030034088280815591102740c08111400c070011445044491351003000804905444090340c01160701445000300085a20011030030540700c0c84418001c0d052641e40c26480d9440c1c0c140d0b0703003c4546003036020341156880e00003001404800d4200e4443c5d80070150002d0b060820030300c0441d213004240090302d00d034152000c0040c42 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 52692989 1250 52691739 52691741
    0x203130e04020a0302060d0608101505090403020307021915090503190b1803090316090c08130b09030c07080c040b0105030103020619050712110618031209010b09040503030109 77
    0x1000c0c1890010009103030406030300107015601c03070344030080c0a08008600110700358850340c044802045e02c6001c0d900c0d00c0c444401c8000050034600341c1d04d407001ca00d076140400d203030500001c00c81c400c5905070025454092682c0800c49040010702150079041140c40010a8501401e99118541e8080b0780711000703254240001c050178002c140c1c03004032561918000784030204150924240c1c0101c0ca182102c0d18686800c02080c0c150b00c81d40501c6605803042a0348a048031440381d80300b20803144144d00811a5440094080354110400e031000058005001c40c4800401e16551407150802064400c4034584034405103071904010503984000c0d155080f0000c10b012034201401810b5143d542441c14514542c1590700083c6240200248c1c981c803c10083d202184c8907001304106c48007240c1002540b808070150800c001d040069052450032a0b000d6034000c502c2c0000d04540408040041101131402c040b1504401c101c4c01c0d40007489003a0541d00c0e540505c00325240e030240c10740900d0240001c0c550b203605080001c0 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 52694239 1250 52692989 52693027
    0xb030603060124030207020a03020303040b03040b011508070e01090f121505010317030903070b01030f02031b0109141f020114130804231002061603060807060f17070203 74
    0x180d80e010f030002414041d000840aa503009111401c006880f034416001060303d041d007540009400d444000340104001200201440c86107209084000c010f03a00c405001070050850651036001c42e03035000106414600030f010701405100185030680c955907454240e07444031801580100b1031008104d0004050118070180040c2d010410321080c41903501d982c0d62036490342203121140d00c90400100100f050a00c040c801c803440241c00c01801e1240f03584070700300028640324030700080b0b1107407080c01c4ca28203050750740318000c02d40284140c403525080c1e0724001a9880c40c84680c4e00d2135500246945089800725072045a020480500307500008a4210181004400040c0a080501d065011005a4000540400c11102900d00380010124041d486582c5103400203004110b10380c0c07087c0d41400c1a1995a8009146d91180710314003840f081110514030260102c0d80540a008000d0308500d6052020030300401c480c40300112036103800500216001d0840007220005d81d2020300503040015035101c00814000c01c0 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 52695489 1250 52694239 52694249
    0x31506090803032a0c0709050906060901051203040503031308010c08090706030f0e101b051204080a0c02030a0b040506010b0406050d0b030f0102042903060307060819060b0306030601 80
    0x8065541c1851181036681c00014544442800a280744180e5501d8400390300001002c401c1e401510398001440003070b00c03200b890083d8022a071404c0d00082a06000050b154024500500130301041c0c1d003014103000210340c0b02c04900544c0c1c44200800600d5482c108010104070840f10400d02c10b10381413111107803c0d0b540d1745414100b0408041d041c071404c4000461560121051400c0003c0c203140031310380c440301420b40c0c0304050300c2c02c1c01810261925001c042c4c02c08404011544610715680c907100c603007034400e80602d80041008140300c2d4000f800141040c0000c02902400d414000c40000c05640024a0040c407200215245c46c0008c0c01d002c10030200f00592400340014003001c44c01c21707041031070040c4180610504120029207030354541c0810384051262034551200913000b51341d500d444005e902c030703000d02500710001c000c000c1080e0b004240d40c445040c1d901409001340903000c0186425012586000c016000a5500d88003216803441601240b14640040004410480e1280b910004050501905070b100c = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 52696739 1250 52695489 52695497
    0x910060203030a0b0420030703051006020309060913020403080d0f0902060910140d060602120a02030a0f03060b030f010e07020601030210050c0703150501051f0804030309060b030607031506 83
    0x2448900e8000c0281c030750000d16100e00141039900d040004016200e0103180130014580c0c030103402d241c8a0458001d52007205a62002d21083d20f03604210054a00f09201d1400160070030b0121100c145840c5004140c0c40c0300061004c2d000220154400303003284e115910459091000060b6913000303144500480032030b0380d8280d0003003112034204d4000c44c40700d00c54a541c00c1d1089982c101c0c82c2a001d805072990705190040b81001689545928241400805180c010310300988164070f002c4c0c0d600001e041c1103441d9a0296406141400d41030281501c2100c070a065280038951112400310b034458000b80598401d10078a11041c0c041e526007400001c407618050308610443d0010801800580c603240f410a44001c85031038000e0b918418003400b6402c08619400003840b07200304442d500d59064203a00600d050b05d600310341d0042100b494a00d5200084003040340d12002c2605100090086800399012182050144401240c00402017000a00300901210442c011030b41d606450003802100400440240070035041c = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 52697845 1106 52696739 52696771
    0x20d0e0d030b0306010b041a0714010603030905040e0a17090d0c05033d0b0402070308010906080703020303030a05070306170d12050f0a0b0105040b04060e09 69
    0x1100388000390500103503401d20310b00818030b14105d0380403020b40e070300e414641003460301c40c2069064002200071041c802c110105650a528500c501d50764000091a40d055207000307040030449400a5004518200840110100005900740c80680001e80d5941c41214160001d0a5200f0304034002d400014444c9d00c0350420841d14812000e40d4000c5090301c00d2101d001c00c08040001403102c2e804a0203003501c441c18480a49504c0d0064036050703402010904540d5000440c0a917400100100e00043c0140010804d0101c5449500c0151241001411141c0c0c619000256a4000604003c61031645c0b00d0100715198001c3d80110000c1c064010340c12441e030009041c1079240c190407a85c50000c102c0f40103404100e4407107817150780c1c81201412200485500c402c1c00640090800d6002241400410000411a01203d0300075000914159440580342140d070000d1051408010b440f10841c40d4810b8 = true := by decide +kernel

theorem cover : BRFrame.Cov 52517989 52697845 := by
  have h0 := BRFrame.cov_init 52517989
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 52517989 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 52517989 ≤ n) (h2 : n < 52697845) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
