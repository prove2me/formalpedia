-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_0820
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-13T22:58:59.575129+00:00
-- url     : https://prove2.me/submissions/b1539599-a3c9-4520-a1bd-80bc780cde13

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 147302158 ≤ n < 147482014 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 147303408 1250 147302158 147302191
    0x1f0c0201110f0f030714210105030f0307060f1104061115060d060b030f0d0903290c070302010204090f09060b032406030c04050c03070342090c0c0605 66
    0x40c1c0c400440d28141c000c0f101194898844d41d00583c0c5035034015038070001d00040460740c42c20001d4080310401088451903031224090b42e981041c075440b4002e2a0398207050342c00401503039000ca40d0a400004150140c000700041541c8481c4d0900c41c036421035048400090541c40b15850740c4513003040420f00e11100d840160383c543c00c10a002854600d12003900404280e120103440180766014010b130300341c4100c03140940d10201c5c0321810050581100340801c440340c1c0081d94110000700c841140c5202c100703214030140708039500d412001600300e80114104030115134080002040b8042c00780914242c0c0740b07460f8000b00e02426a07181034020340d01707100a243e009910031000154a61420040c0e03102480501e02c6040c503e44505002c6030030801c286456035041070800c0140201d001140c4003d41c4150a980c5e02008495429201c608109400d45000350b4009100c2d00c0c0b031880c1090302030101c02d1148800d206045030300d41d02c114100c269180f1034400b0b804510b28402079801d00c042401560b07031152042c0c0038082d41 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 147304658 1250 147303408 147303427
    0xd02030c0f030301060e12070504060b0a14120f04080d1104050f0f0102071a13060f1403060a050108071e08010914010308040b090d140a02010908010506090f091f0c020111 75
    0x615040511b20751207007000301703c820801c5009000501c080c0c400944180f04840d19400504065440584c403000000d01c1500305210004469040e034046d0f41005070f041080342c42d00f06006001070000382003610b884204210384a100d04030f51042c100c0015070380c1c1909807610319140800c1044085403183e1070044492030131403101070b030b8007041c114261051010109014002001c000b0b4140c0201295140d000e40b002101055043d009214054500c2543c0e0340c05800b11824a0045102c0c0025100983c100120701c034140800d40c082c91403030781e00c0b43e00b078074001c44910f100341149011032072007200840c046075424006210207040350059402001d1094084122545503682c1c070192481103101e10a84135002144400d00341d91107106e1030001c150400b00b0b03000d01a540100d4141c6070040d02004902245090000180780300c01030140500c5410000c01d0524903959805c0c83e49090300b0b005104070014021000001c810f5050b000c18039000b81c0c4284c5001454079a100d074040e08442016203030649401050107400304 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 147305908 1250 147304658 147304667
    0x240f06030a0201090e0901230a270303020a0c2003160e01050f030102090d0602120109092105090301090b0f0106080105061b120304080d290607020f030d02030c0f03030106 75
    0x201d45c0300c107074082c4141e0717901c00446004107602501602c4c14120f000b564099882000c2c1d005004001e200d80800025040c0c0421078109000b100e849185a070005202c00080381c049d50151050408900b491801d00e00240c2da0b111104110b003001814070100f8102844a905040000c90340ea5008950712010b201e061856025001c0414454148105e000442d0b013052924290152120910090080d0b108507107145032001c040e401900c050203000c41d250000050740d028502402040d1a00400c10000601d010318062183c1084909207030b05000c010080380308640c600740706a43d00340b4060b04103884281130103890428280c1c01a48910701b0452550300521842e40c5040071610f060382d921005484080c2820021402e1007669800c80881c0e840206c1000203000f5040024050071000030020004ca020701c541150201c445800d80c0056440c15040d00101070920100904a0724001003404c0000e560500c002481e00c1d41e0034140d940141c201040c403003107042c0101710480c408000b80c0059415036040080050 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 147307158 1250 147305908 147305927
    0x106020c180c090307030b010e0c070b0109090317010605040e0c03070219060e191208010e06060702030a050a080c10060e1306180c051306030b010b0309240f06030a0201 74
    0x20303032462941c0214010075442030031286840005810f503003c19030740e400d02c1e1016060034440c1d0804522a07100055416038910212240380343d100e20440c640d40d003400440001401020005c13424012885400b10440710440441802080da9a0301c1030b41d207606006003400221405000400c000001b0b109004000da0007144250000d003110300520784114503410003501814503940010154056010f00c0c80009544510805000d800780703003000c540c00a07244046400d0749d0309101c1c0c610502c40c0d03400498a589480070041203031b6800141143ca4404903610b68908108248208407002c120018103035480503400d005904c004ac5145a041043c0d61405003c60441003005007242141281c1c2c02c006020810543d10100e0083d0b412800850441694030700103410785002d00410348074103805440103d50070b806002d92801e43c1e40c02642d1002e03907480e15082a840f80c0015080b44818094002301640c400300044951001c81c402048218090425000310386000c40d025020601a800c90206071001d81d820080c100d = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 147308408 1250 147307158 147307189
    0x2070f020d02180103120906020303161d120705120307030c0201030207061413140f0715090b0a0c06050a0e0a02010c050c060d020c010e03160f06090206040315050106020c 75
    0xc540c1c0d2003440020328000f280540b641c018400c490010040c000da09240e071482c552240c07102014991074900a0b6038030f0004450031541d60303c141c04031803401803184100c1144200259981c0c80c03803603900b000107082407000c1e0003459080c1e401610100130a21300b8103424500f400410001d1850610140c40080c10b41104a102038103140e0001400410400d86600010000201c22001d000074200041640450481d039031003501d13030004001c801246d540340460720421651a04000301100c510b00903104403c04070189003c03051010040d8001070054030003004082e6800c482d038038042c0c840d20ba0701e0130004039103000d4030589c2120b10f4024604607a00700058032504450302420060744615003858040d10f441c1c202c0604a0b0170200116000c2c0c2d542c50300ba000b030540419454028020144032003807069882c0105030308043d0050301680403002041c415414401c005000d400081058680c4c0d0b00071a2160380154400c5500c0da015102140601010303215407070140c4030a03c040c00c2d01c0800500000c4602c011502c01 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 147309658 1250 147308408 147308419
    0x2120d1a04180609020f090a0c1e02300301060903030f1e03151802070507170c0112020903030310091518020904020408010504030528050301030308090a02030114060a0902070f02 78
    0x9250956603680440768006c40700030100d5895140c946a40030140001d070744413030b01042400301c508c00d4441d41c0000940a42c506a4000c081c000b4a40c0c0707110750701e514005c0c040000c1102d441c460980c12010600154082c20b411b4a07043c0035603140d890014000d480a829080411981c46100114804085802c0c0c0382000240350100f52003d070143c0e04540390000d584058082100109510124005500074015403070003a026203900759a90560060100d19000c1d04030042e810074483c0b8449580202485075441921800040c100703c3c000c404280765034020750b00e030756680d0304901d8100700032586801801c000154050817130ba14249400543c410710000340c10b42c0202c0380e40201d03007881c203511168140e80042032584000c0c0706604107418064060f6214083d60300400350400c0074401c0d82000f070007111500d20640c0d40e0f21ba143d03031302c5d41d1070480b0b0b5100007400034103090080e41123000142c0d07001d010f035448400f00400c00c0380003414582d08011581c1060351020b41e80d5801400081c020030304003030b520480160103882 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 147310908 1250 147309658 147309671
    0x914010503070509030f010606030b0f090a020c28151802040c0c0b130b01050109060507080d1103090607020c0a05011205060102030918010503010f05190c02120d1a041806 75
    0x806603594020740113815018882c0c0a07500c07107910b60540141c800c44166450070041307001107405200c07170508480c0200e80c22003460808074011100b030340e0041c4995140762094a221900062581114100c0036100040782c01c0320800100501107074081242c8030300c244810070041e00b680684146000420700101900c01c40e940c00c0482c0d0036034003c445903c0150303446209556240383c03451650700d40500b072450503940710318036200120b002d50207180840d041d54540d4560500707048040c0c3c1c403440d05d40c2c4880302c48083c81c1e4880f028102820000405907002d80071200246c100c2d0314000e03c3c000c1c0b90499a000c0c05200302d4020001b000941d030002001c20064000d2038020a00d903962100607490361081900c0550080064804c0c6a003030a50400058180c40040b0003e10002c101e03000c030801524810781c1c290388000c0d50480c01c500704a200f54003001750f41c44140151340c400007540000c98242d4000d402c03545000c036143c0402c0c2d01c0400c01c0340d4130001d540d201100c0420800d41d6000c01d201c3c0845001100610b480d030b8486 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 147312158 1250 147310908 147310921
    0x51f0807080a3803010b0102100f09080f07030e0a0f06121104150207080105060609060304050109021903060b180732071b27020909090105040b070914010503 69
    0x108003000506038941c007100d042c3e41c0c2816030b00c11881e041007000d4011000c003060f03601d203107418015a030a02a05078014035060b000381103140000c22441d41c0710700b0f48a0703503007104000240032200500000c020050000e0f448041d81d0070040c200d1122064414030a18003001c041c420a016116288252240d030307c0c02024001c1104401c0c030040c8642c4c010f200c10319001140000354403803107540c140203100f5030ba401c1d030303401551390a106400e03038400341c1f19664040014010f000d101d0802c44095030b4442d01560001c94540955004201c080198060000d5003014820b414070501660380240400f019099031181d054110110014402c1c000103420b034030402400342440c50f40c0f14084c4801d03407600486900c040d0120112403d00b03078140da1010742c0445c6c40070761b03c071419104440b42c00c1c0b401c5d00315078480a150301d581100c1c0b0850b002c0414003903090b13036549600303002106054445801003849521200000100c03401c260030032442e2500001e21020401a05486c10f10a00001010812505800b800c02329180e440341c5 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 147313408 1250 147312158 147312161
    0xe120315040608070e010501090602060907140d020d03030f14040503090d0507180504151a04180b010803090102070503061306090c0810060e0606040b07021309050a0606051f0807080a 80
    0x583c80f05a5500c80d00b80d012940d032058210890480c0d000340c03039100c445030f0340d0385042c1e844840440b03a41032150071100c4100035034000c64040c01c192050080a103110400c8039400515400481030040d00003030390314141d14841d03d1701845941c807400035110850925140650b00c06541c0d21a903031805008007070300d4002100300f0400300000c0e0080c1950640b8110100c8110b01040c0003050200e9054904080702024485851101e01c03940d4400500f4206050103404520107110203415800310b052445001c546080c008582e403440307411b02911044002d10744d17645020b400203203002c105400c8940300341c10000901050005100f142c0301c9055000402044002650500e06003103111540001c44038042c081000f203c7c59407551041c0240c4006820581c900c0d01d5420034018140940d0007002600502082807001500c0c1101040040701004034000c03d928486560340d5052072400642103600e5900e8450500c00303450401d040c2c09280c621409208446030040b80004e01c4103c0240c200c00512001502142e02d80c7c007503 = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 147314658 1250 147313408 147313421
    0x303032202181501030608060621030c240f0a090201030603081908091914160b0a08010905161d040203010f0e09070e07140c0a0809040e12031504 64
    0x41000c1000300c8808542c1c0d030003070000c0b60203850755410109198051345c0244150015104060003c000d01d55500d02442a0303400d0314044640c801c500581c1044668030200014030048051801500440c984007640c0c000300d81151301c015404003540e408102d0b010070800c2c0d9540d030106030094045148941ea00050707004190903080a0b01c0c9420005000b440c580d0300000171142c01d002960380082c0e640e1131000513901d4420803c14404420030000c6a800403070015022601a100300000ba101d9510109841c5524001c140d8031010300081d02103848001c0e650071a01050040c122a0010310251504c5600120800d600314500d0003030100c1c50007103061688002910445281c0e002d80700315a0f0b96140c2c94400c8440d540c500c648550304942c0300c002004880c010030310804640b642054851281c46000e000c0e03404103000a02c100c3d806605001c2155141001c011f02d5034054041c2031590340c0c0721074400500c420741e8040700c0c4015196201c05119400720b42c411048176400715002c5e41c141a80b074140000280038240 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 147315908 1250 147314658 147314663
    0x70b10081c030e0d09051002010b1005180303032707030218070e150306040f090507120f0804030804050f1f05030601030902030319030c1b0210051c06030c1403030322 73
    0x2c169a0310103545d0482905406c2d60b504844640050304603410807400d94102e0962983c120120003140c100c0140540041c1001c1503400c10701c1c0c031201400b0703008030b803643d001102c0d50000307680c018114422140d00c0841c001d200740451000342611a0030342c0c003c2a40d01c0c2000305407584024060740003544c4a445098a403140d00402031141c5215201500340140682098514070310580c60041c0896101585110391001c06038400080c01c44245050130501a603101d0083c140c58807404082503100160001c00248040d41c07244ca04961a00d080a003402107000e04640c01d1401404070f0840f07407040c4d24a4203035a09042200345880740d900d50310840120060200900f000b50540310104540d144034010750100c000010155a0820400d9443c40302181c80055110044071950051103400d005418609004071417590079090840c43d08a2a40403900c080154008007241281e56210503c01c05c00c00c0c1000710300034002020f1507402c41c410440080d03124440501000c8584002d2402c81004140301d044180c010398 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 147317158 1250 147315908 147315913
    0xf01020a030c150e0a03020a03030f02070f060b010c02060c01060306060f0b031b1e071a040b0a02070f080301030b060a050102030418050a06030606030c0e090111070308091011070b10081c030e 84
    0x5c8040c41d020b9a900c0600b00200c0209040918001c24030742c0394030a482c80140c00c9941c000c800360141c6c92b110b0003442180c1210381081403100c520400341e01c80100910302d107450107000080040c51403e240e0202c40203604811102101c00d00200f206224400580b0b4212589140c282c80c0c44c02c01c1c0411105620840b800c030000e0240440c05480c0501e0360b00702500070390340503400b0040709098841141040c0a41240c0c020301d4030755240d010030801c00d201d6001d42403152189582c40c0400c42d1648490040d41c009a000f00d0300c005941040000c0341c101070180704010102800110b00300741c01c20b20b80e14202c40608804401044d2384900041c03504481742c11040003143c00c8402041610349a0808440da1003a60142a520300c06503400715112240522407081d02d0050360203100d0801203240d40455241c0c90203094602c0ca0320800080780058003143c40b8091080c3d10001c41c03195075001c94034002194400003445038030701400b290b4041004010229040010191032005000c6035031050314180d00034040203c45c007582e031 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 147318408 1250 147317158 147317173
    0xf050f0a090e0901090308010902040602070e220b01181104051009050618120d12050c070c26010506090103120c0c090207021c0c1a040911090f01020a030c150e 70
    0x110f0042d8480a82203000396103a000980e25661410142c1c41a8814100160300c0030404000d00c04400040f150440428110031041050500700800d4280d000c500a403900481003004008406486484415000c03903148203000442c034207840da0441e130040b481514011082c07080001c00c2e05108404940c068880280201e840707290130989089030020700681035000d40a080b000e00c040010008502c20102116070f12202c99034401000d07800074000260071058640000d000c0400020403501c83c0d00060311450741c01007c03902403410390300d246584c1c0c0c0f00941c1d400d034900020b00100e5105e280b20141542d812042c0141c0090b48504102c0e4080b50500c40608461030b04000456450588d400410006008440b58400407000e41c0700c0e0f81500013004002170800090290401440003071010900d8410404800c44d400d041e942c00c068401e48a466036240e100d41c400095809403458a5482c0f207a13280000c2c801042c0c90519550301801c1d0a100c0407005d00410824040c071000400560041148980d9200554217031 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 147319658 1250 147318408 147318421
    0x1605010212010302042703120603060207060e060c04030b13051911090c0c03190306090608010617030901080708041b060f090e130305070203010b03070b03040c060f050f0a090e 77
    0x40c1003003804124807480c2000904113550511031601e40b0701060466401428141c1640c048c0d401d24004520320700510384441c00080466901d10140c00070b00d00921022400c207000c103074603c0c1449001000c10b035180e44140028400306101040040e40001d40b80c104841c0d8084078144540743c080c041c06959250b5601e4104041081411003110800100580b4074234081d86480000c170b40140102c284008569009201104c540000110850191700040c2000100750741c0300c890180c19205207412035074440c1e445103410030541c0c4c0c08454200300d800c2100b000c1c5040c03103000300c0004c0071b112002d0801e00400c0034450104040c00040c02d2482c004140442089070043d556000203010400102590390103c1c490450020b0301c0740b00d410704948510200f4185440c044820b6030203039240c1d00800400d076003543d07071404000b0f01910104103a0003c0d0180807078494903442c19140950f4141c00c0c54028400700190030b00c02c1c100c9a50060151015081081307007079910744460b01002ca4004c02594401c1c1542211141881007 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 147320908 1250 147319658 147319687
    0x3020d0c0b16140d0f030b0d0605010b0903060a020403020105031b0c010c0305070e0108071b05100e010e190804060815130203160c05031b03041a1b0a0c05040216050102 74
    0x50702842090880f0038807403071101c100d40304c60400c4240380105051000a000c0306101e544031000c15640100021500782c0141c85000483c1d030b090700441101400010a4038080c541009055805802c0040c1075103040c5c1180e00013403450202074540007d5140c50907580f00940c03d800c040c1c4001d06041e0000704800c024230350700140030f808199038602c0411b15100160826520072043d41e407207120340351903030398181031a10398503c140440d180058509000c1d00d4929403c8801d60700800708503100c0600086520b0075840511428680d02804910b80c2c1040d04008800007000c0da001e5808031142401c110ba003a940390b151086141214034196a44004501400c003503440c16a0301942c02001316042295070070940d0b0905541010401078042d003e0340c0207101800b41c0c0e1200020b02d92001e004103046d203007403560350901c40300c0c0c02e211010f0101e035881c0003243d00a40105400c0f1f0450148135140c2c007e102a62240c0c0f01c401496030f850041c280a5500040d1107600460003521607a40aa8014000c540c0e0f95a02000702a = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 147322158 1250 147320908 147320947
    0x50f16050304030303270809010302090310060e160806010315030b160806150f03070905030607020a051c081306060b070606050901060503040201170a0603080a11010f02040602030403020d0c0b 84
    0x9011a14195080c40c140d000031200d21401b40c907201384064500025200d02c8265003080b401181015000c0142c51000d48040c000d00b030031603081d450042400350030b10313028520054000b89075040c0d0590211024000c141d200d588035400040a0800041c2a85a082c00c0e1540d5040740e0400780101071580107000ca009209c140d4428098426074070b0034426290704e010043d00340c00e2499240c040c01c8062004841c0010000000d40e00f21055081c0010340f55a030700d021900b4140220340c0f400141e0000002d400901000348543c02c81040c1c50106507150034985000501403506c003031301500056107000c52803802c00c465580800c01401007003140f04e44484c0d9500e4504041c16460044c28060194440009400c9004405490107190b05842c1c2c4142c6041400d445212020000d00980116444210000124078500000c00c0c10421640e0307101130042802095a003910303203040500308101e204120402165a000c41964180c0390f040703801c00e86690b03c81c00c1400405402d5081aa11114000b0f159601d2160550103030 = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 147323408 1250 147322158 147322163
    0x311031f030f1b08070807050108060612010303081510141b030c0d170105031e100203010603090303050907050306060d060f0e070f0806060a0b0c100507090617090a03050f1605030403 80
    0x42c1254a40c18181c0d00c0e0141841906c00d160b001010900ca0b6601403d11a0b60001029005500b49aa1949405106c400c03e92090b004100c0c40c4041c45810840840c14540e80c24069030f4030450040110401040f1405003091322042c0c4101240c41c40d07261022402e0307004204404e034100c030b8a0f68203000c1c110f81c940c034021400c107001c40c2616000700310400030140c40b14122007004000d031030080103c202104c1c0c0c4160000c9003510a02544c2d9001070016218400381d4041d242030f03a4000343d031258a28021b404c9aa001c1c2031080e01d60300a170302c208000c1e6030008945610450075074111602c0021864038034043c1c0700010350500301c60304040e00c016081d580059142d0440c0d240c2400490502d59614100740c90380010307100560460300202090102044400c0200203111820041b02c8c485085080c40c0c3c8210f07401518034100080e140681088810340c00f00c188990580f030100244000c1c00c051204a0ba20480c00c18000c0a204001c03400c803140401071020350b000b0407010203510302d0000319072815a480c0d50050104 = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 147324658 1250 147323408 147323453
    0x515091f080a12030c140307050901110a02091506070501230c18040b010c0204140610022b022407020d1b17130b040905070311031f030f 60
    0x900309000641a0b20058000501240781d507442c201c00c5018010a9040c0000d02c40103a403c0805291020000d6110f000c2d183d80303058a407008800018030f83c80c500c070200031a95108042c5030740580c1d502c1d0030700c94205680480720f01021500001082841c0100c0c10050f00a52038006648100d440c1e40e55540c5400c40e06120241843c2c1e1340310750703450840c0a500161a05140610714070b0000b824207a001c034244d40c0050600760b540b00c074540d002500340c80000610f0005089446c05100b028201344130701503441d800a001500f0341320880e4802c80004a40c2c08a0343d14008114080781da06a8024880b004003860f41c4000e0307490860060b54542d00d031540030740302c1800501c1006000c50b01c19100361010791090b0001060311511680544811111040c02c2460400d02042000440c03094421078080300e000f000c2d0720880d50749813032510325610300710388000b803909042c5400c19802c90020300031441103e80c040601031000515181c4003001c0c40050703015400c001c11038550290a00144902084003802d240c151520 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 147325908 1250 147324658 147324721
    0x708010b0307060206040809040204030c1401090f1206180203010501081506030c011e02010e0d03090506090105041e14030310030b0709050108070e01030b1e01020607140a03051509 79
    0x5160b9a142144180e00058100300003240000b061140200b1084100400150800d5165140c042c040e081e01c0c5e10172001881075000070841340d600070b10310700d00508100d007035202d18911300050038103040904080108055134130401c91400d141802c0b54402c01a401a000304010340c1c40380c0302c07130b580c030049402d500c096019005c00107901803a0000c1c11001002d4180c0d10801d1040300690001c1c100003145070302c482555280e041001c0701d28002c02080b01e441a81e40d4000c2801a0b26003003030303410081c02511000031030341008104004074158840300340c00c640c0b14000d050501000c9080c41403070341c4110b4603d1540384c0400400d002025130149990804d0324080d440007010360726600c0d4180d500c40c00301c0c0704242c0429803c070b00064605005013640c0040700010706000c1540101c880020b6902d1040b66040581101014148540c0b540e04010003580403805060900c41002040300803482d500a03540d56504046d111400603251140c0c0c030f840d01d10308042c00b42c00c07282d103410303ca980c070509100d240348040140703160714a = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 147327158 1250 147325908 147325931
    0xc03091c08040302040b0d05063310050901051204081206010c020310020a091212030608030406020c0d030c0209040506161404050405180f0708010c0507030503131103010608070801 79
    0xd03980a11150712070341c034900d801c2c0780d6030030301001d0700f00340754629070200c03101e042840840d20901c0a20301c00c1103400d403440d8008038901c100f16961640c000b5000030307040b0b42c2c0010101d43e49841500382c003500054140b43d0303194030311070004845510a0015071250701166605110401600c0b90181c03518400d00c880c01d19032551900c004507444440000060f505901842c010240b0b05003642c0203001e401080d01d0030124043d00c0d200c0c0010440503840045960a000b012071901c0300e5070612551010780040b40255182500e0140001e40d100c1410748101c0c450400001e07020205401132100082959018050044514160a0042c3c0310301086400f0950900b0a02c071148140e440f0b14500300350079102004040c141410f2005100040400500a5003048a80c42c0c0c0a00100402c100b504c415204043c024008642000e6005003074070b241d11074000901c030081c08040d0000380c00c84160381c3d21804040b1001840c08c01c41c2499070882280d0a15160554a05200030824050205180742601c003184001d01c0b445d002503 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 147328408 1250 147327158 147327199
    0x30c1b030d1407030809010605030102040311040606080105010203040e0a1509020d0b03060709120f021c05070b0316081003060e01090201020120030c2b0902120105040c12020a0306020c0309 83
    0x80c0c45a2503403482c10003541c000240a405001c0d00700f2044400040d82644581c042801ca82c420741096402051904140c111450b2502650010b0328283c80c0654103075140c900080e503a03026602625441c0c40c108000907032a66855800218003185003090902001d40e604100f80096015540d00c05155003000301c15400b07030400013240c1780185503d60f07441d403034145440001190402ea51504480800d40c1100e07000260340c40742c050200c0400c030765a440181c20f41c4c40c82d000f4030301021384d40031505e010002c0c0700304225a00100c000004c60481c07401c0141c115034030384051500c902032079000104030701d00d015140002c4d444154030001c4298030070b0300200311413000640200250040d00d0b40403440250b08000044400504c90060031007054400944400300a44003024600c0040e00c5101c0000a6541c04e1100c0640c90440c0510f1100728a4400801080c241394030340035035030700d000c0c0076048110f003203403a4030030031074887c500e01600460b004081103486004023a03080d5102d034014050b092042d0503d002c0c0c1200040b04 = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 147329658 1250 147328408 147328427
    0x403051b090c070503070503030f01050a0e010b090409030315030602030a2904020901050d1410060f090e07020a1a01060201150b0405041503060c110d0302040609031103030c1b030d 79
    0x5144001030759840202e800c1e40d41c81040101d5030750206100031800294200095405140720600b8494250306000034040310710360540c8048540d80501c4010032040c107000d01100c1d420304d012f031030118401085003003e5019200e55a64409483c41604001007400120380c051400b03510001009d101003281034400c2d5008444840c141040c6501c0c20314080030794500f40e8010700c1e9104060401c0b50601032070320008030031540b503e50340790b041030021402c1050804466078484044d040341e01341040302006000c401840a55a401900c0351034a101001c02c0f007060003040071050066120004440d050118688200000d03030a1245030003540c2031002e40340c1414004440d0f40d099400f46010941003038900b104000250103051200d15520880070004804240280580080750321592034202c1d49e03001d5000d5403850490300c203c1c03030f204041c8103000600140f40d02071141c100302c0340c2103080c5203031002c02e840000e401c61141c2520f210b010f00c504121000005090f03060007410b04822010b4903c00c0ba0f8401c3c05a800110 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 147330908 1250 147329658 147329713
    0x30e0f090105190e01030f051603080306090a02040b0c03071b05090c0901030f020a020102090f0105040b0d052203020706111506100903060606021609060302010c08030a02071205040305 81
    0x161040140450b04281040d00842444503ea041510741d44100004101c1c1084c1c009444c012828408081480010405042144101c5e01c8241b03a107071950b143c00301180406004e440c81100c414010411132072140d015900580b141a241c59650740746207511642c6e070340c450442251000d0890410608800250391550300307c0364080c111508641d507401e011042640203418407814143c1c0d41400728000505840500410740140e000165209030000800c1501c0700d90000340c80c1000020002404460400c0c42a9400d0052850000ca610b80b1004410300b07544a0b0000d1a4518a240100da5800e2590003d0b008089442d56200d00c03048200301d03404591105c3c181d00303890b040035110b038001ca8814104910301000440d0b9901e880f80e2215100d0707490f02c0940343d656000f040103a000d1074084071050440b2030160000e050f0003100700156840d5038000b0f4444004200042c10465022001520780b01d01e60f0101c8965560000d502d1241e100c54010103003060f00180000c0d100d91203180c1454040c007082042c9001502e9 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 147332158 1250 147330908 147330919
    0x90209060316032d0509010903090510020c060d060e0f041a0711070e0105011d030a0206090105070f1a0903031b2a010912140403062313030e0f 63
    0x19a07007032101d05a0341007120110201960b0700c100e0780c0c402100d072013048041001c3c3c0d25980e6050507151114002d6400181081810b03900d00011080005c1c1c014040d0001c44405403414942c1044002d03090342440c0722021134607008400000c1d00000d0200a0b0321000030785040040708201031311071000007943e06104590062168900507c201d251103410490198046040c1c030380826603140d41802c0c982040c1d440e0384035038000030b4104014050b940e0050103002c01e5003580f44155221360400d0001990724801e5503001ba02506001403800640d07407051044900d060303084040084032410750300d8540d042c242c4021020752140c20400c0403031900c00c4080704880c05041c440e0481043d404604480312015800a94a000d10700d07481c0758001e0910007030040012092401c03c000180d00900b0b4103154454900301d440c1c0808000b8440781c0494030031a1181500c4c113687d00031800246440591184444140013030300b0040100079041d04100c581780035151030b5070741c103842983e41d0800079244000380159036000725803207503110 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 147333408 1250 147332158 147332161
    0x110f01060b071416031115070b0106030b060715180203030403030503091501050f040b030f070f0e01060201110a030207081c0f14060609010318060c08010806100b0403021e030303010f0f0902090603 86
    0x5681d1b14212140040001d02d501d0200d1084a012403050748030303c104880c000818401044401c2d05481010305064090314041c0c90301013250303a00304070110b4428007100d09994036800e048050000d2281080341990260407203a840c0c2c3c41f401c000d001d903001241c4410080c490a102d00086446103090381e41221405410921607030318840400000d00042c058246d01442502011400d21800b004004000c244100c0011940c41c2000858012400e05130000c4042d60704150304007110110000884075000031b23900d80140c5801440c90324141c9841420b4000000010441c01c000d5100300d1a48003081d1a0040c0d4010030800100078122204000e00b168496403082082c450f60300617501907005140701404400101000766056a9904100d070f00b403040d00c500042c071034801801018010001c09821800c0300200d00343c107619046901c1a40d100e5400000d00030104010b5140003015103502c8400784020050980b9225a19100b040c0c8160b4420311034203440e54800e03030000980c04624800c507140740c1405080305285 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 147334658 1250 147333408 147333413
    0x3020904030210050127020306011b0c0e040804051f081b040803040303080712060509040f02031c02010506100507020306070305040c0e04120f170106110f01060b07141603 75
    0x10264010300a0341503008030201c00e8140007403441018080c02e69140c410004c6d0b004001d03080c03000040800c414110718410810702801e0b0703801002000400502c44030704507520550b890051500b501580c040b040c1204030005101c00c0080070780c040c00030b5a01c1520300201010120851100c541885081c1201048410010aa003000f0b0b01c0c040002d481041d11025140903699024541b44d544264015000a01000103210040c0d83c82200c1c00040400c8000a000440c14100010103010005e00010460f6103a01d1480045490500c241c0e444030009107900500d009002601a02906d0110340e600d11520b14100220b6245001c3d00941e501aa00a40103021503a5800070a400803c1c0150081e69001500d800000b002c020f2810304520075489030700b1100148581300340c0640608000030400d4103100b46008271081ea400403000050444a807490042c529003040b011380e904008809501004650030320001090f640f2583c0c0c020181d0b42e01c2201032483e43c1a812041903102e49244058001905464104002 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 147335908 1250 147334658 147334669
    0x60a0b09161101060b0c0c01080606030f01060c030e09161b1703070201200703080a020403030c11040e1905060c0a1d031920030706050702040e07030804030c0906050a0b040302 77
    0x2c500c16000000307481615843c110550780c1000000f404103911414039030546581c0703e2001500072109940c0241982001840e181075042c0501440c000c1201c6100d01d0014184544000501400c002d040c02809081100508581426a1442c500824101011000c81d070301c0c80c0d00c11510301900a00804880d603203c40900119600207090401190740300c0c100344089810030704080340c110310b582d000e00b5964080c91030003600250001f051202418418882000400c0e0403c08000a550f0300050a0341341d900490001002007850160001c15031181b1605640c2218140c058006c004c0d004804542c626a1a8408210580700d03601000c00043c0e080c008030038a03020840103101382d9100007025601c26120411800720205d00980058a1190008a445200344106240585240e03002d40c094800b503402c215000e040d620414000a01960350303042005100c1c0001d0040c2c2d070156600600d01d6940e030b076803810410100b4000d8010840c86524150300000c4515010034010119404030300800c0c00d140c615020400c = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 147337158 1250 147335908 147335927
    0xf0207050108150306011d090312010e07090806090a02120c15070606150e1801030b1503030d0e010203060a06020c1003020c2b0201060602060402090402150d090302060a0b0916 77
    0x404040300051500c600b96001d05c0918042e004850300c4681410703082803000c00e00740024201c0042c07504100418041e00700740030469410345101d80c0ca40344068680d9402160410681c1d884000380d0f000d06828400703035002c04501200f034a070088601c81d16043c4500607107526802c6502816a00c612200210104601e014001d8440940100000524aaa6102e0100784d031038060210500180706803240c1401481c20314030440b4903020b400804a46581540c0d40d0207641c0c0000b808090130100d8504501c0c80950b010401c80d000741040d403406112071020f030343c10f8501035001640e4252040f155a680401c0c00d0744006400c110442c0300a00c041928500c1040950003580100400c40b9603010704c04284c85038610310300354140c122003440681d45054600707250007821101e96420400031500603000780800743e42c5034800c0682140e0101d443d406000c1c08000c0c00e550351f221b07031012502c030281003041d40310900d900443c11134170034050440d042c880c070000a0204841d04108840c18407844034082040180303548a5140305 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 147338408 1250 147337158 147337171
    0x112020d0f050f0a0b0a1b08180f0d03110f030a150915090c02030a0914011704030804050c010e030a06091403070605011415041701020409050117010501060f0207050108 74
    0x180ca4030307800d0346032141000240103901c10140e10158002c07041002400d8225801031203507000704151500e45981c000c0802c4c6801c1c8180400c13000d00042881c0220342807131113842c0c00c400000c590340c10007540d1a00e0344a02440900401003883c0400d600030400f9001c04075458280910311807407660b80c0e13043e4110300610740400d0b0400070000c44000429201a00e114850341c07001c500c42414800c900c1d0280302d000707031101010303080115017003400114440c581184441058418040c1e41c45d900c9a07a1100480303041d41401e406980180c5608103200c1810740050344903020700d005030709036550039050340011359103400f03072100480c0c01d944020b0400c4013140342548041d4a49100c0c011103120300b41e408208603d0b5410040090301d16a0741c41d401040325900c914141e042c00041541c0354481014000a07550031070143d44a0280c034000300540264943c2820750445000e8071403402c2c104083e5844500038032810741d40c2c11041c0e24661900d000825294040e00440d24030750700c10f500801c1982c0c180001110b4610016112 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 147339658 1250 147338408 147338423
    0x3070f03140d0e030304060c091a07050a08040b18040606090b0d0605030d030e0105090c10050c0c03010f0614091b09040609050703020c0607080402010f030c02030903070f080705090112020d 83
    0x2034a144120034065003d40c0f001c3c842c000e54890410b400c00200311040c1402d070100f441042e800410100d2040b0119030545808580380d00d4440740d050030903a0400528081c018000e0800040104081030403d0144c800b01080312617456002c00c0c02028001100d440b4054000841d50a4400b040420189801071151484420010400355500d50100e46800c0c01c4204c68004282c44501809051200b40319580d8860306403c0140b182140e000086600341030345030601c03c10810000f0345c8030204d80c0c0400c04540c0710341d0043c6c001c01a40004901080c020710050003202c201440c4070200300d5107480c26510090154101900405090709044e8180c2c07410f034450b05801d60080d03151100012258440d1040d0703031007003006403005039461881e580070707a0404600900d8038003070011050501004d82d80c42004079180e050103050000b9081e1500c170080c0c1c40c600508484541c1445420008900018004ad6020482d00d080d412210016100e0f002c129222030701740920000f80080c144800e003d80791034076225202c0d0340a446e0 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 147340908 1250 147339658 147339667
    0x5030114120a150f0b061602010c0c1203080703020a14090d0606030f0c05011403060405040f050f10051303020a020d0206070206041203090b07110120150a050903070f0314 75
    0x1401c2c0c24074040c0303042a243c0c41c00402c0014031106041c010641e1415611104001595200c40042d4a5019190b8041030520800481c00216402140e103820241d800803000041240d0710030100380000d8040c002100004c0760703440030030040c1e4001d000f038610010f25519840d1014503d60b03000030540d0020700c48503030f0005003400b0141c0416403034403440000c1e6020359040703042c0c11900d06001d042c401d0141d002034104243c40c8a86c160a501143c1500d4102e84211000700d200d0f1100d0420680d100400319015003180600c0504030074440000440d80b1100d58181350901c1903075203034500f0101911100c000940940c02c4001264014900721903400d031241d01c024071040c10300e005034001c40c0030b5400682141084071542c4030050140742d0402e550710010034100120b145003140c103a03501e021f000d010302c402c3d6040c008031060100001300c00100140c801c1d42454100c51624884181640d8910010380301006120715080101c1c4001074040b044400c0290000300b107410f00d00d141d40c1e003107400100180455401100511 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 147342158 1250 147340908 147340939
    0x203011104060c0c08061b09030a080c010b030c040e071a0408120406030e01020307050409151809030e030a170f0f0403030e1008041110050d15150f05030114 69
    0x2000d04041c00c190381c0c6400d107420b50b501c4c0c084c404c440700713421080b40380d8000f1040000181d446241641e28940d02c040b4a070321108040d0100c1d01d80094500300518100b40400c445d1280c402c154052a4185001c404550600f681c403018841120180d00c041d4900c1d40180f1018062282c0c20000d4002520f0b0748403180b0b2819541c0c41445051034400e299148100700c0005040000075414011640c02030401c600031440c6041c0a08003030418890b0b4411403c5140c1c9410603a5402150032203903800030050042e00302c401650f16000d00008003005081100850305030000710000d4180020104059544440d40e012401c1072020200c01c0f035000000c618034001001c020000140c4000d1003d08003c0d4800c3d2240a04600810100001c00305445046001c00240c8800c0101280c218450301480c11401c1e242941961490241181c41d48100e400d00c001050401c3c5000302c9424013a0b486008441781c2d0030440b00c1620340c040302101c4002e0706010110024130300b0300c018802c20380a00c02e000908940200400200790448 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 147343408 1250 147342158 147342191
    0xa1107060c0207030308010801060609030f110907030b040e07150818071511010519050601050906040e040c0e0c03160903051c02010c110304090504020f0616020f06040608060d020301 80
    0x500720390010b8100603c10010540c01c0f0100c240940b500c04003e200c45030030040000e01100d01440040c14a80e8406410018020340c111584803070f143c084e00800701480c101d6009000344c175174000c15038015440d182c940d18020308040741410540d00c8030500b21152003c4a0313400c560808000c2e103c02817080154600c035031004403c01c1964010440d49070400c82e400210306001e8200c8000d0312001002e641030000300020b1108a00e6800001071508100040c02e480300001203e15029040c91a500312000140c04a00300e280030004500ca07900c241008054541c40f494500e0681d10159001d035580701080c00131400c400310020b070000983c842843c140c0c94240c5d5a0721030901d458000940c0c80c001006207542101304031b0703082c00390803182c405605201043c44100002c2590704e00c07440c81450f10080d901e07808501190389035140c01e0208607004003041d4a40039104100d003012004140200e10507100303003c80b055103041401c00e68007100c410f9140c4482c02d69408007407081001ca040c030f00302d0b410b56841500c0c05422100 = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 147344658 1250 147343408 147343421
    0xa0504050c030a0b04020f0a060e010807020f34061b111003020703080c0c0a11060c030f04060e0109180207030314100503120309031c06030501060b22030305030a110706 74
    0x404c245880b030704050040c40440c8161011250081c0c101c00030512229401040d140380b0001d0a1800b0707a40d50b41c400c00d089042a494a03c0c0c030034140100b40c5601c080c0220a1030b00400c0e980a1201200c140302c0c02d000021140c822031103a42c0100f440d8481a05003107141c0d03240344840e103008807224450000310500080c400c1c00c800540d00046030380416080c0c1403603403104800350f010121068030340c940841103441daa81c0d07178000c02c4010150500600440010744075402070320508060841142d481d86800030300b44007603410901a02c400942200c0070b00310990f22410300c00c0111040d142620120464800c50031000c0d5200d40d8003607040c075407514185403909140b010b540d48034003140501052881e081104040c00c040440301c41700c0d030003541482402203003500403080b0345624041c1d641d0702c9041030b80280c17060007408550740080e0a55190590010324a01100001c1c80f41d1132080718031504030b4000c1c0342c1c03449140c000c44c0000380001d8000d00000300310715003d40c0f000344504424945181042c1c0c40e56500003c2d07622 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 147345908 1250 147344658 147344663
    0xc0d050c10030f0c021513170a03200403030c0305160c031101140708460f0201020703020d0302130504020315030f0d0c0206030a0e0f06061002010b01080a0504050c030a 74
    0xe03100c80081100b03d09204001802d240ca101401c034055549040d80c0c1c1800002d0070702c0340c3d0300310410012400c00500001c64144d2050007818541c9425500e40c000d00242000a40030903503409078100f1204a40d5464100c8066a0b4591a0460204080e85007219190806a052803000003210300c003001007508068058001d510611445141c03000f10700005000d6090f80300721081080041c00b003c0c1c0012180c01c1030701c0e500002032600309015484d2800242c0340ea680b112000000c01e24001200e000700c000c11840c0004020301d601c61100103c00c443c0c04034200d1041141c040c006801c0b0044e0b5a402a109400034260740d01039411b020348894580000408982c02070303885071010300f4100080e143e40d00b4148095414003a817500070b05a00500f280c00603114404002c8003e208201c004001298158907030b01000740041071004640b41048a02d03805c40c1d454209484045c1304182021884c92028414015400b00003010380d210b000c00e40766a82082c01805003d0011292809002c00c1e00000351000c1149694050 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 147347158 1250 147345908 147345911
    0x312030c130e1f050303040b090f061c0608010506090108030d0b0105190c05010b010504050d110d0803040f030909110f0304050a08070c0306050606030f0c0d0f1104061e020c0d050c1003 81
    0x6040c3d0700e100b1031580f076900c0b490103901b044c0310800c002c002107402d8404002041e10303241c8041d14801c0006405201e1680032a0b810700e5040c0b9800441c8811f45e010809981ca607000800160704c4010400410050911554411b54401c01c40c00030b02e0890758209201c440b4041c14010700704107190000d8101c00303801506402c0050030260600c3e00b404000d0140760000380003030a050b4a003030b0a02e008500d4016103042d01034141e014204076604507440d0104c14000e031035000540c1903102d05140ca49080d0040d421041640052a680004225040c15101c1d405002013080d1000d8070b44900c00c120703502c040e000288181c0da940650628038021800d08401012010310500101004504519029040f01d502404517806004240100956580036035810340e04102241d01964031206c42c000c01c60007421500080f00038040c140000f103203d04803454090401d60324542c440d43d14205000c01c018080c103403854242c2005038492458041c00e4144800720400203801103055400040d50800864240c1559900340030019 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 147348408 1250 147347158 147347191
    0x30a020a0519020109120c05090a09060c030b06031303170702010c0908120301031e2f06070c030f08040e0708040c06020f0d03022a0a0506060312030c130e 68
    0x1404501002541c141c40024408407503000200b403510180911b10340002e28105060a020401e0005001801c00034070480151400140000150072202c2c0304031010f070300307080d42c44400c203000b8000c09440d02c001074000360550791400341e2500190305461054050101411480c680040c000c2406445011240c0002c180382c00c200344000c0c5000426800145950401d04111305003108c1441140d0447e40c029070400c8001109503841d100400500074000c0019004c4000100361400c1e58148030002d8900313800280c0c05400d0602889424411004020310300c00101c0e40c1440000c0c01010b0002c2694081c110160800741c40340103402da440d2040d107802c404549500c00b00b0080243c50081d0038080d001c2c0d44007030300400c0b00030080c071a65002d001e095001819000310f462283c640c003194215004100d0b500c001c8401209003511580c807050054001c4c2c8044c01403e0000e121800c00152400c04004510303429403440e6600703407044034103805c0f407916159003907190540002c500766410b07030550050100020045a2 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 147349658 1250 147348408 147348413
    0x203070503120f030c0c1005090105010f0305121803030301090e1c08070e01120603060906050f010e010902090a05090405060702100c09090b03030918090c03011b050d0e030a020a 78
    0x40452540c0580d00c030b5031149005800039040242510550b10b0354401841e181e0300d841e0a140024041c40d800c16210b8410300106100c0003280e900a07034090f0520200803c46a41c132152020b502007043e000142042d41711403c480b1400c0800d0380101010440c081c04a07040c58402c40001e400c40e4420307840006981c1d150509181440c0007031040c070248041900e0121642313005100082d000a80042800092086002242c0e41590040e12061914850084200481c07900c3e464248000c00100c007099403240c1c64807001886c141e44584115050b98030041d4524030603807a04141e100a03500006940b038110001c102d000840752a8050342ca40a0b130b01c1000500858640114003e2502c0030402e1414031a904203001c424643c2d80200d00f0320191303507030f229000c42c4807440880407030310710700c2421141130300b01891840c002027110405214900036203003501078a240c220300c14200b40c00d03100340719401036500c002c1802514103c2d0044d0000c100c200309101c004148101818025030450f0001081c180c090380102050008 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 147350908 1250 147349658 147349663
    0x607050a03020c0102060609070815040f060f0803120103020d060b04020f0403032d0c030201060e072c1813060c0203130e011206020304140d23161506050316030203 72
    0x1150f940030f01c0184103528044c030000c0d4072100041e000c501030040c880081510b2600102c0001029107000c4c0c001c2c481c80e404007044000809044c82000300c0c85110446c08101c80c4408822a4800e50248000402507421502000768038281c1b1941140c0c12a070316461041030341c5440c0060544004181c4000b500e544c60b60070043c111107038002000c582401c08009400002c800c0d5000161140740600d852a040a09854241d0060032036800c6045c00018410130003400b00c0d840410004042e103100809401805048d4a0403101500315540503407140b85007801007003500305405819070020f80d0504072004011107403100e00446854801e00c030010b810006081084601103001c0000501000810b444903600d0400b260903040c0c16501c00a0055400002084c107000c80b00d104010142d01103c10f43c0c11744080150040c020882800e224103208400310140100c141d0104250340400c0b15015180c0441341681d0b8544501d4140d03580c41d0305c1072a40d20440811240c034204120350049842d030350785440c00e0341540105031 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 147352158 1250 147350908 147350923
    0xc030605040207020310050c390a0302060615040b18041505091b1e0301081006150f0201060b040308031806010305120306041d061006110c120a020607050a0302 70
    0x18041ca004002c0d880050f100007940d0803100c0810b07580080d054072564440c050a12525070600300410a00740c40001160101002c00c1e0303030300d44410244568003400030324281c0f0b0b0b800300500640507822000006000c0c2c144540180e0003c40e07803a140b40c3c030701a2901c0c2e80302d01a8000301d9031402081a080500d07410707802c16110344d401c0c11800b0a0380d141801e00d0000001c03521000103041b01c900258190f0002aa54043c200346c6800602c141e44441150652440710502c5407c00d00c600c010750300c20030710450a40a500e10030642511440c480b441034a510052050342c10414002500003159a01c420000e41e205c216000381000e94031072900c15990f420414040207203601d4120381e004080e00324400410003e10001594500c01d00e00c0780c4800e4403540d403200010000e110f070328890300761070f66400c111040003c800f040c1c680c82100d002c040c40f41d071180c8402c000c66865280214409140e402140001001d160041e9211300c0f0030030110890340c0404140c1c1c040340094000000c01c551316030015001c142050f80501c82513 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 147353408 1250 147352158 147352169
    0x406110601090e0a170d02030115020d0c0f110a08010203090304050a0b09010906080a090c03060b09100612020c010b1c0209090a110409140a050d0e01110a080306030319030c0306 78
    0x5014440d44003c0b1152210304000e001030601020400780c4100c0c0f003003882a50251601c4000444d165a03465010300c2018284049801c01800303040d142002d83c2d801007295950450b045031950081d600181c3c2c0e0b1056158084000319404800030500060f04002400110f11611042002c2d44c1c542e80313801c0032310540300d002e0780002c40483d500340120412640c1c041d020004960061030f003e2010780b20f010660000f00300182020b0140070300450003005004090f00141402c0a0585481403103694002c44011807080d0360040c3c1d000a800c00c0c2d01102070000302d401034001c19801a0000400e03620300d20001d02c004800740304a203850800741404100750b20346040300d96804859500a0302c10041240c2d541c0b03078040104100726101d1517894200100340241c144210000f0240302c0d08a904ac5519820000d0b41c0b031002c0c00d160000038403056020580f41d44621391010300c64600b00300415904902d0b6841400031380000380a6030709480140828030b00e100385034040302c0035105140c50000780f5240140c80102541c8203900310 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 147354658 1250 147353408 147353411
    0x4060c0f02030c030d0507051905070311031e090a0806150a0e0c07020607060906050709030507060203040e04060f0b1302040602060609060f0d17270f09070c050a08040611060109 78
    0x410f8000040112016810ba00c0c2c400901561a020262428000c0580099843d0b0010209080194011004060080c00307a01c50003281d20030310b44a150b40384699a114003c203203240310704401004440c400751412020082481030040e0f182d0001d00d15000c011a94240a800461001070070717400c041401c4005460b1200b0020318500e0310782400f0400d881043c40c000c2c001c04000904d070301808001e80c481000158030140a10040c2440c140060104001c0c0c0410748281c003d5103400100680004100c8040b61070b00e00d104070003642c9a440d510001c00c071b014820342c115a2200744c0351406594500a048603140301c58001078413641000300007407504000514050040106c0c030140152079807003a1010076003402c00c80b441c0117540010b24000405010520005840f04800308401c9124203191b440c000801104e00c101c1c0e56040003e03001c01c240c00700e4068545030400c4c20200031490b032510038030031002d08a000e4412924120005e550302c80d00b1703034071646c855000500c08542e807404009003840958010900c0117070 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 147355908 1250 147354658 147354667
    0x9110d030518011106010614070803150307060302041206020306030111030c0307080a140a02030a0b090108010207020f040203040c0b0c03220e0906040302070b0904060f06170c13120609060504060c0f0203 89
    0x190b440d0317581018007440e030902496600300c0e4a00c10300300d02115142c40d40104003a88904299001c4000814400313800d6119005a10303021400e54820b2007642c0072140c03003040950341c0d030549445d598020761024025907055500d81166443c0c48405000550168079030410382c0d6545d00d00750768020107652000d81002c000504084040b09042d0181010390b07000100014010303500e84070310705000000e0008009664110541e0800011002819070280c200c943c000e030789160421040408100480c4002c4500611502c18240700303112048086020b082d10700d844004a07481c0207680869602d08001015042d1020100402c050014440c0800010b40140003e002801c4c1820a650f001e921600640100310610b440820050110f60b40e0748c0000c0021f0a041c10a002c00d01e80b5030310028110084030000407020004000401c05100150007240c8914100680d1880b100d03041140a01c0101d18041080e01c610303494a0710600400c02d10b100d0b2074003e6115200001c2c8843c2c000c4405054001c5100100096410610 = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 147357158 1250 147355908 147355937
    0x403050703110c13020d14152b030e0613121e12030e071d07080108030304030f0e0411030a0b0f032a0d0f0507050901052209110d03051801 61
    0x6940c18504c4a0500c070140c0c60350348190390718000b86400340c0c8418101800c90280715180c0c000c50302d8516502e5058403616101c2e04610241c06c5809015000040c1c03810321540c00304007083c42105205484103004150314600507895441c0324540040d40c102c4100b61410740749002c20032420350750121110030f01900004141d071198981001d914692421f56042c1a2a10042002c02c10240001d0380a0100280991030340120110644101001104c840021404107400401d82d001d001007030b43e1007640c1c183d44044029411410469610044251140c4c000e610742000d90350820000014601c1510001070000d148030030070040101a5074801c0b6400d00942200e1036081c1080c0c00b00030000c041c4001c071a505041c590120b80410004510b07008080c091450030080842004004952202240c5040b1801611a62902c0402201c1140d00510240d01c4014100310600718041d41c009600d003900804c4c0240c985149440070a07044850788004a00140000546c05078002140851469000c82840c0500107109400b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 147358408 1250 147357158 147357169
    0x1051f0b0306090406110705030c0d030509070627080d0905090705070f020a330f0815030a06020f041e030f0f0f02060a03060323071e0e0403050703110c 67
    0x242105003d20426000603090140982224030750340c90141b0843e1792100765040c100e0b100c2d000360300c2ca400b050240d80e28061040b4802d0090601801d041c40151400324a0407105032401030003040104910342a80c00110850503d80000c440200030f0080600001640311000609445207504820b00c1020035105000126030b000040d030324a95130084808903000128000100384480a84c03015a107103030444911001031300000380051130700e0b150861036a03250b00a0031094900c5c2c1310147e500c3c0002501c82001451255035444918030840340981038914900f42c0c0c2d25100f09980c4140040d0f41880d800003030401c1903800d0382c039084144114181c80610f442c1d055648a01c40d9440d401da01819402421150105004400004484259006094590300d00c0b011002401070210780c030003902c2250020710b1020000c01d0b0407085030701e00c0c41210040c010841c180b19000c004583c0d80c52100001c1c8507251404100f443c0101122402580a611119251413403454000d1000c1029403400101d42c0004a107d501d58444 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 147359658 1250 147358408 147358411
    0x40c0b0315150910140315010207030c09060302030f010603030537030507140705070b130e04050105011706060d020411090603040c0e070c030903020904020d02040203040b090f0703170309010e030c01051f0b03 91
    0x180c000d200c1c0c7c54800000102e02e480b85a40004e00220110f580004088100d60700410850344241c09a170740621045100c2400c9a03214400540800c4080228079016414000d43c00410f152b103079016000c500300e02c48024003080c0b0050680c008a66640309000400b504141c000c11014408070400d07180099907640c0e02e807120700d03c1c4180c80c0c5100c00441c842140c1c07042845c98034060805064800114941410078502034102842200c901202440d17076189a454017044031342c41400d01030001c1a1080c042d609000007000034201001c60326400b4003000510ba902e01c0b0040d8000d40c0281d180c1448582000f08400d000384010f010181800038040f203000009030000c000e0412a50111580380b0255254004183d0020b0840300003940907100104020030400900d0015006d2106401200c4c960040c5900c541c2c1d0395002400003503c00040c040140310301d02e10110040d580504a0400410400310b181c00e42451a00030752071300300c40b59444008020000c50101e030a4094811240420f826061816000d0a03440c1320 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 147360908 1250 147359658 147359671
    0x902130e12030903090909010b0103060506090612060a080a0633030602030a021309140c18060304060f051618030c0e0a110c0309040b030105040c0b03151509101403 72
    0x200014440300400e005881c0502d85c007a02e00780d8603180594041c1d000385803060100d40403c1ca0701034046010709100055907a04217016101501d081d0341c00c10b00210055004145aa00064003840468900c07030510007080303102d103c1c540200e0302400c0703900c61000c2d001003503880c0d41001c0e1007520114210700b2008603180c01c5036046200140d403601c9014440029202c1c0300100c1100c50010140000d00c180c6550000045400310f500e00f80c0d50303840c0e55000400902c0380000b44500300052610008840c6480801545c1151083c1000190034070340000b000c046d1385040381d141124131031075001035a015402500410312041501d5100e082c3d581141e13a1050750309518003511103540019000101105299404547e40d61080302c2401d41b01d168886003155a175000314038080c080c3d400c01b0040c8042c0d050500804d806194001c2d00061401c0c14102c0f10300d042e410060420542069401183c03145440d060b14a80302d446060011682e10345521060080004e4400208420400351165805501c2c400c0f009490b040034 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 147362158 1250 147360908 147360943
    0x41101110106080a0b09010518071512090602040f091407030908070b010e01080d0306030206030403050901140403050c012d1818020706060e07230409020a030902130e 73
    0x10310850605004003480d03003091400d44204400c050501901401c00e42c0f003500350038000c1c007550b901d08200c0b0300c29048202c5d83c1029030b40314240620420745030b2050224a140c540c6420300c40340710041110802c0c1c41c9440d40a40d0069400101400300c4107050102d48054011004140132203091034901c660036400040c40d001c20982e540300c20408001d010720442c0c002c203410040110340c5584902c0016458102031084064030321613031520854041c0680100f1045a40040245040d59640d4a0644407070380305000d0b070390400201c2000690b2152060300a0005107018000500c9620f2501700090078142c0321b548252102295913030706804d0b41030800f022100409013032401c00700d810000c0c40c003290100c647d42c01507050040d08401c00700c40e00e0065400307020440d000e02303002d0107003c4ea907019099004a050340c2420014a965070400d98a5444884107000580c091154910305035540103508201e0300b0141402c00000d80310003220f0700703529001c02500c5154203075000810659200400b502c1da507c01031030402c000c06 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 147363408 1250 147362158 147362177
    0x90506090c0711040b0d030801050109150815010c120201050415020405060913021b0a021021020a120906090b01080c0a0303080c0405030609062a0a0e0a0510110114041101 75
    0x640313881d040a00d40381806003d502c8800410310300075285803400d00503240000d082c000006000c403150090044d4440b81c41e01e41054607280c45114411034806000b1060520188107410700000d00c10014101c603d0161364000101800c052070100c40001c2c16078075000c0242e0051000b0310041c0d44403011112081011128403203000101c100540181c0142c00e20310520140c05404c0f0034248501081201e00c0038400c560300000c05d84130b00c1007a030794082c80b15a08040304d1310045444821100070b9009105a04060908054149100d140f110580c1e040030001c5441ea91a0020039040102034a151303405486500040c003211079005000c00c0304030060740300280421001c0d4010514481ca110106c50203020080c0540c0d00b289000c1c28100c0d0307030321815285a1654810a06244803443c1c0c21a070112424020f141c409141c414207480442e413011404210300e40c01003880d00001200d40d070304240030402c0f5519469090500c0319000460b421110b03090600701040b85500b0801c400a020303c103902417a40c109083c03401c8107 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 147364658 1250 147363408 147363443
    0x9010f0201061802070b011e050d050309190501020c01091a0702060c060112031d0d11030f151506090319050f0601030308161e080c090301060906090506090c07 70
    0x2d44459445064100c0c28550003540a9645800805000f0301615102d40f40e079907504800000d1000c100e030501008445140180034500e07051040d5058640148222400c1ca044e0700002540c4803030110303100e1103050510408000d076580511166030050401d00384030170170a2400c0d0041081880b24242d030050090700040c28070071940ea00e01950412421031003110310355071f12440080181440c20b00103030b020490980843c0380d494a107c81c3d071a13440201801691030000701c1e560b03002c0d4903211120100e034107000d280c0368110021020003003010303070303a8015901c007020b420204811000501c646034201c0c01900200b00c0d20801c0e4500060740c0140140118290409a015060507820041d039140e8803001800791400000a1582c40400c3c240590344c402a980b00044110070300b6a03007400020b5414400c0701602d0040080e103400741e080182e110340041505894511030070001f80c210703003503a00004e03605551100180040f0086104266006200351850318880c00d0002d02d540050051000040411501c104d64016 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 147365908 1250 147364658 147364661
    0x15020616051612120e01150f15050a0c0209040605100609060912030c020603040605150604080c210109150606050f0304080f0d06090f0507030b010f0e040603021504090b100509010f0201 81
    0x2800440078000300031040445c405140602a0016000da110b100d03510041041007000706850102c80840800402c02400d01105035426002055850107019101d40040c0241e180c4009451040340306000004451500704c865038070f05400c5401030f1041003804003080c0200da80014010040e03800c1040b2035907072040c00c0d25040300c014400c104000e41104000c02400100002c64001c503010784405d103021440816040c05110560185124030348159218a03110700312410001508416005001e03406c021025000302c0d01070a4030010309049035918480e2100c00b0040c010741c420306c00a0151450a81d24040100000203401d0201500182c10206c0000d21501800b2000c0104d03059030300d000780140009a56000340d400108010603207400e80754105400145c50510901c00c280178840140c440b54211411500c0441d00007245050154104e55603582c0032001d80d480c1d210140640103c1d080b90365036582071032100410b8a1240f008a07008400081100308481d03002001d40300b14041c280303400c8e80340080c9207038200d0 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 147367158 1250 147365908 147365927
    0xa0b132117070609030809120f070b0a0905070807080c0405100e25050301080c0a0503030409090f08181f020307300f020c0915090405030415020616051612 68
    0x20040b5142034074201c10160415140751107007a00005a0301081c1c2038451480961044170b271400e50540040040600040717010300350355000715031604001240765075982d0b45840c03c0300a40005030584e000740c800300302c0604d007041200c0707603030700240c0d0203120b1800c00300c030319071501180760003132001c0c9003940000902048805503041131010f42751101160303059403810000d00310754020300410310140101814008181040640344017245e2028004516003450f0002c008000c05006500b1500c4070103d41441d400f00715200007030609000080c0605d03400010b0b0004000941000b074076030070030800381840aa0030007130300481940c5034550060b18081210880310b00b0312a103864000c9010304604580116614260360041101c072a50324107400712605401054104900310000b245c0030b01e103201d120107240310350341030101c80150024481ea0881c1d0409440e001104101003c200b0a000181c1c4124200314080350452903036006c58800d41025891b080055503002405180c4403000f400950361456641402c912500005 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 147368408 1250 147367158 147367163
    0x1a090601200313060801080a050606090901090f110a081f0903030b0301091b0b0f070615030209150307060509130b1f05070b070f020a1506050a0b13211707 68
    0x129540c11080f5004500c0e10040d0081e400042ca005001188100000a106e401260800b000b45610340d250810000c06600c000c003601c00e15520381d480000010440080d00b000380d031083c412400612008000e0001911407984032120355809070041040d5084008400401905503c2010444201e2801c0c00d80191044070321094056182c07602c40b1003404181455442c010b0304501c18505004da84442c40c480a01469924100d901020802c0c00d00092071544001c607070b00701d01303071402d00c01c00c0d41c82e000a2103958003120b441003815490544101d242c40c00340310920240c8210300b40641816101804184410441c2015903c02da50b02c4090007610ba0381c044a00f030145c142e110205240d0703000c0c00402410f80e009010100c516008020104903080e008070821620903802e50f005001c4002d0f99203862548440140440e04403aa4844020a00e030711443e05040103820381d420420303a14109d840312410750301c0182c0e0000f00b0345500c01c0c2920309040c00c000f40c490f1034590003000c0c03100b40c1c010540341c01c1c00911858000 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 147369658 1250 147368408 147368413
    0x11203031407050705060c04053106060503180601030807290a1a09041e030908030403060902100201060501090b0703050d050f070f0f020303070807020f010e010209041a09060120 78
    0x100521190f00c10010200c0501c604c0a6503441e40307c8004210860083d400382660140540140000d041e99a141103240340c180307807041010705001100f410303044461355082030000030000801c20440354000c42d0b4001982d0101c0c1c000301100c4d032440d1036800140c0500c01c0d004107004c0080d00100040e0303403c404e501328198040c2c4c80354000c1e400c4c540c48817001400b94501c440d00011010550201c10f00c1c0118041e4801c5410681e04080d04d0020704040301780b00c0300c6140c218240714290350301033511041040500301440c810b040020307001245004100904200c544c0311011607040113414030a90b64045c0c2d28108540b20004502c1d25544649803d40f070300c0c0500b5403000034452400301008600191a0440da002e14080c2e01e410f40000360380c0c441103441020303a0314031101583c800c10100b01105d201da602154007202c1c81c03054403841d0058804075230030f6030b00141d08080c840e0340100700500d4510b0188208071061a0141b10341d03031049100d6022406504001380780506000c8940e0702c92555000e4540e00b40c00c0f0240a005 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 147370908 1250 147369658 147369661
    0x406170606120106020d170103020906040e25090e030a0e121f06030c0f06020d0c02011106090109030305150310020702030102250b1302180c041a0c061e0112030314 72
    0x90007586c41200d070410200091a1100ca201507451640155050301c0d00589400c080f0b03925402800b02920300c0100c04459403254654492401169900607241e41141c0c1403200046441c01c54100c040da48640c8494485401c20000340c68000e4010004403020701090701c640c03040200444084e0700b41400c0440034600e00a0b440101d9144100641c400026a8803c000d014125921608201029480350041a01513030146d000c0c001181e005403000300d8040c0c13051616031080c9100d0b55010303040c01010760b103180090703459090860405030503015080d40f1048410118000d4442e00c000a60350300c906070850415194009981c1065450a404664002140c400410b44080b070300400301d030710134080850640d201c1d54a00045004105a1102180290b230010001072a000b40300040c2d161b400d0000e012650050401c10000662040900900e42c0d1103d416040541b0303941501d10f807504182005252848000d0154607078003183d0860003926065480a02540811001c10b2500340c00901c910708144440c000f9100 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 147372158 1250 147370908 147370919
    0xf0a0801060806120d080c251502040302130906110409021305100203070f050f06160201050109091a13150e1c081803040f0f050414090705060c010b06040e04120504061706061201 78
    0x40e030300219101d043d001207001c80541c518412400bc07030000a5000e60490458519042c10780c120032110b0303014a200140c2c030f001c48403408040703600c030341d2014450b60f0700402d03080305400419120200030403081e0781601c40d44107103500094507440390301c0f40105100c00f06c0081d0420b0000030009100c4400ee031408407501c6007403401e00c403403030f4101d40101c80340150301b480000301d1456401e00a5486040c0c0c0300180c00310a9060054100c5100801043c1c041c14254100080010402a0380d50780304054000340000380303520450415a04000040d480f10495100c0040350200c5a603100001551050365288c0c2007202c2917001c1e942c1c90452017943d2042c00d5100b40158007280540c020423014040780da04403020046001d6094032413100348001c891117000ca811070481040507040140040210440b014000100e8116101c0010340580081d00201c0146c00c00c4da00308801c1161142d004545070b404d5050540c106843d280d0002d0001000c04c020800003580400890219145c0c2820788150b101140111280c03580c603032 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 147373408 1250 147372158 147372217
    0x3040e010b13140a03110f030d030f2307081003050609071508100b0913050903090301060b3103060905010c09090c230f0a0801060806120d080c 63
    0xc01c000402c04060102c00208031005108256a601c030107440305a40600d0342c0c64400d400c0440390461a003001c210f1050800d44da409000440e0181e08076100000d41c03170082c075075440c00c484094544641c0c040202d40a4002120030654045d1300482d6894030490a50707410030380015500300780c0d2005002d48541024800e41d1003001c28000c060f2100c83c0e6400d10b000e4206081140e02107822750b4802c250490f980002e05c25440b40344010025441301800d03801821007451a9070741200da00700c83c2c54440c1e81020a1082c0146804e01540d4010522070111b11b0074052480145030038405110401800f00300e071041b252080c02c201e060700d40000e5820540400c40003c00b424128042c00c0302031440400180746030004107182c1c0c2944502080c41a41c4c2e5503c81e41d0140160080b00003100c408618480c0ca641881550350845d4604010a43c0f0111940d0f6908154500000a058188050101da201d0103c403c920360a00400040365101c807010741c43e00002c42e46840e04208641c0c800d203540003000510750200a06c8041c081d = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 147374658 1250 147373408 147373417
    0xe0103060203160c0807030c0507050604090e0c091b280507020117010f1404020f070305040306050109060e0f040f0203010f0e060a06060206070c0501020d0204030c0603050603010c050f0a0203040e010b 88
    0x1000c200c40340078a041c0700440705800c04120040c0348071402d01010300071900c034500203811075100304111032800707442f100050f00341e030080e50001c0940307034584421042d200300c02d1000d214103040540381041305040c4010300b01000400a081101d02040108880c2c078070041c1d00c01413036040c071803500c3e010302014500040245a84d0190364242d011628014002041c01e803406000d50494020100391029213003088980115504100c110a510035024014a40f20901942c01441d0709440384c0c85040da40e51451a0140a0701e6059008040c41480c003c4100280c4441640d0640d008007080380440c001d82d41c41c54500c0d070855141d007000c0e42541c6022290545c0440b075910040c201c058580494280d56160040401642c880303028100060f00603001103401a4010000c6419640c0f01ea80054149140181c21a0490f00140e0040d02c00e100c000c0340400403560948100781e003059003600203200e0700d030540e0800341c20780c81200c8600c0790059000034024180c0740309005960151081041075801075035105029900d9412 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 147375908 1250 147374658 147374671
    0x2102040e060f010806130905070503030c03031b04050604090e150c030106120b060a030c0c08030405070f08011a1302040e04050c030d051306050f0c15010810020703080c03040c0e0103060203 83
    0x120550300b85031640c0900c04207403282c42d0040c03120000b044154080d001900d90110704a40ca481808008103480e58180040d200c1d0a15041c0155141d03e0806419503001004940903004d15400304014099516500221001c0da4519140400d801689482692800703540c5501d100d21208d0400500c068a00c0d420001d504850143d6030305141100d81d92505421100c640c50240e40c403120400584a405000f5004241c02c3e0300a814032003840b903965280d00400d94811034003180d0541042405200d04c540f007840c020702030f1847c1c40c000c101c1c6100030169045400c0e03040c80928800d00c62441c07a00615465901101c020f8401c2c044c04490318285840c1140d600e81055003036034401d02845055540301c85c4101c003521700e86440d071951061140d19000090b10749621070740fa00c00300111f040100b404110004c00412101100c0744018840f2589400b0029040803d82404019141e004210040c0070941c040310713440e00102401d82d507640d40d448620f0000c910020591140c00440f021000001c00d00c44180d001c1d501c10358 = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 147377158 1250 147375908 147375919
    0x41b1205150a1811041103040305030702150f0a420b0909070c08160317010e07050414030c0901030318050301090804090b0d02090112170c0606012102040e06 69
    0x32242c40b011002d40e80390801003800d0a0720541041d011408419026100b400c011744002003098208041e84540da00c03c55040e804940d0020910079500d504010004400806401001103400c00749000c0302041d038007400d40f81d159512003010500d40740c400546140002003001c0030840003000c04e03c1e10110321281c2c040d580d84851862100090081000301200e2032008000d2146415580e454400d43e440d511403601034810080611102d8224054081146001c501a4980c641e180e1007066140100d610160010b00300382c1103460071304c10801c0d0848260b0301035480c5000c034907072038148034008286410300c10585164040c1244000109150301310301144180ca011554148030f00703448600349030980b049071100508240040004020400c980e40c01190f06000040c1113401c100204e03000101490b8080e00026610021741001380c1c00c0261011242c908140b40e1403860303080c00e0958018507101e0700020140f40c1400301c44d10055915000c200c0310b4032400c25032034008544494454030300c032a12010480c1c80f5401403 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 147378408 1250 147377158 147377161
    0x30a150806130312180c0305011a0f0427210504050d1e020307030602040611060609042a0b070c0819110a030c14091e041b120515 57
    0xc40c00420001e11682000d1018031245001c0c0d502125060440d00c001141a83c0c1c400a80007808010311301c111107a402002040c4205040d41001c07400c40b21031034010040c4601c0c00d08140542d444080701649060b504580001d808a42078045d0202c8c401641f60f07804030340003031790074030010080030144d030701d4a45400c844100d00180040a05541a2256001c1c01c4e911114140100c80020070142c1c00d6041c141841d20340d03080c003040075170210f49014440e4100302c4000ea0045400d001e45540300c0c15041c410620000200b030541000c030700bc43c0d4860000b51000d021000b613402c2c10070241c1800484040019600ca80300034000f41d42d50788841e0290017070102166019450000002e0000f00000e132505403420007074160b0902e40b507540d280000305454211720b03a00a89894400004140c800b64144010042e410040c07103002c0c00e00003003204010000b440013854110007092400e8a68002410719845580055422891088441c0081d00350f42640c0c4184424080e10400c1401c00c4808101140340301a002c8059407039 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 147379658 1250 147378408 147378419
    0x1204030507050105030108100f0f3305090a050402010c0b0906010e01050402030403023d0204140a150e010215040f02040e010203010b07110a030b1807060206060d0f17030a15 76
    0x1244421f2003030f044107602001e050198003140d030b80207a88940288100045101120790141c045e21801e11910f1540c600c0350b1450b0040000900c1e6004004000035212018030f41004002030f49100d000d8114041c05d0390303d00004045901440c14a00d5064000326080002e10b0141040c60f0b566000340600d228028504d03000107410304050081d68003c0d64150080c2505c0d10102e9444200042d00ea1071034255014850000c0c43c000c10210f030750b04400708000700050307079480c00e00c2c0b00c1c0f140520f20b01807050300503d6200020031820b003c100b0384004029241c5011001981c1800041307280c8007482d01207000c08140042404100f150f00244440b5292007903170148104c44000c0c0d0828203d0009105001404404101e030b40c0005800b030581d024100d00080c0302c1c04969480341c0b1014103020040b40e05810b025024001c1c0c0d405842c00304410001421544000c090600d010004540d03100b04042005059402d5440d4020400500007209030484590112507038a07440d220141401030080c041d9081030481c80510007041 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 147380908 1250 147379658 147379667
    0x2031009060312121b1d06032e0501081902190302120a060e0106050c01060801020f22080703031407020904051e1204060c1b0b130b0304020f10030b0312040305070501 73
    0x1184200d07081103032400381d0040001c0d06c614884800071006070110780e90681182d87da202c05107001e80c820b481031880b0b0800300c0451b03280700790100c00d12070107100d840c0e181080660707400903080c0d07880119801c950030180118140e0780003a020308900820303512050403020712819403560145c103142003950000001074654280e072804644290158444200414006011250107100203080a0f000800009a216519086503003203800c070081d44003411800003007420014101c041540c25101442c04410240c51030084529a40c00d10340c480201070006a04000e1210190386058a00c059000361050306185804c0c9010707510b0703400640410080c00300e80340d03d2807c2d14000260300360348680703100542e40c5002d080c501c00b69a01c500c07980c01220504e20f0080c0b0401c1520500f0013190062060b80c030040c0c0c9030000308402144c4400140c020a04640c818810080585d884504a50040031306031203920504100c20002c078060030324009955014842d800c22481309650640080044a001c0d80540d110310380c640c5d00440303 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 147382158 1250 147380908 147380921
    0x30c1e0f030f0a0e04150611030f0316081b090904030504151206080c010215060a0f0605040e01060509011209050309190f0503030909190b0d03112107060203100906031212 75
    0x30506400c40b006007c094016108103212070550300440307040c5200d4091816940d48200c1c1c880b80043d019000054009400c2420583c0101a1141c6440381c07859000901ca01c501409001c41d109208140c00b15090601913001c6402030621104994040d00d0030036000781c140e00008444001c0245068000602c800020400e0740120354140d000e400141c0d030740300e440c039022070009c0c3c0182da1000c014a400254012140016001451140c558a40300e51070008000c92170340059001c501841800c1180700380607032340080c4485160164031000980b1100c1401e0035440d6005558000ba0060011030f400c907020b40e0f00030280000c94100030b2a40c084581c4850615441e406105083c9810096003004070708500b015160f03508000580500000380305003c480023400a91030114140d000c10b283c01c0b42c4000c4990103103c05189a504007030a940f20842015191105210744d44c4082c081d0369001c404a80014643c5158400402e03231100c0602080d030300c03820109a5402049269008590307402c07c0b440e0700c41810700414 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 147383408 1250 147382158 147382181
    0x20d020705011b080909040f03020d080412080a110307050c0c10020d121401030b041b03020a050402071502031f14060d0c0e090c0d0b03030c1e0f030f0a0e04 69
    0x20840b480c40d1851042411481d101c04c9503c140c00340503800350f94440144191145015444c1184007003503600700a0700781210340849401f0440600b04100100d4070643c0600035640103441c200e03a10756070b01d04081c1d0041c0301c910a50300850700000180300f02d11758440c02804400c4800020346d4030a84100c81042030402d00500d0340d1000d0380046038202800790040e00d800c400210311090116104d007215285401c00340d001d82044a0001d501010312042c820826959002d401c0a51542d00c145400e680000d404501d140c800d462240750001407034000c004c580000f1030314031404078030103544904007145180800038000c55169000d40c0c0d4002c000404403204110030310b0740b03039000d000320b85001d002002d180050420303503054400b0302c1000c1a000c400b07500c4102401d03206040040c41c43d038a41e0100c1c45480250750020806d180302e9071082c04011961000407a0300309451910030f610b01d100032182d4001d42d0034a4070480c030b010f10321f02000c41c1c00c1003c5000070f4003c2c044490701d55039201410900c20100421241b02c0ca200 = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 147384658 1250 147383408 147383417
    0x150605100c052503060f0522020a0314030d090b06010f05040b0913020f0d0b0f0102010b0609041d0703061b05071e0507050d081b010b09040b0403170c0a020d02070501 73
    0x281d1140786550010303d10311004580c08041c41e0703100e449040c15520403000034440c007a03407181040803e00040d004242411300203084c80302100e0071074000a611203103602014005c100b10201c106210b100400844a61905404050100d01c1403400e000307006101c00c441d9240490f00724010540c00a210700121010303544460307141d074103050302d490078841806182c160034100581e0030081e8040183c480c00207841404454000880e800302e0240c00d20201904c8602014156170503d80c0304960fa903100d1064804030720b020f82c1c0009022210050340304040004988502090040003008018026207401030480000410841018409480f4088429100780b0030080c02e51846125019201d801c1c0030101c41c5107030300035000c8881d40c03038403100061500c0c1c1808000f181c1c2e54000290058103045107004d6049601e44400080104c0d004076408122584002400145000b038080d000070200f500500d0044910f6150f80d00d6500203140c90109407407258020300303094025100307030340b0480042c910026115069a806948 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 147385908 1250 147384658 147384673
    0xf020c070e0703021b030c07150906080a06030b071e020a0c290301090204140d03091e08030a032309070b1b15100e040206030105010c0201020109150605100c05 70
    0xd1180150303002a0521003010340070801100301c0c1c0d80410010917084158000385544560051150b03181c8110355100e00707059021a2103040741c06802c400244119545070604014556407084904014a02500010003032141c2c1d1003400350381d40d44401003030421035508010080407010824140c9e9130f00c1802c4001090342521a00c20701168941403100c4418108030540541c403a01c0a004441e0160426009401d186034040b4042010b11450040c083d000b51054559000781850382d00c00904003516070054205403080c0c84e000300076540c003c0c070065000b42200e4003500d03160402e050b8018003401e50b03c14031150f55055034035040c04d03070035050361020f00408141c4000c1c14240d28024150410b5003241520f282c12112281c54410f04843c24040503040349408030070480c9a1503c1c4084102050403500041c483d4043d0904120050700c500b411281901c10900304202040c3c1e00e440100d01408010f80001e15000261561081a54007a0821426150200d412001788108044111842e10420901a140d90310115 = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 147387158 1250 147385908 147385919
    0x2030f0411120a080910051303061d0304060305060f01080f310b04050105010609080d08130f0609030e03030a09050f030f0303090303150d050a020f01200609010f020c07 74
    0x74900d44140801400380078285000000300d0382400d20600040c3c41c091000100c2200500e000101000b0426060a006042103006a00c140800340c45000082160b55504504d01281c0c510307100b104d01c1640700c00d080703d40c1d45803202c800801500040d60070340d02030320516210b481158003440000d84941044250041c5075039807695202c41944030404080c14803c07000d00703084480116a860081d0f0103000b03d14450042c1010324101c0e08681050b80003d0400400040c180725000021071103501d00300041c9400304c0903490300d20040708001c00c1800700900c4030308221054000c0090607000700c6034450003a103d110150b003094041c1a12031080402c1040081c507030300018006850f1010640c1026039000d0104c5245c4aa5016654070350346c01982d03d02c1d00d030760001c010000350a0340d817030001c0c861003410b440b169140c0c0026034580b070365640740b0315009124407644c40140304181d102c0c1d04046400040c500300802c0685c42601042d0300d40a0560700034680c0d5003024020154030a840c0200d8650042a00040040702c1c54071 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 147388408 1250 147387158 147387173
    0x90102150402060702190b0a08060a06030603030f030213091b030507030501050604090e010f0903020a0b0c0702090a020a1812020a120b070f02121201080c090103080912011d01061802030f04 83
    0xc1007404086e5900c20780c003240844c40c2c28081c148614103034179100c640d41050b0b0104a0400c04036030105081500b003400c1840020341c8214103082c0b41c2400d06025072a0118000303c0e81d03040300030790001d802040c40d095081507858101a005400d1440340c1e00e003001b40391100031085060300d000f4001c0340d8105500304800c0200700f4044d0700c043d400719440000045d400c42c0310180c1d80281c589941c0143d0059002c07062200134081500401e907000015000b01625081031a4041503111800030400415240e011444402090241d1598041c40c10300c0c00341112000d40f07458003040fa0b1300d100034040c3c2c01015802d0340403828481c1c081010741e99a03005055800e040d0380b4031004585008040255004601070341d0100211411401e01902c07d050501f0400092503041c038070254903010ba026411b41c42652220010804920350340100da4034442c0c103403142504480c0e04007c1502504698462034460b69004101041604041d804007054030440210300304000c00000c004e0003607000503220720b00c1c19443d0030003260015510 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 147389658 1250 147388408 147388429
    0x5390622020d1703010302090906010815040302160603061409061e03150a0c03140f010302040c141305090c0a02070902030414010504150506270402010c0c0b090102150402060702 78
    0x1040d09034401083d540d4940641d40000a800380710f08040300600451a0112146500c0250000245010743c035010780d10b82c1d10007030f059608519030403030004282072620a100c400c40c2503070030320380c0301259035914000100200400c0c0302e040c040c4400074840705101c0c13500409050050f8001030800c802e80082c2d2011740c030b400040700b8003213502d4464249210800104020034a204119207180001d8a80c10020044d05071a24a04154094954442001800c4000d4820141903036016680001c05181a46083e07801a030b400c0a064000c1001058610303031000710703480040941e002507a4281140c0c540f29146800d60290308002c0340560402e07841840700300c5c000c0c3e000e55030003030190004460848400e0700180c216031081c0c03401d590644041c0c07007900d080052805043e4000e48203540030030041540040149448161402c000303010314012000c1000e580c0b14000c0a064070ba040007611503060790b00c210445240d03011700605400740c0039443c0320070950040480c40307911a0360050b01c4285406010f5013000a001d02 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 147390908 1250 147389658 147389663
    0x7020c030604030905100504030201081602100f0920060d18020d0f0210081603090f020405090f100911060a091e0e06040507020c060a05390622 63
    0x25040100600d940c10001c60b4020340c0a61030ba01c40640c18032040c000d000650002c80d5007806010002000140d0384143e80550114001581c003150050311038041381028024034510f0034507030a0200c0b01714030603c55800050864030503001c40b400c40c1c00d260340d036440c3d100310004d076280d01520520012908501d95042210880654000381d50182c0c200d600080452041b060107450408032407180c0c80c110708010615600c10b82c03860621110514118900310310044881d025101019151802e00c8100990804801c082c3e560081c0148602d01d80102d0701030b85c0d1039408903801c03000d00c14010310a80f4000c603442400200303a0001070b0010400826000d0207103560092a00d00c0400c540c4042c009025944401c071108039110044084030020328042c80f000e0390030310180205200d24036100c180040645c00150742204c185041c3c44982d00c5640c0340205468a0040368054206031b0141a001540500b2908800c000c544480e403500e61281c4800007038a42c0c500007190420300001024481c1042503d098040240491 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 147392158 1250 147390908 147390913
    0xa0209130c09020711090411041802040207080901121a0108090a1505190612020f0a03060f020301050108181b13060806220b0403050d020f07052a0d0b0702 68
    0x4030180d44600e00c01c00250300c0046803d901203403110810203040d044044928045440ba030541c1044e45401403c6001100c0032480707981c4d1696a07982002034402ea24400d29001802151500303d141402d641c41d074461410640010340610070408540c4140c810f0b03000000850700e100700e680c1d40700c00040d621844007030039504161091403100b0002641c100811441aa04504085514104020f403250000304032f25509a009040083c180401551000c03000f140c0c0c0d40480303000f000000040c0114030100030b241c1015080f9420311802540c414104e4000714120352083c3d0b100352155541c800700c41c0e10319203551000703134050704044030120060301082022081100010280e403043d44500315010201c40542c0c0c04160160021000c0040001c6100440807541030313951002c011440c0300390380381c0c8108070000340000c0600c500032548180514040d4103a92150a01c00fa030142d40c2c07019420722607580c2001c464100380d82c2c4908030356000480c2d01080250040e80014181c00400c030410b559203d101040200b00e10210b1 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 147393408 1250 147392158 147392191
    0x9010f0c0b04170702091f15211806020a09090203060609010f050c07031113050c0313030207050a030b0406050c091c05150103080c010c0206060609060a0909060b04050f0a03050a0209 80
    0x10781c0d41d070380103c1c010b140d1107652211f00500e0500700c07200e0141c2944846080245143d41580780e98100014420601c3c040007000c90b181c50152422005041d102c018044070341c4000e8074102044442d80c020300c248020345e11a03040869980759550140d21040715015000901031160150a50003510306404801c80c50402600b00446c5c04491448d001e16a4030035a040030840c0940280c03401c000d910f420803008025403c0c0028134110801d050240b001030250800356864038407100a01d8824081280600740042c02c101c541903680c2800003078941c041c2c0d01500c1c92890540407903241d503034910450f03680076005011103101e84003143c188100021155000c0e02e40703010b0b00c8041100d055408403014040c42c8140340450715000d20002c6e2070f08590f140030360b070419075102c0b4050101300e55035603040d80c03c40d103811180d04d969a00088003c41e01450241d10107201c4a0400102240c48040640a44290740d825281240380d40a030004110682c40b917844080c046820500100c0d0241c00c0a0502d0f40c0e00c58500000c1c407445 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 147394658 1250 147393408 147393413
    0x11060717072007030c051c0f080405030604030e03011d12090d0b04080a020d0305060a05060904091403030a0b091512030c0a1506060e090a051503060103060209010f0c0b041707 77
    0x20350200542c5030346a0400c3e401401001483c414180c06081c007514014411700030103070f5151401001d01c002a158403038104c0c4110802c6010740444000e00409400d0b6602070606141c05010400e509400510030b509100d0100d88510300c44298a100007511070003010445440e40c4d80c10318540c004206982c1202d981c0d420f0f10045003c0c00d00d641c0c0904c5c81a40c4190780c8803880b0300003e0400e4810901e130030415083c0030602030195030380c12401c02961001c940c032079644c50300b410024000340052180244205914076440c1d00141340440514461001c4800030f01c0011070703d40402084400c08c03500380e5071131909200c0c010198200004052051b005040442c1d04d007505440a007481d09402c1c15040b6076203a8122200e00600b0540d000740b900a007030a0401100d2150f1801c00500100c3d0028450f40c08190743d500000c803001c05c4454500215000603065480958480c20000e000e58041105c01c2d000c0781a4041c0340c1903091041001c004410340012500c4501d0301c40740e403109102c3c0d09481214001174403c2c01140d01 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 147395908 1250 147394658 147394697
    0x110a0f061d0a0b0105210604060f020714011d0313090207020d0c080c041b120504020f100203030a05100f0317120a0f06090606020a031b0b010608071106071707 70
    0x90b8940142a900401d624100811103400070b04504044c07201c0801c1c000c96001d201c00981a07030003035840307040030501891090001c0024021000301500c00e1341d50400d030041000e01940b225200740c044a050601000f010084e0319600d204103d6241000544c1e0300e41040400480e5002e461218802803181c020511140c9840040c45210f800c1141150080d090104e0359140038458502000c0180b41d804181400200000d0103a01d61340600c001b56a448800090855488605112003a0001400c100c280d5444030b1009560350002c50b01a409103151102040301c0040003c420b400316440c5560741c5a10b1400c0d0381c1c1c0c2c60060740e01107003060b401030b60030f2180c5c41c185850b44400611803204804000744200d800c0c2c05600560300141d1000b1003407482d000301881007e41c042140101c1c6c54149c1495004a002e10040800c14902c03440090003070030740781002080b070a9100c640c0070702420350f5940d2444440e082101c026110341c0140c607410040f8600349010f1a030341648160655100c8850304000c00c4a21060740c0204 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 147397158 1250 147395908 147395923
    0xa110c040e06181906020a0c050f01060608090c0a030f06020d02031602010c030b0f151902011509050705030708070e090711100b0d1707170a110a0f061d 67
    0x91a03a040340b401c01a00d950700740a1100c00b40c89001c01400703c2200d58248030001401520081d050b141c0000f00003a076180100c1d00c0310a40c039400303022240d4040c0c1021510303000308003501440002070031800c04144040c00c0010407911044005100d0f1900d1403440d90341c40380901d41c4040480310140c080c00220080358140c4040d622458089210451900c10128000d085404840c0c3d80c2040c58940b914400740d42c2c981216080c42c1000c141c50b003000070940f0138404480d1340a083d0500d4503100900759506a51541904801c00000040596161040e1503031000000d807041100c400b00060400d100245201c0d10a80c0c203d500040c450070308180e44a200c40110700d682c5400c55080021582c441160032041d00200280b10098026280800c1000c0c1d540c800102030030b020316000750511140c0c4a20156a0517100c04030f031010f139406800400a0b01410a448209400290840303000c9445202031100784140852101d2500d6802079617103202d80704940d2950001c2041c440c0d8641c080e00420500a00703003004001c0304 = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 147398408 1250 147397158 147397181
    0x1501030506061008190e01090516050a0e070e040f090b10060810120f020f0a0608060a0909020108060d06150f080c04090c09050403020a061109030709020a02030a110c04 74
    0x605032840d000007400005103800c50320b43c0c100034045042004650590206044840c060b2001050481550b08102d01409007600054424066415404405c813210043c03441124804d59030792100a5442005d060a02d408980000104a02d031403032a80500d0150700640c2030240ca4040002d034048141c60300d4414050803158040d904902e20390601030a604244915402204c1c0503502440c41d040c40800d86d59140d4040009101e00000001901159101d4002014480c00a00407941295413030f01d0060ae50340041d61000d01541c20244045024bd205000b000006501078480ea001601c8200c1444618290b101040d640e80e0380d50344580e10b0300d0081106480045c41e0010004070400c1c180591039080920820f072140c81a460203070100f00062400000c1822915111000101c540d16418144e007000c0c048030000f080545021001c5001c0240c1300082c0200040980843d080291140131070001c82c802c0d101490f01503030050250043d82c6218214054007401001d094880780d0004d1000715003907800f804c500 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 147399658 1250 147398408 147398413
    0x71701090c02160503210c0f0a12021b0d020f0402030c0706240605070c090c090905070807090504020a0507021002060601081006050a12090f2d080f090315010305 71
    0x507120140da040105010341101408142c00d41071a01c00002e5031540003030450f804901049090111044841d403c0d110154842400c0c0d407403488440c0e0605403691145441100c0703480350a8243e10110b44001099403c00d8010b909544600f0710480401c09641d1410104a0340107450b441d1003006030f201c6e8000341d4000c1c1200300a280d142c020f43d1500d441900c0c41590642d26082030941b0f001520b441d048031a100b1680c0c68142146d440d90a070811030328221007078015401580c241100840015403107020901240c45400c000c00031510303407a204581c00c036010f550400001342c1d01d50342480315150070b500518404205041440c9010b0080e40803458007407155801c040941c00c0401040302950b00408001da02032500d2407001e84e65428620081c180f80640c80e400c608001c803407503410640d94035680c004102c4c16001040c804e081480c610340801240307400201e03040c40080410300c1520b0608200501ca5210364025251828283d03110322040e0b41d82c201c0d090315645403203512040007440344461480740c041c602a001 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 147400908 1250 147399658 147399671
    0x18011b0306080c03030a032c0706080106020c10050c010e0618010b0913030e180f090c0105090a0902030405070509101a0f072612010e010603020c0d0807170109 70
    0x903080703031190303803140301c0310340124580800030b6030048115408034000c3d040009014908074030f080d8480000014203981d4213100c4945401502c4002a5802190101d6031507070626030301c5401c200e03140c1d400500e005803c101e204407645203050080001d4120b0000c59400041c400034084011072070098103451002308406080300900f020340c4280a01281040c003503480200d42d003064810640c04104002015040040d080c042030480e81d80d02c1c038006020340c1b01c40302c1c480040c10318040d12800d030041a5030b681c80a10070b00c4c804007001d501a805036808001c00404d00d14100f03103011303d0b01010f9070000348110341c10f000321301c030218595070351000803030003510303e02445000e150500c0e942c50310b282c50002c1854150007050000500890155007140d003c82d030b0101a03500c07220443c016030840601400da101c0c010071008210410704c41d881e201c04a0483d1301043c05610580d0340c58100343c0481c483e28a80c2545500305e88020f002050240c00c0c0d19800088915140001442180b90000034200a0f040704840ca5150f02 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 147402158 1250 147400908 147400961
    0x5010b010c050304030b0c1e0306030f06130f06020d060807090b01050306090105040902030a06020a050904180507032307060302030402010221090d141501260c091801 73
    0x411112049000c1c2041201500d00b51192a40c9024622000705007044603000500c56404800a4400c4401c140b03402c002d01c034002540c00c500a03001101e04500a204820310340404010000d8014040c4803440c008641c9009580c80e41c58102c0010a0f05a800503000c0040300040c0101f4810075004003603440240052034201084d120070351360b280764564100720051040c001d280d0f451040d0141100e030308582c0002c11000d50700c0400d04041955101401240c40072906049070ba42010040c11441e6003107408000180c03007084c0c900e6842d10518406070a907030101c201440040c040150038111054032411100c10248034414142c5410000e400c19800281c010081c0411542c0400a8205841225040c0c0c001d22401390941e402e540030303014285219510890605050000c041b0001c508a60841e051b074914100d400c041400c0c6800a1203072003503100c42040c131603232188003007031085000d40720b0b142c068203e01c3d2a80041114190028105010340e01040fa540d07001c0d080240300c0c0f800e1481e06405007034400410034 = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 147403408 1250 147402158 147402161
    0x304081e07080f061503100903110106060903080901081f08010f0c0c12050f070204180317040f031d10031505120304051005071a0a0b0103020a0e090402040f0c0503040501 75
    0x30352208400d43d001540c180290388000c9030555105a01c504098912004540040d01d01004003100d1035620b45009a40001c0c0b5501c844060780c4070b1010f80081c0500c075514101101d20135038900c405061a007003800802510361090b650190448021940d0340c1c46110010003103402541664400d0049079520b0b0194246940c44d030007a504a06003038180555000801c0e02ea0350019018101d644040010005641041880ea10169051190007610070400f45542c000703078003407200c0301c1001a03000c64044c091001202100303401040c800d50307016490701d110114a903810355090300d0341c05854158a040d0820401903480b05d501c81e0070b40401c282d4012921b80180d10b403890b00403065030496405a100c640c1e030030029110010490381200d1080c0c45400c201100c5440031503290284103401071003401d0f0400d2150320b049441c6420b44c00b800d1b25403020000e0100c07840054040b8400c104081c8040742039000c400c401d030b02d002101c0950207400a4404141144910005011968040302070004100007000b07000a01809 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 147404658 1250 147403408 147403423
    0x70905061e010503160203190c1b0b1606140a051005030705061c09051911180a0b01030902190e0109020f040b03070311040311010305090c0603010b0901020304081e 72
    0x50070588104a0907141c002445480000c2c081d400200d07031038070b0107030020b4420070485200c4a0030301141c0314110140c000c01031038140b4a0744140c40300780116040400116083c00d0b41c1044a2240142925040420070401c041c403624000607034403950303220100c4078030070a9150036601c500c4440e80c1c0040c1c0ea29041c0b00440741c08180740c000c02d001e03602040c01880541c079500e00302da011b802030003040b070080b10001012002070500000010194050680310700e10b0001800c004c45032a0744518401c3c0107248651083c0302c5000b841200d45d240c0980c0f0080410640d980d5035211f60b5180314185008511020641c001c83da000f100d070302c100c2c5609024101d00300700150f2100c01c1240500a0110306509c2c02c2c1528059098900036401160030000000000c5a0003500075803221062444504d00740e6103907540c2c0d0419030801c4524511090200381001d0008858402c041480070b103c020081c1300600f1039080000310400c64100c1078041d41503100401010811400c100299039103400c982d107004c00c10909060b142c0d0b003170002 = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 147405908 1250 147404658 147404689
    0x904050901090203030306041503080a09060206012102040c0314040c181e05072003031b270121050105011e0207360506010f0e010c061d07090506 64
    0x50403070000b00595000c03007140c0d040350080320040f5001c4610f80c24070b40412115840207180390f900183d80600640c000383c4540c00c0b00c42d20307000d07500103070f076104004071515030840c2d0300d003212603002c01100c0c0051501d0380c040300100046280c005201c4e550403180c1280e40000b56825100440b00302c804000d0700c5264110304084908184003448a41c4c071a25240e003000600341d105100403500c1c0c41c0001e80036442110032440071401e801c2030003140e480c500b02c0f068996100340d40c444030a8000013080c10031043c0301d100b12852804c8001c3c0110081c14006030303031100b43c070280c1c03c0281040742d0100101d41c0f40c0d20f0245482106603011318002219454100050148a00b10914607200030351440013903d4660040740c0041119540125611510301d800c45045400c094040c000e401c2105031482100c03849002d5000700d08c500400e032a500d021680548040c0e0f0030046650645000841946220f0005162030700322203600b8106480c904100301141f00e40608000c082d820038811541d80b60208259440c2240100617210f5 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 147407158 1250 147405908 147405911
    0xf0c01031112130c0803210402030a080d050103020a0e07020d0e0103020d0207030806090601140f0703030b100804050f06090c040b030a0602070f1502040605040b13030516030b010b0f0405010f0215010b0904050901 93
    0x803c8144020590b243d2950000b58115020300001c8c1991400e000c000240e55008100503542c00004004c0e00082c0000e000580c00303008040300215548041d0180c1500401c86a00182041c4081e840216002c040110781241019000d20503400400b0740390020b01081c502c01e4558281318500101808906800140928100003588102c01c0700c1107017407011940c070744580d01c042076036815160805601400a240d442c940110900c0c0d4603015043e849440140144d10a80540c1d01c044180b03003c195960105440c1c80345181c01050004201e445c0030b5100c0a1190703009070503110080000d84641e07049804c40e504c1951000030004401d03040020010304a59040440d590450420f414248000d01500031405a4110014009440b242c20340a01344064000c1d580002202c41d00b0b11001d500c144a40e0b1b4621040b926000b251001080854001080d140e00490410a60307007481c2c601801114400d01444488003540149000c50071101e4940201c94047c209400c9190355810030007040c00119400180b0205280c0d = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 147408408 1250 147407158 147407167
    0x8190b0a060302060f0d020702060412050f0d0905120c0301060617090a3c0c091a0913210207140111070311040e011d0105090f0c01031112130c0803 65
    0x603a144d005803003204910780d500a0700c403518004050300074483c0010195000754003040c005241c0581c080441d40c5203115209849492103030701480c039961010b0300351040c00b20303118800c10700c00c40c240b0240350faa40341141d000700c898005909000c6401c4812541051000070442003616000c420340120307072038100d141e64000b45102a111703141d140d0411030314120f005200e0030384058503141c039044540c5002c01c1c0c03000e03a100f0700c0303284040c1c6041ca0b01001c03680700f43c114a0381400e242d01c590a01000c0450003c00015081c50265074a04440391025019280304a440c3c05140c9800d50a880012120410203031840d00144050b600700400895200811000305040064440001d500c015001c2032943c11a5407254851b112840808002800340000e9041e0882039031070144400c0140d020320300c500580001403c000c11032621601e0741c0c1a01d0342818210038040340d0004a40000b994445c4c0e12544039407401c4003806062000910328250000020b803602c0c0440d282c0e0b01c0580c1c0070300c060003044000074480c3c84001e6142 = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 147409658 1250 147408408 147408413
    0x5060c070e0601050d1a130b0a17120309010606140403081803030408150123100503040309090504080705010c110c01050c01090501060b030901110702010e1908190b0a0603 75
    0xe4000500500010255500119015034065020b4030b81c0036000302d00a00003c100c80c07040c6a0400d100c00a00c511541081e480545000110310403c020848058102c800d03007810000c069400e00305c01400340290784202e0300021f44403040308020f140501c101c1800480c1c107510341140284000409401c204030a003080008200040c1240e0440f6030940013884081550300d410000203003540a80e50101105003d0030f040c28000c3d13020100c1c03a505030b4010010000c011043c0030007180714441a05c1c84d2503000300e80c9981004481d8015005107921034400c0c541609640c0d02ca10038141907500c00c2d1000c441c40390300412010100182801038062a1120340b400e04a9088000e01c0540e90305007034009507042c441c0c000b900f89c80260007900720390501a0044003d01045984004600c9a43c2c012101084a546015042c5c03da81200304115020f85030143c1d2003445540032082000211501074100b422451410303031001407070b40014030074901e588800c1e038441696174810342000c0c0080c440c000e08150040340b030030310180300 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 147410908 1250 147409658 147409663
    0xe070e0a0302011112030a0b01021c050708070c050310050a0c020a0b01170123090f0601050a03141e0d172205033108210a03020418140105060c 63
    0x880c2d4091900b0007640009000190074840481c0c0e42c600320803000402c1000082203a04007203500b000a0782240e5885440c0c44580c543d02d541180d040000a03000c005640101d45494050020103004039505288184d0301c6000905c1c20110740c2d00c0c6843d8585610420101507031620400e28804071900103040c4282e0325580d41c40355040305000d8850f44101841000421b0802540034040840c2c4880100c0b2403945070300c9002c03140c0c45085954070454458400302d13400b08840403800d03904a0340c1c00b82400c3c03d81421551186502100303c0c00310900d0303125994000500311015001e1504020428010701001140180020b00a8485e1080014852080c2c1c0c2440f6214004081d800c104080c0a0130003000d000d014a0060300350310420511550091710503604681c0450020b000e82e00c43c9904014091509030f681d0300c619110000b581141e050f910f0018000752015599500030003c40c580ca14006185c25180c401d08101c1c0c142000d44001965650f0640c400ba60100ba9400c5014250890342c5504000e070000e0500d5 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 147412158 1250 147410908 147410929
    0x509120a030233011712040815010501050703020606090a0b1e0f030106060e1201060e010605030106021018030311091503060a080609100f0b090a1b0503010803040e04020d02060c06010e070e 83
    0x40c00141384026913200c0701780611451100c20040040c003561180d030780003140c0c0c6d0361404c005541810070000780001820f40c01202195201c6605401600b00e55450004203c5014001800d007003589071150f0700d80c4015925860b07030f5038054108000d61400c034044e40c41070041c0d44d04100b250901903858900103001031a004000c5004100080750b40c84030020301c2c42e2942e0302406042c1d01a500145001002051a540003009141078400503400c65643c5180807009406407040c00c0321001d00d400c100d5159002181c400e40000003002901d00200740341011220115041c3c5056501c0d00116040110500200c0d2802040b003c00802d02800105183d0a120070103a4a07144403503601c00145a603030100300203000340d40d00200850b4200402180d118500600404041c0c01070445042ca15107506c5814a03607180103906881c1650a400c00031030074141880c0c14030b04d82c071402030410f99008565264880040c4d88050007440300c501c5080241999500d0400d1042d003004000d4241e80038400003800d01c0425440c1c100301c50 = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 147413408 1250 147412158 147412169
    0x1506041806090b15090604031a1503011401050d051e07050f04051612060b070b04061b080601051c110a0801060c031b030e0409050c030d1404060509120a03023301 71
    0x2c0341c0c0d9800c4000006d00034455540001c1410003546d09200004001913031840c403c800e44440405042003880415088840141c4074554582d0004014021824247c0e001c0303100511420440d01c4800c85400352304100e200300b05c041842584400018041c9003003801c01c00b25580d1703003910184111300300071410138a11381c1203808280822179030160109030401302c1c2d00114010004644040d0752800141818030741900d049034140c0c0c5050501005088503000000341034054002030303444035800d440310401181d1650007540b000044019440f40d5a000c04424440c02113101c0407081000c0e501d400c6148054800101603001c84103102c4a006003c000c40e4109041c880b10b80c60b00740c85c2c1480d0310020725040d01d0324507504403290740080c903200c0c402c000c01c040040c01d0000c000c030031011610aa84203210480b0307407130410441d03840c95150034082084000e010700d01034a10414020041d085400140304801e10709542104141e0059110009254111032009130306001d1030300310503595030703400b440c40c2d80b081c040a01071041 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 147414658 1250 147413408 147413449
    0x60f060e04021312031e02010207060b030a050705010e2419020d0210090c12060501080105010515090d03090b030c120606040b1608040506070507051c02030709051506041806090b 78
    0x240d200701485441c0f03003003585050102c1c0600346d0b100c00a00071700030b420842301190300030316082105142d0305d400100c0a2806a1140003000a1070518004545d01c501e50103450383c00101c00250380c500724090403042c0c520302045101040e280c8504807042400c42100b100d0324007e40d044454461103907580030404105540062070301284200041c5444150546154810600306a03901030040401c240790300140c1c103e841100c003c0c049030341ca81d8104980382d15240034450381c00e0401c100200c0a803c0440542c1d40443c001d08154042507070304c5107012126401120766a42c0154000f03840704030810079054460b0022400d54829041504010420b800d80c0304000b4080000454848201e0400c105441114050900a8a030309c0c0c8592042c0707045d6581d04101c1c041c0300e2041031907140b16140014100c0e000011250000d00070041c0c5881c081d0854010f02015203950301d41c880861001c19141c403600000d000030104002d0001401c1c03c841c0c00081150300c9500300034031150420311031200d03517624141a50a280b050080 = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 147415908 1250 147414658 147414689
    0x170a1b080705130b031e010b161106030403050a03050702060c0301270c030f061401051b0703020616020102010b0d03050a0e13060902042112031e060f060e040213 71
    0x5050b94280501c0e408110303100b0301c3c8038001c1106840305003c1d5029944a041301040c8204c0d20f008180042000d015101184005001d00780c800b0142a880c000719900a004ea50900c3c1a21000b04595a00864040c1c000c40c0380000c1c1800700980c148107080c1e01c0038081c4082c01071400c007002d00509d9803006216003440c1e02042880c4416903c45034130b41c0c0c044108104000c00c803456154101074040d00c40c04001c17410551410070005030900403001c01100103072050395600c1c91316800040d850580044141100141d1164413400320058961f140201035080c884412035902c441d40c1c0c40024256022566024000e0400b24081c000094012050f41e03480241e505003010042401c00108000082c0040c91041003030070648006031080702075006100303554440d14144101d861031040c1289000703900394004c10520001a0304601544203510086120022170044a1200c261918203002e464403070b0003000e40d005e0b122800300040c80d0402c4a2080014040e2030641c20480d146e500000022a644281c0c0094988a003 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 147417158 1250 147415908 147415921
    0x10201020d061502010e060c09040924020d0c020a0308070f0215010f08010b060406020705060315090a05160f0804020f0d05120901021b06070f080910170a1b08 70
    0x10191204400401c200700007580e511407128408040020544025520300508428034030400b241240c41010032408451034071440c8010f010041c04611003d40b00d50401640a41c88644148004034a684449001585603990b10300c1c04003c0b2040030035240150350041b082000004d4010760495480394682c1882c01c600100c42e4802e80c100321180c0d01c0d040124800c00300120380c9190300816070044e2880c5034001c0085180d024203204440c4902c3c06580b0150b44404c0c400c000302c1c60114015903000b80c0890b05922030041d007070042490400d050b2030034200142c49100304444110a40204804030b20185000340f41081c0070b03c0050000e02010308040e0280e0f084c81c04110700c54442c0c40880099a40c44811940b00c1d002c020440803172078008170002070041c0100880c0c00349a0003145074140311000000d246500d0090b0940e01e468800c244d05108844c2c042c0184506e070840c3e61200080142a001341e200d03501010b00420052101c4a07004008540492400030741050a04164211144a20701801d201d13815841d0700 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 147418408 1250 147417158 147417161
    0xd0309020402040503151f0605040306050910020c0d030f3b030c070801060f0b18030106030c0f0614211302040911010f09061211040b03010609030b010e0709030809010201 75
    0x203403c81601407241c41c0d0400100c0500c042598800e90b0001101f0300d00c01041070344280011228482c03000003800501c01840411401c0d405039420001c40412604040307946000a0140d8001c80c000800c2034001e0440007031125018081c98102503c1c001e170400810034018030914524400703211440883d900503400350101d00007005841c0400da056002c41c0c0d03d51150000880e9141813502a0185070b5080080004071941003068034425a07100703568181c00c3c500843c2c0c2019920020407003080d403564954000001013504861303440060011080441c0c007040c18800d0143c43d005c0c4144030b019650604200202080900d4014401300740c409101c0700400c0c0e103421070300a2911110200103035016103420f4002d000c002c0c0c000040f001c3c0c8131081c0c803a044540308085003510100d4803172180c40007048a45451850781c420350b6101181d203140c003400301810f042d100c052980141e0026086000429038106003030040c02640c3c84400d004080e5444603c0540c500481c004115408620000740101c001185e510001d81c000e = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 147419658 1250 147418408 147418417
    0x7080906010612020d061a030910060e040f02031608030a1d03150615030118051e220b0a0b03070b0a050a0f090b0703080105090603030a0c02090903070803010816050a06020d0309020402 81
    0x100347e48984910800c0384100004ea2081e0355120032031003a05002010000c5500034201240e001000140769987d664945001d401842c810407a894011503940c0094258200d01e904013a1203450000c42e114114180060010405402140c51400c041183c03194a642c0001c2c41e1740c102031041111601685840300421200c8011503030890b807000012001150540000111a00945500d2001d001649904421259000c1402e452054007005000041d05800351110303000d0080f1408501d01700301c24a1619400c40340103065070300d00b54180d240c0102c5002c502d42042100b02500703200400915150a01e03030064500d22400c12000300340504480000c7c019805030100e10003c040811080b550341201d45801404e01c0342c00d010b00d80c070500e400e102185c02424000155031000e015901d50b072680512a03002c005003150003c000c407503e44000c0184900082043c0041d40c0241500b40007003103082c02082d030340c01034005a030b007000f0b01680045d201004840c0d80000c951210702d03420b06000501040340c1c00402c0c040e214 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 147420908 1250 147419658 147419669
    0x40b03090a0302010c0f08040605070e040f05101a030a1a100e18010f050f0f0d0c031101031116060f050c090405060f010504210f030807080906010612020d06 69
    0x402002840034010442010691090b0b008002d4074200c140c1c10b070340e1090502e880360009044003000070005411340c1c1c4140d40003c03140c188a030316944540001403e88014100c69a09540c1728414405400c55a00240f005030080c3e511504141a030b840d0b1101080c00003c10401d42c0c1c64540c19a518024083c1c102454160310103062003d03002503004025085210910403a40201c155480700c81400d000c116205050f9280090cc1c0c3c8031f414940002c0201c901c551309200c0f64400c201400031034041d6030790b80f25036140c0f902c03543c908103540d85141032030610f1031450742140781810304000e040048040c00b4022a4a0800c50350011020304500e41807900040034036120a500c3d0914003414042102c03408000341c540400304480074001599100d0030b1080c8401907500c25400b20b481440144480f013040c00400600c2c03900c41c5540d86802c80261108296440c000300c1c10760104002c0c20910044a920802c010b0384181003500a01a1f5407502070004c20040094039044002503000c98031642040c01134000400421 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 147422158 1250 147420908 147420929
    0x80703170a0c0f09030206041a120f0103050615061b0a141b0a0e01030816050115090b060909010311010c0803010807091b27050414040b0105030f070b0a0504 69
    0x707441500d0200030040c0c60751100208420b5420001094440c00c2d5207030907281c0c054612414240781c21104620001e40d207080d12480c0600348030117894507203982100351040c100c00b42c0c4442d541d455400c0090510b240a081b001d00400c00704103d036a039888540441310742910708a208241e029a8140340c5080c400441802811610001111a1000400603102c050030403450f019011807044e00c400c001140c2d00d9881241c1040c00044010008109124054070500c01c400400b04500642c6590b0142100c400785902c80320303000002014807a501c2036104000d001030099516500d00720f160b01c00100c1d4414148401007510750344000c0d400c1941d1040980e10035966010170300796181d503100c1201d82e80710b890a0203400e14983c5410305403000c4002c00c080e01c0304141d5407502ca030500111248046c0103041404a500510052402d0300042c442d15140b0840c0503146007410510584d08062800c03240c01c2506074002842a4091805500b800501042420440e200f2000c196075866007481d080e0780b14040d9510080d60310 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 147423408 1250 147422158 147422161
    0x5060f041508011502150c030903091305100b0304050a0f03140406080105090c191b080d0b13061a0702041d16061805130e011503050f0606090408070317 67
    0x1a400c002e00300d05a44c03e0600300c3d600c1031038460003241d036140714114031350459000d41c01261401c1106001103400c40e106c903040d41e00e0302044001040e0f00013002d0500400d010354407070070400c0c4030000035100c00207440b10b880c4ca2451401d0681300c003079036031502c280c0c09840f00123a09901e104041c050900f03a48540c1075683c51036142d0703a41d290007410b4004240704a500614641000030410816101143c88080c9200050600019038034002c0f101d0b0201000040c0c180c1c1002a03900000c02c040c2070146c60b011802d040d0200d018144032040c4410141c82e207900045c130074204038043c08040c80c040d074a58400041c040d000c0e0385a000c2400020040c041c6009242d0760451038a481c581004c0c4046281851310100316000c51045950751021941010741c100d18800382c582c1648140000e00d000c40d181030860b4a07002c40840e0704942e8088040c2140c2010b140b0001c0400c1c4280c3c1041040010322107200001c450002515251a2400c040350034104010002480c0c03043c00070710303101018040c4445e59040c40d0101b4016145 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 147424658 1250 147423408 147423449
    0x17070f0608040f11131b02070504110412050c031203180706120f14010605040e0903031b0d0e07060315080102040308030f062205040b25050c03090d050706260105060f04 74
    0x41d007421b030400301c00602400301302042c241807501411a410050441c458a0140307083e42c4900303482d18104040300c1078052101180c12aa604101c0030110400e50300c0041d07a2402d1181c4201440d0908103c0300d0381302d030040d1608115240c0c02a4150700c070140c4100c0b01113401c584012a00006001c075255116044940c10000700360780341d001c070290050f2940310303c0125050710750401040d52804221154451603903449071503102200010054000701e2228a00800e04161070140c203400c20b40941c21080c00203540e20300c0000d45500d41c9000300c004001c1ca10085103040d05580b0303480d00c01e10005040e860045402c1001c1490b640316814000c04404c41030a1110b004058010030b1000761000783e405440d2845e910740441c008001c00324500c4001701d0107002c0c90310b256600110a42d0710350400c85580030140400c2c0105400ea84581411810503407050380a44000d0341080c034080d28844486c0d2048200810006242d480c1e9501c03051024199071007195066100c81181c4070600e02d910807600000710a000c0340309042d14 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 147425908 1250 147424658 147424691
    0x3050c0906010c0f021c05100c0f0c0b0a0908090a0b1206060f2b0e0f071406040605070204110403060f0e010c0c03030207060617070f0608040f1113 65
    0x651a000ca61400640c0c4945004490110840002410b401500e40c00c6400618101c95030754003203031508003801d08420301341c0c444c18100162200c0c40a01c9585070605215031035407005081d645030400782071403498542c89032111650018010104138200c0d40c0d0748080760500540344140d40010b14002c0c2410041e90b22854101031139007240e0390603207151280402207040b171305d0000113544841c00340c49101b6060190303814000545a104d801c500701500d480e0000c8400403c400d0080480c1480420018000c1d41c5e9a00d0115161000b01c1c1d0180b160341404c03a024030703082d85d28942107608454072460b165031100c000d80002002031222050780050700400040000400c9090340100b0000c00c0c1000c0104000303032041c80a54241c6620094000c00142e098600c1d070000f9010b0b82c05800c1d11805888002402d40e1551001c0c43c50308180d0075032480e603034803100042043c101946880d001034034040c40c00449504240d0703603204052013404402082d140c840c070b58982c03490700c1c2c0c212981403c0b44035407020320950426580100 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 147427158 1250 147425908 147425923
    0x4050108100c03140f0a140a060320032e360203030a0318080318061308040621050a0e010b0402091503060a09020304050102090109060807020d081902040305 69
    0x242010b082203080c54049001c2d100320402c0c82d0074400c6604003039891500c3c500c1515030007003d180f03085a545004500d8240340c4440c543c4a0031518100107072160850030804d00c00000712010181911005d0903540558030301003a03c0042c0b1003480c40c0008845c1a1401c01c90316032218010308a8054a05031703107500824500c4d10301c030100000720580341050380081da050400001c003100c0042d416500070410f80c03401900c01e61006914403900ba07010452100c8a40e18412103030310654400c0c4c0a8000e401d4084035282080c042c00da080301058817a80628005907940111314020380c4100000d012800000c1d0100c010a10508511940c0001d4200a24a0b00d00c0c0341d94000c00c00318070300c81030a40c0b9005000c02c2030b0a082c400c072460741200500c020717204010010720803003550008000d2034124070000300003d44900d10b0700146004522600015071901c04000004200c18465400402008207140c03d02c007080307030040b039001c1c0402e134985005070195030b41804149585043c59451041184000307400420b010b00441c466 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 147428408 1250 147427158 147427183
    0x2030a0f0f030e0303072a0515030f060306100501030902041b0909050903040807121b0603060e0a020403150e0705030a06050a0605042919080f0d08090a0b0903040504050108 76
    0x14040481c005044c5580e90282200003840c4403200e003071b00c003060080c00100c0310400c000454039030400c546076404513044405e211603a8110101c00300601c940d5000c140d0b40ca0ba0701550a800509541c9031940385209002224400c0e6814941c2d20030341c50302903407565040040502d4482d10f03c02c1560360b91000081c070a10b41d9100304001d40d40380c80003044610901000300e808071041d207801003401c90b0a0014590081116080840703e02d4a038543c0540d03007080120810004015540740080d500380b0f0050359121a120041008108a20401c014000101e008148032000c2c40d044000050b0507103c80342c7c0d0b42c50403405802c515494440c907030700c1c54204986500110310600d044d04043c05500c1d594401d00043d5583d64403000580044500c1c04c80005403038481c10745d158980200030700c042e103040c80d000c501c400c48142c00c100f106420103001f60dc2c03e03000402c0703d802150541c0c42e00144500d4400c45180c2c4a44407103000410b0070b88010045101006c2c1001540c0242100800804c140d51f0f603071101c2c42c0d680d030208581 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 147429658 1250 147428408 147428417
    0x190c020d05031c0c0f261303030f05070c0b090a0203030c010207060e01060806070c030e04020f0414012c0604030203010c0203070c060207030b041101030f1b0e0f1c02030a0f0f03 78
    0x10361001045030042c0e903900c0000d6224451480100c480907a08020100c0c6962110810a03031504102c5071160700b890b01800d20340d20700d51f142020a040c0201030303402c0901c0414500781400f080c04095903011803c0d071011504080e020100c1d4031558001410441041c0c07011358144004035030540a0427040d802000b969106110411910300c01c42c1040b400d0350381c10300c030f502c0090700814001124903024822000840d0700c80d1509500d64441000002e080360444050440c500501207800d00c0100802a00055a05424202002c1c106000d0b41042c04480c0d1a0340c561000700c2105400c80c1c07a43c1c49910540b8040d40e4001d0003401901c00e4044006c0d541e40141c0e100341d551003045900026a00d001180c0c07501600d40009020403a540c030340d103036094050752590300b2604060341c681c5070349120b846c984242da1800d12022080c000f80c24505070002c10000e42c00d110785100f8040000c5e41c141980c0c41d40b601c056010050f03080c9034441380042c0000b90401441d41c0000c1c2108080e4030380d81d07080040071141940528401e031103 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 147430908 1250 147429658 147429697
    0x30a0b0618040f0201030209060d050f1603180204020c0f0106120b1003050303042d0c0311060a020a0f230f010c030e030a0e150705060f06030d05190c020d0503 70
    0x504640520a81d400740c65103101541903c055482900107000403940600401d191020b9010b00380e00304ca02c00c4500b019418021002d00411f40200680d4441200d100e2a0603c001ca411804c0759142d0194020000c0c440c0d90700040e60b5029040520001110501a0000304045941d4144c405580d0301c6040381100c0d10940c000000e841c1c00a44480c100980f0307080402141035a541759522040590b071a801800640102e0140c0d000003101d007000c106c41c40c0d01c68400040120700c0d51070b00d0103400a01003000c07072050b1000e220240045600141c2d40307031101d07004120240d288542d8209600c22a2408100034903c0142000c000030300303440000c680801c0c110010003046911217201c001c504544601d461420709800410005900c02d200f4507140e4a0320f90010f00044150b9100c1418000541c0b210f0821a856000f0700c1c1045248101111016403000c1e01307070301031301501800302d0780140075105a81e440000c1240560f0b020b8841481104000032140d8040c0140106403c10300b8920703581e801410340110348110505 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 147432158 1250 147430908 147430939
    0x708061009090602120124030b0105090108040809030d09030c06031a06030403020124030c050d0f2301020f07051603021f02010b0d03030501030c06020604111e030a0b06 74
    0x52803441200001080c490140c10140c0c00300141c1081141920156004d0241c600e0282103050303198020700c20802001c502d584196100d5000e024a0b00d811400c1c1031074011644800e036001011101e0700c10f0240390000d415034403807909803a5030161841d030b05d03090301c03501210540f0150044030b1101564003d000c1040e0196460b0011030913076000c801ca00c1340002c2ca260303081455003400e10245401a01c01d00021400d0708640140c0d1040e0310b643d221490318a03a140a081040c4a0f1100486014001c15513500c1c410300711070303181c80711100c14603140200000b032001c070750203104114060520076a0031407000a5681e15000d61140c4065001070406a90f540240c88007403d1000003032280c00101c80d0702510020207503420840e100b1005400922510565480b080c0c0380d03a20303a60380b1420780d0510303209440003d070650450401c40462120781d0000030955010f5010310000c0f52040501c109005005c0b51520800184000011070010345844200e40501c075142c1400108070550244500c24001a01c4d091008034102 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 147433408 1250 147432158 147432163
    0x6090c010203160821010513020304050c1009080312070905040b010c0201031505060d090b070507080304020415091b02010c020d08010905060619031b2c0120010902030708 75
    0x10411800750703108200c2c848010103d070a4194a5a000e100d01d0350400b032140d1150714044074045010402d0100000c014443e51401172a0f0043c0c1d142c2c0b030801141549004d5a416546160341c1d4100b070301c21101c0f000c0e0301e451140b140d54030f4000b03031060300700396511400c400b249100303002420303a2040c022402000340819681064441d0b400201c105a58400d01c0480c0ba4006400030040141c420782d021201c480080f07200c0c1c551400070a003a042422001441c030129040c0100d03043c00140c040010450100020804900d0403c00c2e41c0c0c0080e011100000e00c140358000001c0c168403d84e01a112407410001c0c3c0e02c095a00190400a034800741e41c0007417210008080080f604d9400341d101590100300312200502240e8aa507020325449100601600c1c508070b540a51003505100c92b1503003000082c1c07070b00052580311101c0d103e404091740141c1010800804c4568849051030b20b450744610040f040200d86c01640da00c6865012045151076915003074100503448034902030900148140d002c2d200c2c0c0c202c00580741100 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 147434658 1250 147433408 147433423
    0x60102150403020d0807021606020a050609070515090a030b0c0a02010c0504050d0308131a01061b021807021507020c0f060703080c0309070302060a09051206060901050111101406030609 81
    0xd94040c01d18490700300002d45070060094424021403085160b940401c2c007003039013000054200c9d0b030000c0c140d2160078640285041001400c140c03081e040703020200420341310851241070100c0d8101d110b41e10b03119101d000c00c4006445a102400201500c1c0030320251b000d842004000c0000316070300a015421440c4019a0248503c0c403c1c80d8000780682c58a501203407092440c1034201204e5403002458030102c1e1642c0c106000300c4409001031240040040100c00e4215180042a00b0784509030100314240b0b400280d0b0461040c2c401075039812450001600092007880007108801c900c006024541c1008040296203502102c84580038002c00301e103215280c5010002c0e40d580035410b0b66410816512426010515040a00305400f580306181c004401030381d500f00030700400d044603500e000010340341c00c04100e403d88140c0038014007038002d4018440c181d101d111480d03055603400c1c20700d0904071844600e03c2d860821000c60024038203192904a02c2d0340410451820300640e011811501c55490304528a44c49445 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 147435908 1250 147434658 147434663
    0x61c08030c041d060f041d0304030c0e0721020307170103060c02010b03120301050f0a09020d020d0f0b030c010e0112090602030405010e0303150d02060c0d030504020a09110702060c0102040506040603050601021504 93
    0x401c401d2481c51881c6c01c2d007281c1c80391844800403442d00d00501d4522403441d0801e400445039000312040c203000c12500950601d52003841441c180f0b0382082c560364124030170728030780c40c0d41c2e42419000030018491500450b101c0d1419142c1d021000903647e541d080c07840c010b001c80c1c5181c0c0015424032012503903230b140002e20344a8200803c131800789180d03c2d141c1000301680301c040355140c0201d141a0002101e008901c058a00c03411a0340c030159030781d0b090b07005102c2102c000c03203059849a0300d0700c4820a440d441c0011413045143d400c2c2400f040d986800401600c0903480c2c00034036082c56080590300da04101c0243c001c4c1d805030b8070510003401421030400503603480e804212400d8400903440c0c000d082c82c61a00e10280d0706040c1c00a030030310345040c20180f002800c0420456880000c25100c000340803c40c14448800c0c2e0041c02c2981c01081388100c1820079180038801c00c02c3c007030320604000c14103d2501c071080d4100c40045c0401000c8655940d40ca441c060081d05017110002d0141c001c142102d42c0c180c40c8420381c20320856 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 147437158 1250 147435908 147435919
    0x20106090209150714030c0a0201091d150a05120c100311030c0f0f1215040c050a050d140412030f1b0c152c010c08061c08030c041d06 59
    0x21007907101104a070003c00d0180c0341070500c6180c0101e9008203000070040f0f14904406090144001e0001604bd0308c0702d0341c004803a4010001002140603520740d04103800001502d0782d12565030382c95000811000c19a0811580255500078010b0208800110101c2000c0162406c14089841c20400d40440343c02980742850500f042001450300740580e001000c0b00000f036401c050414100d800d03495502d820450303000e1500344216003404140e1080310190300c60004106c40c24040b00007160780003001801030310007440903c207000c00d001060328030301d402c07130000400e10001016080c50182088001c0401100c4001c0200e407600c02050007000c0700d0301428401c1c081403030002c3c01c0d44140c903a0441d15861400c9003940c0d60446500a085880c1d214028105c444074040030014000403001620041010500c091014980c90410b10341c100da030304046402d03030080e02200e80a00300d448042800903024445140284607100c000200a44096000d018000313035203100c01000d410301004000b00c00c0e4624243d90703095120 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 147438408 1250 147437158 147437179
    0x4080c1c02060d020d060b0301030201020c040515010e032109100905011422030c06030f0902031c0c0c061e0c03090b030901020c010f050a0507090e0115051204050d020106090209 78
    0x1420181c008240c07500c030a0b9401840d20b5030305c1c1c951404446498220030740d131800020041040d0340c0c0c10002582614001c950030011400c20510191600d440041746505101510110100d01d81c1d050107145120729805520310701502264400800d0342e40640c0701c1ca4032800140700600b4a00340700b00f81c20400c3e00c0b41a120300d03084040000c0d110741d594101c03136581034180040407030800d0070f0f86403601120003c3d4861003074511740710300307101d8085c040e1418103a160b1211032038602031388003580e00091074621110121000605c031841898003140c68006040002d88500102240099542e0f80a07004600c0500c1302d5080c88008824804220303203003500c4500150000e02c0004080c408003040000035900698040c00040c070b0007030040301840c00d507085999480d455540d1001007051292181c05010750000c01c40c6403044485080080c52494450103008150324055600061a03800d4080c604603500d65030a07400e0b08280b8501440c0c1203a41e08491907400c4015403c240d000100b440b02d500a50700d0041c030050003510359 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 147439658 1250 147438408 147438413
    0x9080616030f0b030d020705030106170601050d02010e060a020a030207090e100e0309120109020f06030405120d0902090f04150213180609090c03110603060d0816020a0b04080c1c 78
    0x1600900818542d41640d0305040401994204101840981d2030b0f000790880d18502010107084804990080e00345404800703c6518101021170102d046d90411200b101c42002c8500040301c400411000484c0c01880004a41c26017640002e0100e050f03e00c03a60880d81c60907164040801074034404d00b040c0d070299105600500c510052504519031001041e8100c9083c01c14180000303c6240d0101034110750769541d0b00c44601542400050400e440400740ca01a1440c103007aa100b40c2d40380c20809050110f00008a00c40d014070ba8280c02900225400402d1800743d030400981100c0f841900761801c5480e015080c1124188080d14001c0d10100072524409a10041c0750841c0b40c20b84480d4100c1c0b0052050742c5103004079500d034103072040d030080360b00030b14404001c1829860020700c001c4010130b80c0b070f215007014010070540c4c4d5188984004800d03030194200392124004c00354180a00d80c4468025403000c20414080b84000107803002e0400c8403013420494207401d0381c1d0400e000811591742d074040083c2418010300001f = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 147440908 1250 147439658 147439661
    0xd050c0a1b14010204060509090a060501050901050328020d0b0a0608190e060109090512030f1b1605060603151303200a0c090506060a09090c020a150207030908061603 73
    0x41c02401900c0d5403a402041200c0182268025001000410004241100d080c14111102a403040c3da4000411800d03080c900083c0c001d024000c480c0f0b04000000000403d0003402d600e10405511801045e007070103010015000d0081c0d000240e1251606103040030107606072400280d00400c5803456102d84905072a100152420700c180c05031038100c1c0395110041e08405032400c0042500810280314006261002890914105848500d03c414103420a10500040d080415659034000304280007044420020040034412030250302c00358202c0c14904001c0070140300d000703c0c0e003620440049059983c1000c08040c0d4204001c401e94412640801c60aa14070000f07009412403c000100c902071502c440c10141c0c0c1291401038011400c4030114079160302004850700d01c3c001c0d07079005141210003d00b0551400c400406008580c0700d250a4551101c150a88260080c003100f1034558100000e140302c100c0c3c1c4500c8c18081c1d8415002140041c00d40071001564085c0880c859001c2e40c4035522449441c0000d840480 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 147442158 1250 147440908 147440957
    0x150f0906010e03151501090e010303090506160609150f06030804050603040201020c03072d060c030c020a0f12021002010c0f0f02120a0206180706022505090c0d050c0a 73
    0x20b42520490400158940042904d42c1c80f48588000710b070b04000714600010f042220b04e80c05086210b0135480144006600001c082e825105d040d100f4540f42c0d1880c00740fa10703440c0e0288002030142d629011800c014800141020f00d0007030300b01e050501104003210403c0044855600c03010300348003070600c0309225070324001d8019600580144102c7d403102011100090410420b5440810101d4480c03502c103880b0120030340301402a0802c01001c80d951481c00801414800885000501300400b1130414401c5584070490b05014250111032800c40603107840c3ca240341b80076602c0007603114854983d0b600491920500400884d150300342d4482810600500d416920510504060000d60185404c00d00f00c012808002e010719100035401842a400c0c91450705c410500d410f00c0c00319803500003000c103000c42c40c0c001600b198070146400040f08800c00f0888900030182242c1c01107507000b01c0390300500c44940014409090005010f920810182e11007011410f650b00c078022741c00340807600c5510383d6212400080c1498 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 147443408 1250 147442158 147442187
    0xa05150403020402040e070809010b0f0f01120f06260a0816020306070e0f040506031c0207050303031003030206090a030c080a0203090d08030a0b0306010305121308010204080303150f090601 83
    0x24203260322680007a0a03a003181d0414411074007070318204a04103601078140b6401ca41c10070000c01a041407500450700104084401c103010b82000c0849404a0348142040d8040a1810804200c58651482640c014149501c60315401e81030b1801d005c040b5440500c1580a881c03c030b600140380651041d42c0c2c18005030800705c0d03402d06a4803074045460161f2800c0c003400d03220b0b42c0c1c07590760611901d6441007003003180600c1100c0b442c09503107030008021841d100003441d41440041200c032101905114901289060210b4100c070f40c05020120601800d10302c14003000090b01e11a4090340c0e5599603002d03029559034615100a40021070f00303008800452000300050081e044030f481607900d07019800002c140480c480b11000c440351403000040200b074801500c0f81944c000b8084000e44815450350f10b07801c0c2e8131014022240e0b40c41500141c0903020849a007d048001c00b07442c0c0c029500c0d1550740701c1c0f40f62260011505403040c000702800c9000546855203542c207100c0d030700801c100500d4407084011908800d511400 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 147444658 1250 147443408 147443449
    0x6100509130804031a1302012123060312032e031e200102031206210d030b0a1d1b0f03011502030a120e120408010f15050a05 55
    0x401d40416284002080654080c1e0580385159120f028040e00b0540d005042c1a16001c4405030000180c1e030000140441348450480392140803401c80d4181e0040020805010b0080d040f00540200c454240c00301d1403080303c1c11402d4500428085190b910b041c84201e90580c0320104000ca01503004031002c443d0680315901c0b4404121031034903959001943ca80c44982c1c2c104803040452410200000340c2080021449503015801000c0950030020759640568a048601400d2000000e103040e22144400e00300080c0c821142c0790502c403501c050986441e9506034020000341020307070203022810300c030138040112140d20304220750400b120303074001400f4078020f00440382e02e000200d070301103808412001800c03980006c2c514042d62540b400c1181003c580b00c0c1003002044d034006007c80800c03190411035514034200c0041011030043c5c05411024240041c41844001400020a010445280560294100c074840c01d404201700c40050350640c0200025108842d071000703d0010a02c01402c002580c0310620446240 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 147445908 1250 147444658 147444691
    0x12080f041502030c0705010e01090b0304141c180303080105120c10050d231305030c0105040c0503010e0a021003150506040305010b1003020909010603021605010606030b0307060206100509 82
    0x407400065003016101005074000700b0032620580301800f0a078001d02c42400c5c6008038100d00000640440303014815003a074144d010001909000c6040740a0b0301108100341074034000300521a00c040703550241070f403c100103000010a1400c469400d80034000741d039056155241d06a190104019501c192030030401598000d10840c802c8903216082c5106400e2440d882e510b840d442046a01811074103249003544501c003081610300b8803400030b10192600500300301c00c1070400701c3c120304000b8a14400d0102d498029846e09082100b40641440791105603501280280031007210300440a83c0ca4121410103503001919103102402d40f0300990040860300c0d042850304003810b80d2480010035541041d0300656203651141c00e54291450151a0f04503a0301c924101141005c000e9404509403132014000d44042c5a030000e190f101d0500820703940456944d00c10f009000c5162500e400502502c20703082440d02900c00c41001050250002c01d03010f20070b4210307050750300c0720514140421280c180040c02004481c4640803 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 147447158 1250 147445908 147445919
    0x4020409031b0c1719020f03070e0a0603140d120e0a05060a1409070b0403030507060204030b040501061a0c030d09020105130806010f05270604180317070912080f04 72
    0xa240c0030b119400f4a810989081c504000c80010741c81025110986400208100001201562245003c19016506201c684c0300c0500402d14182103900064170b20325442c030070040c1e40007064000f20300307481c8030301080c10220302c02c490115500c142c0114407001182c1814103981c04000107074003a030481580e43c0c003201d551101e192602c07410501c0a9070300b030120b103440f280c00e281140d145403522600114000c0081513418074140c10001c8502460200604010000a41500784000c0350166000f80da000000ca8403d030a05181503070080c1024070411090459042020301050070500550390080d0103000510303d061941e0f00c0502c014000310404905100040c4000007600b00e030001e082001c1e194640c000c0040e03505100c0c06200624181e44041d21550b2541c12080010507201c07410710804441c45040b0186481d1000081c024000605401110010024008051540c00f60380c003c0080703000070034401d03d0703110344104580c03241560048460380400f0821202c0000c05036002001110f80320562941000e8982 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 147448408 1250 147447158 147447197
    0x604150902030405060601090302060d0f0212150f010806062b0905161208040e06010e03030c0a02010801050d0506011809021003060303020c03061006050a090803030108070611150402040903 83
    0x40d04080609940441040100070b030800485030068003d081c009030b01480c50f40091000e1040035003181c6c10702c0c3c40310020381e400400d68040e00d0070249000032190319483c10070250303445424100380d111700c2680045600c540d5035010b102e086009040c064003291610044035a00d403088007442c3c1505800d01c40384002c01d601240d8a05c45c00724403e00c0781000d0050032203040e12011020143d90081c441d521501e0b80712000041d110b100300c400b1907001c0c86503040ca656807500140c0700c4049803e801c84d014003001510024404010810b10b0496100341c17242125039803100705101505080b09001440c0f5404500180710b0500440d0282d14200030401004c10f0300304180e8081030ba50400c0340200b03408251204014000c01d42c05104000210509400400103480c2240348411042d0540c03190031700f0710000040d8910810320500c000301c05040f8000880b65256540c0000f5680c80c0510f101e0407000400d66090340346036090110340c1ca441404017500c249840d032a40d400b00300c0140100c1004500303105202c2c401d0700d54140308 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 147449658 1250 147448408 147448451
    0x30a050102071a0c0301051f0e0306040605010f0e040f0f1712040b01120c050f150c1506060a0c020105300406050705120c0f04030c090c031109090703050604 69
    0x241070411942400c0c600fa41405400a0074990400105100511184e00c80407607890220001960402c3c2013540000c080c4c40000d40b6103455a01801800200000d110701c0c0d400030b504903020480c1d50703440155940034240e080d030340c103503002044600e40000c1040803608149078400b51038090724407448001c14403154001c01c2d50100780003a0122a20800300f00c24007640c100c2c51801000203040703114020308a65650706100c1c82c68001c035485001d048040441d030f6110b8151680e004151014080d40d59100b01c4003007a075545040d541442e0030030000300041c100d8109481070701c5041403151103008600089600544646d04442e181d4050b12036200400708912000552446004c091071004182e2410541001020303100c00800d0401441010400d03840c141344c2d55410190300c080405422a140c44038580704034428403d0b42e2001d803026140302004109041c841c1c1c000c0f00d19030807a840c20400d00c0024241d21900303006004080390311055010020303088502039004180e1040c070040000404085001408940c0038a = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 147450908 1250 147449658 147449663
    0x30f0307050c1b13110702040e0705031615111b0103020706020409020d060b210606070b101d010f05060307030b04020c010218040b03120f070c030b040b070e091302030a05010207 78
    0x110f072010b800505105428104a0380489418003901d0304031120800300c1c0c03040d00320007400b07107548100f034400b0110b09105071406004000d0039280014190500c000c0b001809000e03401c1c140c0c050161310030f10180152404001c4008000103081d82c27910020200e9042c4a160103090b052517000c0210300000341140c40184080c204600005850788854440c0c0402c540040c1c0103005903403420408083d8060310f811b5100320044060001c6500f654695010a10a000e0350500405100130b200a000443e034208810b0340c1a070b5880c041c14007200d400c621110701c00f6070f000c4c441c0d9071000d840d690303007400baa0501000640d4000468203022800c0426080840c0480c2e000303440c941d150382d6000c00c03c0070f1016850074032000440b500701c07418050500040002510307039030b01c1312a1007600500001d082c0d80c881a04004e071143d041e0400400e19030030303035a818015842d2000700c0d0212101078810001989550145988500410f80500b016030a41e540c0880d5560b151941241039030f043c807903506030800060382400148a84d40c03 = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 147452158 1250 147450908 147450943
    0x70303020c060612030d02090303040b0d09030210050f06100e0a181a0a0b070c0308040b04050103050f1e1008030309010c020f06010b070b04021c030e030c030f030f0307050c 76
    0x190515010304002d000381c5007501c9150184502c035003465000061341c480ba020000016524110440003d00e03510442d480002d070480049840700c0001ca0036440545090b0017502690303400f0340d09110500c1140c02c1210707078145034001c0d1004079809003400c0c082c0709001b0708141000300035004010001014a41c0c145e010416240d07003d200101541080e00909011131030008008503041c2200380040c402c1440750150001d07100002c00c18406005452003400003c3d900b1805003980c864956450500b40d5015000d203901080c14180411101c881511459100364074020703240d191040d1080c2d030402c15030b0000d46499881c2d17410010115444800744000c0d8094a20702d40001500072009c540a810002c006100300181d0b0024030040152900721811144803940c04182c0314a41d64403440080c0010500c8070b240c1c000c40324240b10510415822642c601c0900c101241150304694141c000c05550312001004e40a040d0418444923000d0120400a10b82005441c1440c0c0d00f810030b07da1082e481d00301142d142c2080403 = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 147453408 1250 147452158 147452167
    0xa0e0106080a2022140d082d043204090302030f0a080609092a1504140108010816090504050c040e060a050702010c080c0703170a020d05090c010c0b041707030302 71
    0x80c8041c00090b0000c1c146080170b80900079481c40000c002420b007102c05406030134002071801e02c07040c541109009005c003466209040080f00c1211111a400900542c2d41043e1006540102031001f10710020155095051035607409040005000260486c3c4d082101588070a01c07920501e0109a0040c100d001317059940c450030307071600604001c0b420901400340d42d010b1b00072500ca62030300100006264801d80300d50299110042415010510420982001075105500410040380120a52209c800c2800d001d980344005640c85d20b003203d03128940010300c0740b14880a510b0800c00200e95400080e402070083d001ea800910044020074161045600a44d049401c00010031a80c072140e4410940c0000d03c9100810442e02c0162014042c40300240c086003402d14046041020180b141500302001c01c1c074100059114113184800c00040c0d0001004544418180800078030112000a6201c00e61001651400c41c1103085480f4040880070180080d181400388001c0c514114003010000d04034144030b650f005a96 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 147454658 1250 147453408 147453457
    0x1170a0b1503061809150c0a0e150a0e040b0a08010c140406091206090512030109110f04030b19020a021006050108150603070203130f050a0e0106080a20 67
    0x48240000d0440284041401801550745480d840c1e4100307000207211040d80c644800c101e05e0300e8003400f0510004000070001c10400300014510160801c0001521038030070060141c0f0800458101d00c0e00000401c0b0418003456404510541201060b4000540001074200c5407801140401e4404d4220300e880381c0d1034891303e1280c10351126000011000311f01c4c41505040c01c00800400742c075060b103d4030045044452030082400a90303481050501d80c45000c4420030030410340840079a402c244949124a81703401280c2032603a621740c04407a640c82444500a103070a0031941e030040d0084000c0d05580003151500403e240928080c07005160841da113400a0080d803070740000c0d84054568030307000175040040c8901800f11802a04001c60b0015030b040300e5843d16036a82800882c0303580a0146210759040640e840001c500110b0810312040c1d801c01e0b9002943d994840076070f00e58102007071041d0000a825500084c14464240c0c1c003c1c045940b589803069502c0350740348040e0f130690b0410105000d5480c07003003023400030 = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 147455908 1250 147454658 147454669
    0xc11033c070f05240a082205061503070321050c10141e06010f050c0d11010606030e0d030207050a020a03140618032709071e1b0204020901170a0b 64
    0x1c40119002800613035090000c0402c00c14001d0680030801e0029032404101ca1006940f500e4103442010200e0380c140201030f0a1032642c802050340d10b1240b07c2c3c0c8100e40d00185060104900c0c003a40d4020080f0341484201d40082d0841e414003412007403c2080a1194940c03419084c8410078071110b01c58004180b50720404407929201030702070305180602840e60000071045c0301c05ea0304684e011609007051102d10b902840281c84500c20750040d0082c60080c00040281283c10034011095000000700800c99030391035900c15400c4910b4041ca014483c0d200003141c01070325100b034000300000c51180041e02c2102a20745d011079100840d41c3c00c1103c0300410302c1100400c001e030411045911200241a00304104141d2105a449100d02c3c5102c90b1b003484110a1240c00001e8900c800c032981314080d0280e449468907803c01060240088110b1640e240500000200355104180982c4000c45a40640e80030764010741c204402980519052410b000440908444840e680c10031f00b032182e5010300340800e100c41840100503 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 147457158 1250 147455908 147455929
    0xa03050a080c0a0903031d120a0506060301020307020a021009031e02030f011109121614011d030705040203041e1518111005040305030a0c11033c070f05 67
    0xe45a9024021004865407125107407044a0301030408040381f54401040500031078502440a41108a50610701503041c1c001a8403101903016805550954441408041c240e00c0107035a0740d03005034810110440549015203030400c00d52841d050004000c1e680356903171800e9150030301040e892104140241021760030144450080b07541e802008215111000f00c044c6d515014444a5a0107600304221100e0565010003203001c00da500040000811035442055003085080d10041c140050318640140c0c006810a8024003a40c0d000200034009490406081c44002d420081050710158454420b441e01114600719501c40305008a1b0740c10800c00f01140c0725402c2e6600120950420361a05c038003040881c250b03811818a81c24111040c0c0504155400201e0f92400307607400281440c00006131010481d600320211b81d030a244500e030b400021903170040805445120f80d5001060690724036101202007240c540d00f51601d600440340f10301c0501002c040440c03074030348150880c106e006072940c018003030b80c80c1600508 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 147458408 1250 147457158 147457171
    0xf122505060304031e120603060204050109080607090501030504030c14070602011d03030406020a03110313060605060406050306121c090906080715030c0309170a0305010608161b050a03050a08 84
    0x1c1d1940c1000e60300100b003080480c2504521303080c0040c402d03030018810890a854032251540510150303880781041d0000b98802d215031404a007000400088030b032800b1460318490b0030702d07444281c50940740c2401074016105c000c10440422a00701e41c45d50004200b8401a0009090b620003011981d0801d80c0c041d0845da500d6040480c080101e1a40e1141c00c0c00000481c0d51290340301d5030258566691807819800741c5204000780108403004010001d803154503034400c40300503001c0c020034450075540e101444038034402d030302407113001650400000f46a03040070b10079901c450306079008490300c940400c070700200f48501c048901000100307504002c102d880600c2c040c8801600e1704901401c44c00d40703045000f41040300c1000c441e100345619501c0304610103022f54000c1000540015807150321680d140e1500080d6401b5000507408130785441e00203e00d044c4102d220500c2545502c640c0091034405a0007641e07810101703c0115400d21b000c1c610280055418080e44081c2846a01d81c2619607200d000003401c0464014000d = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 147459658 1250 147458408 147458419
    0xf030c0207150513080f03031506070209041e0803070203090a0503010c020a0b07090b030a0b0102060a1104210501110c15040203070902030a020d061401030f02040308090f122505 78
    0x9002d58030030702051454919031800d11664580415401d500e45400592240d00b4600a482c3e4160404034080002c500c02c10081c05c41c40c1c071514160080050354007500744060f400260940c0000d00090000402c4214280812a086251480c5035104100341d80f04a074000d005030400f050403040c42c1421021000a01002c0b40280461074408800a6580704030060140ac80100c0c1e0001c00c2e0031038010716204018208891072690f0301d2a2401541014041d070030155070041c45460005622a0182e00c0f400034030300080c0d80100c0c68649041d410b112540c280103244c0c80324460001c40030002400c2482503903282202503241907200e001003035000d0b00700505e0030720801c1001c061104100c0140c0d0085140016610328002c01600c0381c565114030b400900502c00550b031051b25100e400309203864514104e103440e0300c090703a003409030b42d9904410000346d000d540300050518800340f014005518181780441c481e050007074800c0d69004c861025007071804607100314803003001c0324016803000b18007100340c071080107064141c58 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 147460908 1250 147459658 147459673
    0x21f05040803060603190504050a0b01060e01021b03030405090f041e030f081e0f0f01050103020405010c020d030e090c091011060a0905160306021b07052b02040c0f030c02 75
    0x890007498400241010b00c00c10000001944c000b040c940300d5016030300326240801551901d4030300107554601c0c50500340c0d00da60601d070000802a02c5040d24003140d80043e40075200151012445401d00394042901c3da03418082800086806d40780c9110091080005c0d800300c10081c1000e040200c0c4981c101c0d403400b5640314406070768038042508003100b010007116078a052040ca681d445150044001a81407111002200340140031200b03040703d1103903000c3d07101e0320701504140e641c81c0c005400724801e0f1310411b400b080d2988801c0c4094a000c2c0c1d80429400c0c000d007020035400822030001084544100c580106030000442ca22031141023280e02c1280030b402c103041c071608030700600ca826a91044028505401c10340c0b101c0e4604204042031001c51560710790281c05400098491824001035000700c521000c1c1141c10224881c4011b1000420104460700606500e42c030000c500c07265045254004040445403405005810058690340b0840500c64082d40e240d401490b000761008050f14030800349036045510110 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 147462158 1250 147460908 147460913
    0x201022110090c090303050c070302091303030b040606090b0f040801020c0d0210020711040e010e010c02070501020c03030a081f0503160e1f090c0e0a0e25080a0c021c021f0504 77
    0x210313080d00d8042c1007482d148c01e00c0b0010145413502c1d03504001c0d04425070b40c0900084c036600f0341c80507601c1803194070240031074000501884100c4a003442940d000035402030040000c081c9080c0108910346450b00403603d82030b11000c40c142641d200400910b50741c0c0c040707400c110215038140800002e107071507030390190300e024510340f03d03004071006604100340715590b90018182c9080003580a4919155004000e102030811840084d4403211a440f90034058007803070080c00640c1c50048129082021185c4500c41162520303030041000c124504200b6940d514040d0010520343c1e001c02c045050b244500060302c416074248400d032116001c01130f15100006800c0704204000c4080e0725028801d450200b1400a01c80800201c01c8980801d1102c45580102045801140ea280d0f200c100c1c522030401140f0300c0380164072015440a1800c000324120001411410214802d0181074220084900c5940704860601102c07800c003017480780b00303481100090791000f0b00c006000304c071076507d0141410400d0000c01c500d24298 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 147463408 1250 147462158 147462167
    0x2040b030403030c051c0e011503050307110316030803070f0305160815041e0e0f03091903210206060102010e0601030f0212030409050109110405030c0108070201022110090c 76
    0x980002d06140c1ca440721001c001d4403903801e0b00c90203680c1000203510050009610710041a8090300f0010715401c0409245102a07002d498000f02c1e40d20400841c50002991903400b86407620034465581030042d2000c0f803c0c2c6559100000e0091409680020341d6410000c070043d1841032814425000c0c141440104a8100544112946880c41c1c50401110a83e0751f41e08003900c20b2441c40910307030301500d00a00009500c1c040d8407080d1005500240030031500014441a540d201002511401254400c02000c42d0606080c0c0811205d500f031005002d103983c1d142da0784d04100341d60205c0c4e19501400c0c0c010789c1c0e0304c500c0d504025031500130701c0030300080090320417002c200707512003e050102503c90a200074140d03085480d01002250800044419651610745561064014203000c0c0f047c0c1c40f070039080c80700c01c8520048907030466080f541d004004040e41d074000001942c107418002c0550003555800c1c082e140a1451441002c01c0030007030308102c0702061916500c00001e0720615006040814600040440c80c103412 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 147464658 1250 147463408 147463411
    0x16031404120908010e070302122e0f1b080105240313141614090106031d0d0e12010c020c010804050115030c03020108060f0a0501110a0c0e0103020306090102040b03 72
    0x8440c6a00301c41900c901500d205400d5841000c00d0762070006205141000400c00c44141e901c04c446e1101c0300400c030303a401541c41810300000b4503143d10710803211030b00003011160752070f02011390a4049035441300700d2044d800b03c4a0f4105806110013000300301014083e03004040c0c03409040216000c0005140e00c0d000360910280e020725144490b100040800c2d520702e6080d240c001e402f0f50081c0d4843c20405000c03600c0341c84001900c0d1f11002e0020101d00030801c090409010700d40e07480c000d0450041c1d80c0c40c101c4114007030010721981c140f12400084000c0c9040800b400311030090502520350417426050340040c402c3d8040c44040320801d40c1d00d004200c0305c1455020540c508030b940246010241602c1e541081030040510200e88003031440c1d0108000100421011720000b101e000b600c4041c01e554034a81403100d000c200c0c40310746900061030390040c4500d602550007201001422822a0b40300e040c141e44070000e00c0c02e281c1010340c141a80000400c110314040004640c0a18a00000d40c1058903100c071040c000d000 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 147465908 1250 147464658 147464663
    0x103020c19030203120f0601020a08090d170903070509091b060c01020d1a013f050112050c06190507060f1b030c0507020306010315020403140616031404 67
    0x1000181842088010005002840300c1d0154080c401c1d4018940a580e0b07500c01083e5406402d2001d0000b40075103056482c0c14400c40c0306030050f204ca02819950200694070030300304144d01202510510b13010404007a00300201450101495580d15245c0c2c0406240c041aa0b1285219054800c10000940d0011078201d00c0c070b0302c2c9030300d00c800c1e041e03a00000a03800e806840d00b0030249600c00304426444100540000041d03503c071060f0b20380c0c0c1214500c011601030000d44c036401403c0c0e410195000c4d00401036442030480390152202c8046803881070075101c0c21303108203034080301880380380c0602202403040910170003c811a0850360b0038540300613a1070f840c10000542070309505000011070103800b4020541c1010340341c00320540041080c0081030111500a800c05110980003c2c900380d04e80f020f5078000e0044942c038940007001060280e181d0750300d080810322844010440d003902480004001050310341038070781000c1c4581c003419580c5070611006400b05810742040b4109801e1115988502c140c10380b00e190480d8 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 147467158 1250 147465908 147465911
    0x30230060a060c1104140916050d03050319020f07030c02030d03021e0906090a06030e0c030d020309040e120307020303041b03020f040f141f14090c130b030403030e15070e0103 77
    0x48580016005004d050211003007084080100510300c500856200c02948e4215250403506403a4018000941614100280131035810404650201030f0a00f051100404580d005446c1c0b40048074485000d0f00b00c141d01300d01003800d103030000301140750071300c005240e00b9080e01d4114105031141c00403048001b601040441942d000240ea01542d841d00303001c5809503140905000c0c1159038410f4014014074007140100014000c01071965640d00d03000c82c0e05600321206078011420079840d501000018100c02c00d080c5550b2090f482c1021420071a80091031090120390042d54491610341082c154041c00410b0034803641c40800003d10051380c41c040c0310400e060013030360700041000440d03403000004d00ca03c40392005074491510411004035203020114103c0d801e048041c0c40074603522403000781104142100e150717005101100046071405000c0103488a007110725000c0c0621903490050101c9a071083d502580044c1d182d482c000000c590400c0503104907050022030321064036200800428107407000d44200d0405 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 147468408 1250 147467158 147467183
    0x90a0c06120209090c030a0b010e010519020f0a0c06080702011b05030415090606090b01030501151b0b01150908030901120236010206090708070504020703030230060a060c 75
    0x11280d054404a1001a08040c50390402034038005c156007003241c840d80d00714240320340d44049512401408548803410385541d8204800ca2900400b004a400e0300c2c0405c5100c0c18201182000040080c542c0490052140c4040182000001480c10300020a1070080d0fa0400b00c110402d4000303811a1250809903103880e98403501c1d24074241e01c10b070701c1e0041c22888050400c00403400340705003035200b0011604401c0081147d110752400660540d1000d104a1540d020403820414a560080455071447c29403404c4190004980345d80d07220f2080303030a802000505103e162181c88642c1c01000c0f210240c6030100c01903080c9408140028880c081c6824103210164003c11500082c021450261040400d01c200c040c582c0508100340303042405101250a00502c18000451418640481c004080d50f0600e00940a0340e4100801e1002070b510400303041302010b0b420070022000500d45007505081240c01c064600c070703183e4410440300d003200b4007800040c801d1107050010032240b5004181d61110a41c4001b101440c2c = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 147469658 1250 147468408 147468437
    0x2031513171b0615040b0a09020304140d0e0102070902070b15010207080a030e041503020a0311060910052a0c131503080409050a02030606090105090d051014090a0c06 73
    0x28000d22008091008005514100b9144045600ca128442d82041128100c100c403003000282d4109803031140d04041d1542d0203103c40b820507002103903c0b50141849110300004546600c0c170f80700c030004a8400280c040040c0c6541d42d03a042c00305000410035820f081d424800301e80c0b104c299590b070141101d0103a40260110f088203034000c1c4150380081a20105445c0c0300c0c3d10900b80079023011442010719205e1071500c011158070300400030314103040c0c0e900605000c811030b00307540e11185038854081500794402ca0030b002d03e910035614000c80749a0301e000c03039940503211030720281c00200705402c14103e841d01a901c1c05c0b620884110004103000c41540446620101e0a200312000e4000c004c06043c5c504000740a802c04001e0206c81c03401802298141d18007041a03035140e903000000c80c04299901c540c400030801400060390302ca8405480300240041200703200c280103a81d01407a040051090010345502d0b8421510107001c0b01d40e2003644005190041c1620006030b135203520034085c65001e12418410300c500c42c510f0 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 147470908 1250 147469658 147469703
    0xf0807020c030607030617031603050d0e01050103060603020f040603211101020f0301150914041109041b0e03010e03090405040510090f15021206091b03040b0402031513 74
    0x704210040c0c240da03403508103554000e01a02c4240a002c2c2e05400140c41ca81049000000711040400034025100c2400083d55003240d565000c81c0000b00550b80b140400c0104020a1141c0c0d4000d5210b0500021300c030745144117000e81101e5040b540d500c01d0340707040c108001007903400081400414010f070014440c4139440b0001d543e00e45440030300340c13055840400d41210f810700510055040e60a101d03003030600d0101054048818050b103000714505500c3c0ca50f03141040d8106134000c1c03c0c0468101c4503260401c20323035030302040c00c803950825010100c3d1419401c01e9400ba40216030511095407c0d0000d20541c80c10ba080d165692041074280c90080e03035a83d0028060013810300803d2603034004024180300b044e40508007a0712460207014150741e01b0621078102c120400380c81c4203c0320040d92280c5000010369030340d41004441e07203000f400341049121035200c0d940012408002180303e14425001c03d10b1a050500600d813070310542d400d0320384420640905001030a0004160025425480b601c41c01e000e030708143d0300c0300 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 147472158 1250 147470908 147470923
    0x907080a0e03070506010501110307030e010e0a08012306060403020d0209040302150f0a0c050309100906060803040603140f0108120304020d0c06080a0506010f1202071b1e05030604030f080702 84
    0x10740d0101250341410054003003003c0381202e43c01d07613444030f901c219900d43c161a88200d1400402049040c16110099406290103038003609000f465501c00079034030102507007903031a03040c4222515109511075207440c6e0010709807103401c060f0a581c0c99050600715408142c000c00c01c900080d00c00e44c681000a001c2500c01c1002d40d10b55a01c4175020130300c50603c1c01c2e40d8040c601c81a03a00301c1550341090262803403a44a90241e07880750165000901c4240a01c0320504001d060080042d01c0d45900d407400030866a10800c0144004d010a580000702400315142406000d20b01a0007243c600c9074840042280200c0050030001b0040d229140303907500d450f58400958108005100104028010500051025004042944900d10120b07060100ba50791030011500c0214000b144401304003104131090180c0480d5001e0040640702e401c25240c1c0000c0302003462a545143c0c3d01041d40e5010032060801103000414a00004040c10b43c0100030509060b5000381900300d0200340d25082180c502c0000740003e20810400 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 147473408 1250 147472158 147472181
    0x80d20030406170f040c0b07141e010f06060e0112020903070308030601020114060102120a030b09041101021203010609090c0c200316180507050403061a09070302090907080a 76
    0x40781d0392941c49102910450403000c50900c03c0741c00b00001040c0c0c0951002c041c0c495a0b00c2074156a110b0704108900c41c00d60014041500c01500c01c03880b404546104020001b90b6005500750300b507221880e1000242959a00300e910f00c0f03481e041c00170400410ba04884491800c55003401c0a210b903041169441009003d824000b80d45807190384000400d009551004501a0500303a0003400042c43c45021500c3c1d1440641d07020740140e1110b00403022800000001c1c0580e05500d01c0d0114492403110b00140d0300f0041030f80c05a503031001c4031410064540e0100048450201a11245825589000409410a1118814082c019469000700c1031907a2003020760b40c1c03015034404903241d0f0a01c2d00008002800040b030b88214020310460882c11035400099100d174044070209680c0c2428102d0308450b2102510000d80b2040c28054240300c00700c00038200f40950300c1c610185110084008801204000030200060718400901d0303c1084600780ba40c80b0b60f580c9542c04000340c02d08400d5500c6000d1400014068507079034 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 147474658 1250 147473408 147473413
    0x602030106030c03050c0a090504020d060807260f0606040207020103090813051215040f020307150305041208040816030912110310052a1e030702010e07080d20 70
    0x110710590103038000c00f400711030b6681c2001a07580b2403031000c121340f1501d64143d011500d03c84042002d880c054004200b208400c103808140c1d240d80f0f50640b4a03000498000440c9003a01c61210f081040c1204509141011202d0080450020000d000703519800060400c601407900065039105590003030b08a25070543d030200000365100300d0031403040c8034034a8a0056603c030301039031000465507140004517034184c81c0301c0c18120000750b2580d40d0380125005820f1001c0b60103005280c0000341c0217803410414283c01e031007501c020515103401d00c2c21380c2990354614a4401400004003c3c000400e84000a444404425039030307400107140c0301c1c24150340c4030b030ba180e00080701d242001401703404118072182c14110360b6070281d040380d010351800724407072080c0c2c0c004882c0d8504500e4000050701c1141c00741540360710405c001d11181440c00c082000c410b2112065410034a10b40800081444a2140d0901c1810ba1344003c11000d002143d08000c14151240c1000b03020070100304100000d891224581c12103160782c0702e005001c = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 147475908 1250 147474658 147474661
    0x90e1003120f02010606020309030c01031e09150507090f0603020717030717010902090603040b1e0f16020601030803150303040506180306010f0e0c030403031407030b1011030409020901020307060203 87
    0x4014a442c0704084507038010350800c4400145240008103440943d94014041d103c401200001140248500d8007003a981690700310a4003c04001441a8124035001c1c4c40150032081c1001d0300141500c0e4054040001c01c01110400c0011381456052042980e01030b18016940d8020707130030003c4180f05820400d010780704000080c090001c0c1c00c4820441014400c030325120080e030340c624801049001d800071407900290104001030014889a60310b551042842c04035130280030580c01112040141221141a0401e150080c07000840800c4220b810283c4c9920003230100b9070440e03841d03440d640400740060041b00c4030b280d04021582c0e828001e1340d01510001e000b054890f40c20138280c00e44002c00b241114041e0040d100041000044800301c1307815030721100d0030319030f0039110b1642c00d0409500003002a004c0603540d44203500b0090600844500407860b5a8010805000c3c64082100c40003003a03403020248400015000340d02c120205c141e400311161024010b856000c0c1c000140e055225003500100058070010 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 147477158 1250 147475908 147475943
    0xa030807260d0e150412050409060b0403140613020118050d0503041e0303020a08030403050708070b0a050717060906030a15020a0f090302060d0915021614030406090e1003 75
    0x80c00b07040d0500030582c061004100015115440c0c1c0c20401d00007021901c1c040c00113000c14100c610b0001803941510f841460a80d50709030080480c0d9898100081c44480098104107000c0000305140e501841000500b090741400d003400c1d1003040007200c0084c14006040b803918075040c4003240c0300004183c064440c0701e070800359141003a144e5020740070380000302c03030420101c04400355881c0303902003603a034503400800303c080c2203841e5088140c00041040b010008200a900700045150001d00103c521a1030941701c5818504030304ad05451000f0000d80400c82c039941c0c0300c100d50800c198159041001582c44203026100c00e070209040800d4004081c3c078006520300040e540110360f038001c045003422a0307106013103014925001c036a59525444040d500c04028000c40120000c254440511140b081a1001c240090040288140e8000307500411140d40000703004400d00801c1428004c0780c80d4042c01440c50103041c03801c00307407001c245809001421044d10300040c048104010442e40070f160071220810a400405 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 147478408 1250 147477158 147477233
    0x50304060f020c19060c0c0b0112080405060d0c020d180b03180d050301080606010507020a06080a42030209040b150301060f150c03120b0303070b100e0903090a030807 73
    0x4181100d170185850000c03403d2a1060710f40800c104d5000040445591070000300740d64031042c1280a4510010070000042c46039105402444180880301d400704a0104820ac043d091800050700c0009001110f60300c070704048119418101034506a410079a200e44a03900380000009449034001010b204040311201c1c0c1c2ca8010300074504072068202100c02e070390345000c01100d05004486009400111580c01400b24500511f4100e45c000840d00c800142440702e2904d1200300c000807040410a4281194900030744090039a045a15425a00a00c14032070304d55404540b079540001c202410100d40310740810190b0604030071184d9040c2c0010001e21141d40c442e034107010340c00c18504c20845110300048801c000c40b03010340c50f80310720f80382c06880b11030603010481000006040c4440e02c45034140070030403030440000c5405800b14040e00b5010480c00040c0d0600b185000705400c040d102e0f2075107034130600a00517656039000d02d401c10740358040303511901d500c21858001c013100c0c014483c00308184040c190f269401c1096 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 147479658 1250 147478408 147478453
    0xe061504230a1b0f08220f030909060905010302030c0603060a0b030f0106080105100804030e0d06060905011a0403081c0605040f14070905030a2604090902030c060a050304060f020c 79
    0x100e54210300070780c103c0501a5095aa00a4094040b170304080001301d05101d0108441c2d42c9054807500908016020340e180c1030745642100045020440000081c009a111403041e50081c12403450100055415a0002030f5504486003a5610030303080080000c0b0f00f9145c4003804002032841c12030294490404030f0301582d00c1c400034003030100082c0da20000000c5600d04140100c1200c1c142d1384905642c1d448548045030b1040c41c820300030b03400c018030760b043c0b400282d490f01c02c0c40e00030a0b00400010315541407815050512102071303c5074801603418442417001c034541c3d00c100d03802c640c02c02001c1540da902000307002014180c81c0d40550f91061030320041d054280159003025000b08180701d10b442d070541c1e038203030103803000d514500460f609984a95111000540303260f6408001c00300780800100c0000d80c0042144d03099000750400301526071180c5240085003010060740708000002c840050034001c21400040036404018406024161100f810248003030044d411940040c841130151090782a103034041c00c000101 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 147480908 1250 147479658 147479681
    0x1c0207030f03050c0702090402061e03010510051c0c09120501051005040e1504051501031a01062c0a090501091d0109020114030a060906030f02040e061504230a 70
    0x20002400580e080c0b1900c582e510409401c01303580e0804031103409000c1d842c00001c20403a0800804c10000019181403448000440c0701e5a90007030796981404140b004401320300c0315607400e0100070b0249614030781d0100c04803001d94a4000c800191501056412914500715a00c9030f850500175040740c40600c60b040d001a440b0303404101544a0304c80c1d40b04144011101c0702d01c040c1c04c132500f004401c450050031030405990050b0140782110040d080210b01344090f6030080e401242d0840601101d0411610307002d41243c01451a400c20700005059a180743c00502d1000c801601c5083c3c1801b0903902d01d41d01c054000000d0540100c2c2000250313102c0d4900001802c0b204207840c03484141c15031a055658050081000c86503041e51a50f55a111600314400240c00142c510002c1039103803180456542103501c2650011405680c2c1003141c01200e0052104072034442a90444d80d41144d02001011600070102c14485041940d0005007070400c100d0107042011600701c20400d514410080c8a06a002c40e007080c1c0d40d014 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 147482014 1106 147480908 147480917
    0xc0109080c01060608010909020603161106041202010605060c10110f070303020a0f05070f080c0114010f030302010e0a1a1008030d0f150303231c020703 67
    0x4021006051181c3c0d03680d44100700940d8000b40e42801000901d00c10041500320350041105440018500c5001c080400503121840703100e0b03503c403018801e6990aa0b01c0d94241844d20000709001c5881610040d07007443c0c0d0215903440c1000c02c0710704512640000309015201000100301070403400002e600741400038052240c007201080020280f0030302c241c1e030040c6d88825568000d0050310b1800d135440c041241c14482400081d074448030300800170760802180d84d19615042482405006094040000b8046443c0000b13061006400c41009492184c4c0003803100f000803601680d51511408000362040c05c4411038918410300000145030804401d681c1908016240e00d201c2c3c0c41c0d07522004120120039a2134028800c02c035854840c40002804038a80b003105203103140c40042c4844410210303007840c5c4403101031079160f004001040381c038481e812172940705101100141c00002500304003800d90214 = true := by decide +kernel

theorem cover : BRFrame.Cov 147302158 147482014 := by
  have h0 := BRFrame.cov_init 147302158
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 147302158 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 147302158 ≤ n) (h2 : n < 147482014) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
