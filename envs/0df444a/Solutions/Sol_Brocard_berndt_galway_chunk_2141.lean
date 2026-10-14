-- Prove2me | solution 1 for Brocard.berndt_galway_chunk_2141
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-14T05:46:04.16699+00:00
-- url     : https://prove2.me/submissions/0e102e09-b8d1-4276-8f36-f73f43f8dfaf

import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.NumberTheory.Wilson
import Mathlib.FieldTheory.Finite.Basic

/-! Brocard / Berndt-Galway chunk: no `n` with 384892086 ≤ n < 385071942 has `n! + 1` a square.
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

theorem S0 : BRFrame.sub P3 P4 TB 1680 MM 255 384893336 1250 384892086 384892091
    0xa0510110906031611010f090b060904030f1419030c020d0f050403020114040e01030f0b07172d13020f0405040206031f0e07030603020f310603050f0309032406060d 72
    0x85c0302c03000030320480042410011001441010700d08200244207030040c90035020f0480d52040c8001f0036005a134940c00301883d4a80120311442c20f080d50b2881c0e0045150405005d455407044094864041d00a485008102e42c01c4400c3c00020071022034038040840e0800020135810841030015510981c10586007141141c4c00c5498203682e052410b1103883c09038400e441c2c1c030a0f210008e608120111100580001c801e107050700a00c1e2000c00104404c030b002818a0140b000c2071040041009003594042985040450a6070014034203030240707891168107108100d10a500d50030b44200185400c0c07240c14041c940180000b800c4d907803101c40d0000c40b0054992141648a409000000c4c0c40c1c03080a110751203520f00d41d070041303140c0e455841482030134554800098030030500c050744400c0007400060003183c0c05c0c10411003207011003c00c00c2d880c4020011034001401c0da003c0c013a088010604004001e00c00c1c0c1c00240c040f125640f400340e01d200c40d801d40b03882e0060440042d5a0200701c0c1c038030300003001c2d00c1c1e0300c000203100 = true := by decide +kernel

theorem S1 : BRFrame.sub P3 P4 TB 1680 MM 255 384894586 1250 384893336 384893357
    0x12030405060706060501111c110a06090c0609060201021903020702061623011404080a0e03100e19080906070c120c08010c020a0b160507050a05101109060316 69
    0x141da41d0007101d0221901c03a00d40205200030b5a04c0007026850500d4040145400c5c03c20002c1041c501d40302100d07031000c10440150320f200c1014204189140b080e000042000302188034240300b04003039454000e41e000b00703441c40c40002d80144144210349505190301140c940e00040c0b04030807030107507110100581c3c0c44607007400030a80d0340240000030052588079440c91580c5000c4a44101d02c503401c40d91f440002a494102d41400540b41d018107941d0003540428a980c0e00c641c0300c0c8050b181c4840340d038241074040c4211903103031220300e040c4c1c1c0c03122048a11200407640b409880c0031210700608504c050042451070248000100f85c18400080c0000300e00c102d8121b012a41c80341100026038003003030700035640c8410080041040d40720a102d404924103243c070240c40241d1072920b0b81c00051101510b07000400c1c0030814007400c00f601c100141c07480603a1000640300304400030700b00035650f08000404400780b14900f00b12004000e4022084a1100c6005058142503684094a810301402c0f031a9084060040d810603 = true := by decide +kernel

theorem S2 : BRFrame.sub P3 P4 TB 1680 MM 255 384895836 1250 384894586 384894589
    0x10e06040e0f100612030203070b18010c0201050603161a07030e0d030507170a2a02040212100f050916020a02040f09031211040b0f0c070e010602151512030405 70
    0x1d42c1c028110307008103070142d2600114400d45083e80d002801c030600c403010060100b43e01104403044590041492011501c810300400d20207480408a4a1154a805a403050496040d03700714050340c0c08404541d071a010074020104081c0340c2d807080ca000c1d8000c03c1c800003409a1448003400046000b0b00f0922412001030000c10110240310004500041d000200d50040000381d038004a140d41c9045092420a012958081c1c2002c5c01128455000e401109000816000c964001180554043e00540d01c50724000040503010209031418961012104070100780e0400e9015084220380d002480c910175a05d03610080c3e0309050030b060004e0114000c2c0e240c00005625940500060002c400314002558481c504009002e46402110001e055080c500802c481910b01800d544c20380718140c454030342c0c2c0c1c0e0882040801521918100c4e080c1c41c01603150008035005181c080d24104c40340c0760240c4005540d5220b00380410402194200344001035200074203083c0c240245200c1c02c281010080704e2400761960f0 = true := by decide +kernel

theorem S3 : BRFrame.sub P3 P4 TB 1680 MM 255 384897086 1250 384895836 384895843
    0x10e01061401080a05061c0501061509050a0e0906040f031826010204030f020423090304060f0507020a06030b0d0803010905010f0609060e040c030f020a12150e010e06040e 75
    0x30058801074108400d89a02941e01c0903106600c00c405103010403680c10181c0c001040001c8080020025081d01c440c1e0409010f020343c8004010300d04101114151040e404010302034001c40d1103000c2c82103c00a4002a9001450410910450703810011b8816650343c1e0b6900e07910052801001e804100b00d00380711440e8401940582409400e522000866501440001503a66041c40c83e1303140507640140004c00016000f00220f0f0f45a9a04880209010440c03d46000c0c1001494100f00c440c2c007207040a100426101000500a41d40c0300d94882d81c02c802c1540c4240c0d820f10405c000250080c41052040240c6403003a0300c0220010401000510510b101d600d4416180e04280c100f1914580c0d1800100191054440800021f00c0d4a04000940724030b0200080d01c160100013855008035102c0c410f40c1d0940d8840c0c1d0000344000d803d04c0045441e0500354800422950015207904079039450118014400089103881104a5400f14114412a0308096003201400310240ca020b40080c1c4400e80305103603003401d0 = true := by decide +kernel

theorem S4 : BRFrame.sub P3 P4 TB 1680 MM 255 384898336 1250 384897086 384897089
    0x4020402130308030f090c0109031e11100c03030506090f15010e04020f0c01060e0c0f1615050603011103090d05070503091807080601050403080a0c02120d031a090f04030809010e0106 80
    0x503c5a21720b0700b080c848060402c58110314490500810440c100f002036541e015580c020460f40d243c029614a031420f02203482c0840d004555030040d001c40304001240d4000808000a0b406030380d003004a550340c403051201900c410303500654000b19120014040100070860441c46103010302d000d280b2181c2c0134000c20282d80201c0d11a000c1000041484001d03200e0074820400201036000b0004058188032002002c1c602c106a082954188001036420754082201502c8d410940d10104035400d250041c8000e400130702082e00c03010b00c0b80d420001039054450103042503e001e00001006841d035510b1000f01640d1540c03082c03904071395501003445042c056a80702d07c11040c0214a108041c1c23400e01e41480000c1940c14010105818007400780414000b142207001600c0c41400e00d0304001460092030b000180941c0004960800350344541d80391601d20756850303000581419000030301030054800c020308003c0c1900302251070242c2c24094000003000703e4821519160001c080e440001401d55803034000d81c1c01e50f40507 = true := by decide +kernel

theorem S5 : BRFrame.sub P3 P4 TB 1680 MM 255 384899586 1250 384898336 384898351
    0x1805030a0c1506060c030521010303050316080c1602041d03030403091502060609061c03020d182d030804030b04030e0402030405150901331d0402040213030803 70
    0x4064078401882182003041140b804200c2c2d00700107032810442c02900b4820156000b404011000c00c0c00d00d403250620b11b41846071102641a00220b6030b40b403600400b41e60044500300344000e000252424076078060300c1d00c0c602800d800c0700c1d154105100c03c0c0314103400705400d21044c2d0340301c0c0d03e03001c1c0600381c00400d81c043c036400d035040400385640b803a15082c054002c4607117a1001c0480d650102c8942115a4003007041a00b11004031204000380e01d41c040007800104000141c40c01104151140303104058001070540c6a034140e40d00d2340080440400003038207800712a80320b240161144e81441594401da080c0392010022000a141c0380c075151291215112504150021241840307080d00b80004d06820a45801084808032811751652505907645e90311040206c0040709080d00040109181d008203400429402070600c4241203000000081300300c06c22001c3d600d0211103156083c01040800c00d061840b200c05010128540b05500c4950038030000707500240d402108041d19540201c0054405030003103014005 = true := by decide +kernel

theorem S6 : BRFrame.sub P3 P4 TB 1680 MM 255 384900836 1250 384899586 384899597
    0x91509070603050f0123010309120c031803080f030a23040201140f0702010f0203093001060e0f0a0209040e060601090b1305090c04030611190305070903061805030a 72
    0x7014000307000c581c1d02514600203481880010011000304041e1304080707900074110b500d040703d0200d0040e0003034107620303600801607406244030301c03500d507030081000d982c45000b6a10b42d01d01482c50090082c10ba281800003514800d000c205441e010500140250341207000310b64001140807211550103207104014840c0007400f02e112003408195a072010100740d208940100841c40c217080c0c00764401e11031085840081c144402c084039006154024015515801c4003d03180300210b90442020705000711414040080586c81c8204040011005210714030a644583c0e000700d003507842c1d4400c160903200c4002c01000303096400f04811003060b00c0b2801080ca1040c0080018450340c01c10100141580c3c03003640044080a00c2402091040e115040d119070841c0c4060380d40088603203d01c4400c151a02c80c40d04060000c504104000203041281001003003121186454178400c000700d820102c06450055940700b0000740c3e4a1801d0012500981c050300102401c0461404203498035565107045410020000000c1070 = true := by decide +kernel

theorem S7 : BRFrame.sub P3 P4 TB 1680 MM 255 384902086 1250 384900836 384900839
    0xf16090509010b010c110f040608030406021b010207050d080712080f0a151208090d080901081609180e0f0606030706051603030e0a08030c03060a06020c01120509150907 74
    0x94180192034008503584000c1c003d214042000800b41d400ba0800030307203400203080c0f018045845c1d0700e44010500d86c000e40203201c03868a84000507138a902c90b210b00d00c0141300e41d250100140c64440440035503404141c1c003074103006180004001400e90301c0303101074400d80310800c154400106003550815954035240c5642d181864440e026004c8040001c1500400a040242c920030b11044a00c113401500c04500466944c4201e13400c0182c9070340940e1100c15041048003400d40144102074019128822090340c61600d00d641d040d485001110082d00c940c0c010a0b9036030414002c0071170341c40007117400c220401c0000036000381100650b85041000079241f01c0f5a0094010700007903080906c4000064103c41c18858540304602842025240c145140030f810140e0b58024510f0000b0240089000142c0180b4155202e040c03030750300c80b00203500035504548500020040020400c0c008240e5000214050b1120140965030091400c060000207103c241c080c010041e0b030140003204c2c0442036004140031001003801c036 = true := by decide +kernel

theorem S8 : BRFrame.sub P3 P4 TB 1680 MM 255 384903336 1250 384902086 384902099
    0xa0905191515360f030f02031e03030a09060e0109060506090a20091507050607090905010509041211012a0503060a0b0703090f032109080d030b030f16 66
    0xc110000000c1086912081ca0180c507810b0070212283c21034501456801d0907840041c0d115204a0750040901c0703c441d441d0010511524102c110020750084044e01c03021026002d25880c56056071108070f8468005100142c0f0144080c0d20006c80c6030b00400d00480c01d14001380340349003125020602102c03c07a9480342406028200300501aa10400b00801040b07290510049410b13501c030b42c24400458184001803003a100e0701c481082205441c044040240c44030715038544a5140c6030201c0350ba000082001d0300025002c102c4e409114100c0f400501003c0b00d90311a501c0381c08c1c400042c01020000d00c03030303500691a1020300900c1440e12a90b40300c07102d00c3c50702c80e00084140d004492040182c0400c0350500900c20140c0d02c60b2060811140d848050682d5101170b880d040e82d540d0000d6000da000140c86046c00401c0c004000b071070120560701084151000285901c0a4402100c00e008041241c0e00c528000d1580341d00a5110080c0203d000b400c0f244c0c41240c1c6e007240b071320344130041c05540300d035a9604408000301d = true := by decide +kernel

theorem S9 : BRFrame.sub P3 P4 TB 1680 MM 255 384904586 1250 384903336 384903359
    0x60c09050f0d1709060f03090607091a092d09060a03030f050d060b0d0e010b0a03030e1c050706031b113a0207060e0604050a09051915 59
    0x2612049540740c0401400e040040d491420110000e420540803001c0740c80700d43c03096401c454108801030602030320340340d0103120300400d504201e404980f079000b24030001d050284105034003c240c41401080c000002c01820030b040b241d070801d035a501d802c0b5a021901d41c00301618800c4003103d0a000d020507080e1303042803034188808600081c1c0800d006032400300047c40040e0300003107003078805c1c9139a140032038a60580803113220141400e6400314070b0302240003d0784416030556803c1420800b130300000a00418213002c05110b8140b5072840081c0000301640d607011040d15003ca4007646c801c00341e00146c052080b05848441c10120143c2c040c00c01710f86c0c0c03000202550b00d00b4003088800e100c00750030440380c0031b010002056101c07021075031200c00615601d0301c8901118007841003584c101010004070000f01c0513504000c1d40c0c90041d4040c02002c40c01c0f040e00a103140c0b900303004650a640e40580040307456403400c0201c0d0064031020380f204d010507006402c0c00c2d0544480e4844c03d50800c080e1003440398514a000d110210307 = true := by decide +kernel

theorem S10 : BRFrame.sub P3 P4 TB 1680 MM 255 384905836 1250 384904586 384904589
    0x7050f090411091c110f0d0f0605061f1d01020102040e0f040b0c04080d261e0a1e0b0a0b03070e0a05040623030f0d1119030f030b1309060c09 62
    0x418112a100040102e03524200c2c0e40c00151060720001c0c6c400e043c80c00011a0b624441c4001443c0940300301941043c0441d50388030904c01c00081c0d40804c515521018200403403a43c086103140011000010520a15461160341410140600000d0304294071410141f03080d00d0115503520240d81c1d605c08100038840784880180c1c2005484100c1d503e4582001006500c0f41d844000000502801c07404100c8240f10186044e181d5030f140d40d92802d0a03040c401c648001b42ca51041e03021600508c203002251102581d48103210407040040c0c16450b6042900158201800c060307840c060b80300420300400110109401e00840c0700e41010354030544001084001c00106a80940186024510307145042c810841034021300e800240d100c0c081740c9007182461001a180400311400d0810901a040c41882c120386c11039065030005503450250f450204900007403410b0302d90b0a00000d800580d0100365000c43c1400b81e8482d11150101a1054410040030382c4001d007690280403089903426a13550074100b095034030100000 = true := by decide +kernel

theorem S11 : BRFrame.sub P3 P4 TB 1680 MM 255 384907086 1250 384905836 384905869
    0x16050109050306010e07120903030c18080d140409060b030108150103020604180b0406090c02060108010b01090510031103071205060a030b01260105040501090c0b03070807050f09041109 81
    0x40c841428080070030364843c0c050180d03a020f90403800224041c00d00441c6818205a14410700b03111058030ba250003400f40100d0220800402d441ca1000c0c00200c41c004c418006032421100184000c0c0c811010071508074074000300c241e442060410001c2100400c50150030080c00d1042c4001e9500d524207140c0700c0c130f082403142e402e1070340c514000f00500040c0c1c2d50b14104d90450300000d445070710300d00c060074001004151101c8e81d184d00c1840c2490002d420701e002d401500d6070f242c2c19003d9482c160703640c82410342640d01d94a441c0d800521402001e001500e002c0764030101020552400085000ae0a000700c04964026600400800c050505010000c00031b030103aa94081c00913519213044600c5c50356a00d001560600550f007141c6c41f00341c40d01e04d039027444c9d03603034000d031055120002c0c0701c1400c2c00c1c20401e0007800d07a004c040c0c860121a007030102d04c5400713080459000b480b140c0e58800c1d099491450881e5590000e0038070b0180c00301c040100e420300d990f860103a0700000c3d02c840170080d0f88201070000c10000c8401d116400 = true := by decide +kernel

theorem S12 : BRFrame.sub P3 P4 TB 1680 MM 255 384908336 1250 384907086 384907097
    0x3180303050f1b0d050939030606101115130c080d080402060a030225020301050c18040203060a0b0c0615040e2a09090f0c010507050607030902060f0a02160501 70
    0x72070240744200700b5102c52030080c0e90040345c2ca8580003900390a000a800e00c0314504180018443c4e00340040c0e200000420008000e004c40f0302c94080709041d291035085031004d4111900a0445a50512032180c91003d582c2c02d50548024068800002480c010180c45880c0c2e42c000c41818a0305200711543d8403801840048010201c06019500180c41b4060040003c1e2080c000802c04560b40350003501194501d61802c0303043e032061213803541c20300d041c2801c02748242d02070361030000024462002c1100718ac00e0b01a0b00492003503016500300c10440a5400105003680000e5607420000d0b5802c4100702030100400c3e1700c80030b00181e1401e55481c0c00104207080485200ba42020100300d0074906c04a500152418404c01d01d41410306005107a42c5503541d105507854004100a04200b04070340c02244034814070b40304405403030085956400440d0107011b0307500c000c4c00e01d811540104880600076404404802c2c8003034044e82c2080807100d03a0084039040244c880d80543c00c004d110f803140700c8240d18020098042428403 = true := by decide +kernel

theorem S13 : BRFrame.sub P3 P4 TB 1680 MM 255 384909586 1250 384908336 384908371
    0x3020d03090317092d120a1403040204021315030c0e0d03180e010f0f0f060503150d080c01020703090803071a07020c1314060108010b0f0a03180303050f 67
    0x801041d2034500c072003000c1c8403140100d06080824441704111000d002c06007808030341c40e410480a00d0480c000868841c0c0581000c0d007220101000407904000d0682d5603540060418404000165001402c201da00980c20407800414011001130100101441d0071449000000c981c000f90980e80312072400f10130030416040618040e55041207030503900d90107140c0b40e0540105c2e403083d102c1240c19131304045020f28000000241514803030500b10b0559030540c85803120030b56992102c14007800c082c000d204c0410303010720000d07540c102c0031010444801c500500c03182200c1e83d191a01c8943d0341c010401042c2c0b50350001844000c2c107070003000800090410b1700c000c52a010007038850041d050785217800200d241c01c0074800705419901c00c0201e07404004004003c80c00140103245010002c10b80d480040781d1544003903000800ca5802441c079141207c030903004462428905092440d030942c45001d0440c18190f81d001c5840c1d003a2041c0286981d640e100c0c1d03c0c002418184500244181800140141e91b800c084114 = true := by decide +kernel

theorem S14 : BRFrame.sub P3 P4 TB 1680 MM 255 384910836 1250 384909586 384909593
    0x102120619120c140d05120c071205030705101a22091103070509010509040206090d051f050606091305130f1a0c07030203040303180803030403030f0606020f0a02060a0311040f0303020d0309 83
    0x1140d1003c07c4a2082291301c4035568410b4a0500d100343c1c0c0b004102c0c000300e8540900b800030200040c03000a104400300c914803200007102d0300654054150500b2100a0720800510b28109002d10b1001d11948240204549150310301c41c504a540310300c4282c031941204403214025007406c0029001500301212410101e61400c00003419281004000078041c41c00441c41e88030356121071088a000b168000b040e07600745000d4910250b00b82681c5194071003118140300104480c4d060100c01c032401f811003c0c102c8142441e44c146420082d00c0058011861041f104142e4000f050b120a500c402c804d11411403602da02c03080007a40070210002a00e0090081820031140c03001030340005c06c41c1d08503076040c201411844062880d1182414441c0c0c0940c01c0c5000020411040681c540d00041000132800d40400031203803100000c81e03a40070608181415507000c4490080036150075405804905014030f00407406401c080c469851035045503010101c0d00c00c01c40341c2441050f405203c1011024a2480d040114900170349 = true := by decide +kernel

theorem S15 : BRFrame.sub P3 P4 TB 1680 MM 255 384912086 1250 384910836 384910843
    0xf08031311150d02070515040b0601020105011d0412050f0403060e01060e0606041e0e092103190b04150303050c0613080715091b06110102120619120c140d05 69
    0x3030303c900515034009410710410000703004903140d40003698160342c064940390034429006030007211814010351801d07002244031078441440000c54100c1700d00c400b0b03040d40c41e55104807083c0d00302090781d03091013000e00c52002400300711801080514445c94000c5003501200305041d0070360f000c41c4c01c0000d8400d0f00404202c56602c0d544103031001c0780d0301101c04080c0500c101804641c807039600e4000302e2100707000383c0030019058400140d00300d10070a41c904a0f00503505200c20501240401c0c0c1e007040b03039070141044082c0d0314200f42d044204030040c000c0001442e5044120443c1d00e030900765000f01e0225070042001d4652500502500d5401503060190550300c07140c5644070b2039507126250004000d4031181e10400c8440295070f001034900d9070702415a10030f02106200035142d500301031043d41d0020b4204052401c12280600980c0d04007004100281125110513040011420100b81262004203111200080d500d942c065410302c524007950701884450700700311058541c00040500140103070000c008000010b14000f = true := by decide +kernel

theorem S16 : BRFrame.sub P3 P4 TB 1680 MM 255 384913336 1250 384912086 384912097
    0x2010516080c0703050702030105152713030e09010e07020f070b12040807060501091a06190f050c010c0306090c0c030f080c0c15070206060a0f030209040f0803131115 73
    0x404a558442943c0307130681c1c0038021400003940541c0380400f0420f054031f4043c1a12900c00302182c1d07101000c44082490380400b00c07000a407d0f4980090404165044034a0503110406486410481880c0c81180086802a203090b80411f0049001c03000340b1074415018041000c0200e42c03800a02905030034102e0050703280c0301e00c41103d1401d10b0944005018400c00a054900550f4005018041565615001c4024183e00e8140b05030080114404d080c2c285071070002c51300804030700c10842088134550741043d202c0c00b5856812500f480800c108a00d0070f404213101e40050030b8059200040e8680c2003403000400c94403401c50704000d02c611024440086904804200fa0b0503c507898840c103d69605040d8101c1e0303000340910003030681f03e02c4950061342402d9010307151107040a5800c071520b40e992041007010346005482140d913102c010030000d102505040c2034880e44540582011242660f0b03949e910000740d03004039140f081c040340c0f200c6d0403000c102100705420101801100d03070a407603c685c219000c60500c103e = true := by decide +kernel

theorem S17 : BRFrame.sub P3 P4 TB 1680 MM 255 384914586 1250 384913336 384913351
    0xa0509040c23031b0f1806040905070b030a05151c12050d0204080a020f0f09010902070206120703090c090507050f03100b0a1205010e010f0e04050a020915010201051608 74
    0x40748000d06060b04081c00720591903201a003600c20101e104511000b0082241c40e884c0c0c03107030f0380c03c2401c05030500f420010fa01409018102c90740b01500d50303a050100070001c2e100c003500d190250050100b488034030900114054010140c0c0011103203442c42c40c00d02018045004288140c1544070040300c40744038042d00506840c1c01030184145003481c0c11b0155000d200314039190304414008500020983c0e000f1640e40c1080d0300075581c0e6000a888081001010200305030740a034084400070051008060650281041a1016143d02d1401201c50100007070742e60106c400e01c000a443d61030f06410421018824401010320b05400e0205c0d041c55800030340180206140c2480b607c41c0400080c405110b5190a0001003d40c00c45081e82c84060040007041e40c030500b000c0c5030369141000c1c00040c0c0ea4000c60300703c6c0d048804071018405054100404840b1001d4054425942486204600800340e079884c15000d0090441280e010181d9940c21b00280c2580c100511030000c0300d100341c20781810b1581011610b40d00004 = true := by decide +kernel

theorem S18 : BRFrame.sub P3 P4 TB 1680 MM 255 384915836 1250 384914586 384914609
    0x90504120e04090212030706050c0a0c140a0c030c061704030806040b0a050402030a24050f01030b0103020c0607091508090c09040201020f1605040b06070f030503180a0506060a0509040c 81
    0x344001c038005091000f4040d601000055103012042c4000c0010b01050303000d104148442d41d10f2200c96038251282c7c520b60800100704000840209100307440410030b9a010300c094640c103c8285d16400301b030050701d80041e40c1d05002000c04211a5410030914003810740c0f0341007440241e2826480103002d04000514043c0103645400c400841030703441c0c02400380a0f020040086445c0c1c00c0c070b02c207507070b0040505240c0b401e00d0030903520722021070b203c00d800c1d08400c450300280141d02c008109001103011b4410b1050303090603d43c00340074413680313844240401e80c440c40c0d1075582c030042035103030a00000e2504078495454092100113010301248801c00b041503040c146081e200410591141e100407450320030011049060b50180040c00b88a80030215070314011680121400c0c482c841d0202d003000b00a1007061390091042003041c007105c000a0081d000396031f000840c10300c0e010360241da01c032156050a04030082100e1700e400c02c600b0499289445509180500f03025184a10b20f071a1a60700c5101800440c00307031307524445 = true := by decide +kernel

theorem S19 : BRFrame.sub P3 P4 TB 1680 MM 255 384917086 1250 384915836 384915857
    0x21c0c02012a02030307210216140a051f0306092f0f1303020108010501090e0a0e030c0a050a150506060409020f090a120b07110307060e010f05040309080709050412 72
    0x2c019249501c0780ca0340c041c0c200c079540ca90a080c0729203c0c4003c0780d2100d0003c0e11038000402054400224180400c61041010f04001d01d800032603010280e10a600d190440c0d1110000207641d07450522410066082c814048101c0b0b210542c001c1c02c46103d9001003815500c1d00c070910140510310003204000d844000c1c0b2526801042400103000383c001c40c010030782040000944801101c51080365002200d00c01e807208075050340ca403801900c41840034000d0030400e80c507410000340040c0b46500130700000c400030010b480c034014032854840d041041f403500990311580301402d201c0412480384070022015541000400280c240200056002c1c4180c0c82021040741d004034001410701415021a00d00207401044040c6071079991180e40000d02180740d0685c2d00045100c009103415000e103410f1442000300d103002c0c51038003019a030b401d001480e031000069038942d0b0325101440244000e114180c01107010fa10b418201c50301d010381081c80e201403a0000001141808140000107581d00c01c5001e1503121804e0500104c03 = true := by decide +kernel

theorem S20 : BRFrame.sub P3 P4 TB 1680 MM 255 384918336 1250 384917086 384917147
    0x51e010305150406180f0c0f0305060a09060906050102060a02090108131b060309050607030b0306011e080d050715110a050d02120a0b04061e0504090c0f06021c0c0201 73
    0x80e01000c0582e03070700c5032a00d070300000c05036101114906413a44621050041001b61140c4a0403107011138841c4c00031888074800c03030342a07a10907401243d0001e002400c2d080c50b40d845503130020450300b9541002594640e1140b0a10039503804002a96000c503034040c05500d0002940002800400094005480b10320402c0c110001c20203a0381e40d1101c08200d45104400e915a0352100901401c41200c0c2070f20385004240220700f1007031007400745180f048805801800780c0d1b481c0482c03d00d2800e0b62400118000284041c011440a00c14000320506075031568440303488141074103000301c1c24030000c83e15460243c81c0445a40c242c45c00c07201640c00340c00c0d99081664440c035000000401910926910080f4100100100144501c180d48814444507003a1802c0000759111101f0200c00160b66a0204005060010800c12440c054001c1120320f03114031440c0b0000d5a0b60341101d0074002c0b00341c0101c0b01580080005803019005000d03001642280f501d4258055100341d00080c1a17082c0e281000020030510003004c0d5090b = true := by decide +kernel

theorem S21 : BRFrame.sub P3 P4 TB 1680 MM 255 384919586 1250 384918336 384918361
    0x7080c1f11100c03180f0803070507230d0801081b210d0905040b06030c281e03182a1217072d0206040b0c07051e010305 53
    0x340d442000b5a8500c155000d8240020300d0006404008030345843e1005405503004100c118199034005400300302040c80d82c68a5006400003011031080203800c11214000400060300c0600f14030040028200000321009814140241160440100b0010f040100081d410004003048800c2c0c844040e500c45030703030031000314100ba0500781d1b03001100c2a1100003406060000180192012000e40d2920b41319601d8500700426180381c2d07840c3c4c1d03a00100500210300d601303241e64010302803008000d20381c0d0300d06a40c40c450038808500000841002ca143d05070421a1201d01c2c41601801c0140c51400304460b038031055000c00752940183c0c0c00340410002010450408640e20b0310222248140d080d1402c80ba951240e01e40552401d6680c00c84010b074203180c050401100403c29100c9081d07101040040814003910701ca5040345010502200b0449a8500c0300003685412000307201806044048558403004400ca4515114035548814002c240707241c41080041e400c03c002c039424920903e008212a164003003180103 = true := by decide +kernel

theorem S22 : BRFrame.sub P3 P4 TB 1680 MM 255 384920836 1250 384919586 384919607
    0xb0f090a0c03050d02010e0c0a23092a04210c0e0c04090609020702090714091f031415010c03022104050108010617130213150807080c1f 60
    0x111070741c0c10100c1444000500000d1201c500d0303000f030004d40e00c0070910a032a248000d40301900706206080a004208003182510b100c0f00c070000c0101e181c40c41c00c0c00007450428007904c5e81d28407140a403600300000215000040f081a1490410364502803420f4401c00c505030b00405901450b00010280c5410000041c8508008010341410a000c50604112505403035201d480b50b4000b039490b100b800a09046d050082d10b0480340c000b00280102e81d030755074003600d51200e104076440481c00c040200c4666541ca401345a0030241a036070000c000301c60390307074001740484031a95094110514001e040000c0616801288190361000f883c05208030f90941c5000da14210361607109010325103004195050031850100680200c403400d03612144d4590340e038002600d00c070101407071162400301e11000003003141c00c015515002852024000604d1841c10841141c01c03218403400904819090074820801036104012000c0a4003250001c0c06841d402d0000040080191044035000f09020f0105160f565024941051 = true := by decide +kernel

theorem S23 : BRFrame.sub P3 P4 TB 1680 MM 255 384922086 1250 384920836 384920843
    0x1504021e03031c0b030708010504350f07030908010203090c1e03011b14040e0103081813060312020c010806040b01020115030501020c070f0303051b03040f09021c090b0f090a 76
    0x1101140c4503003043c0282c129000311601034802c885000405400500820f070190b500f280c418050307113040654401c0d25a000c082c1c0c880d0b001c0e031a1030040d00c82c250214002d00f217610418544a4031500c079803400504030906648200400d80c010300c1442034041e030120b9410401d4800311140720382c103a41224402844101815115072552a100c0c11010b6951a080b00340383c40122a500c000c0e4101c00c06411800f80d0056020303032800c60180781e0040c8006192200203014464401c4010705041c0719034000204481c04107868404d034aa10b601381001017144002200000128600252800003245030000300012b00c0100405d200d55290901c11031540d000b1752060321400523040704018040d45034103100b1b02039402a6842c0516210700040042c07407800aa4460042da981590f0321403610000c0c03000c040e0310410081c03003c502030100300700018524218050340c00051070075080268485642420814100644504c0d50301d4035400e208901001031032031404141c0c000b05601e54000c29407100c0c1c0c0c2041c43c0c01385010004 = true := by decide +kernel

theorem S24 : BRFrame.sub P3 P4 TB 1680 MM 255 384923336 1250 384922086 384922117
    0x6070305060d0209070c210c1e24060b0a0e0f150906030a0906240918030513080d020c0418032f0a0812130201020d030c02010f0204171504021e0303 65
    0xf8034945510140c0c288c03040d800355011745c101e6102035041e01001d440c0c440020344070500e8085100170f1944040c3d48800041e00309200400c49941769001c54109601500110011810212185034141055100c05c0d1501c0000c58006001c0d145c0a11520740c03034071070002101c0c0b16142c0007000039148102c41e0701180c46160498400c00001103280020030309490381501c201401e020b100ea0000301e00c030781401204032402e00c580f192421450582d8040d24603801101212245c04c01d0044045500c0104200d04107443c49107a00908803034a040d4280811038040081c10400305900c4a8104013080e00800d80c1d0380285a2107198150320030500c0080c3d242c1c1000500382504a0040c10807410900045a01401d00615043c0806400d81c59016001c10404001c0c00000c3c00360704040140f45800d4000e034840480358025000104007002c01a44900403a44190003410325960420700c1c00700f032200d041001c2d0303921844410340c081160034580c0020b0031a0644031385200180c040c02d01e0070180341d00c050041c2c541c110b4400002 = true := by decide +kernel

theorem S25 : BRFrame.sub P3 P4 TB 1680 MM 255 384924586 1250 384923336 384923393
    0x1b0606060810090908070204180b09030306040c0e0a030201050903100203070c02040f0c020a021917060103120206010b040e040f0609050a170f07110a08060906070305060d0209070c 79
    0xe04a10381501c0000ea031801c2c044022078110742c948500d4450640c0440020302d0803186500780000b0300104076094001022140b8080007007500a03600a11031a418800395a8074a480703010001250703504010741e802c00c0010070407000c841e01c458405605490f02420b003191185404c00c00a031030035001034401d090590000c010b00080d15001005941940e108680912411860b500d5141c12690a031300444010303448150300601600340f19401800e5224100c24200105881e1036900b0740e800362010014003582c0c000303001041404244034400f0000c660354030181c120355141500c43c4240d07000d540542e49295024401150400c00c800070394122042d844042404000007500380b141d154031034008240c81d2400307078002c0f1a50341c8600604551110030741d03441c42070a200d500d80b10f102070040b0305500740b40c102500e210f0200ea40303c02000700c18885e60150008001600d0f0004008090b11001381820740598002e01700040141d03120000c443d8081c02c070f0710f04184204114240f2008040100d680c6001114140c2c14 = true := by decide +kernel

theorem S26 : BRFrame.sub P3 P4 TB 1680 MM 255 384925836 1250 384924586 384924599
    0x60e0304080601090b060313060906020d020708030a1406060a030c02070504181103011116110306090a140703031d030a060c0f021b0306010e0903121008100504080a1b0606 75
    0x2d6042c100c8560640400c44c88141c201400310070702c000c40e02e48d600100441201000200c666100d00455030042038014205401c1c8039600c012640001c4080e00c2d105004010446d50b00118054040c070200c07950041801400d152000c100c0c90f0048040c81c6080c991500c4400c0c3c00248200448001800020014481c0061100345160441c4202c00700340d440151410b8968594141400780d4403482d2500c0d50464585007541c2d0406280840ac2c00d0300b10b440c2540506610340c1603408000c0780340122503981c00344c000740c0e41a1800d850050301d0310903820610b403c01c5d103040021a4010321194114480d0500c0c8203005c11050340024207008814400a1000340b8141500c0312035544107a900020345c0d00ea8080f0b480300c8040d010180c1041a01c2060940d059010600501c041590440704513004821081101c0c2401552940c0441c03103403040f104c3d500c5400349550b00300300742442009035605030b40341000208080e080c90f8558440c180b191008040030301569214820040300400c2c080404160410010082c9507100c00 = true := by decide +kernel

theorem S27 : BRFrame.sub P3 P4 TB 1680 MM 255 384927086 1250 384925836 384925843
    0xa030f1109041b09050402070203070b030f16080403020c0108091e1c05030108191b090b0f010e0306042a0f0602060105030d080f13050a032f1207060e030408 69
    0x41a46000b10f1514030038002c0030007100380100d0351001c1510385402c2980b400c810403020b5404030304100d03018041c1c2c460001d50300411001540c015103084800034550b1803c00780d07603002009501c18a4007004510818800032030340200d2500941e20003842c214020303580d4110306501d4800b814110345011002d40c00f1310042c403040450291013241c20300030240c00040d0510f030204d901d40001e000302003403a000b000c4d0180d45105212207100e0a0b511441071510b504910040c2203000c1c0304154050810b490301c1e0724000026250402c100b80030340d41c00742003440360100d100000c642c0d1000c1c0100020b044640c1c03400c5900743c0418032070040e841c204000d10154650758a90082c40092465072180c1c0f000752041c54000309540c50007143c0849031045950722007495507200300e2100c0195030090710703480d2071a90100031940410030501043c01a140280c8a032261a015140d4480100408041c45604c9101e8000b035034800500120f0360030a50380002c084035480f6021030034014001c04140101c1c0c170140c80700040c0021a1000403 = true := by decide +kernel

theorem S28 : BRFrame.sub P3 P4 TB 1680 MM 255 384928336 1250 384927086 384927097
    0xf09030f060203132a0614270a060306080607030515040f0615091a0a021513080403060b0906041a150c06040f03021c0e0105070501110c07141804080a030f11 69
    0x1103c0095601d0303076070103054034554500d42116000003804c0c85220544010704100c0030f500f040e24405008c0e29044680851401504c40d007103035000945860003441048010001a03402a07001d140401c00c0c0d280c020640404400380c0203100c3d1080d503c82009014401c1180c10102c007a05440c00420440c2003164000f40c4101040d00c260940f0480e000c85107160940e0003426951640015005008dc111044240e4032800500034220001e58041241300c002090070000684091841140c000490900c44400c00c640014000c080a1095041807050031062074403410b400140e56050340c4225140d94006101541c50250503490202441044200030600190b5940140b1441c003d07001d44456426400642d0034442d0a05039070404100107803058001944180e00402542d0700800c00040d101841d00b6051a26074401031216116501c4654203005200002158600c00542101c10601c440081e80d03100c0d500c2c01001707002811101000c15410b444501130307008115071600c54581004550590038140c46c1d40c1e04807 = true := by decide +kernel

theorem S29 : BRFrame.sub P3 P4 TB 1680 MM 255 384929586 1250 384928336 384928403
    0x1e16061503020a080703051c03181505100503070909080702180609091507080403020f0106080d0908011512150615030f0207020a030b0604020f03011202010f09030f06020313 76
    0x261000044c0c203000208052050b039401401500d20900f41059190f00307207140d06258820150364011032195808031000e845119482031002402200341d000d601c00603208050040b005052a880081009035000940c3c0402c8540c2c48401064003813882c20264054001d03901d01a401074029040c911408046100642c45000e0458000c250740c1c681010b2141e079100ac000600503074100d1103000c18200780c0500300ba47da03ca8801e01c103c44407a400344007a103003950082c0c3d0042030268000c1602084485c0c0182080c405003854100030040b06007000300c080e0101d40300b48503608140010801800500c801d41d0182540c070035140c54203200199940c0c0482c100350519800820000e0320b80701c1071602d000300c0d5000300d449864005004d0300d62981140c40d1907480c441c025140701e0f0701c20350811a042041207844041c6009104204000f200010b81340005044a0460356401d001c02500c5202440010426101001d003030303410840c01a141d584688805858100001015040324030601c0c812844d0125038403000200f090 = true := by decide +kernel

theorem S30 : BRFrame.sub P3 P4 TB 1680 MM 255 384930836 1250 384929586 384929599
    0x609071101050c07050d05030c0f0d06230405130203030403110103150b040801050a0204080a061a1c12050c06130f0807060b0406050609010f2a0f171e1606150302 71
    0x100c0e60402c4440380000e4030341005a8404001480e1810805005803454034bd0701c40000500b40c1d60b500740b658550354030205189500300341c0385c540700c1140f90501c150ba502855006034151301a109500080e100e2149000044c00504524039200d01644a0351005125016450385420322988466402c0500c1d04584108101036003040001503594065000366001c42d6401c0340102088000e81c2c2e2410b025203103101404441c080360092080082d0366088407203c503400c5600001c0050401c50034144800d40292808006010040003070b0b5050f030b040000c02030ba1100c17070800d0800f0b1404151411701d1409000c090040e142e10008164002401001d5000030320804040303c0030070010340e0381c9080c4900c1b1301a03044128045a0f00c581d207030101d64000ca01041d55a25500d01912907112098030f0b100d02c0140180e020307190080442c010008200c00441d109403000c682c103040c5c0707007801c030070004000300f03180c2d001c10b44e044022001c254a203080d01210840d00d03110340d000800f07000e1000e903403100341244055440241d10402 = true := by decide +kernel

theorem S31 : BRFrame.sub P3 P4 TB 1680 MM 255 384932086 1250 384930836 384930853
    0x1e0605010909020f06030601181e0824101a03010503010b0f010f0311070f050c030f030322023012120402220c0e0f0102060f0609071101050c0705 64
    0x9522070209003e5002d0001d80f40e040303803041040180d4200501e020b050029190f10729200454000c0c001c000b60116100b0552441c06090a80104424942103034803a80d001c40764042c6003c00d80012009003061001c1c420ac91540e84c40c04000380000280d2000006400a001250754904458069030503110154020800e00c0d4020382009910384603881040d01240094502a6545c0d2298006d2882940a115403500d00f001d155075840c4200c450503400d07151a007001e014003803249010b01c041040041e4900055003141400d581642d003800f17503098010105405000482c085403900c0301c10304448440d4072042c400d004030740e80c491514100044080c0341c05d030080c0ca17044600e01003c0020760340404025003a60855540710b83c02d01210850f4150001c2c800c8440b48841da112031540e000c0d2483d0803ca42c0d030f41958600d1803006100781e00c050510420f0554000100f0000c60380020f60001c0e511080c1100c0940071038503110b1044d00d003d4231040c03818403503500b0401040700744a4500f004003c0c051042045400c2c02 = true := by decide +kernel

theorem S32 : BRFrame.sub P3 P4 TB 1680 MM 255 384933336 1250 384932086 384932099
    0xb0423012702090a0f021324081b03040201030b030a0609110321030405030c12040509010e1302040b061b1c03061208180a06030b1206090a0f050a1e060501 68
    0x8141c0000b5407007100348002c1a801c1c00c0c030783c4c00800c00c1c129100005103803c600005440b1030032148e5002c0c0f0400980c00c14070600281001c42c4103206504d040c00d02c4101070900130b80c0c9502c013a803900394140e052440400020b06580c0309421070f11001001034140c3d0888041801c003c1d001c4c002408042d12000d01d4881c4210242c280050b50754140849070848030500a81c0d500c51102980c009841550700e840b0a016804298009018210000c0c2e04504200e50325441d28052040f8070340d05074800c100040e189410040b9403050400703400c9115504407000102c0030300c1132000a0290096845540054840f240030800303006000a206c0161508120800b5140500040807400d4030117602073304002e1070030b14114130009080c40016001c0c1130140180035088a03d17401c04681c4844007a07100c400043d840d076420103420f0030725803451070396032500801904551802d8110300d680d8421088004003c01c594078896004d0180500c046141e480e88000c0c0704001304120070050b14003c4034071000f540d1084c07030680001800d = true := by decide +kernel

theorem S33 : BRFrame.sub P3 P4 TB 1680 MM 255 384934586 1250 384933336 384933401
    0xc0114090f04180203030a0801080c01020705010f0819020301090b04050a051620120d0f0b0108071112180a141309080c060108010c11030f04030b042301 67
    0x3841402001e00010078004418840a0110705000e01c0031100c070a0302540050b503040c400b500005403540e40d1000d0325072501d03400602c0c0c1010130722003034195003001c01c090000b0791b40700036400032000c40703824401c3c410780f50303c0d4001c2901601c100181a60a1000c03001103038400e4036400034488481d00f1074050040b615191034500c200c401c00d641001040c8120403902c0c55083c01410707030760010301c3d0980c04100700508009100d800c010f80d20005541043e000901c003109000c541c0b04846e820f41d0902400c00075100c2004c0040c01e6268050a03010510806801101004104122544c84090b00c5c076031030798480c170f101c0348091b468240110b02d947c4525446400030844210314a00c1e41c02ca800000e0007042c209402c002c0d500b00905110000390f0305040b04110718580000100427890081240d240000b8250383e200a005100007822028041c503900200b140b40e0002603403400780c1d002d072900417440d0016500c2e01d103031500c0c900c5240c61440003451016151304141c072806600c01c400c50000c081006101009800e0700044 = true := by decide +kernel

theorem S34 : BRFrame.sub P3 P4 TB 1680 MM 255 384935836 1250 384934586 384934597
    0x601082503030c021521130507180e0a230a0c0b18030a0c081b030309040b030f070b0d0609020a0503040f050c131505040b1e0a0b07050c0114 62
    0x10325000d169410404a40f007403180001041c00500b0904400162003031000103684110707820701202d09041c02941d41c245a40310714035403001410422a64980003982c03070700e494031003034401e4040700e1620000c220f40002d0598071840291801100711010440c0741e18200c0d0500b00e5004002d00320700c1c0100d40050220001084680c1c03065401013154208030b0600d02c1e410069007141085e01c600760442d08000016071020007a490146010b07040303010119240c0543d45281002d044103540c0300d80181c17002c24069480010076038640b03071760840700030a508400300d001c02c3c940320654a40d00050310031920f0010710004540002c211030712141005111090700e81515606034030880d074000d00002d104100060200301134007401070009200714242d52040301e1100c00111b0014070512041e46103a0b40d0004a0642d0040000b8080104011754090081150240000b032824465040700424600c40c05400000d951781c160b42034019181010000b03450b0141400c1450751404a201c1013070109010a00070035080b40320006584 = true := by decide +kernel

theorem S35 : BRFrame.sub P3 P4 TB 1680 MM 255 384937086 1250 384935836 384935893
    0x110304090c0215012403200307020a050c011d010c0609082d040302010509090a0b04050a020d1b020d0f0e06040303090305010f1422050d080f07140a1b14060108 70
    0x45c20759882100310020b2250b84003640c21450325940c2c2c00c000460650007580100070a600420040d00307542465402c100c0713312606e42c140000c4e509005c2944507803a0584103001c100342000e0007059064103045c00680500d010003848050000303101c41d400200e5030076a08a44100b002281000f00c12a09a02c182e4401c03400040e000c41c0c800d101c0c0f0a01854054581e96125264400100b80030030810003150642d03000755004c603020380d008651180807180d648240c0d1010758250380084120031000c600079450b269448902400c000600b182c607080e00c0d0003203849902c490740160503180e03141c0c0d481c100100907072114001141e0550818040105a87d240e004012603025040c020008035100c00408640c504188440300268840d40c15500001c07400070301c50360002d0075042d1206d0685140c032450a80801000401c00320502500e2100c190f20103011006582031802241001945080030301c00003a07181c4220180104404000160341c4c02c8042d000c20003504030b43c6900704490f04514103001d00d1403042c070080641c1 = true := by decide +kernel

theorem S36 : BRFrame.sub P3 P4 TB 1680 MM 255 384938336 1250 384937086 384937139
    0x215071701120f05100507140f0d05040305070c030503030117010506030d050c010f020304061d060405030306010f140a1107060507050a060b010905091312030207080307110304090c021501 82
    0x10700c9821100c035030582d02c16210780342003101c08003182e42d8241009013010b40b0032101a0740e9010071012940214060149900e05103c003413601e010b2445010705800f41001c04c1110701d1351040064101070244003118802070b08484002c400940c5d03882e00942ea64400d00449910552612060000420500420740103a8006021b018070240c4444115032070b400c1031901010070743d00c4032500d50098000e407000710b0145009100c0810388121508410917a10701000c034018444d402441003002003a0048142c1381c0003002480c00000f2201002d40442c0d88804001c0c42020700040042c0d6290955000060802c10740b11700000d8611455840109450070b005600000d06141c00800d001000038025500400b0080710504140001c1a16074000c10b0002008a031012082c1800c00390000c03c0c400082d030382e060060100d14041d4038002c00350303031007545c42e000182c0801d05100c0301011040010406105071005424024410450402503078402907683c1c00e02c4144210300d40310300e0b00126000428207110600384600d203214 = true := by decide +kernel

theorem S37 : BRFrame.sub P3 P4 TB 1680 MM 255 384939586 1250 384938336 384938339
    0x1208091c09090f050103021f02060106050f25030201061401300c110c1e090406060801020c07030605012115061a31050607021c030215071701 62
    0x3054021800c0308880c0c1005850440420b00aa15204100040d8a14240003076158118418011003484a00c02c01d01c0005c0c001a94400059001a03c141550024548592651010301801c80d0034060362030b98424529489600e011000c06031841503a04902a078020b020b0303560b403054104c1c1c0f540c205800c55400600c0d2040f80310882c1c001c8400c851008120240d001002c40ca07110034480454500340e032400005010b00c0d03900040450208a4030031070003011146401c00c0300ca40d00d1040b07000682e002c1101c1c01040180006020705c50294082c1004040642c004d660f01c090204103030351a034041e40000c1b103049151100100d201c03001d0510f580001c10720300d81d82008001d01c6481c0c1d00c000c8440790b140030056603203c550228140c110403100700c0013031200414440d15084802c58003d00134100c440f10301100701d0408414041d001020100d4000c80380c05039800766441c0240d0002c0744040309100b000c1040da84280401808240c1d00060f001d8080b044181940300b913843d4000b0854103802c0d210300805218106100 = true := by decide +kernel

theorem S38 : BRFrame.sub P3 P4 TB 1680 MM 255 384940836 1250 384939586 384939613
    0x7023f190507050a060e0a0e070203042303102007080a0302130815010905010e0405150702010f110301050a120521070f1101090b040308040e060f060c030304120809 72
    0xc141920600031000c9401c00c0356104006000c464180c0c21110029006075003001c3c090801ca42d0303803405441203500700c08103403410b6140295240154802c1e2024000e502000307400447c0b1514281c03081a402609490f200b800c8041c0364006064580d200004c022510544009140302c0d80c01622409903015405070f261801c90b00080780a500407100e0a000345009403030008000c2400c00440740340d013a08220300e03100356141c01300d03150895005034803285141855004000000e040460503102000e50740001e40d6030b44c1c40c0c080040b1300402030f2a69410200b8940184044240c0c0c2d001d0141d4125041100c080440719203a40125030401c419640080130303940500e0f007584170320f03455a080c4000c501d9843c050600f03090040d12800c000080804e030a480510b42400181d6195034021a110040e169542013980743c2480c59817076080717a200d907114030b8141030070503008169aa590601c400d4010711004140584580c44400d50382d403030b64010394040781c0750812040140c3e0390034044c41c00c2301d11401c8648041d0942c08072414 = true := by decide +kernel

theorem S39 : BRFrame.sub P3 P4 TB 1680 MM 255 384942086 1250 384940836 384940873
    0x90e0a0b04170d090519020102190602090d03020705030727020d020f1207080903030105010210180503041508100e060607030332060625030507023f 65
    0x180102c691054402c00403052440306405004241c0c940c08002c1280062824418203008951036000c1d600c0341c002110740c0150b41c00181c0410030744280840ca94007420507003052002401080b40e0280c3c01101d422402080c560f0000310002034442c1241507550f0150b82e12180003804d408482c0c2c0e80050028000340c546000142d0340905450410783c000035140841194507183d05502289840c244203614a0a010001750b00525485e0300640200c0114030719414440081e40e14180c00e01891129601c070b040c0ca108050302c0d0400714044940c00000c0301e8035551aa10900303400402d00310003900042e4940005010312004d500c0340c0c003c48081b1200c80300d441e01c3c1c1000780042940b1840055081c580c46800182011a07015060949141e40310807421500d51840003020041002030082ca04c5841c3c1800400c81d0415208200410181080d50b2075104e010103160543d0b0500900e080650b009403c1d26184203a502c03010509134113080701c00e0611202d01105c080e2407001c43e0302c00c0c8402d0103541c003520700340d0b1b070b444401e9 = true := by decide +kernel

theorem S40 : BRFrame.sub P3 P4 TB 1680 MM 255 384943336 1250 384942086 384942091
    0x50c1e07050109080406031413080306060724020316080105010c0305160b090c040b04092a0e010308090907180e06150711041b020606150c011a0109090e0a0b 69
    0x180e0010481a0030b80d00c49400d617501c02d03031007040000d60f210f070303503403510140716003441d4014140122003862281320340c075001c58500004d0121032082000203191010440006030002064403000e1120b0613001d00542c001c0025041120001c1040e503850080d82c000921907500103059410503100c080181f0007070380707045445400540c0c006c615a032b144240c120100d210304000c148600c0030138000742607130703040034081c4801d0312980409280074604110141d40041c0300a040408440a4043c06686242906101d010740d0001a84001030a225481c00402071241003002003031491404d80d00c204141c0c0301c4440c02c485200481c5022a400d800d03880d410f000359020208860740064000b0300c1c050202400c4120000a40d012410446500a12b040d41c0358140c10140902140c42c1441c40c01040200e5801074065211100182110320804e0100c04202d02c101c081d4050790700ca288000c00812501c51060201518000e42c2500c3c240401c1217464001005100c4d130040d420306900e403c0c080d06400303806907150ac0c81040003 = true := by decide +kernel

theorem S41 : BRFrame.sub P3 P4 TB 1680 MM 255 384944586 1250 384943336 384943343
    0xa030807081905040f032a0209090a021203040e0f01180c140c0a02130e03070303090f0807230303070504060518030a08041e03030905010509030c031c03050c1e07 71
    0x7810342490041c0c42c240103040c0558000e4014a003a42d0440c40c01911000003d032079944003a4640001d51600b0541e1800121484d070152070b601c101d903481164840c1451000e400080d8403c41e03e20ba41e0111400020150090311480e0807944075549078200c03091100d000074456072424090b100101841c83c0358640180c0041310386428142461001d24946030759941224040e020503921403e01e51040d450300c4240c0d00c50031004c0050411030002c441030240e44910408501500f03060f20b440c409000c0040f03500e02c880380c0329000700360f141d00c480403450b02c00120381200c1c03440790203010002c02e07040b9541c00c0071049078019401c5450b1189841d01c0c112003600c0c0d0b0b42040414801480c0458110003894400340102110390740321700c2140e0340ea1424542034441a1480b4084030042200f0044180002034200c0c591405a600c242000781c1c45090550000e031500c06104415038160054804c00360281c104a50450044c10703103a2814401641c90303010500b1903016003494000044000c00700000180e100c14010041e2501 = true := by decide +kernel

theorem S42 : BRFrame.sub P3 P4 TB 1680 MM 255 384945836 1250 384944586 384944611
    0x70b0406020a170c25030203040b07031b29090304150908070f0611010e0628110d0e0309100f020f0610030c06030903021b0310050a0207030f020a03080708 68
    0x110f4000e15450314112031043d08540000740300d15407515a200420300004500010700041041038500075940d002d90b02910f400601c002aa800606004990b0280c00c44800d10b0007856524081c500074502c055a50984400c100040400c1c4c9100010101210f2147c1c500f68011030416141c60251401e2401242200042c080484d802007500c0c0400d0207c030020300100250440340c545018401002c0d5081d00c400c150302e0740d141441201c0720038000320702c168005e031080030070618203400754545400d400741101c0e4102002e0b10308440d00c0a2003c83c407010789402c0c00034100400c10114089462a1a0710039800850b034884d909525102c2914001c0d11040e1110304580704582c000c00500046074901001030710a02c200d00f400d04420010045101d4504001d001c05140900909081c0e41d00079544000025500c401c01400b00350781041c0d07450410078012140c5050905000e81d0502201c01e00081d403200c00d069000411090840040a000080321100389074183d440c01d002d0f54400000b112207001c080c0c084c46034040e = true := by decide +kernel

theorem S43 : BRFrame.sub P3 P4 TB 1680 MM 255 384947086 1250 384945836 384945857
    0x11090301020f031e0f0a050a29031e0a021203070f210504030b06040b0616030305061906020607080910061e0e130f050f0a0803100b070b0406020a 64
    0x118244007034080b80c8144028259241003126100c500134101020009000c9082402c004041c60a402101e400100c9603070042019102c04400c200502507a5000720200c51385104800e00c0340b401ca6064071103008059040d50300079005071803403922208948104803182d5011810350401410315100100c2060394100a0b0703810b10305240d90b0045001c411440c181d070304c2103c0c0e02c0300c0c25000340d601d402040f03c00d9007800c0140c80c141c9581d42e0207200c00001801503206070398034070240131952a071204454010a900d485030200c1040d5290150080109035480d5000f444501c040d034200e13010450000c2e094038801d400514a513560000200c500c0d10008204540b28005c120704003041c2c00d914003500025126503000d04080501d010341712410450b05902c0a18407403410820711003d0482d00030340f41314094000c0031103a038110701428280d00d4054010405081d40c80380390182c070203108058002d18010940020080e000c0f6948130840041806503a2018044803060404070300058102d500a0010b051141041d50700344c0b = true := by decide +kernel

theorem S44 : BRFrame.sub P3 P4 TB 1680 MM 255 384948336 1250 384947086 384947089
    0x30d0c140a0812070f0206100603050711030d020a020f010612021e0d060204090b01080f16020313061e030203060a140f030723010915050307231207020c131109 70
    0xd8200f09420f10710410300100f4401000d41080b000120100030b40300401c01441c00441194942555114003404c0c140e460010505552154960315088585807040301d65840140d141e10000750b02c00955040103004030a404602c1074010b0040200b100c00f44010031000d85416000c10940358070001c00c051040c0080c801a0145450b5040c0c0800751a01070b070300050b1582c3c9000380ca00240e6000f200b0460400041c0e900700600440600c3da050b4000070070f10000f602c44414980280e14601c5040090b04032b0342c000c1000040c025620005100840c013032030301020070b040e51200d03090741680000e548855008007410414040d0448151080091003002172110790010840710201b410001c2507004000303003a0609568800060504281100a2a0a207400844503244c480e4854151210020714002c02c0300c00404103c5d20f910896000b21602c00008401808146080620502d90710103e1104041d90f074550018000c076002007070450741890301800004696400ca070410b0000c4c1040e684201d1070020521114445 = true := by decide +kernel

theorem S45 : BRFrame.sub P3 P4 TB 1680 MM 255 384949586 1250 384948336 384948353
    0x303080c041e05150702090106210608010c020d110d1b060e010f061406030c03060a0815090706170a15090204030305090a0b0304120f020a0f06021305030d0c140a 71
    0x81d42e014600d61845800c08060082003441c902c95000a100700300109001610303000e0b134090443d2482e1030500900c5d1000d180500c0c1c2541c80820f85e41c03140d42442000b064095042d4015214003a20340c0803a030540b10320940555500864449449580e007042070b54010b69406030152000d8804015103402c8410315035559102200c1580449449907955284503204165a5220704400340c400728544028402e141b80000e080e600c0014140000d02c00080040744e05519042001c070040c04400060340c01c400404104103a08013012509413000c1d20646000048080c000d80c0041208007180c2034007601d5581e5405014080d00c42260185041c0c500140000b070300901504c085d002440c441c0e501d0643d51850203040044028480d0842403030700c0c03030400070306c4002011000706482400007400c090314004020801070f420001495000703807401c00c542061600b00301c0c2c0c46c1c0c01818494210074120000c0c40e240d03400d00d59070364482d01e8100c1c081010f41304084040360168441c0c488080d095011202081c07404d941d01e546 = true := by decide +kernel

theorem S46 : BRFrame.sub P3 P4 TB 1680 MM 255 384950836 1250 384949586 384949619
    0xa0b04170c0d0306050616082208210307090b0703020a06060b0406140c062d191d1e07120602040602070b0f09040209041d06070e190303080c04 63
    0x2190010b580064500e585402004001c2104845860a04010300000f011410301444000d0004800049100c10310510082500600d8003800d03d00d841190784002d20794540c0030f41150115921580040c041003181c00d101568001c010381c3d95422850b03030900c0c510075141d60180c0002c0c4c0c1903105842144000070f0382c2c0d0080750050114950101d48442c41c040303003c2c0a11002c900c0502408a0a00080c04c007200001070040c0e0000e000c1200704003040b10b4228080011156101d502c005000040400102450540c071181c07842c4200041000301c1c008049a8180c2c15081680030b0106400454881c4007402c0424460f4082082080a039850130b661414a080031402c030760421901e0035004078081004c5501030111100601c10704480501c0d00c5107805074800503101d084116407003950b02041ea81300c10b856651003c281041c2100b681b0918090b48101c16542d801c0459000d00040c0480c142c9003402e0030300d546680f02003403560680f050820f05540d010f0350130b02801019040101c5007444005401a85400c0d07081 = true := by decide +kernel

theorem S47 : BRFrame.sub P3 P4 TB 1680 MM 255 384952086 1250 384950836 384950857
    0x61207081c03060b0d0c05040e100609080f1b040b090405070f060819020a0c020607200a050108040b040201021204120303140705090f010e0a1715090a0b0417 69
    0x6071058810a00c00314a074101c03001100341807406500308000c500300e804480045924070000200714041e0001a18280120b0308040303d4503424004100380043e81c1c07800300003904c010340c941306038141c1d42d50900c40d40c81100400b2201c0c943c0000d400c224440ba80d502e04543d81450040011980b0030000004ca062440212025035580d8801c88042000b40305c2032001d180034100070300e080420391800f0301c082220802d502d81346008855000418040b039601c2400d0711404154020f0210f41d13901d0383ca08040c1d00e824949420020311040d803c2100842e803801c51800b004544043c2c5030340c4040e0f6201e03101c0100c2500010000d0f41075008a42040300c0303120380480140082e2840e481a41c4120301241030003030440e044040506c04031640601401011608101683e1a101c0d044410400c81144640101e03444282d5540c0d06420420300036022607081240324492425002c843c0456174401c2d00c948040700003900552b5a0744154101c2900d00020076400c450207a8080d00032180d000520b080c84808034080d03807080c072281e03 = true := by decide +kernel

theorem S48 : BRFrame.sub P3 P4 TB 1680 MM 255 384953336 1250 384952086 384952093
    0x41e0305031207051b1b0f091914180c10090302010c020402090a24081005130f061511060c04030b150603040f03030b01080c0307050d0612030c020907050403050307030806120708 78
    0x113086c94010003480c1c0c0c60840e400d83d05100d0100044d004151007060103000d07496285180c489070025528a500540900504040700d00e405050600c1c160a96004e40c045a022074042c4402d001c0302400d01520000c4050403030b41d20100c1240c95170300156a1060100416078120740c00300088071894444c040745400420381e05c43e0f140c506000201c0078007425030014285000300204d078001d03c50160711000320502510700c111380d05059504940030507130080c036001112030115400c1550024141400c5403110048026035291303112280900c00344240c55240450381000521014841880410003065a85901c5441500078030848010000003035a41e030400c40701103a84441d000007050800d81c0c1030148940703c42082c02c14030014144a86214240c0c04001d050104120011030021491079a64104000904181c00707030103100c20041c10006c24404114130240d01522000c400b0403021403280d000c60b411a90000051410b25949640446000101070042030744166580c400d1030300c5210900c4901c000300a0351005 = true := by decide +kernel

theorem S49 : BRFrame.sub P3 P4 TB 1680 MM 255 384954586 1250 384953336 384953353
    0x7020114030c091003020d1418030c1b0d0507030b1e19020a0e36040f02040902061b011a01050a08011a040e0a02041e0305031207051b 59
    0x1400314a1644114800e400d041c0140403200901c401a40d9802d14111100071801c030b19a04203c009015112a950b51941850348000c04110f001d0039050258000545406100131030f0101a6564803580040c003113517910400f0304000c0d08070442800c60f1076050040c203030000307083c1c02e131103041c0750203078507002a100c241d40341003030104014031512900005a16a15591001d141c03098000c6407142034044440703d03203600003480d05043d511440c3d40c0a00d0a60003000400341d0049101400c800d12107a4146020b000701c0d03c0e15035810580c0010100c0d1040750302802c03682140e0b5096090002800704c2480c100d80000d07042c00a4420004e14011b900c0c00359101a00004148082c0e1508440c07000103c96071505111040000318003e0b0b90000005066400d00100c82c000002d00780c3ca2400507205552141e03016044800a011072415103400500c201ca0450350186029620582d0510301d400c050300c0010420b510070468070030110100b02e9465400a4242081f43c20810040a0254842030050101070541c102d12070 = true := by decide +kernel

theorem S50 : BRFrame.sub P3 P4 TB 1680 MM 255 384955836 1250 384954586 384954589
    0x613150203040f1505090f03031c091103061003080a02030f0d09050c09012111090c07060605060f0a03050601020c060c010902011d031e0f0a0605041a150f060c01060b0702 75
    0x1020700204440112020354105000026049206d6402c040b4000d030400c00c0b401c04180c45c05c0084455001e550b06030310100c054015103480041c07a103030700700300d51114030320b440c50741145000241c982c0070340240c10b04481e840b8a1995090030725401841200290300040c40b140e048014540003070010105034040c007107124400303450094148103044107218410628000180501c0704d0f00648260400c04002c065802100141818025007401103400d039070020001d01040354001d441c02c013400740e25105030b206002094a5404102c810f000703142c10100310100500c940070501e407190300b09507000201030068441580c0201d004c54807607406442d50070540c0e074454200a04550b84841c01c0001e240d00200100614805680066103410401302001c60702c3c210320040d8280a00144441f9680d0040001100c0440e100b078039151002c0d0408881c02e4601c01c407c078601448290700f17810010f21aa85440030b02852010040c200030a2219107160700e0341210090203401306c02e803003d20402e1b000d00b154441003a2220494030 = true := by decide +kernel

theorem S51 : BRFrame.sub P3 P4 TB 1680 MM 255 384957086 1250 384955836 384955859
    0xb04051e1f0b09040e030d090203070e0105100e2107210503040302040506012607030608150402010813020306041416030f0f0602121006030e0703030e061315020304 72
    0x1088916074100508485440200194050003500c400260403540c2e4000e25001401800c00d460700c0203824000010b4140302029107034401083d651082d800d82e0400d503550503040729400c03424030841d40c110841200e2205420b00c104041281280d006140c4948000c01e214503101500c060500450b040d80039400500480c41c40c805481c4410024800d041e07152101c90b554240c50f0f0040384002400345880d040030403856030217840e158000030760340c503800000c0710105400c2d4100513200342c0360100842e1078060089840600880d9030598512800c03840f40310341c1c681717900440d82103000034010f6044021400c0c1820040c0d40a204a600890280e1071541d1203000c0d035142c0070b0400080d20340946034103050840400008105880e880031440c0c01007564038401d101400d040019101d101d4154000c240c039082081041403010110100ba1903c940d0104500f5450240883d5508020300000d00428000c04043c14107203000d4000b0103681c0c4c084101c4096055892042c26910414882090003503000460248103400152 = true := by decide +kernel

theorem S52 : BRFrame.sub P3 P4 TB 1680 MM 255 384958336 1250 384957086 384957091
    0x30c06090c030115030605041a04030f09350f030d0509010e1c03020a0201020f120403090e1308030a110a170901050106091509030203120405010324060c060b04051e 72
    0x324000c116403000d2103240844c192542c4002071032561514002001c2c0004d4128044600030044d05103140c914080c50000d0903aa0f540d203040004c904011808103411600115000e8401a0b80c1210b40681d008012240c20740085000301e0398491042c90b111100c104401d101408402c03140709804103d50401c003c20a0a4401d418805220782e07025915140440d40454924183c00e003040c200180e80d00f50f02c42c0b00b00d019100e48201e603407200f040014a030f038220f00300580c44d03841140260740310021a900e40c1141d445005080c0c80700c0100e03160322000c14010400081c01107030800303107154000804500b480343c451038503042042040301041c5a560b00684112144d44c515a01c6116440200007a40c109030014003000c645020b0203581c2c00c2d403240c165103494026120704002d103030010225600c0350704e40300c268105607129003d542c2c0002d0424004440c94002003615610003010540c4039074400b4200f40e0704451140807042c084e90104d1721280d4505113a2118170807140601c00904082c503060034080030608800c5c101 = true := by decide +kernel

theorem S53 : BRFrame.sub P3 P4 TB 1680 MM 255 384959586 1250 384958336 384958339
    0x20d02070c090b01052d03100305061308090103020c070905041208010b1606110903011d07050109050603040b071b0b07080f04050a080901200c0109080609031812030c06090c 76
    0x4109200c42070b41c0c0e00c0012101403440c407200c2038012041b070f0107000c510300c521104500441c0400000340300b9849100032041e01102d00c1541190b08664036510810ba441009540081038400c040c0120140e03580680c002c2e0061004900c1100c100303c0c2c0d21800752041c2c401c1a10251400c49955a581d49080e601240742e40c0540901c024851500f4482d0603445459000644040d006550710884c43c11040010000c442071944024020b02c4101d88000c1c540100c58000b416040341e602c603441000425500580807001214401040503007103549640701c9418540000b4051001c019080c1602e214a018003119101d20302d0050703000c0c079540c0c5001a00507140b91b0020b490300031030344104d00420002030400102445501c1d03110164603121203000b40183d801d15205044010040701960041d15207600004142c50100000d9031480b01c0f00d0360340c01415440d41010303035603040b044d04100300c803052454a008280310a400042c00303012185201004050840d000214909040d400c02c1040c407040160802201554410 = true := by decide +kernel

theorem S54 : BRFrame.sub P3 P4 TB 1680 MM 255 384960836 1250 384959586 384959591
    0x7050304030507020402090616031101060f03080403300816030e03070609110604030302010b0f192102060d1d010b03190c0e040510060603020301060e060d0e01020d02070c09 76
    0x1403503100601540510310b0001e100b01e070002005101ca0f26120162440002543e50030903440881b85800303090001c0303014036001c00c1d604e00b910004582090100300001c5079000f40d106880d2604588422000e1807810740160200b03034041903001d0030480e55072101e4404501c5560364040781d042055020b104107c684400208150602c1f4821039204004030455240c240d020000084608851a20f128000f01c40400d00743d00460102d0000300b8907806400c000d801e0326003290b0082c0980090001c01503041048180540c041880002c2030001d03801c0341c800f49011485085507100c17404443d500043e0283e1000341c514080b00d80314070322210b050050243c0c50700680d00e110028840c4621800100380d85618010403010f0131001e8400706814441d507099000301800c900c00400c201450703d0704220f9506c018125600d10154641034000524030710a02c03d0724162106503a0303404241042004100b0706402404040050a54451030581c45640910041c888007510321409600d030540e03400c0960090826a000011050 = true := by decide +kernel

theorem S55 : BRFrame.sub P3 P4 TB 1680 MM 255 384962086 1250 384960836 384960841
    0xb04020a0512100b1605010b06190f090e190f09050c0d02060d020307020105010302100206040f020108040515090d020c0f060301090509191104061d0c0f0c0123070503 73
    0x241c11100b5201d0000b40840c081a0903900c2890390b400380c002030b611001c000740c07002960300615100010b01000c0c480c01000284a281444018440d09102d11080160881e0740c40d00d264094030710908060003981d03c80d250070301300746443e00c00085001005450018200d0f01c0380e07141d641032078080c0c002c1e09088122002e00b0408884140c0b03601c0e403a4200087d0f020701c18041e50707403200210743d10700b4290350040c0c9500c00215107a16201d20064004c2100380000e078803404013451200701052000942500c00c42d03000c14508a651b061358015200108042c00032601405020004100b103914261070a100e41c0c4940000c1181c1911004080d091441c00b01c0268099169481843c0e900d881d00c0084904683c3d00380c00006059807411002030400340310700d00c400182201e664036142030080c0e00b10390440c1030108450801c15259609404101c0401075014440900300301000a410100c00d00c1c050540c1d0900c07109100e14001e004481107013152040802c0c2e0000c00d0b040d140f04022400b2010702d950b808213440c1005899030 = true := by decide +kernel

theorem S56 : BRFrame.sub P3 P4 TB 1680 MM 255 384963336 1250 384962086 384962107
    0x100f180506011e09140405010b09100504020706020918010303180b2706160213050103050a0f021912060e070e0a0902040902150d050a02360a03150b0402 67
    0x41c01c0500803c400d6030ba18000c844000414202d1010003000b141030704000d90001002171245480b410340d000d444c61360820680726040d24000203110b000d05500c0c403c3c48482460882480003179081f00d80d0680303007907509205649643e100e10310010440c649070098011258114a8040d02c100750404506000450b8260309001082e4000308a50409110058249156410810340090101c1900e10b042d040f0b28041582030114102c01c40146206d80700b00c8103850321600141c4000c0032500244809065a486910500c0c0424107212002d00d40a0002d8166015140c5100c58210107003525840f0f141d480040c60041c80910640348150790108138290b0242880c245800741c0c4461603030f00030303112030000d9540d01e44d031034115621503004401c0700d503024000081c600807492001c5c01d01d07086840324500003814140000c066221900c00c03100741056001520514121441e41c8101c2642d019084c0b00310b91011203503081d8641d4071071240200940c0f103500100318045084403c1001d8070b00400321030b40981d006105d44a4030 = true := by decide +kernel

theorem S57 : BRFrame.sub P3 P4 TB 1680 MM 255 384964586 1250 384963336 384963343
    0x1e0d09080d0c0f05030717040e0a0c120f06030212031e1204120201020c010f0c020d0e03060a020c0c040501080604020a090e07050607150603050715022109030f100f1805 74
    0x11150003d10f43c041c1c8040034140b041c1144103083d0700801d403050003410030a201100300302400844106050140495031448840000c1c0d07801c0c440c4034000107406140f100030104180c0d100241d10080f503072000840315240d40c08111148080560703171540fa070012600c040041c00341801c03849150626196a4244440710301a20710140c80a800140004140c8400c072494620035416148010b4101009100302c4d549020000014188506820014020b030729901381b4082c081e031001c050b09000940101101d690340e050700f400942103c1541d10550184107141030203656140505070182c0000b00180804d0304140c41084421141e6074009011581010004003240c0400302c0da900407541c080d00d000e5074403001b070304d032075040140030365021390443c2d26143e4003000784040010400165005aa042464160f042d042a65182d8640440042820105004006800c100c0001d440c02440c003504032030410b404039003801c0c10300206002c0d95210079551003a50101900c070340510840c0780ba84a01c40e0b10821041d4540644 = true := by decide +kernel

theorem S58 : BRFrame.sub P3 P4 TB 1680 MM 255 384965836 1250 384964586 384964607
    0x2032a0a030b030f01050a060e090f150606160b06120a1203020a0318210306180b0f03120306090c0315010804170d090b01050402030717091e0d09080d 66
    0x18195146561011900c00b845000051262113001b04400d28001c0400c40080a85010b80c41c02c0c8095400019032040700010070405007102e100042a00728104d5800303180002c1d0052072540c02c200144800c510312110300f000d070010507200e01000c80b1945040014401700d00800350050200360701428001010030000000c1c9a51007155144c05603031441c1c210019000361481c0c3d070f9260481441c00c0b543c0340c01e02c10707820901901d41a401d8201d41540d01c041714101e00f42c88440c001d2600034600c000300c151414445500c201d0304440b000d8506500c01341c5c45000617003440c0e44001050f110710000002c0040d00e1420600da168002042d04a40d4258204400c1c0c00d50347d54041488103040c0171411001c18140443c0b00107290b045850292000e5940240000003806825806411904241203800101750340c681802600d1040b42c00790381e5945121400b40e0075840d1650064042151409405008030980e2030b044031a492800e60340b8024500d070751a22900411144060303000c254903800240250079034550005813001c = true := by decide +kernel

theorem S59 : BRFrame.sub P3 P4 TB 1680 MM 255 384967086 1250 384965836 384965857
    0x215100608010b0a230a020d1d1909150609060302120105060c070b03090f06010f05031c030b0613140109030309090e0f03120106020706091d070507020d03020102032a 73
    0x1380c079840a01004d5605054000c401c10a90f50f407482c0b209400444400185030b0b40380c05d6800d40c0c00c0d80102110a40e40c0e9101144d1a450185240201c101ca60401c0c5880c6030b41d02c03403076900d03004100d60386654000441e09502014003540414000c01e0101316003001660005058601e070845c600000d01ea0408810303103043c0540d6104a500185100b02004208040805010510b085603500e04044901e55510000c1401c8030025010b0b0000018600c24120f040c0f00071075801502400d541c005811503030045000c112169410b242c0d40d02c80c100e20030340790039002e80101c04545552203109801c04400d0241807942c0b140080c10040000d03020310000794401d00303c4c030480e401c804d070100d80d44407443c64813405c1c00a5101000141d100109222201d0b58054031f045041721100e40036907907060348030f49080750038603981d01a580c5031581e02c11002d09002c80080100d40c0c058013901d419401c0c103215a0010f503e8510000007500147e4021050191020f1000001070201c40358240040455046200c03c040c240242414071 = true := by decide +kernel

theorem S60 : BRFrame.sub P3 P4 TB 1680 MM 255 384968336 1250 384967086 384967109
    0x90231050705071b0911030907050d080705010c0917060601020c0103180f061a1f050a142b06081c02030714060a0c050703020a02040e0708010c021510060801 69
    0x60401402a81a1a00b00380d10441912140444e10440e010a521a1003200384290500340540028002071084070301401215010341451400e200c14801002d07590001200d5038042000fa04000c031300280301d8502c0c1c0482c81d03940c0740c503038600d8509000102c00c1c40240c0c503000f60f0080c40a01009a8000501d1901d061007800d004c02d1050000b4481c504d80e0003a030038050242c0b24401416003c00c00c840d80046130480c0c00707203400308841042d80306201e0200001c050403007180400310410302070640a080500080340980c0340c5805c0c40c0c0d0596400f40520b4108100003160481001b49809900c851160717029688141c90303000308a140c0c80d00754503a584498070b0444144600d1300f51400c1000c10701c2401252000c54000c04d51a04006505003101e5540400320345054510b40740035002c0c0030fa14425812258a43d4155006202d40e40080e000c020050081403100d58051080c2c0400046407142170261599102803600a80201145074108030300406000706409810441c5290902c003258216905506440159010 = true := by decide +kernel

theorem S61 : BRFrame.sub P3 P4 TB 1680 MM 255 384969586 1250 384968336 384968341
    0x50a0f0804031202120105041413030c02030102131205060105040c2106050907020a0b0106020d05030c0306010215071808030a0f080a0f090c06030b0f13090303110307020109023105 79
    0x580d2220341d1a01ca0842d42c3d400020200442c1803660035540c101c1c1e106441c10042c1c0c13480031186100f64101540d585035102c0d81c91440c1408a8843c140040665000400051070500540300d10a01134490740c1c407294844200750030320003d000c1309024150040005480c140700e80094138400a100c0ca242d100c0001c1d600c503890300502c1800e216984104c01511001d0902c0d801c604080c60080d580d09030700a4221500312100c000840c0c6684045044900080305865590031030310780b40321042d8160801840241184200c2d4296103405e00b4039019a801b42402c0d407909d21181c06083c080c03c4818401e900001440e6008004113850305a101c02010a00410b6151818454545003140c00c007501e04002d144400c0ca0401e042d0f04144813007032244100300c84640e2400c2004c0c014800c01e102c014080da85410780c0c0030b12184000c000d200c03103540003401c049111b468002100c2040b014403280d00e41040c1d8605005130741d9104540114103000141c06031030b1004800440c441d0303d5000c007902c855201441c1064107039886101 = true := by decide +kernel

theorem S62 : BRFrame.sub P3 P4 TB 1680 MM 255 384970836 1250 384969586 384969593
    0x603060f0624110f0f07150c0f02040e070303050913020c06040b13050d180e04120809010603060203010f05012a061a0301051501080c1606200d02030f07050a0f0804 72
    0x42051403c50019a01400821030816558040d0385800005601482d80d0000e20100d213036150b0844a080c580300e401044550b0f403141c40d44620340f880c0c1070740c00544a882084d0b103140305200380f0010b03512a4031010384828cc00000d00000364102000443e01600c104068507000e000082d04540c031035800403907100180d81d07010340644000000c0344014014882c010510340915006241550030f52041d071000b1507090340c1e500400c203c0c81416200544003500c141190347d02e10307219910345d0368051800b40002c03034003554a03982c4a08030380c008d901844074061110001d015540c0c0c05100548210b40072920602048022540203100340c090b044000c6c850741d6140e691007000c0c440400002019140203000700701c94682103450310214a1419480e50005030703841c0010312014040d2091310703080050741245400380e0100d982c0b800000c0107294044000000018400101c403140280100b69000e071242016031642065203001d0300a003001341440040c003000780103250480358007039041c9110381307020301d0a010f007500e9509 = true := by decide +kernel

theorem S63 : BRFrame.sub P3 P4 TB 1680 MM 255 384972086 1250 384970836 384970847
    0x27030507080a0c05091e01121e0201050904050a021b0c03010c0302030c03010b0c0a060507170705030c0f0c0304030804120605060123310e060a030b06010c0516090603060f0624 77
    0x8107082d40380322a003c00041d54898050700490224044d0409100c9c000c3d2180084071140040207000340840c4062212540e00c0c2020707032261354048010000180307095202d503610340c100c100c60086002141c0c0b2441418034141070a0245500490300b0381419820350422580510260005001c0c0088030340c030210b07c0100349071013082200945c40c2c0004d820411800c0500d4018001c01c02d000c1e150004948010100702caa074440c208491050941000c241c1c00c006108c3c09000444d8020010f0613400c0c403040c04003202148800300240f000703002c40544000c9980351441e100040c4d40006000038140140c2e9580c031060700c0b00f50215411100004c408950b900c480344014410300314408400c0050300c440010b1701c10300011035272604205881c005440034015680e100304004808600340402820804070b2404500b055002d00080311109104e402942e0390101001100c400030062a071002c0724940d1140340c10070900c8614030070b40b0b10b085c03c04841841a1402d260440030740c402c0785a104c60a541c00b8000e007034221407041 = true := by decide +kernel

theorem S64 : BRFrame.sub P3 P4 TB 1680 MM 255 384973336 1250 384972086 384972121
    0x80705070e01091a0a05091807030b091f02160201050703020a0c1511061e040c0e09010605120c090103170f0304062a0215040327030507080a0c0509 65
    0x4852184807540c458840f02c00800615910b10300f40ca05145125210303107411500c02088440050480585640b00845090f036600010821607036846001d0001c40000d1000e00e0040c03050f040b0b040101003001820303078034001740900c403401c2c00c9441d481040300184406209660705d50032038080c01c01641e10390862030300702d1030300030407160107070580b102c80d1400b058102c801811406401706903600c03c51034000c0d010b40c1d1915481c5c00c0d40e508164003483e880e20081e026400385000c0d4803a0080246c0000140d42d42e1223141d000c04121110042c0b80d65914082c0a1444c05d400381c3c01203c003204004103400c50200011400e010010700014001641441a0000d200e030200c08403420130460107081038803400d040c90700b03001910304128060002c0070244d5040e10080f0082e0109082803446a00414040311001a820b2411102504c143d0404c01d51188051051700d2008004411121202c4416032032481c5092580c1800481d07048211180c02409400001c119041c1c04401034850440700c0d000e03940c90385803035a40800102c = true := by decide +kernel

theorem S65 : BRFrame.sub P3 P4 TB 1680 MM 255 384974586 1250 384973336 384973349
    0x103050c090c22081216060509030f07030905150705061503010b031209100503192415200d050c0114010f090b04050c030708040609060e0c0114030108070308070507 72
    0x121200a02040581c0a10300c081343c0750801202c82c074140000c1031201a010f81500342001c500044200404250700d41c0040307030006440c20030340703107008007c80c1c13880c846520861094002c01e15940040000d0704043c50000e00d440410700e101c6051400f16070300c0685070600a00001c00c80c40d40089c1e030703503099542948401c81c2401c008040302c1042c51020300e00c0000350001c002e06d610070302d01008a8901a40140100c1c1e2040c4000c84c82c5820032051080d40c00c008100c4850208140c00010b0f090100805a13001000c000c0d00341804240c07a21290500020402020220400f09210b51002480b014850000d0541d05107111410441e48607183c2c0c00c0b40c80e00400302e145030344d4003405036140002555081030729410300741c8680e40c0050060620850a020565600b500c5181c1c071000200001140a032280c41d1041c1c0040c03041401080c08846030301c1e6041607805201d1840e420382c008580e83c0c01c107913810495403000c01e01c0f149851811507151019194440d03400348005000914001805810402c4c00d11844029024 = true := by decide +kernel

theorem S66 : BRFrame.sub P3 P4 TB 1680 MM 255 384975836 1250 384974586 384974617
    0x5062a06240a170703230c100215010b0301140316050f060c100b09070f05190e03010f0204091503050c01080603030d0f0605040f0e070b13090e03090a0e0103050c090c 73
    0x107000c0066500c0901744002d90320000380000803ca14905c0d00564556035070050002c01c0810800e6003404131001c0c10481520842c0203c0a054002e291202c0826009100d802001501c950600000d1141402c03002402c40c071990001002841d0042120701c51400c03034030201c95101c0304420f40800728880d8031404540155034060217424004400c00c03076110442403441034440316602e955203a0281c0f8070b0110350b83c0e07a4020030070520111a40c5055032034040885890780c0350000006085001007420b40c0c0070b1055013402e80350080703801d00482d8080e2042444450440c11200d52284c950b84445480d2543c00e4400740c104450600000c00a071810012200d18040007001000340ba00c14140c0c1c08010200c83c081d0380c3c8118104049072400c4110703405100a14880040070b007421a03e4640314031040e03407000210f003440c4c6012280002e0096030034807070764403580d4614020755514001e0400300040703610590010f0a030b50f1114001800841c0000070301c0e00c0e03542300544100c40ba58444041c464030900a90300402c110f803d = true := by decide +kernel

theorem S67 : BRFrame.sub P3 P4 TB 1680 MM 255 384977086 1250 384975836 384975869
    0xf211e200102030a0b0105030112170403060f0507080604090803060d02030a080307030e06010509010e1501020c04060b070b060328060b0913060c050f0a12020405062a06240a 76
    0xc1580218414100d044040080f022450011600c5100c2881041c0601000c0240e0b00041003901000c803c45035260401c89140ca0358903500c11060710754480c1070616440d0350350304000381c054102e0700c03142e80014220740401014070b081e9528007541c0000303081140121040840368045403001c0106041a60700505c649441e440d10702070040250814916590150149500010b00307810280a01410707100c41c50881e140650b503d40014215081010070f090461003034a000054645852042e4400340641d0241169640010f0a0181c0890406040540240d01c5040c5e0703d8428003a40e859020300703092254003101c2d200000c2c00e080c00a0032041a03810384c480401c90078440d50445246210b90403920541c0305101c241445201a1020301440ea1844c012840400030100410b104403403030399069010707110040c02c003610340c4013141e040d812080c500710031490300d4034404054480f42101c0700c48009030f880c0142258500054564140c6407861140220340151842c01401680d50a014102514052140c00c40700e1 = true := by decide +kernel

theorem S68 : BRFrame.sub P3 P4 TB 1680 MM 255 384978336 1250 384977086 384977147
    0xe031b0a03170414030607080106030b030a2901050a05030a03180504050106030618051006180b120601021902131805100b010306060201330b04030f211e 67
    0x103900c44d104285900f91948001043d40c00c0110300307a0f1080a0580b50700351140e107440030a4014003041e050305036060060041c200d0020301d01811148103844010395100c40812402d0304c0281d44141a0800c80c45014030401c00c02683d81c00084450f83c1550610704603011101860340440380b21a550020350b407050400c000400e005903d9481342045070b25105c011410b40701002d110750115003040e61014460f262060040c00624094401010365800c12011444990b9a5011540700c541101062114540454090000d190381c1080884003203400072103041011001ca500140e1035114051806400503151020413114a182c2c5690003000c0e900141968004900d00036440001d1581e0b00c1c0540c0407929040010803080c0c414800c844110001c0c5003000c1410302090724403007030800c6900303916100566104010881a5401d030152000b903100e40d14600c091141e038030300600070040050b444051040c84110300004154000c0a600584010606141081c812000c0413140c00302d46151070b94002e0070003003141c001c0 = true := by decide +kernel

theorem S69 : BRFrame.sub P3 P4 TB 1680 MM 255 384979586 1250 384978336 384978383
    0x121b0b04060c0309050705060306060903060a0903080705041401030b040f0207030f110703020a05060306030c0a0605190305270708011401080607090515090d1e0605070e031b0a03 78
    0x19a104000030800405240410b80403039580313200251181d4010034050102c0e080001c02183c1284004260f00c0c1480500e00010f8909a42200d10580c602e86400da40010960049025074000340d0b2418107034249810500304070602c10148084504050f1500c0300e01d603207070f11158003107a4050cc1d801419540e030303c00f60074090442c43c0f01c0792040700001e21a41030000c84410208103601940d5005182e400c88510b0b040402c441074001412055060003011855241e945c4d03951090001050952075454844580d0032891282001e110041e00c281410042000048070340f80e030110760075401c05010040f005200c14080d501d4038a0ba604001d0140d131900c84e10605002130b01d1095070480700010202c620f199207400e0100c039003054901c101a00000035091404040a039000035011b4200041c004007120001520b400c4040401140c2402000f0110b00040007809254065194007000341e0800c42e83c042d1448005c00e81d00d044100300c0b000e85241c00411403110740e4840090100a5400c5403082d20050680158002d5 = true := by decide +kernel

theorem S70 : BRFrame.sub P3 P4 TB 1680 MM 255 384980836 1250 384979586 384979591
    0x4030e03101808090f1c030311250314030c040f080a0203071809050d03090201020c0111030409020d0204090e0106080610050105031302040b1810051c121b0b 69
    0x840e00c105000a004088940910004003a10800c81140c220b8a0b40d12102c00e500520360050703000800c1a4a441c2549070071800302106401c00741c0b840030700045814003030112805200c400d45c00c02d000b0003140181103101c85140500700610203600040c202213040c00c541059500c105814003040000034000c03001410405001580e94100300062600d03998110f00c1d5580c1d180440003901908948030030450503503540c001d81c914400800001c901810160345260400c02d8106414005c255146200400c3d942d0403c41d070380b00307110300f030030300c00d0360300c114942d100f50f8a028902c2440356840d0000b0b2400707034400d03441e010b03100146403501c404d01c000986804424040c00c0c240c0641c1540348900e00000d44603400d46600801260811b84510b895a201e400c00050311221950b400d036005502c41801c01c0864542d0307112418100c500c03030110441802c20204541403002541c0c800c0f07100d4411040d0010514141c03006200f40305904c0b03003864031a41d10000081da500a180d0484a03580980c60080000f44100b201d465032 = true := by decide +kernel

theorem S71 : BRFrame.sub P3 P4 TB 1680 MM 255 384982086 1250 384980836 384980839
    0x105010e0303190302090a090e010903110a050604110a050411030103020405070f1e050c03030403030e071502060f2d0a0605010507150506060d090807050f1f0507051204030e 76
    0x5510801505041d0b8030b00614505420148150544040c114000d0b03008100c1800c000d450350080640392000300b02550220b41d05098560b65540b0340609140c1c1c0001401254016580030740500c044540724580c3d1404050000b50000003041112240c1e0398440c40000024940500f0610002101d0003545c045500300f44016806182003000007140c080c424810049001c40742c0d21001d00250460340101c9280361410006000d01c64204600700701b0500070400307540300f0340c426a004503441c0c10f03e848a03801c2c50303031b07560121340c3c00642c2032562041d403500802c0c0c03958040e0301c6010301c25044d6640a081814050b028540d084c0016a009041100c1981800041e104102c1d40100b0b0003007640e80c000441e0301d4400c00502600021740c0302031155008003117410280e08041c00400640c00d00c40840200401c0f15205030007101c0d10140000d01d401004024045000b103004c0c0794010700190320154044c05184e0504d5158003003d66610f00000c0c01050040c000d070340507a44a1350205500e46031074034004e130101c0d68040045 = true := by decide +kernel

theorem S72 : BRFrame.sub P3 P4 TB 1680 MM 255 384983336 1250 384982086 384982097
    0x150d110f040c020d0c0501020f03010b0c0c0a1401080915010b030411030712020409170a0903030801050901060504030f03050d090b040b060d150b03030d0f0606080a02040e0105060c010b09040605010501 88
    0x240d06a06040c010402803100320380c01031078011980b180031101400624800c480954080000c4294040395001540c080d1520aa00c5c540d240114aa210314207500e5448044c004c8072240400c22003201e15251070b070000136080c00c152206a41d400070321401d04890007980c8a0280c512000800e1400d008006544554032842106203901011020035503a1111071181c40e0803c10010070b28801800c01d9005075600034031955000036131000340758600205812610a04c1c0005684003000c1040c56841300c1e02500500382030f208041d0550401764000d00c40d00c12070001411501c034510309030042520031802c0702d600d403444131002c12906c6031a00c0e01076040581510306035480007568001c036140d45018580c3e010300a0b03210031002e045054074140318018020b0701c1e0005505001c05c0c0210041903074071740290503002084400c0028400c1c10007401070104d90000c2c0c00d80c00100e20600042c000e03a69204142d0303040d558100c07812034654030044c004502408028003820740285810301444100000d50f04903c0c140c0d1000d8842 = true := by decide +kernel

theorem S73 : BRFrame.sub P3 P4 TB 1680 MM 255 384984586 1250 384983336 384983359
    0x7050a06021c15090f020c060106020c1e10112a0a08010203060d11032b0305070206042604030213060f0812090d05071a0909070504051305150d11 64
    0x1440103441850000081d10460020300704000810340d4000450080d10300000360401f4a0303815a1800d11609a014101603080614036034414905001084822040741d144240e01c8202c020100e0780f1b00601584c0340d0140040d0340d41c015105402002b40310355214000301042c0103403c41c21310510032582c9050307010340522071029002c10100c8060080d28816440504850f0312080c103611444c01c00c240c451034017074060207134402052003002c040300b903d544414a000801683c01031001d0080403940010409000c42d04108140000100710281200b01e80400d0311461809200010040040744600e610080d4802d04c0e03c4910184560340b0b80042044a0b42080c3c51400180e0700c9480300d0b1a844109020429a88200400c1e4003903c0c250440f01c192074000c804a502c0e19484155040c03c2c0740c00026081203c0704046400030130f6140c40c035401e0b9071260a03072801e00d09003480c19010881c03030424803815003921611a00000e01b41c00c1d105007540d00c000f070018605000420305050020400190740081d40c01581507184 = true := by decide +kernel

theorem S74 : BRFrame.sub P3 P4 TB 1680 MM 255 384985836 1250 384984586 384984637
    0x4050a0b0c2113061a060406050702030f010c0203030415060f14030601080115091107061d06100506040e0601020c0a1d010b040302060f03181c1e121107050a0602 71
    0x8402d40f1548280d4006100103610340d40d8800285290300c08000c4d0b07500d502c0d420301855222500070348003038100382e00c0e80c0340c0d03a20260040500d44141002c04615aa04003424026003541c044152604603900408941614410320140b00190982e42c000000d1000780300e80010305000103122080a01d4001c3e0151503032641c0700d48203582038a154042e51443c00c071043c501080b084600e40d2041074114064010141420240c0d50b850040d1000e400e0008504402011040c21b52942480802c2e00304580b590b007464020324100101d030460045120740a800b040760000580d46034024800905010030040210368a5500c4a60f002c0d00d02100c1ca6669110f8907020001080e034002d010201c0b000d80b5002001542420b42c0070702030b03800c40e5200a0000c0f40c0c0c49241490340c5183e0500b001254400140c909200d0504141b5034070003020122400300c100b81c9502a8403494800c580c01c488403102d02a0596004950020310312950310552081ca03030018640d1061f0403840e0144140c50740508485880303074015010b0000c0068 = true := by decide +kernel

theorem S75 : BRFrame.sub P3 P4 TB 1680 MM 255 384987086 1250 384985836 384985897
    0x120906070206011509050a0e100608190203181e01060f0f0b0f1303050c1008060d06050c07020607050309120703030e0d29010302150a0c0b04050a0b0c 66
    0x19480030140e03108500600507541031020b800c1c01002d8a1400e507000d651079401194125180350301c4802c6c2c0342c07090700501c03110300000a04403002c0c15080c504030341149804030345441901d00301a00b00b00115800404039850b441390040c9040031700d00040403618010703600b08010701200c1c4071400c0004030354681180440c0c9840c042541400300c42c9501c2c07074103031028188012000c0541c0032a040104484040001e80d0314880320b000c16800030b5002c1c4c009002680054014450b5400c840d403461002c0103401401c009032a542c0280088030a604590700040c0c59541c2000680d5506c50400007950000021a180081220000003005a1b8400380c80450351100301d100304542c0c0b0003460000030007182d000c1049941d5410b20801c5443c00c1ca00072040480030740c01000d01c8051a010620958804808880040c030a60074142c1d809201c01c40c0382c204542c54000f001000402030041c500004011046400200381444000c2042c070409030340140c100d02050828583d503080e2544245c05408500441c07402000703200c01000d = true := by decide +kernel

theorem S76 : BRFrame.sub P3 P4 TB 1680 MM 255 384988336 1250 384987086 384987091
    0xa060608010c0e04020d061802070203070911031f0902130f0e16052a03090103140c0a12110406020618070311010806010c05031303060b0f0a030210051608120906 71
    0x7a200c3e52034540750392040101075040780061804d050f82c2d4581c00106204880402d441c1480790901c01070340c58078140141400c0003c0360b00300340b072002d0400c03410340080e004403401c03030f680000d10792418000c400d032181ea01032070310703660b40e001000c0c1d07600110382e1051100e9100c0240044510029940740560787c1c40c2e88500500c2000c881c1510905c10720741c800c0c075a06000e88014001410302c00854190b99220304a4803260300f01d0341104c4111540003298654484d40c0510800421000348040e00310305252000182c1d00c3d41c4210702c0f40004001e0300c0c1180405240060b0480700c0c11801c1006c04a8485031650802507480c0c00c201d0300341d00000708801601c05071200101e2030109903508944958044030704a001510640000b400050401914403084c1d400311b1800d001500f00380c1044000020031510f51704119003a00c100d0001a807213400814500100f5985c0d100d100011250b0648501800816504054440d4001c02c5d0841c0040d0107070340190b50401010000410b500c40d040034041a40d070725201140da585070b804 = true := by decide +kernel

theorem S77 : BRFrame.sub P3 P4 TB 1680 MM 255 384989586 1250 384988336 384988361
    0xe040f1401121101051621180b1b0705040f020304031d060d0b031006031b06260c0f030a0506090a05060102071403010603150e150c040311040f0e0a06060801 69
    0x20025a40c4913540300d800104407480d282c2c0a40c034201000da544a4030144416441051030f29030090001c060260f000304c000d540c0c940c0c843d0300208090b0800301d81c602d031841001d8403070303c0c51544024109030704402413203410010324004208110821003003500c4006544201d408800107801107850035800208901c1504050201500c102e040c41c030310f120700c00010072542d4500707580740c850b0828452100180d400b464014501c1008181d001e8003620080e07001001041d00144280680c2e842008018031000041d00440c440c211040c403502d846941110740a88a01101c078002c0f4a00041086241306090300501d0050701c050350840ca817507440c14510802c8402c20380e410b40c0183c000c50400c0004981500321180208001000040e609a0365070390000700481c5c01c5030550300d06403152142c206c18402408025a070841820200340b561410f1140050207104d603000040089c1d00304090000c0f507845540c070564404d81e2040d070802184031009403066070b5000740c203404c4400301d00304603010410361410700401c01c0a626 = true := by decide +kernel

theorem S78 : BRFrame.sub P3 P4 TB 1680 MM 255 384990836 1250 384989586 384989603
    0x15020f251e09020901120203070306090b15071115160320030306090a021c061e060f030f060b03150f1207090905030903060c121e0103020d02010e040f140112 69
    0x1032002c1d000213580b0030714041d8100201e1003a40d4203010384a20003103014a00039100000e0140c5007403c60001d07140c0080403540301d600c3e1000e0700a455569481141c2d58594040300800341c004120b000144504410008010915070108485050154400e90074180c1e5001e51078813146800f2091005407402401504900160803c5c0040b40355030804140350340d00510300100260034a0301c00c5e803840c00b44e2203e00e85c16113542521440100001c58120035400340d030b6142015681c02c00313824600007800c480e0746410980308040d91040c00c90031421240d8040300103000381591003581ca08040341c900320201560f5482910030400d0440070306d130529240d10031150840403d0060801c0b00c0c944407001c1c00405100905442501003044243e025580034041d507441110246075964035442c000c031400c486044010709076000c0441d1100302501c100000784010f4118be0b41192422010249c52004072180b119140f4441d8006042c403082201c0c800ca41d811600942061f1a400002c0f42c0e130f15680500d1038190641c01510442 = true := by decide +kernel

theorem S79 : BRFrame.sub P3 P4 TB 1680 MM 255 384992086 1250 384990836 384990839
    0x305130218060a231c02030309090709090603080c010b0307151805030111280c021314090106181b1404030510050a0c0c05060115020f251e 61
    0x922040120754807020040403480b06998074403c00300c0003820144e1030210f0600a105444091610301c0c1108030b4007000d0f0350030344e48106095000c203640740b00c1d049049208501010000c1c800500c268000300150450180611180b9524502080d45400003c00d00c0841c1d400c0002c000b01600300000d128040340d07600c412107101d6241403a01550800f411828524134045540030115581c1c500f40030700e401c03401d001c24195540703440c4c02e9400101d41460b48200e06024030195140c41a540e0b10004a0304815011640d0b003401000003260380e001041d031244206001304c4144c003004890709041d400f40c0300b19080e1240c0841d0052200c54840203c034240f00800d1111801d11424199040c4503118144202014070802c5180c540ca03901c13802d2800b05d00f21f0a168503591100704100c0c18003428010700903400c2d842d08100c1490f00d45562140d807161414015006841c1d001c51250070541d100300300e08020254130105039145c10355070505218800c2c0c0c0080040c01e003400740010005401e03100580020912561a00c5090310b42d = true := by decide +kernel

theorem S80 : BRFrame.sub P3 P4 TB 1680 MM 255 384993336 1250 384992086 384992119
    0x62d0b0108011d2e080c010206010b1c1a0d03030c0f03020f1c1401030c290d05100f080312010807050d2009131a01060e1314010303090603051302 64
    0xb41380010101481251090301900101d000030000c0c06418043c0041118841d04800203280010580040517007400910411070000b000d11075a2440c001050004580c0188148200c0030f0480d030000001d6100c1c13890285402815055071103440320341650340d680b440c0c51a031414140c090b80300304370a0b504841c50400c0801c40c1954058010081303180740d010003090000149012980c014070a030010340702421154420800c1840100d00d1640900000070118481c0e480f001d401b100e0303801021011000c20362140700040762508000f00e0316010700191201460196140c0c50059601c3c0c005024011061004400100b281d120010f810011104000d000740345408007030380d500311902d1042401048510022100b80d580e81d842e4000c46114040d11030025a0030b50150401c7c4005500b400d0540c0c81c200030000041c0700040e4445202c040c164415621005880021007080c1c00501d4a240d514906d01c544c1c80c004020541d1003881d0f50212803556809008645406082e10a00000c00310029845070194043d003440 = true := by decide +kernel

theorem S81 : BRFrame.sub P3 P4 TB 1680 MM 255 384994586 1250 384993336 384993361
    0x506180606071704080d09030804030209151504080f0724050f040e0910090510091506090203040c081207141f15120b0103062d0b0108011d 61
    0xc007410303640c00c1203407940d40d40030f070b58520807100c45403203101080a02c2a05400c05c214103600c034031071429034041c0785141c503890114866804064042d103452000144001c8403d4015842000082c00442c8018164a03424041d44c205000304035050148450381c1119100004600080d41c104004039112442500e200782282e024248044041c45424014203500010060242c0024010046003140b0703841c2c40024039061507200e0402078085850002c0c1c2d0804078400240302d1124500f00400050312414038200300866511003202822818188040452003007102e8002d140158464461030b1005501c6031515030315000c0d00b04403904019014060b204c0407481031400030806031030a10603104d1030000310752840c3e1843c02981008480c07a450341060180314100d0302c00724008203183340c0d82c4d035595651941c540c0e000c00c0042c800a000c00303450300c0d404101c3c00304241c5030b900d000410391164840d00501c0704c0c26002400b20002194081210308000080719200d0020500c80c220610611200a6440d50004800c = true := by decide +kernel

theorem S82 : BRFrame.sub P3 P4 TB 1680 MM 255 384995836 1250 384994586 384994591
    0x902011407030206190c0801140a0503060411041b14160f0b1906141e03030304030903050c0a0302030a0f05070b070f0606060f05041202012d08010504050618 69
    0x10490040c00c0450003420300300081c0003003402980544420303d844032400300d6a0030001c0c0b8009a0038030b40003a00c01c1082d07210982178155442c90700351945614080000401a6180d6080117505010348000c2c40100701e4203031154118128151070900c05070030052411690001000702090118084030504880203807850010980c3c686089000c49100143c0c2d104c50340c0880310700c0c1d0202c502d11000028410503a602128078018151000400d0015501740101c800010444503000c5020b9511b042201c600c40d40b5000c415009228090304580c2c40740340c43e081c02400e0722803a01c81030f01c031805605c2c0f01c0315107810058040700681e50080e00414802100e41e45400310441c280c402921280500c40303021642400c10001444464012140c620344503d003400c3c440c0440b00107620407028070008940c1091080d80090948048521550b03118a1182c1e41d800140c40e10140c2042410a49590403424024800498816031114403a41d60348a000d0707803118144400c488042ea043c0303500c904440400c44541c804501c0701903 = true := by decide +kernel

theorem S83 : BRFrame.sub P3 P4 TB 1680 MM 255 384997086 1250 384995836 384995839
    0x17030901090e0c070c0902070212010c1713120801140603070c0308150a0602030c06090c01020604150209131e0902090a0e01062102240f0903010b030706020105060307090908030a0902 80
    0x1440c010f01034686181450094105a601c6e6400042240651824800d0b14801b020058001c0100104150020f0302c4001501900810608000b0008130400c0c101c240e1346901c1600404900c8c4109240c0c2001080000709000e600d0703c0395003400b5031188a00344081500d1141d0b00c1500d40320300091180c1c90075074107032600400000d2111008012541d40b61100c2059500414041d0029500d4a10790f0030160300341032000305000f4030f980c0f1500250310541e03800512a82c025401184501034000d0300c80000010f03219011101c0d4202440d1070384140ea484580c0d00450b0002c200c040c40300c05d580000b200803c291000400c3c060340c4180030501140139417106610014a1042c0c0f032000245680c1c3d110010000240402603400b12083c1401c400015402c04220f00c1c0c00d400302420700ea448034000242c0b03000841c06107270f403100e050000109414030305031425400303071000380001000c4403038103036860390000d000e41400c0350703414081c0c0584540060ba8480c035018040300503a00c40f2000381956100426a4004d24882d40244e = true := by decide +kernel

theorem S84 : BRFrame.sub P3 P4 TB 1680 MM 255 384998336 1250 384997086 384997111
    0xb040e190b040c200307050d081e040b0402040c05120403050c0f100603140303010e04030509042d0b0d031704030c0b130b0c03071d03070504110417030901090e 70
    0x858041d9594402d450103101c160f210741c0c0300600c04640c9201080b44003400c11002d500200486c3d00003440209003205d00a50a082041e5070f41c4504030309030200d080f840c00c206141c00b00c580502043c04951030000e1f10641c8221005d02c4445088003040b910390044000f09810030b2102d1011400180c0500090501c01095504454021004030545403920030341c4800c40301503d90340c00007070080c0802074000c0e4494440d03150056186515165101d640008024400b030704120000c04d6282d9140d0700e03604078a0075642c50340f2000d2a0058081107400c0b01040c030605c2c918480d442c201c4000480c2c1050008508103039050f49a5a00c0001d03007083c20401250f006104804010540070402c000484064a2a009001c1e0520b03100c40780c4802d1500a0700e03a0000760481080003000e200308180142d10001c0041d80700c00c070510b04802810305501080c5414841d411090b44030303040040d001496038059018100b00c0b621440014a80f401c140c040c01c1d1030384074a0b0803490000c1d1645d04144603031807a040c081500610384511a = true := by decide +kernel

theorem S85 : BRFrame.sub P3 P4 TB 1680 MM 255 384999586 1250 384998336 384998351
    0x100f0c020f12070b04090c1b060b030309040507030e06090d0903020d1b18060803040e130204091202010e0705060c06011e0305012307090503030307030e030f070b100b040e19 76
    0xc1d030f800c0c10210342019a4120020400b841540c084d0f02c91b400403142c4c1030401c6182c0c11a481560495030554001c014070f00d6880340788004c5282c070706005445200c10050702c1800f1900703100501a02908422180b98864420100041c1010100092500d400744480c2c9442e4000d50554007032210208515034156002003c1000f00303074104440406400c01040c20b00c100f01a600d2000344080c0c2600c01a03440558543c1c02032005000e070280c83e1200a80000b0001c010002c00c41c224404070707003e00049140030300380c0740c1948050220181c040d0401e800400e40c407000c2d211740d940c03180104140d5005503d2601c034140e0182c40140003082c206d041080326102c0b100980e542c090341e6581c0700d90941c1e2142c0110700f4072506425030b0358503061646c81510381128407414a04203043c02d010110b40d607800024494010140c980346900c095110074800c0b5550081000440d0b5039071701040c00d042000060a41e800c1c01e00704481c0c1d0000528481c1d190540701600c0441022003d1078640712a44d80d00342c403117004800b002d07503500d290 = true := by decide +kernel

theorem S86 : BRFrame.sub P3 P4 TB 1680 MM 255 385000836 1250 384999586 384999619
    0x906030a080a14041502030703081f050f0d1b08010f180201031d120a09050103020c0a060507050421140a0c030f170a020706350c0f030a060302100f0c020f 68
    0xc22081084140d00450352103407203103000ac1c00c2c03482c0940f900348054296003440c517801e14607130703018015103005980104600c1420000244803081c11103000d00740704200f92007007214080d5501110180e0340c0c039000030300202200c041c1c6141120603403450904480c42400c0c0030001236220b0382182803801d040f80b102c0d51420a01203210385c101300070104900f084c8000042d410801540054886000344403d00b011418926404402c40c1c0703891108030000c04065403440020344040c0200141c50291604082014040c403401a00d804d0020021380240c0340504a42081c940e00003000402014450344001e1076083c8070f1842e903800398040c40c181d1003256070f0811141520b002840c11030140104103516401800c00f02d213000000703041800d00381500c9145411584080c101c5801285685d0307c1e480d641c4154440341da030b42d07904041c02070007a800018058000007060240b490702940040c030640340215500031100a01c91400c0c0d500240200d800300125601106000140c0b810003424101000044c3c00300000d10345551 = true := by decide +kernel

theorem S87 : BRFrame.sub P3 P4 TB 1680 MM 255 385002086 1250 385000836 385000859
    0x6041508030f07030306151209141002120a0203060109120614040b071409030a08160501020f0403030206010e0f04060c200f1002120f04080412110906030a080a1404 72
    0x640c0c00340100c0401d228040c1640350154600802045c0490b40c10001c142600401c0051004001c25455031641c802e44100151409103080ba0921a410b0318919561014bc0b07002962010b40009030345001c55010401407903041c403c4078003418058507030302103491501c50485076100c9860000d4615a540d983d0481180c1e8400010300d1246105014401003492304034000f604251a010801074000c0d0103000d00e142540b00000c040510b690003a1400d0b4980c42c03480019210120302c0c45c07000300594008200c1d41540b240820140080d01d00c03030307001d0718117070f070b880d43d04554a039141181e0007044d03030b9240030206000c200030350b104100319455850b2800c41c0800180d00d040d0241051031041d00c0b075030b00c01e8014810100040c0050b00d45a592450300303618100c0c9102030003d210030040e00d25101459010041020041c401c1c0890b40140300184410f6100421410211407006000610034020000b2030005082846d0104032a0030495000441d54101740701e400c012100040b10190313484014604010124009840d00d = true := by decide +kernel

theorem S88 : BRFrame.sub P3 P4 TB 1680 MM 255 385003336 1250 385002086 385002097
    0x60c0221010603030e10030618091b0308120708160c1b0f090f020309032b0f0b09070315141c05100b03062a0d1515090602060604150803 60
    0x251030300c2154411171802d201880d4040e00031131003050300c0e002041c4102143c0a101071480404480d0200714610035080031300d07800d00600445810131001d0a800002c014420010302489007045000600580d98182d05039003540c03048a05000040e038500826110ba4021507901d00e00d0307401081120b407003c540441072048100190000c40314a4100306041201070710a0081c07041f01c10300f0312070650460500c00482c035601d0140301c1c01c4654035090024a1001c0b8510381c0c2055510b012a0036047c0141202030684000034101d2001060090303940100244899009006101d420100d03102001a03c51500d02850714800ca25003d02d603001c0e1003194a14404007200e10404070290042020f804c81440d007000020495115640080c0079802200c1007203a40008010030001a9103080c07216080c0032200e0851114a00c20320405408046c40c2441c400d0140c4180086401603910124020115080406040e90303402554401d9100681c80140018011304107500011080071002107134078032841d118a00d250854010303 = true := by decide +kernel

theorem S89 : BRFrame.sub P3 P4 TB 1680 MM 255 385004586 1250 385003336 385003343
    0xb031f06020a080702040f0e0307031d0d020d0b04020f19030b0612150901110d020309150402090c03040305070204061511010e0d0c05070905090615040c05030f0907030c06090519060c0221010603 85
    0xd004003600e486925400c02c54240e80803074dd10440780e01c095000c01c505004904010300a426000005001d640743c85070362102d80c881c000d04201d104401c2d04c628001e12512804241c402c2c8071604001503250412100610310f40145100030f01207402581245840d81000502c0c0d00e90554039280c1c0e122908003258007800e401c6000c0c01000d6160700d401c1c0e0360399207018044100b4035420f840321014130000d62100350702d40340c015a080310000d68aa940341000e603041c0c4039184000303401601d48140042c5c4001300e0040c2a0345401a0390701c21005540003011340742642c080d6110702030300b40c000301114080c2900560110003131a2241c000d03030ba5210380c5c60001d082214411181c1a803103801040c10000c01c211041134144204204850800807400020001400d0703000080044030070100384c101051203160104550001180d2201403080003546845006160001500c00d00740954413044030780b184112184001c6c3c0a840b07040c0d69581a14946400b041581c0d01000880300207090089440781030b000e820700840f4091400b = true := by decide +kernel

theorem S90 : BRFrame.sub P3 P4 TB 1680 MM 255 385005836 1250 385004586 385004597
    0x7020f1f0e030301030f03120b090114041a0102030d0c0e1203120112150b01050c120d0c1713020d0501111b0d0f03020c070b031f06020a080702040f0e030703 69
    0x640d038440180e400240412180750420401440001c1d02030ba007242049170140380140c000300c030080403030004021941c0c2a0b54003c1c241400050b050440c00c00301100d0700c4040c2d030244214185070180100003207040300d030340340581c105010400451f00c40d944204140f00c41d502d8810b1103c40d802d4003241300c2203055400f02c5020f400c0000d00801c0c4221002c44940144080281c07101010001d440d10802c600101440e80f40c00c0d902c0780c074144041c4c0e11960541d204203001c0700c03e455025074944845500b941c005880d01c4004d5040554003100350f80a0795901c82e4401101e40071081c540c0c5c40038000380340f088140d2012684001028680710104000340f1541403410705150303446a491200d41000d280c6101e83d01580d00a541c08407540c880440e070b0080c600c40c0302120904001da01c840384400001d0400302d0f66007180d510007001004200c0603a00fa804c440390400e1203249800c1140391103804c00c07a103031070b1a0940034000c0c0701e08215010050a01346d01100d00720707000703603c0002c8008078400300d41d0440e400050f09800161 = true := by decide +kernel

theorem S91 : BRFrame.sub P3 P4 TB 1680 MM 255 385007086 1250 385005836 385005883
    0x904050a030207050a080a170d020d0e07140a05040209011403040f1b08250b0a080604060f030305040e060319050d0906020f070b13150903050d050403080d0507020f 72
    0x16010846440908021507151505d9031402d1141580e500550720001c1407140484e00144410f070b40b40080d10707065001e5030015501c40e26880070180c000c080c4031103e4900b610407540700003140c0c021956041380c040720140038a00001d00300024080603500840c145410003614448100c0107201d040091801144102001401c105541c10032106010a6454070040005c0b4104104401d090002c0c17110b404001a60704800b422420000d051458041548440d8215000040c031b82609544403201d5440381c407084504108860b100e140140c0c120141c0d000040101c0c2c02040117000e1503a200e00d25991041000342140c4450314a4440407030960b80003803044445920001c1103400740b035080303040c0310301414181c8000d120036000800c400f0f03036a140d540724181c04107800040c00c03051052451000d101070910b6001a000c094042680145407803210711064505008502341007100510402c1224101d0b900304800a00f011042e05210009240c003828a509502c2032071100d1f04a01c005000398080c610241440800c0003 = true := by decide +kernel

theorem S92 : BRFrame.sub P3 P4 TB 1680 MM 255 385008336 1250 385007086 385007093
    0x12050c030d05091509060a0b1e09100e01060e150c0a02010c0615060c0605070206040b0c07020112050106020a05160e371a030105090709020a120e0705041a0d06050a09020904050a 78
    0x2504623405180c0315074000341013a90081494450300a8500044400c4031150302c645c1004000c002d0b454019410328542c2d1000400c0d00f6400003030300820102e00340e070304098424110344050b003140074512450400d0b800c2410300d0700256103d0480740718100e0250300e00040c914403a41c0900c210340c5513a44001e004ca16030182940600c80701d0b209a0350b1125041c00030340210b00d4180e0b50005c40e040c00034160304c0b00201c04504641907900c104442c01050301e8044c4104095611030101959414003400c0844040c4554a103141d050107800e10030404491652190001503140c030664820761883c001b2000d4500c06c0c00d403861007030303008040c1c603009550700804e200064016200729840207510000140c00d0701076810623041c4250154002070304021074200400050b240e10200d03508442e1800c1400e201c048090400100061114004c200e00703080360400c95082080c680c6400d0600d00100c480b040075076110180e070101c4070110f0020341205a00000000000403021710075030000d03030118016503098455500a55407482003 = true := by decide +kernel

theorem S93 : BRFrame.sub P3 P4 TB 1680 MM 255 385009586 1250 385008336 385008341
    0x20d0605181e15040203010e2203021002030c071a060901080c03060105040b03160e070f09060c1103071a03010e0a050105031f060510030912050c030d05091509060a 72
    0x49110302010a0582c0c076040b80c50005107229100c20341203215005001403821954901141406503000b0425581c82d44c1d94204201aa907058605000342400d240c0c001002400120790003076502c2c1d054020300440c1c0001000c00001350401004100d0b40a0108111000075019000321402c200d0150b00400c4c030b508104c41071201a01c0f05070050307400b65109280c400001e9a00240d41411580b04980111f8120b0940740070a0410007002c2080b48003041c1184080340c0d80a03403048062003040e0300c0d03803413040032045c0300011201410540f040c00c0116068101c5080814004a41d498140401800700c1c0c042640c7d403807200100303080f0700031000541c680110051100e10360461209400c01c400c040b09010a5041100198603405441c651241e00f407000a030364040c1c1489a040000180380062000c01c20802c00c4130007602914502e2401c90701c03070324040164080c5900403415190720303522402c0154104000c000f41e00005002c0501410340070722a01c144484100e0000049070701c00c0381001c01610031810400b81e031005 = true := by decide +kernel

theorem S94 : BRFrame.sub P3 P4 TB 1680 MM 255 385010836 1250 385009586 385009609
    0x3040f061e09080a02040203040606030218091002090a0509060117072106050307211205030901050a1a01050a020313030309050a093b0f0102090a0f0e150112020d0605 73
    0x204101004100f02204000a9100e030b819011500141e4035120341c0740810007041c00d0b910003508090301141e40368009001c06012803103068820f003540c0040100341c042c60100e22400100b541d11018542c014446410003030011035114806060061402000c5288001c41c40011501540040d241c80b60703454840403101d42c81d280f04261004c0c18803855040600003515400c581c0039000c0c2409030311103040701903084586000f4030550418001240d16586070300052050340103e404028940c04c14000c144200c4031817280742d0000c2d44c410481c24000091100441d601d034407041c0004110700c8240010503000e80401c60303800c0154441c0c5c03540200c2500c1d12003402181201a80160100e40c17030480a10880341e106004840a0140d04121090001c010a0404404e42c01d00100354030910401ca8203c521410550003460400021240038044607035904a0810200c07560003441424020200030401da2402d405a120741094141084003007611103040100880c3c0010169a94258542504204c8c60038081710080 = true := by decide +kernel

theorem S95 : BRFrame.sub P3 P4 TB 1680 MM 255 385012086 1250 385010836 385010897
    0x1e01020d021507050f1207021b030a030c0204051911120c0c0c010c0812040f0215090f04020307030e0f010501090f02093a081e07030c031103040f06 65
    0x32265034440c0011200a0000382040c00b8403600048502d8000114011502003c09080001b10141030030b102c000e43d100d031408052152041442e003034513101d240c000b40c2c4c0c01301581c1c50783d40c03400c01100030b41c00d00000e0318001d01500d580c54252191242e0251041c00b800031086001d100b195140c280d803600d02c0146000141c400d034550f800c1000450406100428000c0303035082c00f8206980e501c21a4a01111248550315405034800500d10a1200f040301c25902c4100ca18000c030741e5a0b403601d070301d2a002045031003084012640441055288852400c19401842e803115080c10b0003e000c216400d441802d000c52100c941d1203696440005100303080c00c5104800101000d60400c5042114820119050b03205e03840582807801403010740501d030300061500e6840002c2a40000a40390b00003890400c0140d04202c040b485982c05171840f1145034050070040d17800c465015a40c60312038a02135282036034040080c04110040f40400c10000c1032801e440c5c401e10000f0f003403541c2c440c80b0310064030300e0101c41d08bc030070401e90 = true := by decide +kernel

theorem S96 : BRFrame.sub P3 P4 TB 1680 MM 255 385013336 1250 385012086 385012093
    0x20a0c051612080f071401150f06020309040e0102040e0412080108060433180201120c21020904020f0a0e090603030406030e0109052e090203070306020c010b1e01020d02 74
    0xe000b040d407400d8030505034030f41c0420000d41d00c4840020481300742c011004000c10a0715620042c0c1d6400d02c0c1900242c02c18807103040701040054480340c100744c52240d10f00031a001640103100c0c05506280c107401618145081e54001803415407555007180d544081201d040e60f80c440501000c10605170b00811503401885014064141c5040607550090b000e82501c0d0020302030508038182441c84511024406402240d44000304600b02103148071a5402050027402d0b804211320032250308001602e405601085409039031810b40c000d201320010b10b00c40b0380000224520580c28403c6101c2d64030380d4070041044005c464901526414003140040ca5060442585402111150f040c07003078640300082600c00742e550074100416aaa82e0640550050900303207006070040c410529400b24403655514080348e009500c0a01c41c61164552001b00c056656283e0003c0d0140e11001c0100b011880c40c0e800340c03415030190400030072507203002400074200c9001c08684440412119003003200c1503804118038280c001960024 = true := by decide +kernel

theorem S97 : BRFrame.sub P3 P4 TB 1680 MM 255 385014586 1250 385013336 385013339
    0x20306180c0a0503061f0e030d0212041e120308060406050f090610110601030b01030b1825050910050306160804060c0219120306060309021e040b04020a0c0516 70
    0x1ca40181c00303250080720a104000c03000c07032004e079100440d4220410045004480301400a000102800d01c5121403600070302030026442142c1348042024800c0c02d280c030f00010b20b407600e404440040101b5818174108166000400403030b200302c001c4035840200e07020750360f014040d0600c5003c20003198a035600041c13042200244034040c5441c1c84c2c90940d031055080f42e030340d0300b1106c1e41c803800d9800c0b0840640d8120381d4090003001208014017262511b060b24000d12082d80b65548900c0d2200d20040843d07183c0c0f0207540310070880d518400546140e000100c8011201d0040760750f81d00c010035580801584d190000b0020201c05004504040120a42c4030700d55003d003055240007803202610a04001d0406880180c03600701c3c4180550003000300f21450203030800350302c404201c0c0741044d4514000c44a8070000290600000080b081d1080c0694850a0380040000c0070305000000c601054414181c203c41d00b1545443c540105a55580b0140112003000c0d00e5180b0300304000d01e0251304242e005420b2164030000c5100 = true := by decide +kernel

theorem S98 : BRFrame.sub P3 P4 TB 1680 MM 255 385015836 1250 385014586 385014601
    0xa021e0a0e0a05030c040509010b0d03030905160812070512030a0b040b0303090a03080903190c030501050705030606180a1802180909150a0b09040f150c0e010507020d1502030618 78
    0xc1c26200e5174000d407400580ca8907014000381c007401d024000c00303410441244546c420182d055011a09060081d02524284041400068502800c83c49070390320f654056802003400490103070040060324401c0003110315611140110340715030b40040300d1a5449990751105d040960906005030110024110702031460b2581d60800103080010b00d000c0139054400103d0020000d031800c20440c640c40002c02030300e501c0030000f032400000342520740c0000c66040d4200004910164010b105490091800500300ea052a000180d2481c050b02e506006640c003c4070020000b0321114000c1710210914042500980c0e0740b0500010140300041e4442070f940101c0494081042515010402c40f16820ba0f0300e290310b10648801900c100039040c404050f661040701d02043c0400c100480c44608852841614410030700420303182d12000700c600c0300c211007000c1040401c0415456101d00010050588010404001540395846942c0141407900c10822050f500000340b1030340d41307080c80c61b8020104d400020f101c003510b170104 = true := by decide +kernel

theorem S99 : BRFrame.sub P3 P4 TB 1680 MM 255 385017086 1250 385015836 385015843
    0x11040e07150c02010c0605010b130e19050601170f151e06030417040f0603060509091507051b060a0e0f03070f0c15090e070203130302090a021e0a0e0a0503 68
    0x604507040040d0b00c0101d0b003c6a1055010320303055a0480e03428081c958640c3e40e0301a480e4402e4461580301d04410344002510700307403a51607a01c243e1201840d001560700943c0710102500c0c000300090304104151350040542d00d1185c0d2500e0083c0e500381700402c0701c1e1401c114030700c0c3d640c0c421040a5104200f26620704040441201840196503000c0e507229032a0749481c504950081c40c0500008820100030902140c14040402c0c85801c440c40350380c1c00c0c49420b6a034070605c2407075141a640034210b50071040c01c03413080c1010803080c03076081601d1380751040c03910a091700600064100111000c011b030700014140954864140155074140c005400945502c416251a1503176034480d508004005003881e007404000e00c0301050124000340011a0a005200d03444c400040081080c0c0c00760f41115450540400e0109200109580f4910484586441960f045401700030400200504a086d100d408014200240e200380b50001c100d091941180d5449608400d405458203140412550081e10594010032443c0c4d07000 = true := by decide +kernel

theorem S100 : BRFrame.sub P3 P4 TB 1680 MM 255 385018336 1250 385017086 385017119
    0x191107140904081e0c030c07120312050402120a0308041a07080a0b030a1e060f0e0a0201050c0f01020712110a03090501030f0f15050405010b0910120b04050411040e07 73
    0x181d00c0c07660f60416881805000303605a090803030113540c0824410403030071011004004000c91002507441c065203688803400d15803035142000c3c000440e00744841001034925030090b5007140c001000c071022420f00701d00c00f81c03805040075022400200341000b40070812420007840807050701c4003841c29007a8642503a00a0508900600d000c1c2c105072910703407081032a2001d22000021503005008280303400c80070000c902404c1110b8400301c8919103003054641d210720240c450340030030705400c0c4080e20803002c10b1f400450b1107803c12034811410f401102e20030400b07543c0920003410501d205804001400d040088058042601c0805500e181c2c0c000490323100c0042d82c0300403003000303441013401c00090040840c1240c80c0240742d07110341740c114649083d007440300c00c10a41202c0030803140104d4080c0100c2c3e81714809007003130380207000340c0580001000b0004e02d40f03503020328044903440078803420000e007041000000509550064900351522000481c1c045410301780f5006410012030543c0c003c0c03515620b0b210007103100c00e021 = true := by decide +kernel

theorem S101 : BRFrame.sub P3 P4 TB 1680 MM 255 385019586 1250 385018336 385018343
    0x1213050c100e060f1206030c03030901030b0301291503061f02160e16020c0a030f0f0b040804150201020306010e0613080114070e01170a11191107140904 67
    0x54264110300680034100001e080e04014010549448422501502c00d501100d01c9402d584810b400003410fa01c7c0000310542a40e02c0680590f0400745c4078401500580148000c095140d52598041c00c0310340030700c0c0d10124600034141d014000d40880c00f401d10040140e603001c10f801030035040003040b146440c0d80c0300610f0801d0a40070302d0309d80040781c814200d01b0603002c0d40c0481c10b410900200002c00100c2807a00340e0040f00080040940d00fa00490141c1e0b480d0b08840c0916041102924108007082c0c0d50f00010401c58080c26a100390b035446980e50500c0c151040340c08682210001c1024002800342c02c440280e2544075000851550400b43d0010b030980811a1449200d44030009a5a0901e940c29250000801c0d034180240185a06243c2e0410070704030031244080051044c0040841d1580700d00010400001420702c8010316440b1020b20301d0203410743c1c400401e82204200104410705404400d8908100700e40e64504402d04c2800000b9400c1258940c0004a070400035140311006685445005410aa0 = true := by decide +kernel

theorem S102 : BRFrame.sub P3 P4 TB 1680 MM 255 385020836 1250 385019586 385019599
    0x20a120308011a190906080907030f0813081207050105010e19050403030b0a0e01140904080301090903030b150a030f0515040515190303180e04020402090a0f0b1213050c 74
    0x691481c04003c0d0320809003e280d1085200300c000440c25040f240c0a8107407011510341006941e500c0d845c480d50b0305128400a0140c068251030400031400d80c0d0000c050740d00101c8191014280c0b1a404d1030320349640c1d0f003005125040300182c1c070b506101082c4215070140c041d1000c03100035828155805001a80d080c0441141580d03110003040406000b9409143c0c03110000d800d41d00501d0380d5680c0c00d0b100c04401d100700154903070701a90340312141c030b0702c88400e078480c590000040d03040d0707400c1c00c4c10700d80103041809044007456501c0c00d42c2e001582e03032040e0744860a0004c3d19065a24008940000d0554003075291050b12079040400303002084a00700e102910401f402d40d00050240d44910080742e10406541e0305030b400c0800c442e032454040403400c6030003060324001c1d191510500280c00001202558a114058403500441c02140044c074003a00185022100100a110700c143c40e001510b0703000e5010b0b806007034111000a121840894400d2301d150f4407a20380002d03114109502d0311840d46400e45030245a01c6a039 = true := by decide +kernel

theorem S103 : BRFrame.sub P3 P4 TB 1680 MM 255 385022086 1250 385020836 385020869
    0x4030c06110705150901021519050a09030504120c1208031503010606051e09130b03060708040c03080d1e060501260606130801090614090109050c01050310080f0307020a12030801 78
    0x1f4802c001c1c98890035020f070031001440c10045980d00030100400c0300b446c200707030812000800e448400d00690f04020b0f81550707200c1c505031400490300802e010040e000c54201481010014503190100c450310342c07180c0150741c800c0e664248003030111400b0380a201c00718004c3e41030184c2085443c1e041410b4a4940d075000014008103d4504d411170040e12070018103550000c0000000070946503030368404102d00304264206c452540314048c0c19561034004540051a69021806c02d20008803a034001d8000100780b620081521a03502d2190f103140d50711910a041e08958500c6e0800c070300d682c010024000b00c5c03644c8420038560b40d04c00003c10307111b040c0142002e008850000d14820b000d240503e1001c000c0c04124004c00c0700280c6860444050030101c0d41411207100302a0110381d07074a906114a0b055594050028600c5159500c01541e42c6d400c0185418134003203002c00005081e0074144854208405840041d40c1ea5000c50f20400500400d243c01c80e4448601104660b8006900030001340c1c1500d04280d1b102400c207 = true := by decide +kernel

theorem S104 : BRFrame.sub P3 P4 TB 1680 MM 255 385023336 1250 385022086 385022089
    0xa030302090411040e07080618162d020601120507050904140a0303020904060e09060703090302010e0f070f0603020a051e0f04180b0405061804051204030c061107051509 74
    0x280407030304283e10b80c003000180001daa000411552402488143c2e1050682e40302c038000c11144242c1c51140d554181141c501040390440e421200444040a50801c05081441d60444400b07000c480b841e500712500d0105201107540da070600c0b226000d130400035002405a5010384403540d070f41e0f00b240207a40c0a1982103000c2002d0142c0b0341038640500c40003900326110390400d80780c001c01070b400800310a801607007001404520a4030355400d8510503443c0000608095541e800110040c16031150140c0655580e6003602c406010b0a00103000b0455284004029413480c26003105d05c032a960307a0000e02050310600c5040c0405a118040700e41d03000008680e2501000010341c1d500b110711849414000d05c0300006400200307001907683c0030f090301d2428141040f0700c0c0c800c0000c0c00140c5804407406a40814130550741000400220111030300b00b1700403c1103485001903040c2c0a07149902541044d18030b020f800c1410400c04ea403003410818000c140070060504103181001240800c03402c00310b1080c96950104000b40036 = true := by decide +kernel

theorem S105 : BRFrame.sub P3 P4 TB 1680 MM 255 385024586 1250 385023336 385023341
    0x9030201140f0408160b04060509041e0c020d080f010806010303050307090f0905060f1527040501060c020a0f05030c0103020d0219110c1c020f06041e0f080d020a0303020904 76
    0x18240c000480642d2a42c0d2041c0050391200c1d0b1030308044a0030b501420000e80708801b0000e45040310742648a4900c0d0880110421006140d0300070002c2400311100024140311400b0703c581c1191414540090030081005800982042f400502614203400410300603c04c04001041c1c540c1107a506043c41c03512030329034080c150f400e40140e40203034800c0501c010001405c07048a400181c090b00302075441120341d00c2400148000b94008000c4100992000c00007810100324000c0f034021220349080003951a104080000340958100387d202100140d24004183c003540b5000c580c610041000c0c2000f20038451421002c0b035203900401c5540c0d4141a4080340d03021484015804540b03142d44480c810007800003605001809e001d5400200401521903101060070a0a11105d14480c1c480007248001800d24141c0c2005040348a041180e45c02c01424007002030032210480480c250385210701920501c041c14076000ca91411642d501081c50303036205003030f6800348a801041d850701c115094500940d6403038240740400c01 = true := by decide +kernel

theorem S106 : BRFrame.sub P3 P4 TB 1680 MM 255 385025836 1250 385024586 385024597
    0x120306011b0519081204050d3c0224071418010507020a030204140f0c040f12030c051506030d030903050a110705130f0f020415051e0c030c0607030c0903020114 70
    0x1710705140301000100315020680d086002266200e0203c010080000307110501d0f814003500b800041c48000c003103038841c1810038200c4181980e1044858074150580060211b9140c042501541c554640c02e1140b075a8110680c0400446030381c803001e0401e21a0242d07480c0b86049509058140f04001130b0090039501c410184001554000d00180211144618401904a41141c00099031400d400101d849000684221030403070780301c070b01008041802c0200f02d8003100c04405049041c0051480f4100014a043c00b501644044219038501d141c6040700030b060900e4a2000d03940c0405150490b00d43c000303901300c4245c800c6100c0510b400c025196103001403a28068085d001310b0341c00600c000010000c140076030440103981e2a9100d007841040c5603411210b061380200e0149484003034001c80761104083c800c201500744a255004241c0c40451003020180155002c514901c08580000800b0551b41e102005203540206407031504008807518000014880449408002d040028044062a210011805685 = true := by decide +kernel

theorem S107 : BRFrame.sub P3 P4 TB 1680 MM 255 385027086 1250 385025836 385025857
    0x307050a062708030f060a061d041407090f05060301050603070c0203120d02090f0a0b090105030714031006080912032212030c0f0f0918020705120306011b051908 71
    0xa1082c0302c40d00700540190000c982c0f072450210328500144850809654403012034402d51109540014980d402814502000500c176811980c1c1c5d140446c0200c20540400e07000b095580c440c0300000d410076040c0380200c02d8135000240500020401000140ca030034048030b502c00d51034078101009042d0342c0f001030300702008049403802c08034001c6400100d19640381e00a08040e0403c07160b8804c0e101600051088003515445100c80c4e02074140303d03d61840d402030b8011b5501070300900c1d2510783c440e030500051450b0342090380c906c200c0d035903162020700104da0004411500a030180b402010107285900c400881c0744802404c0e559003029149611006020f000c088094507a48800c40494000038040300500074810385020000007401c003001407100c42c0c001d1184a1710001d16641c1d40c05030604004000190a6032100d80c0d0b01c0c526800c00503140450803e10003000c4103151403014070358070f09141c000140f0500c0a000c03103c00f1603450301c41500015a00045a2580b5000c400e4200320b204101c1c02d0003000d5028654461 = true := by decide +kernel

theorem S108 : BRFrame.sub P3 P4 TB 1680 MM 255 385028336 1250 385027086 385027151
    0x723070507152c0f0a050f06031807061211340501060b120711190c0e040b0405060a0e0a020904020607140703170306010203090103150504150e090307050a06 69
    0x883c003c03c0205040440fa00044d50345a034031009034801c110103031203a0303c12107401504007030103031011742000f4000796030196203100c0382029049c141e210240761401d00d5010100196035801c04030300b5409a80140e000800304507491a041040c0000d1410701c04540040403c0a065055005a21980e048541d140b00f207410030020090503a0f1480a010b1075030107040c1050500407000002412540194048006088558010603800c003141d441d0032041520410b064556084061000075440d14407800716210314070803031442001341443c0c035041d4a0080701034800ca88050034490001004507001507440c1c0000d4044034501d44c0d0740c942c0d001007a090722541c03038058503400c0071000d0305000304400901b00c011648603c1e41e02110b02d101c0c100754000e501041e00c816005800c10050701c2c10a6100f81c0150446840580c038040000d691580090121190428a18801c00d100181003000803a02081503900c892407002640c600075a03542c1e686d496543c5010700912060b80d03403000124900031003170403403444240f540e9007 = true := by decide +kernel

theorem S109 : BRFrame.sub P3 P4 TB 1680 MM 255 385029586 1250 385028336 385028387
    0x203060906011107180f06060f020712060b13020c0115080d08041103010e160b040609050d051c030b1203360a090504020f040b061605010f0203072307050715 69
    0x601c0c00f914446e106041007900305100000d07003034414100c414500a1690103820001e041c89800228190b50744000c0e1006031311410f140005070b44044400607050543d15006940b000031076107407400e480c0041e8403601402c200b81000c00c0280d201080b00000c2e031840303280410b61507070b591506050401502c100306826618103448450710380c5000035007400c880c00304950b003000c0c07941e2682904024411802508002100080d040029040492108201c40e01c40d60958601c003401800030340b02c1c4181e92106c01c00103521540701500c01e041041c04c90301e00c500c100b0081c0d45003169004000560503000c0103c008004c180000104400c0f04081c400b018815005018114060703440c00100040c0c5000d0740c0c00e910608440d2200316207803410b8840c44014101c09851036080505110020900000040050300d455480388085046040030348025032181000e0f0700d03004202041001071100f0b00720000c201c481c00040400c817071000300d200041d440c0d0440d4080070b08040340c03080e02c00341202c2d40040700762250302031603000d0340 = true := by decide +kernel

theorem S110 : BRFrame.sub P3 P4 TB 1680 MM 255 385030836 1250 385029586 385029629
    0xa0e030d050129030c0a0509030c041e0b15070807020a03141005012304050a1107230303150904031116050f0f0a0e0402120a11010e040203060906011107 67
    0xc09030f04285400f90301843c072181811810489100a50b0050000d8204010b90300200380104041c004000004007a01c103500c0300e20b0041800c1e10001401401d2000b5442d10490b00344900344208a0b03844415501207501400e01400b61507680315000010f0000000070424008560300c000459010f99842549460b80310030401075130b5030b28041400d60000700b40c20f210011540c0c0c0c034409108103c0704e80542c04052840b00748070070300005120281200307075025158060581c80b030000e04014030002d841603ca0301b0071500c40a1081109022000410196070010020301520714103028485410b030320f0032104107145803030f50300d015140c1c640044e01c0324009006004071080d040c440e8080c1881106e4091f568134240d0604c84041088603200d0007a05507200300c0c2004107020b2060043c0d4003a6010b480601400520400510000e20345980c0100840e80c0d08482176500d540303940c1c4418013540000e4151025070031030400a00041c000c100080c0401e040000c921816603102100b005103c0003400e00040d08046a01c2100b07 = true := by decide +kernel

theorem S111 : BRFrame.sub P3 P4 TB 1680 MM 255 385032086 1250 385030836 385030859
    0x102090d0f02040c1403060112020d110c0607030504210c15050907060503010b1c061a030901060f052b0b01150206060303181009090f0f0e0d05030a0e030d0501 70
    0x4010b0f44142c3c0782c4008404082c0c002d4140c081d41000340081c840c07a555640c40152400c442201d0061039036a402e10843c1c801a80340d201380c43c44203900715260f41d01c0340044a0f01c5c1e40703040d000901c000101030130703c1d003408005200004611004a050101e21030300c01503e80d81111215800000034140c9416030548590039180c070f50080d8000d590170420b507040b107622142c1c192820b10081c401d040b040081000074110410040070380c071190f04032043d008100541e13280c8410903045001c6440401d15040003007848a40b110034811800105039040007065090302d0280052158104522080c200118100c3e0003c036620380c414400301102e5200070700b000e0b5961a2002000703405040a405409849850301190f400d103000404d403001c10748000780c070340380c1c0e40b103600c3c04c3c00710b4001c294207020148150f2441c003052000c1c8a00a00c0c05091140d000001d00e1406d41c00000c05a401050081009401c05202e00483c50742c000d040781d40c4014211000300d07d070404620344034907611801105030391552508002144942856 = true := by decide +kernel

theorem S112 : BRFrame.sub P3 P4 TB 1680 MM 255 385033336 1250 385032086 385032113
    0xc0302040c020a050c040b0111070b03180a08040506030a0b0a080115060e0a0302012604061401120c091109030102070501060509090325080d1503031b020a12050102090d 74
    0xd4804000c10740081c082641e50b03c408a101600e070340d000c421881d5842c58103400c26450403806151070307072140c3e5400101d81e1410401c1d80109424240100801c95414500c81140c4901415000241064102e580728a013a82c815405850b00800001000801034115508607403201900585000303400341c0c0d40c0340c1c0b80c1d00800d080c10001310b58003100741c400190b80388245114403102c50010880030600c5d00e95401036075101d04250541d004080c46402e40f400030480610b4551281d800744001181000c1c503d03040c15004d50058200c800a4400712040001007030032002074100741c0740f0700d0304000b410040f0748000f1034840c014020455415800000e40c50300300041908440e0440e8024ac80071304060302c1d41079030703103440c4d0003681c1c260400400380c0c51b81103800d03aa06180c10000d00340140c18292030114a03500340e0007540e260075525641c2c444040c2d0100200361307000c1d850031300d41441840c03c0744511180307900007415101184206a5451001e118600c1032003420347c100c0c3e45409006240000c400d40c40d203070801165059 = true := by decide +kernel

theorem S113 : BRFrame.sub P3 P4 TB 1680 MM 255 385034586 1250 385033336 385033339
    0x30a0b10120f0212180708030f040305060106170424020706020d0501050406030f080a03110415020f01050702330f0a05090109020604090f1b0c0b011a0a0f1b0c0302 72
    0x304010001c01d41c40758001e542084a0341c002c002210350300d4a0498000d4070400c200b0840c20701c946d400c005000c1074184010003100c507240101d60769172415410002c0c0b828206070301c100104403c1ca041c6001e5180c04c40d80300f03a0020380c065050701d8185001030b0a8001c00c0f40344071038003595610006050040054680c010888142c041c031040c002aa600c4081004a40c010b100181500400458020018608200074802034000c3d040010b00c10746400c681c800c881c1c01c581c100c145000b03444413000340425010030021400011a000078051032901e900001c0d2506801802a03200700710031080294401003e54464070b60300d49504041c0f10b246413036060503074007085c1602c1001d107142ca40404544482411b000300724041e40c015008900c1c1600d480384003070040040e102c0500300550b41d0b50381c04200c140314407002c41c1c24103c241d0752040c610072541484820030386c0692080740702c8042d0440040c0600c9000b02903441c2e030710300c0b410701903030140201b0816281c06151240c0a9130214000b01c0510400000c04403d4094a00 = true := by decide +kernel

theorem S114 : BRFrame.sub P3 P4 TB 1680 MM 255 385035836 1250 385034586 385034591
    0x5040602101b0c06090b04060501090e121e0415030209130902010914060d06080615040608120a0c06020d051e04020f1309021305061221030a0b1012 65
    0x328401820121010441e8120300c40e98110b415a40c0540070381076003400310b03204010000d4019203030f4446c041064401d4074202c880030389407c0100501d82a900440051a1041019002c840c100143c03070b01c41440703018902e141c80c0c0316404100c002800200140c80040c0000040c4180c451500540180250701c2400c0380c038491201207054a241130421300c030780000c0550603181d82e4011410070448941281c00e41e0b075030f075620800800440d1001c0b4880c2c002e01004214041c028846400c0c05c1074000c0340d80c84903e40c114021490400d040040e213000090400e078002c0340c9011241d85d44087d090458081c1c80c4600080e01c01c900024542c030320144158003880c8220364411401c15815800c5c03400c035600d5441520040c0d484590a00701c09040e1616036282c01924501c2400014030348030380c2d400b042c40e00301141074104c00745a03a1000c0108a040c441904001582000050700892500801c5500c05200140c020071880da0080000b405264240e401942c008a00800c00342041080040050441c001803403414100e50 = true := by decide +kernel

theorem S115 : BRFrame.sub P3 P4 TB 1680 MM 255 385037086 1250 385035836 385035853
    0x142211031504110a080a020f0415020a020109120c030b04031e170a0203090c010e211b060403050a062f2107120207050a021c11031b0d050a05070605040602 68
    0x540f0902a01d401442d542d45000c0707161215500e0307034040e40080d40d2618a50004001c0014000440611129100341d140c000d005100344c240009040d911044d4032941c4c0361603104904600040002e403c5d0340a0700d034825800030198595007000c40d591a0308898860040c4403800742c1c0d955103604110034106c0c1d0980d090103031056544a40800c2c00341d0005030303080c203d82d500c621050000b40d80100389403031074500050300d0910b889008103000d2000c0184a042e645098100314a0030750540603c82c0fa0500180c01510700381c0c50b0914542d0391903601c4144070340103041071383c0d40d40f2004a000c6550700885241c90714072802c0c1c211110079808a80c180e41c041d24030080c001000c0d0784c107203004640c500034551045106840d20131054005010380006907124000031240c03401800d01e8140180d0350060b481c00304c214044d136904110204c51600c84c90300c0442c801c480c0c0c4250b002421001e22910324070505040d600302a074a604224400745010b03450034501c941c004100f4052881e002c50f0280e4040f0103003044800e10b1f2300b10343d00103 = true := by decide +kernel

theorem S116 : BRFrame.sub P3 P4 TB 1680 MM 255 385038336 1250 385037086 385037111
    0x21060608030d0608010b09060d15290402070302060f070507020303030f19062402030d02030903031803070f110415060201020a0f031b03151502030a09142211031504 72
    0x3a4091b040719074200034450b001030341030702d85240c421541ca40102c407402c40d0302c2c0c40d405058080340c10000311101c551001e20141c8440c0c40b0210740c40e040c04501624118641a0b140d1806540c0300e070001c2c440c403c2100400d000802d41d6210700e040e680e42c65406011a526800c020508206415003110458507800d0844040842030710756008140484143c43d0070aa9942400300d101019282c403004500c0942c802000880f0303901d1410310082d4440c07038000b4051601e81c20840c01146054220200041c0305038810b01124021030181ca014080d120f50006114510307075a10408500a050304203000300d00068610720004103a90190020b1109407020b40e41e4070308441c2c0400040d4105c4e0800c90014079031022006200d082c2a001e030707014400741034a40d08004040c550f1011902d44190036002c10900580011800c4402a40c00c07841c184085c1c6140d81c0000e0103124114040740304c0d4070000b01c0c0300f01345180c0c2d203041c44050304003503010003d444018902203507139142400350040c503c40b0100c03c00b80910701c0d21584980c1c0d03 = true := by decide +kernel

theorem S117 : BRFrame.sub P3 P4 TB 1680 MM 255 385039586 1250 385038336 385038341
    0xd0b0613080c2805010e0d05060a0b0306070c0503040b130b0703080106110f03041503060314032106030307170405100309120e13050402031915050a0b0a21060608030d060801 76
    0x202c20f091520801160500d4011203e080f90042002e030401880e041c0070340405d9080204511414001d4030100d001c0d002023043c5400d164014102c0010301107c01400780000d40d005c000d503400d440d4404a5981c98414007004071851107043d501a241c1200002800720a0692007194281601c0444d285c00300d0340d036180d24450382d452410b001c401c4480e80060005004082c01d001201c0f208001034500821450f03281d0700d032040c2d0007000341241c1c18554070001e8180d000003202100035109030b00c0e1400c82d51013441c0c00000709807a445020b00040102904c042541e80201403502aa8007504003e443d5034002d81041c0340150040042c1c0505aa16200c148900000584240500112a50090058508580c90303038410409404081c0c81203074140142c4603002c0d000410306038021580d074011507416801480034902c00302140c20107441c00003005e04041125095403200d1200e14110b919410308242621005140c4036084281d50030000c010b181092800950a0000806080740d480e000d041000015036820340d545c00c = true := by decide +kernel

theorem S118 : BRFrame.sub P3 P4 TB 1680 MM 255 385040836 1250 385039586 385039639
    0x30f0e060906040501121d1506040b0a0308070f0b01080718020a2a0206031302011d0102031c110a0c0b10030209040f02060d050c130503060402060d0b0613080c 70
    0x1400b800400060100c0c2d40325039a0314410f0070950002007912201c6940d4041c20b000500300c2212130b5840181c450246e500d65541c925040001035908004455610011401c5201c0707900014082c1040004c04004200711041040187e60308501c403080b0650310b5095a80d16240c0610070340210f003164180c07a001d076070070798130031076102d628962615404c820340302d900d012440e5001d50100580e91a0b141c1d0400150703c0700e600039441342c020004654500740d0107200141c410841c1c20040c0200c01c0c802c0b40082d1840c0d800100303d610003030181c0c410300603c548804110014003140c00c070911074000042488c9116036041604c00154034450b101ca400150b407101070940741c46000c0d200195016135400c0100d00414050ba226071140c5002605042c0f40003100a80741c01035842c10303503802c0701c05200021224032000031004c0701d8010300012400f810041c206070b0001800c0d07016491100030403569030122011603070350328000c458440d80300f100602005aa02c900c40b6803544002142140100c1543d4980e6480c004130741d1050780d = true := by decide +kernel

theorem S119 : BRFrame.sub P3 P4 TB 1680 MM 255 385042086 1250 385040836 385040839
    0x2070803040f12031b030c06060e09150606040302150403022815090503010c081b09010c0809240a120501080318150c0a060f0903020d0305060616030f0e0609 69
    0x11075191801d0b401e0f0540c0a501c6000f601400700e80034a00d429040412100000b41d4041d46450f80d10362a1458240103d414543c08050340c1c0c00742c00140701c107840300401c201000020350510031016480340b6000425500c02c5a000941c4602c1d441c42e040b023030810300e130050401c0f24000c4509509040b80100000512981a105206007c1a80130306011051800d10450040d900c40d1411240c03054440020a0031154004441000300704214100b000b410b000700158040a401c02030342d103091046c08030000e00b0490715000002c2c0800c4c00444c1c001955207421045504da41d40c04a48603058032440c40041c11942e004107910710008006000000b46103d041c040c0328100d40054004502d400e4190700803280030348c011120b0399030141d041044441d5908445000e014001104800b40802615525001c2c049804c84054114854241001070380421f0300071030300020740c03030460038080780580d00c00000410a1250008000c1103110040c520b00a1582c4000c4008070110305481c1e07042082690400c004d2240070b9112171a = true := by decide +kernel

theorem S120 : BRFrame.sub P3 P4 TB 1680 MM 255 385043336 1250 385042086 385042109
    0xf05010e0606090d120207030804080a210c030302090321070506070206060907080405070b040f2c01170f03070c060e0114040603020c010905010e2409060606030601050d0e0105070207080304 83
    0x7140080c61910f440c02d1702d4103041c030564030031030b40380da59100c1da56010742e00184190b40221103d00c00d1005401d001d51400d0030002c0800d50541752140058a0060b00c4100942410f40c0405c2e5a80d41e0744080c0000200c013100c058400c0302401e28980036443c150403080082e00c45100f0302c000a48141d00000c1d401d806000c008210040342d544042d811603503043c0080007100c4074060644001408542c0a02400103071141400082c006403c0507206209260380312000c808040016240707401d070803030880c1000d05650a200c40120404060141d49103006840d6405110622000038100b080c0301030381d4040c1c0c00351941039962000c0353301501c00442d0715035000700350420343c203a08220030098540650700070030440c0815000403924411a0700e071039003110580c0c86203403055004004480c1110310b49031142c6403264401004040c160501c1020681c0e9803100400350b0f400f560000010841c260302440c1910000d0303400c103c06000c21160b0750500d034003070142a01d03800054401d0501c08501d51001209441c203032204013011 = true := by decide +kernel

theorem S121 : BRFrame.sub P3 P4 TB 1680 MM 255 385044586 1250 385043336 385043359
    0x91e01140105131b050a020f1615020a0c060909052a03130503070f0506010e150105090406090f060906120f061a0607031106012c04060b040f05010e060609 68
    0x100300e031000c0c091a15008240e641d10030007045552010703041014501300c3d01e6164441d002284040c0c1082c0c0d00203441040e580141848941c14002c81135200107450034a504011100c260b52416850104140c50103010000306240000d20140d00c83e42c04e1064070400c81c418050760b02c410420055a541041880003110301105500c00619240006180e110051850040d040a865100c2c2811584284400d84524442014040601900b00f0115006181898048001e450200c03074440981c0711401da01410400e00085286403943e80d500320b00060054800f04010010720b0f401204005c0049104180641d410008002024644004c040b40c0702500503c48689180e01683d5038001400da82407042c08804a51018071015100e8002a100041c030a4558411407105215403d14200c0305a01c444080c0c2200ca000c509407030f000b40303110b101d690131254102049884500d0b003400900341d56030909030031510f05400100880769a40199048500c100e004080c651204810700c08184100800c081d0032450003240e = true := by decide +kernel

theorem S122 : BRFrame.sub P3 P4 TB 1680 MM 255 385045836 1250 385044586 385044589
    0x17072904060b2d0315091f140108010c030506100914150c0604410a08131e030209131103010603061a2b1a091e01140105 53
    0x1111003240b50040010000b511103100c41c1c0c40c000c0c0104000b0342c460010075025440d9060802c0111210080e010010910303140002c03038213603a0001c559030707a1090544550442d0000001e6089885141c00c80c00281c0191f684810798039000b010842e6207400003d04000101e1100e0401d4004040d8131900707130381ea5032651400c1c00c01c40c03015a10200043c580100c0340071400343c10700e18208050500682c0c800050308403400c0504141400d155410540c107500c020701001a020701d0011405030f030040224a40d29022104030004060400b902081f020b44108400640da00c09804500c80020a88000d1041ca12503113200700b00d04012041e030303400000e420207038510101e82c010401c0144030008501c030300381c070081020200e00440d0a5450913801118202e44440000248081703d0010803220141920900f281c1690103185022491800c41e508005602e482e6160051103141c00038024800881100c888080c106440c0150340c444280180002c0d005441c40d049100d0b11040c060810380701c45070728020102c2d03401c140 = true := by decide +kernel

theorem S123 : BRFrame.sub P3 P4 TB 1680 MM 255 385047086 1250 385045836 385045841
    0x10b040c1e0806211f090b091b09041e0b0a0c020303011202043621020705011809020708030702010506010c08031b160309060206181b0303071707290406 67
    0x41d543c01c402e115003c500380c40d645c00010a04070760100c2c094003080e1040d89250800300d0312030140610b41c10380c101d24400032041c11903100421083c48100d17007060441d21103003024142681040400e00c1201640d0340348505010302125000d004100c42c803001c11001c40c0040c4226181d001c2801200c440c000c80b00e00280161405402480d80c60040384102c400e0502ca01c3ca1059140040c2d40f41400b9003156515907400b485494a1400422188101a03100080c540e017002900d0303504600405040c44a40300d0011003401c3d003484008041c0401180c2195103134580e04003544241c20468011006608207000220294894a07000c2c40e603603400040e10742036450300c2104500e4002c500c2680e0314800001d00540c1c040801c0d001d00040708501a0b1140301400381800030090800c840102020420f04010882002a620024101141c200051107040e0300e02e070a080007038158801c684025080c41c51868050520130305e40001890840d00ca0b500c45e14141d000f481c40031090120355107940701004510030006001c41c6654 = true := by decide +kernel

theorem S124 : BRFrame.sub P3 P4 TB 1680 MM 255 385048336 1250 385047086 385047139
    0x801090f02042d0903080109020412060f1e0e070f050603070e030a021f1206120f061103070206100504090c23040609020d0605091314010b040c1e0806 66
    0x1000104101c4a00e80505020326100c00c0340f06882ca403903c0c0c00105041d00f04c15a140503040c40c0f80d082d860682441a00e0014940110004000998070032550680d65850780c4515500504d541c980c100c81501d07208444050a0500307124500c5009003080084e40d2545940381604070303038015040ca411030b940c0c2d44d81520700c4070780d42002c680c05000780d200b1072006a44500074042d200c0d032000c14980b802c3d0704030300000305596095404c6004240c80c0400510101c80088140d88142c0e5000106420421507843e040010301030034030340d0700280d0101005016540d500492890305c41d2068250007490a50780300b041000342c075070307503040030700f02d122101c1042c00005480c100400051440c0203841212000c2c40010408a03003282e401410041d5000c00e9840c2c0c0a0260b006640040ca0202c50507045801c007005291010704c484480200004484000c01c4d09090083d00002803c0f10001d01c100b00003c40700002800154510600c4204d4034403003640d000d481d6001d000428011200502a6101040603c1e0341000a0080 = true := by decide +kernel

theorem S125 : BRFrame.sub P3 P4 TB 1680 MM 255 385049586 1250 385048336 385048361
    0x200105070e090f093f0705150402060f070213021306121a090414070915060c0206040b030709120302010902010f020105040b070503100305030f19090b0f0304060e24010801090f0204 79
    0x600d264500301d008459070429030020000d1782c1d99617985143c20000d0400c2c041040c0d91902000354000d110250b624641916401070620500366039460603031002a070303041141c4203400b402a001141c641511441900008100d80c459110a1403004000c05030000302e0b90441100002d02c0d00040003507010742454021598014821a103000e50464401c01462400046034840140641c07035142003c99901c88080510007058a0b081640c0c04414940c0051400c0c00307030b4050784820340c801000290740306229403192002030428045200181d125410002d0203010300300d40c01d9010560704180b2030842032051089520594100d13210008584401340c045406a1003c4e01e84406421900008000705030288001c20021201054056403086501f843d80c00c80441c8050107000d2151000b410000c40c070310402124000f149080c03401d0b40d240c2c0c2d91720300100101182e001d40805032140c10300842001c500a5640030403c0d80d48400001c00c5e80c0e03512089400c1e1205c03040000c00d5410401001001070030a5006001d05580 = true := by decide +kernel

theorem S126 : BRFrame.sub P3 P4 TB 1680 MM 255 385050836 1250 385049586 385049653
    0x12020f090a0605030d020f070b0c011b02030304020a0b1810050c2401050a030c0e040309090c0f030b03070f050103150e04030f031119200105070e090f09 67
    0x184100060800100380c6000740c40c5030703a91030204076a01d0104802e140050860010780550f003020803245445203810b100d880100317840041c00c0003210200b03610501043c1030221110132402142c0303100a640340c20488049000304c000c54804244888078406580c0345401e080c880c14100e0030312000740011540302c0600c1ca07040c46014005415010801e01010f44130f0344240402d000b1100c0c50450040b580300c1c040e44518003078a02003000703001184c8031110900a95495a0188a898603a8681140d02040b954001d6110a02d040352110030383d540180003103005a69070340c0500c9140c05090401d80c8a00d0035106607202d044070107004101e954042d4000c1c0451403400307803002d02516502c4a10b050850340403a021030001c0e183d090b01e1318099030107118104d00d1340e25500700c5c0e034240700c00d078605866003102c40442c2c4000c1c800c01c152004111220a0003070f0180703c0100c0000d00c02400d100e00050112501200c03a5072090003550001350b0f0512080000e1441034480e100180340d00c00251000f8112603022100b44100c0300c4 = true := by decide +kernel

theorem S127 : BRFrame.sub P3 P4 TB 1680 MM 255 385052086 1250 385050836 385050859
    0xb1506270915090a052a0415030507200607030c1407060501080f0f120309010e1213090b03031b07121101081303090501123e04030c1202 60
    0x58401007040e1051102000022848580b00304004007104000c100381492032404080c004403603617004402100b18000d03c2c10800c610091284100140100e60040100402000000c8201c03503142e00054006d41503919650032404031000c01c4454950420f20719a401d0380082c0008150b07501c0703a04180303880b560718103081c400004412128085035011003c140d076000e0300d07900104142002007002d8000070341c0440150145d58802c94541e5200d80c440d04bc4442d01c220b010003c102544420b5101d00c1e0340c3c4040b070040303c800c904040c0d4000c0c90380d040b60441d00da20154071240094214070500070700d1580c44008015507d484070360b02d000301703100324070100b1205d651290040c0402e108015088c6015428052034500c803200007124001865031030010720070a610071306d006e1403400003a003080a40c02580c20900340031882014080e00c10004005c0c06180b1404600c142038400145c51138105c00710030a06c0b03031820500740302070100c401d04508e2180e480020140e007440c03603040041100112250600c1d0784014010036206 = true := by decide +kernel

theorem S128 : BRFrame.sub P3 P4 TB 1680 MM 255 385053336 1250 385052086 385052089
    0x402040801020705030301060f08040803041104020c010203240a03081905070f2d0807140f0106031b09020a02190609020901090f0f0c3504050a0b150627 67
    0xa8200f10021a402d41c030000050141c076403c120540e0120141e458045114580340e95a0106400080e000a2a09007180705d80ba420b075403150141e402110541d4001c545a10344103041200300030030200d9003100351441607184102030030403c010703e056a400c40d855502c0c01180007104082a240400ca5004021040c07094100043c242d5405e1602e143c09280f00101940b0250340d8008000c0840b43c0c14075010b141c0c040b00000180403c01525110358104d1719104030162105201e038100001c0551810b225407038504003104108244004900404032019012a80342c0c449019100306e218002140000d42e0150320035407882e0824103ea041c83c940310f100049a480083c3c1d020a0046000707800042056407a680c11086080319403048510340719107680144942ea00e140806403001100c2c00203004c010111000c4103600d82d5220114050490b601114180b441c500742c10140e0300da05011404840d402400808107003d60382c500b1804415460082c03005140401e60070161495180004000e20038100e03008040031706 = true := by decide +kernel

theorem S129 : BRFrame.sub P3 P4 TB 1680 MM 255 385054586 1250 385053336 385053341
    0x20c0d020d0f0c080c0616022e090806061c1202010e0d051b1506010509030304080a080c060f090d0f1101060f1a040b030112020a090203070e0907170a02090402040801 73
    0x742e00c610001c40c0868106500141040a0070030300a009031340500240d20b07e00ca1075100d07001c4160301078a204070f540b003143c180e000c00c0c41d02071503141c40c6034a91407d0142055134000d016000325010441a01c1e0103880304002c00032000b0007004400c900b817180d5035071000800c248440303e00c00301c12940000207104c21034a154901305600d81501c0d10210310017251082608038494420031394043c04402600507105404d4032820060005019103040200100d00318545403410804c4601074113121045074621009460b01c60300d50340c426245806540202004154002c442101003400348400e02c0c0179201e40d0484000c02c03542010100c074500b003080401420240d00c0310081c40b07128094044a01d071001e00758144401c41b0880036040c0c001c4900d01000700405c20004910b50162410740380315041c0554195038500000b41d40660390b03040648460b20000600c80f4264016552591003082941e40e8040e44d03491400644034485000c940040b00c0001d000020000043c9070300800c056640180014146616080700c00d08 = true := by decide +kernel

theorem S130 : BRFrame.sub P3 P4 TB 1680 MM 255 385055836 1250 385054586 385054613
    0x218070c0c0806040309060c0b0a051512010c170408040317070b091c02030a021f020c03030a09050d030204080307230a0501060915061407020319050625020c0d020d 72
    0x2c2c00e801a005000601d03038480d44407130150807141040030801180340c3d266201700c04024441d25500d0350f2140410311101600d040744040500017080c1c0c40950520011044c000c203a6038000901040000c0188440850800c50052195030031180d00d03810640b03951241312038030507000e032034800640003003180c40002101c00d5200f41c01602444000d2821200340c18010b1070044101c1e4013441907603c140501a1856170002d5074414990007505009080031614a909010b40071741c05070154140000b05c02c000c081c1e4016401800850700800456441800312482034080703110b207008000d41078008000b00004034400d001c419507075080c2601d03003900d0108415070050909010361421510317079446400400840c3c0c80c6010310014061440641c08030700c0d1901c1c0016210002201c042811214040b0301c2400b035581c1440000f10625004100c90104013880c0740c501c4e201d000031030b18000052450340d1031f602036a03000309564060310100d40061644c0000c000401200081113002280e1140c080514000001d11000e0081d1 = true := by decide +kernel

theorem S131 : BRFrame.sub P3 P4 TB 1680 MM 255 385057086 1250 385055836 385055849
    0xa090204050c07030f0e10141209280f08090a08030f090a050906010906111c1101053303010f0c05071a07020a06051302100807030b0d0218070c0c 64
    0x3d464600c5072038010640303c1c00030750358400c01245c40080d101540d280d1041c4460a405820010700702481e05444140710301179581b03101c61111004040000c818404a030300c00006d041d80c20422100107442d100e4148886160070060501000e01f07106100040c000d20045c464424014610030310380d9034a00c003491079540036a07401c0a08800100d00c418030790415003d0000600400c6440f40b0441c030707180c00002d0146c440b500c07a0800700700951003c03011900c4140506040f00e07603d01c0d42c0205800c0100d00243c4046402c4204601e250302c3c003c0003e90700141c0d0404107907e8840c8013007200204d605045210b40c08417840c01010740c15540c0381018440f49070f0320300c40e04030300107120703122184ca40381030b402e1501e60b0801c0d061590380e06015003010881c2a9602140e030a440c0c0c0c0d841900040c0e00d486003041c00c18031207090300700290000d00012400d00c20755040190548074500c55601840000800802c0c0407a5510004000b03411200303c525242c080351113110242d600c42c20601c0c0900c501045030300d030405071009551110 = true := by decide +kernel

theorem S132 : BRFrame.sub P3 P4 TB 1680 MM 255 385058336 1250 385057086 385057111
    0x6190f091107020f0907180609180b0a05040e03040905010314010e0312040b070e0909010614190b0a022802040b010f0c03080c0c070303030b040c0c0206030c030a09020405 75
    0x400c84006980585158204000c0c0118100000c580104080c034481000ea04d100d072032103200040c0c1181c0074610740300c0b04009581182c03001588506010740315542c2c80c003030100444007401c0e489400b0300d01405100d085801c054002c00c4107500d040300384006400c08480c0c074901c0b4007080c400801c44814520a15009500030b81c1980c43c25640744e0b03051400c44040440c0c040840e0400c1200c0500d6084904039940c006502c806008003556070f000080300c0f5200c1c400444c540c04006981403166041054220714182da140740640744641f9a02c004004a08064103454001341019032820003402a040c0c1c081d241c007801900680e1415080310007044020f1200c3d05000008418088010041d814244100c0c0101c1c8800e003446104030580d00809006c944001c00009d0411135000c00180030362404906980840b034001d421aa08140c4070b01e80680501407020718103014524054019940034171801c00079103481c1c3c014080c0e5117181c465003410f081c143d100034401254161100c00030f00060300c2d1841003602c140c000c2c0d00320 = true := by decide +kernel

theorem S133 : BRFrame.sub P3 P4 TB 1680 MM 255 385059586 1250 385058336 385058339
    0x1507021b040f0213050a0503061b0f04170307060b030c030c12160f15030203010b070f021807030e0105060d02090103120903080a030b19050f0607021302160312150b0306190f 76
    0x805c40041b11540081d4000d9014108108041000d90b6924413820aa80c1e002da0300c070040c019022009214a8201940303041500036a00380342c140010142c00f105100301c501b4880c0410400a040c0d6584100c2e10b441d80c0746d440360405030b085061412100100e0003203071050311001d004640590300080410f502904128940d40c000300050340008040502c1c1c1c804a140035803455140510f16480c601170220050404e40070703480312000f1035a80c5016243c0340c440d41c25400805150924024008010702404107146509100001c0c0c1b02d40b4125102c4a262540149042c0150f42141c4600144c480d42000302c03414442100d01c00b00100395281c011302058903a6a80200e860850f06041c09241054000740120f00032800d8001e00040e52030004005142605860180c2c40d1105c1d80000369680451100010703070188000b807034104c1c0300780701c1510740e07c20f030b010ba200c50120403a4045020125005030aa41110201c015024040c5603e1240110f411030002040106491401c060340c56079010160b000c000104c071038040 = true := by decide +kernel

theorem S134 : BRFrame.sub P3 P4 TB 1680 MM 255 385060836 1250 385059586 385059589
    0xa0210050c0d0905060306010e031005181e0a060e071a070c0905100512150112021810050907091502010c09090b0a21080307030e1507021b040f021305 66
    0x4905900b0203e1405072220351900c03001c03078190701000d0030150502c00d45c5610000f05460410419920b07071001d100600050800030014140c41c048600014001c1c000c845200020300d0301c0300c2d040c0c10f011a80e01d00515040500d0b0311040010b140d80c8401d80d00074010b40d903000482c00148441880f0407503d180880c0d54841183c60544d024405d15031240c0c500c1400d100400c01220b05050200040380c1090380c1e6806040340390308000381008181c0c201d095200a82600119644c006070310300450f0350b8030940341c1940640c001c003000125210100da0300080364001c03000a200314100f4518450708160181091808140c40b062038005040c0746100072401070f95240b40d01c100c40760b4025020f400408011100300401090900401c00390100d90040781d941c0240540e040d0300700540506103042d880e40003051503840c1e04114030004e01030b1010910300842e0348100d007801040011560703134940c022000c9030020102080541880c03040040c5090b04c103544255a5917080072000c0f9180010003550214030755402304142040e0 = true := by decide +kernel

theorem S135 : BRFrame.sub P3 P4 TB 1680 MM 255 385062086 1250 385060836 385060843
    0x2030f030c160503190809031e010b062d09090403031a0f0a1e080a0506010824040f0615080106060908030a090b0c0106050307030c0315150501050901020a0210050c 72
    0x14080060388042c01d0104050348000c903400329409800c2085008402140c00c201c2e0f0988034405110741c161082c0b00c0b8500d4414032507102c2c106191032050003406a46291020807041c2c3c05041802801c640c40400c1028a00d404070070b02000100703404c0c45243c1020400d00024200d548112002d42c04203403176500401c2050f03039810402001103011203014400b0003000c40400d04d80c015500500d0000081428856855082500302c80000c00c90a411281c0351003040c03502580ba00000e202d100114451517080e410f078111141070004040e40c00c0e594200141d03540d9101c031000c82d18031810039140c80e980c50202d200340b0060304000c04050311508001003155480e16030010300800c0340d94401c0783d80741c00900c040d6200360785c0130406000701d070341040c00c003522048001c000e9401040581e0209501d88640807001040214074400d007002c032070243c3e800307640c0c5200301ca0102041e145905802d40340003804840c180415800b850203000b81e804103104640320200b055010845e048422260788000c114003060701e020035107080 = true := by decide +kernel

theorem S136 : BRFrame.sub P3 P4 TB 1680 MM 255 385063336 1250 385062086 385062103
    0x60b03070c212f0c0f040b0a15020d021f09030c060504120e0f06031503030c03030114040b01020c0109031e050102120a0b062b14190605010306030c0b130302030f030c 73
    0x40d4040d202c454803402040d91904600700c00c1510510302103005a00c3c0c0c4c1e1b80c0740c1003451100d0300141f40340d800a40d01d018420b0b891580d052210050700030000c1011405001043c00c12814602142c0c0c4e026502c47d050320710006204182e001c03003d04c1120f54000e80030035194410309204500c00c020b000f028000400010300b042c0000b42c12203104101460b06888941c4030300381501d07081006152441d5440f9500390002e420350048080400a9100100c00007646201c1d407541002110401d6070200140c00c0d250340120f0b00d851006480c680400c81004c0d0030000540603509004a002c60301401848102071a03603080e003641c1c032a02d429001e0708442820321101d404a8840c4400170001107914a2410203c0394803070200800c911503401c803000e40225540910401900001e9001c03000e0788404402d4945440b042c0400b1010545408401d0715140c808117080d402841100300340c07038120b11160ba203a8602488918107078440c0380b007040d203482c0c0400c00200680741000402214000c0740003450311840b840404602d0092074 = true := by decide +kernel

theorem S137 : BRFrame.sub P3 P4 TB 1680 MM 255 385064586 1250 385063336 385063397
    0x30a0519020a0c14010c090306050618070504140f0108280f0203010f0605070b1801020f0301170601050102011a0f0607050312041e030c0605090c1f12060b03070c21 72
    0x1046c65401c01d0682140341101183d078130003008240e56407424006101c034610b030009004080d00c0d050401c0308807907000b801042554102d850700705454240b48103000c1034154071b11082e4007042e450320202c0c1c020f82250144682c030034030b43c04800301210842c40e50102540ea052103501c2000b034000c80140081c40740400d90f200903101354070f070460030300380640c0315840301440107400c40089819012074049024001e4044980c400021218030b507a0703596030203c00c55100c2004000c28424058030001090541c818018020503032421210030740c0c41500841048901d50042004a51281003044000e0014a0620140c130700700400000c0701c2301f40e24090904180381340d41505480d03184016030203441d00103500302603290700c1c640c0c21410000c0c203549ca078000f085c80c20408400c125480000e1744040e608130340d403a040c10402280655606140181002d02c001c098802c60b003d03101004100b44006803059100342d6003031801501071288252110704d078441c0b58243c101003040d00400035104150784016050410001c2d40b01009 = true := by decide +kernel

theorem S138 : BRFrame.sub P3 P4 TB 1680 MM 255 385065836 1250 385064586 385064591
    0x20d02061c0609230c070c0312021b0307061d030a03090f140a0608130f0b0106141e0309030d050c03010504060501050c0705130e100b040e0a0305030a0519020a0c1401 73
    0x30000301500074620419104c0c1c4214801c00104c0d81c464500c105840c510341e0700c450b03805a80382e00c03800e180c0c03000103040f00340d032006114030000c074903c0082d0210001210320b00903004000c124100042541d00310351207401001021940c1c140761076140d40820812007440e0290311000c2805050940c072845204450f04144040c0c0c840412080182c0c0320040204100d42242c50100d046031240300742d030744442010307500c0078107900c0305405007500340141c00a0842c12142c1580f50041003950051091001d4002e03a91140c10604500c5082c1c10003120a2009652006031002560315110340e000444044840607070f06002039020200050202e03042900c9040701421090030203d0034040d02404007a9241c0c083e005042c01000c403048070004e408220f0300070780c20340d80121040e5510300702400c010f54010000448040e10071401d2400d0022003240c0417407141c01003030301030f9101c51030741c2d840d210070f58041e05018004401c117808038200071400003040d20250521100f5950307414224440e600b00618107400140c1000007591 = true := by decide +kernel

theorem S139 : BRFrame.sub P3 P4 TB 1680 MM 255 385067086 1250 385065836 385065851
    0x1b031d030301060503180102070b07020c18150f101d0108150d050f030c0c090109090f0809010c0b1e070305130f05011506080f01090203130b04020d02061c0609 70
    0x60010035241140c000e854055503903640d094046069070b0750714a07000c407290700100320340080008021030030740709680355403c0b00c844c8041202004082c0040c20124000e241e087c0010a0010b0841d0b0b400031418003024040c601c0b89a02c000100d40d150313504c1c48050300010300b012001103040c600030b01d50b802402e0092a0000c0c8904000e001460b074001c850040c2d071300c18540080000b040110520030b486d034240c84441070340c2d01c46501c800364544449001d0030491090000d8000440c8441842c0314407035140307401c003580041d040349030740d0340c0035042e440200741d503041c080175880001c00034186c010140d00c11110b141e0712410a82c84103640f0035000101500070000d060501003040f25100302d4081e01070450740c206610f5211b00c042400e040d40101706a0000041032200000c0201e001d41c2c0024415020700742e00c409203185030382d0b00d50b086412808103680740c2511000c54904078001c81c0360450090341150004000c038030640c203590f00049942c0c0c0200b2000040c030008100004030640c4520540000301a80b540c244030a4 = true := by decide +kernel

theorem S140 : BRFrame.sub P3 P4 TB 1680 MM 255 385068336 1250 385067086 385067141
    0xf02090603070e0d0203071d090318011805100509015c010603020a0603090b07050306031501031b0e01030f080a02030c0d170705091f02101b03 63
    0xc1c00014400c6081040c20049103943d0390f03e41d803010700902e0700941078a89054590b582e0031105000c001140c44169414008030303100707403400000c440341070884038141c503507102400c401115400c90f5103603032084036500000c000c41c0c170f03a4520100140031181c0e80c485a0780c0d4075415001424501d00400d00c04807000120380391541400b18901c484041d8890011181c80c0b60510080d101c4040d50701d4007400002607000004072466030300540c040426a402281c60381b49291360f910b400c500340c600c4890028011005d000201e03210038000d0014540000c1b0003802d0700c9400445254440e2b11107001d03030003910032048500b0810a42c20342402c03d440601801a0803100e59030540e00c580705501003200c0024814a000660401418424400d030356441c4403041c20341e034500c5030114004180d403503100f40000d103065541c1c0c049008240074400326040c02c14007410110550001c2c058044c0760700c003002041c2042d0f0042c482d0740c80c01814980720ba0403070180800141c2d04a0090340b10001c0c22240120000f0460551060313810070320 = true := by decide +kernel

theorem S141 : BRFrame.sub P3 P4 TB 1680 MM 255 385069586 1250 385068336 385068349
    0x50d0c03020f210127080a05030a060e04030f08090106060912030507020a1401031d1902061c050a060803040320010212040602030a022e0e0a020d0c06030f0209 70
    0x6481e016142d020b00ba4820700041a5160203074491890720b403d0b401e15465540406410940855501d0903804d40c683d007070034003c01e60306071801c540203107079441c1080709060550285024660050540d900002c3e01385d500c1507908903424046800310005a01400907091442e044039020350400c03201d20081024904020024250309410302a000389260142101c204251141003212070040d4040c180440c00c1d60707200d4650000310002c1d4070481c0824101000710340c142000340b8020040168000040c00c0601c41400440107007081103000f0390300540d042008584901c0301c0300c44581090390200d0009520302d4040f40040440350a604210b1031074000b04400c00200d54070380119040c9280d50201411341101060041c1c0c40c0403102c80c0ea00000e404041800249150040068045420075400f540c00b0000219045940c0c44002820540506400804024240e030541c0c80316405158582c12070f09040c07241d400045001540755000c581514145409020050303241c00784000d80c0051020a500b80030890000808 = true := by decide +kernel

theorem S142 : BRFrame.sub P3 P4 TB 1680 MM 255 385070836 1250 385069586 385069589
    0xc0c070b0706060305030f27010e01080a0e0d02031c09111c060603030804020102010c020106081905161412010b011b060b13050a0c0804080a0f05040f0e040309050d0c 73
    0x30300c034802180c0d80041c86060340c08200103603800801c490b600c04400404a103503410108413044c000061042820040c6e07520100c1d000360744e00503036407400c40c2c09100e001980c800700081e0120380900e9032401c94034110321040240d5040a03425030020340e2241074140400d00d000d444090f640c07407502c1c1406583c50019010314542c0da1040320440b41548024814102c84041c0507030f640026241a0070040300209154010790124000c500070b038000d11070000001800d90999080313100d61701141d0711541d108424001a2040d20000500c100180d520a68040b505a21100001d41050300c2c4d848100400e11000e20300044d2215101c40c010707000b403103502100d20001e08921120320420f04002c444020300410460103501211208a0082c5820700b8100c0701d501100c000e240442e00041043c0c904134680f82c125024030302c0b65220796841801c2500d881e00c0007800700c4000f265084054240b1030180008a0010706001800d0050b010780062103075a840c01d130900420520140d40154016048901c64002040340d0f042e0080 = true := by decide +kernel

theorem S143 : BRFrame.sub P3 P4 TB 1680 MM 255 385071942 1106 385070836 385070849
    0x70f0c0b071505060a090f15080c010f090803090409020f100e120a1e05010b0a03210507020f010819060806090d02150109050702150f0f0c0c07 63
    0x8846050318407691282c84002e003008100959040080c1d401d4480a0110348c40160668040b120b07002500681c82a8001543d03503101540d0281c03c80382c2500141c1b5005025902e01480c0076240d11800d01041d00071a290183d41040d5100c04142c1ba01c199005007416040304c034044801040c01403600030b00c600c02c1c4400001468004800600608159000941e1800c1a000303c000d454290840c0e110031603ea540b11a44089076543d040b803148000c6010b448070003004a00e207030700003e120754aa190311041c42020f104e1440940c9848800450401f000c3c284420192500c5107002e0300d00c0031440f030200001e820428045810000810041e0103a403260b4204c445400304010140d0f1600c69508214807070590b800010001d402098200302d80201050059401442c200c032403043c02004200c4034081b0300c52200042c001503a11b1401610342c0711003000b400b01e08064451700381c10340300c0080b03103e0741 = true := by decide +kernel

theorem cover : BRFrame.Cov 384892086 385071942 := by
  have h0 := BRFrame.cov_init 384892086
  have h1 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S0 h0
  have h2 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S1 h1
  have h3 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S2 h2
  have h4 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S3 h3
  have h5 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S4 h4
  have h6 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S5 h5
  have h7 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S6 h6
  have h8 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S7 h7
  have h9 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S8 h8
  have h10 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S9 h9
  have h11 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S10 h10
  have h12 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S11 h11
  have h13 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S12 h12
  have h14 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S13 h13
  have h15 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S14 h14
  have h16 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S15 h15
  have h17 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S16 h16
  have h18 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S17 h17
  have h19 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S18 h18
  have h20 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S19 h19
  have h21 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S20 h20
  have h22 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S21 h21
  have h23 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S22 h22
  have h24 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S23 h23
  have h25 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S24 h24
  have h26 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S25 h25
  have h27 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S26 h26
  have h28 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S27 h27
  have h29 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S28 h28
  have h30 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S29 h29
  have h31 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S30 h30
  have h32 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S31 h31
  have h33 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S32 h32
  have h34 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S33 h33
  have h35 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S34 h34
  have h36 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S35 h35
  have h37 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S36 h36
  have h38 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S37 h37
  have h39 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S38 h38
  have h40 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S39 h39
  have h41 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S40 h40
  have h42 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S41 h41
  have h43 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S42 h42
  have h44 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S43 h43
  have h45 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S44 h44
  have h46 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S45 h45
  have h47 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S46 h46
  have h48 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S47 h47
  have h49 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S48 h48
  have h50 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S49 h49
  have h51 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S50 h50
  have h52 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S51 h51
  have h53 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S52 h52
  have h54 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S53 h53
  have h55 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S54 h54
  have h56 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S55 h55
  have h57 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S56 h56
  have h58 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S57 h57
  have h59 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S58 h58
  have h60 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S59 h59
  have h61 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S60 h60
  have h62 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S61 h61
  have h63 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S62 h62
  have h64 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S63 h63
  have h65 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S64 h64
  have h66 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S65 h65
  have h67 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S66 h66
  have h68 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S67 h67
  have h69 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S68 h68
  have h70 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S69 h69
  have h71 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S70 h70
  have h72 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S71 h71
  have h73 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S72 h72
  have h74 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S73 h73
  have h75 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S74 h74
  have h76 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S75 h75
  have h77 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S76 h76
  have h78 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S77 h77
  have h79 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S78 h78
  have h80 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S79 h79
  have h81 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S80 h80
  have h82 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S81 h81
  have h83 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S82 h82
  have h84 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S83 h83
  have h85 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S84 h84
  have h86 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S85 h85
  have h87 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S86 h86
  have h88 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S87 h87
  have h89 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S88 h88
  have h90 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S89 h89
  have h91 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S90 h90
  have h92 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S91 h91
  have h93 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S92 h92
  have h94 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S93 h93
  have h95 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S94 h94
  have h96 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S95 h95
  have h97 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S96 h96
  have h98 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S97 h97
  have h99 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S98 h98
  have h100 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S99 h99
  have h101 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S100 h100
  have h102 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S101 h101
  have h103 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S102 h102
  have h104 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S103 h103
  have h105 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S104 h104
  have h106 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S105 h105
  have h107 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S106 h106
  have h108 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S107 h107
  have h109 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S108 h108
  have h110 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S109 h109
  have h111 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S110 h110
  have h112 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S111 h111
  have h113 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S112 h112
  have h114 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S113 h113
  have h115 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S114 h114
  have h116 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S115 h115
  have h117 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S116 h116
  have h118 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S117 h117
  have h119 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S118 h118
  have h120 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S119 h119
  have h121 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S120 h120
  have h122 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S121 h121
  have h123 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S122 h122
  have h124 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S123 h123
  have h125 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S124 h124
  have h126 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S125 h125
  have h127 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S126 h126
  have h128 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S127 h127
  have h129 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S128 h128
  have h130 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S129 h129
  have h131 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S130 h130
  have h132 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S131 h131
  have h133 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S132 h132
  have h134 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S133 h133
  have h135 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S134 h134
  have h136 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S135 h135
  have h137 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S136 h136
  have h138 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S137 h137
  have h139 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S138 h138
  have h140 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S139 h139
  have h141 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S140 h140
  have h142 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S141 h141
  have h143 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S142 h142
  have h144 := BRFrame.sub_sound P3 P4 TB 1680 MM 255 _ 384892086 _ _ _ _ _ _ P3OK P4OK TAB S143 h143
  exact h144

end BRData

theorem solution (n m : ℕ) (h1 : 384892086 ≤ n) (h2 : n < 385071942) (h : Nat.factorial n + 1 = m ^ 2) : False := by
  exact BRData.cover n h1 h2 m h
